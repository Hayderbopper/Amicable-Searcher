#include "engine.h"

#include "general.h"
#include "numeric_utils.h"

#include "fpu.h"
#include "prime_iterator.h"
#include "skip_file.h"
#include <primesieve.hpp>

#include <algorithm>
#include <chrono>
#include <cmath>
#include <condition_variable>
#include <cstddef>
#include <deque>
#include <exception>
#include <fstream>
#include <iostream>
#include <limits>
#include <map>
#include <memory>
#include <mutex>
#include <set>
#include <stdexcept>
#include <string>
#include <thread>
#include <utility>
#include <vector>

#ifdef AMICABLE_TRACE
#include <cstdio>
#include <cstdlib>
#endif

namespace amicable {
namespace {

using Clock = std::chrono::steady_clock;
using u64 = std::uint64_t;
using Path = std::vector<u64>;                   // (root, q1, q2, ...): a point of one k's search

struct Job;

// One k in flight.
struct KJob {
    u64 k;
    SearchK sk;
    OutputSink sink;
    std::atomic<bool> cancel{false};
    std::atomic<bool> timed_out{false};
    std::atomic<bool> failed{false};
    std::atomic<int> incomplete{0};
    std::atomic<int> pending{1};                 // generator + queued jobs
    std::int64_t started_ms = 0;

    // single-k resume tracking
    std::mutex rmu;                              // live, next_id
    std::map<u64, std::weak_ptr<Job>> live;      // queued jobs not finished yet
    u64 next_id = 0;
    std::mutex genmu;                            // gen_pos, gen_done
    Path gen_pos;                                // everything before it is finished or queued
    bool gen_done = false;

    KJob(u64 kk, ResultWriter& w) : k(kk), sink(kk, w) {}

    SearchCtx ctx() {
        SearchCtx c;
        c.sink = &sink;
        c.cancel = &cancel;
        c.incomplete = &incomplete;
        return c;
    }
};

// A queued piece of one k under the node chain.back(), one of
//  * a sweep: its children, the primes of [lo, hi], in blocks of `width`;
//  * a Progression sweep (prog): its tail's u, the class members in [lo, hi],
//    in blocks of `width`;
//  * a batch (q_list not empty): the children q_list, one block each, each
//    with everything below it; single-k runs share those out instead of
//    running them in the generator.
// `path` is chain.back()'s point (root, q1, ..., q_d); the next level's value
// (a child, or u) extends it.
struct Job {
    std::shared_ptr<KJob> kj;
    std::vector<Node> chain;                     // chain[i].parent == &chain[i - 1]
    Path path;
    std::vector<u64> q_list;
    bool prog = false;
    ProgressionPlan plan;                        // prog: the tail's plan, shared by its blocks
    bool spawned = false;                        // split off by a thread running a block
    u64 lo = 0, hi = 0, width = 0, nblocks = 0;
    u64 id = 0;
    std::atomic<u64> next_block{0};
    std::atomic<u64> done_blocks{0};

    std::mutex bmu;                              // first_open, done_ahead
    u64 first_open = 0;                          // every block before it is finished
    std::set<u64> done_ahead;                    // finished blocks after it (a few: blocks
                                                 // are taken in order)
};

// the generator's walk of one root: nodes[d] at depth d, path = (root, q1, ..., q_d)
struct GenState {
    std::vector<Node> nodes;
    Path path;
};

u64 block_width(u64 lo) {
    const double ln = std::log(static_cast<double>(std::max<u64>(lo, 16)));
#ifdef AMICABLE_TRACE
    if (const char* w = std::getenv("AMICABLE_TEST_WIDTH")) return std::max<u64>(1, std::strtoull(w, nullptr, 10));
#endif
    return std::max<u64>(2048, static_cast<u64>(384.0 * ln));
}

std::string incomplete_reason(int flags) {
    std::string s;
    if (flags & INC_UNBOUNDED) s += (s.empty() ? "" : ",") + std::string("bound_not_finite");
    if (flags & INC_SCAN_LIMIT) s += (s.empty() ? "" : ",") + std::string("range_beyond_2^64");
    return s;
}

// The children of n are Progression tails (single-k runs split up their u).
bool children_are_prog(const Node& n) {
    const RootShape& sh = *n.root->shape;
    return sh.prog_tail && n.depth + 1 == sh.tail_depth;
}

std::vector<const Node*> chain_of(const std::vector<Node>& nodes) {
    std::vector<const Node*> c;
    c.reserve(nodes.size() + 2);
    for (const Node& n : nodes) c.push_back(&n);
    return c;
}

std::string path_text(const Path& p) {
    std::string s;
    for (std::size_t i = 0; i < p.size(); ++i) s += (i ? ", " : "") + std::to_string(p[i]);
    return s;
}

#ifdef AMICABLE_TRACE
// test builds only: logs every finished piece and every resume point to
// AMICABLE_TRACE_FILE (checked by tests/check_resume_trace.py)
void trace_line(const std::string& line) { trace_write(line); }
std::string trace_path(const Path& p) {
    std::string s;
    for (std::size_t i = 0; i < p.size(); ++i) s += (i ? "," : "") + std::to_string(p[i]);
    return s;
}
#endif

// this thread's finished k values not yet merged (see Engine::flush_done)
std::vector<u64>& done_buffer() {
    static thread_local std::vector<u64> buf;
    return buf;
}

class Engine {
public:
    explicit Engine(const EngineOptions& o)
        : opt(o),
          stop_k(o.stop_k == 0 ? std::numeric_limits<u64>::max() : o.stop_k),
          next_k(o.start_k),
          frontier(o.start_k),
          t0(Clock::now())
    {
        max_stop = primesieve::get_max_stop();
    }

    EngineStatus run();

private:
    const EngineOptions& opt;
    u64 stop_k;
    u64 max_stop = 0;

    std::atomic<u64> next_k;
    std::atomic<u64> completed{0};
    std::atomic<u64> incomplete_count{0};
    int nthreads_ = 1;
    std::string last_reason;                     // of the last incomplete k (guarded by skipmu)
    std::atomic<u64> active{0};
    std::atomic<bool> stop{false};
    std::atomic<int> running_workers{0};

    std::mutex qmu;
    std::deque<std::shared_ptr<Job>> queue;

    std::mutex wmu;
    std::condition_variable wcv;

    // the main loop waits here between ticks, so it notices at once when the
    // last worker has finished (before, it slept up to one tick, 250 ms, longer)
    std::mutex donemu;
    std::condition_variable donecv;

    std::mutex fmu;
    u64 frontier;
    std::set<u64> ahead;
    // Finished k values are merged into frontier/ahead in batches, from a
    // per-thread buffer: with many quick k (most k of a range have nothing to
    // search) the threads otherwise queue up on fmu for every k.  The buffer
    // is merged when it is full, before a thread waits and when it exits, so
    // frontier lags at most a few k behind (it only ever stays too low,
    // which is safe: a resumed run repeats those k).
    static constexpr std::size_t DONE_BATCH = 64;
    void flush_done();

    std::mutex regmu;
    std::vector<std::weak_ptr<KJob>> registry;
    std::weak_ptr<KJob> single_job;

    std::mutex errmu;
    std::exception_ptr fatal;

    std::mutex skipmu;
    Clock::time_point t0;
    Path last_resume, last_current;
    u64 roots_total = 0;
    std::atomic<bool> any_timeout{false};
    int seen_flags = 0;                          // single-k: INC_* bits seen so far

    std::int64_t now_ms() const {
        return std::chrono::duration_cast<std::chrono::milliseconds>(Clock::now() - t0).count();
    }
    bool halted(const KJob& kj) const {
        return kj.cancel.load(std::memory_order_relaxed) || stop.load(std::memory_order_relaxed);
    }

    void worker();
    bool take_block();
    void run_block(Job& job, u64 b);
    void finish_block(const std::shared_ptr<Job>& job, u64 b, u64 count, bool processed);
    void run_k(u64 k);
    void generate(const std::shared_ptr<KJob>& kj);
    bool expand(const std::shared_ptr<KJob>& kj, GenState& g, int d, int job_depth, bool on_path,
                SearchCtx& ctx);
    void run_item(Job& job, u64 q);              // one child of a batch, everything under it
    std::shared_ptr<Job> new_job(const std::shared_ptr<KJob>& kj, const GenState& g, int depth);
    std::shared_ptr<Job> job_from(const std::shared_ptr<KJob>& kj, const std::vector<const Node*>& chain,
                                  const Path& path);
    void push_job(const std::shared_ptr<KJob>& kj, std::shared_ptr<Job>& job, bool spawned = false);
    bool prog_blocks(const BigInt& first, const BigInt& last, const BigInt& modulus, u64 start,
                     u64& lo, u64& hi, u64& width) const;
    void run_prog_node(const std::shared_ptr<KJob>& kj, const std::vector<const Node*>& chain, const Path& path,
                       SearchCtx& ctx);
    void scan_prog_children(const std::shared_ptr<KJob>& kj, std::vector<const Node*>& chain, Path& path,
                            u64 lo, u64 hi, SearchCtx& ctx);
    void set_gen(KJob& kj, const Path& p, std::size_t len, u64 last);
    bool split_progression(const std::shared_ptr<KJob>& kj, const GenState& g, int depth, bool on_path,
                           SearchCtx& ctx);
    void release(const std::shared_ptr<KJob>& kj);
    void k_done(KJob& kj);
    void handle_exception(KJob& kj);
    void append_incomplete(u64 k, const std::string& why);
    EngineStatus status();
    bool flush_pairs();
    // workers waiting on wcv; a notify with none waiting is skipped (a waiter
    // that just missed one wakes on its own within 2 ms)
    std::atomic<int> sleepers{0};
    void wake() {
        if (sleepers.load() > 0) wcv.notify_all();
    }
};

void Engine::append_incomplete(u64 k, const std::string& why) {
    incomplete_count.fetch_add(1);
    std::lock_guard<std::mutex> lock(skipmu);
    last_reason = why;
    if (opt.incomplete_file.empty()) return;
    append_skip_line(opt.incomplete_file, k, why);    // locked: a skipped run may be rewriting it
}

void Engine::handle_exception(KJob& kj) {
    {
        std::lock_guard<std::mutex> lock(errmu);
        if (!fatal) fatal = std::current_exception();
    }
    kj.failed = true;
    kj.cancel = true;
    stop = true;
    wake();
}

// Writes the pairs found so far to the results file.  false: the write
// failed, the run stops, and no status may be saved (it could count a k as
// done whose pairs are not in the file).
bool Engine::flush_pairs() {
    try {
        opt.writer->flush();
        return true;
    } catch (...) {
        {
            std::lock_guard<std::mutex> lock(errmu);
            if (!fatal) fatal = std::current_exception();
        }
        stop = true;
        wake();
        return false;
    }
}

void Engine::release(const std::shared_ptr<KJob>& kj) {
    if (kj->pending.fetch_sub(1) == 1) k_done(*kj);
}

void Engine::k_done(KJob& kj) {
    if (!kj.failed) {
        std::string why;
        if (kj.timed_out) why = "timeout>" + std::to_string(opt.timeout_seconds) + "s";
        const int inc = kj.incomplete.load();
        if (inc) why += (why.empty() ? "" : ",") + incomplete_reason(inc);
        if (!why.empty()) {
            try {
                append_incomplete(kj.k, why);
            } catch (...) {                         // not recorded: the k is not finished either
                {
                    std::lock_guard<std::mutex> lock(errmu);
                    if (!fatal) fatal = std::current_exception();
                }
                stop = true;
                active.fetch_sub(1);
                wake();
                return;
            }
            std::cerr << "[incomplete] k=" << kj.k << " " << why << '\n';
        }
        done_buffer().push_back(kj.k);
        if (done_buffer().size() >= DONE_BATCH) flush_done();
        completed.fetch_add(1);
    }
    active.fetch_sub(1);
    wake();
}

void Engine::flush_done() {
    std::vector<u64>& buf = done_buffer();
    if (buf.empty()) return;
    std::sort(buf.begin(), buf.end());
    std::lock_guard<std::mutex> lock(fmu);
    for (const u64 k : buf) {
        if (k == frontier) {
            ++frontier;
            while (!ahead.empty() && *ahead.begin() == frontier) {
                ahead.erase(ahead.begin());
                ++frontier;
            }
        } else {
            ahead.insert(k);
        }
    }
    buf.clear();
}

bool Engine::take_block() {
    std::shared_ptr<Job> job;
    {
        std::lock_guard<std::mutex> lock(qmu);
        while (!queue.empty()) {
            const auto& j = queue.front();
            if (j->next_block.load(std::memory_order_relaxed) >= j->nblocks) {
                queue.pop_front();
                continue;
            }
            job = j;
            break;
        }
    }
    if (!job) return false;

    if (job->kj->cancel.load(std::memory_order_relaxed)) {
        const u64 b0 = job->next_block.exchange(job->nblocks);
        if (b0 < job->nblocks) finish_block(job, b0, job->nblocks - b0, false);
        return true;
    }
    const u64 b = job->next_block.fetch_add(1);
    if (b >= job->nblocks) return true;
    try {
        run_block(*job, b);
    } catch (...) {
        handle_exception(*job->kj);
    }
    finish_block(job, b, 1, !job->kj->cancel.load());
    return true;
}

void Engine::run_block(Job& job, u64 b) {
    KJob& kj = *job.kj;
    if (kj.cancel.load(std::memory_order_relaxed)) return;
    if (!job.q_list.empty()) {
        run_item(job, job.q_list[b]);
        return;
    }
    const u64 s = job.lo + b * job.width;
    const u64 e = (job.hi - s < job.width) ? job.hi : s + job.width - 1;
    SearchCtx ctx = kj.ctx();
    if (job.prog) {
        progression_visit(job.chain.back(), s, e, ctx, job.plan);
    } else if (opt.track_resume && children_are_prog(job.chain.back())) {
        std::vector<const Node*> chain = chain_of(job.chain);
        Path path = job.path;
        scan_prog_children(job.kj, chain, path, s, e, ctx);
    } else {
        scan_children(job.chain.back(), s, e, ctx);
    }
#ifdef AMICABLE_TRACE
    if (opt.track_resume && !kj.cancel.load())
        trace_line("DONE B " + trace_path(job.path) + " " + std::to_string(s) + " " + std::to_string(e));
#endif
}

void Engine::finish_block(const std::shared_ptr<Job>& job, u64 b, u64 count, bool processed) {
    if (opt.track_resume && processed) {
        std::lock_guard<std::mutex> lock(job->bmu);
        for (u64 i = b; i < b + count && i < job->nblocks; ++i) {
            if (i != job->first_open) { job->done_ahead.insert(i); continue; }
            ++job->first_open;
            while (!job->done_ahead.empty() && *job->done_ahead.begin() == job->first_open) {
                job->done_ahead.erase(job->done_ahead.begin());
                ++job->first_open;
            }
        }
    }
    if (job->done_blocks.fetch_add(count) + count == job->nblocks) {
        KJob& kj = *job->kj;
        if (opt.track_resume) {
            std::lock_guard<std::mutex> lock(kj.rmu);
            kj.live.erase(job->id);
        }
        release(job->kj);
    }
}

void Engine::run_item(Job& job, u64 q) {
    KJob& kj = *job.kj;
    SearchCtx ctx = kj.ctx();
    Node c;
    const BigInt qb = u64_to_bigint(q);
    if (make_child(job.chain.back(), qb, c)) {
        if (classify(c) == Step::Tail) {
            if (opt.track_resume && is_progression(c)) {
                std::vector<const Node*> chain = chain_of(job.chain);
                chain.push_back(&c);
                Path path = job.path;
                path.push_back(q);
                run_prog_node(job.kj, chain, path, ctx);
            } else {
                process(c, ctx);
            }
        } else {
            const Range r = next_range(c);
            if (r.empty) {
            } else if (r.unbounded) {
                ctx.flag(INC_UNBOUNDED);
            } else if (!bigint_fits_u64(r.hi) || bigint_to_u64(r.hi) > max_stop) {
                ctx.flag(INC_SCAN_LIMIT);
            } else {
                const u64 lo = bigint_to_u64(r.lo), hi = bigint_to_u64(r.hi);
                if (lo > hi) {
                } else if (opt.track_resume && children_are_prog(c)) {
                    std::vector<const Node*> chain = chain_of(job.chain);
                    chain.push_back(&c);
                    Path path = job.path;
                    path.push_back(q);
                    scan_prog_children(job.kj, chain, path, lo, hi, ctx);
                } else {
                    scan_children(c, lo, hi, ctx);
                }
            }
        }
    }
#ifdef AMICABLE_TRACE
    if (opt.track_resume && !kj.cancel.load()) trace_line("DONE I " + trace_path(job.path) + " " + std::to_string(q));
#endif
}

// A job for the children of g.nodes[depth] (point g.path[0 .. depth]).
std::shared_ptr<Job> Engine::new_job(const std::shared_ptr<KJob>& kj, const GenState& g, int depth) {
    std::vector<const Node*> chain;
    for (int i = 0; i <= depth; ++i) chain.push_back(&g.nodes[static_cast<std::size_t>(i)]);
    return job_from(kj, chain, Path(g.path.begin(), g.path.begin() + depth + 1));
}

// A job for the children of chain.back() (point `path`), with its own copy of the chain.
std::shared_ptr<Job> Engine::job_from(const std::shared_ptr<KJob>& kj, const std::vector<const Node*>& chain,
                                      const Path& path) {
    std::shared_ptr<Job> job(new Job());
    job->kj = kj;
    job->chain.reserve(chain.size());
    for (const Node* n : chain) job->chain.push_back(*n);
    job->chain[0].parent = nullptr;
    for (std::size_t i = 1; i < job->chain.size(); ++i) job->chain[i].parent = &job->chain[i - 1];
    job->path = path;
    return job;
}

// The members of a Progression's class, [first, last], as blocks of u: from
// max(first, start), with a width that holds about 64 members when the class
// is sparse.  false: the range ends beyond 2^64 (it is walked whole).
bool Engine::prog_blocks(const BigInt& first, const BigInt& last, const BigInt& modulus, u64 start,
                         u64& lo, u64& hi, u64& width) const {
    if (!bigint_fits_u64(last) || bigint_to_u64(last) > max_stop) return false;
    lo = std::max(bigint_to_u64(first), start);
    hi = bigint_to_u64(last);
    width = block_width(lo);
    if (lo <= hi && modulus >= 64) {
        if (!bigint_fits_u64(modulus) || bigint_to_u64(modulus) > (hi - lo) / 64) width = hi - lo + 1;
        else width = std::max(width, bigint_to_u64(modulus) * 64);
    }
    return true;
}

// Runs the Progression tail of chain.back() (point `path`) on this thread.
// Its plan is made here, by the thread that runs the tail, not by the
// generator.  In a single-k run a long range of u is not walked here but
// queued in blocks, at the front of the queue: every thread joins in, and the
// resume point keeps moving inside it.
void Engine::run_prog_node(const std::shared_ptr<KJob>& kj, const std::vector<const Node*>& chain,
                           const Path& path, SearchCtx& ctx) {
    progression_tail(*chain.back(), ctx, [&](const BigInt& first, const BigInt& last, const BigInt& modulus,
                                             const std::function<ProgressionPlan()>& share) {
        u64 lo = 0, hi = 0, width = 0;
        if (!prog_blocks(first, last, modulus, 0, lo, hi, width)) return false;
        if (hi - lo < width) return false;           // short: walked here
        std::shared_ptr<Job> job = job_from(kj, chain, path);
        job->prog = true;
        job->plan = share();
        job->lo = lo;
        job->hi = hi;
        job->width = width;
        job->nblocks = (hi - lo) / width + 1;
#ifdef AMICABLE_TRACE
        trace_line("SPLIT " + trace_path(path) + " " + std::to_string(lo) + " " + std::to_string(hi));
#endif
        push_job(kj, job, true);
        return true;
    });
}

// scan_children for a node whose children are Progression tails, with each
// tail run by run_prog_node (the same work, but a long tail is shared out).
void Engine::scan_prog_children(const std::shared_ptr<KJob>& kj, std::vector<const Node*>& chain, Path& path,
                                u64 lo, u64 hi, SearchCtx& ctx) {
    if (hi < lo) return;
    const Node& parent = *chain.back();
    primesieve::iterator it(prime_iter_start(lo), hi);
    Node child;
    BigInt qb;
    u64 q;
    chain.push_back(&child);
    path.push_back(0);
    while ((q = it.next_prime()) <= hi) {
        if (ctx.cancelled()) break;
        if (parent.sk->k % q == 0) continue;
        qb = u64_to_bigint(q);
        if (!make_child(parent, qb, child)) continue;
        if (classify(child) != Step::Tail || !is_progression(child)) { process(child, ctx); continue; }
        path.back() = q;
        run_prog_node(kj, chain, path, ctx);
    }
    chain.pop_back();
    path.pop_back();
}

// Queues a filled-in job (sweep or batch).  It is registered for the resume
// point before the generator moves past it, or, for a piece split off by the
// thread running a block (`spawned`), before that block is marked finished.
// Spawned pieces go to the front of the queue and do not wait for it to shrink.
void Engine::push_job(const std::shared_ptr<KJob>& kj, std::shared_ptr<Job>& job, bool spawned) {
    if (!job) return;
    if (!job->q_list.empty()) job->nblocks = job->q_list.size();
    if (opt.track_resume) {
        std::lock_guard<std::mutex> lock(kj->rmu);
        job->id = kj->next_id++;
        kj->live[job->id] = job;
    }
    kj->pending.fetch_add(1);
    {
        std::lock_guard<std::mutex> lock(qmu);
        if (spawned) {
            // The queue holds the pieces split off by running blocks, in search
            // order, then the generator's jobs.  A split-off piece comes from a
            // block taken from the front, so it lies before every block not yet
            // taken; keeping these in order lets the threads work through them
            // the way the search visits them, and the resume point move on.
            job->spawned = true;
            auto it = queue.begin();
            while (it != queue.end() && (*it)->spawned && !(job->path < (*it)->path)) ++it;
            queue.insert(it, job);
        } else {
            queue.push_back(job);
        }
    }
    job.reset();
    wake();
    if (spawned) return;
    // keep the queue short: the generator helps until the others catch up
    for (;;) {
        std::size_t queued = 0;
        {
            std::lock_guard<std::mutex> lock(qmu);
            queued = queue.size();
        }
        if (queued <= static_cast<std::size_t>(2 * nthreads_) || kj->cancel.load() || stop.load()) break;
        if (!take_block()) std::this_thread::sleep_for(std::chrono::milliseconds(1));
    }
}

// The generator's point: p[0 .. len) with the last entry replaced by `last`.
void Engine::set_gen(KJob& kj, const Path& p, std::size_t len, u64 last) {
    if (!opt.track_resume) return;
    std::lock_guard<std::mutex> lock(kj.genmu);
    kj.gen_pos.assign(p.begin(), p.begin() + static_cast<std::ptrdiff_t>(len));
    if (len > 0) kj.gen_pos[len - 1] = last;
}

// A Progression tail at g.nodes[depth] (point g.path[0 .. depth]) that the
// resume point enters, in the generator: queues its u from the point's entry,
// exactly, in blocks.  true: queued, or nothing to do.  false: the caller runs
// the tail whole (a range beyond 2^64, walked with big integers; or, when not
// resumed, a short range).
bool Engine::split_progression(const std::shared_ptr<KJob>& kj, const GenState& g, int depth, bool on_path,
                               SearchCtx& ctx) {
    const Node& c = g.nodes[static_cast<std::size_t>(depth)];
    BigInt first, last, modulus;
    ProgressionPlan plan;
    if (!progression_range(c, ctx, first, last, modulus, &plan)) return true;
    const Path& R = opt.resume;
    const std::size_t ui = static_cast<std::size_t>(depth) + 1;   // index of u in R
    const bool resumed = on_path && ui < R.size();
    u64 lo = 0, hi = 0, width = 0;
    if (!prog_blocks(first, last, modulus, resumed ? R[ui] : 0, lo, hi, width)) return false;
    if (lo > hi) return true;
    if (hi - lo < width && !resumed) return false;   // short: one piece, run whole
    std::shared_ptr<Job> job = new_job(kj, g, depth);
    job->prog = true;
    job->plan = plan;
    job->lo = lo;
    job->hi = hi;
    job->width = width;
    job->nblocks = (hi - lo) / width + 1;
    push_job(kj, job);
    return true;
}

void Engine::generate(const std::shared_ptr<KJob>& kj) {
    SearchK& sk = kj->sk;
    SearchCtx ctx = kj->ctx();
    const Path& R = opt.resume;
    const u64 nroots = sk.roots.size();
    bool resume_this_k = opt.track_resume && kj->k == opt.start_k && !R.empty();
    if (resume_this_k && R[0] >= nroots) {       // not a point of this search: start over
        std::cerr << "[single-k] resume point (" << path_text(R) << ") names root " << R[0] << " of " << nroots
                  << ": ignored, searching k=" << kj->k << " from the start\n";
        resume_this_k = false;
    }
    GenState g;
    std::size_t max_slots = 0;
    for (const Config& c : sk.configs) max_slots = std::max(max_slots, c.slots.size());
    g.nodes.resize(max_slots + 2);               // never reallocated: children point at parents
    for (u64 ri = 0; ri < nroots; ++ri) {
        if (halted(*kj)) return;
        if (resume_this_k && ri < R[0]) continue;
        g.path.assign(1, ri);
        set_gen(*kj, g.path, 1, ri);

        Node& n0 = g.nodes[0];
        root_node(sk, static_cast<int>(ri), n0);
        const bool root_on_path = resume_this_k && ri == R[0];
        if (classify(n0) == Step::Tail) {
            if (opt.track_resume && is_progression(n0)) {
                // the root is a Progression tail: its u from the resume point's
                // entry, exactly, or run here with a long range shared out
                if (root_on_path && R.size() > 1) {
                    if (split_progression(kj, g, 0, true, ctx)) continue;
                    process(n0, ctx);
                } else {
                    run_prog_node(kj, std::vector<const Node*>{&n0}, g.path, ctx);
                }
#ifdef AMICABLE_TRACE
                if (!halted(*kj)) trace_line("DONE R " + std::to_string(ri));
#endif
                continue;
            }
            process(n0, ctx);
#ifdef AMICABLE_TRACE
            if (opt.track_resume && !halted(*kj)) trace_line("DONE R " + std::to_string(ri));
#endif
            continue;
        }
        // The generator walks the levels above `job_depth` itself and queues
        // the work under each node at job_depth: the last scanned level, so
        // a queued block holds only tails.  In a single-k run a Progression
        // tail, whose u is walked like one more level, is planned by the
        // thread that runs it (run_prog_node), which shares a long range of u
        // out in blocks; the generator never plans tails, so it cannot hold
        // the other threads up.  A range run uses the same depth, so idle
        // threads can join a k that runs much longer than the others.
        const RootShape& shape = *n0.root->shape;
        const int job_depth = std::max(1, shape.tail_depth - 1);
        if (!expand(kj, g, 0, job_depth, root_on_path, ctx)) return;
    }
}

// Walks the children of g.nodes[d] (d < job_depth).  `on_path`: g.nodes[d]
// lies on the resume point R, so its children before R[d + 1] are finished.
// false: stopped (time limit or fatal error).
bool Engine::expand(const std::shared_ptr<KJob>& kj, GenState& g, int d, int job_depth, bool on_path,
                    SearchCtx& ctx) {
    const Node& n = g.nodes[static_cast<std::size_t>(d)];
    const Path& R = opt.resume;
    const std::size_t ri = static_cast<std::size_t>(d) + 1;    // index of this level's prime in R
    const Range r = next_range(n);
    if (r.empty) return true;
    if (r.unbounded) { ctx.flag(INC_UNBOUNDED); return true; }
    if (!bigint_fits_u64(r.hi) || bigint_to_u64(r.hi) > max_stop) { ctx.flag(INC_SCAN_LIMIT); return true; }
    u64 lo = bigint_to_u64(r.lo);
    const u64 hi = bigint_to_u64(r.hi);
    const bool path_here = on_path && ri < R.size();
    if (path_here && R[ri] > lo) lo = R[ri];
    if (lo > hi) return true;

    const bool items = (d + 1 == job_depth);     // children are queued, not walked here
    // A child whose remaining work is a tail or a short range has nothing to
    // share, so those children themselves are shared out in batches.  In a
    // range run this lets idle threads join a k that takes much longer than
    // the others, instead of leaving it to the one thread that started it.
    const bool batching = true;
    constexpr std::size_t BATCH = 32;
    std::shared_ptr<Job> batch;
    Node& child = g.nodes[ri];
    BigInt qb;
    g.path.push_back(0);
    const std::size_t plen = g.path.size();
    primesieve::iterator it(prime_iter_start(lo), hi);
    u64 q;
    bool ok = true;
    while ((q = it.next_prime()) <= hi) {
        if (halted(*kj)) { ok = false; break; }
        if (kj->k % q == 0) continue;
        g.path.back() = q;
        // the resume point: children in a batch not yet queued are not finished
        set_gen(*kj, g.path, plen, batch ? batch->q_list.front() : q);
        qb = u64_to_bigint(q);
        if (!make_child(n, qb, child)) continue;
        const bool child_on_path = path_here && q == R[ri];
        if (!items) {
            if (!expand(kj, g, d + 1, job_depth, child_on_path, ctx)) { ok = false; break; }
            continue;
        }
        auto add_to_batch = [&]() {
            if (!batch) {
                batch = new_job(kj, g, d);
                batch->lo = 0;
            }
            batch->q_list.push_back(q);
#ifdef AMICABLE_TRACE
            // test builds: a slow generator, so its own point (with a batch still
            // being filled) becomes the resume point once the workers catch up
            static const long gen_sleep_us = [] {
                const char* v = std::getenv("AMICABLE_TEST_GEN_SLEEP_US");
                return v ? std::atol(v) : 0L;
            }();
            if (gen_sleep_us > 0) std::this_thread::sleep_for(std::chrono::microseconds(gen_sleep_us));
#endif
            if (batch->q_list.size() >= BATCH) push_job(kj, batch);
        };
        if (classify(child) == Step::Tail) {
            // a Progression tail is planned (and split) by the thread that runs
            // it, unless the resume point names a u inside it: then it starts
            // exactly there
            if (batching && child_on_path && ri + 1 < R.size() && is_progression(child) &&
                split_progression(kj, g, d + 1, child_on_path, ctx)) continue;
            if (batching) add_to_batch();
            else process(child, ctx);
            continue;
        }
        const Range r1 = next_range(child);
        if (r1.empty) continue;
        if (r1.unbounded) { ctx.flag(INC_UNBOUNDED); continue; }
        if (!bigint_fits_u64(r1.hi) || bigint_to_u64(r1.hi) > max_stop) { ctx.flag(INC_SCAN_LIMIT); continue; }
        u64 lo1 = bigint_to_u64(r1.lo);
        const u64 hi1 = bigint_to_u64(r1.hi);
        // The resume point (..., child, q, u) lies inside the Progression tail
        // of the child's child q: that tail starts exactly at u, the child's
        // other children after q.
        if (batching && child_on_path && ri + 2 < R.size() && children_are_prog(child)) {
            const u64 gq = R[ri + 1];
            Node& gc = g.nodes[ri + 1];
            g.path.push_back(gq);
            if (gq >= lo1 && gq <= hi1 && make_child(child, u64_to_bigint(gq), gc) &&
                classify(gc) == Step::Tail && is_progression(gc)) {
                if (!split_progression(kj, g, d + 2, true, ctx)) process(gc, ctx);
                lo1 = gq + 1;
            }
            g.path.pop_back();
        }
        // a child on the resume point keeps its exact start: never batched
        const bool resumed = child_on_path && ri + 1 < R.size();
        if (resumed && R[ri + 1] > lo1) lo1 = R[ri + 1];
        if (lo1 > hi1) continue;
        const u64 width = block_width(lo1);
        if (hi1 - lo1 < width && !resumed) {
            if (batching) add_to_batch();
            else scan_children(child, lo1, hi1, ctx);
            continue;
        }
        std::shared_ptr<Job> job = new_job(kj, g, d + 1);
        job->lo = lo1;
        job->hi = hi1;
        job->width = width;
        job->nblocks = (hi1 - lo1) / width + 1;
        push_job(kj, job);
    }
    if (ok && batch && !halted(*kj)) push_job(kj, batch);
    g.path.pop_back();
    return ok;
}

void Engine::run_k(u64 k) {
    std::shared_ptr<KJob> kj(new KJob(k, *opt.writer));
    kj->started_ms = now_ms();
    if (opt.timeout_seconds > 0 || opt.track_resume) {
        // the registry is only read for the time limit and the single-k status
        std::lock_guard<std::mutex> lock(regmu);
        registry.push_back(kj);
        if (opt.track_resume) single_job = kj;
    }
    try {
        if (build_search_k(k, *opt.hash, kj->sk)) {
            if (opt.track_resume) roots_total = kj->sk.roots.size();
            generate(kj);
        }
        // generate() returns early once another k has hit a fatal error: then this
        // k was not searched completely and must not count as finished
        if (stop.load()) kj->failed = true;
    } catch (...) {
        handle_exception(*kj);
    }
    {
        std::lock_guard<std::mutex> lock(kj->genmu);
        kj->gen_done = true;
    }
    release(kj);
}

void Engine::worker() {
    while (!stop.load(std::memory_order_relaxed)) {
        if (take_block()) continue;

        if (next_k.load(std::memory_order_relaxed) < stop_k) {
            active.fetch_add(1);
            const u64 k = next_k.fetch_add(1);
            if (k < stop_k && k >= opt.start_k) {
                run_k(k);
                continue;
            }
            active.fetch_sub(1);
        }
        flush_done();
        if (active.load() == 0) {
            std::lock_guard<std::mutex> lock(qmu);
            if (queue.empty()) break;
        }
        std::unique_lock<std::mutex> lock(wmu);
        sleepers.fetch_add(1);
        wcv.wait_for(lock, std::chrono::milliseconds(2));
        sleepers.fetch_sub(1);
    }
    flush_done();
}

EngineStatus Engine::status() {
    EngineStatus st;
    st.completed_k = completed.load();
    st.incomplete_k = incomplete_count.load();
    {
        std::lock_guard<std::mutex> lock(skipmu);
        st.incomplete_reason = last_reason;
    }
    {
        std::lock_guard<std::mutex> lock(fmu);
        st.resume_k = frontier;
    }
    st.next_k = std::min(next_k.load(), stop_k);
    st.active_k = active.load();
    st.pairs = opt.writer ? opt.writer->total_pairs.load() : 0;
    st.elapsed_seconds = static_cast<u64>(now_ms() / 1000);
    if (opt.track_resume) {
        std::shared_ptr<KJob> kj;
        {
            std::lock_guard<std::mutex> lock(regmu);
            kj = single_job.lock();
        }
        if (kj) seen_flags |= kj->incomplete.load();
        if (kj && !kj->cancel.load()) {
            // The resume point is the smallest of the generator's point and the
            // first unfinished block of every queued job.  The generator's point
            // is read first: a job it has moved past is already registered in
            // `live` (or finished) when `live` is read.
            bool have = false;
            Path best;
            {
                std::lock_guard<std::mutex> lock(kj->genmu);
                if (!kj->gen_done) {
                    best = kj->gen_pos;
                    have = true;
                    last_current = kj->gen_pos;
                }
            }
            Path cand;
            std::lock_guard<std::mutex> lock(kj->rmu);
            for (const auto& [id, weak] : kj->live) {
                auto job = weak.lock();
                if (!job) continue;
                {
                    std::lock_guard<std::mutex> bl(job->bmu);
                    if (job->first_open >= job->nblocks) continue;
                    cand = job->path;
                    // a batch: every child before its first unfinished one is done;
                    // a sweep: every prime before its first unfinished block
                    cand.push_back(job->q_list.empty() ? job->lo + job->first_open * job->width
                                                       : job->q_list[job->first_open]);
                }
                if (!have || cand < best) { best = cand; have = true; }
            }
            if (have) last_resume = best;
#ifdef AMICABLE_TRACE
            if (have) trace_line("STATUS " + trace_path(best));
#endif
        }
        st.resume = last_resume;
        st.current = last_current;
        st.roots_total = roots_total;
        st.flags = seen_flags;
    }
    st.timed_out = any_timeout.load();
    return st;
}

EngineStatus Engine::run() {
    int nthreads = opt.threads;
    if (nthreads <= 0) {
        nthreads = static_cast<int>(std::thread::hardware_concurrency());
        if (nthreads <= 0) nthreads = 4;
    }
    nthreads_ = nthreads;
    if (opt.track_resume) last_resume = opt.resume;

    std::vector<std::thread> threads;
    running_workers = nthreads;
    for (int i = 0; i < nthreads; ++i) {
        threads.emplace_back([this]() {
            use_full_long_double_precision();
            worker();
            running_workers.fetch_sub(1);
            wake();
            { std::lock_guard<std::mutex> lock(donemu); }
            donecv.notify_all();
        });
    }

    // Ticks follow the clock, not a count of sleeps: a sleep can last longer
    // than asked (on Windows by up to a timer period, 15.6 ms by default), and
    // writing the status file takes time, so counting 240 sleeps of 250 ms
    // drifted by seconds per minute.  Status once a second, the report every
    // report_seconds, both measured from the start.
    auto tick = std::chrono::milliseconds(250);
#ifdef AMICABLE_TRACE
    // test builds: a resume point every few milliseconds, to test many of them
    std::int64_t test_tick = 0;
    if (const char* t = std::getenv("AMICABLE_TEST_TICK_MS")) test_tick = std::atoll(t);
    if (test_tick > 0) tick = std::chrono::milliseconds(test_tick);
#endif
    auto next_wake = Clock::now();
    std::int64_t next_status_ms = 1000;
    const std::int64_t report_ms = static_cast<std::int64_t>(opt.report_seconds) * 1000;
    std::int64_t next_report_ms = report_ms;
    std::vector<std::shared_ptr<KJob>> expired;
    while (running_workers.load() > 0) {
        next_wake += tick;
        {
            std::unique_lock<std::mutex> lock(donemu);
            donecv.wait_until(lock, next_wake, [this] { return running_workers.load() == 0; });
        }
        if (running_workers.load() == 0) break;          // all done: the final status follows the join
        if (Clock::now() - next_wake > std::chrono::seconds(1)) next_wake = Clock::now();   // no catch-up burst
        {
            const std::int64_t now = now_ms();
            std::lock_guard<std::mutex> lock(regmu);
            std::size_t w = 0;
            for (std::size_t i = 0; i < registry.size(); ++i) {
                auto kj = registry[i].lock();
                if (!kj) continue;
                registry[w++] = registry[i];
                if (opt.timeout_seconds > 0 && !kj->cancel.load() &&
                    now - kj->started_ms > static_cast<std::int64_t>(opt.timeout_seconds) * 1000)
                    expired.push_back(kj);
            }
            registry.resize(w);
        }
        if (!expired.empty()) {
            if (opt.track_resume) (void)status();        // freeze the resume point first
            for (auto& kj : expired) {
                kj->timed_out = true;
                kj->cancel = true;
                any_timeout = true;
                std::cerr << "[timeout] k=" << kj->k << " exceeded " << opt.timeout_seconds << "s\n";
            }
            expired.clear();
        }
        const std::int64_t ms = now_ms();
#ifdef AMICABLE_TRACE
        if (test_tick > 0 && opt.track_resume) (void)status();
#endif
        if (ms < next_status_ms) continue;
        next_status_ms = (ms / 1000 + 1) * 1000;
        const EngineStatus st = status();
        if (!flush_pairs()) continue;                    // the pairs of every k the snapshot counts as done
        if (opt.on_tick) opt.on_tick(st);
        if (report_ms > 0 && ms >= next_report_ms) {
            next_report_ms = (ms / report_ms + 1) * report_ms;
            if (opt.track_resume) {
                std::cerr << "[single-k] root " << (st.current.empty() ? 0 : st.current[0]) << "/" << st.roots_total
                          << " at (" << path_text(st.current) << ") resume=(" << path_text(st.resume) << ")"
                          << " pairs=" << st.pairs << " elapsed=" << st.elapsed_seconds << "s\n";
            } else {
                std::cerr << "[multi-k] checked=" << st.completed_k << " resume_k=" << st.resume_k
                          << " in_flight=" << st.active_k << " incomplete=" << st.incomplete_k
                          << " pairs=" << st.pairs << " elapsed=" << st.elapsed_seconds << "s\n";
            }
        }
    }
    for (auto& t : threads) t.join();

    EngineStatus st = status();
    const bool flushed = flush_pairs();
    st.finished = !fatal && !stop.load();
    if (flushed && opt.on_tick) opt.on_tick(st);
    if (fatal) std::rethrow_exception(fatal);
    return st;
}

} // namespace

EngineStatus run_engine(const EngineOptions& options) {
    if (options.writer == nullptr) throw std::invalid_argument("run_engine: writer required");
    if (options.hash == nullptr) throw std::invalid_argument("run_engine: hash required");
    Engine engine(options);
    return engine.run();
}

} // namespace amicable
