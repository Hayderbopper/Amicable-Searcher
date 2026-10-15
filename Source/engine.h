#ifndef AMICABLE_ENGINE_H
#define AMICABLE_ENGINE_H

// Work-pool search engine of multi_k_searcher (all three modes).
//
// Every thread runs the same loop:
//   1. if a piece of a k is queued, take its next block
//   2. otherwise start the next k
// For each k the "roots" (orderings of the free primes) are walked in order,
// each prime in increasing order.  The generator (the thread that started the
// k) walks every level down to the last scanned prime and queues the work
// under each node there: a long range in blocks (a sweep), short ones 32 at
// a time (a batch).  So every idle thread can join a k that takes much longer
// than the others.  In a single-k run a block holds only tails and the resume
// point (root, q1, q2, ...) moves forward as soon as a block is finished; a
// long Progression tail is split up too.

#include "hash_spec.h"
#include "types.h"

#include <cstdint>
#include <filesystem>
#include <functional>
#include <string>
#include <vector>

namespace amicable {

struct EngineStatus {
    std::uint64_t completed_k = 0;          // k values finished (searched or reported incomplete)
    std::uint64_t resume_k = 0;             // every k below this is finished
    std::uint64_t next_k = 0;
    std::uint64_t active_k = 0;
    std::uint64_t incomplete_k = 0;         // k values written to incomplete.txt this run
    std::string incomplete_reason;          // reason of the last one ("timeout>60s", "range_beyond_2^64", ...)
    std::uint64_t pairs = 0;
    std::uint64_t elapsed_seconds = 0;
    bool finished = false;
    bool timed_out = false;
    // single-k only (track_resume): everything before the point
    // (root, q1, q2, ...) is done, in lexicographic order
    std::vector<std::uint64_t> resume;
    std::uint64_t roots_total = 0;
    std::vector<std::uint64_t> current;     // where the generator is (root, q1, ...)
    int flags = 0;                          // single-k: INC_* bits raised so far (live)
};

struct EngineOptions {
    const HashSpec* hash = nullptr;
    std::uint64_t start_k = 1;
    std::uint64_t stop_k = 0;               // exclusive; 0 = no end
    int threads = 0;                        // 0 = all cores
    std::uint64_t timeout_seconds = 0;      // per k; 0 = none
    std::uint64_t report_seconds = 60;
    ResultWriter* writer = nullptr;
    std::filesystem::path incomplete_file;  // "k reason" lines for k not searched completely

    // single-k resume point (track_resume): (root, q1, q2, ...), empty = start
    bool track_resume = false;
    std::vector<std::uint64_t> resume;

    std::function<void(const EngineStatus&)> on_tick;   // about once a second
};

EngineStatus run_engine(const EngineOptions& options);

} // namespace amicable

#endif
