#ifndef AMICABLE_GENERAL_H
#define AMICABLE_GENERAL_H

// Exhaustive search for the amicable pairs of one hash and one A1 = k.
//
// Notation (see hash_spec.h): N1 = A1 * prod P^a (smaller), N2 = A1 * prod Q^c.
// Primes of A1 that sit in the hash with b > 0 ("bound" slots) are tried in
// every possible way (finite).  The other ("free") primes do not divide A1.
//
// With K1 = A1 * prod(bound P^a), K2 = A1 * prod(bound Q^c), s1 = sigma(K1),
// s2 = sigma(K2), X = prod(free P^a), Y = prod(free Q^c) the pair conditions
// are exactly
//
//     s1*sigma(X) = s2*sigma(Y) = K1*X + K2*Y,      K1*X < K2*Y.
//
// Search: all free primes are taken in increasing order *across both members*
// (each interleaving of the two sorted lists is its own "root").  For the next
// prime q every later prime is > q, which gives a rigorous, finite range for q
// from the abundancies x = sigma(N1)/N1, y = sigma(N2)/N2:
//     (x-1)(y-1) = 1,  x > 2  (N1 < N2),  y < 2.
// All range tests are done in exact integer arithmetic.  The last two or three
// primes are never scanned: they are solved exactly (closed forms, a divisor
// condition, or a congruence), see general.cpp.

#include "divisors.h"
#include "factoring.h"
#include "hash_spec.h"
#include "types.h"

#include <atomic>
#include <cstdint>
#include <functional>
#include <memory>
#include <string>
#include <utility>
#include <vector>

namespace amicable {

using FacList = std::vector<std::pair<BigInt, int>>;   // (prime, exponent)

// full factorisation of n >= 1 (hurchalla up to 128 bits, FLINT beyond)
void factor_any(const BigInt& n, FacList& out);

struct FreeSlot {
    int side = 0;                 // 0: smaller member N1, 1: larger member N2
    int pos = 0;                  // position among all slots of that side
    int exp = 1;
    std::uint64_t lo = 2;         // static limits from the bound primes around it
    std::uint64_t hi = 0;         // 0 = none
};

struct Config {
    std::vector<std::uint64_t> slot_prime[2];   // bound slots: their prime of A1; free: 0
    BigInt K1, K2, s1, s2;
    FacList s1f, s2f;                           // only filled when s_nat_ok is false
    std::vector<FreeSlot> slots;                // the free slots
    std::vector<int> free_ids[2];               // free slot ids per side, in side order
    std::vector<BigInt> strip_big;              // known primes (A1, s1, s2) above 2^64 (rare)
    std::vector<std::uint64_t> strip64;         // known primes (A1, s1, s2) below 2^64
    struct Div128 { std::uint64_t p; unsigned __int128 inv, lim; };
    std::vector<Div128> strip_div;              // odd strip64 primes: exact-division constants
    NatFactors s_nat[2];                        // s1f / s2f with 128-bit primes
    bool s_nat_ok[2] = {false, false};
};

// An ordering of the free primes; the same for every k and configuration of
// a hash, so it is built once and shared.
struct RootShape {
    std::vector<int> order;                     // free slot ids, smallest prime first
    bool last2_free = false;                    // the last two (one per side) in either order
    bool float3 = false;                        // last three {u < w on one side, v on the other}:
                                                // v may sit anywhere among them
    bool split3 = false;                        // prefix = primes of one member only, tail
                                                // [u, v, w]: v the last of that member, u < w
                                                // the other member's two, anywhere (only their
                                                // own order and limits): one root for all
                                                // interleavings
    bool need_sig[2] = {true, true};            // does the tail need sigma(p^e) factorisations of a side
    int tail_depth = 0;                         // the depth at which the tail takes over
    bool prog_tail = false;                     // that tail is a Progression (its u can be split up)
};

struct Root {
    int config = 0;
    const RootShape* shape = nullptr;
};

struct SearchK {
    std::uint64_t k = 0;
    BigInt kb;
    std::vector<std::pair<std::uint64_t, int>> kf;   // factorisation of k
    const HashSpec* hash = nullptr;
    std::vector<Config> configs;
    std::vector<Root> roots;
};

// false when no configuration exists for this k (nothing to search)
bool build_search_k(std::uint64_t k, const HashSpec& hash, SearchK& out);

// One point of the search: the first `depth` primes of root->order are chosen.
struct Node {
    const SearchK* sk = nullptr;
    const Config* cfg = nullptr;
    const Root* root = nullptr;
    const Node* parent = nullptr;
    int depth = 0;
    int slot = -1;                              // the free slot that `prime` fills (depth > 0)
    BigInt prime;                               // the prime chosen at this node (depth > 0)
    BigInt sx, px, sy, py;                      // s1*sigma(X0), K1*X0, s2*sigma(Y0), K2*Y0
    FacList sig;                                // factorisation of sigma(prime^exp)
    NatFactors sig_nat;                         // the same with 128-bit primes
    bool sig_nat_ok = false;
    bool sig_done = false;                      // false: not computed (the tail does not need it)
    // sx, px, sy, py as 128-bit integers, filled on first use by node_nat()
    // (-1: not yet, 0: one does not fit, 1: nat[] holds them); reset whenever
    // sx..py are set
    mutable signed char nat_state = -1;
    mutable i128 nat[4] = {0, 0, 0, 0};
};

void root_node(const SearchK& sk, int root, Node& out);

// Rigorous range of the next prime.  lo/hi are exact; `unbounded` means the
// range could not be capped (only possible for k with astronomically large
// bounds; such a k is reported as incomplete, never silently skipped).
struct Range {
    bool empty = true;
    bool unbounded = false;
    BigInt lo, hi;
};

enum class Step { Tail, Enumerate };
Step classify(const Node& n);
Range next_range(const Node& n);
// slot < 0: the next slot of the root's order; otherwise that slot (a tail
// that solves its primes in a different order than the root lists them)
bool make_child(const Node& parent, const BigInt& q, Node& child, int slot = -1);

// Why a k could not be searched completely (bit flags, OR-ed into KJob)
enum Incomplete : int {
    INC_NONE = 0,
    INC_UNBOUNDED = 1,        // a bound could not be capped
    INC_SCAN_LIMIT = 2,       // a prime range past primesieve's limit (~1.8e19)
};

struct SearchCtx {
    OutputSink* sink = nullptr;
    const std::atomic<bool>* cancel = nullptr;
    std::atomic<int>* incomplete = nullptr;
    [[nodiscard]] bool cancelled() const noexcept {
        return cancel && cancel->load(std::memory_order_relaxed);
    }
    void flag(int why) const noexcept {
        if (incomplete) incomplete->fetch_or(why, std::memory_order_relaxed);
    }
};

// Everything below this node (tails solved exactly, other levels scanned).
void process(const Node& n, SearchCtx& ctx);

// scan the primes of [lo, hi] (exclusive of primes dividing k) as children
void scan_children(const Node& n, std::uint64_t lo, std::uint64_t hi, SearchCtx& ctx);

// A node whose tail is a Progression (proof §9.4): its prime u runs through
// one residue class u == res (mod modulus).  progression_range gives the first
// and last candidates (false: no u can work, or the k was flagged);
// progression_visit runs the tail for the class members in [lo, hi] only, in
// increasing order.  process(n) is the same as visiting the whole range.
//
// A ProgressionPlan is the plan of one such tail (u's class, its first and
// last candidates, the primes after u), opaque.  It depends only on the node,
// so the pieces of a split tail share the one plan instead of each making it
// again; progression_visit without a plan makes it itself.
using ProgressionPlan = std::shared_ptr<const void>;
bool is_progression(const Node& n);
bool progression_range(const Node& n, SearchCtx& ctx, BigInt& first, BigInt& hi, BigInt& modulus,
                       ProgressionPlan* plan = nullptr);
void progression_visit(const Node& n, std::uint64_t lo, std::uint64_t hi, SearchCtx& ctx,
                       const ProgressionPlan& plan = ProgressionPlan());
// The Progression tail of n with a choice after planning: split(first, hi,
// modulus, share) returning true means the caller takes over the class members
// (and visits them later with progression_visit, in pieces; share() hands it
// the plan); false means they are visited here, all of them.  With split false
// this is the same as process(n).
using ProgressionSplit = std::function<bool(const BigInt&, const BigInt&, const BigInt&,
                                            const std::function<ProgressionPlan()>&)>;
void progression_tail(const Node& n, SearchCtx& ctx, const ProgressionSplit& split);

std::string describe_plan(const SearchK& sk);
std::string root_name(const SearchK& sk, int root);   // e.g. "P1<Q1<Q2<{P2,Q3}  [Q1=5]"

} // namespace amicable

#endif
