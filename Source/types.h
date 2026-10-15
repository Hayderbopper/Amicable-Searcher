#ifndef AMICABLE_TYPES_H
#define AMICABLE_TYPES_H

#include "factoring.h"

#include <atomic>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <mutex>
#include <string>
#include <unordered_set>
#include <vector>

namespace amicable {

using i128 = __int128_t;
using u128 = __uint128_t;

// One results file shared by every k (and every thread), written in the
// sech.me/ap submission format:
//   <type> <author> <year>
//   <smaller>=<factorization>
//   <larger>=<factorization>
//   <blank line>
class ResultWriter {
public:
    ResultWriter(const std::filesystem::path& file, std::string author, std::string year);

    void write(const std::string& type,
               const std::string& small_str, const std::string& small_factors,
               const std::string& large_str, const std::string& large_factors);

    // re-reads the file's pairs (another run of this hash may have added some)
    void refresh_known();

    std::atomic<std::uint64_t> total_pairs{0};      // pairs found this run
    std::atomic<std::uint64_t> repeated_pairs{0};   // of those, already in the file (not written again)

private:
    std::mutex mu_;
    std::filesystem::path path_;
    std::string author_;
    std::string year_;
    std::unordered_set<std::string> known_;         // smaller members already in the file
};

// Per-k sink: removes duplicates found through different P3/P4 routes.
struct OutputSink {
    OutputSink(std::uint64_t search_k, ResultWriter& w);

    void write_pair_with_factors(
        const BigInt& n1,
        const BigInt& n2,
        const FactorBuffer& n1_factors,
        const FactorBuffer& n2_factors);

    std::uint64_t k = 0;
    ResultWriter& writer;
    mutable std::mutex mu;
    std::unordered_set<std::string> seen;
    std::atomic<std::uint64_t> pairs_found{0};
};

#ifdef AMICABLE_TRACE
// test builds only: appends one line to the file named by AMICABLE_TRACE_FILE
// (resume points, finished pieces and pairs written, in the order they happen)
void trace_write(const std::string& line);
#endif

} // namespace amicable

#endif
