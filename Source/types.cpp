#include "types.h"
#include "skip_file.h"

#include "numeric_utils.h"

#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <utility>

namespace amicable {

namespace {

// Smaller members of the pairs already in a results file (each pair is a
// header line followed by "smaller=..." and "larger=...").
std::unordered_set<std::string> pairs_in_file(const std::filesystem::path& file) {
    std::unordered_set<std::string> known;
    std::ifstream in(file);
    std::string line;
    bool expect_small = true;
    std::string pending;                        // smaller member waiting for its larger member
    while (std::getline(in, line)) {
        const auto eq = line.find('=');
        const bool number = eq != std::string::npos && eq > 0 &&
                            line.find_first_not_of("0123456789") == eq;
        if (!number) { expect_small = true; pending.clear(); continue; }
        if (expect_small) pending = line.substr(0, eq);
        else if (!pending.empty()) { known.insert(pending); pending.clear(); }
        expect_small = !expect_small;
    }
    return known;
}

} // namespace

ResultWriter::ResultWriter(const std::filesystem::path& file, std::string author, std::string year)
    : path_(file), author_(std::move(author)), year_(std::move(year))
{
    FileLock lock(path_);
    known_ = pairs_in_file(path_);
    std::ofstream probe(path_, std::ios::out | std::ios::app);
    if (!probe)
        throw std::runtime_error("Cannot open output file: " + file.string());
}

void ResultWriter::refresh_known() {
    std::lock_guard<std::mutex> lock(mu_);
    FileLock flock(path_);
    for (const std::string& n : pairs_in_file(path_)) known_.insert(n);
}

void ResultWriter::write(
    const std::string& type,
    const std::string& small_str, const std::string& small_factors,
    const std::string& large_str, const std::string& large_factors)
{
    std::ostringstream block;
    block << type << ' ' << author_ << ' ' << year_ << '\n'
          << small_str << '=' << small_factors << '\n'
          << large_str << '=' << large_factors << "\n\n";
    const std::string text = block.str();

    std::lock_guard<std::mutex> lock(mu_);
    ++total_pairs;
    if (!known_.insert(small_str).second) {      // found before (a resumed or retried k)
        ++repeated_pairs;
        return;
    }
    std::cout << text;
    std::cout.flush();
    // opened per pair under the lock: another run of this hash (a range run
    // next to a skipped run) may append to the same file
    FileLock flock(path_);
    std::ofstream out(path_, std::ios::out | std::ios::app);
    out << text;
    out.flush();
    if (!out) throw std::runtime_error("Cannot write output file: " + path_.string());
#ifdef AMICABLE_TRACE
    trace_write("PAIR " + small_str);
#endif
}

#ifdef AMICABLE_TRACE
void trace_write(const std::string& line) {
    static std::mutex mu;
    static const char* file = std::getenv("AMICABLE_TRACE_FILE");
    if (!file) return;
    std::lock_guard<std::mutex> lock(mu);
    if (std::FILE* f = std::fopen(file, "a")) { std::fprintf(f, "%s\n", line.c_str()); std::fclose(f); }
}
#endif

OutputSink::OutputSink(std::uint64_t search_k, ResultWriter& w)
    : k(search_k), writer(w) {}

void OutputSink::write_pair_with_factors(
    const BigInt& n1,
    const BigInt& n2,
    const FactorBuffer& n1_factors,
    const FactorBuffer& n2_factors)
{
    const bool n1_is_smaller = n1 < n2;
    const BigInt& smaller = n1_is_smaller ? n1 : n2;
    const BigInt& larger = n1_is_smaller ? n2 : n1;
    const FactorBuffer& small_factors = n1_is_smaller ? n1_factors : n2_factors;
    const FactorBuffer& large_factors = n1_is_smaller ? n2_factors : n1_factors;
    const std::string small_str = smaller.get_str();
    const std::string large_str = larger.get_str();
    const std::string key = small_str + '|' + large_str;

    {
        std::lock_guard<std::mutex> lock(mu);
        if (!seen.insert(key).second) return;
        ++pairs_found;
    }

    writer.write(sech_type(small_factors, large_factors),
                 small_str, format_factorization(small_factors),
                 large_str, format_factorization(large_factors));
}

} // namespace amicable
