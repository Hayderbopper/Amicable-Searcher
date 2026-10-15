#ifndef AMICABLE_SKIP_FILE_H
#define AMICABLE_SKIP_FILE_H

// The skip file Data/<hash>/incomplete.txt (skipped.txt in the former
// Multi_K_Auto_Cached): one line per k that was not searched completely,
//
//     k reason [resume=...]
//
// written by range runs (a k that hits the per-k timeout) and worked through by
// "mode = skipped", which deletes a k's lines once that k has been searched
// completely.  When a k is stopped again (single_timeout_seconds), its line
// keeps the exact point to continue from in "resume=".
//
// Every change goes through FileLock, an exclusive lock on <file>.lock
// that works across processes, so a range run in one window can keep appending
// while a skipped run in another window rewrites the file: no line is lost.
// The results files use the same lock (two runs of one hash both append to
// multi_k_results.txt).
// A rewrite goes to <file>.tmp first and then replaces the file in one step.

#include <cstdint>
#include <filesystem>
#include <functional>
#include <string>
#include <vector>

namespace amicable {

struct SkipLine {
    std::uint64_t k = 0;        // 0: not a "k ..." line (kept as it is)
    std::string reason;         // e.g. "timeout>600s"
    std::string resume;         // text after "resume=", empty if none
    std::string raw;            // the line as read
};

// Exclusive lock on <file>.lock, across the threads of this process and
// across processes (Windows: the lock file opened without sharing; Linux:
// flock).  The OS drops it if the process dies.
class FileLock {
public:
    explicit FileLock(const std::filesystem::path& file);
    ~FileLock();
    FileLock(const FileLock&) = delete;
    FileLock& operator=(const FileLock&) = delete;

private:
#ifdef _WIN32
    void* handle_ = nullptr;
#else
    int fd_ = -1;
#endif
};

// All lines of the file (a missing file has none).  Blank lines are dropped.
[[nodiscard]] std::vector<SkipLine> read_skip_file(const std::filesystem::path& file);

[[nodiscard]] std::string format_skip_line(const SkipLine& line);

// Appends "k reason" under the lock (what a range run does).
void append_skip_line(const std::filesystem::path& file, std::uint64_t k, const std::string& reason);

// Under the lock: re-reads the file, lets edit() change the lines, and writes
// the result back (an empty result leaves an empty file).
void edit_skip_file(const std::filesystem::path& file,
                    const std::function<void(std::vector<SkipLine>&)>& edit);

// Common edits.  remove_k: deletes every line of k, returns how many.
// set_k: replaces every line of k by one line (appends it if k had none).
std::size_t remove_skip_k(const std::filesystem::path& file, std::uint64_t k);
void set_skip_k(const std::filesystem::path& file, std::uint64_t k,
                const std::string& reason, const std::string& resume);

// "key=value" lines of a status file; the first line (the state word) is
// returned under the key "state".  Missing file: empty result.
[[nodiscard]] std::vector<std::pair<std::string, std::string>>
read_status_file(const std::filesystem::path& file);

[[nodiscard]] std::string status_value(const std::vector<std::pair<std::string, std::string>>& kv,
                                       const std::string& key);

} // namespace amicable

#endif
