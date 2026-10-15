#ifndef AMICABLE_APP_COMMON_H
#define AMICABLE_APP_COMMON_H

// Start-up code of multi_k_searcher:
// config.txt, command line, folder layout.

#include "hash_spec.h"

#include <cstdint>
#include <filesystem>
#include <string>
#include <vector>

namespace amicable {

struct AppConfig {
    std::string hash_text = "[(1,0),(1,0)] _ [(1,0),(1,0),(1,0)]";
    std::uint64_t start_k = 1;
    std::uint64_t end_k = 0;
    std::uint64_t timeout_seconds = 0;          // range mode: give up on a k after this long
    std::uint64_t report_seconds = 60;
    std::string mode = "range";                 // range | single | skipped
    std::uint64_t single_k = 0;                 // mode = single
    std::uint64_t single_timeout_seconds = 0;   // single / skipped: time limit per k, 0 = none
    int workers = 0;
    std::string author = "Amicable-Searcher";
    std::string year;                       // empty = current year
    std::filesystem::path root;
    bool show_plan = false;

    bool hash_given = false, start_given = false, end_given = false, timeout_given = false,
         report_given = false, workers_given = false, mode_given = false;
};

[[nodiscard]] bool parse_u64(const std::string& text, std::uint64_t& out);

// "range", "single" or "skipped" (case-insensitive, a few spellings); false otherwise
[[nodiscard]] bool normalize_mode(const std::string& text, std::string& mode);
[[nodiscard]] std::filesystem::path find_root(const char* argv0);
[[nodiscard]] bool load_config_file(const std::filesystem::path& file, AppConfig& cfg);
[[nodiscard]] bool parse_common_args(int argc, char* argv[], AppConfig& cfg,
                                     std::vector<std::string>& positional, bool& help);

struct Session {
    HashSpec hash;
    std::filesystem::path data_dir;         // root/Data/<hash>
    std::string year;
};

[[nodiscard]] bool open_session(const AppConfig& cfg, Session& session, std::string& error);

} // namespace amicable

#endif
