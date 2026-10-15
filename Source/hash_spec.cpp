#include "hash_spec.h"

#include <cctype>
#include <string>
#include <vector>

namespace amicable {

namespace {

std::string slots_text(const std::vector<HashSlot>& v, char open, char close) {
    std::string out(1, open);
    for (std::size_t i = 0; i < v.size(); ++i) {
        if (i) out += ',';
        out += '(' + std::to_string(v[i].exp) + ',' + std::to_string(v[i].mult) + ')';
    }
    out += close;
    return out;
}

// every "(a,b)" in the text, in order
bool extract_pairs(const std::string& s, std::vector<HashSlot>& out, std::string& error) {
    std::size_t i = 0;
    while (i < s.size()) {
        if (s[i] != '(') { ++i; continue; }
        std::size_t j = i + 1;
        auto read_int = [&](long long& v) {
            const std::size_t start = j;
            v = 0;
            while (j < s.size() && std::isdigit(static_cast<unsigned char>(s[j]))) {
                v = v * 10 + (s[j] - '0');
                if (v > 1000) return false;
                ++j;
            }
            return j > start;
        };
        long long a = 0, b = 0;
        if (!read_int(a)) { ++i; continue; }          // an outer bracket like "((1,0),..."
        if (j >= s.size() || s[j] != ',') { error = "expected ',' inside a pair"; return false; }
        ++j;
        if (!read_int(b)) { error = "expected a number after ',' inside a pair"; return false; }
        if (j >= s.size() || s[j] != ')') { error = "expected ')' to close a pair"; return false; }
        if (a < 1) { error = "the first number of every pair (the exponent) must be >= 1"; return false; }
        out.push_back({static_cast<int>(a), static_cast<int>(b)});
        i = j + 1;
    }
    return true;
}

} // namespace

std::string HashSpec::text() const {
    return slots_text(side[0], '[', ']') + " _ " + slots_text(side[1], '[', ']');
}

std::string HashSpec::folder() const {
    return slots_text(side[0], '(', ')') + " _ " + slots_text(side[1], '(', ')');
}

bool parse_hash_spec(const std::string& text, HashSpec& out, std::string& error) {
    out = HashSpec{};
    std::string s;
    for (char c : text)
        if (!std::isspace(static_cast<unsigned char>(c))) s += c;
    if (s.empty()) { error = "empty hash"; return false; }

    std::string parts[2];
    const std::size_t sep = s.find_first_of("_|");
    if (sep != std::string::npos) {
        if (s.find_first_of("_|", sep + 1) != std::string::npos) {
            error = "use a single '_' between the two members";
            return false;
        }
        parts[0] = s.substr(0, sep);
        parts[1] = s.substr(sep + 1);
    } else {
        // two top-level brackets:  [..][..]  or  ((..))((..))
        std::vector<std::string> groups;
        int depth = 0;
        std::size_t start = 0;
        for (std::size_t i = 0; i < s.size(); ++i) {
            const char c = s[i];
            if (c == '(' || c == '[') {
                if (depth == 0) start = i;
                ++depth;
            } else if (c == ')' || c == ']') {
                if (--depth < 0) { error = "unbalanced brackets"; return false; }
                if (depth == 0) groups.push_back(s.substr(start, i - start + 1));
            }
        }
        if (depth != 0) { error = "unbalanced brackets"; return false; }
        if (groups.size() != 2) {
            error = "write the hash as  [smaller member] _ [larger member],  e.g.  "
                    "[(1,0),(1,0)] _ [(1,0),(1,0),(1,0)]";
            return false;
        }
        parts[0] = groups[0];
        parts[1] = groups[1];
    }
    for (int k = 0; k < 2; ++k) {
        if (!extract_pairs(parts[k], out.side[k], error)) return false;
        if (out.side[k].empty()) {
            error = std::string("no (exponent,multiplicity) pairs found for the ")
                  + (k == 0 ? "smaller" : "larger") + " member";
            return false;
        }
    }
    const std::size_t total = out.side[0].size() + out.side[1].size();
    if (total > 16) { error = "at most 16 primes in a hash"; return false; }
    return true;
}

} // namespace amicable
