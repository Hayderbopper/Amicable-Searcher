#pragma once
// long double arithmetic is meant to use the x87 unit's full 64-bit mantissa.
// Linux threads start that way, and so does the main thread of a MinGW
// program.  A thread Windows creates starts at 53 bits, and MinGW's "win32"
// thread model keeps it so for std::thread (the "posix" model, which MSYS2
// uses, resets it), so every search thread sets it explicitly.  No effect on
// other systems.  The results do not depend on it (ModD computes its remainder
// exactly, every other long double value is a hint that is checked exactly),
// but the floating hints are then the same on every build.

namespace amicable {

inline void use_full_long_double_precision() noexcept {
#if defined(_WIN32) && defined(__GNUC__) && (defined(__x86_64__) || defined(__i386__))
    unsigned short cw;
    __asm__ volatile("fnstcw %0" : "=m"(cw));
    cw = static_cast<unsigned short>((cw & ~0x0300u) | 0x0300u);   // precision control: 64 bits
    __asm__ volatile("fldcw %0" : : "m"(cw));
#endif
}

} // namespace amicable
