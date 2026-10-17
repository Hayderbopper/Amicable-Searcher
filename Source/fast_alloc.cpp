// Optional allocator: with -DAMICABLE_MIMALLOC (and -lmimalloc) every C++
// new/delete and every GMP allocation goes through mimalloc.  The search makes
// many small short-lived allocations from several threads (BigInt temporaries,
// vectors); the Windows heap behind MinGW's malloc is much slower at that than
// mimalloc.  Without the macro this file is empty.
//
// Memory that was allocated elsewhere (by the C runtime, or by a DLL such as
// libstdc++ that does not see these replacements) can still reach the free
// functions here, so each free checks who owns the pointer first.
#ifdef AMICABLE_MIMALLOC

#include <mimalloc.h>
#include <gmp.h>

#include <cstddef>
#include <cstdlib>
#include <cstring>
#include <new>

namespace {

inline bool ours(void* p) { return mi_is_in_heap_region(p); }

void release(void* p) {
    if (!p) return;
    if (ours(p)) mi_free(p);
    else std::free(p);
}

void* gmp_alloc(std::size_t n) {
    void* p = mi_malloc(n);
    if (!p) std::abort();
    return p;
}

void* gmp_realloc(void* p, std::size_t old_size, std::size_t n) {
    if (p && !ours(p)) {
        void* q = gmp_alloc(n);
        std::memcpy(q, p, old_size < n ? old_size : n);
        std::free(p);
        return q;
    }
    void* q = mi_realloc(p, n);
    if (!q) std::abort();
    return q;
}

void gmp_free(void* p, std::size_t) { release(p); }

// before every other static constructor, so no GMP number is made with the
// default functions first (the ownership check covers it if one is)
struct SetGmpAllocator {
    SetGmpAllocator() { mp_set_memory_functions(gmp_alloc, gmp_realloc, gmp_free); }
} set_gmp_allocator __attribute__((init_priority(101)));

void* alloc_or_throw(std::size_t n) {
    void* p = mi_malloc(n);
    if (!p) throw std::bad_alloc();
    return p;
}

void* aligned_or_throw(std::size_t n, std::align_val_t a) {
    void* p = mi_malloc_aligned(n, static_cast<std::size_t>(a));
    if (!p) throw std::bad_alloc();
    return p;
}

}  // namespace

void* operator new(std::size_t n) { return alloc_or_throw(n); }
void* operator new[](std::size_t n) { return alloc_or_throw(n); }
void* operator new(std::size_t n, const std::nothrow_t&) noexcept { return mi_malloc(n); }
void* operator new[](std::size_t n, const std::nothrow_t&) noexcept { return mi_malloc(n); }
void* operator new(std::size_t n, std::align_val_t a) { return aligned_or_throw(n, a); }
void* operator new[](std::size_t n, std::align_val_t a) { return aligned_or_throw(n, a); }
void* operator new(std::size_t n, std::align_val_t a, const std::nothrow_t&) noexcept {
    return mi_malloc_aligned(n, static_cast<std::size_t>(a));
}
void* operator new[](std::size_t n, std::align_val_t a, const std::nothrow_t&) noexcept {
    return mi_malloc_aligned(n, static_cast<std::size_t>(a));
}

void operator delete(void* p) noexcept { release(p); }
void operator delete[](void* p) noexcept { release(p); }
void operator delete(void* p, std::size_t) noexcept { release(p); }
void operator delete[](void* p, std::size_t) noexcept { release(p); }
void operator delete(void* p, const std::nothrow_t&) noexcept { release(p); }
void operator delete[](void* p, const std::nothrow_t&) noexcept { release(p); }
void operator delete(void* p, std::align_val_t) noexcept { release(p); }
void operator delete[](void* p, std::align_val_t) noexcept { release(p); }
void operator delete(void* p, std::size_t, std::align_val_t) noexcept { release(p); }
void operator delete[](void* p, std::size_t, std::align_val_t) noexcept { release(p); }
void operator delete(void* p, std::align_val_t, const std::nothrow_t&) noexcept { release(p); }
void operator delete[](void* p, std::align_val_t, const std::nothrow_t&) noexcept { release(p); }

#endif
