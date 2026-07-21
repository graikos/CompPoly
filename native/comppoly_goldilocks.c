#include <stdint.h>
#include <lean/lean.h>

/*
 * Native transcriptions of the extern bodies in
 * CompPoly/Fields/Goldilocks/FastExt.lean. Lean checks only the types of the
 * extern declarations; each function here must agree bit-for-bit with its Lean
 * body, which `lake exe CompPolyGoldilocksFastExtTests` checks at runtime.
 */

/* Ext.mulHi: high 64 bits of the 64-by-64 widening product. */
LEAN_EXPORT uint64_t comppoly_uint64_mul_hi(uint64_t a, uint64_t b) {
    return (uint64_t)(((unsigned __int128)a * b) >> 64);
}

static const uint64_t GOLDILOCKS_MODULUS     = 0xFFFFFFFF00000001ULL;
static const uint64_t GOLDILOCKS_NEG_MODULUS = 0x00000000FFFFFFFFULL;

/* Ext.mulRawNative: the 128-bit product folded with 2^64 = 2^32 - 1 (mod p),
 * then one conditional subtraction to canonicalize. */
LEAN_EXPORT uint64_t comppoly_goldilocks_mul(uint64_t a, uint64_t b) {
    unsigned __int128 prod = (unsigned __int128)a * b;
    uint64_t lo = (uint64_t)prod;
    uint64_t hi = (uint64_t)(prod >> 64);

    uint64_t hi_hi = hi >> 32;
    uint64_t hi_lo = hi & GOLDILOCKS_NEG_MODULUS;

    uint64_t t0 = lo - hi_hi;                       /* subBorrow */
    if (lo < hi_hi) {
        t0 -= GOLDILOCKS_NEG_MODULUS;
    }

    uint64_t t1 = hi_lo * GOLDILOCKS_NEG_MODULUS;

    uint64_t t2 = t0 + t1;                          /* addOverflow */
    if (t2 < t0) {
        t2 += GOLDILOCKS_NEG_MODULUS;
    }

    return t2 < GOLDILOCKS_MODULUS ? t2 : t2 - GOLDILOCKS_MODULUS;
}
