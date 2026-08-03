#include <stdint.h>
#include <lean/lean.h>

/*
 * Native backends for the fast binary tower fields, called through the
 * @[extern] declarations in CompPoly/Fields/Binary/Tower/FastExt.lean.
 * Proofs only see the Lean bodies of those declarations; runtime agreement
 * with this file is checked by `lake exe CompPolyBTExtTests`.
 *
 * The bit-level helpers below mirror the rungs of the verified ladder in
 * CompPoly/Fields/Binary/Tower/Fast.lean; they run once at load time to
 * build the GF(2^8) tables, and the runtime kernels are Karatsuba over
 * table lookups. The inverse kernels return candidates that callers verify.
 */

/* `mul2`: GF(4) multiplication. */
static inline uint64_t bt_mul2(uint64_t a, uint64_t b) {
    uint64_t a0 = a & 1, a1 = a >> 1, b0 = b & 1, b1 = b >> 1;
    uint64_t p0 = a0 & b0;
    uint64_t p2 = a1 & b1;
    uint64_t p1 = (a0 ^ a1) & (b0 ^ b1);
    uint64_t lo = p0 ^ p2;
    return ((p1 ^ lo ^ p2) << 1) | lo;
}

/* `mulByZ1`: multiplication by the level-1 generator. */
static inline uint64_t bt_mulbyz1(uint64_t v) {
    uint64_t v0 = v & 1, v1 = v >> 1;
    return ((v0 ^ v1) << 1) | v1;
}

/* `sq2`: GF(4) squaring. */
static inline uint64_t bt_sq2(uint64_t v) {
    uint64_t v0 = v & 1, v1 = v >> 1;
    return (v1 << 1) | (v0 ^ v1);
}

/* `inv2`: GF(4) inversion, 0 -> 0. */
static inline uint64_t bt_inv2(uint64_t v) {
    uint64_t v0 = v & 1, v1 = v >> 1;
    uint64_t next = v0 ^ v1;
    uint64_t delta = (v0 & next) ^ v1;
    return ((delta & v1) << 1) | (delta & next);
}

/* `mul4`: GF(2^4) multiplication. */
static inline uint64_t bt_mul4(uint64_t a, uint64_t b) {
    uint64_t a0 = a & 0x3, a1 = a >> 2, b0 = b & 0x3, b1 = b >> 2;
    uint64_t p0 = bt_mul2(a0, b0);
    uint64_t p2 = bt_mul2(a1, b1);
    uint64_t p1 = bt_mul2(a0 ^ a1, b0 ^ b1);
    uint64_t lo = p0 ^ p2;
    return ((p1 ^ lo ^ bt_mulbyz1(p2)) << 2) | lo;
}

/* `mulByZ2`: multiplication by the level-2 generator. */
static inline uint64_t bt_mulbyz2(uint64_t v) {
    uint64_t v0 = v & 0x3, v1 = v >> 2;
    return ((v0 ^ bt_mulbyz1(v1)) << 2) | v1;
}

/* `sq4`: GF(2^4) squaring. */
static inline uint64_t bt_sq4(uint64_t v) {
    uint64_t s0 = bt_sq2(v & 0x3);
    uint64_t s1 = bt_sq2(v >> 2);
    return (bt_mulbyz1(s1) << 2) | (s0 ^ s1);
}

/* `inv4`: GF(2^4) inversion, 0 -> 0. */
static inline uint64_t bt_inv4(uint64_t v) {
    uint64_t v0 = v & 0x3, v1 = v >> 2;
    uint64_t next = v0 ^ bt_mulbyz1(v1);
    uint64_t delta = bt_mul2(v0, next) ^ bt_sq2(v1);
    uint64_t d = bt_inv2(delta);
    return (bt_mul2(d, v1) << 2) | bt_mul2(d, next);
}

/* `mul8`: GF(2^8) multiplication. */
static inline uint64_t bt_mul8(uint64_t a, uint64_t b) {
    uint64_t a0 = a & 0xF, a1 = a >> 4, b0 = b & 0xF, b1 = b >> 4;
    uint64_t p0 = bt_mul4(a0, b0);
    uint64_t p2 = bt_mul4(a1, b1);
    uint64_t p1 = bt_mul4(a0 ^ a1, b0 ^ b1);
    uint64_t lo = p0 ^ p2;
    return ((p1 ^ lo ^ bt_mulbyz2(p2)) << 4) | lo;
}

/* `mulByZ3`: multiplication by the level-3 generator. */
static inline uint64_t bt_mulbyz3(uint64_t v) {
    uint64_t v0 = v & 0xF, v1 = v >> 4;
    return ((v0 ^ bt_mulbyz2(v1)) << 4) | v1;
}

/* `sq8`: GF(2^8) squaring. */
static inline uint64_t bt_sq8(uint64_t v) {
    uint64_t s0 = bt_sq4(v & 0xF);
    uint64_t s1 = bt_sq4(v >> 4);
    return (bt_mulbyz2(s1) << 4) | (s0 ^ s1);
}

/* `inv8`: GF(2^8) inversion, 0 -> 0. */
static inline uint64_t bt_inv8(uint64_t v) {
    uint64_t v0 = v & 0xF, v1 = v >> 4;
    uint64_t next = v0 ^ bt_mulbyz2(v1);
    uint64_t delta = bt_mul4(v0, next) ^ bt_sq4(v1);
    uint64_t d = bt_inv4(delta);
    return (bt_mul4(d, v1) << 4) | bt_mul4(d, next);
}

/* GF(2^8) tables, filled at load from the helpers above. */
static uint8_t BT_MUL8[256][256];
static uint8_t BT_MBZ3[256];
static uint8_t BT_SQ8[256];
static uint8_t BT_INV8[256];

__attribute__((constructor)) static void bt_init(void) {
    for (int a = 0; a < 256; a++) {
        for (int b = 0; b < 256; b++) {
            BT_MUL8[a][b] = (uint8_t)bt_mul8((uint64_t)a, (uint64_t)b);
        }
        BT_MBZ3[a] = (uint8_t)bt_mulbyz3((uint64_t)a);
        BT_SQ8[a] = (uint8_t)bt_sq8((uint64_t)a);
        BT_INV8[a] = (uint8_t)bt_inv8((uint64_t)a);
    }
}

/* Table-based kernels: the Lean rung shapes, with level-3 operations
 * replaced by table lookups. */

/* `mul16` over the tables. */
static inline uint64_t bt_mul16t(uint64_t a, uint64_t b) {
    uint64_t a0 = a & 0xFF, a1 = a >> 8, b0 = b & 0xFF, b1 = b >> 8;
    uint64_t p0 = BT_MUL8[a0][b0];
    uint64_t p2 = BT_MUL8[a1][b1];
    uint64_t p1 = BT_MUL8[a0 ^ a1][b0 ^ b1];
    uint64_t lo = p0 ^ p2;
    return ((p1 ^ lo ^ BT_MBZ3[p2]) << 8) | lo;
}

/* `mulByZ4` over the tables. */
static inline uint64_t bt_mbz4t(uint64_t v) {
    uint64_t v0 = v & 0xFF, v1 = v >> 8;
    return ((v0 ^ BT_MBZ3[v1]) << 8) | v1;
}

/* `sq16` over the tables. */
static inline uint64_t bt_sq16t(uint64_t v) {
    uint64_t s0 = BT_SQ8[v & 0xFF];
    uint64_t s1 = BT_SQ8[v >> 8];
    return ((uint64_t)BT_MBZ3[s1] << 8) | (s0 ^ s1);
}

/* `inv16` over the tables. */
static inline uint64_t bt_inv16t(uint64_t v) {
    uint64_t v0 = v & 0xFF, v1 = v >> 8;
    uint64_t next = v0 ^ BT_MBZ3[v1];
    uint64_t delta = BT_MUL8[v0][next] ^ BT_SQ8[v1];
    uint64_t d = BT_INV8[delta];
    return ((uint64_t)BT_MUL8[d][v1] << 8) | BT_MUL8[d][next];
}

/* `mul32` over the tables. */
static inline uint64_t bt_mul32t(uint64_t a, uint64_t b) {
    uint64_t a0 = a & 0xFFFF, a1 = a >> 16, b0 = b & 0xFFFF, b1 = b >> 16;
    uint64_t p0 = bt_mul16t(a0, b0);
    uint64_t p2 = bt_mul16t(a1, b1);
    uint64_t p1 = bt_mul16t(a0 ^ a1, b0 ^ b1);
    uint64_t lo = p0 ^ p2;
    return ((p1 ^ lo ^ bt_mbz4t(p2)) << 16) | lo;
}

/* `mulByZ5` over the tables. */
static inline uint64_t bt_mbz5t(uint64_t v) {
    uint64_t v0 = v & 0xFFFF, v1 = v >> 16;
    return ((v0 ^ bt_mbz4t(v1)) << 16) | v1;
}

/* `sq32` over the tables. */
static inline uint64_t bt_sq32t(uint64_t v) {
    uint64_t s0 = bt_sq16t(v & 0xFFFF);
    uint64_t s1 = bt_sq16t(v >> 16);
    return (bt_mbz4t(s1) << 16) | (s0 ^ s1);
}

/* `inv32` over the tables. */
static inline uint64_t bt_inv32t(uint64_t v) {
    uint64_t v0 = v & 0xFFFF, v1 = v >> 16;
    uint64_t next = v0 ^ bt_mbz4t(v1);
    uint64_t delta = bt_mul16t(v0, next) ^ bt_sq16t(v1);
    uint64_t d = bt_inv16t(delta);
    return (bt_mul16t(d, v1) << 16) | bt_mul16t(d, next);
}

/* `mul64` over the tables. */
static inline uint64_t bt_mul64t(uint64_t a, uint64_t b) {
    uint64_t a0 = a & 0xFFFFFFFF, a1 = a >> 32;
    uint64_t b0 = b & 0xFFFFFFFF, b1 = b >> 32;
    uint64_t p0 = bt_mul32t(a0, b0);
    uint64_t p2 = bt_mul32t(a1, b1);
    uint64_t p1 = bt_mul32t(a0 ^ a1, b0 ^ b1);
    uint64_t lo = p0 ^ p2;
    return ((p1 ^ lo ^ bt_mbz5t(p2)) << 32) | lo;
}

/* `mulByZ6` over the tables. */
static inline uint64_t bt_mbz6t(uint64_t v) {
    uint64_t v0 = v & 0xFFFFFFFF, v1 = v >> 32;
    return ((v0 ^ bt_mbz5t(v1)) << 32) | v1;
}

/* `sq64` over the tables. */
static inline uint64_t bt_sq64t(uint64_t v) {
    uint64_t s0 = bt_sq32t(v & 0xFFFFFFFF);
    uint64_t s1 = bt_sq32t(v >> 32);
    return (bt_mbz5t(s1) << 32) | (s0 ^ s1);
}

/* `inv64` over the tables. */
static inline uint64_t bt_inv64t(uint64_t v) {
    uint64_t v0 = v & 0xFFFFFFFF, v1 = v >> 32;
    uint64_t next = v0 ^ bt_mbz5t(v1);
    uint64_t delta = bt_mul32t(v0, next) ^ bt_sq32t(v1);
    uint64_t d = bt_inv32t(delta);
    return (bt_mul32t(d, v1) << 32) | bt_mul32t(d, next);
}

/* `FastBT128.mul` over the tables. */
static inline void bt_mul128t(uint64_t alo, uint64_t ahi, uint64_t blo,
                              uint64_t bhi, uint64_t *rlo, uint64_t *rhi) {
    uint64_t p0 = bt_mul64t(alo, blo);
    uint64_t p2 = bt_mul64t(ahi, bhi);
    uint64_t p1 = bt_mul64t(alo ^ ahi, blo ^ bhi);
    uint64_t lo = p0 ^ p2;
    *rlo = lo;
    *rhi = p1 ^ lo ^ bt_mbz6t(p2);
}

/* `FastBT128.inv` over the tables. */
static inline void bt_inv128t(uint64_t vlo, uint64_t vhi, uint64_t *rlo,
                              uint64_t *rhi) {
    uint64_t next = vlo ^ bt_mbz6t(vhi);
    uint64_t delta = bt_mul64t(vlo, next) ^ bt_sq64t(vhi);
    uint64_t d = bt_inv64t(delta);
    *rlo = bt_mul64t(d, next);
    *rhi = bt_mul64t(d, vhi);
}

/* Extern entry points. FastBT128 is a two-scalar-field constructor: `lo` at
 * byte offset 0, `hi` at byte offset 8. */

LEAN_EXPORT uint64_t comppoly_bt_mul64(uint64_t a, uint64_t b) {
    return bt_mul64t(a, b);
}

LEAN_EXPORT uint64_t comppoly_bt_inv64(uint64_t v) {
    return bt_inv64t(v);
}

LEAN_EXPORT lean_object *comppoly_bt128_mul(b_lean_obj_arg a, b_lean_obj_arg b) {
    uint64_t rlo, rhi;
    bt_mul128t(lean_ctor_get_uint64(a, 0), lean_ctor_get_uint64(a, 8),
               lean_ctor_get_uint64(b, 0), lean_ctor_get_uint64(b, 8), &rlo,
               &rhi);
    lean_object *res = lean_alloc_ctor(0, 0, 2 * sizeof(uint64_t));
    lean_ctor_set_uint64(res, 0, rlo);
    lean_ctor_set_uint64(res, 8, rhi);
    return res;
}

LEAN_EXPORT lean_object *comppoly_bt128_inv(b_lean_obj_arg v) {
    uint64_t rlo, rhi;
    bt_inv128t(lean_ctor_get_uint64(v, 0), lean_ctor_get_uint64(v, 8), &rlo,
               &rhi);
    lean_object *res = lean_alloc_ctor(0, 0, 2 * sizeof(uint64_t));
    lean_ctor_set_uint64(res, 0, rlo);
    lean_ctor_set_uint64(res, 8, rhi);
    return res;
}
