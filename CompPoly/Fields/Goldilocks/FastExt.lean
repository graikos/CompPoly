/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Varun Thakore, Georgios Raikos
-/

import CompPoly.Fields.Goldilocks.Fast

/-!
# Extern-Backed Fast Goldilocks Operations (opt-in)

Native backends for the fast Goldilocks field; the verified pure-Lean operations remain
the default. Each `@[extern]` declaration carries the verified Lean implementation as its
body and is provably equal to its verified counterpart, so trust is runtime-only:
`native/comppoly_goldilocks.c` must transcribe these bodies. The module interpreter cannot
call project-local externs, so runtime checks live in
`lake exe CompPolyGoldilocksFastExtTests`.
-/

namespace Goldilocks.Fast.Ext

/-- High 64 bits of the 64×64 widening product. The body is the verified limb
computation; compiled code calls the trusted native `comppoly_uint64_mul_hi`. -/
@[extern "comppoly_uint64_mul_hi"]
def mulHi (a b : UInt64) : UInt64 := wideMulHi a b

/-- The whole canonical Goldilocks product. The body is the verified `mulRaw`;
compiled code calls the trusted native `comppoly_goldilocks_mul`. -/
@[extern "comppoly_goldilocks_mul"]
def mulRawNative (a b : UInt64) : UInt64 := mulRaw a b

/-- Multiplication with the extern high word; the reduction is compiled Lean. -/
@[inline]
def mulWithMulHi (x y : Field) : Field :=
  .mk (reduceWide (x.val * y.val) (mulHi x.val y.val)) (mulRaw_lt x.val y.val)

/-- `mulWithMulHi` agrees with the verified multiplication. -/
theorem mulWithMulHi_eq_mul (x y : Field) : mulWithMulHi x y = x * y := rfl

/-- Whole-operation native multiplication. -/
@[inline]
def mulNative (x y : Field) : Field :=
  .mk (mulRawNative x.val y.val) (mulRaw_lt x.val y.val)

/-- `mulNative` agrees with the verified multiplication. -/
theorem mulNative_eq_mul (x y : Field) : mulNative x y = x * y := rfl

/-- Squaring with the extern high word. -/
@[inline]
def squareWithMulHi (x : Field) : Field := mulWithMulHi x x

/-- Squaring through the whole-operation native multiplication. -/
@[inline]
def squareNative (x : Field) : Field := mulNative x x

/-- `squareNative` agrees with the verified squaring. -/
theorem squareNative_eq_square (x : Field) : squareNative x = square x := rfl

/-- Repeated squaring through the native multiplication. -/
@[inline]
def squareNNative (x : Field) : ℕ → Field
  | 0 => x
  | n + 1 => squareNative (squareNNative x n)

/-- `squareNNative` agrees with the verified repeated squaring. -/
theorem squareNNative_eq_squareN (x : Field) (n : ℕ) :
    squareNNative x n = squareN x n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [squareNNative, squareN, ih, squareNative_eq_square]

/-- The Goldilocks `p - 2` addition chain over the native multiplication. -/
@[noinline]
def invNative (x : Field) : Field :=
  let t2 := mulNative (squareNative x) x
  let t4 := mulNative (squareNNative t2 2) t2
  let t8 := mulNative (squareNNative t4 4) t4
  let t16 := mulNative (squareNNative t8 8) t8
  let t31 := mulNative (squareNNative t16 15)
    (mulNative (squareNNative t8 7)
      (mulNative (squareNNative t4 3) (mulNative (squareNative t2) x)))
  let t32m2 := squareNative t31
  let t32m1 := mulNative t32m2 x
  mulNative (squareNNative t32m2 32) t32m1

/-- `invNative` agrees with the verified inversion. -/
theorem invNative_eq_inv (x : Field) : invNative x = x⁻¹ := by
  simp only [invNative, inv_def, inv, mulNative_eq_mul, squareNative_eq_square,
    squareNNative_eq_squareN, square_def]

/-- Division through native inversion and multiplication. -/
@[inline]
def divNative (x y : Field) : Field := mulNative x (invNative y)

/-- `divNative` agrees with the verified division. -/
theorem divNative_eq_div (x y : Field) : divNative x y = x / y := by
  rw [divNative, mulNative_eq_mul, invNative_eq_inv, div_def]

end Goldilocks.Fast.Ext
