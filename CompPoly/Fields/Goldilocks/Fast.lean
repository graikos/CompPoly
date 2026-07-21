/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Varun Thakore, Georgios Raikos
-/

import CompPoly.Fields.Goldilocks.Basic
import Mathlib.Algebra.Field.TransferInstance
import Mathlib.FieldTheory.Finite.Basic

/-!
# Fast Goldilocks Field

Native `UInt64` implementation of the Goldilocks field `p = 2^64 - 2^32 + 1`.

Values are canonical residues below `p`. Multiplication computes the 128-bit product as
two words and folds them with the Goldilocks identity `2^64 ≡ 2^32 - 1 (mod p)`.
-/

namespace Goldilocks.Fast

/-! ## Parameters -/

/-- The Goldilocks modulus `2^64 - 2^32 + 1` as a native word. -/
def modulus : UInt64 := 0xFFFFFFFF00000001

/-- `2^64 - p = 2^32 - 1`, the correction applied when a word operation wraps. -/
def negModulus : UInt64 := 0xFFFFFFFF

/-- The native modulus agrees with the mathematical Goldilocks modulus. -/
@[simp] theorem modulus_toNat : modulus.toNat = fieldSize := by decide

/-- The native correction word is `2^32 - 1`. -/
@[simp] theorem negModulus_toNat : negModulus.toNat = 2 ^ 32 - 1 := by decide

/-- The Goldilocks modulus is positive. -/
theorem fieldSize_pos : 0 < fieldSize := by decide

private theorem toNat_lt_two_pow_64 (x : UInt64) : x.toNat < 2 ^ 64 := x.toNat_lt_size

/-! ## Raw word operations -/

variable {x y : UInt64}

/-- Right-shifting by 32 divides the natural value by `2^32`. -/
theorem shiftRight32_toNat (x : UInt64) : (x >>> 32).toNat = x.toNat / 2 ^ 32 := by
  rw [UInt64.toNat_shiftRight, (by decide : (32 : UInt64).toNat % 64 = 32),
    Nat.shiftRight_eq_div_pow]

/-- Masking with `negModulus` takes the natural value modulo `2^32`. -/
theorem and_negModulus_toNat (x : UInt64) : (x &&& negModulus).toNat = x.toNat % 2 ^ 32 := by
  rw [UInt64.toNat_and, negModulus_toNat, Nat.and_two_pow_sub_one_eq_mod]

/-- One conditional subtraction of `p`. Since `2^64 < 2p`, this canonicalizes any word. -/
@[inline]
def conditionalSubtract (x : UInt64) : UInt64 :=
  if x < modulus then x else x - modulus

theorem conditionalSubtract_toNat (x : UInt64) :
    (conditionalSubtract x).toNat = x.toNat % fieldSize := by
  have hx := toNat_lt_two_pow_64 x
  simp only [conditionalSubtract]
  split <;> rename_i h <;> rw [UInt64.lt_iff_toNat_lt, modulus_toNat] at h
  · simp only [fieldSize] at *; omega
  · rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, modulus_toNat]; omega),
      modulus_toNat]
    simp only [fieldSize] at *; omega

theorem conditionalSubtract_lt (x : UInt64) : (conditionalSubtract x).toNat < fieldSize := by
  rw [conditionalSubtract_toNat]; exact Nat.mod_lt _ fieldSize_pos

/-- High word of the full 64×64 product, computed from 32-bit limbs. -/
@[inline]
def wideMulHi (x y : UInt64) : UInt64 :=
  let xLo := x &&& negModulus
  let xHi := x >>> 32
  let yLo := y &&& negModulus
  let yHi := y >>> 32
  let p00 := xLo * yLo
  let p01 := xLo * yHi
  let p10 := xHi * yLo
  let p11 := xHi * yHi
  let carry := (p00 >>> 32) + (p01 &&& negModulus) + (p10 &&& negModulus)
  p11 + (p01 >>> 32) + (p10 >>> 32) + (carry >>> 32)

theorem wideMulHi_toNat (x y : UInt64) :
    (wideMulHi x y).toNat = x.toNat * y.toNat / 2 ^ 64 := by
  have hx := toNat_lt_two_pow_64 x
  have hy := toNat_lt_two_pow_64 y
  have h00 : x.toNat % 2 ^ 32 * (y.toNat % 2 ^ 32) ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h01 : x.toNat % 2 ^ 32 * (y.toNat / 2 ^ 32) ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h10 : x.toNat / 2 ^ 32 * (y.toNat % 2 ^ 32) ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h11 : x.toNat / 2 ^ 32 * (y.toNat / 2 ^ 32) ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hsplit : x.toNat * y.toNat =
      x.toNat % 2 ^ 32 * (y.toNat % 2 ^ 32)
        + 2 ^ 32 * (x.toNat % 2 ^ 32 * (y.toNat / 2 ^ 32)
          + x.toNat / 2 ^ 32 * (y.toNat % 2 ^ 32))
        + 2 ^ 64 * (x.toNat / 2 ^ 32 * (y.toNat / 2 ^ 32)) := by
    calc x.toNat * y.toNat
        = (x.toNat % 2 ^ 32 + 2 ^ 32 * (x.toNat / 2 ^ 32))
            * (y.toNat % 2 ^ 32 + 2 ^ 32 * (y.toNat / 2 ^ 32)) := by
          rw [Nat.mod_add_div, Nat.mod_add_div]
      _ = _ := by ring
  simp only [wideMulHi, UInt64.toNat_add, UInt64.toNat_mul, shiftRight32_toNat,
    and_negModulus_toNat]
  omega

/-- Subtraction with the Goldilocks borrow correction: `x - y (mod p)` for `y ≤ p`. -/
@[inline]
def subBorrow (x y : UInt64) : UInt64 :=
  if x < y then x - y - negModulus else x - y

theorem subBorrow_toNat (hy : y.toNat ≤ fieldSize) :
    (subBorrow x y).toNat =
      if y.toNat ≤ x.toNat then x.toNat - y.toNat else x.toNat + fieldSize - y.toNat := by
  have hx := toNat_lt_two_pow_64 x
  have hy64 := toNat_lt_two_pow_64 y
  simp only [subBorrow]
  split <;> rename_i h <;> rw [UInt64.lt_iff_toNat_lt] at h
  · have hsub : (x - y).toNat = 2 ^ 64 - y.toNat + x.toNat := by
      rw [UInt64.toNat_sub, Nat.mod_eq_of_lt (by omega)]
    rw [UInt64.toNat_sub_of_le _ _ (by
        rw [UInt64.le_iff_toNat_le, negModulus_toNat, hsub]
        simp only [fieldSize] at hy; omega),
      hsub, negModulus_toNat, if_neg (by omega)]
    simp only [fieldSize] at *; omega
  · rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega), if_pos (by omega)]

/-- Addition with the Goldilocks overflow correction, valid below `2^64 + p`. -/
@[inline]
def addOverflow (x y : UInt64) : UInt64 :=
  if x + y < x then x + y + negModulus else x + y

theorem addOverflow_toNat (h : x.toNat + y.toNat < 2 ^ 64 + fieldSize) :
    (addOverflow x y).toNat =
      if x.toNat + y.toNat < 2 ^ 64 then x.toNat + y.toNat
      else x.toNat + y.toNat - fieldSize := by
  have hx := toNat_lt_two_pow_64 x
  have hy := toNat_lt_two_pow_64 y
  simp only [addOverflow]
  split <;> rename_i hc <;>
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at hc
  · rw [UInt64.toNat_add, UInt64.toNat_add, negModulus_toNat]
    simp only [fieldSize] at *
    split <;> omega
  · rw [UInt64.toNat_add]
    simp only [fieldSize] at *
    split <;> omega

/-- Fold a 128-bit value `(lo, hi)` into one word congruent to it modulo `p`. -/
@[inline]
def reducePartial (lo hi : UInt64) : UInt64 :=
  addOverflow (subBorrow lo (hi >>> 32)) ((hi &&& negModulus) * negModulus)

theorem reducePartial_toNat_mod (lo hi : UInt64) :
    (reducePartial lo hi).toNat % fieldSize =
      (lo.toNat + 2 ^ 64 * hi.toNat) % fieldSize := by
  have hlo := toNat_lt_two_pow_64 lo
  have hhi := toNat_lt_two_pow_64 hi
  have hmul : ((hi &&& negModulus) * negModulus).toNat = hi.toNat % 2 ^ 32 * (2 ^ 32 - 1) := by
    rw [UInt64.toNat_mul, and_negModulus_toNat, negModulus_toNat,
      Nat.mod_eq_of_lt (by
        have : hi.toNat % 2 ^ 32 * (2 ^ 32 - 1) ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
          Nat.mul_le_mul (by omega) (by omega)
        omega)]
  have hsub := subBorrow_toNat (x := lo) (y := hi >>> 32) (by
    rw [shiftRight32_toNat]; simp only [fieldSize]; omega)
  rw [reducePartial, addOverflow_toNat (by
      have := toNat_lt_two_pow_64 (subBorrow lo (hi >>> 32))
      have : hi.toNat % 2 ^ 32 * (2 ^ 32 - 1) ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      rw [hmul]; simp only [fieldSize] at *; omega),
    hmul, hsub, shiftRight32_toNat]
  simp only [fieldSize] at *
  split_ifs <;> omega

/-- Canonical reduction of a 128-bit value `(lo, hi)`. -/
@[inline]
def reduceWide (lo hi : UInt64) : UInt64 :=
  conditionalSubtract (reducePartial lo hi)

theorem reduceWide_toNat (lo hi : UInt64) :
    (reduceWide lo hi).toNat = (lo.toNat + 2 ^ 64 * hi.toNat) % fieldSize := by
  rw [reduceWide, conditionalSubtract_toNat, reducePartial_toNat_mod]

/-- Goldilocks product of two words, canonical. -/
@[inline]
def mulRaw (x y : UInt64) : UInt64 :=
  reduceWide (x * y) (wideMulHi x y)

theorem mulRaw_toNat (x y : UInt64) :
    (mulRaw x y).toNat = x.toNat * y.toNat % fieldSize := by
  have hw := wideMulHi_toNat x y
  have hprod : (x * y).toNat = x.toNat * y.toNat % 2 ^ 64 := UInt64.toNat_mul x y
  rw [mulRaw, reduceWide_toNat, hw, hprod]
  simp only [fieldSize]
  omega

theorem mulRaw_lt (x y : UInt64) : (mulRaw x y).toNat < fieldSize := by
  rw [mulRaw_toNat]; exact Nat.mod_lt _ fieldSize_pos

/-- Canonical addition: one wrapping add, then carry fold or conditional subtraction. -/
@[inline]
def addRaw (x y : UInt64) : UInt64 :=
  let s := x + y
  if s < x then s + negModulus else conditionalSubtract s

theorem addRaw_toNat (hx : x.toNat < fieldSize) (hy : y.toNat < fieldSize) :
    (addRaw x y).toNat = (x.toNat + y.toNat) % fieldSize := by
  have hx64 := toNat_lt_two_pow_64 x
  have hy64 := toNat_lt_two_pow_64 y
  simp only [addRaw]
  split <;> rename_i h <;> rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h
  · rw [UInt64.toNat_add, UInt64.toNat_add, negModulus_toNat]
    simp only [fieldSize] at *; omega
  · rw [conditionalSubtract_toNat, UInt64.toNat_add]
    simp only [fieldSize] at *; omega

/-- Canonical negation. -/
@[inline]
def negRaw (x : UInt64) : UInt64 :=
  if x = 0 then 0 else modulus - x

theorem negRaw_toNat (hx : x.toNat < fieldSize) :
    (negRaw x).toNat = (fieldSize - x.toNat) % fieldSize := by
  simp only [negRaw]
  split <;> rename_i h
  · have hx0 : x.toNat = 0 := by simpa using UInt64.toNat_inj.mpr h
    simp [hx0]
  · have hx0 : x.toNat ≠ 0 := by simpa using UInt64.toNat_inj.not.mpr h
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, modulus_toNat]; omega),
      modulus_toNat, Nat.mod_eq_of_lt (by omega)]

/-! ## Carrier and conversions -/

/-- The fast Goldilocks carrier: a native word below `p`. At runtime this erases
to `UInt64`. -/
def Field : Type := { x : UInt64 // x.toNat < fieldSize }

instance : DecidableEq Field :=
  inferInstanceAs (DecidableEq { x : UInt64 // x.toNat < fieldSize })

namespace Field

/-- Build a fast element from a canonical natural representative. -/
@[inline]
def ofCanonicalNat (n : ℕ) (h : n < fieldSize) : Field :=
  .mk (UInt64.ofNat n) <| by
    rw [UInt64.toNat_ofNat']
    simp only [fieldSize] at *; omega

/-- Convert a natural number into fast canonical representation. -/
@[inline]
def ofNat (n : ℕ) : Field :=
  ofCanonicalNat (n % fieldSize) (Nat.mod_lt _ fieldSize_pos)

/-- Convert a 64-bit word into fast canonical representation. -/
@[inline]
def ofUInt64 (x : UInt64) : Field :=
  .mk (conditionalSubtract x) (conditionalSubtract_lt x)

/-- Convert from the canonical `ZMod` field into fast canonical form. -/
@[inline]
def ofField (x : Goldilocks.Field) : Field :=
  ofCanonicalNat x.val (ZMod.val_lt x)

/-- Convert an integer into fast canonical representation. -/
@[inline]
private def ofInt (n : ℤ) : Field :=
  ofField (n : Goldilocks.Field)

/-- The canonical natural representative of a fast element. -/
@[inline]
def toNat (x : Field) : ℕ := x.val.toNat

/-- Interpret a fast element in the canonical `ZMod` field. -/
@[inline]
def toField (x : Field) : Goldilocks.Field := (x.toNat : Goldilocks.Field)

@[simp]
theorem val_toNat_lt (x : Field) : x.val.toNat < fieldSize := x.property

theorem toNat_lt (x : Field) : x.toNat < fieldSize := x.property

end Field

open Field

/-! ## Field operations -/

/-- The zero fast element. -/
def zero : Field := .mk 0 (by decide)

/-- The one fast element. -/
def one : Field := .mk 1 (by decide)

/-- Fast modular addition. -/
@[inline]
def add (x y : Field) : Field :=
  .mk (addRaw x.val y.val) <| by
    rw [addRaw_toNat x.property y.property]; exact Nat.mod_lt _ fieldSize_pos

/-- Fast modular negation. -/
@[inline]
def neg (x : Field) : Field :=
  .mk (negRaw x.val) <| by
    rw [negRaw_toNat x.property]; exact Nat.mod_lt _ fieldSize_pos

/-- Fast modular subtraction. -/
@[inline]
def sub (x y : Field) : Field :=
  .mk (subBorrow x.val y.val) <| by
    rw [subBorrow_toNat (Nat.le_of_lt y.property)]
    have hx := x.property
    have hy := y.property
    split <;> omega

/-- Fast modular multiplication. -/
@[inline]
def mul (x y : Field) : Field :=
  .mk (mulRaw x.val y.val) (mulRaw_lt x.val y.val)

/-- Fast squaring. -/
@[inline]
def square (x : Field) : Field := mul x x

/-- Repeated squaring: `squareN x n` computes `x^(2^n)`. -/
@[inline]
def squareN (x : Field) : ℕ → Field
  | 0 => x
  | n + 1 => square (squareN x n)

/-- Exponentiation over the fast representation by binary exponentiation. -/
@[specialize]
def pow (x : Field) (n : ℕ) : Field :=
  @npowBinRec Field ⟨one⟩ ⟨mul⟩ n x

instance : Zero Field := ⟨zero⟩
instance : One Field := ⟨one⟩
instance : Add Field where add
instance : Neg Field where neg
instance : Sub Field where sub
instance : Mul Field where mul
instance : Pow Field ℕ where pow

theorem zero_def : (0 : Field) = zero := rfl
theorem one_def : (1 : Field) = one := rfl
theorem add_def (x y : Field) : x + y = add x y := rfl
theorem neg_def (x : Field) : -x = neg x := rfl
theorem sub_def (x y : Field) : x - y = sub x y := rfl
theorem mul_def (x y : Field) : x * y = mul x y := rfl
theorem square_def (x : Field) : square x = x * x := rfl

/-- Fast inversion by Fermat via an addition chain for `p - 2 = 0xFFFFFFFE_FFFFFFFF`:
build `x^(2^31 - 1)`, square into `x^(2^32 - 2)` and `x^(2^32 - 1)`, and combine as
`(2^32 - 2) * 2^32 + (2^32 - 1) = p - 2`. Zero maps to zero. -/
@[noinline]
def inv (x : Field) : Field :=
  let t2 := square x * x
  let t4 := squareN t2 2 * t2
  let t8 := squareN t4 4 * t4
  let t16 := squareN t8 8 * t8
  let t31 := squareN t16 15 * (squareN t8 7 * (squareN t4 3 * (square t2 * x)))
  let t32m2 := square t31
  let t32m1 := t32m2 * x
  squareN t32m2 32 * t32m1

/-- Division through inversion and fast multiplication. -/
@[inline]
def div (x y : Field) : Field := mul x (inv y)

instance : Inv Field where inv
instance : Div Field where div

theorem inv_def (x : Field) : x⁻¹ = inv x := rfl
theorem div_def (x y : Field) : x / y = x * y⁻¹ := rfl

instance : NatCast Field := ⟨ofNat⟩
instance : IntCast Field := ⟨ofInt⟩

instance : SMul ℕ Field where
  smul n x := ofNat n * x

instance : SMul ℤ Field where
  smul n x := ofInt n * x

instance : Pow Field ℤ where
  pow x n :=
    match n with
    | Int.ofNat k => pow x k
    | Int.negSucc k => pow (inv x) (k + 1)

instance : NNRatCast Field where
  nnratCast q := ofField (q : Goldilocks.Field)

instance : RatCast Field where
  ratCast q := ofField (q : Goldilocks.Field)

instance : SMul ℚ≥0 Field where
  smul q x := ofField (q • toField x)

instance : SMul ℚ Field where
  smul q x := ofField (q • toField x)

/-! ## Correctness -/

/-- Converting a canonical natural representative to fast form preserves its value. -/
@[simp]
theorem toField_ofCanonicalNat {n : ℕ} (h : n < fieldSize) :
    toField (ofCanonicalNat n h) = (n : Goldilocks.Field) := by
  show ((UInt64.ofNat n).toNat : Goldilocks.Field) = _
  rw [UInt64.toNat_ofNat']
  congr 1
  simp only [fieldSize] at *; omega

/-- Converting a canonical natural representative to fast form and reading it back is
the identity. -/
@[simp]
theorem toNat_ofCanonicalNat {n : ℕ} (h : n < fieldSize) :
    toNat (ofCanonicalNat n h) = n := by
  show (UInt64.ofNat n).toNat = n
  rw [UInt64.toNat_ofNat']
  simp only [fieldSize] at *; omega

/-- Converting a `UInt64` to fast form agrees with casting its natural value. -/
@[simp]
theorem toField_ofUInt64 (x : UInt64) :
    toField (ofUInt64 x) = (x.toNat : Goldilocks.Field) := by
  show ((conditionalSubtract x).toNat : Goldilocks.Field) = _
  rw [conditionalSubtract_toNat, ZMod.natCast_mod]

/-- Converting from the canonical field to fast form and back is the identity. -/
@[simp]
theorem toField_ofField (x : Goldilocks.Field) : toField (ofField x) = x := by
  show toField (ofCanonicalNat x.val (ZMod.val_lt x)) = x
  rw [toField_ofCanonicalNat]
  exact ZMod.natCast_zmod_val x

/-- Converting from fast form to the canonical field and back is the identity. -/
@[simp]
theorem ofField_toField (x : Field) : ofField (toField x) = x := by
  apply Subtype.ext
  apply UInt64.toNat_inj.mp
  show (UInt64.ofNat ((x.val.toNat : Goldilocks.Field)).val).toNat = x.val.toNat
  rw [ZMod.val_natCast_of_lt x.property, UInt64.toNat_ofNat']
  have := toNat_lt_two_pow_64 x.val
  omega

/-- The canonical-field interpretation distinguishes fast Goldilocks values. -/
theorem toField_injective : Function.Injective toField :=
  Function.LeftInverse.injective ofField_toField

/-- `toField` maps fast zero to canonical zero. -/
@[simp]
theorem toField_zero : toField (0 : Field) = 0 := by decide

/-- `toField` maps fast one to canonical one. -/
@[simp]
theorem toField_one : toField (1 : Field) = 1 := by decide

/-- Fast addition agrees with addition in the canonical field. -/
@[simp]
theorem toField_add (x y : Field) : toField (x + y) = toField x + toField y := by
  show ((addRaw x.val y.val).toNat : Goldilocks.Field)
    = (x.val.toNat : Goldilocks.Field) + (y.val.toNat : Goldilocks.Field)
  rw [addRaw_toNat x.property y.property, ZMod.natCast_mod, Nat.cast_add]

/-- Fast negation agrees with negation in the canonical field. -/
@[simp]
theorem toField_neg (x : Field) : toField (-x) = -toField x := by
  show ((negRaw x.val).toNat : Goldilocks.Field) = -(x.val.toNat : Goldilocks.Field)
  rw [negRaw_toNat x.property, ZMod.natCast_mod,
    Nat.cast_sub (Nat.le_of_lt x.property), ZMod.natCast_self]
  ring

/-- Fast subtraction agrees with subtraction in the canonical field. -/
@[simp]
theorem toField_sub (x y : Field) : toField (x - y) = toField x - toField y := by
  show ((subBorrow x.val y.val).toNat : Goldilocks.Field)
    = (x.val.toNat : Goldilocks.Field) - (y.val.toNat : Goldilocks.Field)
  rw [subBorrow_toNat (Nat.le_of_lt y.property)]
  split <;> rename_i h
  · rw [Nat.cast_sub h]
  · rw [Nat.cast_sub (by have := y.property; omega), Nat.cast_add, ZMod.natCast_self]
    ring

/-- Fast multiplication agrees with multiplication in the canonical field. -/
@[simp]
theorem toField_mul (x y : Field) : toField (x * y) = toField x * toField y := by
  show ((mulRaw x.val y.val).toNat : Goldilocks.Field)
    = (x.val.toNat : Goldilocks.Field) * (y.val.toNat : Goldilocks.Field)
  rw [mulRaw_toNat, ZMod.natCast_mod, Nat.cast_mul]

/-- Fast squaring agrees with multiplication by itself in the canonical field. -/
@[simp]
theorem toField_square (x : Field) : toField (square x) = toField x * toField x := by
  rw [square_def, toField_mul]

/-- Repeated fast squaring agrees with raising to `2^n` in the canonical field. -/
@[simp]
theorem toField_squareN (x : Field) (n : ℕ) :
    toField (squareN x n) = toField x ^ 2 ^ n := by
  induction n with
  | zero => simp [squareN]
  | succ n ih =>
      rw [squareN, toField_square, ih, ← pow_add]
      congr 1
      rw [Nat.pow_succ]; omega

private theorem mul_assoc (x y z : Field) : x * y * z = x * (y * z) := by
  apply toField_injective
  rw [toField_mul, toField_mul, toField_mul, toField_mul]
  ring

private theorem pow_succ_field (x : Field) (n : ℕ) : pow x (n + 1) = pow x n * x := by
  unfold pow
  letI : Semigroup Field := { mul, mul_assoc }
  exact npowBinRec_succ n x

/-- Fast natural-power computation agrees with powers in the canonical field. -/
@[simp]
theorem toField_pow (x : Field) (n : ℕ) : toField (pow x n) = toField x ^ n := by
  induction n with
  | zero =>
      unfold pow
      rw [npowBinRec_zero, toField_one, pow_zero]
  | succ n ih =>
      rw [pow_succ_field, toField_mul, ih, _root_.pow_succ]

/-- Fermat-style inversion in the canonical Goldilocks field. -/
private theorem inv_eq_pow {a : Goldilocks.Field} (ha : a ≠ 0) :
    a⁻¹ = a ^ (fieldSize - 2) := by
  have hcard : Fintype.card Goldilocks.Field = fieldSize := ZMod.card fieldSize
  have h1 : a ^ (fieldSize - 1) = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one a ha
    rw [hcard] at h; exact h
  have hmul : a * a ^ (fieldSize - 2) = 1 := by
    rw [← pow_succ']; show a ^ (fieldSize - 2 + 1) = 1
    have : fieldSize - 2 + 1 = fieldSize - 1 := by unfold fieldSize; omega
    rw [this]; exact h1
  exact (eq_inv_of_mul_eq_one_left (by rwa [mul_comm])).symm

/-- The inversion chain computes the Fermat exponent `p - 2`. -/
private theorem toField_inv_chain (x : Field) :
    toField (inv x) = toField x ^ (fieldSize - 2) := by
  simp only [inv, toField_mul, toField_square, toField_squareN]
  ring_nf

/-- Fast inversion agrees with inversion in the canonical field. -/
@[simp]
theorem toField_inv (x : Field) : toField x⁻¹ = (toField x)⁻¹ := by
  rw [inv_def, toField_inv_chain]
  by_cases hx : toField x = 0
  · rw [hx, inv_zero, zero_pow (by decide : fieldSize - 2 ≠ 0)]
  · rw [inv_eq_pow hx]

/-- Fast division agrees with division in the canonical field. -/
@[simp]
theorem toField_div (x y : Field) : toField (x / y) = toField x / toField y := by
  rw [div_def, toField_mul, toField_inv]
  rfl

/-- Natural casts into fast form agree with natural casts into the canonical field. -/
@[simp]
theorem toField_natCast (n : ℕ) : toField (n : Field) = (n : Goldilocks.Field) := by
  show toField (ofNat n) = _
  rw [ofNat, toField_ofCanonicalNat, ZMod.natCast_mod]

/-- Integer casts into fast form agree with integer casts into the canonical field. -/
@[simp]
theorem toField_intCast (n : ℤ) : toField (n : Field) = (n : Goldilocks.Field) := by
  show toField (ofField (n : Goldilocks.Field)) = _
  rw [toField_ofField]

/-- Natural scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_nsmul (n : ℕ) (x : Field) : toField (n • x) = n • toField x := by
  show toField ((n : Field) * x) = n • toField x
  rw [toField_mul, toField_natCast, nsmul_eq_mul]

/-- Integer scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_zsmul (n : ℤ) (x : Field) : toField (n • x) = n • toField x := by
  show toField ((n : Field) * x) = n • toField x
  rw [toField_mul, toField_intCast, zsmul_eq_mul]

/-- Natural powers through the `Pow` instance are preserved by `toField`. -/
@[simp]
theorem toField_npow (x : Field) (n : ℕ) : toField (x ^ n) = toField x ^ n := by
  show toField (pow x n) = toField x ^ n
  rw [toField_pow]

/-- Integer powers through the `Pow` instance are preserved by `toField`. -/
@[simp]
theorem toField_zpow (x : Field) (n : ℤ) : toField (x ^ n) = toField x ^ n := by
  cases n with
  | ofNat n =>
      show toField (pow x n) = toField x ^ (Int.ofNat n)
      rw [toField_pow]
      exact (zpow_natCast (toField x) n).symm
  | negSucc n =>
      show toField (pow (inv x) (n + 1)) = toField x ^ (Int.negSucc n)
      have hinv : toField (inv x) = (toField x)⁻¹ := by
        rw [← inv_def, toField_inv]
      rw [toField_pow, hinv, zpow_negSucc, inv_pow]

/-- Nonnegative rational casts into fast form agree with canonical-field casts. -/
@[simp]
theorem toField_nnratCast (q : ℚ≥0) : toField (q : Field) = (q : Goldilocks.Field) := by
  show toField (ofField (q : Goldilocks.Field)) = _
  rw [toField_ofField]

/-- Rational casts into fast form agree with canonical-field casts. -/
@[simp]
theorem toField_ratCast (q : ℚ) : toField (q : Field) = (q : Goldilocks.Field) := by
  show toField (ofField (q : Goldilocks.Field)) = _
  rw [toField_ofField]

/-- Nonnegative rational scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_nnqsmul (q : ℚ≥0) (x : Field) : toField (q • x) = q • toField x := by
  show toField (ofField (q • toField x)) = q • toField x
  rw [toField_ofField]

/-- Rational scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_qsmul (q : ℚ) (x : Field) : toField (q • x) = q • toField x := by
  show toField (ofField (q • toField x)) = q • toField x
  rw [toField_ofField]

/-! ## Algebraic structure -/

/-- Ring equivalence between the fast representation and the canonical field. -/
def ringEquiv : Field ≃+* Goldilocks.Field where
  toFun := toField
  invFun := ofField
  left_inv := ofField_toField
  right_inv := toField_ofField
  map_add' := toField_add
  map_mul' := toField_mul

@[simp]
theorem ringEquiv_apply (x : Field) : ringEquiv x = toField x := rfl

@[simp]
theorem ringEquiv_symm_apply (x : Goldilocks.Field) : ringEquiv.symm x = ofField x := rfl

/-- Field instance transferred from the canonical field through `toField`. -/
instance instField : _root_.Field Field := by
  apply toField_injective.field toField <;> simp

/-- Fast Goldilocks is a non-binary field. -/
instance instNonBinaryField : NonBinaryField Field where
  char_neq_2 := by
    intro h
    apply (by decide : (2 : Goldilocks.Field) ≠ 0)
    calc
      _ = toField ((2 : ℕ) : Field) := (toField_natCast 2).symm
      _ = toField (0 : Field) := congrArg toField h
      _ = 0 := toField_zero

end Goldilocks.Fast
