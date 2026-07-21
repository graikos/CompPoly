/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Varun Thakore
-/

import CompPoly.Fields.Basic
import CompPoly.Fields.PrattCertificate

/-!
# Goldilocks Prime Field `2^{64} - 2^{32} + 1`

The canonical `ZMod` model of the Goldilocks prime field, used in Plonky2/3.
-/

namespace Goldilocks

/-- The Goldilocks field modulus, `2^64 - 2^32 + 1`. -/
@[reducible]
def fieldSize : ℕ := 2 ^ 64 - 2 ^ 32 + 1

/-- The Goldilocks prime field as a `ZMod`. -/
abbrev Field := ZMod fieldSize

/-- The Goldilocks modulus is prime, verified by a Pratt certificate. -/
theorem is_prime : Nat.Prime fieldSize := by
  unfold fieldSize
  pratt

instance : Fact (Nat.Prime fieldSize) := ⟨is_prime⟩

instance : _root_.Field Field := ZMod.instField fieldSize

instance : NonBinaryField Field where
  char_neq_2 := by
    simpa [Field, fieldSize] using
      (by decide : (2 : ZMod (2 ^ 64 - 2 ^ 32 + 1)) ≠ 0)

end Goldilocks
