/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Varun Thakore, Georgios Raikos
-/

import CompPoly.Fields.Goldilocks.Fast

/-!
# Fast Goldilocks Field Tests

Regression checks for the verified `UInt64` representation.
-/

namespace Goldilocks.Fast

#guard (0 : Field).val = 0
#guard (1 : Field).val = 1
#guard (73 : Field).toNat = 73
#guard (Goldilocks.fieldSize : Field).toNat = 0
#guard (Goldilocks.fieldSize + 73 : Field).toNat = 73
#guard (Field.ofUInt64 (UInt64.ofNat (2 ^ 64 - 1))).toNat = 2 ^ 32 - 2
#guard ((Goldilocks.fieldSize - 1 : Field) + 4).toNat = 3
#guard ((Goldilocks.fieldSize - 1 : Field) + (Goldilocks.fieldSize - 1 : Field)).toNat =
  Goldilocks.fieldSize - 2
#guard ((17 : Field) - 6).toNat = 11
#guard ((6 : Field) - 17).toNat = Goldilocks.fieldSize - 11
#guard (-(0 : Field)).toNat = 0
#guard (-(1 : Field)).toNat = Goldilocks.fieldSize - 1
#guard ((Goldilocks.fieldSize - 1 : Field) * (Goldilocks.fieldSize - 1 : Field)).toNat = 1
#guard ((54321 : Field) * 54321).toField = ((54321 : Goldilocks.Field) ^ 2)
#guard ((73 : Field) ^ 0).toNat = 1
#guard ((73 : Field) ^ 1).toNat = 73
#guard ((987654321 : Field) ^ 19).toField = ((987654321 : Goldilocks.Field) ^ 19)
#guard ((987654321 : Field) ^ 511).toField = ((987654321 : Goldilocks.Field) ^ 511)
#guard ((0 : Field)⁻¹).toNat = 0
#guard ((73 : Field)⁻¹ * 73).toNat = 1
#guard ((73 : Field) / 73).toNat = 1
#guard ((73 : Field)⁻¹).toField = ((73 : Goldilocks.Field)⁻¹)
#guard ((73 : Field) ^ (-5 : Int)).toField = ((73 : Goldilocks.Field) ^ (-5 : Int))

end Goldilocks.Fast
