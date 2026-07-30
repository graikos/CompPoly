/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.Binary.Tower.Fast

/-!
# Extern-Backed Binary Tower Operations (opt-in)

Native backends for the fast binary tower stack; the verified pure-Lean operations remain
the default. Each `@[extern]` declaration carries the verified Lean implementation as its
body, so proofs only ever see the verified ladder. Unlike `Native256Ext`, the native
multiplication kernels are not transcriptions: `native/comppoly_bt.c` computes the same
function by a different route (table-accelerated Karatsuba), so runtime agreement is
enforced by `lake exe CompPolyBTExtTests`, which proofs cannot see. Inversion is only a
*candidate*: each use site checks it with one multiplication and falls back to the proven
descent, so it adds no runtime trust beyond the multiplication kernel. The module
interpreter cannot call project-local externs, so the runtime checks live in an executable.
-/

namespace ConcreteBinaryTower.Fast.Ext

/-! ## Extern word kernels -/

/-- GF(2^64) multiplication; compiled code calls the trusted native `comppoly_bt_mul64`. -/
@[extern "comppoly_bt_mul64"]
def mul64Native (a b : UInt64) : UInt64 := mul64 a b

/-- `mul64Native` agrees with the verified `mul64`. -/
theorem mul64Native_eq (a b : UInt64) : mul64Native a b = mul64 a b := rfl

/-- GF(2^64) inverse candidate; compiled code calls the trusted native `comppoly_bt_inv64`.
Callers verify the result and fall back, so its provenance never affects correctness. -/
@[extern "comppoly_bt_inv64"]
def inv64Candidate (v : UInt64) : UInt64 := inv64 v

/-- `inv64Candidate` agrees with the verified `inv64`. -/
theorem inv64Candidate_eq (v : UInt64) : inv64Candidate v = inv64 v := rfl

/-! ## Level-6 carrier operations -/

/-- `BT64` multiplication through the native kernel. -/
@[inline] def bt64MulNative (a b : BT64) : BT64 :=
  ⟨mul64Native a.val b.val, UInt64.toNat_lt _⟩

/-- `bt64MulNative` agrees with the verified multiplication. -/
theorem bt64MulNative_eq_mul (a b : BT64) : bt64MulNative a b = a * b := rfl

/-- `BT64` inversion: the native descent candidate, checked by one native multiplication,
with the verified descent as fallback (taken only for `0` or a candidate miss). -/
@[inline] def bt64InvNative (a : BT64) : BT64 :=
  let z := inv64Candidate a.val
  if mul64Native a.val z == 1 then ⟨z, UInt64.toNat_lt _⟩ else a⁻¹

/-- `bt64InvNative` agrees with the verified inversion. -/
theorem bt64InvNative_eq_inv (a : BT64) : bt64InvNative a = a⁻¹ := by
  simp only [bt64InvNative]
  split <;> rfl

/-! ## Level-7 operations -/

/-- GF(2^128) multiplication; compiled code calls the trusted native `comppoly_bt128_mul`. -/
@[extern "comppoly_bt128_mul"]
def mul128Native (a b : @& FastBT128) : FastBT128 := FastBT128.mul a b

/-- `mul128Native` agrees with the verified multiplication. -/
theorem mul128Native_eq_mul (a b : FastBT128) : mul128Native a b = a * b := rfl

/-- GF(2^128) inverse candidate; compiled code calls the trusted native
`comppoly_bt128_inv`. Callers verify the result and fall back. -/
@[extern "comppoly_bt128_inv"]
def inv128Candidate (v : @& FastBT128) : FastBT128 := FastBT128.inv v

/-- `inv128Candidate` agrees with the verified descent. -/
theorem inv128Candidate_eq (v : FastBT128) : inv128Candidate v = FastBT128.inv v := rfl

/-- GF(2^128) inversion: the native descent candidate, checked by one native
multiplication, with the verified descent as fallback. -/
@[inline] def inv128Native (v : FastBT128) : FastBT128 :=
  let z := inv128Candidate v
  if mul128Native v z == 1 then z else v⁻¹

/-- `inv128Native` agrees with the verified inversion. -/
theorem inv128Native_eq_inv (v : FastBT128) : inv128Native v = v⁻¹ := by
  simp only [inv128Native]
  split <;> rfl

end ConcreteBinaryTower.Fast.Ext
