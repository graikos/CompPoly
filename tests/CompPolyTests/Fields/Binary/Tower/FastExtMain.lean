/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPolyTests.Fields.Binary.Tower.FastExt

/-!
# Entry Point for `CompPolyBTExtTests`

Kept outside the `CompPolyTests` root so its `main` cannot collide with other
executable test modules.
-/

/-- Run the extern-backed binary tower regression checks and latency loops. -/
def main : IO UInt32 :=
  CompPolyTests.Fields.Binary.Tower.FastExt.run
