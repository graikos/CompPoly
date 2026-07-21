/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Varun Thakore, Georgios Raikos
-/

import CompPoly.Fields.Goldilocks.FastExt

/-!
# Extern-Backed Fast Goldilocks Tests

Runtime regression checks for `Goldilocks.Fast.Ext`: the extern-backed operations are
compared against the verified implementation on boundary values and a deterministic
pseudorandom sweep. The Lean models are already proved equal to the verified operations;
what these checks exercise is the trusted C in `native/comppoly_goldilocks.c`, which
proofs cannot see. They live in an executable because the module interpreter cannot call
project-local externs.

Run this file with: `lake exe CompPolyGoldilocksFastExtTests`
-/

namespace CompPolyTests.Fields.Goldilocks.FastExt

open Goldilocks.Fast

private def check (name : String) (ok : Bool) : IO Bool := do
  if ok then
    return true
  else
    IO.eprintln s!"failed: {name}"
    return false

/-- One step of Knuth's MMIX 64-bit LCG. -/
private def lcg (s : UInt64) : UInt64 :=
  s * 6364136223846793005 + 1442695040888963407

/-- Boundary words: small values, limb edges, values around `p`, and the word maximum. -/
private def boundaryWords : List UInt64 :=
  [0, 1, 2, 73,
   0xFFFFFFFE, 0xFFFFFFFF, 0x100000000, 0x100000001,
   0xFFFFFFFF00000000, modulus - 1, modulus, modulus + 1,
   0xFFFFFFFFFFFFFFFF]

/-- 512 deterministic pseudorandom words. -/
private def randomWords : List UInt64 := Id.run do
  let mut s : UInt64 := 0x243F6A8885A308D3
  let mut out : List UInt64 := []
  for _ in [0:512] do
    s := lcg s
    out := s :: out
  return out

private def words : List UInt64 := boundaryWords ++ randomWords

private def elems : List Field := words.map .ofUInt64

/-- The raw extern words agree with the verified words on all pairs. -/
private def mulHiOk : Bool :=
  words.all fun a => words.all fun b => Ext.mulHi a b == wideMulHi a b

private def mulRawNativeOk : Bool :=
  words.all fun a => words.all fun b => Ext.mulRawNative a b == mulRaw a b

private def mulNativeOk : Bool :=
  (elems.take 60).all fun x => (elems.take 60).all fun y => Ext.mulNative x y = x * y

private def mulWithMulHiOk : Bool :=
  (elems.take 60).all fun x => (elems.take 60).all fun y => Ext.mulWithMulHi x y = x * y

private def squareOk : Bool :=
  elems.all fun x =>
    Ext.squareNative x = square x && Ext.squareWithMulHi x = square x
      && Ext.squareNNative x 8 = squareN x 8

private def invOk : Bool :=
  elems.all fun x => Ext.invNative x = x⁻¹

private def divOk : Bool :=
  (elems.take 40).all fun x => (elems.take 40).all fun y => Ext.divNative x y = x / y

private def runChecks : IO Bool := do
  let ok1 ← check "mulHi raw sweep" mulHiOk
  let ok2 ← check "mulRawNative raw sweep" mulRawNativeOk
  let ok3 ← check "mulNative" mulNativeOk
  let ok4 ← check "mulWithMulHi" mulWithMulHiOk
  let ok5 ← check "squareNative / squareWithMulHi / squareNNative" squareOk
  let ok6 ← check "invNative" invOk
  let ok7 ← check "divNative" divOk
  return ok1 && ok2 && ok3 && ok4 && ok5 && ok6 && ok7

end CompPolyTests.Fields.Goldilocks.FastExt

/-- Run the extern-backed Goldilocks regression checks. -/
def main : IO UInt32 := do
  if ← CompPolyTests.Fields.Goldilocks.FastExt.runChecks then
    IO.println "all extern-backed Goldilocks checks passed"
    return 0
  else
    return 1
