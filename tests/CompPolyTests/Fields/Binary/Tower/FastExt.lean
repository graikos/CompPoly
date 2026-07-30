/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.Binary.Tower.FastExt

/-!
# Extern-Backed Binary Tower Tests

Runtime regression checks for `ConcreteBinaryTower.Fast.Ext`: the extern-backed
operations are compared against the verified ladder on basis pairs, boundary values,
and a deterministic pseudorandom sweep, followed by latency measurements. The Lean
models are already proved equal to the verified operations; what these checks exercise
is the trusted C in `native/comppoly_bt.c`, which proofs cannot see. The inverse
candidates are compared directly because the checked wrappers cannot detect a broken
candidate: a miss silently takes the fallback. They live in an executable because the
module interpreter cannot call project-local externs.

Run this file with: `lake exe CompPolyBTExtTests`
-/

namespace CompPolyTests.Fields.Binary.Tower.FastExt

open ConcreteBinaryTower.Fast ConcreteBinaryTower.Fast.Ext

private def check (name : String) (ok : Bool) : IO Bool := do
  if ok then
    return true
  else
    IO.eprintln s!"failed: {name}"
    return false

/-- One step of Knuth's MMIX 64-bit LCG. -/
private def lcg (s : UInt64) : UInt64 :=
  s * 6364136223846793005 + 1442695040888963407

/-- The `i`-th basis word. -/
private def basis64 (i : Nat) : UInt64 :=
  (1 : UInt64) <<< UInt64.ofNat i

/-- The `i`-th level-7 basis element. -/
private def basis128 (i : Nat) : FastBT128 :=
  if i < 64 then ⟨basis64 i, 0⟩ else ⟨0, basis64 (i - 64)⟩

/-- Boundary words: small values, the generators of each half, and all-ones patterns. -/
private def edges64 : List UInt64 :=
  [0, 1, 2, 3, 0xFF, 0x10000, 0x80000000, 0x100000000, 0x100000001,
    0x8000000000000001, 0xFFFFFFFFFFFFFFFF]

/-- Level-6 checks: every edge and basis pair through the native multiplication, every
edge and a pseudorandom sweep through both inverse paths. -/
private def check64 : IO Bool := do
  let mut ok := true
  for i in [0:64] do
    for j in [0:64] do
      let a := basis64 i
      let b := basis64 j
      unless mul64Native a b == mul64 a b do
        ok := (← check s!"mul64 basis ({i}, {j})" false)
  for a in edges64 do
    for b in edges64 do
      ok := (← check s!"mul64 edge ({a}, {b})" (mul64Native a b == mul64 a b)) && ok
    ok := (← check s!"inv64 edge {a}" (inv64Candidate a == inv64 a)) && ok
  let mut s : UInt64 := 0xC0FFEE
  for _ in [0:100000] do
    let a := lcg s
    let b := lcg a
    s := b
    unless mul64Native a b == mul64 a b do
      ok := (← check s!"mul64 random ({a}, {b})" false)
    unless inv64Candidate a == inv64 a do
      ok := (← check s!"inv64 random {a}" false)
  ok := (← check "bt64InvNative zero" (bt64InvNative 0 == 0)) && ok
  return ok

/-- Level-7 checks: basis pairs through the native multiplication, a pseudorandom sweep
through multiplication and both inverse paths. -/
private def check128 : IO Bool := do
  let mut ok := true
  for i in [0:128] do
    for j in [0:128] do
      let a := basis128 i
      let b := basis128 j
      unless mul128Native a b == a * b do
        ok := (← check s!"mul128 basis ({i}, {j})" false)
  let mut s : UInt64 := 0xB1AB1A
  for _ in [0:50000] do
    let s1 := lcg s
    let s2 := lcg s1
    let s3 := lcg s2
    let s4 := lcg s3
    s := s4
    let a : FastBT128 := ⟨s1, s2⟩
    let b : FastBT128 := ⟨s3, s4⟩
    unless mul128Native a b == a * b do
      ok := (← check s!"mul128 random ({a.lo}, {a.hi}) ({b.lo}, {b.hi})" false)
    unless inv128Candidate a == FastBT128.inv a do
      ok := (← check s!"inv128 random ({a.lo}, {a.hi})" false)
    unless inv128Native a == a⁻¹ do
      ok := (← check s!"inv128Native random ({a.lo}, {a.hi})" false)
  ok := (← check "inv128 zero" (inv128Candidate 0 == FastBT128.inv 0)) && ok
  ok := (← check "inv128 one" (inv128Candidate 1 == FastBT128.inv 1)) && ok
  return ok

/-! ## Latency loops

Accumulator-chained so each iteration depends on the previous result. -/

private def loopMul64N : Nat → UInt64 → UInt64 → UInt64
  | 0, acc, _ => acc
  | n + 1, acc, x => loopMul64N n (mul64Native acc x) x

private def loopMul64P : Nat → UInt64 → UInt64 → UInt64
  | 0, acc, _ => acc
  | n + 1, acc, x => loopMul64P n (mul64 acc x) x

private def loopInv64N : Nat → UInt64 → UInt64 → UInt64
  | 0, acc, _ => acc
  | n + 1, acc, x => loopInv64N n (inv64Candidate (acc ^^^ x)) x

private def loopInv64P : Nat → UInt64 → UInt64 → UInt64
  | 0, acc, _ => acc
  | n + 1, acc, x => loopInv64P n (inv64 (acc ^^^ x)) x

private def loopMul128N : Nat → FastBT128 → FastBT128 → FastBT128
  | 0, acc, _ => acc
  | n + 1, acc, x => loopMul128N n (mul128Native acc x) x

private def loopMul128P : Nat → FastBT128 → FastBT128 → FastBT128
  | 0, acc, _ => acc
  | n + 1, acc, x => loopMul128P n (acc * x) x

private def loopInv128C : Nat → FastBT128 → FastBT128 → FastBT128
  | 0, acc, _ => acc
  | n + 1, acc, x => loopInv128C n (inv128Candidate (acc + x)) x

private def loopInv128N : Nat → FastBT128 → FastBT128 → FastBT128
  | 0, acc, _ => acc
  | n + 1, acc, x => loopInv128N n (inv128Native (acc + x)) x

private def loopInv128P : Nat → FastBT128 → FastBT128 → FastBT128
  | 0, acc, _ => acc
  | n + 1, acc, x => loopInv128P n ((acc + x)⁻¹) x

/-- Time `run n`, branching on the result before the second clock read so the compiler
cannot sink the work out of the measured window. -/
@[noinline] private def timeLoop (label : String) (n : Nat) (run : Nat → UInt64) :
    IO Unit := do
  let t0 ← IO.monoNanosNow
  let r := run n
  if r == 0xFFFFFFFFFFFFFFFF then IO.eprintln "sentinel hit"
  let t1 ← IO.monoNanosNow
  IO.println s!"{label}: {(t1 - t0).toFloat / n.toFloat} ns/op (sink {r})"

private def runBench : IO Unit := do
  let x64 : UInt64 := 0x9E3779B97F4A7C15
  let x128 : FastBT128 := ⟨0x9E3779B97F4A7C15, 0xD1B54A32D192ED03⟩
  let _ := loopMul64N 1000 1 x64
  IO.println "-- latency --"
  timeLoop "mul64 native " 2000000 (loopMul64N · 1 x64)
  timeLoop "mul64 pure   " 500000 (loopMul64P · 1 x64)
  timeLoop "inv64 native " 500000 (loopInv64N · 1 x64)
  timeLoop "inv64 pure   " 200000 (loopInv64P · 1 x64)
  timeLoop "mul128 native" 1000000 (fun n => (loopMul128N n 1 x128).lo)
  timeLoop "mul128 pure  " 200000 (fun n => (loopMul128P n 1 x128).lo)
  timeLoop "inv128 cand  " 500000 (fun n => (loopInv128C n 1 x128).lo)
  timeLoop "inv128 check " 500000 (fun n => (loopInv128N n 1 x128).lo)
  timeLoop "inv128 pure  " 100000 (fun n => (loopInv128P n 1 x128).lo)

/-- Aggregate result over both extern-backed levels. -/
def runChecks : IO Bool := do
  let ok1 ← check64
  let ok2 ← check128
  return ok1 && ok2

/-- Run the extern-backed binary tower regression checks and latency loops. -/
def run : IO UInt32 := do
  if ← runChecks then
    IO.println "all extern-backed binary tower checks passed"
    runBench
    return 0
  else
    return 1

end CompPolyTests.Fields.Binary.Tower.FastExt
