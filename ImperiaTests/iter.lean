/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Imperia
import Imperia.Test.GuardIR

open Imperia

@[inline] def String.chars (s : String) : Iter μ Char :=
  let rec @[specialize] loop (p : String.Pos) : Iter μ Char := μdo
    if h : s.atEnd p then
      return
    else
      yield s.get' p h
      loop (s.next' p h)
  termination_by s.utf8ByteSize - p.byteIdx
  decreasing_by
    simp [atEnd] at h
    exact Nat.sub_lt_sub_left h (lt_next s p)
  loop 0

instance : Iterable μ String Char := ⟨String.chars⟩

@[simp] theorem String.iter_eq
  {s : String} : Iterable.iter (μ := μ) s = s.chars
:= rfl

def testRef (s : String) : IO Unit :=
  let rec loop (p : String.Pos) := do
    if h : s.atEnd p then
      return
    else
      IO.println (s.get' p h)
      loop (s.next' p h)
  termination_by s.utf8ByteSize - p.byteIdx
  decreasing_by
    simp [String.atEnd] at h
    exact Nat.sub_lt_sub_left h (String.lt_next s p)
  loop 0

def forInTest (s : String) : IO Unit := μdo
  for c in s do
    IO.println c

/--
info: def forInTest : String → IO Unit :=
fun s =>
  Cont.run
    (iter s
      (fun c _μdo_loop => do
        liftM (IO.println c)
        _μdo_loop ())
      fun x => nop)
-/
#guard_msgs in #print forInTest

#guard_ir String.chars.loop._at.forInTest._spec_1._at.forInTest._spec_2 testRef.loop

@[simp] theorem liftM_eq_liftM_liftM {n o m α}
  [MonadLift n o] [MonadLiftT m n] {x : m α} :
  liftM x = liftM (m := n) (n := o) (liftM x)
:= rfl

example : @forInTest = @testRef := by
  funext s
  simp only [forInTest, testRef]
  let charsLoop s i :=
    @String.chars.loop (Cont (IO Unit) Empty) s i
      (fun c loop => bind (IO.println c) >>= loop)
      (fun x => halt) Empty.elim
  have charsLoop_def (s) (i) :
    charsLoop s i =
      @String.chars.loop (Cont (IO Unit) Empty) s i
        (fun c loop => bind (IO.println c) >>= loop)
        (fun x => halt) Empty.elim
    := rfl
  suffices h : ∀ s i, testRef.loop s i = charsLoop s i by
    simp [String.chars, ← charsLoop_def, h]
  intro s i
  induction i using testRef.loop.induct s with
  | case1 i h =>
    unfold testRef.loop charsLoop String.chars.loop
    simp [h]
  | case2 i h ih =>
    simp only [String.next'_eq] at ih
    unfold testRef.loop charsLoop String.chars.loop
    simp [h, ← charsLoop_def, ih]
