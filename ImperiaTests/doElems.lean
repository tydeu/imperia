/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Imperia.Do.Elab

open Imperia

def doLet : Unit := μdo
  let _ := ← pure ()
  let 0 := ← pure 1
    | ← pure ()
  let _ ← pure ()
  ()

/-- error: `mut` has not been implemented for `μdo` -/
#guard_msgs in
def doLetMut : Unit := μdo
  let mut _ := ← pure ()
  let mut 0 := ← pure 1
    | ← pure ()
  let mut _ ← pure ()
  ()

def doMatch : Unit := μdo
  -- w/ jump
  match ← pure 0 with
  | 0 => ← pure ()
  | _ => ← pure ()
  -- w/o jump
  match ← pure 0 with
  | 0 => ← pure ()
  | _ => ← pure ()

/-- error: cannot lift `(<- ...)` over motive -/
#guard_msgs in
def doMatchLiftMotive : Unit := μdo
  match (motive := ← pure <| Unit → Cont Unit Empty) () with
  | _ => ()

def doIf : Unit := μdo
  -- w/ jump
  if ← pure false then ← pure ()
  else if ← pure false then ← pure ()
  else if ← pure false then ← pure ()
  else ← pure ()
  -- w/o jump
  if ← pure false then ← pure ()
  else if ← pure false then ← pure ()
  else if ← pure false then ← pure ()
  else ← pure ()

def doUnless : Unit := μdo
  unless ← pure true do ← pure () -- w/ jump
  unless ← pure true do ← pure () -- w/o jump

def doReturn : Id Nat := μdo
  return 0

def doReturnVoid : Unit := μdo
  return

/-- error: return must be the last element in a `do` sequence -/
#guard_msgs in
def doReturnNonterminal : Unit := μdo
  return
  return

def doRaise : Except Nat Unit := μdo
  raise 0

def doRaiseVoid : Except Unit Unit := μdo
  raise

/-- error: raise must be the last element in a `do` sequence -/
#guard_msgs in
def doRaiseNonterminal : Except Unit Unit := μdo
  raise
  raise

-- TODO: `doTry` test (requires touchup)
