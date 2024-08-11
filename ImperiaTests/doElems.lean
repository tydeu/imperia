/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Imperia.Do.Elab

open Imperia

/-! ## Test unimplemented `do` elements -/

open Lean Elab Command in
def checkKinds : CommandElabM Unit := do
  let attrKinds {α} (s : KeyedDeclsAttribute.ExtensionState α) : NameSet :=
    s.table.fold (init := {}) fun ks k e => e.foldl (init := ks) fun ks e =>
      if !s.erased.contains e.declName then ks.insert k else ks
  let μdoKinds := attrKinds <| μdoElabAttr.ext.getState (← getEnv)
  let cats := Parser.parserExtension.getState (← getEnv) |>.categories
  let doKinds := cats.find? `doElem |>.get!.kinds
  let macroKinds := attrKinds <| macroAttribute.ext.getState (← getEnv)
  let consts := doKinds.foldl (init := []) fun ks k _ =>
    if μdoKinds.contains k || macroKinds.contains k then ks else
    MessageData.ofConst (mkConst k) :: ks
  logInfo m!"unimplemented kinds:{indentD <| MessageData.joinSep consts "\n"}"
  let consts := doKinds.foldl (init := []) fun ks k _ =>
    if macroKinds.contains k then MessageData.ofConst (mkConst k) :: ks else ks
  logInfo m!"macro kinds:{indentD <| MessageData.joinSep consts "\n"}"

/--
info: unimplemented kinds:
  Lean.Parser.Term.doReassign
  Lean.Parser.Term.doReassignArrow
  Lean.Parser.Term.doLetRec
  Lean.Parser.Term.doAssert
  Lean.Parser.Term.doMatchExpr
  Lean.Parser.Term.doHave
  Lean.Parser.Term.doLetMetaExpr
  Lean.Parser.Term.doBreak
  Lean.Parser.Term.doFor
  Lean.Parser.Term.doLetExpr
  Lean.Parser.Term.doContinue
  Lean.Parser.Term.doDbgTrace
---
info: macro kinds:
  Lean.«doElemTrace[_]__»
  Lean.doElemRepeat__Until_
  Lean.doElemRepeat_
  doRaise
  Lean.«doElemWhile_:_Do_»
  Lean.doElemWhile_Do_
-/
#guard_msgs in run_cmd checkKinds

/-! ## Test implemented `do` elements -/

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

-- TODO: `doTry` test (requires fixes)

/-! ## Test `do` macros -/

open Lean Elab Command in
def doTrace : CommandElabM Unit := μdo
  trace[bogus] "some text"
