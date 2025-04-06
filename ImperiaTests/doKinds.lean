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
  Lean.Parser.Term.doTry
  Lean.Parser.Term.doLetRec
  Lean.Parser.Term.doAssert
  Lean.Parser.Term.doMatchExpr
  Lean.Parser.Term.doHave
  Lean.Parser.Term.doLetMetaExpr
  Lean.Parser.Term.doLetExpr
  Lean.Parser.Term.doBreak
  Lean.Parser.Term.doContinue
  Lean.Parser.Term.doDbgTrace
---
info: macro kinds:
  doYield
  Lean.«doElemTrace[_]__»
  Lean.doElemRepeat__Until_
  Lean.doElemRepeat_
  doRaise
  Lean.«doElemWhile_:_Do_»
  Lean.doElemWhile_Do_
-/
#guard_msgs in run_cmd checkKinds
