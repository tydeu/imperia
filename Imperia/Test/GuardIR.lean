/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Elab.Command
import Lean.Util.Diff

open Lean Diff Elab Command

namespace Imperia

deriving instance BEq for IR.Param
deriving instance BEq for IR.DeclInfo
deriving instance BEq for ExternEntry
deriving instance BEq for ExternAttrData

def diffIRParams (actual expected : Array (IR.Param)) : Except String Unit := do
  if h_sz : actual.size = expected.size then
    for h : i in [0:actual.size] do
      have : i < expected.size := h_sz ▸ h.upper
      unless actual[i].ty == expected[i].ty do
        throw s!"type mismatch at {i}: got {actual[i].ty}, expected {expected[i].ty}"
  else
    throw s!"arity mismatch: got {actual.size}, expected {expected.size}"

def diffIRFnBody (afn xfn : Name) (abody xbody : IR.FnBody) : Except String Unit := do
  unless abody == xbody do
    let air := (toString abody).replace (afn.toString false) (xfn.toString false)
    let alns := air.split (· == '\n') |>.toArray
    let xlns := (toString xbody).split (· == '\n') |>.toArray
    let diffs := diff xlns alns
    unless diffs.all (fun ⟨act,_⟩ => act matches .skip) do
      throw <| linesToString diffs

def diffIRDecl (actual expected : IR.Decl) : Except String Unit := do
  match actual, expected with
  | .fdecl afn aps aty abody ainfo, .fdecl xfn xps xty xbody xinfo =>
    if let .error e := diffIRParams aps xps then
      throw s!"parameter mismatch: {e}"
    unless aty == xty do
      throw s!"return type mismatch: got {aty}, expected {xty}"
    unless ainfo == xinfo do
      throw "declaration info mismatch"
    if let .error diff := diffIRFnBody afn xfn abody xbody then
      throw s!"body mismatch:\n{diff}"
  | .extern _ aps aty xdata, .extern _ xps xty ydata =>
    if let .error e := diffIRParams aps xps then
      throw s!"parameter mismatch: {e}"
    unless aty == xty do
      throw s!"return type mismatch: got {aty}, expected {xty}"
    unless xdata == ydata do
      throw "declaration info mismatch"
  | _, _ =>
    throw "declaration kind mismatch"

scoped elab kw:"#guard_ir" actId:ident expId:ident : command => do
  let actDeclName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo actId
  let expDeclName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo expId
  let env ← getEnv
  let some actDecl := IR.findEnvDecl env actDeclName
    | throwErrorAt actId "no IR found for {actDeclName}"
  let some envDecl := IR.findEnvDecl env expDeclName
    | throwErrorAt actId "no IR found for {actDeclName}"
  if let .error e := diffIRDecl actDecl envDecl then
    throwErrorAt kw "IR differs: {e}"
