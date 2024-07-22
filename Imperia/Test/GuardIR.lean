/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Elab.Command

open Lean Elab Command

namespace Imperia

deriving instance BEq for IR.Param
deriving instance BEq for IR.DeclInfo
deriving instance BEq for ExternEntry
deriving instance BEq for ExternAttrData

def diffIRDecl (actual expected : IR.Decl) : Except String Unit := do
  match actual, expected with
  | .fdecl _ aps aty abody ainfo, .fdecl _ xps xty xbody xinfo =>
    unless aps == xps do
      throw "parameter mismatch"
    unless aty == xty do
      throw "return type mismatch"
    unless ainfo == xinfo do
      throw "declaration info mismatch"
    unless abody == xbody do
      throw "body mismatch"
  | .extern _ aps aty xdata, .extern _ xps xty ydata =>
    unless aps == xps do
      throw "parameter mismatch"
    unless aty == xty do
      throw "return type mismatch"
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
