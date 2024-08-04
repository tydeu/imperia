/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Parser
import Imperia.Cont

open Lean Parser Elab

namespace Imperia

abbrev DoElem := TSyntax `doElem
abbrev DoSeq := TSyntax ``Term.doSeq

abbrev MatchAlt := TSyntax ``Term.matchAlt
abbrev doMatchAlt := Term.matchAlt Term.doSeq

instance : Coe Term DoElem where
  coe x := Unhygienic.run `(doElem|$x:term)

instance : Coe Ident (TSyntax ``binderIdent) where
  coe x := Unhygienic.run `(binderIdent|$x:ident)

def mkBinderIdentPat (x : TSyntax [identKind, ``Term.hole]) : Term := Unhygienic.run do
  match x with
  | `($id:ident) => pure id
  | _ => `(_)

instance : Coe (TSyntax [identKind, ``Term.hole]) Term := ⟨mkBinderIdentPat⟩

def expandDoSeq (x : DoSeq) : MacroM (Array DoElem) :=
  match x with
  | `(Term.doSeq|$[$xs $[;]?]*) => pure xs
  | `(Term.doSeq|{$[$xs $[;]?]*}) => pure xs
  | x => Macro.throwErrorAt x "ill-formed `do` sequence"
