/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Imperia
import Imperia.Test.Init
import Imperia.Test.GuardIR
import Lean.Parser

open Imperia Lean Parser

/-! ## `ParserState.hasError` Monkey Patch -/

/-- IR optimized implementation of `Lean.Parser.ParserState.hasError`. -/
@[inline] abbrev hasError (s : ParserState) : Bool :=
  s.errorMsg.isSome

@[csimp, simp]
theorem eq_hasError : @ParserState.hasError = @hasError := by
  funext s
  simp only [hasError, ParserState.hasError]
  cases s.errorMsg
  · decide
  · conv => lhs; whnf
    simp

@[simp] theorem hasError_eq : hasError s = s.errorMsg.isSome := rfl

/-! ## `ParserFn` Primitives  -/

namespace Lean.Parser.ParserFn

@[simp] theorem app_ite [Decidable P] {t e : ParserFn} :
  ite P t e c s = ite P (t c s) (e c s)
:= by split <;> rfl

@[simp] theorem app_dite [Decidable P] {t : P → ParserFn} {e : ¬ P → ParserFn} :
  dite P t e c s = dite P (fun h => t h c s) (fun h => e h c s)
:= by split <;> rfl

@[always_inline, inline] protected def nop : ParserFn :=
  fun _ s => s

instance : Nop ParserFn := ⟨ParserFn.nop⟩

@[simp] theorem app_nop : (nop : ParserFn) c s = s := rfl

@[always_inline, inline]
protected def andThen (p : ParserFn) (f : Unit → ParserFn) : ParserFn := fun c s =>
  let s := p c s; f () c s

instance : AndThen ParserFn := ⟨ParserFn.andThen⟩

@[simp] theorem app_andThen {p p' : ParserFn} : (p >> p') c s = p' c (p c s) := rfl

@[always_inline, inline]
protected def ParserFn.read (f : ParserContext → ParserFn) : ParserFn := fun c s =>
  f c c s

instance : MonadReaderOf ParserContext (Cont ParserFn) := ⟨ParserFn.read⟩

@[simp] theorem app_read : (read : Cont ParserFn ParserContext) k c s = k c c s := rfl

@[always_inline, inline]
protected def modifyState (f : ParserState → ParserState) : ParserFn := fun _ s =>
  f s

instance : ModifyState ParserState ParserFn := ⟨ParserFn.modifyState⟩

@[simp] theorem app_modifyState : (modifyState f : ParserFn) c s = f s := rfl

@[always_inline, inline]
protected def modifyGet (f : ParserState → α × ParserState) : Cont ParserFn α := Cont.mk fun k c s =>
  let (a, s) := f s; k a c s

instance : ModifyGet ParserState (Cont ParserFn) := ⟨ParserFn.modifyGet⟩

@[simp] theorem app_modifyGet :
  (modifyGet f : Cont ParserFn α) k c s = let (a, s) := f s; k a c s
:= rfl

end Lean.Parser.ParserFn

@[always_inline, inline]
def guardError : Cont ParserFn Unit := Cont.mk fun k => μdo
  unless (← get).hasError do k ()

@[simp] theorem app_guardError :
  guardError k c s = if s.hasError then s else k () c s
:= by simp [guardError]

@[always_inline,inline]
def setErrorFn (e : Error) (pushMissing := true) : ParserFn := fun _ s =>
  let s := s.setError e
  if pushMissing then s.pushSyntax .missing else s

instance : SetError Parser.Error ParserFn := ⟨setErrorFn⟩

@[always_inline,inline]
def mkUnexpectedError (msg : String) (expected : List String := []) (pushMissing := true) : ParserFn :=
  fun _ s => s.mkUnexpectedError msg expected pushMissing

@[simp] theorem app_mkUnexpectedError :
  mkUnexpectedError msg expected pushMissing c s = s.mkUnexpectedError msg expected pushMissing
:= rfl

instance : SetError String ParserFn := ⟨mkUnexpectedError⟩

@[simp] theorem app_setUnexpectedError {msg : String} : (setError msg : ParserFn) c s = s.mkUnexpectedError msg := rfl

@[always_inline, inline]
def mkEOIError (expected : List String := []) : ParserFn :=
  fun _ s => s.mkEOIError expected

@[simp] theorem app_mkEOIError : mkEOIError expected c s = s.mkEOIError expected := rfl

structure EOIError

instance : SetError EOIError ParserFn := ⟨fun _ => mkEOIError⟩

@[simp] theorem app_setEOIError : (setError EOIError.mk : ParserFn) c s = s.mkEOIError := rfl

abbrev unexpectedEOI := EOIError.mk

/-! ## `ParserFn` Combinators -/

@[always_inline, inline]
def anyChar : Cont ParserFn Char := μdo
  let input := (← read).input
  let i := (← get).pos
  if h : input.atEnd i then
    raise unexpectedEOI
  else
    let curr := input.get' i h
    modify (·.setPos <| input.next' i h)
    return curr

@[always_inline, inline]
def anyCharUnchecked : Cont ParserFn Char := μdo
  let input := (← read).input
  let i := (← get).pos
  let curr := input.get i
  modify (·.setPos <| input.next i)
  return curr

@[simp] theorem app_anyCharUnchecked :
  anyCharUnchecked k c s = k (c.input.get s.pos) c (s.setPos (c.input.next s.pos))
:= rfl

/-! ## `charLitFnAux` Test Case -/

/--
Reference implementation of core's `Lean.Parser.charLitFnAux`
adapted for IR equivalence checking with the Imperia implementations.

Differences from core:
* Uses the well-inlined custom `hasError` (via `csimp`) instead of
`ParserState.hasError`. This avoids IR inequalities due to differences
in `Option.none` hoisting.
-/
def charLitFnAuxRef (startPos : String.Pos) : ParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  if h : input.atEnd i then s.mkEOIError
  else
    let curr := input.get' i h
    let s    := s.setPos (input.next' i h)
    let s    := if curr == '\\' then quotedCharFn c s else s
    if s.hasError then s
    else
      let i    := s.pos
      let curr := input.get i
      let s    := s.setPos (input.next i)
      if curr == '\'' then mkNodeToken charLitKind startPos c s
      else s.mkUnexpectedError "missing end of character literal"

example : @charLitFnAuxRef = @charLitFnAux := rfl

def charLitFnAuxNew (startPos : String.Pos) : ParserFn := μdo
  let curr ← anyChar
  μdo if curr == '\\' then quotedCharFn
  guardError
  let curr ← anyCharUnchecked
  if curr == '\'' then
    mkNodeToken charLitKind startPos
  else
    raise "missing end of character literal"

#guard_ir charLitFnAuxRef charLitFnAuxNew

example : charLitFnAuxNew = charLitFnAuxRef := by
  funext startPos c s
  simp [charLitFnAuxNew, charLitFnAuxRef, anyChar, guardError]
  done

/-! ## Example Proof -/

@[simp] theorem setPos_eq {s : ParserState} : s.setPos i = {s with pos := i} := rfl

example
  (h_errMsg : s.errorMsg = none)
  (h_input : c.input = "'a'") (h_pos : s.pos = ⟨1⟩)
: charLitFnAuxNew 0 c s = mkNodeToken charLitKind 0 c (s.setPos ⟨3⟩)
:= by
  simp only [charLitFnAuxNew, anyChar, guardError]
  simp [h_pos, h_input, h_errMsg]
  done
