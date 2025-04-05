# Imperia

Imperia is a **work-in-progress** experiment with imperative programming in Lean. At present, the focus is an alternative `do` notation (using the keyword `μdo`) that supports non-monadic types. However, the implementation is not complete, so it is currently lacking many features of the standard `do` notation (e.g., `try`, `for`, `mut`).

## Example

The standard approach to writing imperative programs in Lean is to use  `do` notation. The notation is very elegant, but it only supports monadic types.

To demonstrate how this can be a problem, consider Lean core's `ParserFn`, which is the type of primitive parser functions used to parse Lean. `ParserFn` is not a monad for performance reasons. This means that Lean parser functions can neither use `do` notation in their code or follow a Paersec-like functional style. Instead, they must be written in a very verbose and inelegant  manner that carefully tracks the state and context. A simple example is `charLitFnAux` in core:

```lean
/--
Parses the part of a character literal
after the initial quote (e.g., `a'` of `'a'`).

`startPos` is the position of the initial quote.
-/
def charLitFnAux (startPos : String.Pos) : ParserFn := fun c s =>
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
```

Imperia's `μdo` notation provides an alternative elaboration of the same do-elements of the standard `do` notation, but with support for types like `ParserFn`. With  `μdo`, `charLitFnAux` can be written in Parsec-like functional style:

```lean
def charLitFnAux (startPos : String.Pos) : ParserFn := μdo
  let curr ← anyChar
  μdo if curr == '\\' then quotedCharFn
  guardError
  let curr ← anyCharUnchecked
  if curr == '\'' then
    mkNodeToken charLitKind startPos
  else
    raise "missing end of character literal"
```

While it may look better, recall that `ParserFn` was not a monad for a reason -- performance! Fortunately, Imperia's approach manages to maintain the same IR and even the same `simp` normal forms as the original implementation.

If this has piqued your curiosity, [ImperiaTests/parser.lean](ImperiaTests/parser.lean) contains the nitty-gritty details of how this Parsec-like `ParserFn` function is implemented with Imperia.
