# Accompanying artifact for PLDI submission 2024

The current artifact provides an implementation of Zilly, a reactive language whose [abstract syntax](./Zilly_Abstract_Syntax.pdf) is that of a imperative with opt-in lazy evaluation turing complete language.

We decided to embed Zilly because of its unique challenges as an embedded language:

- Default strict evaluation strategy with opt-in lazyness vs haskell lazy by default with opt-in lazyness.
- Lazyness "levels" (how many times we have to evaluate an expression till we get a reduced value) are statically typed contrary to haskell, which are hidden.
- Variables can hold un/reduced (reactive) expressions.
- Higher order functions, means we have to embed second order logic inside Haskell's type system.

## Project Structure

This is a cabal project, so please run `cabal v2-repl` in order to load the ghci.

- `Zilly.hs`: Definition of the language, this file holds the interfaces and type judgments of Zilly.
- `Basic.hs`: A basic interpreter for `Zilly.hs`
- `ZTest.hs`: Holds some example Zilly programs written generically (`exampleX`) and concretely (`bX`).
