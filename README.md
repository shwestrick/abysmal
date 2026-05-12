# abysmal

A nanopass compiler frontend for Standard ML. Very much a work in progress. Very vibe-coded.

## What it does

Parses `.sml` and `.mlb` source files and runs them through a sequence of
translation passes, each eliminating one syntactic concept and producing a
strictly smaller IR. Invariants are enforced by types: eliminated forms simply
don't exist in downstream IRs.

Every pass also produces a provenance table mapping each output node back to
its origin — either a source byte span (for parsed nodes) or the input node
that caused it to be synthesized (for desugared nodes).

## Passes (in order)

**Debasification** — Eliminates the MLBasis layer. Inline `basis`/`local`
MLB declarations are expanded into SML `local...in...end` blocks using
globally unique structure names. Shared sub-MLBs are materialized once at
the top level.

**Record unification** — Eliminates tuples, unit, and record punning.
Tuples become records with numeric labels (`"1"`, `"2"`, ...). Unit becomes
an empty record. Punned record fields (`{x}`) become explicit `{x = x}`.

**Boolean elaboration** — Eliminates `if/then/else`, `andalso`, and `orelse`.
All three desugar into `case` expressions.

**Infix elaboration** — Eliminates infix operators and infix function
definitions. `left opr right` becomes `opr (left, right)` (as a record).
`infix`/`infixr`/`nonfix` declarations are dropped.

**TODO: more to come...**

## Build

```
make        # requires mlton
make fmt    # requires smlfmt
make clean
```

Input: any `.sml`, `.sig`, `.fun`, or `.mlb` file.
Output: JSON AST dumps at each pass stage (printed to stdout).
