# abysmal — project notes for Claude

## What this project is

A compiler frontend for Standard ML. It parses SML/MLB sources and
translates them through a sequence of typed IRs toward a target
representation. Currently the frontend produces a `SourceAst.t` and
then performs a series of nanopasses.

## Core design philosophy: parse, don't validate

Each pass eliminates syntactic sugar by producing a *strictly smaller*
type that cannot represent the eliminated forms. Invariants are encoded
in new types — not as side conditions checked on the previous IR.

Example: after record unification, `Ty.Tuple`, `Pat.Tuple`,
`Exp.Tuple`, `Exp.Unit`, `Pat.Unit`, and `Exp.RecordPun` are gone from
the output type. You cannot accidentally forget to handle them in a
downstream pass — the type simply doesn't have those constructors.

## File layout conventions

- `src/frontend/irs/<name>/` — AST type definitions (e.g. `SourceAst.sml`,
  `AfterRecordUnification.sml`)
- `src/frontend/translations/<name>/` — translation passes between IRs
- `src/provenance/` — provenance event type (`ProvenanceEvent.sml`),
  compiled as part of the frontend build

## Every pass tracks provenance

Every translation pass returns a provenance table alongside its output
AST: `OutputIR.t * (NodeID.t -> ProvenanceEvent.t)`.

- Nodes that are translated 1:1 keep their `node_id` from the input IR.
  Their provenance is inherited from the previous pass's table.
- Freshly synthesized nodes (e.g. from desugaring a tuple into record
  rows) emit `ProvenanceEvent.Synthesized {id, pass, origin, why}`.
- The `origin` field points to the input-IR node that caused the fresh
  node to be created, allowing provenance chains to be followed back to
  source.

The initial provenance table (from `ToSourceAst`) records every parsed
node as `ProvenanceEvent.Parsed {id, source}` where `source: Source.t`
carries the file path and byte span.

Inside each pass, use a local `emit` helper to append to `prov_entries`:

```sml
fun emit (id, p) =
  prov_entries := (id, p) :: !prov_entries

fun synth (origin: NodeID.t) (why: string) : NodeID.t =
  let val id = NodeID.fresh ()
  in emit (id, ProvenanceEvent.Synthesized {...}); id
  end
```

`emit` is the single point of contact with `prov_entries` — do not
prepend to the ref directly anywhere else in the pass.

## Translations

Every translation pass (except for `to-source/`, which is special)
should begin with `I` (input) and `O` (output) structure definitions,
defining the input and output IRs, and a corresponding signature.

structure BooleanElaboration:
sig
  val translate:
    AfterRecordUnification.t -> AfterBooleanElaboration.t * Provenance.t
end =
struct
  structure I = AfterRecordUnification
  structure O = AfterBooleanElaboration

  fun translate (input: I.t) : O.t * Provenance.t =
  ...
end

## State threading style

Use explicit parameter/return threading for state that affects the
traversal — do not use `ref` cells for that purpose.

Exception: write-only accumulators that don't influence the traversal
(like `prov_entries`) may use `ref` inside a local `let`, consistent
with how `ToSourceAst` handles them. Keep such refs strictly local.

## Formatting

Run `make fmt` (via `smlfmt`) before committing. Do not hand-format
around smlfmt's output.

## Build

```
make              # build with mlton
make fmt          # format with smlfmt
make clean        # remove build/
```

## Keeping README in sync

When adding a new pass, add a brief entry to `README.md` under the
**Passes (in order)** section describing what it eliminates. Always
make sure these appear in the correct order, from first to last
translation!

## Keeping the Makefile in sync

The `SOURCES` list in `Makefile` must stay consistent with every `.sml`
and `.mlb` file under `src/` (excluding `src/frontend/smlfmt/`). When
adding or removing a file, update `Makefile`, `src/frontend/sources.mlb`
(or the relevant `.mlb`), and delete any orphaned files. Verify with:

```
find src -not -path '*/smlfmt/*' \( -name '*.sml' -o -name '*.mlb' \) | sort
```