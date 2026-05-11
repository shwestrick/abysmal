structure AfterDebasification =
struct

  type node_id = NodeID.t
  type longid = string Seq.t

  (** Reuse SourceAst's SML sub-types directly.  All constructors and record
    * fields are identical; no conversion is needed for 1:1 nodes.
    *
    * Changes from SourceAst:
    *   - Mlb structure removed
    *   - program datatype removed
    *   - sml_ast removed
    *   - t simplified: no Mlb case; always a flat sequence of topdecs
    *)
  structure Ty = SourceAst.Ty
  structure Pat = SourceAst.Pat
  structure Exp = SourceAst.Exp
  structure Sig = SourceAst.Sig
  structure Str = SourceAst.Str
  structure Fun = SourceAst.Fun

  datatype topdec = datatype SourceAst.topdec

  datatype t = Program of {id: node_id, topdecs: topdec Seq.t}

end
