structure ProvenanceEvent =
struct

  datatype t =

  (** This node was produced by parsing a contiguous span of source text.
    * The Source.t carries both the file identity and the byte range. *)
    Parsed of {id: NodeID.t, source: Source.t}

  (** This node was freshly synthesized during a transformation pass.
    *
    * 'origin' is the id of the node whose elaboration caused this one to
    * be created (used to trace back to source).
    *
    * 'pass' names the translation pass (e.g. "record-unification").
    *
    * 'why' is a human-readable phrase describing the specific reason,
    * e.g. "tuple element label" or "punned identifier". *)
  | Synthesized of {id: NodeID.t, pass: string, origin: NodeID.t, why: string}

end
