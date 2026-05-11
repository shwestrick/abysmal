structure Debasification:
sig
  val translate: SourceAst.t -> AfterDebasification.t * Provenance.t
end =
struct
  structure I = SourceAst
  structure O = AfterDebasification

  fun translate (input: I.t) : O.t * Provenance.t =
    let
      val pass = "Debasification"

      val prov_entries: (NodeID.t * ProvenanceEvent.t) list ref = ref []

      fun emit (id, p) =
        prov_entries := (id, p) :: !prov_entries

      fun synth (origin: NodeID.t) (why: string) : NodeID.t =
        let
          val id = NodeID.fresh ()
        in
          emit (id, ProvenanceEvent.Synthesized
            {id = id, pass = pass, origin = origin, why = why});
          id
        end

      fun lookup (id: NodeID.t) : ProvenanceEvent.t =
        case
          List.find (fn (id', _) => NodeID.compare (id, id') = EQUAL)
            (!prov_entries)
        of
          SOME (_, p) => p
        | NONE =>
            raise Fail
              ("Debasification: no provenance for " ^ NodeID.toString id)

      (** A namespace describes what unique-globally-named exports a basis makes
        * available.  Each entry pairs the public name (as declared in the MLB
        * filter) with the unique synthesised SML identifier.
        *
        * Unique names use the scheme  basname ^ "__S__" ^ public  so they
        * cannot clash with user-written SML identifiers.
        *)
      type namespace =
        { structures: {public: string, unique: string} list
        , signatures: {public: string, unique: string} list
        , functors: {public: string, unique: string} list
        }

      val empty_ns: namespace =
        {structures = [], signatures = [], functors = []}

      (** Merge two namespaces; entries from ns2 shadow same-named entries in ns1. *)
      fun merge_ns (ns1: namespace) (ns2: namespace) : namespace =
        let
          fun merge l1 l2 =
            let
              val keys2 = List.map #public l2
              val l1' =
                List.filter
                  (fn {public, ...} =>
                     not (List.exists (fn k => k = public) keys2)) l1
            in
              l1' @ l2
            end
        in
          { structures = merge (#structures ns1) (#structures ns2)
          , signatures = merge (#signatures ns1) (#signatures ns2)
          , functors = merge (#functors ns1) (#functors ns2)
          }
        end

      (** Map from basis name -> namespace, populated as we process `bases`. *)
      val basis_ns_map: (string * namespace) list ref = ref []

      fun find_ns (name: string) : namespace =
        case List.find (fn (n, _) => n = name) (!basis_ns_map) of
          SOME (_, ns) => ns
        | NONE => raise Fail ("Debasification: unknown basis " ^ name)

      fun register_ns (name: string) (ns: namespace) =
        basis_ns_map := (name, ns) :: !basis_ns_map

      (** Unique name generators. *)
      fun uniq_str bn n = bn ^ "__S__" ^ n
      fun uniq_sig bn n = bn ^ "__Sig__" ^ n
      fun uniq_fun bn n = bn ^ "__F__" ^ n

      (** Convert a topdec to a strdec for use inside a local block.
        * SigDec and FunDec cannot appear inside local; we drop them here.
        * TopExp becomes a wildcard val binding. *)
      fun topdec_as_strdec (td: O.topdec) : O.Str.strdec =
        case td of
          O.StrDec sd => sd
        | O.SigDec _ => O.Str.DecEmpty
        | O.FunDec _ => O.Str.DecEmpty
        | O.TopExp {id, exp} =>
            O.Str.DecCore (O.Exp.DecVal
              { id = synth id "top-level expression"
              , tyvars = Seq.empty ()
              , elems = Seq.%
                  [{ is_rec = false
                   , pat = O.Pat.Wild (synth id "top-level expression wildcard")
                   , exp = exp
                   }]
              })

      (** Combine a list of strdecs into one, using DecMultiple if needed. *)
      fun multi_strdec (origin: NodeID.t) (sds: O.Str.strdec list) :
        O.Str.strdec =
        case sds of
          [] => O.Str.DecEmpty
        | [sd] => sd
        | _ =>
            O.Str.DecMultiple
              {id = synth origin "strdec sequence", elems = Seq.fromList sds}

      (** Generate aliasing strdecs that bring a namespace's exports into scope
        * under their public names (used when expanding a DecRef in inner context).
        *   structure Foo = mlb_0__S__Foo *)
      fun ns_to_alias_strdecs (origin: NodeID.t) (ns: namespace) :
        O.Str.strdec list =
        List.map
          (fn {public, unique} =>
             O.Str.DecStructure
               { id = synth origin ("import " ^ public)
               , elems = Seq.%
                   [{ name = public
                    , constraint = NONE
                    , strexp = O.Str.Ident
                        { id = synth origin ("import " ^ public ^ " strexp")
                        , name = Seq.% [unique]
                        }
                    }]
               }) (#structures ns)
      (* TODO: signatures, functors *)

      (** Generate strdecs that re-export a namespace's entries under new unique
        * names for the current basis (used in conv_filter for DecRef).
        *   structure bn__S__Foo = mlb_0__S__Foo *)
      fun ns_to_reexport_strdecs (origin: NodeID.t) (bn: string) (ns: namespace) :
        O.Str.strdec list * namespace =
        let
          val strdecs =
            List.map
              (fn {public, unique = src_unique} =>
                 O.Str.DecStructure
                   { id = synth origin ("reexport " ^ public)
                   , elems = Seq.%
                       [{ name = uniq_str bn public
                        , constraint = NONE
                        , strexp = O.Str.Ident
                            { id = synth origin
                                ("reexport " ^ public ^ " strexp")
                            , name = Seq.% [src_unique]
                            }
                        }]
                   }) (#structures ns)
          val new_ns =
            { structures =
                List.map
                  (fn {public, ...} =>
                     {public = public, unique = uniq_str bn public})
                  (#structures ns)
            , signatures = []
            , functors = []
            }
        in
          (strdecs, new_ns)
        end

      (** conv_inner: translate a basdec to strdecs for use INSIDE a local block.
        * The content is hidden — no namespace tracking needed.
        * DecRef is expanded by aliasing the referenced basis's public names. *)
      fun conv_inner (bn: string) (basdec: I.Mlb.basdec) : O.Str.strdec list =
        case basdec of
          I.Mlb.DecEmpty => []

        | I.Mlb.DecMultiple {elems, ...} =>
            List.concat (Seq.toList (Seq.map (conv_inner bn) elems))

        | I.Mlb.DecRef {id, name} => ns_to_alias_strdecs id (find_ns name)

        | I.Mlb.DecSml {sml = I.SmlAst {topdecs, ...}, ...} =>
            List.map topdec_as_strdec (Seq.toList topdecs)

        | I.Mlb.DecLocalInEnd {id, basdec1, basdec2} =>
            let
              val sd1 = conv_inner bn basdec1
              val sd2 = conv_inner bn basdec2
            in
              [O.Str.DecLocalInEnd
                 { id = id
                 , strdec1 = multi_strdec (synth id "inner local1") sd1
                 , strdec2 = multi_strdec (synth id "inner local2") sd2
                 }]
            end

        | I.Mlb.DecStructure {id, elems} =>
            Seq.toList
              (Seq.map
                 (fn {name, alias} =>
                    O.Str.DecStructure
                      { id = id
                      , elems = Seq.%
                          [{ name = name
                           , constraint = NONE
                           , strexp = O.Str.Ident
                               { id = synth id ("inner str alias " ^ name)
                               , name = Seq.% [Option.getOpt (alias, name)]
                               }
                           }]
                      }) elems)

        | I.Mlb.DecSignature _ => []
        | I.Mlb.DecFunctor _ => []

        | I.Mlb.DecAnn {basdec, ...} => conv_inner bn basdec

        | I.Mlb.DecUnderscorePrim _ => []

        | I.Mlb.DecOpen {id, elems} =>
            List.concat
              (List.map (fn name => ns_to_alias_strdecs id (find_ns name))
                 (Seq.toList elems))

        | I.Mlb.DecBasis _ =>
            raise Fail "Debasification: DecBasis not supported"

      (** conv_filter: translate a basdec to (topdecs, namespace).
        * Used for the exported portion of a basis or the `in` part of local.
        * Creates unique-named aliases for all exports so they survive globally. *)
      and conv_filter (bn: string) (basdec: I.Mlb.basdec) :
        O.topdec list * namespace =
        case basdec of
          I.Mlb.DecEmpty => ([], empty_ns)

        | I.Mlb.DecMultiple {elems, ...} =>
            Seq.iterate
              (fn ((acc_tds, acc_ns), bd) =>
                 let val (tds, ns) = conv_filter bn bd
                 in (acc_tds @ tds, merge_ns acc_ns ns)
                 end) ([], empty_ns) elems

        | I.Mlb.DecRef {id, name} =>
            let
              val ref_ns = find_ns name
              val (strdecs, new_ns) = ns_to_reexport_strdecs id bn ref_ns
            in
              (List.map O.StrDec strdecs, new_ns)
            end

        | I.Mlb.DecSml {id, sml = I.SmlAst {topdecs, ...}} =>
            let
              val tds = Seq.toList topdecs
              (* Find all top-level structure names declared in this SML file. *)
              val str_names = List.concat
                (List.map
                   (fn td =>
                      case td of
                        O.StrDec (O.Str.DecStructure {elems, ...}) =>
                          Seq.toList (Seq.map #name elems)
                      | _ => []) tds)
              val alias_strdecs =
                List.map
                  (fn name =>
                     O.Str.DecStructure
                       { id = synth id ("unique alias " ^ name)
                       , elems = Seq.%
                           [{ name = uniq_str bn name
                            , constraint = NONE
                            , strexp = O.Str.Ident
                                { id = synth id ("unique alias strexp " ^ name)
                                , name = Seq.% [name]
                                }
                            }]
                       }) str_names
              val ns =
                { structures =
                    List.map (fn n => {public = n, unique = uniq_str bn n})
                      str_names
                , signatures = []
                , functors = []
                }
            in
              (tds @ List.map O.StrDec alias_strdecs, ns)
            end

        | I.Mlb.DecLocalInEnd {id, basdec1, basdec2} =>
            let
              val sd1_list = conv_inner bn basdec1
              val (sd2_list, ns2) = conv_filter_as_strdecs bn basdec2
              val local_sd = O.Str.DecLocalInEnd
                { id = id
                , strdec1 = multi_strdec (synth id "filter local1") sd1_list
                , strdec2 = multi_strdec (synth id "filter local2") sd2_list
                }
            in
              ([O.StrDec local_sd], ns2)
            end

        | I.Mlb.DecStructure {id, elems} =>
            let
              val strdecs = Seq.toList
                (Seq.map
                   (fn {name, alias} =>
                      O.Str.DecStructure
                        { id = id
                        , elems = Seq.%
                            [{ name = uniq_str bn name
                             , constraint = NONE
                             , strexp = O.Str.Ident
                                 { id = synth id ("filter str alias " ^ name)
                                 , name = Seq.% [Option.getOpt (alias, name)]
                                 }
                             }]
                        }) elems)
              val ns =
                { structures = Seq.toList
                    (Seq.map
                       (fn {name, ...} =>
                          {public = name, unique = uniq_str bn name}) elems)
                , signatures = []
                , functors = []
                }
            in
              (List.map O.StrDec strdecs, ns)
            end

        | I.Mlb.DecSignature _ => ([], empty_ns)
        | I.Mlb.DecFunctor _ => ([], empty_ns)

        | I.Mlb.DecAnn {basdec, ...} => conv_filter bn basdec

        | I.Mlb.DecUnderscorePrim _ => ([], empty_ns)

        | I.Mlb.DecOpen {id, elems} =>
            List.foldl
              (fn (name, (acc_tds, acc_ns)) =>
                 let
                   val ref_ns = find_ns name
                   val (strdecs, new_ns) = ns_to_reexport_strdecs id bn ref_ns
                 in
                   (acc_tds @ List.map O.StrDec strdecs, merge_ns acc_ns new_ns)
                 end) ([], empty_ns) (Seq.toList elems)

        | I.Mlb.DecBasis _ =>
            raise Fail "Debasification: DecBasis not supported"

      (** Like conv_filter but returns strdecs instead of topdecs.
        * Used for basdec2 of DecLocalInEnd (which must be inside a strdec). *)
      and conv_filter_as_strdecs (bn: string) (basdec: I.Mlb.basdec) :
        O.Str.strdec list * namespace =
        let val (tds, ns) = conv_filter bn basdec
        in (List.map topdec_as_strdec tds, ns)
        end

      (** Translate the `main` basdec: expand DecRef by aliasing (not re-exporting),
        * since the unique names are already global and just need to be brought into
        * local scope under their public names. *)
      fun conv_main (basdec: I.Mlb.basdec) : O.topdec list =
        case basdec of
          I.Mlb.DecEmpty => []

        | I.Mlb.DecMultiple {elems, ...} =>
            List.concat (Seq.toList (Seq.map conv_main elems))

        | I.Mlb.DecRef {id, name} =>
            List.map O.StrDec (ns_to_alias_strdecs id (find_ns name))

        | I.Mlb.DecSml {sml = I.SmlAst {topdecs, ...}, ...} =>
            Seq.toList topdecs

        | I.Mlb.DecLocalInEnd {id, basdec1, basdec2} =>
            let
              val sd1 = conv_inner "main" basdec1
              val sd2 = List.map topdec_as_strdec (conv_main basdec2)
            in
              [O.StrDec (O.Str.DecLocalInEnd
                 { id = id
                 , strdec1 = multi_strdec (synth id "main local1") sd1
                 , strdec2 = multi_strdec (synth id "main local2") sd2
                 })]
            end

        | I.Mlb.DecStructure {id, elems} =>
            List.map O.StrDec (Seq.toList
              (Seq.map
                 (fn {name, alias} =>
                    O.Str.DecStructure
                      { id = id
                      , elems = Seq.%
                          [{ name = name
                           , constraint = NONE
                           , strexp = O.Str.Ident
                               { id = synth id ("main str alias " ^ name)
                               , name = Seq.% [Option.getOpt (alias, name)]
                               }
                           }]
                      }) elems))

        | I.Mlb.DecSignature _ => []
        | I.Mlb.DecFunctor _ => []
        | I.Mlb.DecAnn {basdec, ...} => conv_main basdec
        | I.Mlb.DecUnderscorePrim _ => []
        | I.Mlb.DecOpen {id, elems} =>
            List.concat
              (List.map
                 (fn name =>
                    List.map O.StrDec (ns_to_alias_strdecs id (find_ns name)))
                 (Seq.toList elems))
        | I.Mlb.DecBasis _ =>
            raise Fail "Debasification: DecBasis not supported"

      val result_topdecs =
        case input of
          I.Sml (I.SmlAst {id, topdecs}) =>
            O.Program {id = id, topdecs = topdecs}

        | I.Mlb (I.Program {bases, main}) =>
            let
              (* Process each basis in topo order, materialising it at the
               * top level and recording its namespace. *)
              val basis_topdecs: O.topdec list =
                Seq.iterate
                  (fn (acc, {name, id = _, basdec}) =>
                     let val (tds, ns) = conv_filter name basdec
                     in register_ns name ns; acc @ tds
                     end) [] bases

              val main_topdecs = conv_main main

              val all_topdecs = basis_topdecs @ main_topdecs
              val prog_id = synth (NodeID.fresh ()) "program root"
            in
              O.Program {id = prog_id, topdecs = Seq.fromList all_topdecs}
            end
    in
      (result_topdecs, lookup)
    end

end
