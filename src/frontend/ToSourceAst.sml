structure ToSourceAst =
struct

  datatype provenance = ParsedFrom of Source.t

  type provenance_table = NodeID.t -> provenance

  fun to_source_ast_mlb (top_src: Source.t) (top_ast: MLBAst.t)
      : SourceAst.t * provenance_table =
    let
      val pathmap = MLtonPathMap.getPathMap ()

      val prov_entries : (NodeID.t * provenance) list ref = ref []
      val bases_acc :
        {name: string, id: NodeID.t, basdec: SourceAst.Mlb.basdec} list ref =
        ref []
      val visited : (FilePath.t * string) list ref = ref []

      fun fresh_node (src: Source.t) : NodeID.t =
        let val id = NodeID.fresh ()
        in prov_entries := (id, ParsedFrom src) :: !prov_entries; id
        end

      fun resolve_path (mlb_src: Source.t) (rel: FilePath.t) : FilePath.t =
        let
          val mlb_dir = FilePath.dirname (Source.fileName mlb_src)
          val {result = expanded, ...} = MLtonPathMap.expandPath pathmap rel
        in
          if FilePath.isAbsolute expanded then expanded
          else FilePath.normalize (FilePath.join (mlb_dir, expanded))
        end

      fun find_visited (fp: FilePath.t) : string option =
        Option.map #2
          (List.find (fn (fp', _) => FilePath.sameFile (fp, fp')) (!visited))

      fun tok_str (tok: MLBToken.t) : string =
        Source.toString (MLBToken.getSource tok)

      fun convert_basexp (mlb_src: Source.t) (bexp: MLBAst.basexp)
          : SourceAst.Mlb.basexp =
        case bexp of
          MLBAst.Ident tok =>
            SourceAst.Mlb.Ident
              { id = fresh_node (MLBToken.getSource tok)
              , name = tok_str tok
              }
        | MLBAst.LetInEnd {lett, basdec, inn = _, basexp, endd = _} =>
            SourceAst.Mlb.LetInEnd
              { id = fresh_node (MLBToken.getSource lett)
              , basdec = convert_basdec mlb_src basdec
              , basexp = convert_basexp mlb_src basexp
              }
        | MLBAst.BasEnd {bas, basdec, endd = _} =>
            SourceAst.Mlb.BasEnd
              { id = fresh_node (MLBToken.getSource bas)
              , basdec = convert_basdec mlb_src basdec
              }

      and convert_basdec (mlb_src: Source.t) (dec: MLBAst.basdec)
          : SourceAst.Mlb.basdec =
        case dec of
          MLBAst.DecEmpty => SourceAst.Mlb.DecEmpty

        | MLBAst.DecMultiple {elems, delims = _} =>
            SourceAst.Mlb.DecMultiple
              { id = fresh_node mlb_src
              , elems = Seq.map (convert_basdec mlb_src) elems
              }

        | MLBAst.DecPathSML {path, token = _} =>
            let
              val sml_src = Source.loadFromFile (resolve_path mlb_src path)
            in
              SourceAst.Mlb.DecSml
                { id = fresh_node sml_src
                , sml = SourceAst.SmlAst
                    { id = fresh_node sml_src
                    , topdecs = Seq.empty ()  (* TODO: PARSE SML FILES *)
                    }
                }
            end

        | MLBAst.DecPathMLB {path, token = _} =>
            let
              val abs_path = resolve_path mlb_src path
            in
              case find_visited abs_path of
                SOME name =>
                  SourceAst.Mlb.DecRef {id = fresh_node mlb_src, name = name}
              | NONE =>
                  let
                    val name = UniqueName.fresh "mlb"
                    val _ = visited := (abs_path, name) :: !visited
                    val nested_src = Source.loadFromFile abs_path
                    val MLBAst.Ast nested_dec = MLBParser.parse nested_src
                    val nested_basdec = convert_basdec nested_src nested_dec
                    val basis_id = fresh_node nested_src
                  in
                    bases_acc :=
                      {name = name, id = basis_id, basdec = nested_basdec}
                      :: !bases_acc;
                    SourceAst.Mlb.DecRef {id = fresh_node mlb_src, name = name}
                  end
            end

        | MLBAst.DecBasis {basis, elems, delims = _} =>
            SourceAst.Mlb.DecBasis
              { id = fresh_node (MLBToken.getSource basis)
              , elems = Seq.map
                  (fn {basid, eq = _, basexp} =>
                    { name = tok_str basid
                    , basexp = convert_basexp mlb_src basexp
                    })
                  elems
              }

        | MLBAst.DecLocalInEnd {locall, basdec1, inn = _, basdec2, endd = _} =>
            SourceAst.Mlb.DecLocalInEnd
              { id = fresh_node (MLBToken.getSource locall)
              , basdec1 = convert_basdec mlb_src basdec1
              , basdec2 = convert_basdec mlb_src basdec2
              }

        | MLBAst.DecOpen {openn, elems} =>
            SourceAst.Mlb.DecOpen
              { id = fresh_node (MLBToken.getSource openn)
              , elems = Seq.map tok_str elems
              }

        | MLBAst.DecStructure {structuree, elems, delims = _} =>
            SourceAst.Mlb.DecStructure
              { id = fresh_node (MLBToken.getSource structuree)
              , elems = Seq.map
                  (fn {strid, eqstrid} =>
                    { name = tok_str strid
                    , alias =
                        Option.map (fn {eq = _, strid} => tok_str strid) eqstrid
                    })
                  elems
              }

        | MLBAst.DecSignature {signaturee, elems, delims = _} =>
            SourceAst.Mlb.DecSignature
              { id = fresh_node (MLBToken.getSource signaturee)
              , elems = Seq.map
                  (fn {sigid, eqsigid} =>
                    { name = tok_str sigid
                    , alias =
                        Option.map (fn {eq = _, sigid} => tok_str sigid) eqsigid
                    })
                  elems
              }

        | MLBAst.DecFunctor {functorr, elems, delims = _} =>
            SourceAst.Mlb.DecFunctor
              { id = fresh_node (MLBToken.getSource functorr)
              , elems = Seq.map
                  (fn {funid, eqfunid} =>
                    { name = tok_str funid
                    , alias =
                        Option.map (fn {eq = _, funid} => tok_str funid) eqfunid
                    })
                  elems
              }

        | MLBAst.DecAnn {ann, annotations, inn = _, basdec, endd = _} =>
            SourceAst.Mlb.DecAnn
              { id = fresh_node (MLBToken.getSource ann)
              , annotations = Seq.map tok_str annotations
              , basdec = convert_basdec mlb_src basdec
              }

        | MLBAst.DecUnderscorePrim tok =>
            SourceAst.Mlb.DecUnderscorePrim (fresh_node (MLBToken.getSource tok))

      val MLBAst.Ast top_basdec = top_ast
      val main = convert_basdec top_src top_basdec
      val program_id = fresh_node top_src
      val bases_seq = Seq.fromList (List.rev (!bases_acc))
      val prov_list = !prov_entries

      fun lookup (id: NodeID.t) : provenance =
        case List.find (fn (id', _) => NodeID.compare (id, id') = EQUAL)
               prov_list of
          SOME (_, p) => p
        | NONE =>
            raise Fail ("no provenance for node " ^ NodeID.toString id)
    in
      ( SourceAst.Mlb (SourceAst.Program
          { id = program_id
          , bases = bases_seq
          , main = main
          })
      , lookup
      )
    end

end
