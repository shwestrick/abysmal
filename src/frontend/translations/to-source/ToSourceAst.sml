structure ToSourceAst =
struct

  fun to_source_ast_mlb (top_src: Source.t) (top_ast: MLBAst.t) :
    SourceAst.t * (NodeID.t -> ProvenanceEvent.t) =
    let
      val pathmap = MLtonPathMap.getPathMap ()

      val prov_entries: (NodeID.t * ProvenanceEvent.t) list ref = ref []
      val
        bases_acc:
          {name: string, id: NodeID.t, basdec: SourceAst.Mlb.basdec} list ref =
        ref []
      val visited: (FilePath.t * (string * InfixDict.t)) list ref = ref []

      fun fresh_node (src: Source.t) : NodeID.t =
        let
          val id = NodeID.fresh ()
        in
          prov_entries
          :=
          (id, ProvenanceEvent.Parsed {id = id, source = src}) :: !prov_entries;
          id
        end

      fun resolve_path (mlb_src: Source.t) (rel: FilePath.t) : FilePath.t =
        let
          val mlb_dir = FilePath.dirname (Source.fileName mlb_src)
          val {result = expanded, ...} = MLtonPathMap.expandPath pathmap rel
        in
          if FilePath.isAbsolute expanded then expanded
          else FilePath.normalize (FilePath.join (mlb_dir, expanded))
        end

      fun find_visited (fp: FilePath.t) : (string * InfixDict.t) option =
        Option.map #2
          (List.find (fn (fp', _) => FilePath.sameFile (fp, fp')) (!visited))

      fun tok_str (tok: MLBToken.t) : string =
        Source.toString (MLBToken.getSource tok)

      fun convert_basexp (mlb_src: Source.t) (infdict: InfixDict.t)
        (bexp: MLBAst.basexp) : InfixDict.t * SourceAst.Mlb.basexp =
        case bexp of
          MLBAst.Ident tok =>
            ( infdict
            , SourceAst.Mlb.Ident
                {id = fresh_node (MLBToken.getSource tok), name = tok_str tok}
            )
        | MLBAst.LetInEnd {lett, basdec, inn = _, basexp, endd = _} =>
            let
              val infdict = InfixDict.newScope infdict
              val (infdict, basdec') = convert_basdec mlb_src infdict basdec
              val infdict = InfixDict.newScope infdict
              val (infdict, basexp') = convert_basexp mlb_src infdict basexp
              val {old = infdict, popped = exported} =
                InfixDict.popScope infdict
              val {old = infdict, ...} = InfixDict.popScope infdict
              val infdict = InfixDict.merge (infdict, exported)
            in
              ( infdict
              , SourceAst.Mlb.LetInEnd
                  { id = fresh_node (MLBToken.getSource lett)
                  , basdec = basdec'
                  , basexp = basexp'
                  }
              )
            end
        | MLBAst.BasEnd {bas, basdec, endd = _} =>
            let
              val (infdict', basdec') = convert_basdec mlb_src infdict basdec
            in
              ( infdict'
              , SourceAst.Mlb.BasEnd
                  {id = fresh_node (MLBToken.getSource bas), basdec = basdec'}
              )
            end

      and convert_basdec (mlb_src: Source.t) (infdict: InfixDict.t)
        (dec: MLBAst.basdec) : InfixDict.t * SourceAst.Mlb.basdec =
        case dec of
          MLBAst.DecEmpty => (infdict, SourceAst.Mlb.DecEmpty)

        | MLBAst.DecMultiple {elems, delims = _} =>
            let
              val (infdict', rev_elems) =
                Seq.iterate
                  (fn ((d, acc), elem) =>
                     let val (d', e) = convert_basdec mlb_src d elem
                     in (d', e :: acc)
                     end) (infdict, []) elems
            in
              ( infdict'
              , SourceAst.Mlb.DecMultiple
                  {id = fresh_node mlb_src, elems = Seq.fromRevList rev_elems}
              )
            end

        | MLBAst.DecPathSML {path, token = _} =>
            let
              val sml_src = Source.loadFromFile (resolve_path mlb_src path)
              val (infdict', ast) =
                Parser.parse_sml_with_infdict infdict sml_src
              val sml = ToSourceAstSML.convert fresh_node sml_src ast
            in
              ( infdict'
              , SourceAst.Mlb.DecSml {id = fresh_node sml_src, sml = sml}
              )
            end

        | MLBAst.DecPathMLB {path, token = _} =>
            let
              val abs_path = resolve_path mlb_src path
            in
              case find_visited abs_path of
                SOME (name, nested_infdict) =>
                  ( InfixDict.merge (infdict, nested_infdict)
                  , SourceAst.Mlb.DecRef {id = fresh_node mlb_src, name = name}
                  )
              | NONE =>
                  let
                    val name = UniqueName.fresh "mlb"
                    val nested_src = Source.loadFromFile abs_path
                    val MLBAst.Ast nested_dec = MLBParser.parse nested_src
                    (* Per spec: sub-MLB files are elaborated independently,
                     * not inheriting the current basis. *)
                    val (nested_infdict, nested_basdec) =
                      convert_basdec nested_src InfixDict.empty nested_dec
                    val basis_id = fresh_node nested_src
                  in
                    visited := (abs_path, (name, nested_infdict)) :: !visited;
                    bases_acc
                    :=
                    {name = name, id = basis_id, basdec = nested_basdec}
                    :: !bases_acc;
                    ( InfixDict.merge (infdict, nested_infdict)
                    , SourceAst.Mlb.DecRef
                        {id = fresh_node mlb_src, name = name}
                    )
                  end
            end

        | MLBAst.DecBasis {basis, elems, delims = _} =>
            let
              val (infdict', rev_elems) =
                Seq.iterate
                  (fn ((d, acc), {basid, eq = _, basexp}) =>
                     let val (d', basexp') = convert_basexp mlb_src d basexp
                     in (d', {name = tok_str basid, basexp = basexp'} :: acc)
                     end) (infdict, []) elems
            in
              ( infdict'
              , SourceAst.Mlb.DecBasis
                  { id = fresh_node (MLBToken.getSource basis)
                  , elems = Seq.fromRevList rev_elems
                  }
              )
            end

        | MLBAst.DecLocalInEnd {locall, basdec1, inn = _, basdec2, endd = _} =>
            let
              val infdict = InfixDict.newScope infdict
              val (infdict, basdec1') = convert_basdec mlb_src infdict basdec1
              val infdict = InfixDict.newScope infdict
              val (infdict, basdec2') = convert_basdec mlb_src infdict basdec2
              val {old = infdict, popped = exported} =
                InfixDict.popScope infdict
              val {old = infdict, ...} = InfixDict.popScope infdict
              val infdict = InfixDict.merge (infdict, exported)
            in
              ( infdict
              , SourceAst.Mlb.DecLocalInEnd
                  { id = fresh_node (MLBToken.getSource locall)
                  , basdec1 = basdec1'
                  , basdec2 = basdec2'
                  }
              )
            end

        | MLBAst.DecOpen {openn, elems} =>
            ( infdict
            , SourceAst.Mlb.DecOpen
                { id = fresh_node (MLBToken.getSource openn)
                , elems = Seq.map tok_str elems
                }
            )

        | MLBAst.DecStructure {structuree, elems, delims = _} =>
            ( infdict
            , SourceAst.Mlb.DecStructure
                { id = fresh_node (MLBToken.getSource structuree)
                , elems =
                    Seq.map
                      (fn {strid, eqstrid} =>
                         { name = tok_str strid
                         , alias =
                             Option.map (fn {eq = _, strid} => tok_str strid)
                               eqstrid
                         }) elems
                }
            )

        | MLBAst.DecSignature {signaturee, elems, delims = _} =>
            ( infdict
            , SourceAst.Mlb.DecSignature
                { id = fresh_node (MLBToken.getSource signaturee)
                , elems =
                    Seq.map
                      (fn {sigid, eqsigid} =>
                         { name = tok_str sigid
                         , alias =
                             Option.map (fn {eq = _, sigid} => tok_str sigid)
                               eqsigid
                         }) elems
                }
            )

        | MLBAst.DecFunctor {functorr, elems, delims = _} =>
            ( infdict
            , SourceAst.Mlb.DecFunctor
                { id = fresh_node (MLBToken.getSource functorr)
                , elems =
                    Seq.map
                      (fn {funid, eqfunid} =>
                         { name = tok_str funid
                         , alias =
                             Option.map (fn {eq = _, funid} => tok_str funid)
                               eqfunid
                         }) elems
                }
            )

        | MLBAst.DecAnn {ann, annotations, inn = _, basdec, endd = _} =>
            let
              val (infdict', basdec') = convert_basdec mlb_src infdict basdec
            in
              ( infdict'
              , SourceAst.Mlb.DecAnn
                  { id = fresh_node (MLBToken.getSource ann)
                  , annotations = Seq.map tok_str annotations
                  , basdec = basdec'
                  }
              )
            end

        | MLBAst.DecUnderscorePrim tok =>
            ( infdict
            , SourceAst.Mlb.DecUnderscorePrim
                (fresh_node (MLBToken.getSource tok))
            )

      val MLBAst.Ast top_basdec = top_ast
      val (_, main) = convert_basdec top_src InfixDict.empty top_basdec
      val bases_seq = Seq.fromList (List.rev (!bases_acc))
      val prov_list = !prov_entries

      fun lookup (id: NodeID.t) : ProvenanceEvent.t =
        case
          List.find (fn (id', _) => NodeID.compare (id, id') = EQUAL) prov_list
        of
          SOME (_, p) => p
        | NONE => raise Fail ("no provenance for node " ^ NodeID.toString id)
    in
      ( SourceAst.Mlb (SourceAst.Program {bases = bases_seq, main = main})
      , lookup
      )
    end

end
