structure RecordUnification:
sig
  val translate: SourceAst.t
                 -> AfterRecordUnification.t * (NodeID.t -> ProvenanceEvent.t)
end =
struct

  structure A = AfterRecordUnification

  fun numeric_label i =
    Int.toString (i + 1)

  fun translate (input: SourceAst.t) :
    AfterRecordUnification.t * (NodeID.t -> ProvenanceEvent.t) =
    let
      val prov_entries: (NodeID.t * ProvenanceEvent.t) list ref = ref []

      fun emit (id, p) =
        prov_entries := (id, p) :: !prov_entries

      fun synth (origin: NodeID.t) (why: string) : NodeID.t =
        let
          val id = NodeID.fresh ()
        in
          emit (id, ProvenanceEvent.Synthesized
            {id = id, pass = "record-unification", origin = origin, why = why});
          id
        end

      fun lookup (id: NodeID.t) : ProvenanceEvent.t =
        case
          List.find (fn (id', _) => NodeID.compare (id, id') = EQUAL)
            (!prov_entries)
        of
          SOME (_, p) => p
        | NONE => raise Fail ("no provenance for node " ^ NodeID.toString id)


      (* ===== Types ===== *)

      fun conv_ty ty =
        case ty of
          SourceAst.Ty.Var {id, name} => A.Ty.Var {id = id, name = name}

        | SourceAst.Ty.Record {id, elems} =>
            A.Ty.Record
              { id = id
              , elems =
                  Seq.map (fn {lab, ty} => {lab = lab, ty = conv_ty ty}) elems
              }

        | SourceAst.Ty.Tuple {id, elems} =>
            A.Ty.Record
              { id = id
              , elems =
                  Seq.mapIdx
                    (fn (i, ty) => {lab = numeric_label i, ty = conv_ty ty})
                    elems
              }

        | SourceAst.Ty.Con {id, args, name} =>
            A.Ty.Con {id = id, args = Seq.map conv_ty args, name = name}

        | SourceAst.Ty.Arrow {id, from, to} =>
            A.Ty.Arrow {id = id, from = conv_ty from, to = conv_ty to}


      (* ===== Patterns ===== *)

      fun conv_patrow patrow =
        case patrow of
          SourceAst.Pat.DotDotDot id => A.Pat.DotDotDot id

        | SourceAst.Pat.LabEqPat {id, lab, pat} =>
            A.Pat.LabEqPat {id = id, lab = lab, pat = conv_pat pat}

        | SourceAst.Pat.LabAsPat {id, name, ty, aspat} =>
            let
              val inner =
                case aspat of
                  SOME p =>
                    A.Pat.Layered
                      { id = synth id "as-pattern expansion"
                      , has_op = false
                      , name = name
                      , ty = Option.map conv_ty ty
                      , pat = conv_pat p
                      }
                | NONE =>
                    let
                      val ident = A.Pat.Ident
                        { id = synth id "punned pattern identifier"
                        , has_op = false
                        , name = Seq.% [name]
                        }
                    in
                      case ty of
                        NONE => ident
                      | SOME t =>
                          A.Pat.Typed
                            { id = synth id "type-annotated punned pattern"
                            , pat = ident
                            , ty = conv_ty t
                            }
                    end
            in
              A.Pat.LabEqPat {id = id, lab = name, pat = inner}
            end

      and conv_pat pat =
        case pat of
          SourceAst.Pat.Wild id => A.Pat.Wild id

        | SourceAst.Pat.Const {id, value} =>
            A.Pat.Const {id = id, value = value}

        | SourceAst.Pat.Unit id => A.Pat.Record {id = id, elems = Seq.empty ()}

        | SourceAst.Pat.Ident {id, has_op, name} =>
            A.Pat.Ident {id = id, has_op = has_op, name = name}

        | SourceAst.Pat.List {id, elems} =>
            A.Pat.List {id = id, elems = Seq.map conv_pat elems}

        | SourceAst.Pat.Tuple {id, elems} =>
            A.Pat.Record
              { id = id
              , elems =
                  Seq.mapIdx
                    (fn (i, p) =>
                       A.Pat.LabEqPat
                         { id = synth id "tuple pattern element"
                         , lab = numeric_label i
                         , pat = conv_pat p
                         }) elems
              }

        | SourceAst.Pat.Record {id, elems} =>
            A.Pat.Record {id = id, elems = Seq.map conv_patrow elems}

        | SourceAst.Pat.Con {id, has_op, name, atpat} =>
            A.Pat.Con
              {id = id, has_op = has_op, name = name, atpat = conv_pat atpat}

        | SourceAst.Pat.Infix {id, left, opr, right} =>
            A.Pat.Infix
              {id = id, left = conv_pat left, opr = opr, right = conv_pat right}

        | SourceAst.Pat.Typed {id, pat, ty} =>
            A.Pat.Typed {id = id, pat = conv_pat pat, ty = conv_ty ty}

        | SourceAst.Pat.Layered {id, has_op, name, ty, pat} =>
            A.Pat.Layered
              { id = id
              , has_op = has_op
              , name = name
              , ty = Option.map conv_ty ty
              , pat = conv_pat pat
              }

        | SourceAst.Pat.Or {id, elems} =>
            A.Pat.Or {id = id, elems = Seq.map conv_pat elems}


      (* ===== Expressions and declarations ===== *)

      fun conv_typbind {elems} =
        {elems =
           Seq.map
             (fn {tyvars, tycon, ty} =>
                {tyvars = tyvars, tycon = tycon, ty = conv_ty ty}) elems}

      fun conv_datbind {elems} =
        {elems =
           Seq.map
             (fn {tyvars, tycon, elems} =>
                { tyvars = tyvars
                , tycon = tycon
                , elems =
                    Seq.map
                      (fn {has_op, name, arg} =>
                         { has_op = has_op
                         , name = name
                         , arg = Option.map conv_ty arg
                         }) elems
                }) elems}

      fun conv_exbind exbind =
        case exbind of
          SourceAst.Exp.ExnNew {id, has_op, name, arg} =>
            A.Exp.ExnNew
              { id = id
              , has_op = has_op
              , name = name
              , arg = Option.map conv_ty arg
              }
        | SourceAst.Exp.ExnReplicate {id, has_op, left_name, right_name} =>
            A.Exp.ExnReplicate
              { id = id
              , has_op = has_op
              , left_name = left_name
              , right_name = right_name
              }

      fun conv_row_exp row =
        case row of
          SourceAst.Exp.RecordRow {id, lab, exp} =>
            A.Exp.RecordRow {id = id, lab = lab, exp = conv_exp exp}

        | SourceAst.Exp.RecordPun {id, name} =>
            A.Exp.RecordRow
              { id = id
              , lab = name
              , exp = A.Exp.Ident
                  { id = synth id "punned record expression"
                  , has_op = false
                  , name = Seq.% [name]
                  }
              }

      and conv_fname_args fname_args =
        case fname_args of
          SourceAst.Exp.PrefixedFun {id, has_op, name, args} =>
            A.Exp.PrefixedFun
              { id = id
              , has_op = has_op
              , name = name
              , args = Seq.map conv_pat args
              }

        | SourceAst.Exp.InfixedFun {id, larg, name, rarg} =>
            A.Exp.InfixedFun
              {id = id, larg = conv_pat larg, name = name, rarg = conv_pat rarg}

        | SourceAst.Exp.CurriedInfixedFun {id, larg, name, rarg, args} =>
            A.Exp.CurriedInfixedFun
              { id = id
              , larg = conv_pat larg
              , name = name
              , rarg = conv_pat rarg
              , args = Seq.map conv_pat args
              }

      and conv_fvalbind {elems} =
        {elems =
           Seq.map
             (fn {elems} =>
                {elems =
                   Seq.map
                     (fn {fname_args, ty, exp} =>
                        { fname_args = conv_fname_args fname_args
                        , ty = Option.map conv_ty ty
                        , exp = conv_exp exp
                        }) elems}) elems}

      and conv_exp exp =
        case exp of
          SourceAst.Exp.Const {id, value} =>
            A.Exp.Const {id = id, value = value}

        | SourceAst.Exp.Ident {id, has_op, name} =>
            A.Exp.Ident {id = id, has_op = has_op, name = name}

        | SourceAst.Exp.Record {id, elems} =>
            A.Exp.Record {id = id, elems = Seq.map conv_row_exp elems}

        | SourceAst.Exp.Select {id, label} =>
            A.Exp.Select {id = id, label = label}

        | SourceAst.Exp.Unit id => A.Exp.Record {id = id, elems = Seq.empty ()}

        | SourceAst.Exp.Tuple {id, elems} =>
            A.Exp.Record
              { id = id
              , elems =
                  Seq.mapIdx
                    (fn (i, e) =>
                       A.Exp.RecordRow
                         { id = synth id "tuple expression element"
                         , lab = numeric_label i
                         , exp = conv_exp e
                         }) elems
              }

        | SourceAst.Exp.List {id, elems} =>
            A.Exp.List {id = id, elems = Seq.map conv_exp elems}

        | SourceAst.Exp.Sequence {id, elems} =>
            A.Exp.Sequence {id = id, elems = Seq.map conv_exp elems}

        | SourceAst.Exp.LetInEnd {id, dec, exps} =>
            A.Exp.LetInEnd
              {id = id, dec = conv_dec dec, exps = Seq.map conv_exp exps}

        | SourceAst.Exp.App {id, left, right} =>
            A.Exp.App {id = id, left = conv_exp left, right = conv_exp right}

        | SourceAst.Exp.Infix {id, left, opr, right} =>
            A.Exp.Infix
              {id = id, left = conv_exp left, opr = opr, right = conv_exp right}

        | SourceAst.Exp.Typed {id, exp, ty} =>
            A.Exp.Typed {id = id, exp = conv_exp exp, ty = conv_ty ty}

        | SourceAst.Exp.Andalso {id, left, right} =>
            A.Exp.Andalso
              {id = id, left = conv_exp left, right = conv_exp right}

        | SourceAst.Exp.Orelse {id, left, right} =>
            A.Exp.Orelse {id = id, left = conv_exp left, right = conv_exp right}

        | SourceAst.Exp.Handle {id, exp, elems} =>
            A.Exp.Handle
              { id = id
              , exp = conv_exp exp
              , elems =
                  Seq.map
                    (fn {pat, exp} => {pat = conv_pat pat, exp = conv_exp exp})
                    elems
              }

        | SourceAst.Exp.Raise {id, exp} =>
            A.Exp.Raise {id = id, exp = conv_exp exp}

        | SourceAst.Exp.IfThenElse {id, exp1, exp2, exp3} =>
            A.Exp.IfThenElse
              { id = id
              , exp1 = conv_exp exp1
              , exp2 = conv_exp exp2
              , exp3 = conv_exp exp3
              }

        | SourceAst.Exp.While {id, exp1, exp2} =>
            A.Exp.While {id = id, exp1 = conv_exp exp1, exp2 = conv_exp exp2}

        | SourceAst.Exp.Case {id, exp, elems} =>
            A.Exp.Case
              { id = id
              , exp = conv_exp exp
              , elems =
                  Seq.map
                    (fn {pat, exp} => {pat = conv_pat pat, exp = conv_exp exp})
                    elems
              }

        | SourceAst.Exp.Fn {id, elems} =>
            A.Exp.Fn
              { id = id
              , elems =
                  Seq.map
                    (fn {pat, exp} => {pat = conv_pat pat, exp = conv_exp exp})
                    elems
              }

        | SourceAst.Exp.MLtonSpecific {id, directive, contents} =>
            A.Exp.MLtonSpecific
              {id = id, directive = directive, contents = contents}

      and conv_dec dec =
        case dec of
          SourceAst.Exp.DecEmpty => A.Exp.DecEmpty

        | SourceAst.Exp.DecVal {id, tyvars, elems} =>
            A.Exp.DecVal
              { id = id
              , tyvars = tyvars
              , elems =
                  Seq.map
                    (fn {is_rec, pat, exp} =>
                       {is_rec = is_rec, pat = conv_pat pat, exp = conv_exp exp})
                    elems
              }

        | SourceAst.Exp.DecFun {id, tyvars, fvalbind} =>
            A.Exp.DecFun
              {id = id, tyvars = tyvars, fvalbind = conv_fvalbind fvalbind}

        | SourceAst.Exp.DecType {id, typbind} =>
            A.Exp.DecType {id = id, typbind = conv_typbind typbind}

        | SourceAst.Exp.DecDatatype {id, datbind, withtypee} =>
            A.Exp.DecDatatype
              { id = id
              , datbind = conv_datbind datbind
              , withtypee = Option.map conv_typbind withtypee
              }

        | SourceAst.Exp.DecReplicateDatatype {id, left_name, right_name} =>
            A.Exp.DecReplicateDatatype
              {id = id, left_name = left_name, right_name = right_name}

        | SourceAst.Exp.DecAbstype {id, datbind, withtypee, dec} =>
            A.Exp.DecAbstype
              { id = id
              , datbind = conv_datbind datbind
              , withtypee = Option.map conv_typbind withtypee
              , dec = conv_dec dec
              }

        | SourceAst.Exp.DecException {id, elems} =>
            A.Exp.DecException {id = id, elems = Seq.map conv_exbind elems}

        | SourceAst.Exp.DecLocal {id, left_dec, right_dec} =>
            A.Exp.DecLocal
              { id = id
              , left_dec = conv_dec left_dec
              , right_dec = conv_dec right_dec
              }

        | SourceAst.Exp.DecOpen {id, elems} =>
            A.Exp.DecOpen {id = id, elems = elems}

        | SourceAst.Exp.DecMultiple {id, elems} =>
            A.Exp.DecMultiple {id = id, elems = Seq.map conv_dec elems}

        | SourceAst.Exp.DecInfix {id, precedence, elems} =>
            A.Exp.DecInfix {id = id, precedence = precedence, elems = elems}

        | SourceAst.Exp.DecInfixr {id, precedence, elems} =>
            A.Exp.DecInfixr {id = id, precedence = precedence, elems = elems}

        | SourceAst.Exp.DecNonfix {id, elems} =>
            A.Exp.DecNonfix {id = id, elems = elems}


      (* ===== Signatures ===== *)

      fun conv_sigexp sigexp =
        case sigexp of
          SourceAst.Sig.Ident {id, name} => A.Sig.Ident {id = id, name = name}

        | SourceAst.Sig.Spec {id, spec} =>
            A.Sig.Spec {id = id, spec = conv_spec spec}

        | SourceAst.Sig.WhereType {id, sigexp, elems} =>
            A.Sig.WhereType
              { id = id
              , sigexp = conv_sigexp sigexp
              , elems =
                  Seq.map
                    (fn {tyvars, tycon, ty} =>
                       {tyvars = tyvars, tycon = tycon, ty = conv_ty ty}) elems
              }

      and conv_spec spec =
        case spec of
          SourceAst.Sig.EmptySpec => A.Sig.EmptySpec

        | SourceAst.Sig.Val {id, elems} =>
            A.Sig.Val
              { id = id
              , elems =
                  Seq.map (fn {name, ty} => {name = name, ty = conv_ty ty})
                    elems
              }

        | SourceAst.Sig.Type {id, elems} => A.Sig.Type {id = id, elems = elems}

        | SourceAst.Sig.TypeAbbreviation {id, typbind} =>
            A.Sig.TypeAbbreviation {id = id, typbind = conv_typbind typbind}

        | SourceAst.Sig.Eqtype {id, elems} =>
            A.Sig.Eqtype {id = id, elems = elems}

        | SourceAst.Sig.Datatype {id, elems} =>
            A.Sig.Datatype
              { id = id
              , elems =
                  Seq.map
                    (fn {tyvars, tycon, elems} =>
                       { tyvars = tyvars
                       , tycon = tycon
                       , elems =
                           Seq.map
                             (fn {name, arg} =>
                                {name = name, arg = Option.map conv_ty arg})
                             elems
                       }) elems
              }

        | SourceAst.Sig.ReplicateDatatype {id, left_id, right_id} =>
            A.Sig.ReplicateDatatype
              {id = id, left_id = left_id, right_id = right_id}

        | SourceAst.Sig.Exception {id, elems} =>
            A.Sig.Exception
              { id = id
              , elems =
                  Seq.map
                    (fn {name, arg} =>
                       {name = name, arg = Option.map conv_ty arg}) elems
              }

        | SourceAst.Sig.Structure {id, elems} =>
            A.Sig.Structure
              { id = id
              , elems =
                  Seq.map
                    (fn {name, sigexp} =>
                       {name = name, sigexp = conv_sigexp sigexp}) elems
              }

        | SourceAst.Sig.Include {id, sigexp} =>
            A.Sig.Include {id = id, sigexp = conv_sigexp sigexp}

        | SourceAst.Sig.IncludeIds {id, names} =>
            A.Sig.IncludeIds {id = id, names = names}

        | SourceAst.Sig.SharingType {id, spec, elems} =>
            A.Sig.SharingType {id = id, spec = conv_spec spec, elems = elems}

        | SourceAst.Sig.Sharing {id, spec, elems} =>
            A.Sig.Sharing {id = id, spec = conv_spec spec, elems = elems}

        | SourceAst.Sig.Multiple {id, elems} =>
            A.Sig.Multiple {id = id, elems = Seq.map conv_spec elems}

      fun conv_sigdec (SourceAst.Sig.Signature {id, elems}) =
        A.Sig.Signature
          { id = id
          , elems =
              Seq.map
                (fn {name, sigexp} => {name = name, sigexp = conv_sigexp sigexp})
                elems
          }


      (* ===== Structures ===== *)

      fun conv_strexp strexp =
        case strexp of
          SourceAst.Str.Ident {id, name} => A.Str.Ident {id = id, name = name}

        | SourceAst.Str.Struct {id, strdec} =>
            A.Str.Struct {id = id, strdec = conv_strdec strdec}

        | SourceAst.Str.Constraint {id, strexp, is_opaque, sigexp} =>
            A.Str.Constraint
              { id = id
              , strexp = conv_strexp strexp
              , is_opaque = is_opaque
              , sigexp = conv_sigexp sigexp
              }

        | SourceAst.Str.FunAppExp {id, funid, strexp} =>
            A.Str.FunAppExp
              {id = id, funid = funid, strexp = conv_strexp strexp}

        | SourceAst.Str.FunAppDec {id, funid, strdec} =>
            A.Str.FunAppDec
              {id = id, funid = funid, strdec = conv_strdec strdec}

        | SourceAst.Str.LetInEnd {id, strdec, strexp} =>
            A.Str.LetInEnd
              { id = id
              , strdec = conv_strdec strdec
              , strexp = conv_strexp strexp
              }

      and conv_strdec strdec =
        case strdec of
          SourceAst.Str.DecEmpty => A.Str.DecEmpty

        | SourceAst.Str.DecCore dec => A.Str.DecCore (conv_dec dec)

        | SourceAst.Str.DecStructure {id, elems} =>
            A.Str.DecStructure
              { id = id
              , elems =
                  Seq.map
                    (fn {name, constraint, strexp} =>
                       { name = name
                       , constraint =
                           Option.map
                             (fn {is_opaque, sigexp} =>
                                { is_opaque = is_opaque
                                , sigexp = conv_sigexp sigexp
                                }) constraint
                       , strexp = conv_strexp strexp
                       }) elems
              }

        | SourceAst.Str.DecMultiple {id, elems} =>
            A.Str.DecMultiple {id = id, elems = Seq.map conv_strdec elems}

        | SourceAst.Str.DecLocalInEnd {id, strdec1, strdec2} =>
            A.Str.DecLocalInEnd
              { id = id
              , strdec1 = conv_strdec strdec1
              , strdec2 = conv_strdec strdec2
              }

        | SourceAst.Str.MLtonOverload {id, prec, name, ty, elems} =>
            A.Str.MLtonOverload
              { id = id
              , prec = prec
              , name = name
              , ty = conv_ty ty
              , elems = elems
              }


      (* ===== Functors ===== *)

      fun conv_funarg funarg =
        case funarg of
          SourceAst.Fun.ArgIdent {id, name, sigexp} =>
            A.Fun.ArgIdent {id = id, name = name, sigexp = conv_sigexp sigexp}
        | SourceAst.Fun.ArgSpec {id, spec} =>
            A.Fun.ArgSpec {id = id, spec = conv_spec spec}

      fun conv_fundec (SourceAst.Fun.DecFunctor {id, elems}) =
        A.Fun.DecFunctor
          { id = id
          , elems =
              Seq.map
                (fn {name, funarg, constraint, strexp} =>
                   { name = name
                   , funarg = conv_funarg funarg
                   , constraint =
                       Option.map
                         (fn {is_opaque, sigexp} =>
                            {is_opaque = is_opaque, sigexp = conv_sigexp sigexp})
                         constraint
                   , strexp = conv_strexp strexp
                   }) elems
          }


      (* ===== Top-level ===== *)

      fun conv_topdec topdec =
        case topdec of
          SourceAst.SigDec sd => A.SigDec (conv_sigdec sd)
        | SourceAst.StrDec sd => A.StrDec (conv_strdec sd)
        | SourceAst.FunDec fd => A.FunDec (conv_fundec fd)
        | SourceAst.TopExp {id, exp} => A.TopExp {id = id, exp = conv_exp exp}

      fun conv_sml_ast (SourceAst.SmlAst {id, topdecs}) =
        A.SmlAst {id = id, topdecs = Seq.map conv_topdec topdecs}


      (* ===== MLB ===== *)

      fun conv_basexp basexp =
        case basexp of
          SourceAst.Mlb.Ident {id, name} => A.Mlb.Ident {id = id, name = name}

        | SourceAst.Mlb.LetInEnd {id, basdec, basexp} =>
            A.Mlb.LetInEnd
              { id = id
              , basdec = conv_basdec basdec
              , basexp = conv_basexp basexp
              }

        | SourceAst.Mlb.BasEnd {id, basdec} =>
            A.Mlb.BasEnd {id = id, basdec = conv_basdec basdec}

      and conv_basdec basdec =
        case basdec of
          SourceAst.Mlb.DecEmpty => A.Mlb.DecEmpty

        | SourceAst.Mlb.DecMultiple {id, elems} =>
            A.Mlb.DecMultiple {id = id, elems = Seq.map conv_basdec elems}

        | SourceAst.Mlb.DecRef {id, name} => A.Mlb.DecRef {id = id, name = name}

        | SourceAst.Mlb.DecSml {id, sml} =>
            A.Mlb.DecSml {id = id, sml = conv_sml_ast sml}

        | SourceAst.Mlb.DecBasis {id, elems} =>
            A.Mlb.DecBasis
              { id = id
              , elems =
                  Seq.map
                    (fn {name, basexp} =>
                       {name = name, basexp = conv_basexp basexp}) elems
              }

        | SourceAst.Mlb.DecLocalInEnd {id, basdec1, basdec2} =>
            A.Mlb.DecLocalInEnd
              { id = id
              , basdec1 = conv_basdec basdec1
              , basdec2 = conv_basdec basdec2
              }

        | SourceAst.Mlb.DecOpen {id, elems} =>
            A.Mlb.DecOpen {id = id, elems = elems}

        | SourceAst.Mlb.DecStructure {id, elems} =>
            A.Mlb.DecStructure {id = id, elems = elems}

        | SourceAst.Mlb.DecSignature {id, elems} =>
            A.Mlb.DecSignature {id = id, elems = elems}

        | SourceAst.Mlb.DecFunctor {id, elems} =>
            A.Mlb.DecFunctor {id = id, elems = elems}

        | SourceAst.Mlb.DecAnn {id, annotations, basdec} =>
            A.Mlb.DecAnn
              {id = id, annotations = annotations, basdec = conv_basdec basdec}

        | SourceAst.Mlb.DecUnderscorePrim id => A.Mlb.DecUnderscorePrim id


      (* ===== Entry point ===== *)

      val result =
        case input of
          SourceAst.Sml sml => A.Sml (conv_sml_ast sml)
        | SourceAst.Mlb (SourceAst.Program {bases, main}) =>
            A.Mlb (A.Program
              { bases =
                  Seq.map
                    (fn {name, id, basdec} =>
                       {name = name, id = id, basdec = conv_basdec basdec})
                    bases
              , main = conv_basdec main
              })
    in
      (result, lookup)
    end

end
