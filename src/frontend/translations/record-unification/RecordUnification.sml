structure RecordUnification:
sig
  val translate: AfterDebasification.t
                 -> AfterRecordUnification.t * (NodeID.t -> ProvenanceEvent.t)
end =
struct

  structure D = AfterDebasification
  structure R = AfterRecordUnification

  fun numeric_label i =
    Int.toString (i + 1)

  fun translate (input: D.t) :
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
          D.Ty.Var {id, name} => R.Ty.Var {id = id, name = name}

        | D.Ty.Record {id, elems} =>
            R.Ty.Record
              { id = id
              , elems =
                  Seq.map (fn {lab, ty} => {lab = lab, ty = conv_ty ty}) elems
              }

        | D.Ty.Tuple {id, elems} =>
            R.Ty.Record
              { id = id
              , elems =
                  Seq.mapIdx
                    (fn (i, ty) => {lab = numeric_label i, ty = conv_ty ty})
                    elems
              }

        | D.Ty.Con {id, args, name} =>
            R.Ty.Con {id = id, args = Seq.map conv_ty args, name = name}

        | D.Ty.Arrow {id, from, to} =>
            R.Ty.Arrow {id = id, from = conv_ty from, to = conv_ty to}


      (* ===== Patterns ===== *)

      fun conv_patrow patrow =
        case patrow of
          D.Pat.DotDotDot id => R.Pat.DotDotDot id

        | D.Pat.LabEqPat {id, lab, pat} =>
            R.Pat.LabEqPat {id = id, lab = lab, pat = conv_pat pat}

        | D.Pat.LabAsPat {id, name, ty, aspat} =>
            let
              val inner =
                case aspat of
                  SOME p =>
                    R.Pat.Layered
                      { id = synth id "as-pattern expansion"
                      , has_op = false
                      , name = name
                      , ty = Option.map conv_ty ty
                      , pat = conv_pat p
                      }
                | NONE =>
                    let
                      val ident = R.Pat.Ident
                        { id = synth id "punned pattern identifier"
                        , has_op = false
                        , name = Seq.% [name]
                        }
                    in
                      case ty of
                        NONE => ident
                      | SOME t =>
                          R.Pat.Typed
                            { id = synth id "type-annotated punned pattern"
                            , pat = ident
                            , ty = conv_ty t
                            }
                    end
            in
              R.Pat.LabEqPat {id = id, lab = name, pat = inner}
            end

      and conv_pat pat =
        case pat of
          D.Pat.Wild id => R.Pat.Wild id

        | D.Pat.Const {id, value} => R.Pat.Const {id = id, value = value}

        | D.Pat.Unit id => R.Pat.Record {id = id, elems = Seq.empty ()}

        | D.Pat.Ident {id, has_op, name} =>
            R.Pat.Ident {id = id, has_op = has_op, name = name}

        | D.Pat.List {id, elems} =>
            R.Pat.List {id = id, elems = Seq.map conv_pat elems}

        | D.Pat.Tuple {id, elems} =>
            R.Pat.Record
              { id = id
              , elems =
                  Seq.mapIdx
                    (fn (i, p) =>
                       R.Pat.LabEqPat
                         { id = synth id "tuple pattern element"
                         , lab = numeric_label i
                         , pat = conv_pat p
                         }) elems
              }

        | D.Pat.Record {id, elems} =>
            R.Pat.Record {id = id, elems = Seq.map conv_patrow elems}

        | D.Pat.Con {id, has_op, name, atpat} =>
            R.Pat.Con
              {id = id, has_op = has_op, name = name, atpat = conv_pat atpat}

        | D.Pat.Infix {id, left, opr, right} =>
            R.Pat.Infix
              {id = id, left = conv_pat left, opr = opr, right = conv_pat right}

        | D.Pat.Typed {id, pat, ty} =>
            R.Pat.Typed {id = id, pat = conv_pat pat, ty = conv_ty ty}

        | D.Pat.Layered {id, has_op, name, ty, pat} =>
            R.Pat.Layered
              { id = id
              , has_op = has_op
              , name = name
              , ty = Option.map conv_ty ty
              , pat = conv_pat pat
              }

        | D.Pat.Or {id, elems} =>
            R.Pat.Or {id = id, elems = Seq.map conv_pat elems}


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
          D.Exp.ExnNew {id, has_op, name, arg} =>
            R.Exp.ExnNew
              { id = id
              , has_op = has_op
              , name = name
              , arg = Option.map conv_ty arg
              }
        | D.Exp.ExnReplicate {id, has_op, left_name, right_name} =>
            R.Exp.ExnReplicate
              { id = id
              , has_op = has_op
              , left_name = left_name
              , right_name = right_name
              }

      fun conv_row_exp row =
        case row of
          D.Exp.RecordRow {id, lab, exp} =>
            R.Exp.RecordRow {id = id, lab = lab, exp = conv_exp exp}

        | D.Exp.RecordPun {id, name} =>
            R.Exp.RecordRow
              { id = id
              , lab = name
              , exp = R.Exp.Ident
                  { id = synth id "punned record expression"
                  , has_op = false
                  , name = Seq.% [name]
                  }
              }

      and conv_fname_args fname_args =
        case fname_args of
          D.Exp.PrefixedFun {id, has_op, name, args} =>
            R.Exp.PrefixedFun
              { id = id
              , has_op = has_op
              , name = name
              , args = Seq.map conv_pat args
              }

        | D.Exp.InfixedFun {id, larg, name, rarg} =>
            R.Exp.InfixedFun
              {id = id, larg = conv_pat larg, name = name, rarg = conv_pat rarg}

        | D.Exp.CurriedInfixedFun {id, larg, name, rarg, args} =>
            R.Exp.CurriedInfixedFun
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
          D.Exp.Const {id, value} => R.Exp.Const {id = id, value = value}

        | D.Exp.Ident {id, has_op, name} =>
            R.Exp.Ident {id = id, has_op = has_op, name = name}

        | D.Exp.Record {id, elems} =>
            R.Exp.Record {id = id, elems = Seq.map conv_row_exp elems}

        | D.Exp.Select {id, label} => R.Exp.Select {id = id, label = label}

        | D.Exp.Unit id => R.Exp.Record {id = id, elems = Seq.empty ()}

        | D.Exp.Tuple {id, elems} =>
            R.Exp.Record
              { id = id
              , elems =
                  Seq.mapIdx
                    (fn (i, e) =>
                       R.Exp.RecordRow
                         { id = synth id "tuple expression element"
                         , lab = numeric_label i
                         , exp = conv_exp e
                         }) elems
              }

        | D.Exp.List {id, elems} =>
            R.Exp.List {id = id, elems = Seq.map conv_exp elems}

        | D.Exp.Sequence {id, elems} =>
            R.Exp.Sequence {id = id, elems = Seq.map conv_exp elems}

        | D.Exp.LetInEnd {id, dec, exps} =>
            R.Exp.LetInEnd
              {id = id, dec = conv_dec dec, exps = Seq.map conv_exp exps}

        | D.Exp.App {id, left, right} =>
            R.Exp.App {id = id, left = conv_exp left, right = conv_exp right}

        | D.Exp.Infix {id, left, opr, right} =>
            R.Exp.Infix
              {id = id, left = conv_exp left, opr = opr, right = conv_exp right}

        | D.Exp.Typed {id, exp, ty} =>
            R.Exp.Typed {id = id, exp = conv_exp exp, ty = conv_ty ty}

        | D.Exp.Andalso {id, left, right} =>
            R.Exp.Andalso
              {id = id, left = conv_exp left, right = conv_exp right}

        | D.Exp.Orelse {id, left, right} =>
            R.Exp.Orelse {id = id, left = conv_exp left, right = conv_exp right}

        | D.Exp.Handle {id, exp, elems} =>
            R.Exp.Handle
              { id = id
              , exp = conv_exp exp
              , elems =
                  Seq.map
                    (fn {pat, exp} => {pat = conv_pat pat, exp = conv_exp exp})
                    elems
              }

        | D.Exp.Raise {id, exp} => R.Exp.Raise {id = id, exp = conv_exp exp}

        | D.Exp.IfThenElse {id, exp1, exp2, exp3} =>
            R.Exp.IfThenElse
              { id = id
              , exp1 = conv_exp exp1
              , exp2 = conv_exp exp2
              , exp3 = conv_exp exp3
              }

        | D.Exp.While {id, exp1, exp2} =>
            R.Exp.While {id = id, exp1 = conv_exp exp1, exp2 = conv_exp exp2}

        | D.Exp.Case {id, exp, elems} =>
            R.Exp.Case
              { id = id
              , exp = conv_exp exp
              , elems =
                  Seq.map
                    (fn {pat, exp} => {pat = conv_pat pat, exp = conv_exp exp})
                    elems
              }

        | D.Exp.Fn {id, elems} =>
            R.Exp.Fn
              { id = id
              , elems =
                  Seq.map
                    (fn {pat, exp} => {pat = conv_pat pat, exp = conv_exp exp})
                    elems
              }

        | D.Exp.MLtonSpecific {id, directive, contents} =>
            R.Exp.MLtonSpecific
              {id = id, directive = directive, contents = contents}

      and conv_dec dec =
        case dec of
          D.Exp.DecEmpty => R.Exp.DecEmpty

        | D.Exp.DecVal {id, tyvars, elems} =>
            R.Exp.DecVal
              { id = id
              , tyvars = tyvars
              , elems =
                  Seq.map
                    (fn {is_rec, pat, exp} =>
                       {is_rec = is_rec, pat = conv_pat pat, exp = conv_exp exp})
                    elems
              }

        | D.Exp.DecFun {id, tyvars, fvalbind} =>
            R.Exp.DecFun
              {id = id, tyvars = tyvars, fvalbind = conv_fvalbind fvalbind}

        | D.Exp.DecType {id, typbind} =>
            R.Exp.DecType {id = id, typbind = conv_typbind typbind}

        | D.Exp.DecDatatype {id, datbind, withtypee} =>
            R.Exp.DecDatatype
              { id = id
              , datbind = conv_datbind datbind
              , withtypee = Option.map conv_typbind withtypee
              }

        | D.Exp.DecReplicateDatatype {id, left_name, right_name} =>
            R.Exp.DecReplicateDatatype
              {id = id, left_name = left_name, right_name = right_name}

        | D.Exp.DecAbstype {id, datbind, withtypee, dec} =>
            R.Exp.DecAbstype
              { id = id
              , datbind = conv_datbind datbind
              , withtypee = Option.map conv_typbind withtypee
              , dec = conv_dec dec
              }

        | D.Exp.DecException {id, elems} =>
            R.Exp.DecException {id = id, elems = Seq.map conv_exbind elems}

        | D.Exp.DecLocal {id, left_dec, right_dec} =>
            R.Exp.DecLocal
              { id = id
              , left_dec = conv_dec left_dec
              , right_dec = conv_dec right_dec
              }

        | D.Exp.DecOpen {id, elems} => R.Exp.DecOpen {id = id, elems = elems}

        | D.Exp.DecMultiple {id, elems} =>
            R.Exp.DecMultiple {id = id, elems = Seq.map conv_dec elems}

        | D.Exp.DecInfix {id, precedence, elems} =>
            R.Exp.DecInfix {id = id, precedence = precedence, elems = elems}

        | D.Exp.DecInfixr {id, precedence, elems} =>
            R.Exp.DecInfixr {id = id, precedence = precedence, elems = elems}

        | D.Exp.DecNonfix {id, elems} =>
            R.Exp.DecNonfix {id = id, elems = elems}


      (* ===== Signatures ===== *)

      fun conv_sigexp sigexp =
        case sigexp of
          D.Sig.Ident {id, name} => R.Sig.Ident {id = id, name = name}

        | D.Sig.Spec {id, spec} => R.Sig.Spec {id = id, spec = conv_spec spec}

        | D.Sig.WhereType {id, sigexp, elems} =>
            R.Sig.WhereType
              { id = id
              , sigexp = conv_sigexp sigexp
              , elems =
                  Seq.map
                    (fn {tyvars, tycon, ty} =>
                       {tyvars = tyvars, tycon = tycon, ty = conv_ty ty}) elems
              }

      and conv_spec spec =
        case spec of
          D.Sig.EmptySpec => R.Sig.EmptySpec

        | D.Sig.Val {id, elems} =>
            R.Sig.Val
              { id = id
              , elems =
                  Seq.map (fn {name, ty} => {name = name, ty = conv_ty ty})
                    elems
              }

        | D.Sig.Type {id, elems} => R.Sig.Type {id = id, elems = elems}

        | D.Sig.TypeAbbreviation {id, typbind} =>
            R.Sig.TypeAbbreviation {id = id, typbind = conv_typbind typbind}

        | D.Sig.Eqtype {id, elems} => R.Sig.Eqtype {id = id, elems = elems}

        | D.Sig.Datatype {id, elems} =>
            R.Sig.Datatype
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

        | D.Sig.ReplicateDatatype {id, left_id, right_id} =>
            R.Sig.ReplicateDatatype
              {id = id, left_id = left_id, right_id = right_id}

        | D.Sig.Exception {id, elems} =>
            R.Sig.Exception
              { id = id
              , elems =
                  Seq.map
                    (fn {name, arg} =>
                       {name = name, arg = Option.map conv_ty arg}) elems
              }

        | D.Sig.Structure {id, elems} =>
            R.Sig.Structure
              { id = id
              , elems =
                  Seq.map
                    (fn {name, sigexp} =>
                       {name = name, sigexp = conv_sigexp sigexp}) elems
              }

        | D.Sig.Include {id, sigexp} =>
            R.Sig.Include {id = id, sigexp = conv_sigexp sigexp}

        | D.Sig.IncludeIds {id, names} =>
            R.Sig.IncludeIds {id = id, names = names}

        | D.Sig.SharingType {id, spec, elems} =>
            R.Sig.SharingType {id = id, spec = conv_spec spec, elems = elems}

        | D.Sig.Sharing {id, spec, elems} =>
            R.Sig.Sharing {id = id, spec = conv_spec spec, elems = elems}

        | D.Sig.Multiple {id, elems} =>
            R.Sig.Multiple {id = id, elems = Seq.map conv_spec elems}

      fun conv_sigdec (D.Sig.Signature {id, elems}) =
        R.Sig.Signature
          { id = id
          , elems =
              Seq.map
                (fn {name, sigexp} => {name = name, sigexp = conv_sigexp sigexp})
                elems
          }


      (* ===== Structures ===== *)

      fun conv_strexp strexp =
        case strexp of
          D.Str.Ident {id, name} => R.Str.Ident {id = id, name = name}

        | D.Str.Struct {id, strdec} =>
            R.Str.Struct {id = id, strdec = conv_strdec strdec}

        | D.Str.Constraint {id, strexp, is_opaque, sigexp} =>
            R.Str.Constraint
              { id = id
              , strexp = conv_strexp strexp
              , is_opaque = is_opaque
              , sigexp = conv_sigexp sigexp
              }

        | D.Str.FunAppExp {id, funid, strexp} =>
            R.Str.FunAppExp
              {id = id, funid = funid, strexp = conv_strexp strexp}

        | D.Str.FunAppDec {id, funid, strdec} =>
            R.Str.FunAppDec
              {id = id, funid = funid, strdec = conv_strdec strdec}

        | D.Str.LetInEnd {id, strdec, strexp} =>
            R.Str.LetInEnd
              { id = id
              , strdec = conv_strdec strdec
              , strexp = conv_strexp strexp
              }

      and conv_strdec strdec =
        case strdec of
          D.Str.DecEmpty => R.Str.DecEmpty

        | D.Str.DecCore dec => R.Str.DecCore (conv_dec dec)

        | D.Str.DecStructure {id, elems} =>
            R.Str.DecStructure
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

        | D.Str.DecMultiple {id, elems} =>
            R.Str.DecMultiple {id = id, elems = Seq.map conv_strdec elems}

        | D.Str.DecLocalInEnd {id, strdec1, strdec2} =>
            R.Str.DecLocalInEnd
              { id = id
              , strdec1 = conv_strdec strdec1
              , strdec2 = conv_strdec strdec2
              }

        | D.Str.MLtonOverload {id, prec, name, ty, elems} =>
            R.Str.MLtonOverload
              { id = id
              , prec = prec
              , name = name
              , ty = conv_ty ty
              , elems = elems
              }


      (* ===== Functors ===== *)

      fun conv_funarg funarg =
        case funarg of
          D.Fun.ArgIdent {id, name, sigexp} =>
            R.Fun.ArgIdent {id = id, name = name, sigexp = conv_sigexp sigexp}
        | D.Fun.ArgSpec {id, spec} =>
            R.Fun.ArgSpec {id = id, spec = conv_spec spec}

      fun conv_fundec (D.Fun.DecFunctor {id, elems}) =
        R.Fun.DecFunctor
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
          D.SigDec sd => R.SigDec (conv_sigdec sd)
        | D.StrDec sd => R.StrDec (conv_strdec sd)
        | D.FunDec fd => R.FunDec (conv_fundec fd)
        | D.TopExp {id, exp} => R.TopExp {id = id, exp = conv_exp exp}

      fun conv_topdecs (D.Program {id, topdecs}) =
        R.Program {id = id, topdecs = Seq.map conv_topdec topdecs}

      val result = conv_topdecs input
    in
      (result, lookup)
    end

end
