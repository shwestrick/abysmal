structure FnElaboration:
sig
  val translate: AfterFunElaboration.t -> AfterFnElaboration.t * Provenance.t
end =
struct

  structure I = AfterFunElaboration
  structure O = AfterFnElaboration

  fun translate (input: I.t) : O.t * Provenance.t =
    let
      val pass = "FnElaboration"

      val prov_entries: (NodeID.t * ProvenanceEvent.t) list ref = ref []

      fun emit (id, p) =
        prov_entries := (id, p) :: !prov_entries

      fun synth (origin: NodeID.t) (why: string) : NodeID.t =
        let
          val id = NodeID.fresh ()
        in
          emit
            ( id
            , ProvenanceEvent.Synthesized
                {id = id, pass = pass, origin = origin, why = why}
            );
          id
        end

      fun lookup (id: NodeID.t) : ProvenanceEvent.t =
        case
          List.find (fn (id', _) => NodeID.compare (id, id') = EQUAL)
            (!prov_entries)
        of
          SOME (_, p) => p
        | NONE =>
            raise Fail ("no provenance for node " ^ NodeID.toString id)

      fun conv_ty (ty: I.Ty.t) : O.Ty.t =
        case ty of
          I.Ty.Var {id, name} => O.Ty.Var {id = id, name = name}
        | I.Ty.Record {id, elems} =>
            O.Ty.Record
              { id = id
              , elems =
                  Seq.map (fn {lab, ty} => {lab = lab, ty = conv_ty ty}) elems
              }
        | I.Ty.Con {id, args, name} =>
            O.Ty.Con {id = id, args = Seq.map conv_ty args, name = name}
        | I.Ty.Arrow {id, from, to} =>
            O.Ty.Arrow {id = id, from = conv_ty from, to = conv_ty to}

      fun conv_pat (pat: I.Pat.t) : O.Pat.t =
        case pat of
          I.Pat.Wild id => O.Pat.Wild id
        | I.Pat.Const {id, value} => O.Pat.Const {id = id, value = value}
        | I.Pat.Ident {id, name} => O.Pat.Ident {id = id, name = name}
        | I.Pat.List {id, elems} =>
            O.Pat.List {id = id, elems = Seq.map conv_pat elems}
        | I.Pat.Record {id, elems} =>
            O.Pat.Record {id = id, elems = Seq.map conv_patrow elems}
        | I.Pat.Con {id, name, atpat} =>
            O.Pat.Con {id = id, name = name, atpat = conv_pat atpat}
        | I.Pat.Typed {id, pat, ty} =>
            O.Pat.Typed {id = id, pat = conv_pat pat, ty = conv_ty ty}
        | I.Pat.Layered {id, name, ty, pat} =>
            O.Pat.Layered
              { id = id
              , name = name
              , ty = Option.map conv_ty ty
              , pat = conv_pat pat
              }
        | I.Pat.Or {id, elems} =>
            O.Pat.Or {id = id, elems = Seq.map conv_pat elems}

      and conv_patrow (row: I.Pat.patrow) : O.Pat.patrow =
        case row of
          I.Pat.DotDotDot id => O.Pat.DotDotDot id
        | I.Pat.LabEqPat {id, lab, pat} =>
            O.Pat.LabEqPat {id = id, lab = lab, pat = conv_pat pat}

      fun conv_exp (exp: I.Exp.exp) : O.Exp.exp =
        case exp of
          I.Exp.Const {id, value} => O.Exp.Const {id = id, value = value}
        | I.Exp.Ident {id, name} => O.Exp.Ident {id = id, name = name}
        | I.Exp.Record {id, elems} =>
            O.Exp.Record {id = id, elems = Seq.map conv_row_exp elems}
        | I.Exp.Select {id, label} => O.Exp.Select {id = id, label = label}
        | I.Exp.List {id, elems} =>
            O.Exp.List {id = id, elems = Seq.map conv_exp elems}
        | I.Exp.Sequence {id, elems} =>
            O.Exp.Sequence {id = id, elems = Seq.map conv_exp elems}
        | I.Exp.LetInEnd {id, dec, exps} =>
            O.Exp.LetInEnd
              {id = id, dec = conv_dec dec, exps = Seq.map conv_exp exps}
        | I.Exp.App {id, left, right} =>
            O.Exp.App {id = id, left = conv_exp left, right = conv_exp right}
        | I.Exp.Typed {id, exp, ty} =>
            O.Exp.Typed {id = id, exp = conv_exp exp, ty = conv_ty ty}
        | I.Exp.Handle {id, exp, elems} =>
            O.Exp.Handle
              { id = id
              , exp = conv_exp exp
              , elems =
                  Seq.map
                    (fn {pat, exp} => {pat = conv_pat pat, exp = conv_exp exp})
                    elems
              }
        | I.Exp.Raise {id, exp} => O.Exp.Raise {id = id, exp = conv_exp exp}
        | I.Exp.While {id, exp1, exp2} =>
            O.Exp.While {id = id, exp1 = conv_exp exp1, exp2 = conv_exp exp2}
        | I.Exp.Case {id, exp, elems} =>
            O.Exp.Case
              { id = id
              , exp = conv_exp exp
              , elems =
                  Seq.map
                    (fn {pat, exp} => {pat = conv_pat pat, exp = conv_exp exp})
                    elems
              }
        | I.Exp.Fn {id, elems} =>
            (case Seq.toList elems of
               [{pat, exp}] =>
                 (* Single clause: pure passthrough, no provenance events *)
                 O.Exp.Fn {id = id, pat = conv_pat pat, exp = conv_exp exp}
             | clauses =>
                 (* Multi-clause: introduce _x and dispatch with case *)
                 let
                   val x_pat_id = synth id "fn multi-clause arg pat"
                   val x_exp_id = synth id "fn multi-clause arg exp"
                   val case_id = synth id "fn multi-clause case"
                   val fn_id = synth id "fn multi-clause"
                 in
                   O.Exp.Fn
                     { id = fn_id
                     , pat = O.Pat.Ident {id = x_pat_id, name = Seq.% ["_x"]}
                     , exp = O.Exp.Case
                         { id = case_id
                         , exp =
                             O.Exp.Ident {id = x_exp_id, name = Seq.% ["_x"]}
                         , elems = Seq.%
                             (List.map
                                (fn {pat, exp} =>
                                   { pat = conv_pat pat
                                   , exp = conv_exp exp
                                   })
                                clauses)
                         }
                     }
                 end)
        | I.Exp.MLtonSpecific {id, directive, contents} =>
            O.Exp.MLtonSpecific
              {id = id, directive = directive, contents = contents}

      and conv_row_exp (row: I.Exp.exp I.Exp.row_exp) : O.Exp.exp O.Exp.row_exp =
        case row of
          I.Exp.RecordRow {id, lab, exp} =>
            O.Exp.RecordRow {id = id, lab = lab, exp = conv_exp exp}

      and conv_dec (dec: I.Exp.dec) : O.Exp.dec =
        case dec of
          I.Exp.DecEmpty => O.Exp.DecEmpty
        | I.Exp.DecVal {id, tyvars, elems} =>
            O.Exp.DecVal
              { id = id
              , tyvars = tyvars
              , elems =
                  Seq.map
                    (fn {is_rec, pat, exp} =>
                       {is_rec = is_rec, pat = conv_pat pat, exp = conv_exp exp})
                    elems
              }
        | I.Exp.DecType {id, typbind} =>
            O.Exp.DecType {id = id, typbind = conv_typbind typbind}
        | I.Exp.DecDatatype {id, datbind, withtypee} =>
            O.Exp.DecDatatype
              { id = id
              , datbind = conv_datbind datbind
              , withtypee = Option.map conv_typbind withtypee
              }
        | I.Exp.DecReplicateDatatype {id, left_name, right_name} =>
            O.Exp.DecReplicateDatatype
              {id = id, left_name = left_name, right_name = right_name}
        | I.Exp.DecAbstype {id, datbind, withtypee, dec} =>
            O.Exp.DecAbstype
              { id = id
              , datbind = conv_datbind datbind
              , withtypee = Option.map conv_typbind withtypee
              , dec = conv_dec dec
              }
        | I.Exp.DecException {id, elems} =>
            O.Exp.DecException {id = id, elems = Seq.map conv_exbind elems}
        | I.Exp.DecLocal {id, left_dec, right_dec} =>
            O.Exp.DecLocal
              { id = id
              , left_dec = conv_dec left_dec
              , right_dec = conv_dec right_dec
              }
        | I.Exp.DecOpen {id, elems} => O.Exp.DecOpen {id = id, elems = elems}
        | I.Exp.DecMultiple {id, elems} =>
            O.Exp.DecMultiple {id = id, elems = Seq.map conv_dec elems}

      and conv_typbind ({elems}: I.Exp.typbind) : O.Exp.typbind =
        {elems =
           Seq.map
             (fn {tyvars, tycon, ty} =>
                {tyvars = tyvars, tycon = tycon, ty = conv_ty ty}) elems}

      and conv_datbind ({elems}: I.Exp.datbind) : O.Exp.datbind =
        {elems =
           Seq.map
             (fn {tyvars, tycon, elems} =>
                { tyvars = tyvars
                , tycon = tycon
                , elems =
                    Seq.map
                      (fn {name, arg} =>
                         {name = name, arg = Option.map conv_ty arg}) elems
                }) elems}

      and conv_exbind (eb: I.Exp.exbind) : O.Exp.exbind =
        case eb of
          I.Exp.ExnNew {id, name, arg} =>
            O.Exp.ExnNew {id = id, name = name, arg = Option.map conv_ty arg}
        | I.Exp.ExnReplicate {id, left_name, right_name} =>
            O.Exp.ExnReplicate
              {id = id, left_name = left_name, right_name = right_name}

      fun conv_sigexp (se: I.Sig.sigexp) : O.Sig.sigexp =
        case se of
          I.Sig.Ident {id, name} => O.Sig.Ident {id = id, name = name}
        | I.Sig.Spec {id, spec} => O.Sig.Spec {id = id, spec = conv_spec spec}
        | I.Sig.WhereType {id, sigexp, elems} =>
            O.Sig.WhereType
              { id = id
              , sigexp = conv_sigexp sigexp
              , elems =
                  Seq.map
                    (fn {tyvars, tycon, ty} =>
                       {tyvars = tyvars, tycon = tycon, ty = conv_ty ty}) elems
              }

      and conv_spec (spec: I.Sig.spec) : O.Sig.spec =
        case spec of
          I.Sig.EmptySpec => O.Sig.EmptySpec
        | I.Sig.Val {id, elems} =>
            O.Sig.Val
              { id = id
              , elems =
                  Seq.map (fn {name, ty} => {name = name, ty = conv_ty ty})
                    elems
              }
        | I.Sig.Type {id, elems} => O.Sig.Type {id = id, elems = elems}
        | I.Sig.TypeAbbreviation {id, typbind} =>
            O.Sig.TypeAbbreviation {id = id, typbind = conv_typbind typbind}
        | I.Sig.Eqtype {id, elems} => O.Sig.Eqtype {id = id, elems = elems}
        | I.Sig.Datatype {id, elems} =>
            O.Sig.Datatype
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
        | I.Sig.ReplicateDatatype {id, left_id, right_id} =>
            O.Sig.ReplicateDatatype
              {id = id, left_id = left_id, right_id = right_id}
        | I.Sig.Exception {id, elems} =>
            O.Sig.Exception
              { id = id
              , elems =
                  Seq.map
                    (fn {name, arg} =>
                       {name = name, arg = Option.map conv_ty arg}) elems
              }
        | I.Sig.Structure {id, elems} =>
            O.Sig.Structure
              { id = id
              , elems =
                  Seq.map
                    (fn {name, sigexp} =>
                       {name = name, sigexp = conv_sigexp sigexp}) elems
              }
        | I.Sig.Include {id, sigexp} =>
            O.Sig.Include {id = id, sigexp = conv_sigexp sigexp}
        | I.Sig.IncludeIds {id, names} =>
            O.Sig.IncludeIds {id = id, names = names}
        | I.Sig.SharingType {id, spec, elems} =>
            O.Sig.SharingType {id = id, spec = conv_spec spec, elems = elems}
        | I.Sig.Sharing {id, spec, elems} =>
            O.Sig.Sharing {id = id, spec = conv_spec spec, elems = elems}
        | I.Sig.Multiple {id, elems} =>
            O.Sig.Multiple {id = id, elems = Seq.map conv_spec elems}

      fun conv_sigdec (sd: I.Sig.sigdec) : O.Sig.sigdec =
        case sd of
          I.Sig.Signature {id, elems} =>
            O.Sig.Signature
              { id = id
              , elems =
                  Seq.map
                    (fn {name, sigexp} =>
                       {name = name, sigexp = conv_sigexp sigexp}) elems
              }

      fun conv_strexp (se: I.Str.strexp) : O.Str.strexp =
        case se of
          I.Str.Ident {id, name} => O.Str.Ident {id = id, name = name}
        | I.Str.Struct {id, strdec} =>
            O.Str.Struct {id = id, strdec = conv_strdec strdec}
        | I.Str.Constraint {id, strexp, is_opaque, sigexp} =>
            O.Str.Constraint
              { id = id
              , strexp = conv_strexp strexp
              , is_opaque = is_opaque
              , sigexp = conv_sigexp sigexp
              }
        | I.Str.FunAppExp {id, funid, strexp} =>
            O.Str.FunAppExp
              {id = id, funid = funid, strexp = conv_strexp strexp}
        | I.Str.FunAppDec {id, funid, strdec} =>
            O.Str.FunAppDec
              {id = id, funid = funid, strdec = conv_strdec strdec}
        | I.Str.LetInEnd {id, strdec, strexp} =>
            O.Str.LetInEnd
              { id = id
              , strdec = conv_strdec strdec
              , strexp = conv_strexp strexp
              }

      and conv_strdec (sd: I.Str.strdec) : O.Str.strdec =
        case sd of
          I.Str.DecEmpty => O.Str.DecEmpty
        | I.Str.DecCore dec => O.Str.DecCore (conv_dec dec)
        | I.Str.DecStructure {id, elems} =>
            O.Str.DecStructure
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
        | I.Str.DecMultiple {id, elems} =>
            O.Str.DecMultiple {id = id, elems = Seq.map conv_strdec elems}
        | I.Str.DecLocalInEnd {id, strdec1, strdec2} =>
            O.Str.DecLocalInEnd
              { id = id
              , strdec1 = conv_strdec strdec1
              , strdec2 = conv_strdec strdec2
              }
        | I.Str.MLtonOverload {id, prec, name, ty, elems} =>
            O.Str.MLtonOverload
              { id = id
              , prec = prec
              , name = name
              , ty = conv_ty ty
              , elems = elems
              }

      fun conv_funarg (fa: I.Fun.funarg) : O.Fun.funarg =
        case fa of
          I.Fun.ArgIdent {id, name, sigexp} =>
            O.Fun.ArgIdent {id = id, name = name, sigexp = conv_sigexp sigexp}
        | I.Fun.ArgSpec {id, spec} =>
            O.Fun.ArgSpec {id = id, spec = conv_spec spec}

      fun conv_fundec (fd: I.Fun.fundec) : O.Fun.fundec =
        case fd of
          I.Fun.DecFunctor {id, elems} =>
            O.Fun.DecFunctor
              { id = id
              , elems =
                  Seq.map
                    (fn {name, funarg, constraint, strexp} =>
                       { name = name
                       , funarg = conv_funarg funarg
                       , constraint =
                           Option.map
                             (fn {is_opaque, sigexp} =>
                                { is_opaque = is_opaque
                                , sigexp = conv_sigexp sigexp
                                }) constraint
                       , strexp = conv_strexp strexp
                       }) elems
              }

      fun conv_topdec (td: I.topdec) : O.topdec =
        case td of
          I.SigDec sd => O.SigDec (conv_sigdec sd)
        | I.StrDec sd => O.StrDec (conv_strdec sd)
        | I.FunDec fd => O.FunDec (conv_fundec fd)
        | I.TopExp {id, exp} => O.TopExp {id = id, exp = conv_exp exp}

      fun conv_program (I.Program {id, topdecs}) : O.t =
        O.Program {id = id, topdecs = Seq.map conv_topdec topdecs}

      val result = conv_program input
    in
      (result, lookup)
    end

end
