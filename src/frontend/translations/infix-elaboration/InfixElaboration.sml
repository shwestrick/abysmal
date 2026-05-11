structure InfixElaboration =
struct

  structure B = AfterBooleanElaboration
  structure A = AfterInfixElaboration

  fun translate (input: B.t) : A.t * (NodeID.t -> ProvenanceEvent.t) =
    let
      val pass = "InfixElaboration"

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
        | NONE => raise Fail ("no provenance for node " ^ NodeID.toString id)

      (* Synthesize a 2-element record pattern {"1"=left, "2"=right},
       * used when rewriting infix patterns to constructor applications. *)
      fun pair_pat (origin: NodeID.t) (left: A.Pat.t) (right: A.Pat.t) : A.Pat.t =
        A.Pat.Record
          { id = synth origin "infix pair record pattern"
          , elems = Seq.%
              [ A.Pat.LabEqPat
                  { id = synth origin "infix pair record pattern field 1"
                  , lab = "1"
                  , pat = left
                  }
              , A.Pat.LabEqPat
                  { id = synth origin "infix pair record pattern field 2"
                  , lab = "2"
                  , pat = right
                  }
              ]
          }

      (* Synthesize a 2-element record expression {"1"=left, "2"=right},
       * used when rewriting infix expressions to function applications. *)
      fun pair_exp (origin: NodeID.t) (left: A.Exp.exp) (right: A.Exp.exp) :
        A.Exp.exp =
        A.Exp.Record
          { id = synth origin "infix pair record expression"
          , elems = Seq.%
              [ A.Exp.RecordRow
                  { id = synth origin "infix pair record expression field 1"
                  , lab = "1"
                  , exp = left
                  }
              , A.Exp.RecordRow
                  { id = synth origin "infix pair record expression field 2"
                  , lab = "2"
                  , exp = right
                  }
              ]
          }

      fun conv_ty (ty: B.Ty.t) : A.Ty.t =
        case ty of
          B.Ty.Var {id, name} => A.Ty.Var {id = id, name = name}
        | B.Ty.Record {id, elems} =>
            A.Ty.Record
              { id = id
              , elems =
                  Seq.map (fn {lab, ty} => {lab = lab, ty = conv_ty ty}) elems
              }
        | B.Ty.Con {id, args, name} =>
            A.Ty.Con {id = id, args = Seq.map conv_ty args, name = name}
        | B.Ty.Arrow {id, from, to} =>
            A.Ty.Arrow {id = id, from = conv_ty from, to = conv_ty to}

      fun conv_pat (pat: B.Pat.t) : A.Pat.t =
        case pat of
          B.Pat.Wild id => A.Pat.Wild id
        | B.Pat.Const {id, value} => A.Pat.Const {id = id, value = value}
        | B.Pat.Ident {id, has_op = _, name} =>
            A.Pat.Ident {id = id, name = name}
        | B.Pat.List {id, elems} =>
            A.Pat.List {id = id, elems = Seq.map conv_pat elems}
        | B.Pat.Record {id, elems} =>
            A.Pat.Record {id = id, elems = Seq.map conv_patrow elems}
        | B.Pat.Con {id, has_op = _, name, atpat} =>
            A.Pat.Con {id = id, name = name, atpat = conv_pat atpat}
        | B.Pat.Infix {id, left, opr, right} =>
            A.Pat.Con
              { id = id
              , name = Seq.% [opr]
              , atpat = pair_pat id (conv_pat left) (conv_pat right)
              }
        | B.Pat.Typed {id, pat, ty} =>
            A.Pat.Typed {id = id, pat = conv_pat pat, ty = conv_ty ty}
        | B.Pat.Layered {id, has_op = _, name, ty, pat} =>
            A.Pat.Layered
              { id = id
              , name = name
              , ty = Option.map conv_ty ty
              , pat = conv_pat pat
              }
        | B.Pat.Or {id, elems} =>
            A.Pat.Or {id = id, elems = Seq.map conv_pat elems}

      and conv_patrow (row: B.Pat.patrow) : A.Pat.patrow =
        case row of
          B.Pat.DotDotDot id => A.Pat.DotDotDot id
        | B.Pat.LabEqPat {id, lab, pat} =>
            A.Pat.LabEqPat {id = id, lab = lab, pat = conv_pat pat}

      fun conv_exp (exp: B.Exp.exp) : A.Exp.exp =
        case exp of
          B.Exp.Const {id, value} => A.Exp.Const {id = id, value = value}
        | B.Exp.Ident {id, has_op = _, name} =>
            A.Exp.Ident {id = id, name = name}
        | B.Exp.Record {id, elems} =>
            A.Exp.Record {id = id, elems = Seq.map conv_row_exp elems}
        | B.Exp.Select {id, label} => A.Exp.Select {id = id, label = label}
        | B.Exp.List {id, elems} =>
            A.Exp.List {id = id, elems = Seq.map conv_exp elems}
        | B.Exp.Sequence {id, elems} =>
            A.Exp.Sequence {id = id, elems = Seq.map conv_exp elems}
        | B.Exp.LetInEnd {id, dec, exps} =>
            A.Exp.LetInEnd
              {id = id, dec = conv_dec dec, exps = Seq.map conv_exp exps}
        | B.Exp.App {id, left, right} =>
            A.Exp.App {id = id, left = conv_exp left, right = conv_exp right}
        | B.Exp.Infix {id, left, opr, right} =>
            A.Exp.App
              { id = id
              , left = A.Exp.Ident
                  {id = synth id "infix operator as prefix", name = Seq.% [opr]}
              , right = pair_exp id (conv_exp left) (conv_exp right)
              }
        | B.Exp.Typed {id, exp, ty} =>
            A.Exp.Typed {id = id, exp = conv_exp exp, ty = conv_ty ty}
        | B.Exp.Handle {id, exp, elems} =>
            A.Exp.Handle
              { id = id
              , exp = conv_exp exp
              , elems =
                  Seq.map
                    (fn {pat, exp} => {pat = conv_pat pat, exp = conv_exp exp})
                    elems
              }
        | B.Exp.Raise {id, exp} => A.Exp.Raise {id = id, exp = conv_exp exp}
        | B.Exp.While {id, exp1, exp2} =>
            A.Exp.While {id = id, exp1 = conv_exp exp1, exp2 = conv_exp exp2}
        | B.Exp.Case {id, exp, elems} =>
            A.Exp.Case
              { id = id
              , exp = conv_exp exp
              , elems =
                  Seq.map
                    (fn {pat, exp} => {pat = conv_pat pat, exp = conv_exp exp})
                    elems
              }
        | B.Exp.Fn {id, elems} =>
            A.Exp.Fn
              { id = id
              , elems =
                  Seq.map
                    (fn {pat, exp} => {pat = conv_pat pat, exp = conv_exp exp})
                    elems
              }
        | B.Exp.MLtonSpecific {id, directive, contents} =>
            A.Exp.MLtonSpecific
              {id = id, directive = directive, contents = contents}

      and conv_row_exp (row: B.Exp.exp B.Exp.row_exp) : A.Exp.exp A.Exp.row_exp =
        case row of
          B.Exp.RecordRow {id, lab, exp} =>
            A.Exp.RecordRow {id = id, lab = lab, exp = conv_exp exp}

      and conv_dec (dec: B.Exp.dec) : A.Exp.dec =
        case dec of
          B.Exp.DecEmpty => A.Exp.DecEmpty
        | B.Exp.DecVal {id, tyvars, elems} =>
            A.Exp.DecVal
              { id = id
              , tyvars = tyvars
              , elems =
                  Seq.map
                    (fn {is_rec, pat, exp} =>
                       {is_rec = is_rec, pat = conv_pat pat, exp = conv_exp exp})
                    elems
              }
        | B.Exp.DecFun {id, tyvars, fvalbind} =>
            A.Exp.DecFun
              {id = id, tyvars = tyvars, fvalbind = conv_fvalbind fvalbind}
        | B.Exp.DecType {id, typbind} =>
            A.Exp.DecType {id = id, typbind = conv_typbind typbind}
        | B.Exp.DecDatatype {id, datbind, withtypee} =>
            A.Exp.DecDatatype
              { id = id
              , datbind = conv_datbind datbind
              , withtypee = Option.map conv_typbind withtypee
              }
        | B.Exp.DecReplicateDatatype {id, left_name, right_name} =>
            A.Exp.DecReplicateDatatype
              {id = id, left_name = left_name, right_name = right_name}
        | B.Exp.DecAbstype {id, datbind, withtypee, dec} =>
            A.Exp.DecAbstype
              { id = id
              , datbind = conv_datbind datbind
              , withtypee = Option.map conv_typbind withtypee
              , dec = conv_dec dec
              }
        | B.Exp.DecException {id, elems} =>
            A.Exp.DecException {id = id, elems = Seq.map conv_exbind elems}
        | B.Exp.DecLocal {id, left_dec, right_dec} =>
            A.Exp.DecLocal
              { id = id
              , left_dec = conv_dec left_dec
              , right_dec = conv_dec right_dec
              }
        | B.Exp.DecOpen {id, elems} => A.Exp.DecOpen {id = id, elems = elems}
        | B.Exp.DecMultiple {id, elems} =>
            A.Exp.DecMultiple {id = id, elems = Seq.map conv_dec elems}
        | B.Exp.DecInfix _ => A.Exp.DecEmpty
        | B.Exp.DecInfixr _ => A.Exp.DecEmpty
        | B.Exp.DecNonfix _ => A.Exp.DecEmpty

      and conv_typbind ({elems}: B.Exp.typbind) : A.Exp.typbind =
        {elems =
           Seq.map
             (fn {tyvars, tycon, ty} =>
                {tyvars = tyvars, tycon = tycon, ty = conv_ty ty}) elems}

      and conv_datbind ({elems}: B.Exp.datbind) : A.Exp.datbind =
        {elems =
           Seq.map
             (fn {tyvars, tycon, elems} =>
                { tyvars = tyvars
                , tycon = tycon
                , elems =
                    Seq.map
                      (fn {has_op = _, name, arg} =>
                         {name = name, arg = Option.map conv_ty arg}) elems
                }) elems}

      and conv_exbind (eb: B.Exp.exbind) : A.Exp.exbind =
        case eb of
          B.Exp.ExnNew {id, has_op = _, name, arg} =>
            A.Exp.ExnNew {id = id, name = name, arg = Option.map conv_ty arg}
        | B.Exp.ExnReplicate {id, has_op = _, left_name, right_name} =>
            A.Exp.ExnReplicate
              {id = id, left_name = left_name, right_name = right_name}

      and conv_fname_args (fa: B.Exp.fname_args) : A.Exp.fname_args =
        case fa of
          B.Exp.PrefixedFun {id, has_op = _, name, args} =>
            {id = id, name = name, args = Seq.map conv_pat args}
        | B.Exp.InfixedFun {id, larg, name, rarg} =>
            { id = id
            , name = name
            , args = Seq.% [pair_pat id (conv_pat larg) (conv_pat rarg)]
            }
        | B.Exp.CurriedInfixedFun {id, larg, name, rarg, args} =>
            { id = id
            , name = name
            , args = Seq.append
                ( Seq.% [pair_pat id (conv_pat larg) (conv_pat rarg)]
                , Seq.map conv_pat args
                )
            }

      and conv_fvalbind (fvb: B.Exp.exp B.Exp.fvalbind) :
        A.Exp.exp A.Exp.fvalbind =
        {elems =
           Seq.map
             (fn {elems} =>
                {elems =
                   Seq.map
                     (fn {fname_args, ty, exp} =>
                        { fname_args = conv_fname_args fname_args
                        , ty = Option.map conv_ty ty
                        , exp = conv_exp exp
                        }) elems}) (#elems fvb)}

      fun conv_sigexp (se: B.Sig.sigexp) : A.Sig.sigexp =
        case se of
          B.Sig.Ident {id, name} => A.Sig.Ident {id = id, name = name}
        | B.Sig.Spec {id, spec} => A.Sig.Spec {id = id, spec = conv_spec spec}
        | B.Sig.WhereType {id, sigexp, elems} =>
            A.Sig.WhereType
              { id = id
              , sigexp = conv_sigexp sigexp
              , elems =
                  Seq.map
                    (fn {tyvars, tycon, ty} =>
                       {tyvars = tyvars, tycon = tycon, ty = conv_ty ty}) elems
              }

      and conv_spec (spec: B.Sig.spec) : A.Sig.spec =
        case spec of
          B.Sig.EmptySpec => A.Sig.EmptySpec
        | B.Sig.Val {id, elems} =>
            A.Sig.Val
              { id = id
              , elems =
                  Seq.map (fn {name, ty} => {name = name, ty = conv_ty ty})
                    elems
              }
        | B.Sig.Type {id, elems} => A.Sig.Type {id = id, elems = elems}
        | B.Sig.TypeAbbreviation {id, typbind} =>
            A.Sig.TypeAbbreviation {id = id, typbind = conv_typbind typbind}
        | B.Sig.Eqtype {id, elems} => A.Sig.Eqtype {id = id, elems = elems}
        | B.Sig.Datatype {id, elems} =>
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
        | B.Sig.ReplicateDatatype {id, left_id, right_id} =>
            A.Sig.ReplicateDatatype
              {id = id, left_id = left_id, right_id = right_id}
        | B.Sig.Exception {id, elems} =>
            A.Sig.Exception
              { id = id
              , elems =
                  Seq.map
                    (fn {name, arg} =>
                       {name = name, arg = Option.map conv_ty arg}) elems
              }
        | B.Sig.Structure {id, elems} =>
            A.Sig.Structure
              { id = id
              , elems =
                  Seq.map
                    (fn {name, sigexp} =>
                       {name = name, sigexp = conv_sigexp sigexp}) elems
              }
        | B.Sig.Include {id, sigexp} =>
            A.Sig.Include {id = id, sigexp = conv_sigexp sigexp}
        | B.Sig.IncludeIds {id, names} =>
            A.Sig.IncludeIds {id = id, names = names}
        | B.Sig.SharingType {id, spec, elems} =>
            A.Sig.SharingType {id = id, spec = conv_spec spec, elems = elems}
        | B.Sig.Sharing {id, spec, elems} =>
            A.Sig.Sharing {id = id, spec = conv_spec spec, elems = elems}
        | B.Sig.Multiple {id, elems} =>
            A.Sig.Multiple {id = id, elems = Seq.map conv_spec elems}

      fun conv_sigdec (sd: B.Sig.sigdec) : A.Sig.sigdec =
        case sd of
          B.Sig.Signature {id, elems} =>
            A.Sig.Signature
              { id = id
              , elems =
                  Seq.map
                    (fn {name, sigexp} =>
                       {name = name, sigexp = conv_sigexp sigexp}) elems
              }

      fun conv_strexp (se: B.Str.strexp) : A.Str.strexp =
        case se of
          B.Str.Ident {id, name} => A.Str.Ident {id = id, name = name}
        | B.Str.Struct {id, strdec} =>
            A.Str.Struct {id = id, strdec = conv_strdec strdec}
        | B.Str.Constraint {id, strexp, is_opaque, sigexp} =>
            A.Str.Constraint
              { id = id
              , strexp = conv_strexp strexp
              , is_opaque = is_opaque
              , sigexp = conv_sigexp sigexp
              }
        | B.Str.FunAppExp {id, funid, strexp} =>
            A.Str.FunAppExp
              {id = id, funid = funid, strexp = conv_strexp strexp}
        | B.Str.FunAppDec {id, funid, strdec} =>
            A.Str.FunAppDec
              {id = id, funid = funid, strdec = conv_strdec strdec}
        | B.Str.LetInEnd {id, strdec, strexp} =>
            A.Str.LetInEnd
              { id = id
              , strdec = conv_strdec strdec
              , strexp = conv_strexp strexp
              }

      and conv_strdec (sd: B.Str.strdec) : A.Str.strdec =
        case sd of
          B.Str.DecEmpty => A.Str.DecEmpty
        | B.Str.DecCore dec => A.Str.DecCore (conv_dec dec)
        | B.Str.DecStructure {id, elems} =>
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
        | B.Str.DecMultiple {id, elems} =>
            A.Str.DecMultiple {id = id, elems = Seq.map conv_strdec elems}
        | B.Str.DecLocalInEnd {id, strdec1, strdec2} =>
            A.Str.DecLocalInEnd
              { id = id
              , strdec1 = conv_strdec strdec1
              , strdec2 = conv_strdec strdec2
              }
        | B.Str.MLtonOverload {id, prec, name, ty, elems} =>
            A.Str.MLtonOverload
              { id = id
              , prec = prec
              , name = name
              , ty = conv_ty ty
              , elems = elems
              }

      fun conv_funarg (fa: B.Fun.funarg) : A.Fun.funarg =
        case fa of
          B.Fun.ArgIdent {id, name, sigexp} =>
            A.Fun.ArgIdent {id = id, name = name, sigexp = conv_sigexp sigexp}
        | B.Fun.ArgSpec {id, spec} =>
            A.Fun.ArgSpec {id = id, spec = conv_spec spec}

      fun conv_fundec (fd: B.Fun.fundec) : A.Fun.fundec =
        case fd of
          B.Fun.DecFunctor {id, elems} =>
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
                                { is_opaque = is_opaque
                                , sigexp = conv_sigexp sigexp
                                }) constraint
                       , strexp = conv_strexp strexp
                       }) elems
              }

      fun conv_topdec (td: B.topdec) : A.topdec =
        case td of
          B.SigDec sd => A.SigDec (conv_sigdec sd)
        | B.StrDec sd => A.StrDec (conv_strdec sd)
        | B.FunDec fd => A.FunDec (conv_fundec fd)
        | B.TopExp {id, exp} => A.TopExp {id = id, exp = conv_exp exp}

      fun conv_topdecs (B.Program {id, topdecs}) : A.t =
        A.Program {id = id, topdecs = Seq.map conv_topdec topdecs}

      val result = conv_topdecs input
    in
      (result, lookup)
    end

end
