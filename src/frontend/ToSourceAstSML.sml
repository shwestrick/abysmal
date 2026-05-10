structure ToSourceAstSML =
struct

  fun convert
      (fresh_node: Source.t -> NodeID.t)
      (sml_src: Source.t)
      (ast: Ast.t)
      : SourceAst.sml_ast =
    let
      fun nn () = fresh_node sml_src

      fun tok_str (tok: Token.t) : string = Token.toString tok

      fun split_longid (s: string) : string Seq.t =
        let
          fun loop acc i j =
            if j >= String.size s then
              Seq.fromList (List.rev (String.substring (s, i, j - i) :: acc))
            else if String.sub (s, j) = #"." then
              loop (String.substring (s, i, j - i) :: acc) (j + 1) (j + 1)
            else
              loop acc i (j + 1)
        in
          loop [] 0 0
        end

      fun longid_of (mlt: MaybeLongToken.t) : SourceAst.longid =
        split_longid (tok_str (MaybeLongToken.getToken mlt))

      fun tyvars_of_ss (ss: Token.t Ast.SyntaxSeq.t) : string Seq.t =
        case ss of
          Ast.SyntaxSeq.Empty => Seq.empty ()
        | Ast.SyntaxSeq.One tok => Seq.singleton (tok_str tok)
        | Ast.SyntaxSeq.Many {elems, ...} => Seq.map tok_str elems


      fun conv_ty (ty: Ast.Ty.ty) : SourceAst.Ty.ty =
        let
          fun ss_to_seq ss =
            case ss of
              Ast.SyntaxSeq.Empty => Seq.empty ()
            | Ast.SyntaxSeq.One t => Seq.singleton (conv_ty t)
            | Ast.SyntaxSeq.Many {elems, ...} => Seq.map conv_ty elems
        in
          case ty of
            Ast.Ty.Var tok =>
              SourceAst.Ty.Var {id = nn (), name = tok_str tok}
          | Ast.Ty.Record {elems, ...} =>
              SourceAst.Ty.Record
                { id = nn ()
                , elems = Seq.map
                    (fn {lab, ty, ...} => {lab = tok_str lab, ty = conv_ty ty})
                    elems
                }
          | Ast.Ty.Tuple {elems, ...} =>
              SourceAst.Ty.Tuple {id = nn (), elems = Seq.map conv_ty elems}
          | Ast.Ty.Con {args, id} =>
              SourceAst.Ty.Con
                { id = nn ()
                , args = ss_to_seq args
                , name = longid_of id
                }
          | Ast.Ty.Arrow {from, to, ...} =>
              SourceAst.Ty.Arrow {id = nn (), from = conv_ty from, to = conv_ty to}
          | Ast.Ty.Parens {ty, ...} => conv_ty ty
        end


      fun conv_patrow (pr: Ast.Pat.patrow) : SourceAst.Pat.patrow =
        case pr of
          Ast.Pat.DotDotDot _ =>
            SourceAst.Pat.DotDotDot (nn ())
        | Ast.Pat.LabEqPat {lab, pat, ...} =>
            SourceAst.Pat.LabEqPat
              { id = nn ()
              , lab = tok_str lab
              , pat = conv_pat pat
              }
        | Ast.Pat.LabAsPat {id, ty, aspat} =>
            SourceAst.Pat.LabAsPat
              { id = nn ()
              , name = tok_str id
              , ty = Option.map (fn {ty, ...} => conv_ty ty) ty
              , aspat = Option.map (fn {pat, ...} => conv_pat pat) aspat
              }

      and conv_pat (pat: Ast.Pat.pat) : SourceAst.Pat.pat =
        case pat of
          Ast.Pat.Wild _ =>
            SourceAst.Pat.Wild (nn ())
        | Ast.Pat.Const tok =>
            SourceAst.Pat.Const {id = nn (), value = tok_str tok}
        | Ast.Pat.Unit _ =>
            SourceAst.Pat.Unit (nn ())
        | Ast.Pat.Ident {opp, id} =>
            SourceAst.Pat.Ident
              { id = nn ()
              , has_op = Option.isSome opp
              , name = longid_of id
              }
        | Ast.Pat.List {elems, ...} =>
            SourceAst.Pat.List {id = nn (), elems = Seq.map conv_pat elems}
        | Ast.Pat.Tuple {elems, ...} =>
            SourceAst.Pat.Tuple {id = nn (), elems = Seq.map conv_pat elems}
        | Ast.Pat.Record {elems, ...} =>
            SourceAst.Pat.Record {id = nn (), elems = Seq.map conv_patrow elems}
        | Ast.Pat.Parens {pat, ...} => conv_pat pat
        | Ast.Pat.Con {opp, id, atpat} =>
            SourceAst.Pat.Con
              { id = nn ()
              , has_op = Option.isSome opp
              , name = longid_of id
              , atpat = conv_pat atpat
              }
        | Ast.Pat.Infix {left, id, right} =>
            SourceAst.Pat.Infix
              { id = nn ()
              , left = conv_pat left
              , opr = tok_str id
              , right = conv_pat right
              }
        | Ast.Pat.Typed {pat, ty, ...} =>
            SourceAst.Pat.Typed {id = nn (), pat = conv_pat pat, ty = conv_ty ty}
        | Ast.Pat.Layered {opp, id, ty, pat, ...} =>
            SourceAst.Pat.Layered
              { id = nn ()
              , has_op = Option.isSome opp
              , name = tok_str id
              , ty = Option.map (fn {ty, ...} => conv_ty ty) ty
              , pat = conv_pat pat
              }
        | Ast.Pat.Or {elems, ...} =>
            SourceAst.Pat.Or {id = nn (), elems = Seq.map conv_pat elems}


      fun conv_typbind ({elems, ...}: Ast.Exp.typbind) : SourceAst.Exp.typbind =
        { elems = Seq.map
            (fn {tyvars, tycon, ty, ...} =>
              { tyvars = tyvars_of_ss tyvars
              , tycon = tok_str tycon
              , ty = conv_ty ty
              })
            elems
        }

      fun conv_datbind ({elems, ...}: Ast.Exp.datbind) : SourceAst.Exp.datbind =
        { elems = Seq.map
            (fn {tyvars, tycon, elems, ...} =>
              { tyvars = tyvars_of_ss tyvars
              , tycon = tok_str tycon
              , elems = Seq.map
                  (fn {opp, id, arg} =>
                    { has_op = Option.isSome opp
                    , name = tok_str id
                    , arg = Option.map (fn {ty, ...} => conv_ty ty) arg
                    })
                  elems
              })
            elems
        }

      fun conv_exbind (eb: Ast.Exp.exbind) : SourceAst.Exp.exbind =
        case eb of
          Ast.Exp.ExnNew {opp, id, arg} =>
            SourceAst.Exp.ExnNew
              { id = nn ()
              , has_op = Option.isSome opp
              , name = tok_str id
              , arg = Option.map (fn {ty, ...} => conv_ty ty) arg
              }
        | Ast.Exp.ExnReplicate {opp, left_id, right_id, ...} =>
            SourceAst.Exp.ExnReplicate
              { id = nn ()
              , has_op = Option.isSome opp
              , left_name = tok_str left_id
              , right_name = longid_of right_id
              }


      fun conv_row_exp (re: Ast.Exp.exp Ast.Exp.row_exp)
          : SourceAst.Exp.exp SourceAst.Exp.row_exp =
        case re of
          Ast.Exp.RecordRow {lab, exp, ...} =>
            SourceAst.Exp.RecordRow {id = nn (), lab = tok_str lab, exp = conv_exp exp}
        | Ast.Exp.RecordPun {id} =>
            SourceAst.Exp.RecordPun {id = nn (), name = tok_str id}

      and conv_fname_args (fa: Ast.Exp.fname_args) : SourceAst.Exp.fname_args =
        case fa of
          Ast.Exp.PrefixedFun {opp, id, args} =>
            SourceAst.Exp.PrefixedFun
              { id = nn ()
              , has_op = Option.isSome opp
              , name = tok_str id
              , args = Seq.map conv_pat args
              }
        | Ast.Exp.InfixedFun {larg, id, rarg} =>
            SourceAst.Exp.InfixedFun
              { id = nn ()
              , larg = conv_pat larg
              , name = tok_str id
              , rarg = conv_pat rarg
              }
        | Ast.Exp.CurriedInfixedFun {larg, id, rarg, args, ...} =>
            SourceAst.Exp.CurriedInfixedFun
              { id = nn ()
              , larg = conv_pat larg
              , name = tok_str id
              , rarg = conv_pat rarg
              , args = Seq.map conv_pat args
              }

      and conv_fvalbind ({elems, ...}: Ast.Exp.exp Ast.Exp.fvalbind)
          : SourceAst.Exp.exp SourceAst.Exp.fvalbind =
        { elems = Seq.map
            (fn {elems, ...} =>
              { elems = Seq.map
                  (fn {fname_args, ty, exp, ...} =>
                    { fname_args = conv_fname_args fname_args
                    , ty = Option.map (fn {ty, ...} => conv_ty ty) ty
                    , exp = conv_exp exp
                    })
                  elems
              })
            elems
        }

      and conv_exp (exp: Ast.Exp.exp) : SourceAst.Exp.exp =
        case exp of
          Ast.Exp.Const tok =>
            SourceAst.Exp.Const {id = nn (), value = tok_str tok}
        | Ast.Exp.Ident {opp, id} =>
            SourceAst.Exp.Ident
              { id = nn ()
              , has_op = Option.isSome opp
              , name = longid_of id
              }
        | Ast.Exp.Record {elems, ...} =>
            SourceAst.Exp.Record {id = nn (), elems = Seq.map conv_row_exp elems}
        | Ast.Exp.Select {label, ...} =>
            SourceAst.Exp.Select {id = nn (), label = tok_str label}
        | Ast.Exp.Unit _ =>
            SourceAst.Exp.Unit (nn ())
        | Ast.Exp.Tuple {elems, ...} =>
            SourceAst.Exp.Tuple {id = nn (), elems = Seq.map conv_exp elems}
        | Ast.Exp.List {elems, ...} =>
            SourceAst.Exp.List {id = nn (), elems = Seq.map conv_exp elems}
        | Ast.Exp.Sequence {elems, ...} =>
            SourceAst.Exp.Sequence {id = nn (), elems = Seq.map conv_exp elems}
        | Ast.Exp.LetInEnd {dec, exps, ...} =>
            SourceAst.Exp.LetInEnd
              { id = nn ()
              , dec = conv_dec dec
              , exps = Seq.map conv_exp exps
              }
        | Ast.Exp.Parens {exp, ...} => conv_exp exp
        | Ast.Exp.App {left, right} =>
            SourceAst.Exp.App
              { id = nn ()
              , left = conv_exp left
              , right = conv_exp right
              }
        | Ast.Exp.Infix {left, id, right} =>
            SourceAst.Exp.Infix
              { id = nn ()
              , left = conv_exp left
              , opr = tok_str id
              , right = conv_exp right
              }
        | Ast.Exp.Typed {exp, ty, ...} =>
            SourceAst.Exp.Typed {id = nn (), exp = conv_exp exp, ty = conv_ty ty}
        | Ast.Exp.Andalso {left, right, ...} =>
            SourceAst.Exp.Andalso
              { id = nn ()
              , left = conv_exp left
              , right = conv_exp right
              }
        | Ast.Exp.Orelse {left, right, ...} =>
            SourceAst.Exp.Orelse
              { id = nn ()
              , left = conv_exp left
              , right = conv_exp right
              }
        | Ast.Exp.Handle {exp, elems, ...} =>
            SourceAst.Exp.Handle
              { id = nn ()
              , exp = conv_exp exp
              , elems = Seq.map
                  (fn {pat, exp, ...} => {pat = conv_pat pat, exp = conv_exp exp})
                  elems
              }
        | Ast.Exp.Raise {exp, ...} =>
            SourceAst.Exp.Raise {id = nn (), exp = conv_exp exp}
        | Ast.Exp.IfThenElse {exp1, exp2, exp3, ...} =>
            SourceAst.Exp.IfThenElse
              { id = nn ()
              , exp1 = conv_exp exp1
              , exp2 = conv_exp exp2
              , exp3 = conv_exp exp3
              }
        | Ast.Exp.While {exp1, exp2, ...} =>
            SourceAst.Exp.While
              { id = nn ()
              , exp1 = conv_exp exp1
              , exp2 = conv_exp exp2
              }
        | Ast.Exp.Case {exp, elems, ...} =>
            SourceAst.Exp.Case
              { id = nn ()
              , exp = conv_exp exp
              , elems = Seq.map
                  (fn {pat, exp, ...} => {pat = conv_pat pat, exp = conv_exp exp})
                  elems
              }
        | Ast.Exp.Fn {elems, ...} =>
            SourceAst.Exp.Fn
              { id = nn ()
              , elems = Seq.map
                  (fn {pat, exp, ...} => {pat = conv_pat pat, exp = conv_exp exp})
                  elems
              }
        | Ast.Exp.MLtonSpecific {directive, contents, ...} =>
            SourceAst.Exp.MLtonSpecific
              { id = nn ()
              , directive = tok_str directive
              , contents = Seq.map tok_str contents
              }

      and conv_dec (dec: Ast.Exp.dec) : SourceAst.Exp.dec =
        case dec of
          Ast.Exp.DecEmpty =>
            SourceAst.Exp.DecEmpty
        | Ast.Exp.DecVal {tyvars, elems, ...} =>
            SourceAst.Exp.DecVal
              { id = nn ()
              , tyvars = tyvars_of_ss tyvars
              , elems = Seq.map
                  (fn {recc, pat, exp, ...} =>
                    { is_rec = Option.isSome recc
                    , pat = conv_pat pat
                    , exp = conv_exp exp
                    })
                  elems
              }
        | Ast.Exp.DecFun {tyvars, fvalbind, ...} =>
            SourceAst.Exp.DecFun
              { id = nn ()
              , tyvars = tyvars_of_ss tyvars
              , fvalbind = conv_fvalbind fvalbind
              }
        | Ast.Exp.DecType {typbind, ...} =>
            SourceAst.Exp.DecType {id = nn (), typbind = conv_typbind typbind}
        | Ast.Exp.DecDatatype {datbind, withtypee, ...} =>
            SourceAst.Exp.DecDatatype
              { id = nn ()
              , datbind = conv_datbind datbind
              , withtypee = Option.map (fn {typbind, ...} => conv_typbind typbind) withtypee
              }
        | Ast.Exp.DecReplicateDatatype {left_id, right_id, ...} =>
            SourceAst.Exp.DecReplicateDatatype
              { id = nn ()
              , left_name = tok_str left_id
              , right_name = longid_of right_id
              }
        | Ast.Exp.DecAbstype {datbind, withtypee, dec, ...} =>
            SourceAst.Exp.DecAbstype
              { id = nn ()
              , datbind = conv_datbind datbind
              , withtypee = Option.map (fn {typbind, ...} => conv_typbind typbind) withtypee
              , dec = conv_dec dec
              }
        | Ast.Exp.DecException {elems, ...} =>
            SourceAst.Exp.DecException
              { id = nn ()
              , elems = Seq.map conv_exbind elems
              }
        | Ast.Exp.DecLocal {left_dec, right_dec, ...} =>
            SourceAst.Exp.DecLocal
              { id = nn ()
              , left_dec = conv_dec left_dec
              , right_dec = conv_dec right_dec
              }
        | Ast.Exp.DecOpen {elems, ...} =>
            SourceAst.Exp.DecOpen
              { id = nn ()
              , elems = Seq.map longid_of elems
              }
        | Ast.Exp.DecMultiple {elems, ...} =>
            SourceAst.Exp.DecMultiple
              { id = nn ()
              , elems = Seq.map conv_dec elems
              }
        | Ast.Exp.DecInfix {precedence, elems, ...} =>
            SourceAst.Exp.DecInfix
              { id = nn ()
              , precedence =
                  Option.map (fn tok => valOf (Int.fromString (tok_str tok))) precedence
              , elems = Seq.map tok_str elems
              }
        | Ast.Exp.DecInfixr {precedence, elems, ...} =>
            SourceAst.Exp.DecInfixr
              { id = nn ()
              , precedence =
                  Option.map (fn tok => valOf (Int.fromString (tok_str tok))) precedence
              , elems = Seq.map tok_str elems
              }
        | Ast.Exp.DecNonfix {elems, ...} =>
            SourceAst.Exp.DecNonfix
              { id = nn ()
              , elems = Seq.map tok_str elems
              }


      fun conv_sigexp (se: Ast.Sig.sigexp) : SourceAst.Sig.sigexp =
        case se of
          Ast.Sig.Ident tok =>
            SourceAst.Sig.Ident {id = nn (), name = tok_str tok}
        | Ast.Sig.Spec {spec, ...} =>
            SourceAst.Sig.Spec {id = nn (), spec = conv_spec spec}
        | Ast.Sig.WhereType {sigexp, elems} =>
            SourceAst.Sig.WhereType
              { id = nn ()
              , sigexp = conv_sigexp sigexp
              , elems = Seq.map
                  (fn {tyvars, tycon, ty, ...} =>
                    { tyvars = tyvars_of_ss tyvars
                    , tycon = longid_of tycon
                    , ty = conv_ty ty
                    })
                  elems
              }

      and conv_spec (spec: Ast.Sig.spec) : SourceAst.Sig.spec =
        case spec of
          Ast.Sig.EmptySpec => SourceAst.Sig.EmptySpec
        | Ast.Sig.Val {elems, ...} =>
            SourceAst.Sig.Val
              { id = nn ()
              , elems = Seq.map
                  (fn {vid, ty, ...} => {name = tok_str vid, ty = conv_ty ty})
                  elems
              }
        | Ast.Sig.Type {elems, ...} =>
            SourceAst.Sig.Type
              { id = nn ()
              , elems = Seq.map
                  (fn {tyvars, tycon} =>
                    {tyvars = tyvars_of_ss tyvars, tycon = tok_str tycon})
                  elems
              }
        | Ast.Sig.TypeAbbreviation {typbind, ...} =>
            SourceAst.Sig.TypeAbbreviation
              { id = nn ()
              , typbind = conv_typbind typbind
              }
        | Ast.Sig.Eqtype {elems, ...} =>
            SourceAst.Sig.Eqtype
              { id = nn ()
              , elems = Seq.map
                  (fn {tyvars, tycon} =>
                    {tyvars = tyvars_of_ss tyvars, tycon = tok_str tycon})
                  elems
              }
        | Ast.Sig.Datatype {elems, ...} =>
            SourceAst.Sig.Datatype
              { id = nn ()
              , elems = Seq.map
                  (fn {tyvars, tycon, elems, ...} =>
                    { tyvars = tyvars_of_ss tyvars
                    , tycon = tok_str tycon
                    , elems = Seq.map
                        (fn {vid, arg} =>
                          { name = tok_str vid
                          , arg = Option.map (fn {ty, ...} => conv_ty ty) arg
                          })
                        elems
                    })
                  elems
              }
        | Ast.Sig.ReplicateDatatype {left_id, right_id, ...} =>
            SourceAst.Sig.ReplicateDatatype
              { id = nn ()
              , left_id = tok_str left_id
              , right_id = longid_of right_id
              }
        | Ast.Sig.Exception {elems, ...} =>
            SourceAst.Sig.Exception
              { id = nn ()
              , elems = Seq.map
                  (fn {vid, arg} =>
                    { name = tok_str vid
                    , arg = Option.map (fn {ty, ...} => conv_ty ty) arg
                    })
                  elems
              }
        | Ast.Sig.Structure {elems, ...} =>
            SourceAst.Sig.Structure
              { id = nn ()
              , elems = Seq.map
                  (fn {id, sigexp, ...} =>
                    {name = tok_str id, sigexp = conv_sigexp sigexp})
                  elems
              }
        | Ast.Sig.Include {sigexp, ...} =>
            SourceAst.Sig.Include {id = nn (), sigexp = conv_sigexp sigexp}
        | Ast.Sig.IncludeIds {sigids, ...} =>
            SourceAst.Sig.IncludeIds {id = nn (), names = Seq.map tok_str sigids}
        | Ast.Sig.SharingType {spec, elems, ...} =>
            SourceAst.Sig.SharingType
              { id = nn ()
              , spec = conv_spec spec
              , elems = Seq.map longid_of elems
              }
        | Ast.Sig.Sharing {spec, elems, ...} =>
            SourceAst.Sig.Sharing
              { id = nn ()
              , spec = conv_spec spec
              , elems = Seq.map longid_of elems
              }
        | Ast.Sig.Multiple {elems, ...} =>
            SourceAst.Sig.Multiple
              { id = nn ()
              , elems = Seq.map conv_spec elems
              }

      fun conv_sigdec (sd: Ast.Sig.sigdec) : SourceAst.Sig.sigdec =
        case sd of
          Ast.Sig.Signature {elems, ...} =>
            SourceAst.Sig.Signature
              { id = nn ()
              , elems = Seq.map
                  (fn {ident, sigexp, ...} =>
                    {name = tok_str ident, sigexp = conv_sigexp sigexp})
                  elems
              }


      fun conv_strexp (se: Ast.Str.strexp) : SourceAst.Str.strexp =
        case se of
          Ast.Str.Ident mlt =>
            SourceAst.Str.Ident {id = nn (), name = longid_of mlt}
        | Ast.Str.Struct {strdec, ...} =>
            SourceAst.Str.Struct {id = nn (), strdec = conv_strdec strdec}
        | Ast.Str.Constraint {strexp, colon, sigexp} =>
            SourceAst.Str.Constraint
              { id = nn ()
              , strexp = conv_strexp strexp
              , is_opaque = tok_str colon = ":>"
              , sigexp = conv_sigexp sigexp
              }
        | Ast.Str.FunAppExp {funid, strexp, ...} =>
            SourceAst.Str.FunAppExp
              { id = nn ()
              , funid = tok_str funid
              , strexp = conv_strexp strexp
              }
        | Ast.Str.FunAppDec {funid, strdec, ...} =>
            SourceAst.Str.FunAppDec
              { id = nn ()
              , funid = tok_str funid
              , strdec = conv_strdec strdec
              }
        | Ast.Str.LetInEnd {strdec, strexp, ...} =>
            SourceAst.Str.LetInEnd
              { id = nn ()
              , strdec = conv_strdec strdec
              , strexp = conv_strexp strexp
              }

      and conv_strdec (sd: Ast.Str.strdec) : SourceAst.Str.strdec =
        case sd of
          Ast.Str.DecEmpty => SourceAst.Str.DecEmpty
        | Ast.Str.DecCore dec => SourceAst.Str.DecCore (conv_dec dec)
        | Ast.Str.DecStructure {elems, ...} =>
            SourceAst.Str.DecStructure
              { id = nn ()
              , elems = Seq.map
                  (fn {strid, constraint, strexp, ...} =>
                    { name = tok_str strid
                    , constraint = Option.map
                        (fn {colon, sigexp} =>
                          { is_opaque = tok_str colon = ":>"
                          , sigexp = conv_sigexp sigexp
                          })
                        constraint
                    , strexp = conv_strexp strexp
                    })
                  elems
              }
        | Ast.Str.DecMultiple {elems, ...} =>
            SourceAst.Str.DecMultiple
              { id = nn ()
              , elems = Seq.map conv_strdec elems
              }
        | Ast.Str.DecLocalInEnd {strdec1, strdec2, ...} =>
            SourceAst.Str.DecLocalInEnd
              { id = nn ()
              , strdec1 = conv_strdec strdec1
              , strdec2 = conv_strdec strdec2
              }
        | Ast.Str.MLtonOverload {prec, name, ty, elems, ...} =>
            SourceAst.Str.MLtonOverload
              { id = nn ()
              , prec = tok_str prec
              , name = tok_str name
              , ty = conv_ty ty
              , elems = Seq.map longid_of elems
              }


      fun conv_funarg (fa: Ast.Fun.funarg) : SourceAst.Fun.funarg =
        case fa of
          Ast.Fun.ArgIdent {strid, sigexp, ...} =>
            SourceAst.Fun.ArgIdent
              { id = nn ()
              , name = tok_str strid
              , sigexp = conv_sigexp sigexp
              }
        | Ast.Fun.ArgSpec spec =>
            SourceAst.Fun.ArgSpec {id = nn (), spec = conv_spec spec}

      fun conv_fundec (fd: Ast.Fun.fundec) : SourceAst.Fun.fundec =
        case fd of
          Ast.Fun.DecFunctor {elems, ...} =>
            SourceAst.Fun.DecFunctor
              { id = nn ()
              , elems = Seq.map
                  (fn {funid, funarg, constraint, strexp, ...} =>
                    { name = tok_str funid
                    , funarg = conv_funarg funarg
                    , constraint = Option.map
                        (fn {colon, sigexp} =>
                          { is_opaque = tok_str colon = ":>"
                          , sigexp = conv_sigexp sigexp
                          })
                        constraint
                    , strexp = conv_strexp strexp
                    })
                  elems
              }

      fun conv_topdec ({topdec, ...}) : SourceAst.topdec =
        case topdec of
          Ast.SigDec sd => SourceAst.SigDec (conv_sigdec sd)
        | Ast.StrDec sd => SourceAst.StrDec (conv_strdec sd)
        | Ast.FunDec fd => SourceAst.FunDec (conv_fundec fd)
        | Ast.TopExp {exp, ...} => SourceAst.TopExp {id = nn (), exp = conv_exp exp}

      val Ast.Ast topdecs = ast
    in
      SourceAst.SmlAst
        { id = nn ()
        , topdecs = Seq.map conv_topdec topdecs
        }
    end

end
