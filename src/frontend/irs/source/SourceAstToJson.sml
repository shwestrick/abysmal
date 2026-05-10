(* Completely vibe-coded, not checked much.
 * Could be revisited for bugs and optimizations. *)
structure SourceAstToJson =
struct

  (* ===== JSON primitives ===== *)

  fun escape_str s =
    String.concatWith ""
      (List.map
         (fn #"\"" => "\\\""
           | #"\\" => "\\\\"
           | #"\n" => "\\n"
           | #"\r" => "\\r"
           | #"\t" => "\\t"
           | c => String.str c) (String.explode s))

  fun jstr s =
    "\"" ^ escape_str s ^ "\""
  fun jnum n = Int.toString n
  fun jbool b =
    if b then "true" else "false"
  fun jnull () = "null"
  fun jarray elems =
    "[" ^ String.concatWith "," elems ^ "]"
  fun jobj fields =
    "{"
    ^ String.concatWith "," (List.map (fn (k, v) => jstr k ^ ":" ^ v) fields)
    ^ "}"
  fun jopt f NONE = jnull ()
    | jopt f (SOME x) = f x
  fun jtag tag fields =
    jobj (("tag", jstr tag) :: fields)

  fun seq_to_list s =
    List.tabulate (Seq.length s, Seq.nth s)
  fun jseq f s =
    jarray (List.map f (seq_to_list s))

  fun json_id id = NodeID.toString id
  fun json_longid ids = jseq jstr ids

  (* ===== Ty ===== *)

  fun json_ty ty =
    case ty of
      SourceAst.Ty.Var {id, name} =>
        jtag "Var" [("id", json_id id), ("name", jstr name)]
    | SourceAst.Ty.Record {id, elems} =>
        jtag "Record"
          [ ("id", json_id id)
          , ( "elems"
            , jseq
                (fn {lab, ty} => jobj [("lab", jstr lab), ("ty", json_ty ty)])
                elems
            )
          ]
    | SourceAst.Ty.Tuple {id, elems} =>
        jtag "Tuple" [("id", json_id id), ("elems", jseq json_ty elems)]
    | SourceAst.Ty.Con {id, args, name} =>
        jtag "Con"
          [ ("id", json_id id)
          , ("args", jseq json_ty args)
          , ("name", json_longid name)
          ]
    | SourceAst.Ty.Arrow {id, from, to} =>
        jtag "Arrow"
          [("id", json_id id), ("from", json_ty from), ("to", json_ty to)]

  (* ===== Pat ===== *)

  fun json_patrow pr =
    case pr of
      SourceAst.Pat.DotDotDot id => jtag "DotDotDot" [("id", json_id id)]
    | SourceAst.Pat.LabEqPat {id, lab, pat} =>
        jtag "LabEqPat"
          [("id", json_id id), ("lab", jstr lab), ("pat", json_pat pat)]
    | SourceAst.Pat.LabAsPat {id, name, ty, aspat} =>
        jtag "LabAsPat"
          [ ("id", json_id id)
          , ("name", jstr name)
          , ("ty", jopt json_ty ty)
          , ("aspat", jopt json_pat aspat)
          ]

  and json_pat pat =
    case pat of
      SourceAst.Pat.Wild id => jtag "Wild" [("id", json_id id)]
    | SourceAst.Pat.Const {id, value} =>
        jtag "Const" [("id", json_id id), ("value", jstr value)]
    | SourceAst.Pat.Unit id => jtag "Unit" [("id", json_id id)]
    | SourceAst.Pat.Ident {id, has_op, name} =>
        jtag "Ident"
          [ ("id", json_id id)
          , ("has_op", jbool has_op)
          , ("name", json_longid name)
          ]
    | SourceAst.Pat.List {id, elems} =>
        jtag "List" [("id", json_id id), ("elems", jseq json_pat elems)]
    | SourceAst.Pat.Tuple {id, elems} =>
        jtag "Tuple" [("id", json_id id), ("elems", jseq json_pat elems)]
    | SourceAst.Pat.Record {id, elems} =>
        jtag "Record" [("id", json_id id), ("elems", jseq json_patrow elems)]
    | SourceAst.Pat.Con {id, has_op, name, atpat} =>
        jtag "Con"
          [ ("id", json_id id)
          , ("has_op", jbool has_op)
          , ("name", json_longid name)
          , ("atpat", json_pat atpat)
          ]
    | SourceAst.Pat.Infix {id, left, opr, right} =>
        jtag "Infix"
          [ ("id", json_id id)
          , ("left", json_pat left)
          , ("opr", jstr opr)
          , ("right", json_pat right)
          ]
    | SourceAst.Pat.Typed {id, pat, ty} =>
        jtag "Typed"
          [("id", json_id id), ("pat", json_pat pat), ("ty", json_ty ty)]
    | SourceAst.Pat.Layered {id, has_op, name, ty, pat} =>
        jtag "Layered"
          [ ("id", json_id id)
          , ("has_op", jbool has_op)
          , ("name", jstr name)
          , ("ty", jopt json_ty ty)
          , ("pat", json_pat pat)
          ]
    | SourceAst.Pat.Or {id, elems} =>
        jtag "Or" [("id", json_id id), ("elems", jseq json_pat elems)]

  (* ===== Exp helpers ===== *)

  fun json_typbind ({elems}: SourceAst.Exp.typbind) =
    jobj
      [( "elems"
       , jseq
           (fn {tyvars, tycon, ty} =>
              jobj
                [ ("tyvars", jseq jstr tyvars)
                , ("tycon", jstr tycon)
                , ("ty", json_ty ty)
                ]) elems
       )]

  fun json_datbind ({elems}: SourceAst.Exp.datbind) =
    jobj
      [( "elems"
       , jseq
           (fn {tyvars, tycon, elems} =>
              jobj
                [ ("tyvars", jseq jstr tyvars)
                , ("tycon", jstr tycon)
                , ( "elems"
                  , jseq
                      (fn {has_op, name, arg} =>
                         jobj
                           [ ("has_op", jbool has_op)
                           , ("name", jstr name)
                           , ("arg", jopt json_ty arg)
                           ]) elems
                  )
                ]) elems
       )]

  fun json_exbind eb =
    case eb of
      SourceAst.Exp.ExnNew {id, has_op, name, arg} =>
        jtag "ExnNew"
          [ ("id", json_id id)
          , ("has_op", jbool has_op)
          , ("name", jstr name)
          , ("arg", jopt json_ty arg)
          ]
    | SourceAst.Exp.ExnReplicate {id, has_op, left_name, right_name} =>
        jtag "ExnReplicate"
          [ ("id", json_id id)
          , ("has_op", jbool has_op)
          , ("left_name", jstr left_name)
          , ("right_name", json_longid right_name)
          ]

  fun json_row_exp json_e re =
    case re of
      SourceAst.Exp.RecordRow {id, lab, exp} =>
        jtag "RecordRow"
          [("id", json_id id), ("lab", jstr lab), ("exp", json_e exp)]
    | SourceAst.Exp.RecordPun {id, name} =>
        jtag "RecordPun" [("id", json_id id), ("name", jstr name)]

  fun json_fname_args fa =
    case fa of
      SourceAst.Exp.PrefixedFun {id, has_op, name, args} =>
        jtag "PrefixedFun"
          [ ("id", json_id id)
          , ("has_op", jbool has_op)
          , ("name", jstr name)
          , ("args", jseq json_pat args)
          ]
    | SourceAst.Exp.InfixedFun {id, larg, name, rarg} =>
        jtag "InfixedFun"
          [ ("id", json_id id)
          , ("larg", json_pat larg)
          , ("name", jstr name)
          , ("rarg", json_pat rarg)
          ]
    | SourceAst.Exp.CurriedInfixedFun {id, larg, name, rarg, args} =>
        jtag "CurriedInfixedFun"
          [ ("id", json_id id)
          , ("larg", json_pat larg)
          , ("name", jstr name)
          , ("rarg", json_pat rarg)
          , ("args", jseq json_pat args)
          ]

  fun json_fvalbind json_e ({elems}: 'e SourceAst.Exp.fvalbind) =
    jobj
      [( "elems"
       , jseq
           (fn {elems} =>
              jobj
                [( "elems"
                 , jseq
                     (fn {fname_args, ty, exp} =>
                        jobj
                          [ ("fname_args", json_fname_args fname_args)
                          , ("ty", jopt json_ty ty)
                          , ("exp", json_e exp)
                          ]) elems
                 )]) elems
       )]

  (* ===== Exp / Dec (mutually recursive) ===== *)

  fun json_exp e =
    case e of
      SourceAst.Exp.Const {id, value} =>
        jtag "Const" [("id", json_id id), ("value", jstr value)]
    | SourceAst.Exp.Ident {id, has_op, name} =>
        jtag "Ident"
          [ ("id", json_id id)
          , ("has_op", jbool has_op)
          , ("name", json_longid name)
          ]
    | SourceAst.Exp.Record {id, elems} =>
        jtag "Record"
          [("id", json_id id), ("elems", jseq (json_row_exp json_exp) elems)]
    | SourceAst.Exp.Select {id, label} =>
        jtag "Select" [("id", json_id id), ("label", jstr label)]
    | SourceAst.Exp.Unit id => jtag "Unit" [("id", json_id id)]
    | SourceAst.Exp.Tuple {id, elems} =>
        jtag "Tuple" [("id", json_id id), ("elems", jseq json_exp elems)]
    | SourceAst.Exp.List {id, elems} =>
        jtag "List" [("id", json_id id), ("elems", jseq json_exp elems)]
    | SourceAst.Exp.Sequence {id, elems} =>
        jtag "Sequence" [("id", json_id id), ("elems", jseq json_exp elems)]
    | SourceAst.Exp.LetInEnd {id, dec, exps} =>
        jtag "LetInEnd"
          [ ("id", json_id id)
          , ("dec", json_dec dec)
          , ("exps", jseq json_exp exps)
          ]
    | SourceAst.Exp.App {id, left, right} =>
        jtag "App"
          [ ("id", json_id id)
          , ("left", json_exp left)
          , ("right", json_exp right)
          ]
    | SourceAst.Exp.Infix {id, left, opr, right} =>
        jtag "Infix"
          [ ("id", json_id id)
          , ("left", json_exp left)
          , ("opr", jstr opr)
          , ("right", json_exp right)
          ]
    | SourceAst.Exp.Typed {id, exp, ty} =>
        jtag "Typed"
          [("id", json_id id), ("exp", json_exp exp), ("ty", json_ty ty)]
    | SourceAst.Exp.Andalso {id, left, right} =>
        jtag "Andalso"
          [ ("id", json_id id)
          , ("left", json_exp left)
          , ("right", json_exp right)
          ]
    | SourceAst.Exp.Orelse {id, left, right} =>
        jtag "Orelse"
          [ ("id", json_id id)
          , ("left", json_exp left)
          , ("right", json_exp right)
          ]
    | SourceAst.Exp.Handle {id, exp, elems} =>
        jtag "Handle"
          [ ("id", json_id id)
          , ("exp", json_exp exp)
          , ( "elems"
            , jseq
                (fn {pat, exp} =>
                   jobj [("pat", json_pat pat), ("exp", json_exp exp)]) elems
            )
          ]
    | SourceAst.Exp.Raise {id, exp} =>
        jtag "Raise" [("id", json_id id), ("exp", json_exp exp)]
    | SourceAst.Exp.IfThenElse {id, exp1, exp2, exp3} =>
        jtag "IfThenElse"
          [ ("id", json_id id)
          , ("exp1", json_exp exp1)
          , ("exp2", json_exp exp2)
          , ("exp3", json_exp exp3)
          ]
    | SourceAst.Exp.While {id, exp1, exp2} =>
        jtag "While"
          [("id", json_id id), ("exp1", json_exp exp1), ("exp2", json_exp exp2)]
    | SourceAst.Exp.Case {id, exp, elems} =>
        jtag "Case"
          [ ("id", json_id id)
          , ("exp", json_exp exp)
          , ( "elems"
            , jseq
                (fn {pat, exp} =>
                   jobj [("pat", json_pat pat), ("exp", json_exp exp)]) elems
            )
          ]
    | SourceAst.Exp.Fn {id, elems} =>
        jtag "Fn"
          [ ("id", json_id id)
          , ( "elems"
            , jseq
                (fn {pat, exp} =>
                   jobj [("pat", json_pat pat), ("exp", json_exp exp)]) elems
            )
          ]
    | SourceAst.Exp.MLtonSpecific {id, directive, contents} =>
        jtag "MLtonSpecific"
          [ ("id", json_id id)
          , ("directive", jstr directive)
          , ("contents", jseq jstr contents)
          ]

  and json_dec d =
    case d of
      SourceAst.Exp.DecEmpty => jtag "DecEmpty" []
    | SourceAst.Exp.DecVal {id, tyvars, elems} =>
        jtag "DecVal"
          [ ("id", json_id id)
          , ("tyvars", jseq jstr tyvars)
          , ( "elems"
            , jseq
                (fn {is_rec, pat, exp} =>
                   jobj
                     [ ("is_rec", jbool is_rec)
                     , ("pat", json_pat pat)
                     , ("exp", json_exp exp)
                     ]) elems
            )
          ]
    | SourceAst.Exp.DecFun {id, tyvars, fvalbind} =>
        jtag "DecFun"
          [ ("id", json_id id)
          , ("tyvars", jseq jstr tyvars)
          , ("fvalbind", json_fvalbind json_exp fvalbind)
          ]
    | SourceAst.Exp.DecType {id, typbind} =>
        jtag "DecType" [("id", json_id id), ("typbind", json_typbind typbind)]
    | SourceAst.Exp.DecDatatype {id, datbind, withtypee} =>
        jtag "DecDatatype"
          [ ("id", json_id id)
          , ("datbind", json_datbind datbind)
          , ("withtypee", jopt json_typbind withtypee)
          ]
    | SourceAst.Exp.DecReplicateDatatype {id, left_name, right_name} =>
        jtag "DecReplicateDatatype"
          [ ("id", json_id id)
          , ("left_name", jstr left_name)
          , ("right_name", json_longid right_name)
          ]
    | SourceAst.Exp.DecAbstype {id, datbind, withtypee, dec} =>
        jtag "DecAbstype"
          [ ("id", json_id id)
          , ("datbind", json_datbind datbind)
          , ("withtypee", jopt json_typbind withtypee)
          , ("dec", json_dec dec)
          ]
    | SourceAst.Exp.DecException {id, elems} =>
        jtag "DecException"
          [("id", json_id id), ("elems", jseq json_exbind elems)]
    | SourceAst.Exp.DecLocal {id, left_dec, right_dec} =>
        jtag "DecLocal"
          [ ("id", json_id id)
          , ("left_dec", json_dec left_dec)
          , ("right_dec", json_dec right_dec)
          ]
    | SourceAst.Exp.DecOpen {id, elems} =>
        jtag "DecOpen" [("id", json_id id), ("elems", jseq json_longid elems)]
    | SourceAst.Exp.DecMultiple {id, elems} =>
        jtag "DecMultiple" [("id", json_id id), ("elems", jseq json_dec elems)]
    | SourceAst.Exp.DecInfix {id, precedence, elems} =>
        jtag "DecInfix"
          [ ("id", json_id id)
          , ("precedence", jopt jnum precedence)
          , ("elems", jseq jstr elems)
          ]
    | SourceAst.Exp.DecInfixr {id, precedence, elems} =>
        jtag "DecInfixr"
          [ ("id", json_id id)
          , ("precedence", jopt jnum precedence)
          , ("elems", jseq jstr elems)
          ]
    | SourceAst.Exp.DecNonfix {id, elems} =>
        jtag "DecNonfix" [("id", json_id id), ("elems", jseq jstr elems)]

  (* ===== Sig (sigexp / spec mutually recursive) ===== *)

  fun json_sigexp se =
    case se of
      SourceAst.Sig.Ident {id, name} =>
        jtag "Ident" [("id", json_id id), ("name", jstr name)]
    | SourceAst.Sig.Spec {id, spec} =>
        jtag "Spec" [("id", json_id id), ("spec", json_spec spec)]
    | SourceAst.Sig.WhereType {id, sigexp, elems} =>
        jtag "WhereType"
          [ ("id", json_id id)
          , ("sigexp", json_sigexp sigexp)
          , ( "elems"
            , jseq
                (fn {tyvars, tycon, ty} =>
                   jobj
                     [ ("tyvars", jseq jstr tyvars)
                     , ("tycon", json_longid tycon)
                     , ("ty", json_ty ty)
                     ]) elems
            )
          ]

  and json_spec sp =
    case sp of
      SourceAst.Sig.EmptySpec => jtag "EmptySpec" []
    | SourceAst.Sig.Val {id, elems} =>
        jtag "Val"
          [ ("id", json_id id)
          , ( "elems"
            , jseq
                (fn {name, ty} => jobj [("name", jstr name), ("ty", json_ty ty)])
                elems
            )
          ]
    | SourceAst.Sig.Type {id, elems} =>
        jtag "Type"
          [ ("id", json_id id)
          , ( "elems"
            , jseq
                (fn {tyvars, tycon} =>
                   jobj [("tyvars", jseq jstr tyvars), ("tycon", jstr tycon)])
                elems
            )
          ]
    | SourceAst.Sig.TypeAbbreviation {id, typbind} =>
        jtag "TypeAbbreviation"
          [("id", json_id id), ("typbind", json_typbind typbind)]
    | SourceAst.Sig.Eqtype {id, elems} =>
        jtag "Eqtype"
          [ ("id", json_id id)
          , ( "elems"
            , jseq
                (fn {tyvars, tycon} =>
                   jobj [("tyvars", jseq jstr tyvars), ("tycon", jstr tycon)])
                elems
            )
          ]
    | SourceAst.Sig.Datatype {id, elems} =>
        jtag "Datatype"
          [ ("id", json_id id)
          , ( "elems"
            , jseq
                (fn {tyvars, tycon, elems} =>
                   jobj
                     [ ("tyvars", jseq jstr tyvars)
                     , ("tycon", jstr tycon)
                     , ( "elems"
                       , jseq
                           (fn {name, arg} =>
                              jobj
                                [("name", jstr name), ("arg", jopt json_ty arg)])
                           elems
                       )
                     ]) elems
            )
          ]
    | SourceAst.Sig.ReplicateDatatype {id, left_id, right_id} =>
        jtag "ReplicateDatatype"
          [ ("id", json_id id)
          , ("left_id", jstr left_id)
          , ("right_id", json_longid right_id)
          ]
    | SourceAst.Sig.Exception {id, elems} =>
        jtag "Exception"
          [ ("id", json_id id)
          , ( "elems"
            , jseq
                (fn {name, arg} =>
                   jobj [("name", jstr name), ("arg", jopt json_ty arg)]) elems
            )
          ]
    | SourceAst.Sig.Structure {id, elems} =>
        jtag "Structure"
          [ ("id", json_id id)
          , ( "elems"
            , jseq
                (fn {name, sigexp} =>
                   jobj [("name", jstr name), ("sigexp", json_sigexp sigexp)])
                elems
            )
          ]
    | SourceAst.Sig.Include {id, sigexp} =>
        jtag "Include" [("id", json_id id), ("sigexp", json_sigexp sigexp)]
    | SourceAst.Sig.IncludeIds {id, names} =>
        jtag "IncludeIds" [("id", json_id id), ("names", jseq jstr names)]
    | SourceAst.Sig.SharingType {id, spec, elems} =>
        jtag "SharingType"
          [ ("id", json_id id)
          , ("spec", json_spec spec)
          , ("elems", jseq json_longid elems)
          ]
    | SourceAst.Sig.Sharing {id, spec, elems} =>
        jtag "Sharing"
          [ ("id", json_id id)
          , ("spec", json_spec spec)
          , ("elems", jseq json_longid elems)
          ]
    | SourceAst.Sig.Multiple {id, elems} =>
        jtag "Multiple" [("id", json_id id), ("elems", jseq json_spec elems)]

  fun json_sigdec (SourceAst.Sig.Signature {id, elems}) =
    jtag "Signature"
      [ ("id", json_id id)
      , ( "elems"
        , jseq
            (fn {name, sigexp} =>
               jobj [("name", jstr name), ("sigexp", json_sigexp sigexp)]) elems
        )
      ]

  (* ===== Str (strexp / strdec mutually recursive) ===== *)

  fun json_constraint c =
    jobj
      [("is_opaque", jbool (#is_opaque c)), ("sigexp", json_sigexp (#sigexp c))]

  fun json_strexp se =
    case se of
      SourceAst.Str.Ident {id, name} =>
        jtag "Ident" [("id", json_id id), ("name", json_longid name)]
    | SourceAst.Str.Struct {id, strdec} =>
        jtag "Struct" [("id", json_id id), ("strdec", json_strdec strdec)]
    | SourceAst.Str.Constraint {id, strexp, is_opaque, sigexp} =>
        jtag "Constraint"
          [ ("id", json_id id)
          , ("strexp", json_strexp strexp)
          , ("is_opaque", jbool is_opaque)
          , ("sigexp", json_sigexp sigexp)
          ]
    | SourceAst.Str.FunAppExp {id, funid, strexp} =>
        jtag "FunAppExp"
          [ ("id", json_id id)
          , ("funid", jstr funid)
          , ("strexp", json_strexp strexp)
          ]
    | SourceAst.Str.FunAppDec {id, funid, strdec} =>
        jtag "FunAppDec"
          [ ("id", json_id id)
          , ("funid", jstr funid)
          , ("strdec", json_strdec strdec)
          ]
    | SourceAst.Str.LetInEnd {id, strdec, strexp} =>
        jtag "LetInEnd"
          [ ("id", json_id id)
          , ("strdec", json_strdec strdec)
          , ("strexp", json_strexp strexp)
          ]

  and json_strdec sd =
    case sd of
      SourceAst.Str.DecEmpty => jtag "DecEmpty" []
    | SourceAst.Str.DecCore dec => jtag "DecCore" [("dec", json_dec dec)]
    | SourceAst.Str.DecStructure {id, elems} =>
        jtag "DecStructure"
          [ ("id", json_id id)
          , ( "elems"
            , jseq
                (fn {name, constraint, strexp} =>
                   jobj
                     [ ("name", jstr name)
                     , ("constraint", jopt json_constraint constraint)
                     , ("strexp", json_strexp strexp)
                     ]) elems
            )
          ]
    | SourceAst.Str.DecMultiple {id, elems} =>
        jtag "DecMultiple"
          [("id", json_id id), ("elems", jseq json_strdec elems)]
    | SourceAst.Str.DecLocalInEnd {id, strdec1, strdec2} =>
        jtag "DecLocalInEnd"
          [ ("id", json_id id)
          , ("strdec1", json_strdec strdec1)
          , ("strdec2", json_strdec strdec2)
          ]
    | SourceAst.Str.MLtonOverload {id, prec, name, ty, elems} =>
        jtag "MLtonOverload"
          [ ("id", json_id id)
          , ("prec", jstr prec)
          , ("name", jstr name)
          , ("ty", json_ty ty)
          , ("elems", jseq json_longid elems)
          ]

  (* ===== Fun ===== *)

  fun json_funarg fa =
    case fa of
      SourceAst.Fun.ArgIdent {id, name, sigexp} =>
        jtag "ArgIdent"
          [ ("id", json_id id)
          , ("name", jstr name)
          , ("sigexp", json_sigexp sigexp)
          ]
    | SourceAst.Fun.ArgSpec {id, spec} =>
        jtag "ArgSpec" [("id", json_id id), ("spec", json_spec spec)]

  fun json_fundec (SourceAst.Fun.DecFunctor {id, elems}) =
    jtag "DecFunctor"
      [ ("id", json_id id)
      , ( "elems"
        , jseq
            (fn {name, funarg, constraint, strexp} =>
               jobj
                 [ ("name", jstr name)
                 , ("funarg", json_funarg funarg)
                 , ("constraint", jopt json_constraint constraint)
                 , ("strexp", json_strexp strexp)
                 ]) elems
        )
      ]

  (* ===== Top-level SML ===== *)

  fun json_topdec td =
    case td of
      SourceAst.SigDec sigdec => jtag "SigDec" [("sigdec", json_sigdec sigdec)]
    | SourceAst.StrDec strdec => jtag "StrDec" [("strdec", json_strdec strdec)]
    | SourceAst.FunDec fundec => jtag "FunDec" [("fundec", json_fundec fundec)]
    | SourceAst.TopExp {id, exp} =>
        jtag "TopExp" [("id", json_id id), ("exp", json_exp exp)]

  fun json_sml_ast (SourceAst.SmlAst {id, topdecs}) =
    jobj [("id", json_id id), ("topdecs", jseq json_topdec topdecs)]

  (* ===== MLB (basexp / basdec mutually recursive) ===== *)

  fun json_basexp be =
    case be of
      SourceAst.Mlb.Ident {id, name} =>
        jtag "Ident" [("id", json_id id), ("name", jstr name)]
    | SourceAst.Mlb.LetInEnd {id, basdec, basexp} =>
        jtag "LetInEnd"
          [ ("id", json_id id)
          , ("basdec", json_basdec basdec)
          , ("basexp", json_basexp basexp)
          ]
    | SourceAst.Mlb.BasEnd {id, basdec} =>
        jtag "BasEnd" [("id", json_id id), ("basdec", json_basdec basdec)]

  and json_basdec bd =
    case bd of
      SourceAst.Mlb.DecEmpty => jtag "DecEmpty" []
    | SourceAst.Mlb.DecMultiple {id, elems} =>
        jtag "DecMultiple"
          [("id", json_id id), ("elems", jseq json_basdec elems)]
    | SourceAst.Mlb.DecRef {id, name} =>
        jtag "DecRef" [("id", json_id id), ("name", jstr name)]
    | SourceAst.Mlb.DecSml {id, sml} =>
        jtag "DecSml" [("id", json_id id), ("sml", json_sml_ast sml)]
    | SourceAst.Mlb.DecBasis {id, elems} =>
        jtag "DecBasis"
          [ ("id", json_id id)
          , ( "elems"
            , jseq
                (fn {name, basexp} =>
                   jobj [("name", jstr name), ("basexp", json_basexp basexp)])
                elems
            )
          ]
    | SourceAst.Mlb.DecLocalInEnd {id, basdec1, basdec2} =>
        jtag "DecLocalInEnd"
          [ ("id", json_id id)
          , ("basdec1", json_basdec basdec1)
          , ("basdec2", json_basdec basdec2)
          ]
    | SourceAst.Mlb.DecOpen {id, elems} =>
        jtag "DecOpen" [("id", json_id id), ("elems", jseq jstr elems)]
    | SourceAst.Mlb.DecStructure {id, elems} =>
        jtag "DecStructure"
          [ ("id", json_id id)
          , ( "elems"
            , jseq
                (fn {name, alias} =>
                   jobj [("name", jstr name), ("alias", jopt jstr alias)]) elems
            )
          ]
    | SourceAst.Mlb.DecSignature {id, elems} =>
        jtag "DecSignature"
          [ ("id", json_id id)
          , ( "elems"
            , jseq
                (fn {name, alias} =>
                   jobj [("name", jstr name), ("alias", jopt jstr alias)]) elems
            )
          ]
    | SourceAst.Mlb.DecFunctor {id, elems} =>
        jtag "DecFunctor"
          [ ("id", json_id id)
          , ( "elems"
            , jseq
                (fn {name, alias} =>
                   jobj [("name", jstr name), ("alias", jopt jstr alias)]) elems
            )
          ]
    | SourceAst.Mlb.DecAnn {id, annotations, basdec} =>
        jtag "DecAnn"
          [ ("id", json_id id)
          , ("annotations", jseq jstr annotations)
          , ("basdec", json_basdec basdec)
          ]
    | SourceAst.Mlb.DecUnderscorePrim id =>
        jtag "DecUnderscorePrim" [("id", json_id id)]

  (* ===== Program / top-level ===== *)

  fun json_program (SourceAst.Program {bases, main}) =
    jobj
      [ ( "bases"
        , jseq
            (fn {name, id, basdec} =>
               jobj
                 [ ("name", jstr name)
                 , ("id", json_id id)
                 , ("basdec", json_basdec basdec)
                 ]) bases
        )
      , ("main", json_basdec main)
      ]

  fun to_json (ast: SourceAst.t) : string =
    case ast of
      SourceAst.Sml sml_ast => jtag "Sml" [("sml", json_sml_ast sml_ast)]
    | SourceAst.Mlb program => jtag "Mlb" [("program", json_program program)]

end
