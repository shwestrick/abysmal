structure AfterSequenceElaboration =
struct

  type node_id = NodeID.t

  (** Long identifiers: qualifier path followed by name,
    * e.g. ["Foo", "Bar", "baz"] for Foo.Bar.baz
    *)
  type longid = string Seq.t


  (** =========================================================================
    * Types.
    *
    * Changes from AfterWhileElaboration: none.
    *)
  structure Ty =
  struct
    datatype ty =
      Var of {id: node_id, name: string}

    (** { lab: ty, ..., lab: ty } *)
    | Record of {id: node_id, elems: {lab: string, ty: ty} Seq.t}

    (** tyseq longtycon *)
    | Con of {id: node_id, args: ty Seq.t, name: longid}

    (** ty -> ty *)
    | Arrow of {id: node_id, from: ty, to: ty}

    type t = ty
  end


  (** =========================================================================
    * Patterns.
    *
    * Changes from AfterWhileElaboration: none.
    *)
  structure Pat =
  struct

    datatype patrow =
      DotDotDot of node_id

    | LabEqPat of {id: node_id, lab: string, pat: pat}


    and pat =
      Wild of node_id

    | Const of {id: node_id, value: string}

    (** longvid *)
    | Ident of {id: node_id, name: longid}

    (** [ pat, ..., pat ] *)
    | List of {id: node_id, elems: pat Seq.t}

    (** { patrow, ..., patrow } *)
    | Record of {id: node_id, elems: patrow Seq.t}

    (** longvid atpat *)
    | Con of {id: node_id, name: longid, atpat: pat}

    (** pat : ty *)
    | Typed of {id: node_id, pat: pat, ty: Ty.t}

    (** vid [:ty] as pat *)
    | Layered of {id: node_id, name: string, ty: Ty.t option, pat: pat}

    (** pat | pat | ... | pat  (SuccessorML) *)
    | Or of {id: node_id, elems: pat Seq.t}

    type t = pat
  end


  (** =========================================================================
    * Expressions and declarations.
    *
    * Changes from AfterWhileElaboration:
    *   - Sequence removed (rewritten to let val _ = ... in ... end)
    *   - LetInEnd.exps seq replaced by single exp
    *)
  structure Exp =
  struct

    (** tyvarseq tycon = ty [and ...] *)
    type typbind =
      {elems: {tyvars: string Seq.t, tycon: string, ty: Ty.t} Seq.t}

    (** tyvarseq tycon = conbind [and ...] *)
    type datbind =
      {elems:
         { tyvars: string Seq.t
         , tycon: string
         , elems: {name: string, arg: Ty.t option} Seq.t
         } Seq.t}

    datatype exbind =
      ExnNew of {id: node_id, name: string, arg: Ty.t option}

    | ExnReplicate of {id: node_id, left_name: string, right_name: longid}


    datatype 'exp row_exp = RecordRow of {id: node_id, lab: string, exp: 'exp}


    datatype exp =
      Const of {id: node_id, value: string}

    (** longvid *)
    | Ident of {id: node_id, name: longid}

    (** { lab = exp, ..., lab = exp } *)
    | Record of {id: node_id, elems: exp row_exp Seq.t}

    (** # label *)
    | Select of {id: node_id, label: string}

    (** [ exp, ..., exp ] *)
    | List of {id: node_id, elems: exp Seq.t}

    (** let dec in exp end *)
    | LetInEnd of {id: node_id, dec: dec, exp: exp}

    (** exp exp *)
    | App of {id: node_id, left: exp, right: exp}

    (** exp : ty *)
    | Typed of {id: node_id, exp: exp, ty: Ty.t}

    (** exp handle pat => exp [| ...] *)
    | Handle of {id: node_id, exp: exp, elems: {pat: Pat.t, exp: exp} Seq.t}

    (** raise exp *)
    | Raise of {id: node_id, exp: exp}

    (** case exp of pat => exp [| ...] *)
    | Case of {id: node_id, exp: exp, elems: {pat: Pat.t, exp: exp} Seq.t}

    (** fn pat => exp *)
    | Fn of {id: node_id, pat: Pat.t, exp: exp}

    (** _prim, _import, etc. *)
    | MLtonSpecific of {id: node_id, directive: string, contents: string Seq.t}


    and dec =
      DecEmpty

    (** val tyvarseq [rec] pat = exp [and ...] *)
    | DecVal of
        { id: node_id
        , tyvars: string Seq.t
        , elems: {is_rec: bool, pat: Pat.t, exp: exp} Seq.t
        }

    (** type tyvarseq tycon = ty [and ...] *)
    | DecType of {id: node_id, typbind: typbind}

    (** datatype datbind [withtype typbind] *)
    | DecDatatype of {id: node_id, datbind: datbind, withtypee: typbind option}

    (** datatype tycon = datatype longtycon *)
    | DecReplicateDatatype of
        {id: node_id, left_name: string, right_name: longid}

    (** abstype datbind [withtype typbind] with dec end *)
    | DecAbstype of
        {id: node_id, datbind: datbind, withtypee: typbind option, dec: dec}

    (** exception exbind [and ...] *)
    | DecException of {id: node_id, elems: exbind Seq.t}

    (** local dec in dec end *)
    | DecLocal of {id: node_id, left_dec: dec, right_dec: dec}

    (** open longstrid [longstrid ...] *)
    | DecOpen of {id: node_id, elems: longid Seq.t}

    (** dec [; dec ...] *)
    | DecMultiple of {id: node_id, elems: dec Seq.t}

    type t = exp
  end


  (** =========================================================================
    * Module Signatures.
    *)
  structure Sig =
  struct

    type typbind = Exp.typbind

    datatype spec =
      EmptySpec

    (** val vid : ty [and ...] *)
    | Val of {id: node_id, elems: {name: string, ty: Ty.t} Seq.t}

    (** type tyvarseq tycon [and ...] *)
    | Type of {id: node_id, elems: {tyvars: string Seq.t, tycon: string} Seq.t}

    | TypeAbbreviation of {id: node_id, typbind: typbind}

    (** eqtype tyvarseq tycon [and ...] *)
    | Eqtype of
        {id: node_id, elems: {tyvars: string Seq.t, tycon: string} Seq.t}

    (** datatype tyvarseq tycon = condesc [and ...] *)
    | Datatype of
        { id: node_id
        , elems:
            { tyvars: string Seq.t
            , tycon: string
            , elems: {name: string, arg: Ty.t option} Seq.t
            } Seq.t
        }

    (** datatype tycon = datatype longtycon *)
    | ReplicateDatatype of {id: node_id, left_id: string, right_id: longid}

    (** exception vid [of ty] [and ...] *)
    | Exception of {id: node_id, elems: {name: string, arg: Ty.t option} Seq.t}

    (** structure strid : sigexp [and ...] *)
    | Structure of {id: node_id, elems: {name: string, sigexp: sigexp} Seq.t}

    (** include sigexp *)
    | Include of {id: node_id, sigexp: sigexp}

    (** include sigid ... sigid *)
    | IncludeIds of {id: node_id, names: string Seq.t}

    (** spec sharing type longtycon = ... = longtycon *)
    | SharingType of {id: node_id, spec: spec, elems: longid Seq.t}

    (** spec sharing longstrid = ... = longstrid *)
    | Sharing of {id: node_id, spec: spec, elems: longid Seq.t}

    (** spec [; spec ...] *)
    | Multiple of {id: node_id, elems: spec Seq.t}


    and sigexp =
      Ident of {id: node_id, name: string}

    (** sig spec end *)
    | Spec of {id: node_id, spec: spec}

    (** sigexp where type tyvarseq tycon = ty [where type ...] *)
    | WhereType of
        { id: node_id
        , sigexp: sigexp
        , elems: {tyvars: string Seq.t, tycon: longid, ty: Ty.t} Seq.t
        }


    and sigdec =
      Signature of {id: node_id, elems: {name: string, sigexp: sigexp} Seq.t}

  end


  (** =========================================================================
    * Module Structures.
    *)
  structure Str =
  struct

    datatype strexp =
      Ident of {id: node_id, name: longid}

    (** struct strdec end *)
    | Struct of {id: node_id, strdec: strdec}

    (** strexp [: | :>] sigexp  (is_opaque distinguishes : from :>) *)
    | Constraint of
        {id: node_id, strexp: strexp, is_opaque: bool, sigexp: Sig.sigexp}

    (** funid ( strexp ) *)
    | FunAppExp of {id: node_id, funid: string, strexp: strexp}

    (** funid ( strdec ) *)
    | FunAppDec of {id: node_id, funid: string, strdec: strdec}

    (** let strdec in strexp end *)
    | LetInEnd of {id: node_id, strdec: strdec, strexp: strexp}


    and strdec =
      DecEmpty

    | DecCore of Exp.dec

    (** structure strid [constraint] = strexp [and ...] *)
    | DecStructure of
        { id: node_id
        , elems:
            { name: string
            , constraint: {is_opaque: bool, sigexp: Sig.sigexp} option
            , strexp: strexp
            } Seq.t
        }

    (** strdec [; strdec ...] *)
    | DecMultiple of {id: node_id, elems: strdec Seq.t}

    (** local strdec in strdec end *)
    | DecLocalInEnd of {id: node_id, strdec1: strdec, strdec2: strdec}

    (** _overload prec name : ty as longvid [and ...] *)
    | MLtonOverload of
        {id: node_id, prec: string, name: string, ty: Ty.t, elems: longid Seq.t}

  end


  (** =========================================================================
    * Module Functors.
    *)
  structure Fun =
  struct

    datatype funarg =
      ArgIdent of {id: node_id, name: string, sigexp: Sig.sigexp}
    | ArgSpec of {id: node_id, spec: Sig.spec}

    datatype fundec =
      DecFunctor of
        { id: node_id
        , elems:
            { name: string
            , funarg: funarg
            , constraint: {is_opaque: bool, sigexp: Sig.sigexp} option
            , strexp: Str.strexp
            } Seq.t
        }

  end


  (** =========================================================================
    * Top-level SML.
    *)
  datatype topdec =
    SigDec of Sig.sigdec
  | StrDec of Str.strdec
  | FunDec of Fun.fundec
  | TopExp of {id: node_id, exp: Exp.exp}

  datatype t = Program of {id: node_id, topdecs: topdec Seq.t}

end
