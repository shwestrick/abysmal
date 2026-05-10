structure Parser:
sig
  val parse_sml: Source.t -> Ast.t
  val parse_sml_with_infdict: InfixDict.t -> Source.t -> InfixDict.t * Ast.t
  val parse_mlb: Source.t -> MLBAst.t
end =
struct
  val allows = AstAllows.make
    { topExp = true
    , optBar = true
    , recordPun = true
    , orPat = true
    , extendedText = true
    , sigWithtype = true
    }

  fun parse_sml_with_infdict infdict src =
    case SMLFmtParser.parseWithInfdict allows infdict (Lexer.tokens allows src) of
      (infdict', SMLFmtParser.Ast ast) => (infdict', ast)
    | (infdict', SMLFmtParser.JustComments _) => (infdict', Ast.empty)

  fun parse_sml src =
    #2 (parse_sml_with_infdict InfixDict.initialTopLevel src)

  val parse_mlb = MLBParser.parse
end
