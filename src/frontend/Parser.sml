structure Parser:
sig
  val parse_sml: Source.t -> Ast.t
  val parse_mlb: Source.t -> MLBAst.t
end =
struct
  val allows = AstAllows.make
    { topExp = true
    , optBar = false
    , recordPun = false
    , orPat = false
    , extendedText = false
    , sigWithtype = false
    }

  fun parse_sml src =
    case SMLFmtParser.parse allows (Lexer.tokens allows src) of
      SMLFmtParser.Ast ast => ast
    | SMLFmtParser.JustComments _ => Ast.empty

  val parse_mlb = MLBParser.parse
end
