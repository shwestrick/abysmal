structure TCS = TerminalColorString

fun handleError exn =
  let
    val e =
      case exn of
        Error.Error e => e
      | other => raise other
    val hist = ExnHistory.history exn
  in
    TCS.printErr
      (Error.show {highlighter = SOME SyntaxHighlighter.fuzzyHighlight} e);
    if List.null hist then ()
    else
      TextIO.output
        ( TextIO.stdErr
        , "\n" ^ String.concat (List.map (fn ln => ln ^ "\n") hist)
        );
    OS.Process.exit OS.Process.failure
  end

val inputfile =
  case CommandLineArgs.positional () of
    [f] => f
  | _ =>
      ( TextIO.output (TextIO.stdErr, "usage: abysmal FILE\n")
      ; OS.Process.exit OS.Process.failure
      )

val filepath = FilePath.fromUnixPath inputfile

val source =
  Source.loadFromFile filepath
  handle exn =>
    ( TextIO.output (TextIO.stdErr, "error: " ^ exnMessage exn ^ "\n")
    ; OS.Process.exit OS.Process.failure
    )

fun parse_sml_standalone src =
  SourceAst.Sml
    (ToSourceAstSML.convert (fn _ => NodeID.fresh ()) src (Parser.parse_sml src))

val source_ast =
  (case OS.Path.ext inputfile of
    SOME "mlb" =>
      #1 (ToSourceAst.to_source_ast_mlb source (Parser.parse_mlb source))
  | SOME "sml" => parse_sml_standalone source
  | SOME "sig" => parse_sml_standalone source
  | SOME "fun" => parse_sml_standalone source
  | _ =>
      ( TextIO.output
          ( TextIO.stdErr
          , "error: unrecognized file extension: " ^ inputfile ^ "\n"
          )
      ; OS.Process.exit OS.Process.failure
      ))
  handle exn => handleError exn

val _ = print (SourceAstToJson.to_json source_ast ^ "\n")
