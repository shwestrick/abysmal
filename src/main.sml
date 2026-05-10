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

val source_ast =
  case OS.Path.ext inputfile of
    SOME "mlb" =>
      #1 (ToSourceAst.to_source_ast_mlb source (Parser.parse_mlb source))
  | SOME "sml" =>
      ( TextIO.output (TextIO.stdErr, "error: SML-only input not yet supported\n")
      ; OS.Process.exit OS.Process.failure
      )
  | SOME "sig" =>
      ( TextIO.output (TextIO.stdErr, "error: SML-only input not yet supported\n")
      ; OS.Process.exit OS.Process.failure
      )
  | SOME "fun" =>
      ( TextIO.output (TextIO.stdErr, "error: SML-only input not yet supported\n")
      ; OS.Process.exit OS.Process.failure
      )
  | _ =>
      ( TextIO.output
          ( TextIO.stdErr
          , "error: unrecognized file extension: " ^ inputfile ^ "\n"
          )
      ; OS.Process.exit OS.Process.failure
      )

val _ = print (SourceAstToJson.to_json source_ast ^ "\n")
