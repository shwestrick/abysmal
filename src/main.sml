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

val _ =
  case OS.Path.ext inputfile of
    SOME "sml" =>
      let val _ = Parser.parse_sml source
      in print ("parsed SML: " ^ inputfile ^ "\n")
      end
  | SOME "sig" =>
      let val _ = Parser.parse_sml source
      in print ("parsed SML: " ^ inputfile ^ "\n")
      end
  | SOME "fun" =>
      let val _ = Parser.parse_sml source
      in print ("parsed SML: " ^ inputfile ^ "\n")
      end
  | SOME "mlb" =>
      let val _ = Parser.parse_mlb source
      in print ("parsed MLB: " ^ inputfile ^ "\n")
      end
  | _ =>
      ( TextIO.output
          ( TextIO.stdErr
          , "error: unrecognized file extension: " ^ inputfile ^ "\n"
          )
      ; OS.Process.exit OS.Process.failure
      )
