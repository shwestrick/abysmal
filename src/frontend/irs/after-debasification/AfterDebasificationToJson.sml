structure AfterDebasificationToJson =
struct

  open SourceAstToJson

  fun to_json (AfterDebasification.Program {id, topdecs}) =
    jobj [("id", json_id id), ("topdecs", jseq json_topdec topdecs)]

end
