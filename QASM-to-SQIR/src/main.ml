open OQAST

let _ =
  try
    let lexbuf = Lexing.from_channel stdin in
    while true do
      let result = OQParser.mainprogram OQLexer.token lexbuf in
        print_endline (show_program result); print_newline(); flush stdout
    done
  with OQLexer.Eof ->
    exit 0
