open OQAST

let parse f =
  let lexbuf = Lexing.from_channel (open_in f) in
  while true do
    let result = OQParser.mainprogram OQLexer.token lexbuf in
      print_endline (show_program result); print_newline(); flush stdout
  done
