{
open Lexing
open OQParser

exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }
}

let digit   = ['0'-'9']
let exp = ['e' 'E'] ['-' '+']? digit+

let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let id = ['a'-'z'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let real = (digit+'.'digit* | digit*'.'digit+) exp?
let nninteger = (['1'-'9']+digit*) | '0'

rule token =
  parse
  | "OPENQASM"  { OPENQASM }

  | ';'         { SEMICOLON }
  | ','         { COMMA }
  | "=="        { EQUALS }
  | "->"        { ARROW }

  | '{'         { LBRACE }
  | '}'         { RBRACE }
  | '('         { LPAREN }
  | ')'         { RPAREN }
  | '['         { LBRACKET }
  | ']'         { RBRACKET }

  (* | "opaque"    { OPAQUE } *)
  | "if"        { IF }
  (* | "barrier"   { BARRIER } *)

  | "qreg"      { QREG }
  | "creg"      { CREG }

  | "gate"      { GATE }

  | "measure"   { MEASURE }
  | "reset"     { RESET }

  | 'U'         { U }
  | "CX"        { CX }

  | "pi"        { PI }
  | '+'         { PLUS }
  | '-'         { MINUS }
  | '*'         { TIMES }
  | '/'         { DIV }
  | '^'         { POW }

  (* | "sin"       { SIN }
  | "cos"       { COS }
  | "tan"       { TAN }
  | "exp"       { EXP }
  | "ln"        { LN }
  | "sqrt"      { SQRT } *)

  | id          { ID (Lexing.lexeme lexbuf) }
  | real        { REAL (float_of_string (Lexing.lexeme lexbuf)) }
  | nninteger   { NINT (int_of_string (Lexing.lexeme lexbuf)) }

  (* Ignore whitespace, comments and include line *)
  | white                  { token lexbuf }
  | newline                { next_line lexbuf; token lexbuf }
  | "//" [^ '\010' '\013']* newline       { next_line lexbuf; token lexbuf }
  (* TODO maybe not ignore *)
  | "include " [^ '\010' '\013']* newline { next_line lexbuf; token lexbuf }

  | _   { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | eof { EOF }
