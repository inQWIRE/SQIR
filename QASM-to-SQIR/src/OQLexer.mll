{
  open OQParser
}

let numeric = ['0' - '9']
let letter =  ['a' - 'z' 'A' - 'Z']
let newline = ('\010' | '\013' | "\013\010")

rule token = parse
  | "qreg"    { QReg }
  | "creg"    { CReg }
  | "gate"    { Gate }
  | "pi"      { Pi }
  | "CX"|"cx" { CNOT }
  | "H"|"h"   { H }
  | "T"       { T } (* including t conflicts with def. of cu3 in std. library *)
  | "Tdg"     { Tdg }
  | "tdg"     { Tdg }
  | "U"       { U }
  | "X"|"x"   { X }
  | "Y"|"y"   { Y }
  | "Z"|"z"   { Z }
  | "->"      { Arrow }
  | "measure" { Measure }
  | "reset"   { Reset }
  | "["       { LBracket }
  | "]"       { RBracket }
  | "{"       { LBrace }
  | "}"       { RBrace }
  | "("       { LParen }
  | ")"       { RParen }
  | "+"       { Plus }
  | "-"       { Minus }
  | "*"       { Mult }
  | "/"       { Div }
  | "^"       { Pow }
  | "if"      { If }
  | "=="      { DEquals }
  | ";"       { SemiColon }
  | ","       { Comma }
  | eof       { EOF }
  | [ ' ' '\t' ] | newline                  { token lexbuf }
  | "//" [^ '\010' '\013']* newline         { token lexbuf }
  | "OPENQASM 2" [^ '\010' '\013']* newline { token lexbuf }
  | "include " [^ '\010' '\013']* newline   { token lexbuf }
  | letter (letter | numeric | "_")* as id  { ID id }
  | (['1'-'9']+ numeric*) | "0" as str      { NInt(int_of_string(str)) }
  | _ as chr { failwith ("lex error: "^(Char.escaped chr))}
