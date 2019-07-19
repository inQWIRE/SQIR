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
  | "Pi"      { Pi }
  | "CX"      { CNOT }
  | "H"       { H }
  | "T"       { T }
  | "Tdg"     { Tdg }
  | "U"       { U }
  | "X"       { X }
  | "Y"       { Y }
  | "Z"       { Z }
  | "->"      { Arrow }
  | "measure" { Measure }
  | "reset"   { Reset }
  | "["       { LBracket }
  | "]"       { RBracket }
  | "{"       { LBrace }
  | "}"       { RBrace }
  | "("       { LParen }
  | ")"       { RParen }
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
