{
  open OQParser
}

let numeric = ['0' - '9']
let letter =  ['a' - 'z' 'A' - 'Z']

rule token = parse
  | "qreg"    { QReg }
  | "creg"    { CReg }
  | "gate"    { Gate }
  | "Pi"      { Pi }
  | "U"       { U }
  | "CX"      { CNOT }
  | "X"       { X }
  | "Y"       { Y }
  | "Z"       { Z }
  | "H"       { H }
  | "->"      { Arrow }
  | "measure" { Measure }
  | "reset"   { Reset }
  (* | "barrier" { Barrier } *)
  | "["       { LBracket }
  | "]"       { RBracket }
  | "{"       { LBrace }
  | "}"       { RBrace }
  | "("       { LParen }
  | ")"       { RParen }
  (* | "="       { Equal } *)
  | "+"       { Plus }
  | "-"       { Minus }
  | "*"       { Mult }
  | "/"       { Div }
  | ";"       { SemiColon }
  | ","       { Comma }
  | eof       { EOF }
  | [ ' ' '\t' '\n' ]                       { token lexbuf }
  | letter (letter | numeric | "_")* as id  { ID id }
  | numeric numeric* as str                 { Idx(int_of_string(str)) }
  | _ as chr { failwith ("lex error: "^(Char.escaped chr))}
