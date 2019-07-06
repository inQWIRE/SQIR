{
  open Qparser
}

rule token = parse
| [ ' ' '\t' '\n' '"' ] { token lexbuf } (* escape spaces *)
| "QGate" { QG }
| "[" { LB }
| "]" { RB }
| "(" { LP }
| ")" { RP }
| "with controls" { WC }
| "with nocontrol" { WN }
| "=" { EQ }
| "+" { PLS }
| ":" { CLN }
| "," { CMA }
| "H" { H }
| "Z" { Z }
| "not" { X }
| "Qbit" { QB }
| "Cbit" { CB }
| "Inputs" { IN }
| "Outputs" { OUT }
| ['0'-'9']['0'-'9']* as str { ID(int_of_string(str)) }
| eof { EOF }
| _ as chr { failwith ("lex error: "^(Char.escaped chr))}
