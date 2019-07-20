type exp =
  | Real of float
  | Nninteger of int
  | Pi
  | Id of string

type argument = string * int option

type uop  =
  | CX of argument * argument
  | H of argument
  | T of argument
  | Tdg of argument
  | U of exp list * argument
  | X of argument
  | Y of argument
  | Z of argument
  | Gate of string * exp list * argument list

type qop  =
  | Uop of uop
  | Meas of argument * argument
  | Reset of argument

type gop  =
  | Uop of uop

type gatedecl = string * string list option * string list

type decl =
  | Qreg of string * int
  | Creg of string * int

type statement  =
  | Decl of decl
  | GateDecl of gatedecl * gop list
  | Qop of qop
  | If of string * int * qop

type program = statement list
