type id = string

type ty = TVal | TCReg of int | TQReg of int | TGate of int * int

type binaryop =
  | Plus
  | Minus
  | Times
  | Div
  | Pow

type unaryop =
  | Sin
  | Cos
  | Tan
  | Exp
  | Ln
  | Sqrt
  | UMinus

type exp =
  | Real of float
  | Nninteger of int
  | Pi
  | Id of id
  | BinaryOp of binaryop * exp * exp
  | UnaryOp of unaryop * exp

type argument = id * int option

type uop  =
  | CX of argument * argument
  | U of exp list * argument
  | Gate of id * exp list * argument list

type qop  =
  | Uop of uop
  | Meas of argument * argument
  | Reset of argument

type gop  =
  | GUop of uop
  | GBarrier of id list

type gatedecl = id * id list * id list

type decl =
  | QReg of id * int
  | CReg of id * int

type statement  =
  | Include of string
  | Decl of decl
  | GateDecl of gatedecl * gop list
  | OpaqueDecl of gatedecl
  | Qop of qop
  | If of id * int * qop
  | Barrier of argument list

type program = statement list
