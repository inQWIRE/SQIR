type binaryop =
  | Plus
  | Minus
  | Times
  | Div
  | Pow
[@@deriving show]

type unaryop =
  | Sin
  | Cos
  | Tan
  | Exp
  | Ln
  | Sqrt
  | UMinus
[@@deriving show]

type exp =
  | Real of float
  | Nninteger of int
  | Pi
  | Id of string
  | BinaryOp of binaryop * exp * exp
  | UnaryOp of unaryop * exp
[@@deriving show]

type argument = string * int option [@@deriving show]

type uop  =
  | CX of argument * argument
  | U of exp list * argument
  | Gate of string * exp list * argument list
[@@deriving show]

type qop  =
  | Uop of uop
  | Meas of argument * argument
  | Reset of argument
(* [@@deriving show] *)

type gop  =
  | GUop of uop
  | GBarrier of string list
(* [@@deriving show] *)

type gatedecl = string * string list * string list (* [@@deriving show] *)

type decl =
  | QReg of string * int
  | CReg of string * int
(* [@@deriving show] *)

type statement  =
  | Include of string
  | Decl of decl
  | GateDecl of gatedecl * gop list
  | OpaqueDecl of gatedecl
  | Qop of qop
  | If of string * int * qop
  | Barrier of argument list
(* [@@deriving show] *)

type program = statement list (* [@@deriving show] *)
