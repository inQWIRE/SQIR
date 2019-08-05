type binaryop  =
  | Plus
  | Minus
  | Times
  | Div
  | Pow
[@@deriving show]

type exp =
  | Real of float
  | Nninteger of int
  | Pi
  | Id of string
  | Binaryop of exp * binaryop * exp
  | UMinus of exp
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
  | Uop of uop
  | Barrier of string list
(* [@@deriving show] *)

type gatedecl = string * string list option * string list (* [@@deriving show] *)

type decl =
  | Qreg of string * int
  | Creg of string * int
(* [@@deriving show] *)

type statement  =
  | Decl of decl
  | GateDecl of gatedecl * gop list
  | OpaqueDecl of gatedecl
  | Qop of qop
  | If of string * int * qop
  | Barrier of argument list
(* [@@deriving show] *)

type program = statement list (* [@@deriving show] *)
