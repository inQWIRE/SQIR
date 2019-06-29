Require Import String.
Require Import Reals.
Require Import List.
Import ListNotations.

(* Representation of OpenQASM *)

Inductive mop : Set :=
| plus | minus | times | div.

Definition print_mop (m : mop) : string :=
  match m with
  | plus => "+"
  | minus => "-"
  | times => "*"
  | div => "/"
  end.

Inductive exp : Set :=
| e_nat : nat -> exp
| e_real : R -> exp
| e_pi : exp
| e_str : string -> exp
| e_mop : mop -> exp -> exp -> exp.

Definition nat_to_string (n : nat) : string :=
  match n with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
  | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
  end.

Fixpoint print_exp (e : exp) : string :=
  match e with
  | e_nat n => nat_to_string n
  | e_real r => "real number: to implement"
  | e_pi => "pi"
  | e_str s => s
  | e_mop m e1 e2 => print_exp e1 ++ print_mop m ++ print_exp e2
  end.

Inductive decl : Set :=
| qreg : nat -> nat -> decl
| creg : nat -> nat -> decl.

Definition print_decl (d : decl) : string :=
  match d with
  | qreg n m => "qreg q" ++ nat_to_string n ++ "[" ++ nat_to_string m ++ "]"
  | creg n m => "creg q" ++ nat_to_string n ++ "[" ++ nat_to_string m ++ "]"
  end.

Inductive qmem : Set :=
| qubit : nat -> qmem
| qlist : nat -> nat -> qmem.

Definition print_qmem (q : qmem) : string :=
  match q with
  | qubit n => "q" ++ nat_to_string n
  | qlist n m => "q" ++ nat_to_string n ++ "[" ++ nat_to_string m ++ "]"
  end.

Inductive cmem : Set :=
| cbit : nat -> cmem
| clist : nat -> nat -> cmem.

Definition print_cmem (c : cmem) : string :=
  match c with
  | cbit n => "c" ++ nat_to_string n
  | clist n m => "c" ++ nat_to_string n ++ "[" ++ nat_to_string m ++ "]"
  end.

Inductive unitary : Set :=
| u_U : list exp -> qmem -> unitary
| u_CX : qmem -> qmem -> unitary.


Fixpoint print_explist (exps : list exp) : string :=
  match exps with
  | [] => ""
  | e :: [] => print_exp e
  | e :: l => print_exp e ++ "," ++ print_explist l
  end.

Definition print_unitary (u : unitary) : string :=
  match u with
  | u_U l q => "U(" ++ print_explist l ++ ") " ++ print_qmem q
  | u_CX q1 q2 => "CX " ++ print_qmem q1 ++ ", " ++ print_qmem q2
  end.

Inductive op : Set :=
| o_app : unitary -> op
| o_meas : qmem -> cmem -> op
| o_if : cmem -> exp -> op -> op
| o_reset : qmem -> op.

Fixpoint print_op (o : op) : string :=
  match o with
  | o_app u => print_unitary u
  | o_meas q c => "measure " ++ print_qmem q ++ " -> " ++ print_cmem c
  | o_if c e o => "if(" ++ print_cmem c ++ "==" ++ print_exp e ++ ") " ++ print_op o
  | o_reset q => "reset " ++ print_qmem q
  end.

Inductive statement : Set :=
| s_decl : decl -> statement
| s_op : op -> statement
| s_err : string -> statement.

Definition print_statement (st : statement) : string :=
  match st with
  | s_decl d => print_decl d
  | s_op o => print_op o
  | s_err s => s
  end.

Definition program := list statement.

Definition newline := String (Ascii.ascii_of_N 10) EmptyString.

Fixpoint print_program (p : program) : string :=
  match p with
  | [] => ""
  | s :: [] => print_statement s
  | s :: p' => print_statement s ++ ";" ++ newline ++ print_program p'
  end.

Definition printer (p : program) : string :=
  "OPENQASM 2.0;" ++ newline ++ "include ""qelib1.inc"";" ++ newline ++ print_program p.


Require Import SQIRE.

Definition unitary_to_angle (u : Unitary 1) : list exp :=
  match u with
  | U_H => (e_mop div e_pi (e_nat 2)) :: (e_nat 0) :: [e_pi]
  | U_X => (e_pi) :: (e_nat 0) :: [e_pi]
  | U_Y => (e_pi) :: (e_mop div e_pi (e_nat 2)) :: [e_mop div e_pi (e_nat 2)]
  | U_Z => (e_nat 0) :: (e_nat 0) :: [e_pi]
  | U_R ϕ => (e_nat 0) :: (e_nat 0) :: [e_real ϕ]
  end.

Fixpoint decl_qregs (dim : nat) : program :=
  match dim with
  | O => []
  | S dim' => decl_qregs dim' ++ [s_decl (qreg dim' 1)]
  end.

Open Scope com.

Fixpoint com_to_qasm' {dim : nat} (c : com dim) : program :=
  match c with
  | skip => []
  | c1; c2 => com_to_qasm' c1 ++ com_to_qasm' c2
  | app1 u x  => let angle := unitary_to_angle u in 
                [s_op (o_app (u_U angle (qubit x)))]
  | app2 u x y => match u with 
                 | U_CNOT => [s_op (o_app (u_CX (qubit x) (qubit y)))]
                 | _ => [s_err "app2 error"]
                 end
  | meas x skip skip => [s_decl (creg x 1)] ++ [s_op (o_meas (qubit x) (cbit x))]
  | meas x _ _ => [s_err "classical control circuit not supported."]
  end.

Definition com_to_qasm {dim : nat} (c : com dim) : program :=
  decl_qregs dim ++ com_to_qasm' c.

Definition bell (a b : nat) : com 3 := H a ; CNOT a b.
Definition alice (q a : nat) : com 3 := CNOT q a ; H q ; measure q ; measure a.
Definition bob (q a b : nat) : com 3 := CNOT a b; CZ q b.
Definition teleport (q a b : nat) : com 3 := bell a b; alice q a; bob q a b.

Definition teleport_qasm := Eval compute in com_to_qasm (teleport 0 1 2).
Definition teleport_string := Eval compute in printer teleport_qasm. 
Print teleport_string.

Close Scope com.

Open Scope ucom.
Fixpoint ucom_to_qasm' {dim : nat} (c : ucom dim) : program :=
  match c with
  | uskip => []
  | c1; c2 => ucom_to_qasm' c1 ++ ucom_to_qasm' c2
  | uapp1 u x  => let angle := unitary_to_angle u in 
                [s_op (o_app (u_U angle (qubit x)))]
  | uapp2 u x y => match u with 
                 | U_CNOT => [s_op (o_app (u_CX (qubit x) (qubit y)))]
                 | _ => [s_err "app2 error"]
                 end
  end.

Definition ucom_to_qasm {dim : nat} (c : ucom dim) : program :=
  decl_qregs dim ++ ucom_to_qasm' c.

Require Import GHZ.

Definition ghz_qasm (n : nat) := Eval compute in ucom_to_qasm (GHZ n).
Compute (ghz_qasm 10).
Definition ghz_string (n : nat) := Eval compute in printer (ghz_qasm n).
Compute (ghz_string 10).

Close Scope ucom.

