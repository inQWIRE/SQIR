Require Import String.
Require Import List.
Import ListNotations.
Open Scope string_scope.

(* Definition of 'extended SQIR' language, which is a step between SQIR 
   and high-level languages like Silq and Q#. *)

(** Abstract syntax **)

(* eSQIR expressions

   For now, this is just a lambda calculus w/ some nat and bool
   primitives. Note that Var and ArrVar may describe nats, bools,
   or indices into the quantum store. *)
Inductive exp : Type :=
  | Num     (n : nat)
  | Plus    (e1 e2 : exp)
  | Minus   (e1 e2 : exp)
  | Mult    (e1 e2 : exp)
  | BTrue
  | BFalse
  | Eq      (e1 e2 : exp)
  | Le      (e1 e2 : exp)
  | Not     (e : exp)
  | And     (e1 e2 : exp)
  | Var     (x : string)
  | ArrVar  (arr : string) (idx : exp) (* indexing into an array *)
  | Lam     (x : string) (e : exp)
  | App     (e1 e2 : exp).

(* Type for unitary gates -- do we want the dependent type? *)
Parameter gate : nat -> Set. 

(* eSQIR programs 
  
   Some notes:
   - Operations (OpDef, OpApp, OpAppRet) do not allow recursion.
   - Operations may return nats, bools, or arrays of nats or bools; they
     cannot return qubit variables as this would allow for renaming qubits
     (which leads to linearity issues). This means that any qubits allocated
     within an operation are out of scope after the operation.
   - We could add a While statment, but it's unclear how this should be
     translated to SQIR.
   - It's worthwhile to have arrays in the IR because we'll often want
     to pass n-qubit arrays as input to operations. *)
Inductive stmt : Type :=

  (* Standard constructs *)
  | Arr      (arr : string) (sz : exp)
  | Assn     (x : string) (e : exp)
  | Skip
  | Seq      (s1 s2 : stmt)
  | Repeat   (x : string) (bnd : exp) (body : stmt)
  | If       (b : exp) (s1 s2 : stmt)
  | OpDef    (op : string) (params : list string) (body : stmt)
  | OpApp    (op : string) (args : list exp)
  | OpAppRet (ret op : string) (args : list exp)
  | Ret      (x : string)

  (* Quantum extensions *)
  | Init     (qs : string) (sz : exp)
  | Gate     {n : nat} (g : gate n) (qs : list exp)
  | Meas     (x : string) (q : exp)
  | Oracle   (f : exp) (arg : string)
  | Control  (q : string) (s : stmt)
  | Adjoint  (s : stmt).

(** Examples **)

(* Assume a few gates for now. *)
Axiom H : gate 1.
Axiom X : gate 1.
Axiom Z : gate 1.
Axiom CNOT : gate 2.

(* Teleport

   def prepare-bell(a,b) := H a; CNOT a b
   def alice(q,a) := CNOT q a; H q
   def bob(q,a,b) := 
       x <- meas q;
       y <- meas a;
       if (x == 1) { X b };
       if (y == 1) { Z b }
   def teleport(q) := 
       init a; 
       init b; 
       prepare-bell(a,b);
       alice(q,a);
       bob(q,a,b) *)
Definition teleport :=
  Seq (OpDef "prepare-bell" ["a";"b"] 
        (Seq (Gate H [Var "a"]) (Gate CNOT [Var "a"; Var "b"])))
 (Seq (OpDef "alice" ["q";"a"]
        (Seq (Gate CNOT [Var "q"; Var "a"]) (Gate H [Var "q"])))
 (Seq (OpDef "bob" ["q";"a";"b"]
        (Seq (Meas "x" (Var "q")) 
        (Seq (Meas "y" (Var "a")) 
        (Seq (If (Eq (Var "x") (Num 1)) (Gate X [Var "b"]) Skip)
             (If (Eq (Var "y") (Num 1)) (Gate Z [Var "b"]) Skip)))))
 (OpDef "teleport" ["q"]
   (Seq (Init "a" (Num 1))
   (Seq (Init "b" (Num 1))
   (Seq (OpApp "prepare-bell" [Var "a"; Var "b"])
   (Seq (OpApp "alice" [Var "q"; Var "a"])
        (OpApp "bob" [Var "q"; Var "a"; Var "b"])))))))).

(* n-qubit GHZ 

   def ghz(n) :=
     init qs[n];
     H qs[0];
     for i upto n-1 { CNOT(qs[i],qs[i+1]) }
*)
Definition GHZ :=
  OpDef "ghz" ["n"]
   (Seq (Init "qs" (Var "n"))
   (Seq (Gate H [ArrVar "qs" (Num 0)])
   (Repeat "i" (Minus (Var "n") (Num 1))
     (Gate CNOT [ArrVar "qs" (Var "i"); ArrVar "qs" (Plus (Var "i") (Num 1))])))).

(** Typing **)

(* eSQIR types *)
Inductive ty : Type :=
  | Nat : ty
  | Bool : ty  
  | Qubit : ty
  | Array : ty -> nat -> ty
  | Arrow : ty -> ty -> ty
  | OpArrow : ty -> ty -> ty. 
(* ^ we probably want two arrow types, one for functions and one for operations *)

(* TODO: define typing relation; type checking function *)

(** Evaluation **)

(* Interpreter for expressions *)
Inductive value : Type :=
  | NatVal : nat -> value
  | BoolVal : bool -> value  
  | QubitVar : string -> value
  | ArrayVal : list value -> value
  | LambdaVal : string -> exp -> value.

Definition env_t := string -> option value.
Definition empty : env_t := fun _ => None.
Definition extend (env : env_t) (x : string) (v : value) :=
  fun y => if x =? y then Some v else env y.

(* TODO: steal a verified interpreter from Software Foundations *)
Fixpoint interp (e : exp) (env : env_t) fuel : option value :=
match fuel with
| O => None
| S n' =>
  match e with
  | Num n => Some (NatVal n)
  | Plus e1 e2 => 
      match interp e1 env n', interp e2 env n' with
      | Some (NatVal n1), Some (NatVal n2) => Some (NatVal (n1 + n2))
      | _, _ => None
      end 
  | Minus e1 e2 =>
      match interp e1 env n', interp e2 env n' with
      | Some (NatVal n1), Some (NatVal n2) => Some (NatVal (n1 - n2))
      | _, _ => None
      end 
  | Mult e1 e2 =>
      match interp e1 env n', interp e2 env n' with
      | Some (NatVal n1), Some (NatVal n2) => Some (NatVal (n1 * n2))
      | _, _ => None
      end 
  | BTrue => Some (BoolVal true)
  | BFalse => Some (BoolVal false)
  | Eq e1 e2 =>
      match interp e1 env n', interp e2 env n' with
      | Some (NatVal n1), Some (NatVal n2) => Some (BoolVal (Nat.eqb n1 n2))
      | _, _ => None
      end 
  | Le e1 e2 =>
      match interp e1 env n', interp e2 env n' with
      | Some (NatVal n1), Some (NatVal n2) => Some (BoolVal (Nat.leb n1 n2))
      | _, _ => None
      end
  | Not e =>
      match interp e env n' with
      | Some (BoolVal b) => Some (BoolVal (negb b))
      | _ => None
      end 
  | And e1 e2 =>
      match interp e1 env n', interp e2 env n' with
      | Some (BoolVal b1), Some (BoolVal b2) => Some (BoolVal (b1 && b2))
      | _, _ => None
      end 
  | Var x => env x
  | ArrVar arr idx => 
      match env arr, interp idx env n' with
      | Some (ArrayVal l), Some (NatVal n) => List.nth_error l n
      | _, _ => None
      end
  | Lam x e => Some (LambdaVal x e)
  | App e1 e2 => 
      match interp e1 env n', interp e2 env n' with
      | Some (LambdaVal x body), Some v => interp body (extend env x v) n'
      | _, _ => None
      end 
  end
end.

Eval vm_compute in interp (Plus (Num 1) (Num 2)) empty 100.
Eval vm_compute in interp (Plus (Num 1) (ArrVar "a" (Num 2))) (extend empty "a" (ArrayVal [NatVal 0; NatVal 1; NatVal 2])) 100.
Eval vm_compute in interp (App (Lam "x" (Plus (Num 1) (Var "x"))) (Var "y")) (extend empty "y" (NatVal 2)) 100.

(* Evaluation of statements will track four different states:
   1. env  - classical store used in interp
   2. lbls - operation definitions, possibly a special 'return' value
   3. qmap - mapping from qubit variables to indices in the denotation matrix
   4. mat  - density matrix representing the state of the quantum system 

Fixpoint eval p env lbls qmap mat :=
  match p with
  | Arr a sz => evaluate sz; add an array of size sz to env
  | Assn x e => evaluate e; add x to env
  | Seq s1 s2 => evaluate s1; evaluate s2
  | Repeat x bnd body => evaluate body bnd times (with different bindings for x)
  | If b s1 s2 => evaluate b; evaluate s1 or s2
  | OpDef op params body => add the operation defn to lbls
  | OpApp op args => lookup name in lbls; evaluate args; apply op to args
  | OpAppRet ret op args => apply op to args; store return value in ret
  | Ret x => store x in the return location
  | Init x sz => add x to qmap; update mat to mat ⊗ ∣0⟩⟨0∣ ⊗ ... ⊗ ∣0⟩⟨0∣
  | Gate g qs => lookup qs in qmap; update mat to (apply g qs × st × (apply g qs)†)
  | Meas x q => ???
  | Oracle f q => apply unitary describing f to qubits in q
  | Control q s => evaluate s; apply controlled version to mat
  | Adjoint s => evaluate s; apply adjoint to mat
*)

(** Conversion to SQIR **)

(* For conversion to SQIR we need to track:
   1. env - classical store used in interp
   2. lbls - operation definitions, possibly a special 'return' value
   3. qmap - mapping from qubit variables to indices in the denotation matrix

   Translation returns a SQIR term, as well as updated env and qmap.

Fixpoint eSQIR_to_SQIR p env lbls qmap :=
  match p with
  | Arr a sz => add a to env (SQIR no-op)
  | Assn x e => add x to env (SQIR no-op)
  | Seq s1 s2 => translate s1; translate s2
  | Repeat x bnd body => evaluate bnd; translate body; unroll loop iterations
  | If b s1 s2 => evaluate b; translate either s1 or s2
  | OpDef op params body => add defn to lbls (SQIR no-op)
  | OpApp op args => translate result of applying op to args
  | OpAppRet ret op args => translate result of applying op to args; store return value in ret
  | Ret x => store x in the return location
  | Init x sz => add x to qmap (SQIR no-op)
  | Gate g q => equivalent SQIR gate app
  | Meas x q => Meas q (translate w/ env where x is 0) (translate w/ env where x is 1)
  | Oracle f => use compile function from BooleanCompilation
  | Control q s => use control function from UnitaryOps
  | Adjoint s => use invert function from UnitaryOps

   Optimizations to keep in mind:
   * we will want to do 'partial' compilation that does not require advance
     knowledge of all classical values
   * we want to reduce qubit usage when possible - which eSQIR variables can
     be mapped to the same physical qubits? 
   * our 'LCR' optimization routine can be used to optimize loops with >2 iters.
*)