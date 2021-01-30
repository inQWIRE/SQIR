Require Import VectorStates UnitaryOps Coq.btauto.Btauto Strings.String.

(* The language for RCIR+, a target language for QLLVM to compile to. *)
Local Open Scope nat_scope.


(* We first define two types variables appearing in an expression.
    global variables and local variables. *)
Definition ivar := nat.

Definition evar := nat.

Inductive rtype := Q (n:nat).

Inductive avar := lvar : ivar -> avar | gvar : evar -> avar.

Definition avar_eq (r1 r2 : avar) : bool := 
                match r1 with lvar a1 
                            => match r2
                               with lvar a2
                                     => (a1 =? a2)
                                  | gvar a2 => false
                                 end
                     | (gvar a1) => match r2 with (gvar a2) => (a1 =? a2)
                                                   | (lvar a2) => false
                                       end
                end.

Notation "i '==?' j" := (avar_eq i j) (at level 50).

(* Define predicate for applying gates on different circuit. *)
(* all bound has the form nat * var + nat format. 
   single var is 1 * var + 0, a constant is 0 * var - nat. *)
Definition nvar := nat.

Inductive bound : Set := 
   | Br : nat -> nvar -> nat -> bound.

Inductive pred : Set :=
   | Unit : nat -> pred (* x = m * var + m for exactly one *)
   | Lt : nat -> pred (* x < m * var + m *)
   | Ge : nat -> pred (* x > m * var + m *)
   | Space : nat -> nat -> pred. (* forall x, x =  m * x + m for every one that sat the formula. *)

(*   | Rel : ivar -> ivar -> bound -> pred (* forall x, x := m * y + m *)
   | Pow : ivar -> bound -> pred (* x = 2 ^ bound *)
   | Fun : ivar -> (nat -> bool) -> pred (* forall x , f x *)
   | AnDiv : ivar -> nat -> bound -> pred (* Angle x = n * Pi / 2 ^ y  *)
   | Angle : ivar -> nat -> pred (* Angle x = n *)
   | Conj : pred -> pred -> pred. (* pred /\ pred *)*)


Definition eval_pred (x:nat) (p:pred) : Prop :=
   match p with 
                 | Unit n => (x = n)
                 | Lt n => (x < n)
                 | Ge n => (x >= n)
                 | Space n m => (exists y, x = n * y + m)
   end.

Definition neq_pred (x:nat) (p:pred) : Prop :=
   match p with 
                 | Unit n => (x <> n)
                 | Lt n => (x >= n)
                 | Ge n => (x < n)
                 | Space n m => (forall y, x <> n * y + m)
   end.


(* This is the expression in a function in the RCIR+ language. 
   It does not contain quantum gates. quantum gates will be foreign functions. *)
Inductive rexp :=
             | rskip : rexp | rx : (avar * pred) -> rexp | rcont : (avar * nat) -> rexp -> rexp 
     | rseq : rexp -> rexp -> rexp | copyto : avar -> avar -> rexp.

Definition regs := (avar -> option (rtype * (nat -> bool))).

(* well-formedness of a predicate based on the relation of
    the input dimension number and the specified predicate type and number. *)
Inductive WF_pred : nat -> pred -> Prop := 
  | WF_unit : forall n x, x < n -> WF_pred n (Unit x)
  | WF_lt : forall n x, x <= n -> WF_pred n (Lt x)
  | WF_ge : forall n x, x < n -> WF_pred n (Ge x)
  | WF_space : forall n x y, y < n -> WF_pred n (Space x y).


(* The following defines the well-formedness of an RCIR+ expression. 
   The well-formedness depends on an input register set. *)
Inductive WF_freeVar : avar -> nat -> rexp -> Prop := 
  | free_rskip : forall x n, WF_freeVar x n rskip
  | free_rx : forall x y p n , x <> y \/ (x = y /\ neq_pred n p) -> WF_freeVar x n (rx (y,p))
  | free_rcont : forall x y n m e, x <> y \/ (x = y /\ n <> m) -> WF_freeVar x n e -> WF_freeVar x n (rcont (y,m) e)
  | free_rseq : forall x n e1 e2, WF_freeVar x n e1 -> WF_freeVar x n e2 -> WF_freeVar x n (rseq e1 e2)
  | free_copy : forall x n y z, x <> y -> y <> z -> WF_freeVar x n (copyto y z).

Inductive WF_rexp : regs -> rexp -> Prop := 
  | WF_rskip : forall r, WF_rexp r rskip
  | WF_rx : forall r x n p g, 0 < n -> r x = Some (Q n, g) -> WF_pred n p -> WF_rexp r (rx (x,p))
  | WF_rcont : forall r x n p g e, 0 < n -> r x = Some (Q n, g) -> p < n -> WF_freeVar x p e -> WF_rexp r (rcont (x,p) e)
  | WF_rseq : forall r e1 e2,  WF_rexp r e1 -> WF_rexp r e2 -> WF_rexp r (rseq e1 e2)
  | WF_copy : forall r x y n m f g, 0 < n -> 0 < m -> r x = Some (Q n, g) -> r y = Some (Q m, f) -> n <= m -> WF_rexp r (copyto x y).

(* A RCIR+ function can be a function with a RCIR+ expression or a cast oeration,
    or a RCIR+ foreign expression that might contain quantum gates.
    The requirement of quantum foreign gates in RCIR+ is that the input of registers
    for the functions to be all 0/1 bits, while the output also contains only 0/1 bits. *)
Inductive rfun A :=
       Fun : (list (rtype * evar)) -> (list (rtype * ivar)) -> rexp -> rfun A
     | cast : rtype ->  evar -> rtype -> rfun A
     | foreign : (list (rtype * evar)) -> (list (rtype * ivar)) -> A -> rfun A.


(* The following defines the initialization of a register set for the expression in a function. *)
Definition allfalse := fun (_ : nat) => false.

Fixpoint gen_regs_evar (l : list (rtype * evar)) : regs := 
  match l with [] => (fun (_: avar) => None)
            | (Q n, x)::xl => 
               fun y => if y ==? gvar x then Some (Q n, allfalse) else gen_regs_evar xl y
  end.

Fixpoint gen_regs (l: list (rtype * ivar)) (r :regs) :=
   match l with [] => r
         | (Q n, x)::xl => 
             fun y => if y ==? lvar x then Some (Q n, allfalse) else gen_regs xl r y
   end.

(* The following defines the well-formedness of rfun that depends on an input register set
    having all variables being global variables. *)
Fixpoint type_match (l: list (rtype * evar)) (r : regs) : Prop :=
    match l with [] => True
          | (Q n, x)::xl => (match r (gvar x) with Some (Q m, f) => n = m | None => False end) /\  type_match xl r
    end.

(* Define the top level of the language. Every program is a list of global variable definitions plus a list of rfun functions. *)
Inductive rtop A := Prog : list (rtype * evar) -> list (rfun A) -> rtop A.


Definition update_type (f : regs) (i : avar) (x : rtype) :=
  fun y => if y ==? i then Some (x,allfalse) else f y.


(* The well-formedness of a program is based on a step by step type checking on the wellfi*)
Inductive WF_rfun_list {A} : regs -> list (rfun A) -> Prop :=
    | WF_empty : forall r, WF_rfun_list r []
    | WF_fun : forall r l1 l2 e fl, WF_rexp (gen_regs l2 (gen_regs_evar l1)) e -> type_match l1 r ->
                WF_rfun_list r fl -> WF_rfun_list r ((Fun A l1 l2 e)::fl)
    | WF_cast : forall r n m x g fl, r (gvar x) = Some (Q n, g) -> 0 < n -> 0 < m ->
            WF_rfun_list (update_type r (gvar x) (Q m)) fl -> WF_rfun_list r ((cast A (Q n) x (Q m))::fl).

Inductive WF_rtop {A} : rtop A -> Prop := 
    | WF_prog : forall l fl, WF_rfun_list (gen_regs_evar l) (fl) -> WF_rtop (Prog A l fl).

(*
Definition pos_eq (r1 r2 : pos) : bool := 
                match r1 with (lvar a1,b1) 
                            => match r2
                               with (lvar a2,b2)
                                     => (a1 =? a2) && (b1 =? b2)
                                  | (gvar a2,b2) => false
                                 end
                     | (gvar a1,b1) => match r2 with (gvar a2,b2) => (a1 =? a2) && (b1 =? b2)
                                                   | (lvar a2, b2) => false
                                       end
                end.


Notation "i '=pos' j" := (pos_eq i j) (at level 50).




Definition eupdate (f : regs) (x: pos) (v : bool) :=
 match x with (a,b) => 
  fun j => if j ==? a then (match f j with None => None
                                | Some (tv,gv) =>  Some (tv, nupdate gv b v) end) else f j
 end.

Notation "f '[' i '|->' x ']'" := (eupdate f i x) (at level 10).

Fixpoint gup {A} (f : nat -> A) (g : nat -> A) (n : nat) :=
  match n with 0 => f
             | S m => gup (update f m (g m)) g m
  end.

Definition pupdate (f : regs) (x: avar) (g: nat -> bool) :=
           fun j => if j ==? x then (match f j with None => None | Some (tv,gv) => Some (tv,g) end) else f j.
*)


(* The semantic definition of expressions for RCIR+ including some well-formedness requirement.
   TODO: need to split well-formedness requirement with RCIR+ semantics. 
Inductive estep : regs -> rexp -> regs -> Prop := 
  | skip_rule : forall r , estep r rskip r
  | x_rule : forall r x i n gv, r x = Some (Q n,gv) -> i < n -> estep r (rx (x,i)) (r [(x,i) |-> (¬ (gv i))])
  | if_rule1 : forall r x i n gv e r', r x = Some (Q n,gv) -> i < n -> gv i = true
                            -> estep r e r' -> estep r (rcont (x,i) e) r'
  | if_rule2 : forall r x i n gv e, r x = Some (Q n,gv) -> i < n -> gv i = false
                            -> estep r (rcont (x,i) e) r
  | seq_rule : forall r e1 e2 r' r'', estep r e1 r' -> estep r' e2 r'' -> estep r (rseq e1 e2) r''
  | copy_rule : forall r x n fv y m gv,  r x = Some (Q n, fv) -> r y = Some (Q m,gv)
               -> n <= m -> (forall i, 0 <= i < m -> gv i = false) 
        -> estep r (copyto x y) (pupdate r y (gup gv fv n)).



Inductive rtop := Define : list (rtype * evar) -> rtop
                               | Insts : rfun -> rtop.

    *)






