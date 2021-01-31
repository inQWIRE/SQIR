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

(* This is the expression in a function in the RCIR+ language. 
   It does not contain quantum gates. quantum gates will be foreign functions. *)
Definition pos : Type := (avar * nat).

Inductive rexp :=
             | Skip : rexp | X : pos -> rexp | CU : pos -> rexp -> rexp 
             | Seq : rexp -> rexp -> rexp | Copyto : avar -> avar -> rexp
             | Inv : rexp -> rexp.

Definition regs := (avar -> option (rtype * (nat -> bool))).

(* Defining the CNOT and CCX gate. *)
Definition CNOT (p1 p2 : pos) := CU p1 (X p2).

Definition CCX (p1 p2 p3 : pos) := CU p1 (CNOT p2 p3).


(* well-formedness of a predicate based on the relation of
    the input dimension number and the specified predicate type and number. *)

Inductive freevar_exp : avar -> nat -> rexp -> Prop := 
   freevar_skip : forall a n, freevar_exp a n Skip
 | freevar_x_eq : forall a x b, a <> b -> freevar_exp x b (X (x,a))
 | freevar_x_neq : forall a x b y, x <> y -> freevar_exp x b (X (y,a))
 | freevar_cont_eq : forall a x b e, a <> b -> freevar_exp x b e -> freevar_exp x b (CU (x,a) e)
 | freevar_cont_neq : forall a x y b e, x <> y -> freevar_exp x b e -> freevar_exp x b (CU (y,a) e)
 | freevar_seq : forall x a e1 e2, freevar_exp x a e1 -> freevar_exp x a e2 -> freevar_exp x a (Seq e1 e2)
 |  freevar_copyto : forall x n a b, freevar_exp x n (Copyto a b)
 | freevar_inv : forall x a e, freevar_exp x a e -> freevar_exp x a (Inv e).

Inductive WF_rexp : regs -> rexp -> Prop := 
  | WF_skip : forall r, WF_rexp r Skip
  | WF_x : forall r x n a g, 0 < n -> r x = Some (Q n, g) -> a < n -> WF_rexp r (X (x,a)) 
  | WF_cont : forall r x n a g e, 0 < n -> r x = Some (Q n, g) -> a < n -> freevar_exp x a e -> WF_rexp r (CU (x,a) e)
  | WF_rseq : forall r e1 e2,  WF_rexp r e1 -> WF_rexp r e2 -> WF_rexp r (Seq e1 e2)
  | WF_copy : forall r x y n m g1 g2, 0 < n -> 0 < m -> r x = Some (Q n, g1) -> r y = Some (Q m, g2) 
                     -> n <= m -> WF_rexp r (Copyto x y)
  | WF_inv : forall r e, WF_rexp r e -> WF_rexp r (Inv e).


(* A RCIR+ function can be a function with a RCIR+ expression or a cast oeration,
    or a RCIR+ foreign expression that might contain quantum gates.
    The requirement of quantum foreign gates in RCIR+ is that the input of registers
    for the functions to be all 0/1 bits, while the output also contains only 0/1 bits. *)
Inductive rfun A :=
       Fun : (list (rtype * evar)) -> (list (rtype * ivar)) -> rexp -> rfun A
     | Cast : rtype ->  evar -> rtype -> rfun A
     | Foreign : (list (rtype * evar)) -> (list (rtype * ivar)) -> A -> rfun A.


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

Fixpoint drop_regs (l: list (rtype * ivar)) (r :regs) :=
   match l with [] => r
         | (Q n, x)::xl => 
             fun y => if y ==? lvar x then None else drop_regs xl r y
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
Inductive WF_rfun {A} : regs -> (rfun A) -> regs -> Prop := 
    | WF_fun : forall r l1 l2 e, WF_rexp (gen_regs l2 r) e -> type_match l1 r ->
               WF_rfun r (Fun A l1 l2 e) r
    | WF_cast : forall r n m x g, r (gvar x) = Some (Q n, g) -> 0 < n -> 0 < m ->
            WF_rfun r (Cast A (Q n) x (Q m)) (update_type r (gvar x) (Q m)).

Inductive WF_rfun_list {A} : regs -> list (rfun A) -> Prop :=
    | WF_empty : forall r, WF_rfun_list r []
    | WF_many : forall r x xs r', WF_rfun r x r' -> WF_rfun_list r' xs -> WF_rfun_list r (x::xs).

Inductive WF_rtop {A} : rtop A -> Prop := 
    | WF_prog : forall l fl, WF_rfun_list (gen_regs_evar l) (fl) -> WF_rtop (Prog A l fl).



(* The semantic definition of expressions for RCIR+ including some well-formedness requirement. *)
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

Definition nupdate {A} (f : nat -> A) (i : nat) (x : A) :=
  fun j => if j =? i then x else f j.

Definition eupdate (f : regs) (x: pos) (v : bool) :=
 match x with (a,b) => 
  fun j => if j ==? a then (match f j with None => None
                                | Some (tv,gv) =>  Some (tv, nupdate gv b v) end) else f j
 end.

Notation "f '[' i '|->' x ']'" := (eupdate f i x) (at level 10).

Definition eget (f : regs) (x: pos) : option bool :=
   match x with (a,b) => match f a with None => None
                                      | Some (Q n,g) => Some (g b)
                         end
   end.

Fixpoint gup {A} (f : nat -> A) (g : nat -> A) (n : nat) :=
  match n with 0 => f
             | S m => gup (update f m (g m)) g m
  end.

Definition pupdate (f : regs) (x: avar) (g: nat -> bool) :=
           fun j => if j ==? x then (match f j with None => None | Some (tv,gv) => Some (tv,g) end) else f j.

Fixpoint app_inv p :=
  match p with
  | Skip => Skip
  | X n => X n
  | CU n p => CU n (app_inv p)
  | Seq p1 p2 => Seq (app_inv p2) (app_inv p1)
  | Copyto a b => Copyto a b
  | Inv e => e
  end.

Inductive estep : regs -> rexp -> regs -> Prop := 
  | skip_rule : forall r , estep r Skip r
  | x_rule : forall r x i n gv, r x = Some (Q n,gv) -> estep r (X (x,i)) (r [(x,i) |-> (¬ (gv i))])
  | if_rule1 : forall r p e r', eget r p = Some true -> estep r e r' -> estep r (CU p e) r'
  | if_rule2 : forall r p e, eget r p = Some false -> estep r (CU p e) r
  | seq_rule : forall r e1 e2 r' r'', estep r e1 r' -> estep r' e2 r'' -> estep r (Seq e1 e2) r''
  | copy_rule : forall r x n fv y m gv,  r x = Some (Q n, fv) -> r y = Some (Q m,gv)
               -> (forall i, 0 <= i < m -> gv i = false) 
        -> estep r (Copyto x y) (pupdate r y (gup gv fv n))
  | inv_rule : forall r r' e, estep r (app_inv e) r' -> estep r (Inv e) r'.

Definition update_type_val (f : regs) (i : avar) (x : rtype) :=
  fun y => if y ==? i then (match f i with None => None
                                 | Some (a,g) => Some (x,g)
                            end) else f y.


Inductive step_rfun {A} : regs -> rfun A -> regs -> Prop :=
   | fun_step : forall r r' l1 l2 e,
             estep (gen_regs l2 r) e r' -> step_rfun r (Fun A l1 l2 e) (drop_regs l2 r')
   | cast_step : forall r nt mt x, step_rfun r (Cast A nt x mt) (update_type_val r (gvar x) mt).

Inductive step_rfun_list {A} : regs -> list (rfun A) -> regs -> Prop :=
   | empty_step : forall r, step_rfun_list r [] r
   | many_step : forall r r' x xs, step_rfun r x r' -> step_rfun_list r (x::xs) r'.

Inductive step_top {A} : rtop A -> regs -> Prop :=
  | the_top_step : forall l fl r, step_rfun_list (gen_regs_evar l) fl r -> step_top (Prog A l fl) r.






