Require Import VectorStates UnitaryOps Coq.btauto.Btauto Strings.String.

(* The language for RCIR+, a target language for QLLVM to compile to. *)
Local Open Scope nat_scope.


(* We first define two types variables appearing in an expression.
    global variables and local variables. *)
Definition ivar := nat.

Definition evar := nat.

Definition nvar := nat.

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

Inductive bound : Set := 
   | Br : nat -> nvar -> nat -> bound
   | NBr : nat -> nvar -> nat -> bound
   | Num : nat -> bound.

Inductive pred : Set :=
   | Unit : bound -> pred (* x = m * var + m for exactly one *)
   | Space : nat -> nat -> pred. (* forall x, x =  m * x + m for every one that sat the formula. *)

(*   | Rel : ivar -> ivar -> bound -> pred (* forall x, x := m * y + m *)
   | Pow : ivar -> bound -> pred (* x = 2 ^ bound *)
   | Fun : ivar -> (nat -> bool) -> pred (* forall x , f x *)
   | AnDiv : ivar -> nat -> bound -> pred (* Angle x = n * Pi / 2 ^ y  *)
   | Angle : ivar -> nat -> pred (* Angle x = n *)
   | Conj : pred -> pred -> pred. (* pred /\ pred *)*)

Definition update_nvar {A} (f : (nvar -> A)) (i : nvar) (x : A) :=
  fun y => if y =? i then x else f y.

Definition eval_pred (x:nat) (f : nvar -> Prop) (p:pred) : Prop :=
   match p with 
                 | Unit (Br n y m) => (x = (n * y + m) /\ f y)
                 | Unit (NBr n y m) => (x = (n * y - m) /\ f y)
                 | Unit (Num n) => (x = n)
                 | Space n m => (exists y, x = n * y + m)
   end.

Definition neq_pred (x:nat) (yv : nat) (p:pred) : Prop :=
   match p with 
                 | Unit (Br n y m) => (x <> (n * yv + m))
                 | Unit (NBr n y m) => (x <> (n * yv - m))
                 | Unit (Num n) => (x <> n)
                 | Space n m => (forall y, x <> n * y + m)
   end.


(* This is the expression in a function in the RCIR+ language. 
   It does not contain quantum gates. quantum gates will be foreign functions. *)
Inductive rexp :=
             | Skip : rexp | X : (avar * nvar) -> rexp | Cont : (avar * nvar) -> rexp -> rexp 
     | Let : nvar -> pred -> rexp -> rexp | Seq : rexp -> rexp -> rexp | Copyto : avar -> avar -> rexp.

Definition regs := (avar -> option (rtype * (nat -> bool))).


(* The following defines the well-formedness of an RCIR+ expression. 
   The well-formedness depends on an input register set. *)
Inductive bound_pred : list nvar -> pred -> Prop :=
   | bound_pred_unit_br : forall xs n y m, In y xs -> bound_pred xs (Unit (Br n y m))
   | bound_pred_unit_nbr : forall xs n y m, In y xs -> bound_pred xs (Unit (NBr n y m))
   | bound_pred_unit_num : forall xs n, bound_pred xs (Unit (Num n))
   | bound_pred_space : forall xs n m, bound_pred xs (Space n m).

Inductive bound_let : list nvar -> rexp -> Prop :=
   | bound_let_skip : forall xs, bound_let xs Skip
   | bound_let_x : forall xs y m, In m xs -> bound_let xs (X (y,m))
   | bound_let_cont : forall xs y m e, In m xs -> bound_let xs e -> bound_let xs (Cont (y,m) e)
   | bound_let_let : forall xs n p e, bound_pred xs p -> bound_let (n::xs) e -> bound_let xs (Let n p e)
   | bound_let_seq : forall xs e1 e2, bound_let xs e1 -> bound_let xs e2 -> bound_let xs (Seq e1 e2)
   | bound_let_copy : forall xs x y, bound_let xs (Copyto x y).

Inductive map_elem : Set := Enum (n:nat) | Espace (n1:nat) (n2:nat).

(* well-formedness of a predicate based on the relation of
    the input dimension number and the specified predicate type and number. *)
Inductive WF_elem : nat -> map_elem -> Prop := 
  | WF_unit_Num : forall n x, x < n -> WF_elem n (Enum x)
  | WF_space : forall n x y, y < n -> WF_elem n (Espace x y).

Definition nvar_map_pred (x:nvar) (p:pred) (f : nvar -> option map_elem) : (nvar -> option map_elem) :=
   match p with Unit (Num n) => update_nvar f x (Some (Enum n))
             | Unit (Br n y m) => (match f y with None => update_nvar f x None
                                           | Some (Enum a) => update_nvar f x (Some (Enum (n * a + m)))
                                           | Some (Espace n1 m1) => update_nvar f x (Some (Espace (n * n1) (n*m1 + m)))
                                   end)
             | Unit (NBr n y m) => (match f y with None => update_nvar f x None
                                           | Some (Enum a) => update_nvar f x (Some (Enum (n * a - m)))
                                           | Some (Espace n1 m1) => update_nvar f x (Some (Espace (n * n1) (n*m1 - m)))
                                    end)
            | Space n m => update_nvar f x (Some (Espace n m))
   end.


Fixpoint nvar_map (r:rexp) (f : nvar -> option map_elem) : (nvar -> option map_elem) :=
   match r with Skip => f
             | X (x,n) => f
             | Let x p e => nvar_map e (nvar_map_pred x p f)
             | Cont (x,n) e => nvar_map e f
             | Seq e1 e2 => nvar_map e2 (nvar_map e1 f)
             | Copyto x y => f
   end.

Inductive freevar_exp : avar -> nat -> (nvar -> option map_elem) -> rexp -> Prop := 
   freevar_skip : forall a n f, freevar_exp a n f Skip
 | freevar_x_neq : forall a x b n f, a <> x -> freevar_exp a n f (X (x,b))
 | freevar_x_num : forall f x n m b,  f b = Some (Enum m) -> n <> m -> freevar_exp x n f (X (x,b))
 | freevar_x_space : forall f x n i j b,  f b = Some (Espace i j) -> (forall y, n <> i * y + j) -> freevar_exp x n f (X (x,b))
 | freevar_cont_neq : forall f a x n b e,  a <> x -> freevar_exp a n f e -> freevar_exp a n f (Cont (x,b) e)
 | freevar_cont_num : forall f x n m b e,  f b = Some (Enum m) -> n <> m ->
                                 freevar_exp x n f e -> freevar_exp x n f (Cont (x,b) e)
 | freevar_cont_space : forall f x n i j b e,  f b = Some (Espace i j) -> (forall y, n <> i * y + j) ->
                           freevar_exp x n f e -> freevar_exp x n f (Cont (x,b) e)
 | freevar_seq : forall f x n e1 e2, freevar_exp x n f e1 -> freevar_exp x n f e2 -> freevar_exp x n f (Seq e1 e2)
 |  freevar_copyto : forall x n f a b, freevar_exp x n f (Copyto a b).

Inductive WF_rexp : (nvar -> option map_elem) -> regs -> rexp -> Prop := 
  | WF_skip : forall f r, WF_rexp f r Skip
  | WF_x : forall f r x n p a g, 0 < n -> r x = Some (Q n, g) ->
                          f p = Some a -> WF_elem n a -> WF_rexp f r (X (x,p))
  | WF_let : forall f r x p e, WF_rexp (nvar_map_pred x p f) r e -> WF_rexp f r (Let x p e)
  | WF_cont_num : forall f r x n a p g e, 0 < n -> r x = Some (Q n, g) -> a < n -> f p = Some (Enum a)
                    -> freevar_exp x a f e -> WF_rexp f r (Cont (x,p) e)
  | WF_cont_space : forall f r x n a b p g e y, 0 < n -> r x = Some (Q n, g) -> a < n -> f p = Some (Espace a b)
                    -> (exists z, y = a * z + b -> freevar_exp x y f e) -> WF_rexp f r (Cont (x,p) e)
  | WF_rseq : forall f r e1 e2,  WF_rexp f r e1 -> WF_rexp f r e2 -> WF_rexp f r (Seq e1 e2)
  | WF_copy : forall f r x y n m g1 g2, 0 < n -> 0 < m -> r x = Some (Q n, g1) -> r y = Some (Q m, g2) 
                     -> n <= m -> WF_rexp f r (Copyto x y).

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

Definition allNone : (nvar -> option map_elem) := fun (_ : nvar) => None.

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
    | WF_fun : forall r l1 l2 e, WF_rexp allNone (gen_regs l2 (gen_regs_evar l1)) e -> type_match l1 r ->
               WF_rfun r (Fun A l1 l2 e) r
    | WF_cast : forall r n m x g, r (gvar x) = Some (Q n, g) -> 0 < n -> 0 < m ->
            WF_rfun r (Cast A (Q n) x (Q m)) (update_type r (gvar x) (Q m)).

Inductive WF_rfun_list {A} : regs -> list (rfun A) -> Prop :=
    | WF_empty : forall r, WF_rfun_list r []
    | WF_many : forall r x xs r', WF_rfun r x r' -> WF_rfun_list r' xs -> WF_rfun_list r (x::xs).

Inductive WF_rtop {A} : rtop A -> Prop := 
    | WF_prog : forall l fl, WF_rfun_list (gen_regs_evar l) (fl) -> WF_rtop (Prog A l fl).



(* The semantic definition of expressions for RCIR+ including some well-formedness requirement. *)
Definition pos_eq (r1 r2 : (avar * nvar)) : bool := 
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

(*
Definition eupdate (f : regs) (x: (avar * nvar)) (v : bool) :=
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

Definition eval_bound (f: nvar -> nat) (b:bound) : nat :=
   match b with Br n x m => n * (f x) + m
              | NBr n x m => n * (f x) - m
              | Num n => n
   end.

Inductive estep : (nvar -> nat) -> regs -> rexp -> regs -> Prop := 
  | skip_rule : forall f r , estep f r Skip r
  | let_rule_num : forall f r r' x p e, estep (update_nvar f x (eval_bound f p)) r e r' -> estep f r (Let x (Unit p) e) r'
  | let_rule_space : forall f r r' x a b e, 
                  (forall y , exists z , y = a * z + b -> estep (update_nvar f x y) r e r')
                                             -> estep f r (Let x (Space a b) e) r'.
  | x_rule : forall r x i n gv, r x = Some (Q n,gv) -> i < n -> estep r (rx (x,i)) (r [(x,i) |-> (¬ (gv i))])
  | if_rule1 : forall r x i n gv e r', r x = Some (Q n,gv) -> i < n -> gv i = true
                            -> estep r e r' -> estep r (rcont (x,i) e) r'
  | if_rule2 : forall r x i n gv e, r x = Some (Q n,gv) -> i < n -> gv i = false
                            -> estep r (rcont (x,i) e) r
  | seq_rule : forall r e1 e2 r' r'', estep r e1 r' -> estep r' e2 r'' -> estep r (rseq e1 e2) r''
  | copy_rule : forall r x n fv y m gv,  r x = Some (Q n, fv) -> r y = Some (Q m,gv)
               -> n <= m -> (forall i, 0 <= i < m -> gv i = false) 
        -> estep r (copyto x y) (pupdate r y (gup gv fv n)).






