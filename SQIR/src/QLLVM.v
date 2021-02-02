Require Import VectorStates UnitaryOps Coq.btauto.Btauto Strings.String.

(* The syntax of IR Language for classical circuit. *)
Definition var := nat.

Definition qvar := nat.

Inductive const :=
| cvar (x : var)
| cnum (n : nat)
| cplus (c1 : const) (c2 : const)
| cminus (c1 : const) (c2 : const)
| cmult (c1 : const) (c2 : const)
| cdiv (c1 : const) (c2 : const)
| cmod (c1 : const) (c2 : const)
| cfac (c1 : const)
| cpow (c1 : const) (c2: const)
.

Inductive factor := fconst (c:const) | fvar (x : qvar).

Inductive exp := eplus (x : factor) (y: factor)
      | eminus (x:factor) (y:factor)
      | emult (x:factor) (y:factor)
      | ediv (x:factor) (y:factor)
      | emod (x:factor) (y:factor)
      | efac (y:const)
      | epow (x:factor) (y:const)
      | esqrt (x:factor)
      | esin (x:factor)
      | ecos (x:factor)
      | ecall (f:qvar) (vs: list factor)
      | sigma (c1:const) (c2:const) (f:qvar) (vs: list factor).

Inductive inst := assign (x:qvar) (e:exp) | uncompute.

Inductive efun := elet qvar (ns : list var) (qs: list qvar) (ins : list inst) (ret : qvar).

Inductive setting :=setFixedPointNum (n: const) | setBitLength (n:const) | efixed (x: list var) | setUncomputeStrategy (x: string).

Inductive top := Prog (ss : list setting) (fs : list efun).

(* The frontend level language. QC. *)
Inductive C := varC (v:qvar) | natC (n:nat).

Inductive E := cconst (c:C) | plusC (e1:E) (e2:E) 
             | minusC (e1:E) (e2:E) | multC (e1:E) (e2:E)
             | divC (e1:E) (e2:E) | modC (e1:E) (e2:E)
             | facC (e:E) 
             | powC (e:E) (n:C) 
             | sinC (e:E) | cosC (e:E) | sqrtC (e:E)
             | sigmaC (c1:C) (c2:C) (f:qvar) (v : E).

Inductive cinst := letin (v:var) (e1:E) (e2:E).

Inductive ctop := setFixedPointNumC (n: nat) | setBitLengthC (n:nat) 
              | fixedC (x: list var) | setUncomputeStrategyC (x: string) | ins (cs : list cinst).


(* The language for RCIR+, a target language for QLLVM to compile to. 
Local Open Scope nat_scope.
Definition ivar := nat.

Definition evar := nat.

Inductive rtype := Q (n:nat).

Inductive avar := lvar : ivar -> avar | gvar : evar -> avar.

Definition pos : Type := avar * nat.

Inductive rexp :=
             | rskip : rexp | rx : pos -> rexp | rcont : pos -> rexp -> rexp 
     | rseq : rexp -> rexp -> rexp | copyto : avar -> avar -> rexp.

Definition regs := (avar -> option (rtype * (nat -> bool))).

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


Definition nupdate {A} (f : nat -> A) (i : nat) (x : A) :=
  fun j => if j =? i then x else f j.

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

(* The semantic definition of expressions for RCIR+ including some well-formedness requirement.
   TODO: need to split well-formedness requirement with RCIR+ semantics. *)
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

Inductive rfun :=
       Fun : (list (rtype * evar)) -> (list (rtype * ivar)) -> rexp -> rfun
     | cast : rtype ->  evar -> rtype -> rfun.

Inductive rtop := Define : list (rtype * evar) -> rtop
                               | Insts : rfun -> rtop.
*)
    






