Require Import VectorStates UnitaryOps Coq.btauto.Btauto Strings.String.
From QuickChick Require Import QuickChick. Import QcNotation.
Require Export ExtLib.Structures.Monads.
Export MonadNotation.
Open Scope monad_scope.
Local Open Scope string.
(* The language for RCIR+, a target language for QLLVM to compile to. *)
Local Open Scope nat_scope.


(* We first define two types variables appearing in an expression.
    global variables and local variables. *)

Fixpoint string_of_nat_aux (time n : nat) (acc : string) : string :=
  let d := match n mod 10 with
           | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
           | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
           end in
  let acc' := d ++ acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => string_of_nat_aux time' n' acc'
      end
  end.

Definition ivar := nat.


Definition evar := nat.
(*For whatever reason QuickChick does not want to derive these *)


Inductive rtype := Q (n:nat).
Derive Show for rtype.

Definition genRtype (min max : nat) : G rtype :=
  liftM Q (choose (min, max)).
Locate "<-".
Locate "freq".
Definition genEvar (min max : nat ) : G evar :=
  choose (min, max).
Definition genIvar (min max : nat ) : G ivar :=
  choose (min, max).
Fixpoint genListRtypeEvar (size : nat): G (list (rtype * evar)) :=
  match size with
  | 0 => ret []
  | S size' =>   (bind (genListRtypeEvar size')
                         (fun xs => bind (genRtype 4 8)
                                      (fun x => bind (genEvar 1 4)
                                                  (fun e => ret ((x, e):: xs)))))
                    end. 
Fixpoint genListRtypeIvar (size : nat): G (list (rtype * ivar)) :=
  match size with
  | 0 => ret []
  | S size' =>   (bind (genListRtypeIvar size')
                         (fun xs => bind (genRtype 4 8)
                                      (fun x => bind (genIvar 1 4)
                                                  (fun e => ret ((x, e):: xs)))))
                    end. 

Sample (genListRtypeIvar 3).
Inductive avar := lvar : ivar -> avar | gvar : evar -> avar.
Notation " 'freq' [ x ;;; y ] " := (freq_ (snd x) (cons x (cons y nil))) .
Notation " 'freq' [ x ;;; y ;;; .. ;;; z ] " := (freq_ (snd x) (cons x (cons y .. (cons z nil) ..))).
Notation " 'oneOf' ( x ;;; l ) " := (oneOf_ x (cons x l)) .
Notation " 'oneOf' [ x ;;; y ;;; .. ;;; z ] " := (oneOf_ (snd x) (cons x (cons y .. (cons z nil) ..))).
(*This isn't working Properly *)
Definition genAvar (min max : nat) : G avar :=
  freq [ (1, (bind (genIvar min max) (fun i => ret (lvar i)))) ;;;
         (1,  (bind (genEvar min max) (fun e => ret (gvar e))))
        ].

Definition genAvarConst (label : nat) : G avar :=
  freq [ (1, ret (lvar label)) ;;;
          (1, ret (gvar label)) ]. 


Derive Show for avar.
Sample (genAvar 1 6).
(* Warning: The following logical axioms were
encountered: semBindOptSizeMonotonicIncl_r semBindOptSizeMonotonicIncl_l.
Having invalid logical
axiom in the environment when extracting may lead to incorrect or non-terminating ML terms.
 [extraction-logical-axiom,extraction] 
[lvar 4; lvar 2; lvar 5; lvar 3; gvar 4; lvar 4; lvar 5; gvar 5; gvar 2; lvar 6; lvar 4]*)


Sample (genAvarConst 3).
(* Warning: The following logical axioms were
encountered: semBindOptSizeMonotonicIncl_r semBindOptSizeMonotonicIncl_l.
Having invalid logical
axiom in the environment when extracting may lead to incorrect or non-terminating ML terms.
 [extraction-logical-axiom,extraction]
[gvar 3; gvar 3; gvar 3; lvar 3; gvar 3; lvar 3; gvar 3; gvar 3; lvar 3; gvar 3; lvar 3] *)
Locate "oneOf".
Definition genAvarOneOf (min max : nat) : G avar :=
  oneOf [  (bind (genIvar min max) (fun i => ret (lvar i))) ;;
         (bind (genEvar min max) (fun e => ret (gvar e)))
        ].
Sample (genAvarOneOf 1 6).
(* [gvar 5; gvar 2; gvar 1; gvar 6; gvar 5; gvar 6; gvar 3; gvar 3; gvar 2; gvar 4; gvar 1]
 *)
Print genAvar.
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
Instance showPair {A B : Type} `{Show A} `{Show B} : Show (A * B) :=
  {
    show p :=
      let (a,b) := p in
        "(" ++ show a ++ "," ++ show b ++ ")"
  }.
Fixpoint gen_pos (min max : nat) : G pos :=
  (bind (choose (min, max)) (fun n =>
           (bind (genAvarConst n) (fun a =>
                (bind (choose (min, n)) (fun m => ret (a, m)))) )  )).
Sample (gen_pos 1 6). 
Inductive rexp :=
             | Skip : rexp | X : pos -> rexp | CU : pos -> rexp -> rexp 
             | Seq : rexp -> rexp -> rexp | Copyto : avar -> avar -> rexp.
Derive Show for rexp.

(* The following defines the initialization of a register set for the expression in a function. *)
Definition allfalse := fun (_ : nat) => false.

(* The following defines the registers. *)
Require Import OrderedTypeEx.

Module Heap := FMapList.Make Nat_as_OT.

Definition heap := Heap.t (rtype * (nat -> bool)).

Definition empty_heap := @Heap.empty (rtype * (nat -> bool)).

Module Regs := FMapList.Make Nat_as_OT.

Definition regs := Regs.t (rtype * (nat -> bool)).

Definition empty_regs := @Regs.empty (rtype * (nat -> bool)).

Definition nupdate {A} (f : nat -> A) (i : nat) (x : A) :=
  fun j => if j =? i then x else f j.

Definition update_type_heap (h:heap) (x:evar) (t:rtype) : heap := Heap.add x (t,allfalse) h.

Definition update_type_regs (r:regs) (x:ivar) (t:rtype) : regs := Regs.add x (t,allfalse) r.

Definition update_val_heap (h:heap) (x:evar) (g:(nat -> bool)) : heap :=
               match Heap.find x h with Some (t,v) => Heap.add x (t,v) h | None => h end.

Definition update_val_regs (r:regs) (x:evar) (g:(nat -> bool)) : regs :=
               match Regs.find x r with Some (t,v) => Regs.add x (t,v) r | None => r end.

Definition update_bit_heap (h:heap) (u:evar) (b:nat) (v:bool) : heap :=
              match Heap.find u h with Some (t,g) => Heap.add u (t,nupdate g b v) h | None => h end.

Definition update_bit_regs (h:regs) (u:evar) (b:nat) (v:bool) : regs :=
              match Regs.find u h with Some (t,g) => Regs.add u (t,nupdate g b v) h | None => h end.

(*Just a sample generator, could be improved *)

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
 |  freevar_copyto : forall x n a b, freevar_exp x n (Copyto a b).

Definition lookup (h:heap) (r:regs)  (x:avar) : option (rtype * (nat -> bool)) :=
    match x with gvar u => Heap.find u h
               | lvar u => Regs.find u r
     end.

Inductive WF_rexp : heap -> regs -> rexp -> Prop := 
  | WF_skip : forall h r, WF_rexp h r Skip
  | WF_x1 : forall h r x n a g, 0 < n -> Heap.MapsTo x (Q n, g) h -> a < n -> WF_rexp h r (X (gvar x,a))
  | WF_x2 : forall h r x n a g, 0 < n -> Regs.MapsTo x (Q n, g) r -> a < n -> WF_rexp h r (X (lvar x,a))
  | WF_cont1 : forall h r x n a g e, 0 < n -> Heap.MapsTo x (Q n, g) h -> a < n
                         -> freevar_exp (gvar x) a e -> WF_rexp h r (CU (gvar x,a) e)
  | WF_cont2 : forall h r x n a g e, 0 < n -> Regs.MapsTo x (Q n, g) r -> a < n
                         -> freevar_exp (lvar x) a e -> WF_rexp h r (CU (lvar x,a) e)
  | WF_rseq : forall h r e1 e2,  WF_rexp h r e1 -> WF_rexp h r e2 -> WF_rexp h r (Seq e1 e2)
  | WF_copy : forall h r x y n m g1 g2, 0 < n -> 0 < m -> lookup h r x = Some (Q n, g1) -> lookup h r y = Some (Q m, g2) 
                     -> n <= m -> WF_rexp h r (Copyto x y).


(* A RCIR+ function can be a function with a RCIR+ expression or a cast oeration,
    or a RCIR+ foreign expression that might contain quantum gates.
    The requirement of quantum foreign gates in RCIR+ is that the input of registers
    for the functions to be all 0/1 bits, while the output also contains only 0/1 bits. *)
Inductive rfun A :=
       Fun : (list (rtype * evar)) -> (list (rtype * ivar)) -> rexp -> rfun A
     | Cast : rtype ->  evar -> rtype -> rfun A
      (* init is to initialize a local variable with a number. 
         A local variable refers to a constant in QSSA. *)
     | Init : rtype -> evar -> (nat -> bool) -> rfun A
     | Inv : list (rfun A) -> rfun A
     | Foreign : (list (rtype * evar)) -> (list (rtype * ivar)) -> A -> rfun A.

Fixpoint gen_heap (l : list (rtype * evar)) : heap := 
  match l with [] => empty_heap
            | (Q n, x)::xl => Heap.add x (Q n, allfalse) (gen_heap xl)
  end.

Fixpoint gen_regs (l: list (rtype * ivar)) : regs :=
   match l with [] => empty_regs
         | (Q n, x)::xl => Regs.add x (Q n, allfalse) (gen_regs xl)
   end.

(* The following defines the well-formedness of rfun that depends on an input register set
    having all variables being global variables. *)
Fixpoint type_match (l: list (rtype * evar)) (r : heap) : Prop :=
    match l with [] => True
          | (Q n, x)::xl => 
         (match Heap.find x r with Some (Q m, f) => n = m | None => False end) /\  type_match xl r
    end.

(* Define the top level of the language. Every program is a list of global variable definitions plus a list of rfun functions. *)
Inductive rtop A := Prog : list (rtype * evar) -> list (rfun A) -> rtop A.

(*
Definition update_type (f : regs) (i : avar) (x : rtype) :=
  fun y => if y ==? i then Some (x,allfalse) else f y.
*)

(* The well-formedness of a program is based on a step by step type checking on the wellfi*)
Definition WF_type (t:rtype) : Prop := match t with Q 0 => False | _ => True end.

Inductive WF_rfun {A} : heap -> (rfun A) -> heap -> Prop := 
    | WF_fun : forall h l1 l2 e, WF_rexp h (gen_regs l2) e -> type_match l1 h ->
               WF_rfun h (Fun A l1 l2 e) h
    | WF_cast : forall h n m x g, Heap.MapsTo x (Q n, g) h -> 0 < n -> 0 < m ->
            WF_rfun h (Cast A (Q n) x (Q m)) (update_type_heap h x (Q m))
    | WF_init : forall h x g t, WF_type t -> ~ Heap.In x h -> WF_rfun h (Init A t x g) (update_type_heap h x t)
    | WF_inv : forall h h' l, WF_rfun_list h l h' -> WF_rfun h (Inv A l) h'
with
 WF_rfun_list {A} : heap -> list (rfun A) -> heap -> Prop :=
    | WF_empty : forall h, WF_rfun_list h [] h
    | WF_many : forall h h' h'' x xs, WF_rfun h x h' -> WF_rfun_list h' xs h'' -> WF_rfun_list h (x::xs) h''.

Inductive WF_rtop {A} : rtop A -> Prop := 
    | WF_prog : forall l h fl,  WF_rfun_list (gen_heap l) fl h -> WF_rtop (Prog A l fl).



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

(*
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
Definition emptyregs : regs :=
  fun j => None.
(* regs :  avar -> option (rtype * (nat -> bool)) *)

Definition emptyfun : nat -> bool :=
  fun j => false.
Definition emptyreg : (rtype * (nat -> bool)) :=
  (Q 3, emptyfun).
*)


Definition genBool : G bool :=
  freq [ (1, ret false) ;;;
         (1, ret true)

      ].
  
Fixpoint genRandomSizedFun (size : nat) : G (nat -> bool) :=
  match size with
  |0 => bind (genBool) (fun v =>  ret (update allfalse 0 v))
  | S s' => bind (genBool) (fun v =>
                (bind (genRandomSizedFun s') (fun g => ret ( update g s' v))))
                                     end.
Eval compute in show empty_regs.
Sample (genRandomSizedFun 3).
Sample genBool.

Fixpoint show_reg_aux (reg : (rtype * (nat -> bool))) : string :=
  let (rl, f) := reg in match rl with
                          |Q n =>("(Q " ++ show n ++ ", " ++ show (funbool_to_list n f) ++ ")")end. 
                                                                  
Instance show_reg 
  : Show (rtype * (nat -> bool)) :=
  {
    show p :=
      show_reg_aux p 
  }.

Fixpoint genReg (min_size max_size : nat ) : G (rtype * (nat -> bool)) := 
  (bind (choose (min_size, max_size)) (fun s => (bind (genRandomSizedFun s)
                                               (fun f => ret (Q s, f))) )).
Sample (genReg 2 6).
(* like pupdate but adds a register to regs *)
Definition update_regs (f : regs) (x: ivar) (g: (rtype * (nat -> bool))) :=
  fun j => if j =? x then Some g else Regs.find j f.

(*
Fixpoint show_regs_aux (regs :  ivar -> option (rtype * (nat -> bool)))
         (max_var_num : nat) : string :=
  let (l, e) := (lvar max_var_num, gvar max_var_num) in match max_var_num with
        | 0 => "{" ++ show l ++ ": " ++ show (regs l) ++ "}{" ++ show e ++ ": " ++ show (regs e) ++ "}"
        | S s'=> "{" ++ show l ++ ": " ++ show (regs l) ++ "}{" ++ show e ++ ": " ++ show (regs e) ++ "}, " ++ (show_regs_aux regs s')
                                                               end. 
                                                                  
  (* arbitrarily choosing 10 as the max register *)
Instance show_regs 
  : Show (regs) :=
  {
    show p :=
      show_regs_aux p 1
  }.
Fixpoint genRegsSized (fuel reg_size_min reg_size_max : nat) : G regs :=
  let reg := (genReg reg_size_min reg_size_max)
    in match fuel with
      |0 =>  freq [ (1, (bind (genIvar fuel fuel)
          (fun i => (bind reg                                                                               
               (fun r => ret (update_regs emptyregs (lvar i) r) ))))) ;;;
             (1, (bind (genEvar fuel fuel)
          (fun e => (bind reg                                                                               
     (fun r => ret (update_regs emptyregs (gvar e) r) )))))  ;;;
             (1, ret emptyregs)                                                               
                  ]
      |S s' =>    let regs := (genRegsSized s' reg_size_min reg_size_max) in
          freq [ (1, (bind (genIvar fuel fuel)
          (fun i => (bind reg                                                                               
                          (fun r => (bind regs (fun rs => ret (update_regs rs (lvar i) r)) )))))) ;;;
             (1, (bind (genEvar fuel fuel)
          (fun e => (bind reg                                                                              
                             (fun r => bind regs (fun rs => ret (update_regs rs (gvar e) r))) ))))  ;;;
             (1, (bind regs (fun rs => ret rs)))                                                               
                  ]

                  end.
(* genposfromregs? *)
Sample (genRegsSized 1 4 4).
(* TODO: Fix how it shows the functions *)
Fixpoint app_inv p :=
  match p with
  | Skip => Skip
  | X n => X n
  | CU n p => CU n (app_inv p)
  | Seq p1 p2 => Seq (app_inv p2) (app_inv p1)
  | Copyto a b => Copyto a b
  | Inv e => e
  end.
*)

Fixpoint gup {A} (f : nat -> A) (g : nat -> A) (n : nat) :=
  match n with 0 => f
             | S m => gup (update f m (g m)) g m
  end.

Inductive estep : heap -> regs -> rexp -> heap -> regs -> Prop := 
  | skip_rule : forall h r , estep h r Skip h r
  | x_rule1 : forall h r x i n gv, Regs.MapsTo x (Q n,gv) r
                          -> estep h r (X (lvar x,i)) h (update_bit_regs r x i (¬ (gv i)))
  | x_rule2 : forall h r x i n gv, Heap.MapsTo x (Q n,gv) h
                       -> estep h r (X (gvar x,i)) (update_bit_heap h x i (¬ (gv i))) r
  | if_rule_true1 : forall h r x i n gv e h' r', Regs.MapsTo x (Q n, gv) r -> gv i = true ->
                         estep h r e h' r' -> estep h r (CU (lvar x,i) e) h r'
  | if_rule_true2 : forall h r x i n gv e h' r', Heap.MapsTo x (Q n, gv) h -> gv i = true ->
                         estep h r e h' r' -> estep h r (CU (gvar x,i) e) h r'
  | if_rule_false1 : forall h r x i n gv e, Regs.MapsTo x (Q n, gv) r -> gv i = false -> estep h r (CU (lvar x, i) e) h r
  | if_rule_false2 : forall h r x i n gv e, Heap.MapsTo x (Q n, gv) h -> gv i = false -> estep h r (CU (gvar x, i) e) h r
  | seq_rule : forall h r e1 e2 h' r' h'' r'', estep h r e1 h' r'
                        -> estep h' r' e2 h'' r'' -> estep h r (Seq e1 e2) h'' r''
  | copy_rule1 : forall h r x n fv y m gv,  lookup h r x = Some (Q n, fv) -> Regs.MapsTo y (Q m,gv) r
               -> (forall i, 0 <= i < m -> gv i = false) 
               -> estep h r (Copyto x (lvar y)) h (update_val_regs r y (gup gv fv n))
  | copy_rule2 : forall h r x n fv y m gv,  lookup h r x = Some (Q n, fv) -> Heap.MapsTo y (Q m,gv) h
               -> (forall i, 0 <= i < m -> gv i = false) 
               -> estep h r (Copyto x (lvar y)) (update_val_heap h y (gup gv fv n)) r.


Inductive step_rfun {A} : heap -> rfun A -> heap -> Prop :=
   | fun_step : forall r h h' l1 l2 e,
             estep h (gen_regs l2) e h' r -> step_rfun h (Fun A l1 l2 e) h'
   | cast_step : forall h nt mt x, step_rfun h (Cast A nt x mt) (update_type_heap h x mt)
   | init_step : forall h t x n, step_rfun h (Init A t x n) (update_val_heap (update_type_heap h x t) x n)
   | inv_step : forall h h' l, step_rfun_list h l h' -> step_rfun h (Inv A l) h'

with step_rfun_list {A} : heap -> list (rfun A) -> heap -> Prop :=
   | empty_step : forall h, step_rfun_list h [] h
   | many_step : forall h h' h'' x xs, step_rfun h x h' -> step_rfun_list h' xs h'' -> step_rfun_list h (x::xs) h''.

Inductive step_top {A} : rtop A -> heap -> Prop :=
  | the_top_step : forall l fl h, step_rfun_list (gen_heap l) fl h -> step_top (Prog A l fl) h.


Require Import RCIR.

(* fb_push is to take a qubit and then push it to the zero position 
        in the bool function representation of a number. *)
Definition fb_push b f : nat -> bool :=
  fun x => match x with
        | O => b
        | S n => f n
        end.

(*
Definition allfalse := fun (_ : nat) => false.
*)

(* fb_push_n is the n repeatation of fb_push. *)
Definition fb_push_n n f g : nat -> bool :=
  fun i => if (i <? n) then f i else g (i - n).

(* A function to compile positive to a bool function. *)
Fixpoint pos2fb p : nat -> bool :=
  match p with
  | xH => fb_push true allfalse
  | xI p' => fb_push true (pos2fb p')
  | xO p' => fb_push false (pos2fb p')
  end.

(* A function to compile N to a bool function. *)
Definition N2fb n : nat -> bool :=
  match n with
  | 0%N => allfalse
  | Npos p => pos2fb p
  end.

Definition add_c b x y :=
  match b with
  | false => Pos.add x y
  | true => Pos.add_carry x y
  end.

(* A function to compile a natural number to a bool function. *)
Definition nat2fb n := N2fb (N.of_nat n).

(* reg_push is the encapsulation of fb_push_n. *)
Definition reg_push (x : nat) (n : nat) (f : nat -> bool) := fb_push_n n (nat2fb x) f.


(* The following three lemmas show that the relationship between
   the bool function before and after the application of fb_push/fb_push_n
   in different bit positions. *)
Lemma fb_push_right:
  forall n b f, 0 < n -> fb_push b f n = f (n-1).
Proof.
  intros. induction n. lia.
  simpl. assert ((n - 0) = n) by lia.
  rewrite H0. reflexivity.
Qed.

Lemma fb_push_n_left :
  forall n x f g,
    x < n -> fb_push_n n f g x = f x.
Proof.
  intros. unfold fb_push_n. rewrite <- Nat.ltb_lt in H. rewrite H. easy.
Qed.

Lemma fb_push_n_right :
  forall n x f g,
    n <= x -> fb_push_n n f g x = g (x - n).
Proof.
  intros. unfold fb_push_n. rewrite <- Nat.ltb_ge in H. rewrite H. easy.
Qed.

(* The lemma shows that the reg_push of a number x that has n qubit is essentially
   the same as turning the number to a bool function. *)
Lemma reg_push_inv:
  forall x n f a, a < n -> (reg_push x n f) a = (nat2fb x) a.
Proof.
  intros.
  unfold nat2fb,N2fb,reg_push,fb_push_n.
  destruct x.
  simpl.
  bdestruct (a <? n).
  unfold nat2fb.
  simpl. reflexivity.
  lia.
  bdestruct (a <? n).
  unfold nat2fb.
  simpl.
  reflexivity.
  lia.
Qed.

Ltac fb_push_n_simpl := repeat (try rewrite fb_push_n_left by lia; try rewrite fb_push_n_right by lia).
Ltac update_simpl := repeat (try rewrite update_index_neq by lia); try rewrite update_index_eq by lia.

Ltac BreakIfExpression :=
  match goal with
  | [ |- context[if ?X <? ?Y then _ else _] ] => bdestruct (X <? Y); try lia
  | [ |- context[if ?X <=? ?Y then _ else _] ] => bdestruct (X <=? Y); try lia
  | [ |- context[if ?X =? ?Y then _ else _] ] => bdestruct (X =? Y); try lia
  end.

Ltac IfExpSimpl := repeat BreakIfExpression.





