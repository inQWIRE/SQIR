Require Import VectorStates UnitaryOps Coq.btauto.Btauto Strings.String.
Require Import RCIRplus.
Require Import RCIR.
Require Import OrderedType.

Local Open Scope nat_scope.

Module Avar_as_OT <: OrderedType.

Definition t := avar.

Definition eq (x y: avar) := avar_eq x y = true.

Definition lt (x y:avar) :=
   match x with gvar x => match y with gvar y =>  x < y
                                     | lvar y => True 
                          end
              | lvar x => match y with gvar y => False
                                     | lvar y => x < y
                          end
   end.

Lemma eq_refl : forall x : t, eq x x.
Proof.
 intros. unfold eq,avar_eq.
 destruct x. apply Nat.eqb_eq. reflexivity.
 apply Nat.eqb_eq. reflexivity.
Qed.

Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof.
 intros. unfold eq,avar_eq in *.
 destruct y. destruct x. apply Nat.eqb_eq. apply Nat.eqb_eq in H. lia.
 inversion H.
 destruct x. inversion H.
 apply Nat.eqb_eq. apply Nat.eqb_eq in H. lia.
Qed.

Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof.
 intros. unfold eq,avar_eq in *.
 destruct x. destruct y. destruct z. 
 apply Nat.eqb_eq. apply Nat.eqb_eq in H. apply Nat.eqb_eq in H0.
 lia.
 inversion H0. inversion H.
 destruct y. destruct z. 
 inversion H. inversion H.
 destruct z. inversion H0.
 apply Nat.eqb_eq. apply Nat.eqb_eq in H. apply Nat.eqb_eq in H0.
 lia.
Qed.

Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof.
  intros. unfold lt in *.
 destruct x. destruct y. destruct z. lia.
 inversion H0. inversion H.
 destruct y. destruct z. easy.
 inversion H0.
 destruct z. easy.
 lia.
Qed.

Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof.
 intros. unfold lt,eq,avar_eq in *.
 destruct x. destruct y.
 apply not_true_iff_false.
 apply Nat.eqb_neq. lia. easy.
 destruct y. easy.
 apply not_true_iff_false.
 apply Nat.eqb_neq. lia.
Qed.

Lemma compare : forall (x y : avar), Compare lt eq x y.
Proof.
Admitted.

Lemma eq_dec : forall (x y : avar), { eq x y } + { ~ eq x y }.
Proof.
Admitted.

End Avar_as_OT.


(* a pointer is an index for indicating the beginning place and the length of a variable in 
   a line of qubits. *)
Module Pointers := FMapList.Make Avar_as_OT.

Definition pointers := Pointers.t (nat * nat).

Definition empty_pointers := @Pointers.empty (nat * nat).

Fixpoint copy_fun (bits : (nat -> bool)) (base:nat) (n:nat) (f:(nat -> bool)) : nat -> bool :=
    match n with 0 => nupdate bits base (f 0)
               | S m => nupdate (copy_fun bits base m f) (base + m) (f m)
    end.

Definition fold_heap := (@Heap.fold (rtype * (nat -> bool)) (nat * pointers * (nat -> bool))).

Definition fold_regs := (@Regs.fold (rtype * (nat -> bool)) (nat * pointers * (nat -> bool))).

(* We first compile registers/heap to a line of qubits. *)
Definition compile_heap (h:heap) : (nat * pointers * (nat -> bool)) :=
   fold_heap (fun a tv result =>
               match tv with (Q n, f) => 
                   match result with (new_base,new_pointers,bits) =>
                       (new_base+n,Pointers.add (gvar a) (new_base,n) new_pointers, copy_fun bits new_base n f)
                   end
               end) h (0,empty_pointers,allfalse).

Definition compile_regs (r:regs) (result :nat * pointers * (nat -> bool)) : (nat * pointers * (nat -> bool)) :=
   fold_regs (fun a tv result =>
               match tv with (Q n, f) => 
                   match result with (new_base,new_pointers,bits) =>
                       (new_base+n,Pointers.add (lvar a) (new_base,n) new_pointers, copy_fun bits new_base n f)
                   end
               end) r result.

Lemma compile_heap_correct_1 : forall r x n f base base' pointers line, Heap.MapsTo x (Q n,f) r -> 
                  (compile_heap r) = (base,pointers,line) -> Pointers.MapsTo (gvar x) (base',n) pointers.
Proof.
Admitted.


Lemma compile_heap_correct_2 : forall r x n f base base' pointers line, Heap.MapsTo x (Q n,f) r -> 
                  (compile_heap r) = (base,pointers,line) -> Pointers.MapsTo (gvar x) (base',n) pointers ->
                  (forall m, 0 <= m < n -> line (base' + m) = f m).
Proof.
Admitted.

(* copy the bits in basea -> basea + n to the bits in baseb -> baseb + n. *)
Fixpoint compile_copy (basea: nat) (baseb: nat) (n : nat) : bccom :=
    match n with 0 => bccnot basea baseb 
               | S m => bcseq (bccnot basea baseb) (compile_copy basea baseb m)
    end.

(* compiling rexp to bccom. *)
Fixpoint compile_exp (p: pointers) (e:rexp) : option bccom :=
   match e with Skip => Some bcskip
             | X (x,m) => (match Pointers.find x p with Some (base,n) => Some (bcx (base + m)) | None => None end)
             | CU (x,m) e1 => (match Pointers.find x p with Some (base,n) =>
                                   match (compile_exp p e1) with Some e1' => Some (bccont (base + m) e1')
                                                               | None => None
                                   end
                                              | None => None
                               end)
             | Seq e1 e2 => match compile_exp p e1 with None => None
                                                    | Some e1' => 
                                   match compile_exp p e2 with None => None
                                                | Some e2' => Some (bcseq e1' e2')
                                   end
                            end
             | Copyto x y => (match Pointers.find x p with Some (basea,n)
                         => match Pointers.find y p with Some (baseb,m) => Some (compile_copy basea baseb n)
                                                       | None => None
                            end
                               | None => None
                            end)
   end.



Lemma WF_exp_compiled : forall h r e base p f, WF_rexp h r e ->
                 (compile_regs r (compile_heap h)) = (base,p,f) -> (exists b, compile_exp p e = Some b).
Proof.
 intros. induction e.
 simpl. exists bcskip. reflexivity.
 simpl. 
Admitted.

Lemma compile_exp_correct : forall h h' r r' e b base base' p p' env env', WF_rexp h r e ->
           (compile_regs r (compile_heap h)) = (base,p,env) -> compile_exp p e = Some b
                 -> estep h r e h' r' ->  (compile_regs r' (compile_heap h')) = (base',p',env') -> bcexec b env = env'.
Proof.
Admitted.


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





