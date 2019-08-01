Require Export QWIRE.Quantum.
Require Import Omega.

(* A general tactics file. Many of these tactics will eventually be
   moved to more appropriate places in the QWIRE or SQIRE developments. *)

(* Belongs in Prelim *)
Lemma f_equal_gen : forall {A B} (f g : A -> B) a b, f = g -> a = b -> f a = g b.
Proof. intros. subst. reflexivity. Qed.

(** Restoring Matrix dimensions *)
Ltac is_nat_equality :=
  match goal with 
  | |- ?A = ?B => match type of A with
                | nat => idtac
                end
  end.

Ltac unify_matrices_light := 
  repeat (apply f_equal_gen; trivial; try (is_nat_equality; unify_pows_two; lia)).

Ltac restore_dims_rec A :=
   match A with
  | ?A × ?B   => let A' := restore_dims_rec A in 
                let B' := restore_dims_rec B in 
                match type of A' with 
                | Matrix ?m' ?n' =>
                  match type of B' with 
                  | Matrix ?n'' ?o' => constr:(@Mmult m' n' o' A' B')
                  end
                end 
  | ?A ⊗ ?B   => let A' := restore_dims_rec A in 
                let B' := restore_dims_rec B in 
                match type of A' with 
                | Matrix ?m' ?n' =>
                  match type of B' with 
                  | Matrix ?o' ?p' => constr:(@kron m' n' o' p' A' B')
                  end
                end
  | ?A †      => let A' := restore_dims_rec A in 
                match type of A' with
                | Matrix ?m' ?n' => constr:(@adjoint m' n' A')
                end
  | ?A .+ ?B => let A' := restore_dims_rec A in 
               let B' := restore_dims_rec B in 
               match type of A' with 
               | Matrix ?m' ?n' =>
                 match type of B' with 
                 | Matrix ?m'' ?n'' => constr:(@Mplus m' n' A' B')
                 end
               end
  | ?c .* ?A => let A' := restore_dims_rec A in 
               match type of A' with
               | Matrix ?m' ?n' => constr:(@scale m' n' c A')
               end
  | ?A       => A
   end.

Ltac restore_dims_fast := 
  match goal with
  | |- ?A = ?B => let A' := restore_dims_rec A in 
                let B' := restore_dims_rec B in 
                replace A with A' by unify_matrices_light; 
                replace B with B' by unify_matrices_light
  end.

(** Distribute addition to the outside of matrix expressions. *)

Ltac distribute_plus :=
  repeat match goal with 
  | |- context [?a × (?b .+ ?c)] => rewrite (Mmult_plus_distr_l _ _ _ a b c)
  | |- context [(?a .+ ?b) × ?c] => rewrite (Mmult_plus_distr_r _ _ _ a b c)
  | |- context [?a ⊗ (?b .+ ?c)] => rewrite (kron_plus_distr_l _ _ _ _ a b c)
  | |- context [(?a .+ ?b) ⊗ ?c] => rewrite (kron_plus_distr_r _ _ _ _ a b c)
  end.

(** Very lightweight matrix automation **)

(* For handling non well-typed cases. (Shouldn't Msimpl do this?) *)
Ltac remove_zero_gates :=
  repeat rewrite Mmult_0_l;
  repeat rewrite Mmult_0_r;
  repeat rewrite Mmult_0_l; (* hacky *)
  repeat rewrite Mmult_0_r;
  repeat rewrite kron_0_l;
  repeat rewrite kron_0_r;
  repeat rewrite kron_0_l;
  repeat rewrite kron_0_r.

(* Remove extra identity gates. (Shouldn't Msimpl do this too?) *)
Ltac remove_id_gates :=
  repeat rewrite Mmult_1_l;
  repeat rewrite Mmult_1_r;
  try auto with wf_db.
  
(* Several of the type rewrites are just associativity issues, and lia
   is a little slow solving these. *)
Ltac rewrite_assoc :=
  repeat rewrite mult_assoc;
  easy.

(** Dealing with padding **)

Local Close Scope R_scope.
Local Close Scope C_scope.

Lemma repad_lemma1_l : forall (a b d : nat),
  a < b -> d = (b - a - 1) -> b = a + 1 + d.
Proof. intros. subst. omega. Qed. (* surprising lia choke point *)

Lemma repad_lemma1_r : forall (a b d : nat),
  a < b -> d = (b - a - 1) -> b = d + 1 + a.
Proof. intros. subst. omega. Qed.

Lemma repad_lemma2 : forall (a b d : nat),
  a <= b -> d = (b - a) -> b = a + d.
Proof. intros. subst. omega. Qed.

Ltac contradict_eqb_false :=
  match goal with
  | H : _ =? _ = false |- _ => apply Nat.eqb_neq in H; try lia
  | H : _ <=? _ = false |- _ => apply Nat.leb_nle in H; try lia
  | H : _ <? _ = false |- _ => apply Nat.ltb_nlt in H; try lia
  end.

Ltac repad := 
  repeat match goal with
  (* cnot normalization *)
  | |- context[?a <? ?b] =>
    let H := fresh "H" in 
    destruct (a <? b) eqn:H;
    [apply Nat.ltb_lt in H | apply Nat.ltb_nlt in H;
                             try (remove_zero_gates; reflexivity)]
  | H : ?a < ?b |- context[?b - ?a - 1] => 
    let d := fresh "d" in
    let R := fresh "R" in
    remember (b - a - 1) as d eqn:R ;
    apply (repad_lemma1_l a b d) in H; trivial;
    clear R;
    try rewrite H in *;
    try clear b H
  (* pad normalization *)
  | |- context[?a <=? ?b] =>
    let H := fresh "H" in 
    destruct (a <=? b) eqn:H;
    [apply Nat.leb_le in H | apply Nat.leb_nle in H;
                             try (remove_zero_gates; reflexivity)]
  | H:?a <= ?b  |- context [ ?b - ?a ] =>
    let d := fresh "d" in
    let R := fresh "R" in
    remember (b - a) as d eqn:R ;
    apply (repad_lemma2 a b d) in H; trivial;
    clear R;
    try rewrite H in *;
    try clear b H
  end;
  try lia.

(** Gridify: Turns an matrix expression into a normal form with 
    plus on the outside, then tensor, then matrix multiplication.
    Eg: ((..×..×..)⊗(..×..×..)⊗(..×..×..)) .+ ((..×..)⊗(..×..))
*)

Lemma le_ex_diff_l : forall a b, a <= b -> exists d, b = d + a. 
Proof. intros. exists (b - a). omega. Qed.

Lemma le_ex_diff_r : forall a b, a <= b -> exists d, b = a + d. 
Proof. intros. exists (b - a). omega. Qed.  

Lemma lt_ex_diff_l : forall a b, a < b -> exists d, b = d + 1 + a. 
Proof. intros. exists (b - a - 1). omega. Qed.

Lemma lt_ex_diff_r : forall a b, a < b -> exists d, b = a + 1 + d. 
Proof. intros. exists (b - a - 1). omega. Qed.

Ltac bdestruct_all :=
  repeat match goal with
  | |- context[?a <? ?b] => bdestruct (a <? b)
  | |- context[?a <=? ?b] => bdestruct (a <=? b)                                       
  | |- context[?a =? ?b] => bdestruct (a =? b)
  end; try (exfalso; lia).

(* Remove _ < _ from hyps, remove _ - _  from goal *)
Ltac remember_differences :=
  repeat match goal with
  | H : ?a < ?b |- context[?b - ?a - 1] => 
    let d := fresh "d" in
    let R := fresh "R" in
    remember (b - a - 1) as d eqn:R ;
    apply (repad_lemma1_l a b d) in H; trivial;
    clear R;
    try rewrite H in *;
    try clear b H
  | H:?a <= ?b  |- context [ ?b - ?a ] =>
    let d := fresh "d" in
    let R := fresh "R" in
    remember (b - a) as d eqn:R ;
    apply (repad_lemma2 a b d) in H; trivial;
    clear R;
    try rewrite H in *;
    try clear b H
  end.

(* gets the exponents of the dimensions of the given matrix expression *)
(* assumes all matrices are square *)
Ltac get_dimensions M :=
  match M with
  | ?A ⊗ ?B  => let a := get_dimensions A in
               let b := get_dimensions B in
               constr:(a + b)
  | ?A .+ ?B => get_dimensions A
  | _        => match type of M with
               | Matrix 2 2 => constr:(1)
               | Matrix (2^?a) (2^?a) => constr:(a)
               | Matrix ?a ?b => idtac "bad dims";
                                idtac M;
                                constr:(a)
               end
  end.

(* not necessary in this instance - produced hypothesis is H1 *)
(* This is probably fragile and should be rewritten *)
Ltac hypothesize_dims :=
  match goal with
  | |- ?A × ?B = _ => let a := get_dimensions A in
                    let b := get_dimensions B in
                    assert(a = b) by lia
  | |- _ = ?A × ?B => let a := get_dimensions A in
                    let b := get_dimensions B in
                    assert(a = b) by lia
  end.

(* Unifies an equation of the form `a + 1 + b + 1 + c = a' + 1 + b' + 1 + c'`
   (exact symmetry isn't required) by filling in the holes *) 
Ltac fill_differences :=
  repeat match goal with 
  | R : _ < _ |- _           => let d := fresh "d" in
                              destruct (lt_ex_diff_r _ _ R);
                              clear R; subst
  | H : _ = _ |- _           => rewrite <- plus_assoc in H
  | H : ?a + _ = ?a + _ |- _ => apply Nat.add_cancel_l in H; subst
  | H : ?a + _ = ?b + _ |- _ => destruct (lt_eq_lt_dec a b) as [[?|?]|?]; subst
  end; try lia.

Ltac gridify :=
  (* remove boolean comparisons *)
  bdestruct_all; remove_zero_gates; try reflexivity;
  (* remove minus signs *) 
  remember_differences;
  (* put dimensions in hypothesis [will sometimes exist] *)
  try hypothesize_dims; clear_dups;
  (* where a < b, replace b with a + 1 + fresh *)
  fill_differences;
  (* distribute *)  
  restore_dims_fast; distribute_plus;
  repeat rewrite Nat.pow_add_r;
  repeat rewrite <- id_kron; simpl;
  repeat rewrite mult_assoc;
  restore_dims_fast; repeat rewrite <- kron_assoc;
  restore_dims_fast; repeat rewrite kron_mixed_product;
  (* simplify *)
  Msimpl.


(** Simplify Complex number expressions **)

Ltac nonzero :=
  repeat split;
   try match goal with
       | |- not (@eq _ ?x (RtoC (IZR Z0))) => apply RtoC_neq
       | |- not (@eq _ Ci (RtoC (IZR Z0))) => apply C0_snd_neq; simpl
       end;
   repeat
    match goal with
    | |- not (@eq _ (sqrt ?x) (IZR Z0)) => apply sqrt_neq_0_compat
    | |- not (@eq _ (Rinv ?x) (IZR Z0)) => apply Rinv_neq_0_compat
    end; match goal with
         | |- not (@eq _ _ _) => lra
         | |- Rlt _ _ => lra
         end.

Ltac C_field_simplify := repeat field_simplify_eq [ Csqrt2_sqrt Csqrt2_inv Ci2].
