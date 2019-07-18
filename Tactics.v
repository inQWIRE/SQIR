Require Import UnitarySem.

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
Proof. intros. subst. lia. Qed.

Lemma repad_lemma1_r : forall (a b d : nat),
  a < b -> d = (b - a - 1) -> b = d + 1 + a.
Proof. intros. subst. lia. Qed.

Lemma repad_lemma2 : forall (a b d : nat),
  a <= b -> d = (b - a) -> b = a + d.
Proof. intros. subst. lia. Qed.

Ltac cnot_tac :=
  repeat match goal with
  | |- context[?a <? ?b] =>
    let H := fresh "H" in 
    destruct (a <? b) eqn:H;
    try apply Nat.ltb_lt in H;
    try (remove_zero_gates; reflexivity)
  | H : ?a < ?b |- context[?b - ?a - 1] =>
    let d := fresh "d" in
    let R := fresh "R" in
    remember (b - a - 1) as d eqn:R;
    rewrite (repad_lemma1_l a b d H R) in * by assumption;
    try clear R H b
  end.

Ltac pad_tac :=
  repeat match goal with
  | |- context[?a <=? ?b] =>
    let H := fresh "H" in 
    destruct (a <=? b) eqn:H;
    try apply Nat.leb_le in H;
    try (remove_zero_gates; reflexivity)
  | H : ?a <= ?b |- context[?b - ?a] =>
    let d := fresh "d" in
    let R := fresh "R" in
    remember (b - a) as d eqn:R;
    rewrite (repad_lemma2 a b d H R) in *;
    try clear R H b
  end.

Ltac repad := 
  repeat match goal with
  | |- context[?a <? ?b] =>
    let H := fresh "H" in 
    destruct (a <? b) eqn:H;
    try apply Nat.ltb_lt in H;
    try (remove_zero_gates; reflexivity)
  | H : ?a < ?b |- context[?b - ?a - 1] =>
    let d := fresh "d" in
    let R := fresh "R" in
    remember (b - a - 1) as d eqn:R;
    rewrite (repad_lemma1_l a b d H R) in * by assumption;
    try clear R H b
  | |- context[?a <=? ?b] =>
    let H := fresh "H" in 
    destruct (a <=? b) eqn:H;
    try apply Nat.leb_le in H;
    try (remove_zero_gates; reflexivity)
  | H : ?a <= ?b |- context[?b - ?a] =>
    let d := fresh "d" in
    let R := fresh "R" in
    remember (b - a) as d eqn:R;
    rewrite (repad_lemma2 a b d H R) in *;
    try clear R H b
  end.

(** Make into a Plus (Kron (Mult (... ) ...) ...) Grid. **)
(* Unfinished and HIGHLY EXPERIMENTAL *)
Ltac gridify :=
  repeat rewrite kron_assoc;
  repeat rewrite <- mult_assoc;
  repeat match goal with
  | |- context[(I ?a ⊗ _) × (I ?a ⊗ _)] =>
    rewrite kron_mixed_product
  | |- context[(I (2 ^ ?a) ⊗ _) × (I (2 ^ ?b) ⊗ _)] =>
    let E := fresh "H" in 
    let d := fresh "d" in
    let R := fresh "R" in
    destruct (lt_eq_lt_dec a b) as [[H|H]|H]; [|rewrite H in *; clear H|]
  | H : ?a < ?b |- _ =>
    let d := fresh "d" in
    let R := fresh "R" in
    remember (b - a - 1) as d eqn:R;
    rewrite (repad_lemma1_l a b d H R) in * by assumption;
    clear R H b;
    repeat rewrite Nat.pow_add_r;
    repeat rewrite <- id_kron;
    repeat rewrite kron_assoc
  end;
  repeat rewrite <- kron_assoc;
  repeat rewrite mult_assoc;
  repeat match goal with
  | |- context[(_ ⊗ I ?a) × (_ ⊗ I ?b)] =>
    rewrite kron_mixed_product
  | |- context[(_ ⊗ I (2 ^ ?a)) × (_ ⊗ I (2 ^ ?b))] =>
    let E := fresh "H" in 
    let d := fresh "d" in
    let R := fresh "R" in
    destruct (lt_eq_lt_dec a b) as [[H|H]|H]; [|rewrite H in *; clear H|]
  | H : ?a < ?b |- _ =>
    let d := fresh "d" in
    let R := fresh "R" in
    remember (b - a - 1) as d eqn:R;
    rewrite (repad_lemma1_r a b d H R) in * by assumption;
    clear R H b;
    repeat rewrite Nat.pow_add_r;
    repeat rewrite <- id_kron;
    repeat rewrite <- kron_assoc
  end.


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
