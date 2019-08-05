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

Ltac unify_matrices := 
  try reflexivity; 
  repeat (apply f_equal_gen; try reflexivity; 
          try (is_nat_equality; unify_pows_two; lia)).

Ltac restore_dims_rec A :=
   match A with
(* special cases *)
  | ?A × I _          => let A' := restore_dims_rec A in 
                        match type of A' with 
                        | Matrix ?m' ?n' => constr:(@Mmult m' n' n' A' (I n'))
                        end
  | I _ × ?B          => let B' := restore_dims_rec B in 
                        match type of B' with 
                        | Matrix ?n' ?o' => constr:(@Mmult n' n' o' (I n')  B')
                        end
  | ?A × @Zero ?n ?n  => let A' := restore_dims_rec A in 
                        match type of A' with 
                        | Matrix ?m' ?n' => constr:(@Mmult m' n' n' A' (@Zero n' n'))
                        end
  | @Zero ?n ?n × ?B  => let B' := restore_dims_rec B in 
                        match type of B' with 
                        | Matrix ?n' ?o' => constr:(@Mmult n' n' o' (@Zero n' n') B')
                        end
  | ?A × @Zero ?n ?o  => let A' := restore_dims_rec A in 
                        match type of A' with 
                        | Matrix ?m' ?n' => constr:(@Mmult m' n' o A' (@Zero n' o))
                        end
  | @Zero ?m ?n × ?B  => let B' := restore_dims_rec B in 
                        match type of B' with 
                        | Matrix ?n' ?o' => constr:(@Mmult n' n' o' (@Zero m n') B')
                        end
  | ?A .+ @Zero ?m ?n => let A' := restore_dims_rec A in 
                        match type of A' with 
                        | Matrix ?m' ?n' => constr:(@Mplus m' n' A' (@Zero m' n'))
                        end
  | @Zero ?m ?n .+ ?B => let B' := restore_dims_rec B in 
                        match type of B' with 
                        | Matrix ?m' ?n' => constr:(@Mplus m' n' (@Zero m' n') B')
                        end
(* general cases *)
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
  (* New: deal with functions applied to matrices *)
  | ?f ?A    => let f' := restore_dims_rec f in 
               let A' := restore_dims_rec A in 
               constr:(f' A')
  (* default *)
  | ?A       => A
   end.

Ltac restore_dims_fast := 
  try progress match goal with
  | |- ?A = ?B => let A' := restore_dims_rec A in 
                let B' := restore_dims_rec B in 
                replace A with A' by unify_matrices; 
                replace B with B' by unify_matrices
(*| |- context[?A] => match type of A with 
                    | Matrix _ _ => let A' := restore_dims_rec A in
                                   replace A with A' by unify_matrices
                    end *)
  | |- ?A      => let A' := restore_dims_rec A in 
                replace A with A' by unify_matrices
  end.

(** New matrix simplication tactics *)

Hint Rewrite kron_1_r kron_1_l Mmult_1_l Mmult_1_r Mscale_1_l 
     using (auto 100 with wf_db) : M_db_light.
Hint Rewrite kron_0_l kron_0_r Mmult_0_l Mmult_0_r Mplus_0_l Mplus_0_r
     Mscale_0_l Mscale_0_r 
     using (auto 100 with wf_db) : M_db_light.

(* I don't like always doing restore_dims first, but otherwise sometimes leaves 
   unsolvable WF_Matrix goals. *)
Ltac Msimpl_light := restore_dims_fast; autorewrite with M_db_light.

Hint Rewrite @Mmult_adjoint Mplus_adjoint @kron_adjoint @kron_mixed_product
     adjoint_involutive id_adjoint_eq 
     using (auto 100 with wf_db) : M_db'.

Ltac Msimpl := restore_dims_fast; autorewrite with M_db_light M_db'.

(* Tactics for ∣0⟩, ∣1⟩, cnot and σx. *)

Lemma Mmult00 : ⟨0∣ × ∣0⟩ = I 1. Proof. solve_matrix. Qed.
Lemma Mmult01 : ⟨0∣ × ∣1⟩ = Zero. Proof. solve_matrix. Qed.
Lemma Mmult10 : ⟨1∣ × ∣0⟩ = Zero. Proof. solve_matrix. Qed.
Lemma Mmult11 : ⟨1∣ × ∣1⟩ = I 1. Proof. solve_matrix. Qed.

Lemma σx_on_right0 : forall (q : Vector 2), (q × ⟨0∣) × σx = q × ⟨1∣.
Proof. intros. rewrite Mmult_assoc, Mmult0X. reflexivity. Qed.

Lemma σx_on_right1 : forall (q : Vector 2), (q × ⟨1∣) × σx = q × ⟨0∣.
Proof. intros. rewrite Mmult_assoc, Mmult1X. reflexivity. Qed.

Lemma σx_on_left0 : forall (q : Matrix 1 2), σx × (∣0⟩ × q) = ∣1⟩ × q.
Proof. intros. rewrite <- Mmult_assoc, MmultX0. reflexivity. Qed.

Lemma σx_on_left1 : forall (q : Matrix 1 2), σx × (∣1⟩ × q) = ∣0⟩ × q.
Proof. intros. rewrite <- Mmult_assoc, MmultX1. reflexivity. Qed.

Lemma cancel00 : forall (q1 : Matrix 2 1) (q2 : Matrix 1 2), 
  WF_Matrix q2 ->
  (q1 × ⟨0∣) × (∣0⟩ × q2) = q1 × q2.
Proof. 
  intros. 
  rewrite Mmult_assoc. 
  rewrite <- (Mmult_assoc ⟨0∣).
  rewrite Mmult00.             
  Msimpl; reflexivity.
Qed.

Lemma cancel01 : forall (q1 : Matrix 2 1) (q2 : Matrix 1 2), 
  (q1 × ⟨0∣) × (∣1⟩ × q2) = Zero.
Proof. 
  intros. 
  rewrite Mmult_assoc. 
  rewrite <- (Mmult_assoc ⟨0∣).
  rewrite Mmult01.             
  Msimpl_light; reflexivity.
Qed.

Lemma cancel10 : forall (q1 : Matrix 2 1) (q2 : Matrix 1 2), 
  (q1 × ⟨1∣) × (∣0⟩ × q2) = Zero.
Proof. 
  intros. 
  rewrite Mmult_assoc. 
  rewrite <- (Mmult_assoc ⟨1∣).
  rewrite Mmult10.             
  Msimpl_light; reflexivity.
Qed.

Lemma cancel11 : forall (q1 : Matrix 2 1) (q2 : Matrix 1 2), 
  WF_Matrix q2 ->
  (q1 × ⟨1∣) × (∣1⟩ × q2) = q1 × q2.
Proof. 
  intros. 
  rewrite Mmult_assoc. 
  rewrite <- (Mmult_assoc ⟨1∣).
  rewrite Mmult11.             
  Msimpl; reflexivity.
Qed.

Hint Rewrite Mmult00 Mmult01 Mmult10 Mmult11 Mmult0X MmultX0 Mmult1X MmultX1 : cnot_db.
Hint Rewrite σx_on_right0 σx_on_right1 σx_on_left0 σx_on_left1 : cnot_db.
Hint Rewrite cancel00 cancel01 cancel10 cancel11 using (auto with wf_db) : cnot_db.


(** Distribute addition to the outside of matrix expressions. *)

Ltac distribute_plus :=
  repeat match goal with 
  | |- context [?a × (?b .+ ?c)] => rewrite (Mmult_plus_distr_l _ _ _ a b c)
  | |- context [(?a .+ ?b) × ?c] => rewrite (Mmult_plus_distr_r _ _ _ a b c)
  | |- context [?a ⊗ (?b .+ ?c)] => rewrite (kron_plus_distr_l _ _ _ _ a b c)
  | |- context [(?a .+ ?b) ⊗ ?c] => rewrite (kron_plus_distr_r _ _ _ _ a b c)
  end.

(** Distribute scaling to the outside of matrix expressions *)

Ltac distribute_scale := 
  repeat
   match goal with
   | |- context [ (?c .* ?A) × ?B   ] => rewrite (Mscale_mult_dist_l _ _ _ c A B)
   | |- context [ ?A × (?c .* ?B)   ] => rewrite (Mscale_mult_dist_r _ _ _ c A B)
   | |- context [ (?c .* ?A) ⊗ ?B   ] => rewrite (Mscale_kron_dist_l _ _ _ _ c A B)
   | |- context [ ?A ⊗ (?c .* ?B)   ] => rewrite (Mscale_kron_dist_r _ _ _ _ c A B)
   | |- context [ ?c .* (?c' .* ?A) ] => rewrite (Mscale_assoc _ _ c c' A)
   end.


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

(* Removed in favor of subtactic of gridify.
Ltac repad := 
  repeat match goal with
  (* cnot normalization *)
  | |- context[?a <? ?b] =>
    let H := fresh "H" in 
    destruct (a <? b) eqn:H;
    [apply Nat.ltb_lt in H | apply Nat.ltb_nlt in H;
                             try (Msimpl_light; reflexivity)]
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
                             try (Msimpl_light; reflexivity)]
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
*)

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
               | Matrix 4 4 => constr:(2)
               | Matrix (2^?a) (2^?a) => constr:(a)
(*             | Matrix ?a ?b => idtac "bad dims";
                                idtac M;
                                constr:(a) *)
               end
  end.

(* not necessary in this instance - produced hypothesis is H1 *)
(* This is probably fragile and should be rewritten *)
(*
Ltac hypothesize_dims :=
  match goal with
  | |- ?A × ?B = _ => let a := get_dimensions A in
                    let b := get_dimensions B in
                    assert(a = b) by lia
  | |- _ = ?A × ?B => let a := get_dimensions A in
                    let b := get_dimensions B in
                    assert(a = b) by lia
  end.
*)

(* Hopefully always grabs the outermost product. *)
Ltac hypothesize_dims :=
  match goal with
  | |- context[?A × ?B] => let a := get_dimensions A in
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

Ltac repad := 
  (* remove boolean comparisons *)
  bdestruct_all; Msimpl_light; try reflexivity;
  (* remove minus signs *) 
  remember_differences;
  (* put dimensions in hypothesis [will sometimes exist] *)
  try hypothesize_dims; clear_dups;
  (* where a < b, replace b with a + 1 + fresh *)
  fill_differences.

Ltac gridify :=
  (* remove boolean comparisons *)
  bdestruct_all; Msimpl_light; try reflexivity;
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
  Msimpl_light.


(** Simplify Complex number expressions **)
(* TODO: Update the tactics in QWIRE/Complex.v and remove these *)

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
Ltac C_field := C_field_simplify; nonzero; trivial.
