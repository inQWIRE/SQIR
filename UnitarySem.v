Require Export Denote_Ctrls.
Require Export SQIMP.

Open Scope ucom_scope.

(** Denotation of ucoms **)

Fixpoint uc_eval (dim : nat) (c : ucom) : Matrix (2^dim) (2^dim) :=
  match c with
  | uskip   => I (2^dim)
  | l *= u  => apply_unitary dim u l
  | c1 ; c2 => uc_eval dim c2 × uc_eval dim c1 
  end.

(* Basic Lemmas *)

Lemma uskip_id_l : forall (dim : nat) (c : ucom), uc_eval dim (uskip ; c) = uc_eval dim c.
Proof.
  intros dim c.
  simpl.
  rewrite Mmult_1_r. reflexivity.
  (* time to handle *)
Abort.


(* Minor optimizations *)

Fixpoint rm_uskips (c : ucom) : ucom :=
  match c with
  | c1 ; c2 => match rm_uskips c1, rm_uskips c2 with
              | uskip, c2' => c2'
              | c1', uskip => c1'
              | c1', c2'   => c1'; c2'
              end
  | c'      => c'
  end.

Lemma rm_uskips_sound : forall c dim, uc_eval dim c = uc_eval dim (rm_uskips c).
Proof.
  intros c dim.
  induction c; trivial.
  simpl.
  destruct (rm_uskips c1) eqn:E1, (rm_uskips c2) eqn:E2; trivial.
  - rewrite IHc1, IHc2.
    simpl. Msimpl. reflexivity.
  - rewrite IHc1, IHc2.
    simpl. Msimpl. rewrite Mmult_1_r.
