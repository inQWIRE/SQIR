From Coq Require Import Arith NArith Vector Bvector.
From QuickChick Require Import QuickChick.
Require Import PQASM Testing RZArith.

Open Scope exp_scope.

Fixpoint exp2 n :=
  match n with
  | 0 => 1%N
  | S n' => N.double (exp2 n')
  end.

Lemma exp2_spec :
  forall n, exp2 n = (2 ^ N.of_nat n)%N.
Proof.
  intros n. induction n as [| n IH].
  - reflexivity.
  - rewrite Nat2N.inj_succ, N.pow_succ_r'. cbn - [ N.mul ].
    rewrite IH. apply N.double_spec.
Qed.

Definition add_bvector {n} (vn vn' : Bvector n) :=
  n2bvector n ((bvector2n vn + bvector2n vn') mod (exp2 n))%N.

Infix "[+]" := add_bvector (at level 50).

Definition mul_bvector {n} (vn vn' : Bvector n) :=
  n2bvector n ((bvector2n vn * bvector2n vn') mod (exp2 n))%N.

Infix "[*]" := mul_bvector (at level 40).

Module RzAdd.

  Definition x := 0.
  Definition y := 1.
  Definition ex := 2.

  Definition mod_add_circ n :=
    Exp (Rev x; Rev y);;
    QFT x;;
    Exp (rz_full_adder x n y);;
    RQFT x;;
    Exp (Rev y; Rev x).

  Definition mod_add_env n : f_env := fun _ => n.

  Definition mod_add_prec n : nat := get_prec (mod_add_env n) (mod_add_circ n).

  Conjecture mod_add_spec :
    forall (n : nat) (vx vy : Bvector n),
    st_equiv (get_vars (mod_add_circ n)) (mod_add_env n) (mod_add_prec n)
      (prog_sem (fun _ => n) (mod_add_circ n) (x |=> vx, y |=> vy))
          (x |=> vx [+] vy, y |=> vy).

End RzAdd.

(*
QuickChick RzAdd.mod_add_spec.
*)

Module ModMul.

  Definition mod_mul n n' d := (n * n' mod (2 ^ d))%N.

  Definition mod_mul_vec {n} (vn vn' : Bvector n) :=
    n2bvector n (mod_mul (bvector2n vn) (bvector2n vn') (N.of_nat n)).

  Definition x := 0.
  Definition y := 1.
  Definition re := 2.
  Definition ex := 3.

  Definition mod_mul_circ n := nat_full_mult n x y re ex.

  Definition mod_mul_vars n := get_vars (mod_mul_circ n).

  Definition mod_mul_env n : f_env := fun _ => n.

  Definition mod_mul_prec n : nat := get_prec (mod_mul_env n) (mod_mul_circ n).

  Conjecture mod_mul_spec :
    forall (n : nat) (vx vy vre : Bvector n),
    st_equiv (mod_mul_vars n) (mod_mul_env n) (mod_mul_prec n)
      (prog_sem (mod_mul_env n) (mod_mul_circ n)
        (x |=> vx, y |=> vy, re |=> vre))
      (x |=> vx, y |=> vy, re |=> vre [+] vx [*] vy).

End ModMul.

(*
QuickChickWith (updMaxSuccess stdArgs 1) ModMul.mod_mul_spec.
 *)

