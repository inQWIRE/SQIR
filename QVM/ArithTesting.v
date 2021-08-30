From Coq Require Import Arith NArith Vector Bvector.
From QuickChick Require Import QuickChick.
Require Import BasicUtility PQASM Testing RZArith CLArith.

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

Instance genPosSized : GenSized positive :=
  {| arbitrarySized x := fmap N.succ_pos (arbitrarySized x) |}.

Instance shrinkPos : Shrink positive :=
  {| shrink x := List.map N.succ_pos (shrink (Pos.pred_N x)) |}.

Instance showPos : Show positive := {| show p := show_N (Npos p) |}.

Definition add_bvector {n} (v v' : Bvector n) :=
  n2bvector n (bvector2n v + bvector2n v')%N.

Infix "[+]" := add_bvector (at level 50).

Definition mul_bvector {n} (v v' : Bvector n) :=
  n2bvector n (bvector2n v * bvector2n v')%N.

Infix "[*]" := mul_bvector (at level 40).

Definition div_bvector {n} (v : Bvector n) (m : nat) :=
  n2bvector n (bvector2n v / N.of_nat m).

Infix "[/]" := div_bvector (at level 40).

Definition mod_bvector {n} (v : Bvector n) (m : nat) :=
  n2bvector n (bvector2n v mod N.of_nat m).

Infix "[%]" := mod_bvector (at level 40).

Definition nth_or_false {n} (v : Bvector n) (i : nat) :=
  match lt_dec i n with
  | left P => nth_order v P
  | in_right => false
  end.

Module TofAdd.

  Definition x : var := 0.
  Definition y : var := 1.
  Definition c : posi := (2, 0).

  Definition tof_add_circ n := adder01 n x y c.

  Definition tof_add_env n : f_env := fun _ => n.

  Definition tof_add_prec n : nat := get_prec (tof_add_env n) (tof_add_circ n).

  Conjecture tof_add_spec :
    forall (n : nat) (vx vy : Bvector n),
    st_equiv (get_vars (tof_add_circ n)) (tof_add_env n) (tof_add_prec n)
      (exp_sem (fun _ => n) (tof_add_circ n) (x |=> vx, y |=> vy))
          (x |=> vx, y |=> vx [+] vy).

End TofAdd.

(*
QuickChick TofAdd.tof_add_spec.
 *)

Module RzAdd.

  Definition x := 0.
  Definition y := 1.
  Definition ex := 2.

  Definition rz_add_circ n :=
     (Rev x; Rev y);
    QFT x;
     (rz_full_adder x n y);
    RQFT x;
     (Rev y; Rev x).

  Definition rz_add_env n : f_env := fun _ => n.

  Definition rz_add_prec n : nat := get_prec (rz_add_env n) (rz_add_circ n).

  Conjecture rz_add_spec :
    forall (n : nat) (vx vy : Bvector n),
    st_equiv (get_vars (rz_add_circ n)) (rz_add_env n) (rz_add_prec n)
      (exp_sem (fun _ => n) (rz_add_circ n) (x |=> vx, y |=> vy))
          (x |=> vx [+] vy, y |=> vy).

End RzAdd.

(*
QuickChick RzAdd.rz_add_spec.
*)

Module AddParam.

  Definition x := 0.
  Definition re := 1.

  Definition add_param_circ n (vm : Bvector n) :=
    Rev x; QFT x; rz_adder x n (nth_or_false vm); RQFT x; Rev x.

  Definition add_param_vars n := get_vars (add_param_circ n (Bvect_false n)).

  Definition add_param_env n : f_env := fun _ => n.

  Definition add_param_prec n : nat :=
    get_prec (add_param_env n) (add_param_circ n (Bvect_false n)).

  Conjecture add_param_spec :
    forall (n : nat) (vm vx vre : Bvector n),
    st_equiv (add_param_vars n) (add_param_env n) (add_param_prec n)
      (exp_sem (add_param_env n) (add_param_circ n vm)
        (x |=> vx))
      (x |=> vx [+] vm).

End AddParam.

(*
QuickChick AddParam.add_param_spec.
 *)

Module RzMul.

  Definition x := 0.
  Definition y := 1.
  Definition re := 2.

  Definition rz_mul_circ n := nat_full_mult n x y re.

  Definition rz_mul_vars n := get_vars (rz_mul_circ n).

  Definition rz_mul_env n : f_env := fun _ => n.

  Definition rz_mul_prec n : nat := get_prec (rz_mul_env n) (rz_mul_circ n).

  Conjecture rz_mul_spec :
    forall (n : nat) (vx vy vre : Bvector n),
    st_equiv (rz_mul_vars n) (rz_mul_env n) (rz_mul_prec n)
      (exp_sem (rz_mul_env n) (rz_mul_circ n)
        (x |=> vx, y |=> vy, re |=> vre))
      (x |=> vx, y |=> vy, re |=> vre [+] vx [*] vy).

End RzMul.

(*
QuickChick RzMul.rz_mul_spec.
 *)

Module MulParam.

  Definition x := 0.
  Definition re := 1.

  Definition mul_param_circ n (vm : Bvector n) :=
    nat_mult n x re (nth_or_false vm).

  Definition mul_param_vars n := get_vars (mul_param_circ n (Bvect_false n)).

  Definition mul_param_env n : f_env := fun _ => n.

  Definition mul_param_prec n : nat :=
    get_prec (mul_param_env n) (mul_param_circ n (Bvect_false n)).

  Conjecture mul_param_spec :
    forall (n : nat) (vm vx vre : Bvector n),
    st_equiv (mul_param_vars n) (mul_param_env n) (mul_param_prec n)
      (exp_sem (mul_param_env n) (mul_param_circ n vm)
        (x |=> vx, re |=> vre))
      (x |=> vx, re |=> vre [+] vx [*] vm).

End MulParam.

(*
QuickChick MulParam.mul_param_spec.
 *)

Module TofMul.

  Definition x  : var := 0.
  Definition y  : var := 1.
  Definition re : var := 2.
  Definition c : posi := (3, 0).

  Definition tof_mul_circ n := cl_full_mult n x y re c.

  Definition tof_mul_vars n := get_vars (tof_mul_circ n).

  Definition tof_mul_env n : f_env := fun _ => n.

  Definition tof_mul_prec n : nat := get_prec (tof_mul_env n) (tof_mul_circ n).

  Conjecture tof_mul_spec :
    forall (n : nat) (vx vy vre : Bvector n),
    st_equiv (tof_mul_vars n) (tof_mul_env n) (tof_mul_prec n)
      (exp_sem (tof_mul_env n) (tof_mul_circ n)
        (x |=> vx, y |=> vy, re |=> vre))
            (x |=> vx, y |=> vy, re |=> vre [+] vx [*] vy).

End TofMul.

(*
QuickChick TofMul.tof_mul_spec.
 *)

Module TofMulParam.

  Definition x  : var := 0.
  Definition re : var := 2.
  Definition c : posi := (3, 0).

  Definition tof_mul_param_circ n (vm : Bvector n) :=
    cl_nat_mult n x re c (nth_or_false vm).

  Definition tof_mul_param_vars n := get_vars (tof_mul_param_circ n (Bvect_false n)).

  Definition tof_mul_param_env n : f_env := fun _ => n.

  Definition tof_mul_param_prec n : nat :=
    get_prec (tof_mul_param_env n) (tof_mul_param_circ n (Bvect_false n)).

  Conjecture tof_mul_param_spec :
    forall (n : nat) (vm vx vre : Bvector n),
    st_equiv (tof_mul_param_vars n) (tof_mul_param_env n) (tof_mul_param_prec n)
      (exp_sem (tof_mul_param_env n) (tof_mul_param_circ n vm)
        (x |=> vx, re |=> vre))
      (x |=> vx, re |=> vre [+] vx [*] vm).

End TofMulParam.

(*
QuickChick TofMul.tof_mul_spec.
 *)

Module DivMod.

  Definition x  : var := 0.
  Definition ex : var := 1.

  Definition div_mod_circ n m :=
    rz_div_mod (S n) x ex m.

  Definition div_mod_vars n := get_vars (div_mod_circ n 1).

  Definition div_mod_env n : f_env := fun _ => S n.

  Definition div_mod_prec n : nat :=
    get_prec (div_mod_env n) (div_mod_circ n 1).

  Definition div_mod_spec : Checker :=
    forAll (choose (1, 8)) (fun n =>
    forAll (choose (1, 2 ^ n - 1)) (fun m =>
    forAllShrink arbitrary shrink (fun vx : Bvector n =>
    dec2checker
    (st_equiv (div_mod_vars n) (div_mod_env n) (div_mod_prec n)
      (exp_sem (div_mod_env n) (div_mod_circ n m)
        (x |=> vx))
      (x |=> vx [%] m, ex |=> vx [/] m))))).

End DivMod.

(*
QuickChick DivMod.div_mod_spec.
 *)

Module TofDivMod.

  Definition x  : var := 0.
  Definition y  : var := 1.
  Definition ex : var := 2.
  Definition c1 : posi := (3, 0).

  Definition tof_div_mod_circ n m :=
    cl_div_mod n x y ex c1 m.

  Definition tof_div_mod_vars n := get_vars (tof_div_mod_circ n 1).

  Definition tof_div_mod_env n : f_env := fun _ => S n.

  Definition tof_div_mod_prec n : nat :=
    get_prec (tof_div_mod_env n) (tof_div_mod_circ n 1).

  Definition tof_div_mod_spec : Checker :=
    forAll (choose (1, 8)) (fun n =>
    forAll (choose (1, 2 ^ n - 1)) (fun m =>
    forAllShrink arbitrary shrink (fun vx : Bvector n =>
    dec2checker
    (st_equiv (tof_div_mod_vars n) (tof_div_mod_env n) (tof_div_mod_prec n)
      (exp_sem (tof_div_mod_env n) (tof_div_mod_circ n m)
        (x |=> vx))
      (x |=> vx [%] m, ex |=> vx [/] m))))).

End TofDivMod.

(*
QuickChick TofDivMod.tof_div_mod_spec.
 *)

