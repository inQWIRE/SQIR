Require Import Reals.
Require Import Psatz.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat. 
Require Import Dirac.
Require Import QPE.
From QuickChick Require Import QuickChick.
Require Import PQASM.
Require Import CLArith.
Require Import RZArith.
Require Import QIMP.

Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Structures.Monads.

Require Import Nat Bvector.
From Bits Require Import bits.
Require Import Testing.

Local Open Scope exp_scope.
Local Open Scope nat_scope.

Definition dec2checker P `{Dec P} := checker (dec2bool P).

Fixpoint rotate_left_n (x : qvar) n :=
  match n with
  | 0 => skip
  | S n' => slrot (Nor (Var x));;; rotate_left_n x n'
  end.

Definition chacha_estore :=
  init_estore_g (map (fun x => (TNor Q Nat, x)) (seq 0 16)).

(*define example hash_function as the oracle for grover's search.
  https://qibo.readthedocs.io/en/stable/tutorials/hash-grover/README.html *)
Definition qr_qexp (a b c d : qvar) :=
  nadd (Nor (Var a)) (Nor (Var b));;;
  qxor (Nor (Var d)) (Nor (Var a)) ;;;
  rotate_left_n d (32 - 16);;;
  nadd (Nor (Var c)) (Nor (Var d));;;
  qxor (Nor (Var b)) (Nor (Var c));;;
  rotate_left_n b (32 - 12);;;
  nadd (Nor (Var a)) (Nor (Var b));;;
  qxor (Nor (Var d)) (Nor (Var a));;;
  rotate_left_n d (32 - 8);;;
  nadd (Nor (Var c)) (Nor (Var d));;;
  qxor (Nor (Var b)) (Nor (Var c));;;
  rotate_left_n b (32 - 7).

Open Scope bits_scope.

Definition rolBn (p : DWORD) k := iter k rolB p.

Infix "+" := addB : bits_scope.
Infix "^" := xorB : bits_scope.
Infix "<<<" := rolBn (at level 30, no associativity) : bits_scope.

Definition qr_spec (a b c d : DWORD) : DWORD * DWORD * DWORD * DWORD :=
  let a := a + b in
  let d := d ^ a in
  let d := d <<< 16 in
  let c := c + d in
  let b := b ^ c in
  let b := b <<< 12 in
  let a := a + b in
  let d := d ^ a in
  let d := d <<< 8 in
  let c := c + d in
  let b := b ^ c in
  let b := b <<< 7 in
  (a, b, c, d).

Definition bits2bvector {n : nat} (p : BITS n) : Bvector n :=
  n2bvector n (Z.to_N (toPosZ p)).

Definition bvector2bits {n : nat} (v : Bvector n) : BITS n :=
  fromZ (Z.of_N (bvector2n v)).

Module QRTesting.

Definition a : var := 0.
Definition b : var := 1.
Definition c : var := 2.
Definition d : var := 3.
Definition tmp : var := 101.
Definition stack : var := 102.

Definition qr_vmap : qvar * nat -> var :=
  fun '(x, _) =>
  match x with
  | L x' => x'
  | G x' => x'
  end.

Definition qr_benv :=
 match
  gen_genv (cons (TNor Q Nat, a) (cons (TNor Q Nat, b) (cons (TNor Q Nat, c) (cons (TNor Q Nat, d) nil))))
  with None => empty_benv | Some bv => bv
 end.

Definition qr_smap := 
(gen_smap_l (cons (TNor Q Nat, a) (cons (TNor Q Nat, b) (cons (TNor Q Nat, c) (cons (TNor Q Nat, d) nil)))) (fun _ => 0)).

Definition qr_pexp := 
  match
  trans_qexp
    32 (fun _ => 1) qr_vmap qr_benv QFTA empty_cstore tmp stack 0 nil
    chacha_estore chacha_estore
    (qr_qexp (G a) (G b) (G c) (G d))
  with
  | Some (Value (Some p, _, _, _)) => p
  | _ => SKIP (a, 0)
  end.

Definition qr_env : f_env := fun _ => 32.

Definition qr_oracle_spec : Checker :=
  forAllShrink arbitrary shrink (fun va =>
  forAllShrink arbitrary shrink (fun vb =>
  forAllShrink arbitrary shrink (fun vc =>
  forAllShrink arbitrary shrink (fun vd =>
  let
    '(a', b', c', d') :=
    qr_spec (bvector2bits va) (bvector2bits vb)
            (bvector2bits vc) (bvector2bits vd)
  in
  let va' := bits2bvector a' in
  let vb' := bits2bvector b' in
  let vc' := bits2bvector c' in
  let vd' := bits2bvector d' in
  dec2checker
  (st_equiv (get_vars qr_pexp) qr_env (get_prec qr_env qr_pexp)
    (prog_sem qr_env qr_pexp (a |=> va, b |=> vb, c |=> vc, d |=> vd))
        (a |=> va', b |=> vb', c |=> vc', d |=> vd')))))).

End QRTesting.

(*
QuickChickWith (updMaxSuccess stdArgs 1) QRTesting.qr_oracle_spec.
 *)

Definition dr_spec x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 :=
  let '(x0, x4, x8, x12) := qr_spec x0 x4 x8 x12 in
  let '(x1, x5, x9, x13) := qr_spec x1 x5 x9 x13 in
  let '(x2, x6, x10, x14) := qr_spec x2 x6 x10 x14 in
  let '(x3, x7, x11, x15) := qr_spec x3 x7 x11 x15 in
  let '(x0, x5, x10, x15) := qr_spec x0 x5 x10 x15 in
  let '(x1, x6, x11, x12) := qr_spec x1 x6 x11 x12 in
  let '(x2, x7, x8, x13) := qr_spec x2 x7 x8 x13 in
  let '(x3, x4, x9, x14) := qr_spec x3 x4 x9 x14 in
  (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15).

Definition dr_qexp x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 :=
  qr_qexp x0 x4 x8 x12;;;
  qr_qexp x1 x5 x9 x13;;;
  qr_qexp x2 x6 x10 x14;;;
  qr_qexp x3 x7 x11 x15;;;
  qr_qexp x0 x5 x10 x15;;;
  qr_qexp x1 x6 x11 x12;;;
  qr_qexp x2 x7 x8 x13;;;
  qr_qexp x3 x4 x9 x14.

Module DRTesting.

  Definition tmp : var := 16.
  Definition stack : var := 17.

  Definition dr_vmap : qvar * nat -> var :=
    fun '(x, _) =>
    match x with
    | L x' => x'
    | G x' => x'
    end.

  Definition dr_benv :=
   match  gen_genv (map (fun x => (TNor Q Nat, x)) (seq 0 16)) with None => empty_benv | Some bv => bv end.

  Definition dr_estore :=
    init_estore_g (map (fun x => (TNor Q Nat, x)) (seq 0 16)).

  Definition compile_dr :=
    trans_qexp 32 (fun _ => 1) dr_vmap dr_benv QFTA (empty_cstore) tmp stack 0 nil dr_estore dr_estore
    (dr_qexp (G 0) (G 1) (G 2) (G 3) (G 4) (G 5) (G 6) (G 7)
             (G 8) (G 9) (G 10) (G 11) (G 12) (G 13) (G 14) (G 15)).

  Definition dr_pexp : pexp.
  Proof.
(*

    destruct (compile_dr) eqn:E1.
    - destruct p, p, o.
      + apply p.
      + discriminate.
    - discriminate.
  Defined.
*)
  Admitted.


  Definition dr_env : f_env := fun _ => 32.

  Definition dr_oracle_spec : Checker :=
    forAllShrink arbitrary shrink (fun v0 =>
    forAllShrink arbitrary shrink (fun v1 =>
    forAllShrink arbitrary shrink (fun v2 =>
    forAllShrink arbitrary shrink (fun v3 =>
    forAllShrink arbitrary shrink (fun v4 =>
    forAllShrink arbitrary shrink (fun v5 =>
    forAllShrink arbitrary shrink (fun v6 =>
    forAllShrink arbitrary shrink (fun v7 =>
    forAllShrink arbitrary shrink (fun v8 =>
    forAllShrink arbitrary shrink (fun v9 =>
    forAllShrink arbitrary shrink (fun v10 =>
    forAllShrink arbitrary shrink (fun v11 =>
    forAllShrink arbitrary shrink (fun v12 =>
    forAllShrink arbitrary shrink (fun v13 =>
    forAllShrink arbitrary shrink (fun v14 =>
    forAllShrink arbitrary shrink (fun v15 =>
    let
      '(x0', x1', x2', x3', x4', x5', x6', x7',
        x8', x9', x10', x11', x12', x13', x14', x15') :=
      dr_spec
        (bvector2bits v0) (bvector2bits v1) (bvector2bits v2) (bvector2bits v3)
        (bvector2bits v4) (bvector2bits v5) (bvector2bits v6) (bvector2bits v7)
        (bvector2bits v8) (bvector2bits v9)
        (bvector2bits v10) (bvector2bits v11)
        (bvector2bits v12) (bvector2bits v13)
        (bvector2bits v14) (bvector2bits v15)
    in
    let v0' := bits2bvector x0' in
    let v1' := bits2bvector x1' in
    let v2' := bits2bvector x2' in
    let v3' := bits2bvector x3' in
    let v4' := bits2bvector x4' in
    let v5' := bits2bvector x5' in
    let v6' := bits2bvector x6' in
    let v7' := bits2bvector x7' in
    let v8' := bits2bvector x8' in
    let v9' := bits2bvector x9' in
    let v10' := bits2bvector x10' in
    let v11' := bits2bvector x11' in
    let v12' := bits2bvector x12' in
    let v13' := bits2bvector x13' in
    let v14' := bits2bvector x14' in
    let v15' := bits2bvector x15' in
    dec2checker
    (st_equiv (get_vars dr_pexp) dr_env (get_prec dr_env dr_pexp)
     (prog_sem dr_env dr_pexp
        (0 |=> v0, 1 |=> v1, 2 |=> v2, 3 |=> v3,
         4 |=> v4, 5 |=> v5, 6 |=> v6, 7 |=> v7,
         8 |=> v8, 9 |=> v9, 10 |=> v10, 11 |=> v11,
         12 |=> v12, 13 |=> v13, 14 |=> v14, 15 |=> v15))
     (0 |=> v0', 1 |=> v1', 2 |=> v2', 3 |=> v3',
      4 |=> v4', 5 |=> v5', 6 |=> v6', 7 |=> v7',
      8 |=> v8', 9 |=> v9', 10 |=> v10', 11 |=> v11',
      12 |=> v12', 13 |=> v13', 14 |=> v14', 15 |=> v15')))))))))))))))))).

  (*
  Conjecture dr_oracle_spec :
    forall v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15,
    let
      '(x0', x1', x2', x3', x4', x5', x6', x7',
        x8', x9', x10', x11', x12', x13', x14', x15') :=
      dr_spec
        (bvector2bits v0) (bvector2bits v1) (bvector2bits v2) (bvector2bits v3)
        (bvector2bits v4) (bvector2bits v5) (bvector2bits v6) (bvector2bits v7)
        (bvector2bits v8) (bvector2bits v9)
        (bvector2bits v10) (bvector2bits v11)
        (bvector2bits v12) (bvector2bits v13)
        (bvector2bits v14) (bvector2bits v15)
  in
  let v0' := bits2bvector x0' in
  let v1' := bits2bvector x1' in
  let v2' := bits2bvector x2' in
  let v3' := bits2bvector x3' in
  let v4' := bits2bvector x4' in
  let v5' := bits2bvector x5' in
  let v6' := bits2bvector x6' in
  let v7' := bits2bvector x7' in
  let v8' := bits2bvector x8' in
  let v9' := bits2bvector x9' in
  let v10' := bits2bvector x10' in
  let v11' := bits2bvector x11' in
  let v12' := bits2bvector x12' in
  let v13' := bits2bvector x13' in
  let v14' := bits2bvector x14' in
  let v15' := bits2bvector x15' in
  st_equiv (get_vars dr_pexp) dr_env (get_prec dr_env dr_pexp)
  (prog_sem dr_env dr_pexp
     (0 |=> v0, 1 |=> v1, 2 |=> v2, 3 |=> v3,
      4 |=> v4, 5 |=> v5, 6 |=> v6, 7 |=> v7,
      8 |=> v8, 9 |=> v9, 10 |=> v10, 11 |=> v11,
      12 |=> v12, 13 |=> v13, 14 |=> v14, 15 |=> v15))
  (0 |=> v0', 1 |=> v1', 2 |=> v2', 3 |=> v3',
   4 |=> v4', 5 |=> v5', 6 |=> v6', 7 |=> v7',
   8 |=> v8', 9 |=> v9', 10 |=> v10', 11 |=> v11',
   12 |=> v12', 13 |=> v13', 14 |=> v14', 15 |=> v15').
   *)

End DRTesting.

(*
QuickChickWith (updMaxSuccess stdArgs 1) DRTesting.dr_oracle_spec.
 *)

Fixpoint chacha_qexp' n x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 :=
  match n with
  | 0 => skip
  | S n' =>
      dr_qexp x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15;;;
      chacha_qexp' n' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
  end.

Definition chacha_qexp := chacha_qexp' 10.

Fixpoint chacha_spec' n v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 :=
  match n with
  | 0 => (v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15)
  | S n' =>
      let
        '(v0', v1', v2', v3', v4', v5', v6', v7',
          v8', v9', v10', v11', v12', v13', v14', v15') :=
        dr_spec v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
      in
      chacha_spec' n' v0' v1' v2' v3' v4' v5' v6' v7'
                      v8' v9' v10' v11' v12' v13' v14' v15'
  end.

Definition chacha_spec := chacha_spec' 10.

Module ChaChaTesting.

  Definition tmp : var := 16.
  Definition stack : var := 17.

  Definition chacha_vmap : qvar * nat -> var :=
    fun '(x, _) =>
    match x with
    | L x' => x'
    | G x' => x'
    end.

  Definition chacha_benv := 
   match gen_genv (map (fun x => (TNor Q Nat, x)) (seq 0 16)) with None => empty_benv | Some bv => bv end.

  Definition compile_chacha :=
    trans_qexp
    32 (fun _ => 1) chacha_vmap chacha_benv QFTA (empty_cstore) tmp stack 0 nil
    chacha_estore chacha_estore
    (chacha_qexp (G 0) (G 1) (G 2) (G 3) (G 4) (G 5) (G 6) (G 7)
             (G 8) (G 9) (G 10) (G 11) (G 12) (G 13) (G 14) (G 15)).

  Definition chacha_pexp : pexp.
  Proof.
(*
    destruct (compile_chacha) eqn:E1.
    - destruct p, p, o.
      + apply p.
      + discriminate.
    - discriminate.
  Defined.
*)
Admitted.

  Definition chacha_env : f_env := fun _ => 32.

  Definition chacha_oracle_spec : Checker :=
    forAllShrink arbitrary shrink (fun v0 =>
    forAllShrink arbitrary shrink (fun v1 =>
    forAllShrink arbitrary shrink (fun v2 =>
    forAllShrink arbitrary shrink (fun v3 =>
    forAllShrink arbitrary shrink (fun v4 =>
    forAllShrink arbitrary shrink (fun v5 =>
    forAllShrink arbitrary shrink (fun v6 =>
    forAllShrink arbitrary shrink (fun v7 =>
    forAllShrink arbitrary shrink (fun v8 =>
    forAllShrink arbitrary shrink (fun v9 =>
    forAllShrink arbitrary shrink (fun v10 =>
    forAllShrink arbitrary shrink (fun v11 =>
    forAllShrink arbitrary shrink (fun v12 =>
    forAllShrink arbitrary shrink (fun v13 =>
    forAllShrink arbitrary shrink (fun v14 =>
    forAllShrink arbitrary shrink (fun v15 =>
    let
      '(x0', x1', x2', x3', x4', x5', x6', x7',
        x8', x9', x10', x11', x12', x13', x14', x15') :=
      chacha_spec
        (bvector2bits v0) (bvector2bits v1) (bvector2bits v2) (bvector2bits v3)
        (bvector2bits v4) (bvector2bits v5) (bvector2bits v6) (bvector2bits v7)
        (bvector2bits v8) (bvector2bits v9)
        (bvector2bits v10) (bvector2bits v11)
        (bvector2bits v12) (bvector2bits v13)
        (bvector2bits v14) (bvector2bits v15)
    in
    let v0' := bits2bvector x0' in
    let v1' := bits2bvector x1' in
    let v2' := bits2bvector x2' in
    let v3' := bits2bvector x3' in
    let v4' := bits2bvector x4' in
    let v5' := bits2bvector x5' in
    let v6' := bits2bvector x6' in
    let v7' := bits2bvector x7' in
    let v8' := bits2bvector x8' in
    let v9' := bits2bvector x9' in
    let v10' := bits2bvector x10' in
    let v11' := bits2bvector x11' in
    let v12' := bits2bvector x12' in
    let v13' := bits2bvector x13' in
    let v14' := bits2bvector x14' in
    let v15' := bits2bvector x15' in
    dec2checker
    (st_equiv
     (get_vars chacha_pexp) chacha_env (get_prec chacha_env chacha_pexp)
     (prog_sem chacha_env chacha_pexp
        (0 |=> v0, 1 |=> v1, 2 |=> v2, 3 |=> v3,
         4 |=> v4, 5 |=> v5, 6 |=> v6, 7 |=> v7,
         8 |=> v8, 9 |=> v9, 10 |=> v10, 11 |=> v11,
         12 |=> v12, 13 |=> v13, 14 |=> v14, 15 |=> v15))
     (0 |=> v0', 1 |=> v1', 2 |=> v2', 3 |=> v3',
      4 |=> v4', 5 |=> v5', 6 |=> v6', 7 |=> v7',
      8 |=> v8', 9 |=> v9', 10 |=> v10', 11 |=> v11',
      12 |=> v12', 13 |=> v13', 14 |=> v14', 15 |=> v15')))))))))))))))))).

End ChaChaTesting.

(*
QuickChickWith (updMaxSuccess stdArgs 1) ChaChaTesting.chacha_oracle_spec.
 *)

Module Collision.

Definition x0 : qvar := L 0.
Definition x1 : qvar := L 1.
Definition x2 : qvar := L 2.
Definition x3 : qvar := L 3.
Definition x4 : qvar := L 4.
Definition x5 : qvar := L 5.
Definition x6 : qvar := L 6.
Definition x7 : qvar := L 7.
Definition x8 : qvar := L 8.
Definition x9 : qvar := L 9.
Definition x10 : qvar := L 10.
Definition x11 : qvar := L 11.
Definition x12 : qvar := L 12.
Definition x13 : qvar := L 13.
Definition x14 : qvar := L 14.
Definition x15 : qvar := L 15.
Definition out : qvar := G 16.

Definition collision_qexp
  (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : DWORD) :=
  chacha_qexp x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15;;;
  qif (ceq Nat (Nor (Var x0)) (Nor (Num (getBit v0))))
  (qif (ceq Nat (Nor (Var x1)) (Nor (Num (getBit v1))))
  (qif (ceq Nat (Nor (Var x2)) (Nor (Num (getBit v2))))
  (qif (ceq Nat (Nor (Var x3)) (Nor (Num (getBit v3))))
  (qif (ceq Nat (Nor (Var x4)) (Nor (Num (getBit v4))))
  (qif (ceq Nat (Nor (Var x5)) (Nor (Num (getBit v5))))
  (qif (ceq Nat (Nor (Var x6)) (Nor (Num (getBit v6))))
  (qif (ceq Nat (Nor (Var x7)) (Nor (Num (getBit v7))))
  (qif (ceq Nat (Nor (Var x8)) (Nor (Num (getBit v8))))
  (qif (ceq Nat (Nor (Var x9)) (Nor (Num (getBit v9))))
  (qif (ceq Nat (Nor (Var x10)) (Nor (Num (getBit v10))))
  (qif (ceq Nat (Nor (Var x11)) (Nor (Num (getBit v11))))
  (qif (ceq Nat (Nor (Var x12)) (Nor (Num (getBit v12))))
  (qif (ceq Nat (Nor (Var x13)) (Nor (Num (getBit v13))))
  (qif (ceq Nat (Nor (Var x14)) (Nor (Num (getBit v14))))
  (qif (ceq Nat (Nor (Var x15)) (Nor (Num (getBit v15))))
  (init (Nor (Var out)) (Nor (Num (fun _ => true))))
  skip) skip) skip) skip) skip) skip) skip) skip)
  skip) skip) skip) skip) skip) skip) skip) skip.

(*
Definition collision_spec
  (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 
  v0' v1' v2' v3' v4' v5' v6' v7' v8' v9' v10' v11' v12' v13' v14' v15' : DWORD)
  :=
  let
    '(v0'', v1'', v2'', v3'', v4'', v5'', v6'', v7'',
    v8'', v9'', v10'', v11'', v12'', v13'', v14'', v15'') :=
    chacha_spec v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  in
  eqtype.eq_op v0' v0'' &&
  eqtype.eq_op v1' v1'' &&
  eqtype.eq_op v2' v2'' &&
  eqtype.eq_op v3' v3'' &&
  eqtype.eq_op v4' v4'' &&
  eqtype.eq_op v5' v5'' &&
  eqtype.eq_op v6' v6'' &&
  eqtype.eq_op v7' v7'' &&
  eqtype.eq_op v8' v8'' &&
  eqtype.eq_op v9' v9'' &&
  eqtype.eq_op v10' v10'' &&
  eqtype.eq_op v11' v11'' &&
  eqtype.eq_op v12' v12'' &&
  eqtype.eq_op v13' v13'' &&
  eqtype.eq_op v14' v14'' &&
  eqtype.eq_op v15' v15''.
 *)

End Collision.

Open Scope list_scope.


Definition g :var := 1.
Definition x :var := 7.
Definition a :var := 3.
Definition b :var := 4.
Definition c :var := 6.
Definition d :var := 100.
Definition f :var := 8.
Definition result :var := 9.

(* define sin/cos. a = x^2, b = x^1/3/5/...., d is the result
    the input of sin/cos function is x/2 (not x) range from [0,pi/2) *)


Definition x2 := 6.
Definition x3 := 0.
(*
Definition x5 := 1.
Definition x7 := 2.
Definition x9 := 3.
Definition x11 := 4.
*)
Definition n : var := 10. 
Definition e : var := 15. 
Definition rc : var := 11. 
Definition re : var := 14. 
Definition fac : var := 12. 
Definition xc : var := 13. 
Definition f1 :var := 16.
Definition n1 : var := 17. 

Definition m : var := 22. 
Definition x4 : var := 23. 

Definition x_n (size:nat): func :=
   (f1, ((TNor C Nat,n)::(TNor C Nat,m)::(TArray C Nat 5, n1)::(TArray Q FixedP 5, x3)::(TArray Q FixedP 6, x4)
         ::(TNor C FixedP,e)::[]),
               qfor n (Nor (Num (nat2fb 5))) (
                nmod (Nor (Var (L m))) (Nor (Var (L n))) (Nor (Num (nat2fb 2)));;;
                qif (ceq Nat (Nor (Var (L m))) (Nor (Num (nat2fb 0)))) 
                 (ndiv (Nor (Var (L n))) (Nor (Var (L n))) (Nor (Num (nat2fb 2)));;;
                  ncadd (Index (L n1) (Var (L n))) (Index (L n1) (Var (L n))) (Nor (Num (nat2fb 1))))
                 (ndiv (Nor (Var (L n))) (Nor (Var (L n))) (Nor (Num (nat2fb 2)))));;;

               init (Index (L x3) ((Num (nat2fb 0)))) (Nor (Var (G x)));;;
               qfor n (Nor (Num (nat2fb 5))) (
                   qif (ceq Nat (Nor (Var (L n))) (Nor (Num (nat2fb 0))))
                   (skip)
                   (ncsub (Nor (Var (L m))) (Nor (Var (L n))) (Nor (Num (nat2fb 1)));;;
                    fmul (Index (L x3) (Var (L n))) (Index (L x3) (Var (L m))) (Index (L x3) (Var (L m)))
                    ));;;
               qfor n (Nor (Num (nat2fb 5))) (
                   qif (ceq Nat (Index (L n1) (Var (L n))) (Nor (Num (nat2fb 0))))
                   (skip)
                   (ncadd (Nor (Var (L m))) (Nor (Var (L n))) (Nor (Num (nat2fb 1)));;;
                    fmul (Index (L x3) (Var (L m))) (Index (L x4) (Var (L n))) (Index (L x4) (Var (L n)))
                    ));;;
                init (Nor (Var (L e))) (Index (L x4) (Num (nat2fb 5)))

,Nor (Var (L e))).

Definition taylor_sin : func := 
     (f, ((TNor C Nat, m)::(TArray Q FixedP 5,x3)::(TNor Q FixedP,x2)::(TNor Q FixedP,e)::
              (TNor C Nat,g)::(TNor C Nat,n)::(TNor C Nat, xc)::(TNor C Nat,fac)
               ::(TNor C FixedP,rc)::(TNor Q FixedP,re)::[]),
                         init (Nor (Var (L re))) (Nor (Var (G x)));;;
                         fmul (Nor (Var (L x2))) (Nor (Var (G x))) (Nor (Var (L re)));;;
                         fmul (Index (L x3) (Num (nat2fb 0))) (Nor (Var (L x2))) (Nor (Var (G x)));;;
                         fmul (Index (L x3) (Num (nat2fb 1))) (Index (L x3) (Num (nat2fb 0))) (Nor (Var (L x2)));;;
                         fmul (Index (L x3) (Num (nat2fb 2))) (Index (L x3) (Num (nat2fb 1))) (Nor (Var (L x2)));;;
                         fmul (Index (L x3) (Num (nat2fb 3))) (Index (L x3) (Num (nat2fb 2))) (Nor (Var (L x2)));;;
                         fmul (Index (L x3) (Num (nat2fb 4))) (Index (L x3) (Num (nat2fb 3))) (Nor (Var (L x2)));;;
                         ncadd (Nor (Var (L n))) (Nor (Num (nat2fb 1))) (Nor (Var (L n)));;;
                         ncadd (Nor (Var  (L xc))) (Nor (Num (nat2fb 1))) (Nor (Var  (L xc)));;;
         qfor g (Nor ((Var (L m)))) 
             (qif (iseven (Nor (Var (L g)))) 
                      (ncadd (Nor (Var ((L n)))) (Nor (Var ((L n)))) (Nor (Num (nat2fb 2)));;;
                       nfac (Nor (Var (L fac))) (Nor (Var (L n)));;;
                       ncmul (Nor (Var (L xc))) (Nor (Num (nat2fb 4))) (Nor (Var (L xc)));;;
                       fndiv (Nor (Var (L rc))) (Nor (Var (L xc))) (Nor (Var (L fac)));;;
                       fmul (Nor (Var (L e))) (Nor (Var (L rc))) (Index (L x3) (Var (L g)));;;
                       fsub (Nor (Var (L re))) (Nor (Var (L e)));;;
                       qinv ((Nor (Var (L e)))))
                      (ncadd (Nor (Var ((L n)))) (Nor (Num (nat2fb 2))) (Nor (Var ((L n))));;;
                       nfac (Nor (Var (L fac))) (Nor (Var (L n)));;;
                       ncmul (Nor (Var (L xc))) (Nor (Num (nat2fb 4))) (Nor (Var (L xc)));;;
                       fndiv (Nor (Var (L rc))) (Nor (Var (L xc))) (Nor (Var (L fac)));;;
                       fmul (Nor (Var (L e))) (Nor (Var (L rc))) (Index (L x3) (Var (L g)));;;
                       fadd (Nor (Var (L re))) (Nor (Var (L e)));;;
                       qinv ((Nor (Var (L e))))))
             ,Nor (Var (L re))).

Definition sin_prog (size:nat) : prog := 
         (size,((TNor Q FixedP, x)::[(TNor Q FixedP,result)]),(taylor_sin::[]),f,result).

Definition smapa := fun i => if i =? x3 then 5 else 1.

Definition vmapa := 
   match (gen_vmap_g ((TNor Q FixedP, x)::[(TNor Q FixedP,result)])) with (vmapg,i) =>
          gen_vmap_l ((TArray Q FixedP 5,x3)::(TNor Q FixedP,x2)::(TNor Q FixedP,e)::
              (TNor C Nat,g)::(TNor C Nat,n)::(TNor C Nat, xc)::(TNor C Nat,fac)
               ::(TNor C FixedP,rc)::(TNor Q FixedP,re)::[]) vmapg i
   end.


Parameter Pi_4 : nat -> bool. (*a binary representation of PI/4 *)

Definition taylor_cos : func := 
     (f, ((TArray Q FixedP 5,x3)::(TNor Q FixedP,x2)::(TNor Q FixedP,e)::
              (TNor C Nat,g)::(TNor C Nat,n)::(TNor C Nat, xc)::(TNor C Nat,fac)
                ::(TNor C FixedP,rc)::(TNor Q FixedP,re)::[]),
                         fsub (Nor (Var (G x))) (Nor (Num Pi_4)) ;;;
                         init (Nor (Var (L re))) (Nor (Var (G x)));;;
                         fmul (Nor (Var (L x2))) (Nor (Var (G x))) (Nor (Var (L re)));;;
                         fmul (Index (L x3) (Num (nat2fb 0))) (Nor (Var (G x))) (Nor (Var (L x2)));;;
                         fmul (Index (L x3) (Num (nat2fb 1))) (Nor (Var (L x2))) (Index (L x3) (Num (nat2fb 0)));;;
                         fmul (Index (L x3) (Num (nat2fb 2))) (Nor (Var (L x2))) (Index (L x3) (Num (nat2fb 1)));;;
                         fmul (Index (L x3) (Num (nat2fb 3))) (Nor (Var (L x2))) (Index (L x3) (Num (nat2fb 2)));;;
                         fmul (Index (L x3) (Num (nat2fb 4))) (Nor (Var (L x2))) (Index (L x3) (Num (nat2fb 3)));;;
                         ncadd (Nor (Var (L n))) (Nor (Var (L n))) (Nor (Num (nat2fb 1))) ;;;
                         ncadd (Nor (Var  (L xc))) (Nor (Var  (L xc))) (Nor (Num (nat2fb 1))) ;;;
         qfor g (Nor (Num (nat2fb 5))) 
             (qif (iseven (Nor (Var (L g)))) 
                      (ncadd (Nor (Var ((L n)))) (Nor (Var ((L n)))) (Nor (Num (nat2fb 2)));;;
                       nfac (Nor (Var (L fac))) (Nor (Var (L n)));;;
                       ncmul (Nor (Var (L xc))) (Nor (Num (nat2fb 4))) (Nor (Var (L xc)));;;
                       fndiv (Nor (Var (L rc))) (Nor (Var (L xc))) (Nor (Var (L fac)));;;
                       fmul (Nor (Var (L e))) (Nor (Var (L rc))) (Index (L x3) (Var (L g)));;;
                       fsub (Nor (Var (L re))) (Nor (Var (L e)));;;
                       qinv ((Nor (Var (L e)))))
                      (ncadd (Nor (Var ((L n)))) (Nor (Num (nat2fb 2))) (Nor (Var ((L n))));;;
                       nfac (Nor (Var (L fac))) (Nor (Var (L n)));;;
                       ncmul (Nor (Var (L xc))) (Nor (Num (nat2fb 4))) (Nor (Var (L xc)));;;
                       fndiv (Nor (Var (L rc))) (Nor (Var (L xc))) (Nor (Var (L fac)));;;
                       fmul (Nor (Var (L e))) (Nor (Var (L rc))) (Index (L x3) (Var (L g)));;;
                       fadd (Nor (Var (L re))) (Nor (Var (L e)));;;
                       qinv ((Nor (Var (L e))))))
             ,Nor (Var (L re))).

Definition cos_prog (size:nat) : prog := 
         (size,((TNor Q FixedP, x)::[(TNor Q FixedP,result)]),(taylor_cos::[]),f,result).



Definition test_fun : qexp := ndiv (Nor (Var (L x_var))) (Nor (Var (L y_var))) (Nor (Var (L z_var)))
                           ;;; nmul (Nor (Var (L s_var))) (Nor (Var (L x_var))) (Nor (Var (L c_var))).


Definition temp_var := 5. Definition temp1_var := 6. Definition stack_var := 7.

Definition qr_vmap : qvar * nat -> var :=
  fun '(x, _) =>
  match x with
  | L x' => x'
  | G x' => x'
  end.

Definition var_list := (cons (TNor C Nat, x_var) (cons (TNor C Nat, y_var) 
                   (cons (TNor C Nat, z_var) (cons (TNor Q Nat, s_var) (cons (TNor Q Nat, c_var) nil))))).

Definition qr_benv :=
 match
  gen_env var_list empty_benv
  with None => empty_benv | Some bv => bv
 end.

Definition qr_estore := init_estore empty_estore var_list.

Definition qr_cstore := init_cstore empty_cstore var_list.

Definition compile_qr_qft := 
  trans_qexp
    8 (fun _ => 1) qr_vmap qr_benv QFTA qr_cstore temp_var temp1_var stack_var 0 nil qr_estore qr_estore
    (test_fun).

Definition compile_qr_classic := 
  trans_qexp
    8 (fun _ => 1) qr_vmap qr_benv Classic qr_cstore temp_var temp1_var stack_var 0 nil qr_estore qr_estore
    (test_fun).

Check compile_qr_qft.






