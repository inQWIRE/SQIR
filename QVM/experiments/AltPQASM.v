(* We need to redefine trans_pexp to output SQIR programs using the
   alternate gate set & prove that this new definition is equivalent
   to the old (see utilities/AltGateSet2.v and examples/shor/AltShor.v
   for examples). *)

Require Import Prelim.
Require Import RCIR.
Require Import AltGateSet2.
Require Import PQASM.
Require Import RZArith.
Require Import CLArith.
Require Import QIMP.

Definition rz_ang (n:nat) : R := ((R2 * PI)%R / R2^n). (* redefined using R2 *)

Definition rrz_ang (n:nat) : R := ((R2 * PI)%R - ((R2 * PI)%R / R2^n)).

Fixpoint gen_sr_gate' (f:vars) (x:var) (n:nat) (size:nat) : ucom U := 
    match n with 
    | 0 => AltGateSet2.ID (find_pos f (x,0))
    | S m => (gen_sr_gate' f x m size) >> (U1 (rz_ang (size - m)) (find_pos f (x,m)))
    end.
Definition gen_sr_gate (f:vars) (x:var) (n:nat) := gen_sr_gate' f x (S n) (S n).

Fixpoint gen_srr_gate' (f:vars) (x:var) (n:nat) (size:nat) : ucom U := 
    match n with 
    | 0 => AltGateSet2.ID (find_pos f (x,0))
    | S m => (gen_srr_gate' f x m size) >> (U1 (rrz_ang (size - m)) (find_pos f (x,m)))
    end.
Definition gen_srr_gate (f:vars) (x:var) (n:nat) := gen_srr_gate' f x (S n) (S n).

Check control.

Fixpoint trans_exp (f : vars) (dim:nat) (exp:exp) (avs: nat -> posi) : (ucom U * vars  * (nat -> posi)) :=
    match exp with
    | SKIP p => (AltGateSet2.ID (find_pos f p), f, avs)
    | X p => (AltGateSet2.X (find_pos f p), f, avs)
    | RZ q p => (U1 (rz_ang q) (find_pos f p), f, avs)
    | RRZ q p => (U1 (rrz_ang q) (find_pos f p), f, avs)
    | SR n x => (gen_sr_gate f x n, f, avs)
    | SRR n x => (gen_srr_gate f x n, f, avs)
    | Lshift x => (AltGateSet2.ID (find_pos f (x,0)), trans_lshift f x, lshift_avs dim f avs x)
    | Rshift x => (AltGateSet2.ID (find_pos f (x,0)), trans_rshift f x, rshift_avs dim f avs x)
    | Rev x => (AltGateSet2.ID (find_pos f (x,0)), trans_rev f x, rev_avs dim f avs x)
    | HCNOT p1 p2 => (AltGateSet2.CX (find_pos f p1) (find_pos f p2), f, avs)
    | CU p e1 => match trans_exp f dim e1 avs with 
                 | (e1', f',avs') => (control (find_pos f p) e1', f, avs) end
    | (e1 ; e2)%exp => match trans_exp f dim e1 avs with 
                 | (e1', f', avs') => 
                        match trans_exp f' dim e2 avs' with 
                        | (e2',f'',avs'') => (e1' >> e2', f'', avs'') end
                  end
    end.

Fixpoint controlled_rotations_gen (f : vars) (x:var) (n : nat) (i:nat) : ucom U :=
    match n with
    | 0 | 1 => AltGateSet2.ID (find_pos f (x,i))
    | S m => (controlled_rotations_gen f x m i) >>
              (control (find_pos f (x,m+i)) (U1 (rz_ang n) (find_pos f (x,i))))
    end.

Fixpoint QFT_gen (f : vars) (x:var) (n : nat) (size:nat) : ucom U :=
    match n with
    | 0 => AltGateSet2.ID (find_pos f (x,0))
    | S m => (QFT_gen f x m size) >>
             ((AltGateSet2.H (find_pos f (x,m))) >> 
             (controlled_rotations_gen f x (size-m) m))
    end.

Definition trans_qft (f:vars) (x:var) : ucom U := 
    QFT_gen f x (vsize f x) (vsize f x).

Definition trans_rqft (f:vars) (x:var) : ucom U :=
          invert (QFT_gen f x (vsize f x) (vsize f x)).

Fixpoint nH (f : vars) (x:var) (n:nat) : ucom U :=
    match n with 
    | 0 => AltGateSet2.ID (find_pos f (x,0))
    | S m => (AltGateSet2.H (find_pos f (x,m))) >> (nH f x m)
    end.

Definition trans_h (f : vars) (x:var) : ucom U := nH f x (vsize f x).
       
Fixpoint trans_pexp' (vs:vars) (dim:nat) (exp:pexp) (avs: nat -> posi) :=
     match exp with Exp s => (trans_exp vs dim s avs)
                 | QFT x => (trans_qft vs x, vs, avs)
                 | RQFT x => (trans_rqft vs x, vs, avs)
                 | H x => (trans_h vs x, vs, avs)
                 | PCU p e1 => match trans_pexp' vs dim e1 avs with (e1', vs',avs')
                              => (control (find_pos vs p) e1', vs, avs) end
                 | PSeq e1 e2 =>  
                         match trans_pexp' vs dim e1 avs with (e1',vs',avs') => 
                             match trans_pexp' vs' dim e2 avs' with (e2',vs'',avs'') => 
                                        (e1' >> e2', vs'', avs'')
                             end
                            end
     end.

Definition trans_pexp (vs:vars) (dim:nat) (exp:pexp) (avs: nat -> posi) := trans_pexp' (vs) dim (pexp_elim exp) avs.

(* z = M + x (TOFF-based) *)
(*
 Definition trans_cl_const_adder (size:nat) :=
   TODO
*)

(* z = x + y (TOFF-based) *)
Definition trans_cl_adder (size:nat) :=
  trans_pexp (CLArith.vars_for_adder01 size) (2 * size + 1) (CLArith.adder01_out size) (PQASM.avs_for_arith size).

(* z = M * x (TOFF-based) *)
Definition trans_cl_const_mul (size M:nat) :=
  trans_pexp (CLArith.vars_for_cl_nat_m size) (3 * size + 1) (CLArith.cl_nat_mult_out size (nat2fb M)) (PQASM.avs_for_arith size).

(* z = x * y (TOFF-based) *)
Definition trans_cl_mul (size:nat) :=
  trans_pexp (CLArith.vars_for_cl_nat_full_m size) (4 * size + 1) (CLArith.cl_full_mult_out size) (PQASM.avs_for_arith size).

(* z = M + x (QFT-based) *)
Definition trans_rz_const_adder (size M:nat) :=
  trans_pexp (RZArith.vars_for_rz_adder size) size (RZArith.rz_adder_out size (nat2fb M)) (PQASM.avs_for_arith size).

(* z = x + y (QFT-based) *)
Definition trans_rz_adder (size:nat) :=
  trans_pexp (RZArith.vars_for_rz_full_add size) (2 * size) (RZArith.rz_full_adder_out size) (PQASM.avs_for_arith size).

(* z = M * x (QFT-based) *)
Definition trans_rz_const_mul (size M:nat) :=
  trans_pexp (RZArith.vars_for_rz_nat_m size) (2 * size) (RZArith.nat_mult_out size (nat2fb M)) (PQASM.avs_for_arith size).


(* z = x * y (QFT-based) *)
Definition trans_rz_mul (size:nat) :=
  trans_pexp (RZArith.vars_for_rz_nat_full_m size) (4 * size) (RZArith.nat_full_mult_out size) (PQASM.avs_for_arith size). 


(* z = x mod y (Classical-based) *)
Definition trans_cl_mod (size M:nat) :=
  trans_pexp (CLArith.vars_for_cl_moder size) (4 * size + 2) (CLArith.cl_moder_out size M) (PQASM.avs_for_arith size). 

(* z = x / y (Classical-based) *)
Definition trans_cl_div (size M:nat) :=
  trans_pexp (CLArith.vars_for_cl_div size) (4 * size + 2) (CLArith.cl_div_out size M) (PQASM.avs_for_arith size). 

(* z = x mod y,x/y (Classical-based) *)
Definition trans_cl_div_mod (size M:nat) :=
  trans_pexp (CLArith.vars_for_cl_div_mod size) (3 * size + 2) (CLArith.cl_div_mod_out size M) (PQASM.avs_for_arith size). 


(* z = x mod y (QFT-based) *)
Definition trans_rz_mod (size M:nat) :=
  trans_pexp (RZArith.vars_for_rz_moder size) (3 * (S size) + 1) (RZArith.rz_moder_out size M) (RZArith.avs_for_rz_moder size). 

(* z = x / y (QFT-based) *)
Definition trans_rz_div (size M:nat) :=
  trans_pexp (RZArith.vars_for_rz_div size) (3 * (S size) + 1) (RZArith.rz_div_out size M) (RZArith.avs_for_rz_div size). 

(* z = x mod y,x/y (QFT-based) *)
Definition trans_rz_div_mod (size M:nat) :=
  trans_pexp (RZArith.vars_for_rz_div_mod size) (2 * (S size) + 1) (RZArith.rz_div_mod_out size M) (RZArith.avs_for_rz_div_mod size). 

(* Compile a prog to a circuit. *)
Definition prog_to_sqir_real (p:prog) (f:flag) : ucom U :=
  match prog_to_sqir p f with 
  | Some (d,size,p,vars,avs) => fst (fst (trans_pexp vars d p avs))
  | None => AltGateSet2.SKIP
end.

(* Redefine funcs in RZArith and CLArith to use the new trans_pexp *)
Definition trans_rz_modmult_rev (M C Cinv size:nat) :=
        trans_pexp (vars_for_rz size) (2*size+1) (real_rz_modmult_rev M C Cinv size) (avs_for_arith size).
Definition trans_rz_modmult_rev_alt (M C Cinv size:nat) :=
        trans_pexp (vars_for_rz size) (2*size+1) (real_rz_modmult_rev_alt M C Cinv size) (avs_for_arith size).
Definition trans_modmult_rev (M C Cinv size:nat) :=
        trans_pexp (vars_for_cl size) (4*size+2) (real_modmult_rev M C Cinv size) (avs_for_arith size).

(* Also want bc2ucom for comparison's sake *)
Fixpoint bc2ucom (bc : bccom) : ucom U :=
  match bc with
  | bcskip => AltGateSet2.SKIP
  | bcx a => AltGateSet2.X a
  | bcswap a b => (AltGateSet2.CX a b) >> (AltGateSet2.CX b a) >> (AltGateSet2.CX a b)
  | bccont a bc1 => control a (bc2ucom bc1)
  | bcseq bc1 bc2 => (bc2ucom bc1) >> (bc2ucom bc2)
  end.
  
Lemma bc2ucom_WF : forall bc, well_formed (bc2ucom bc).
Proof.
  induction bc; repeat constructor; auto.
  simpl. unfold control. apply control'_WF.
  assumption.
Qed.

(*Lemma bc2ucom_fresh : forall dim q bc,
UnitaryOps.is_fresh q (to_base_ucom dim (bc2ucom bc)) <->
@UnitaryOps.is_fresh _ dim q (RCIR.bc2ucom bc).
Proof.
intros dim q bc.
induction bc; try reflexivity.
simpl.
destruct bc; try reflexivity.
rewrite <- UnitaryOps.fresh_control.
unfold control.
rewrite <- fresh_control'.
rewrite IHbc.
reflexivity.
lia.
apply bc2ucom_WF.
rewrite <- UnitaryOps.fresh_control.
unfold control.
rewrite <- fresh_control'.
rewrite IHbc.
reflexivity.
lia.
apply bc2ucom_WF.
split; intro H; inversion H; subst; simpl.
constructor.
apply IHbc1; auto.
apply IHbc2; auto.
constructor.
apply IHbc1; auto.
apply IHbc2; auto.
Qed.

Lemma bc2ucom_correct : forall dim (bc : bccom),
uc_eval dim (bc2ucom bc) = UnitarySem.uc_eval (RCIR.bc2ucom bc).
Proof.
intros dim bc.
induction bc; try reflexivity.
simpl.
rewrite control_correct.
destruct bc; try reflexivity.
apply UnitaryOps.control_ucom_X.
apply UnitaryOps.control_cong.
apply IHbc.
apply bc2ucom_fresh. 
apply UnitaryOps.control_cong.
apply IHbc.
apply bc2ucom_fresh. 
apply bc2ucom_WF. 
unfold uc_eval in *. simpl.
rewrite IHbc1, IHbc2.
reflexivity.  
Qed.
*)
