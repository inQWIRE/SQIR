(* We need to redefine trans_pexp to output SQIR programs using the
   alternate gate set & prove that this new definition is equivalent
   to the old (see utilities/AltGateSet.v and examples/shor/AltShor.v
   for examples). *)
  
Require Import Reals. 
Require Import AltGateSet.
Require Import VSQIR.

Definition rz_ang (n:nat) : R := ((R2 * PI)%R / R2^n).

Definition rrz_ang (n:nat) : R := ((R2 * PI)%R - ((R2 * PI)%R / R2^n)).

Fixpoint gen_sr_gate' (f:vars) (x:var) (n:nat) (size:nat) : ucom U := 
    match n with 
    | 0 => AltGateSet.SKIP
    | S m => (gen_sr_gate' f x m size) >> (U1 (rz_ang (size - m)) (find_pos f (x,m)))
    end.
Definition gen_sr_gate (f:vars) (x:var) (n:nat) := gen_sr_gate' f x (S n) (S n).

Fixpoint gen_srr_gate' (f:vars) (x:var) (n:nat) (size:nat) : ucom U := 
    match n with 
    | 0 => AltGateSet.SKIP
    | S m => (gen_srr_gate' f x m size) >> (U1 (rrz_ang (size - m)) (find_pos f (x,m)))
    end.
Definition gen_srr_gate (f:vars) (x:var) (n:nat) := gen_srr_gate' f x (S n) (S n).

Fixpoint trans_exp (f : vars) (dim:nat) (exp:exp) (avs: nat -> posi) : (ucom U * vars  * (nat -> posi)) :=
    match exp with
    | SKIP p => (AltGateSet.SKIP, f, avs)
    | X p => (AltGateSet.X (find_pos f p), f, avs)
    | RZ q p => (U1 (rz_ang q) (find_pos f p), f, avs)
    | RRZ q p => (U1 (rrz_ang q) (find_pos f p), f, avs)
    | SR n x => (gen_sr_gate f x n, f, avs)
    | SRR n x => (gen_srr_gate f x n, f, avs)
    | Lshift x => (AltGateSet.SKIP, trans_lshift f x, lshift_avs dim f avs x)
    | Rshift x => (AltGateSet.SKIP, trans_rshift f x, rshift_avs dim f avs x)
    | Rev x => (AltGateSet.SKIP, trans_rev f x, rev_avs dim f avs x)
    | HCNOT p1 p2 => (AltGateSet.CX (find_pos f p1) (find_pos f p2), f, avs)
    | CU p1 (X p2) => (AltGateSet.CX (find_pos f p1) (find_pos f p2), f, avs)
    | CU p e1 => match trans_exp f dim e1 avs with 
                 | (e1', f',avs') => (control (find_pos f p) e1', f, avs) end
    | (e1 ; e2)%exp => match trans_exp f dim e1 avs with 
                 | (e1', f', avs') => 
                        match trans_exp f' dim e2 avs' with 
                        | (e2',f'',avs'') => (e1' >> e2', f'', avs'') end
                  end
    end.

(* TODO: reuse defns in AltShor? *)

Fixpoint controlled_rotations_gen (f : vars) (x:var) (n : nat) (i:nat) : ucom U :=
    match n with
    | 0 | 1 => AltGateSet.SKIP
    | S m => (controlled_rotations_gen f x m i) >>
              (control (find_pos f (x,m+i)) (U1 (rz_ang n) (find_pos f (x,i))))
    end.

Fixpoint QFT_gen (f : vars) (x:var) (n : nat) (size:nat) : ucom U :=
    match n with
    | 0 => AltGateSet.SKIP
    | S m => (AltGateSet.H (find_pos f (x,m))) >> 
             ((controlled_rotations_gen f x (size-m) m) >>
             (QFT_gen f x m size))
    end.

Definition trans_qft (f:vars) (x:var) : ucom U := 
    QFT_gen f x (vsize f x) (vsize f x).

Fixpoint controlled_rotations_gen_r (f : vars) (x:var) (n : nat) (i:nat) : ucom U :=
    match n with
    | 0 | 1 => AltGateSet.SKIP
    | S m  => (control (find_pos f (x,m+i)) (U1 (rrz_ang n) (find_pos f (x,i)))) >>
              (controlled_rotations_gen_r f x m i)
    end.

Fixpoint QFT_gen_r (f : vars) (x:var) (n : nat) (size:nat) : ucom U :=
    match n with
    | 0 => AltGateSet.SKIP
    | S m => (controlled_rotations_gen_r f x (size-m) m) >>
             ((AltGateSet.H (find_pos f (x,m))) >> (QFT_gen_r f x m size))
    end.

Definition trans_rqft (f:vars) (x:var) : ucom U :=
    QFT_gen_r f x (vsize f x) (vsize f x).

Fixpoint nH (f : vars) (x:var) (n:nat) : ucom U :=
    match n with 
    | 0 => AltGateSet.SKIP
    | S m => (AltGateSet.H (find_pos f (x,m))) >> (nH f x m)
    end.

Definition trans_h (f : vars) (x:var) : ucom U := nH f x (vsize f x).
       
Fixpoint trans_pexp (vs:vars) (dim:nat) (exp:pexp) (avs: nat -> posi) :=
     match exp with Exp s => (trans_exp vs dim s avs)
                 | QFT x => (trans_qft vs x, vs, avs)
                 | RQFT x => (trans_rqft vs x, vs, avs)
                 | H x => (trans_h vs x, vs, avs)
                 | PCU p e1 => match trans_pexp vs dim e1 avs with (e1', vs',avs')
                              => (control (find_pos vs p) e1', vs, avs) end
                 | PSeq e1 e2 =>  
                         match trans_pexp vs dim e1 avs with (e1',vs',avs') => 
                             match trans_pexp vs' dim e2 avs' with (e2',vs'',avs'') => 
                                        (e1' >> e2', vs'', avs'')
                             end
                            end
     end.
