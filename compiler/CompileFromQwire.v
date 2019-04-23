Require Import QWIRE.Denotation.
Require Import DensitySem.
Require Import HOASCircuits.

Local Open Scope com_scope.

(* SQIRE is a limited language, so not every QWIRE circuit has a SQIRE equivalent.
   In particular, we will ignore circuits with classical control (lift) and 
   unsupported gates (which, for now, is most gates). 
   
   As a first pass, we will ignore:
   - ctrl U for U <> X
   - bit_ctrl U
   - BNOT
   - init0
   - init1
   - new0
   - new1
   - meas
   - discard
   - assert0
   - assert1
  
   TODO extensions:
   * Support arbitrary controlled unitaries - requires writing a function to
     describe arbitrary controlled unitaries using SQIRE constructs.
   * Support discard, init, etc. - the denotation of the output SQIRE program 
     should be the same as the denotation of the QWIRE program, but padded with
     extra \ket{0}'s where qubits are initialized or discarded. I expect that 
     this will be non-trivial.
   * Compile from HOAS boxes instead of DB circuits (this change is not hard).
*)

Definition compile_gate {W1 W2 : WType} (g : Gate W1 W2) (l : list nat) : com :=
  match g with 
  | U u => match W1 with
          | Qubit => let q := hd 0%nat l in
                    match u with
                    | _H => H q
                    | _X => X q
                    | _Y => Y q
                    | _Z => Z q
                    | _R_ ϕ => uapp (U_R ϕ) [q]
                    | _ => skip (* unsupported *)
                    end
          | Qubit ⊗ Qubit => let q1 := hd 0%nat l in
                             let q2 := hd 0%nat (tl l) in
                             match u with
                             |  ctrl _X => CNOT q1 q2
                             | _ => skip (* unsupported *)
                             end
          | _ => skip (* unsupported *)
          end
  | measQ => meas (hd 0%nat l)
  | _ => skip (* unsupported *)
  end.

Fixpoint compile_from_db_circuit {W : WType} (c : DeBruijn_Circuit W) : com :=
  match c with
  | db_output p => skip
  | db_gate g p c' => compile_gate g (pat_to_list p); compile_from_db_circuit c'
  | _ => skip (* unsupported *)
  end.

(* Does the input circuit only contain supported operations? *)
Inductive is_supported {W : WType} : DeBruijn_Circuit W -> Prop :=
  | supported_output : forall p, is_supported (db_output p)
  | suported_gate_H : forall p c, is_supported c -> is_supported (db_gate (U _H) p c)
  | suported_gate_X : forall p c, is_supported c -> is_supported (db_gate (U _X) p c)
  | suported_gate_Y : forall p c, is_supported c -> is_supported (db_gate (U _Y) p c)
  | suported_gate_Z : forall p c, is_supported c -> is_supported (db_gate (U _Z) p c)
  | suported_gate_R : forall p c ϕ, is_supported c -> is_supported (db_gate (U (_R_ ϕ)) p c)
  | suported_gate_CNOT : forall p c, is_supported c -> is_supported (db_gate (U (ctrl _X)) p c)
  | supported_measQ : forall p c, is_supported c -> is_supported (db_gate measQ p c).

(* Compilation is correct. 
   - The true/false flag to denote_db_circuit doesn't matter because we don't 
     currently handle asserts.
   - The Types_DB assumption may not be the right assumption, but we need something
     like this. *)
Lemma compile_correct : forall {W : WType} (c : DeBruijn_Circuit W) (Γ : Ctx),
  Types_DB Γ c ->
  is_supported c ->
  c_eval (⟦ Γ ⟧) (compile_from_db_circuit c) = denote_db_circuit false 0 (⟦ Γ ⟧) c.
Proof. 
Admitted.

(* Example - unitary superdense coding *)
(* TODO - Fix scoping issue. Why doesn't Open Scope circ_scope work? *)
Local Close Scope com_scope.
Local Open Scope circ_scope.

Definition bell00 : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  box_ (p,q) ⇒ (ctrl _X) $ (_H $ p, q).

(*
Definition encode (b1 b2 : bool) : Box Qubit Qubit :=
  box_ e ⇒ let_ e ← (if b2 then _X else _I) $ e;
           (if b1 then _Z else _I) $ e.
*)
Definition encode (b1 b2 : bool) : Box Qubit Qubit :=
  box_ e ⇒ compose ((if b2 then _X else id_circ) $ e)
                   (fun e => (if b1 then _Z else id_circ) $ e).

(*
Definition decode : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  box_ qs ⇒ let_ (x,y) ← (ctrl _X) $ qs; (_H $ x, y).
*)
Definition decode : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  box_ qs ⇒ compose ((ctrl _X) $ qs) 
                    (fun z => letpair x y z (_H $ x, y)).

(*
Definition superdense (b1 b2: bool) : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  box_ (a,b) =>
    let_ (a,b) <- bell00 $ (a,b);
    let_ q     <- encode b1 b2 $ a;
    decode $ (q,b).
*)
Definition superdense (b1 b2: bool) : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  box_ (a,b) ⇒
    compose (bell00 $ (a,b))
            (fun ab => letpair a b ab (compose (encode b1 b2 $ a) 
                                            (fun q => (decode $ (q,b))))).

Definition superdense_circ := match (hoas_to_db_box (superdense true true)) with
                              | db_box _ c => c
                              end.
Compute (compile_from_db_circuit superdense_circ).