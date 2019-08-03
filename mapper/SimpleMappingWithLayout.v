Require Import SimpleMapping.

Local Close Scope C_scope.
Local Close Scope R_scope.

(** Simple Mapping Extended with Layouts - WORK IN PROGRESS **)

(* This extends the simple mapping approach with a mapping between
   logical and physical qubits. In SimpleMapping, we moved logical 
   qubits to be adjacent before a CNOT and then moved them back to 
   their original locations before continuing. In practice, this is
   very inefficient. It is better to leave the logical qubits in their 
   new positions, and continue from there. *)

(* We will represent a layout with two functions: one that maps from
   logical qubits to physcial qubits, and one that maps from physical
   qubits to logical qubits. We use two functions instead of one to 
   make lookup in either direction efficient. However, this requires
   some extra machinery to describe well-formed layouts. *)
Definition qmap (dim : nat) : Type := (nat -> nat) * (nat -> nat).

Definition log2phys {dim} (m : qmap dim) q :=
  match m with
  | (m, _) => m q
  end.

Definition phys2log {dim} (m : qmap dim) q :=
  match m with
  | (_, m) => m q
  end.

(* Swap the logical qubits associated with physical qubits phys1 and phys2. *)
Definition swap_in_map {dim} (m : qmap dim) phys1 phys2 : qmap dim :=
  match m with
  | (m1, m2) => 
      let log1 := m2 phys1 in
      let log2 := m2 phys2 in
      let m1' q := if q =? log1 then phys2
                   else if q =? log2 then phys1 
                   else m1 q in
      let m2' q := if q =? phys1 then log2 
                   else if q =? phys2 then log1 
                   else m2 q in
      (m1', m2')
  end.

(* Copied from Coq.Logic.FinFun *)
Definition bFun n (f : nat -> nat) := forall x, x < n -> f x < n.
Definition bInjective n (f : nat -> nat) :=
 forall x y, x < n -> y < n -> f x = f y -> x = y.

Definition bInverse n (f g : nat -> nat) := 
  (forall x, x < n -> g (f x) = x) /\ (forall y, y < n -> f (g y) = y).

(* Is there a more succinct way to write this? *)
Definition layout_well_formed {dim} (m : qmap dim) := 
  bFun dim (log2phys m) /\
  bFun dim (phys2log m) /\
  bInjective dim (log2phys m) /\
  bInjective dim (phys2log m) /\
  bInverse dim (log2phys m) (phys2log m).

(* Mapping function definition. *)

Fixpoint path_to_swaps dim p m : (ucom dim * qmap dim) :=
  match p with
  | n1 :: n2 :: [] => (uskip, m) (* normal termination *)
  | n1 :: ((n2 :: _) as t) => 
      let (c, m') := path_to_swaps dim t (swap_in_map m n1 n2) in
      (SWAP n1 n2 ; c, m')
  | _ => (uskip, m) (* bad input case *)
  end.

Fixpoint simple_map_w_layout {dim} (c : ucom dim) (m : qmap dim) (get_path : nat -> nat -> list nat) (is_in_graph_b : nat -> nat -> bool) :=
  match c with
  | c1; c2 => let (c1', m') := simple_map_w_layout c1 m get_path is_in_graph_b in
             let (c2', m'') := simple_map_w_layout c2 m' get_path is_in_graph_b in
             (c1'; c2', m'')
  | uapp_CNOT n1 n2 => 
      let p := get_path (log2phys m n1) (log2phys m n2) in
      let (c', m') := path_to_swaps dim p m in
      let c'' := fix_cnots (c'; CNOT (log2phys m' n1) (log2phys m' n2)) is_in_graph_b in
      (c'', m')
  | uapp_R θ ϕ λ n => (uapp_R θ ϕ λ (log2phys m n), m)
  | _ => (c, m)
  end.  

(* For soundness we will want to prove that the resulting program is equivalent
   to the input program if you 'undo' all the SWAPs. To state this, we need a 
   way to produce a series of SWAPs that converts between layouts. *)

(* If the m1 has logical qubit A at physical qubit 0 and m2 has A at 3, 
   then convert_between_layouts should produce a program that swaps the
   values at locations 0 and 3. Note that we don't worry about satisfying
   connectivity constraints because the generated program is used in our
   proof - it is not meant to be run on a machine. *)
Fixpoint convert_between_layouts' {dim} n (m1 m2 : qmap dim) : ucom dim :=
  match n with 
  | O => uskip
  | S n' => 
      let x := log2phys m1 (phys2log m2 n') in
      if n' =? x 
      then convert_between_layouts' n' m1 m2
      else SWAP n' x ; convert_between_layouts' n' (swap_in_map m1 n' x) m2
  end.

Definition convert_between_layouts {dim} (m1 m2 : qmap dim) : ucom dim :=
  convert_between_layouts' dim m1 m2.

(* Example *)
Definition trivial_layout : qmap 5 := (fun x => x, fun x => x).
Definition test_layout1 : qmap 5 := 
  let l2p q := if q =? 0 then 4
               else if q =? 1 then 2
                    else if q =? 2 then 3
                         else if q =? 3 then 0
                              else 1 in
  let p2l q := if q =? 0 then 3
               else if q =? 1 then 4
                    else if q =? 2 then 1
                         else if q =? 3 then 2
                              else 0 in
  (l2p, p2l).
Compute (convert_between_layouts trivial_layout test_layout1).
Compute (convert_between_layouts test_layout1 trivial_layout).
Compute (convert_between_layouts test_layout1 test_layout1).

(* The statements of correctness will probably look like the following: *)
Lemma simple_map_w_layout_sound : forall dim (c : ucom dim) (m : qmap dim) get_path is_in_graph is_in_graph_b c' m',
  valid_graph dim is_in_graph ->
  get_path_valid dim get_path is_in_graph ->
  (forall n1 n2, reflect (is_in_graph n1 n2) (is_in_graph_b n1 n2)) ->
  uc_well_typed c ->
  layout_well_formed m ->
  simple_map_w_layout c m get_path is_in_graph_b = (c', m') -> 
  (c' ; convert_between_layouts m' m) ≡ (map_qubits (log2phys m) c).
Proof. Admitted.

Lemma simple_map_w_layout_respect_constraints : forall dim (c : ucom dim) (m : qmap dim) get_path is_in_graph is_in_graph_b c' m',
  valid_graph dim is_in_graph ->
  get_path_valid dim get_path is_in_graph ->
  (forall n1 n2, reflect (is_in_graph n1 n2) (is_in_graph_b n1 n2)) ->
  uc_well_typed c ->
  layout_well_formed m ->
  simple_map_w_layout c m get_path is_in_graph_b = (c', m') -> 
  respects_constraints is_in_graph c'.
Proof. Admitted.




Definition map_to_tenerife_w_layout (c : ucom 5) (m : qmap 5) :=
  simple_map_w_layout c m tenerife_get_path tenerife_is_in_graph_b.

Compute (map_to_tenerife_w_layout test_tenerife1 trivial_layout).
Compute (map_to_tenerife_w_layout test_tenerife1 test_layout1).
Compute (map_to_tenerife_w_layout test_tenerife2 trivial_layout).
Compute (map_to_tenerife_w_layout test_tenerife2 test_layout1).
Compute (map_to_tenerife_w_layout test_tenerife3 trivial_layout).
Compute (map_to_tenerife_w_layout test_tenerife3 test_layout1).

(* Represent a layout as a list where element x at index i indicates
   that logical qubit x is located at physical qubit i.  *)
Fixpoint layout_to_list' {dim} n (m : qmap dim) :=
  match n with 
  | O => []
  | S n' => (layout_to_list' n' m) ++ [phys2log m n'] 
  end.
Definition layout_to_list {dim} (m : qmap dim) := layout_to_list' dim m.

Compute (layout_to_list trivial_layout).
Compute (layout_to_list test_layout1).

Fixpoint layout_from_list' n l :=
  match l with 
  | [] => (fun x => x, fun x => x)
  | h :: t => let (l2p, p2l) := layout_from_list' (n+1) t in
            let l2p' x := if x =? h then n else l2p x in
            let p2l' x := if x =? n then h else p2l x in
            (l2p', p2l')   
  end.
Definition layout_from_list dim l : (qmap dim) := layout_from_list' 0 l.

Compute (layout_to_list (layout_from_list 5 (3 :: 4 :: 1 :: 2 :: 0 :: []))).