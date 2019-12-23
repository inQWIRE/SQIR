
val xorb : bool -> bool -> bool

val negb : bool -> bool

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val add : int -> int -> int

val mul : int -> int -> int

val eqb : bool -> bool -> bool

module Nat :
 sig
  val ltb : int -> int -> bool
 end

val rev : 'a1 list -> 'a1 list

val forallb : ('a1 -> bool) -> 'a1 list -> bool

module Pos :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val pred_double : int -> int

  val compare_cont : comparison -> int -> int -> comparison

  val compare : int -> int -> comparison

  val eqb : int -> int -> bool
 end

module Z :
 sig
  val double : int -> int

  val succ_double : int -> int

  val pred_double : int -> int

  val pos_sub : int -> int -> int

  val add : int -> int -> int

  val opp : int -> int

  val sub : int -> int -> int

  val compare : int -> int -> comparison

  val ltb : int -> int -> bool

  val eqb : int -> int -> bool
 end

val inb : int -> int list -> bool

type 'u gate_app =
| App1 of 'u * int
| App2 of 'u * int * int
| App3 of 'u * int * int * int

type 'u gate_list = 'u gate_app list

val uc_well_typed_l_b : int -> 'a1 gate_list -> bool

val next_single_qubit_gate :
  'a1 gate_list -> int -> (('a1 gate_list * 'a1) * 'a1 gate_list) option

val last_single_qubit_gate :
  'a1 gate_list -> int -> (('a1 gate_list * 'a1) * 'a1 gate_list) option

val next_two_qubit_gate :
  'a1 gate_list -> int -> (((('a1 gate_list * 'a1) * int) * int) * 'a1
  gate_list) option

val next_gate :
  'a1 gate_list -> int list -> (('a1 gate_list * 'a1 gate_app) * 'a1
  gate_list) option

val does_not_reference_appl : int -> 'a1 gate_app -> bool

val does_not_reference : 'a1 gate_list -> int -> bool

val try_rewrites :
  'a1 gate_list -> ('a1 gate_list -> 'a1 gate_list option) list -> 'a1
  gate_list option

val try_rewrites2 :
  'a1 gate_list -> ('a1 gate_list -> ('a1 gate_list * 'a1 gate_list) option)
  list -> ('a1 gate_list * 'a1 gate_list) option

val propagate :
  'a1 gate_list -> ('a1 gate_list -> ('a1 gate_list * 'a1 gate_list) option)
  list -> ('a1 gate_list -> 'a1 gate_list option) list -> int -> 'a1
  gate_list option

type 'u single_qubit_pattern = 'u list

val single_qubit_pattern_to_program :
  'a1 single_qubit_pattern -> int -> 'a1 gate_list

val remove_single_qubit_pattern :
  'a1 gate_list -> int -> 'a1 single_qubit_pattern -> ('a1 -> 'a1 -> bool) ->
  'a1 gate_list option

val replace_single_qubit_pattern :
  'a1 gate_list -> int -> 'a1 single_qubit_pattern -> 'a1
  single_qubit_pattern -> ('a1 -> 'a1 -> bool) -> 'a1 gate_list option

type pI4_Unitary =
| UPI4_H
| UPI4_X
| UPI4_PI4 of int
| UPI4_CNOT

val uPI4_T : pI4_Unitary

val uPI4_P : pI4_Unitary

val uPI4_Z : pI4_Unitary

val uPI4_PDAG : pI4_Unitary

val uPI4_TDAG : pI4_Unitary

val t : int -> pI4_Unitary gate_app

val tDAG : int -> pI4_Unitary gate_app

val p : int -> pI4_Unitary gate_app

val pDAG : int -> pI4_Unitary gate_app

val z : int -> pI4_Unitary gate_app

val h : int -> pI4_Unitary gate_app

val x : int -> pI4_Unitary gate_app

val cNOT : int -> int -> pI4_Unitary gate_app

type pI4_ucom_l = pI4_Unitary gate_list

val cCX : int -> int -> int -> pI4_ucom_l

val cCZ : int -> int -> int -> pI4_ucom_l

val match_gate : pI4_Unitary -> pI4_Unitary -> bool

val pI4_list_well_typed_b : int -> pI4_ucom_l -> bool

val rz_commute_rule1 :
  int -> pI4_ucom_l -> (pI4_Unitary gate_app list * pI4_Unitary gate_list)
  option

val rz_commute_rule2 :
  int -> pI4_ucom_l -> (pI4_Unitary gate_app list * pI4_Unitary gate_list)
  option

val rz_commute_rule3 :
  int -> pI4_ucom_l -> (pI4_Unitary gate_app list * pI4_Unitary gate_list)
  option

val rz_commute_rules :
  int -> (pI4_ucom_l -> (pI4_Unitary gate_app list * pI4_Unitary gate_list)
  option) list

val rz_cancel_rule :
  int -> int -> pI4_ucom_l -> pI4_Unitary gate_app list option

val h_cancel_rule : int -> pI4_ucom_l -> pI4_Unitary gate_app list option

val x_commute_rule :
  int -> pI4_ucom_l -> (pI4_Unitary gate_app list * pI4_Unitary gate_list)
  option

val x_cancel_rule : int -> pI4_ucom_l -> pI4_Unitary gate_app list option

val cNOT_commute_rule1 : int -> pI4_ucom_l -> (pI4_ucom_l * pI4_ucom_l) option

val cNOT_commute_rule2 :
  int -> int -> pI4_ucom_l -> (pI4_Unitary gate_app list * pI4_Unitary
  gate_list) option

val cNOT_commute_rule3 :
  int -> int -> pI4_ucom_l -> (pI4_Unitary gate_app list * pI4_Unitary
  gate_list) option

val cNOT_commute_rule4 :
  int -> int -> pI4_ucom_l -> (pI4_Unitary gate_app list * pI4_Unitary
  gate_app list) option

val cNOT_commute_rules :
  int -> int -> (pI4_ucom_l -> (pI4_ucom_l * pI4_ucom_l) option) list

val cNOT_cancel_rule :
  int -> int -> pI4_ucom_l -> pI4_Unitary gate_app list option

val propagate_PI4 :
  int -> pI4_ucom_l -> int -> int -> pI4_Unitary gate_list option

val propagate_H : pI4_ucom_l -> int -> pI4_Unitary gate_list option

val propagate_X : pI4_ucom_l -> int -> int -> pI4_Unitary gate_list option

val propagate_CNOT :
  pI4_ucom_l -> int -> int -> int -> pI4_Unitary gate_list option

val cancel_single_qubit_gates' : pI4_ucom_l -> int -> pI4_ucom_l

val cancel_single_qubit_gates : pI4_ucom_l -> pI4_ucom_l

val cancel_two_qubit_gates' : pI4_ucom_l -> int -> pI4_ucom_l

val cancel_two_qubit_gates : pI4_ucom_l -> pI4_ucom_l

val apply_H_equivalence1 : int -> pI4_ucom_l -> pI4_Unitary gate_list option

val apply_H_equivalence2 : int -> pI4_ucom_l -> pI4_Unitary gate_list option

val apply_H_equivalence3 :
  int -> pI4_ucom_l -> pI4_Unitary gate_app list option

val apply_H_equivalence4 :
  int -> pI4_ucom_l -> pI4_Unitary gate_app list option

val apply_H_equivalence5 :
  int -> pI4_ucom_l -> pI4_Unitary gate_app list option

val apply_H_equivalence : pI4_ucom_l -> int -> pI4_ucom_l option

val apply_H_equivalences : pI4_ucom_l -> int -> pI4_ucom_l

val hadamard_reduction : pI4_ucom_l -> pI4_ucom_l

val update : (int -> 'a1) -> int -> 'a1 -> int -> 'a1

val add0 : int -> int list -> int list

val get_subcircuit' :
  pI4_ucom_l -> int list -> int list -> int -> (pI4_Unitary gate_app
  list * pI4_Unitary gate_app list) * pI4_ucom_l

val get_subcircuit :
  pI4_ucom_l -> int -> (pI4_Unitary gate_app list * pI4_Unitary gate_app
  list) * pI4_ucom_l

val f_eqb : (int -> bool) -> (int -> bool) -> int -> bool

val neg : (int -> bool) -> int -> int -> bool

val xor : (int -> bool) -> (int -> bool) -> int -> bool

val merge' :
  int -> pI4_ucom_l -> int list -> int -> int -> (int -> int -> bool) ->
  pI4_Unitary gate_app list option

val merge :
  int -> pI4_ucom_l -> int -> int -> pI4_Unitary gate_app list option

val merge_rotation :
  int -> pI4_ucom_l -> int -> int -> pI4_Unitary gate_app list option

val merge_rotations' : int -> pI4_ucom_l -> int -> pI4_ucom_l

val merge_rotations : int -> pI4_ucom_l -> pI4_ucom_l

val propagate_Z : pI4_ucom_l -> int -> int -> pI4_Unitary gate_app list

val propagate_X0 : pI4_ucom_l -> int -> int -> pI4_Unitary gate_app list

val not_propagation' : pI4_ucom_l -> int -> pI4_ucom_l

val not_propagation : pI4_ucom_l -> pI4_ucom_l

val optimize : int -> pI4_ucom_l -> pI4_ucom_l

val optimize_check_for_type_errors : int -> pI4_ucom_l -> pI4_ucom_l option
