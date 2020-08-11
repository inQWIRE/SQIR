open GateCancellation
open HadamardReduction
open NotPropagation
open RotationMerging
open Optimize
open Qasm2sqir
open GateCount

let optimizer a =
  let optim_circuit = optimize (fst a) in
  optim_circuit, (snd a)
                 
let not_p a =
  let optim_circuit = not_propagation (fst a) in
  optim_circuit, (snd a)

let single a =
  let optim_circuit = cancel_single_qubit_gates (fst a) in
  optim_circuit, (snd a)
                 
let two a =
  let optim_circuit = cancel_two_qubit_gates (fst a) in
  optim_circuit, (snd a)

let merge a =
  let optim_circuit = merge_rotations (fst a) in
  optim_circuit, (snd a)
                 
let hadamard a =
  let optim_circuit = hadamard_reduction (fst a) in
  optim_circuit, (snd a)

let write_qasm a b =
  write_qasm_file a (fst b) (snd b)

let x_c a =
  get_x_count (fst a)

let h_c a =
  get_h_count (fst a)

let rz_c a =
  get_rz_count (fst a)

let cnot_c a =
  get_cnot_count (fst a)

let t_c a =
  let t = get_t_count (fst a) in
  match t with
  |None -> "N/A"
  |Some x -> string_of_int x

let cliff_c a =
  get_clifford_rot_count (fst a)

let tot a =
  List.length (fst a)
