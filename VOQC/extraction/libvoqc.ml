open Optimize
open Qasm2sqir
open GateCount

(* Input/output values are pairs of (circuit * number of qubits).
   The reason we track number of qubits is because it's used by our (naive) write_qasm function.
   Note that none of our current optimizations change the number of qubits used.  *)

let () = Callback.register "optimize" (fun v -> (optimize (fst v), snd v))
let () = Callback.register "write_qasm_file" (fun s v -> write_qasm_file s (fst v) (snd v))
let () = Callback.register "read_qasm_file" get_gate_list 
let () = Callback.register "x_count" (fun v -> get_x_count (fst v))
let () = Callback.register "h_count" (fun v -> get_h_count (fst v))
let () = Callback.register "rz_count" (fun v -> get_rz_count (fst v))
let () = Callback.register "cnot_count" (fun v -> get_cnot_count (fst v))
let () = Callback.register "t_count" (fun v -> match get_t_count (fst v) with Some n -> n | _ -> -1)
let () = Callback.register "c_count" (fun v -> get_clifford_rot_count (fst v))
let () = Callback.register "total_count" (fun v -> List.length (fst v))