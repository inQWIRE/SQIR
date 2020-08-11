open Bindings
open Qasm2sqir
let () = Callback.register "optimizer" optimizer
let () = Callback.register "not_p" not_p
let () = Callback.register "hadamard" hadamard
let () = Callback.register "cancel_two" two
let () = Callback.register "cancel_single" single
let () = Callback.register "merge" merge
let () = Callback.register "write_qasm" write_qasm
let () = Callback.register "get_gate" get_gate_list 
let () = Callback.register "x_c" x_c
let () = Callback.register "h_c" h_c
let () = Callback.register "rz_c" rz_c
let () = Callback.register "cnot_c" cnot_c
let () = Callback.register "t_c" t_c
let () = Callback.register "cliff_c" cliff_c
let () = Callback.register "tot" tot
