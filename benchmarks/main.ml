open Printf
open Ast
open Extracted_code

let parse_file f  =
  let lexbuf = Lexing.from_channel (open_in f) in
  Qparser.program Qlexer.token lexbuf

let get_list l =
  match l with
  | a :: [] -> a
  | _ -> []

let parse_op (o : Ast.op) : benchmark_gate_app list =
  let (ty, id, ctrls) = o in
  let ctrl = get_list ctrls in
	match ty with
    | H -> (match ctrl with
           | [] -> let x = Bench_H id in [x]
           | _ -> [] )
	| X -> (match ctrl with
		| [] -> let x = Bench_X id in [x]
		| a :: [] -> let x = Bench_CNOT (a, id) in [x]
                | a :: b :: [] -> let x = Bench_TOFF (a, b, id) in [x]
                | _ -> [])
    | Z -> (match ctrl with
            | [] -> let x = Bench_Z id in [x]
	    | a :: b :: [] -> let x = Bench_H id in
		    	      let y = Bench_TOFF (a, b, id) in 
		    	      [x; y; x]
	    | _ -> [])

let rec append l1 l2 =
  match l1 with
  | [] -> l2
  | a :: l1' -> a :: append l1' l2

let rec parse_program p =
  match p with
  | [] -> []
  | a :: p' -> let l = parse_op a in
	         let m = parse_program p' in
	           append l m

let parse_gate_list f =
  let p = parse_file f in
    parse_program p

let parse f =
  let q = parse_gate_list f in
    benchmark_to_list q

let benchmark_filenames = [
  "nam_benchmarks/csla_mux_3_before_original";
  "nam_benchmarks/gf2^E7_mult_before";
  "nam_benchmarks/mod_red_21_before";
  "nam_benchmarks/tof_4_before";
  "nam_benchmarks/tof_10_before";
  "nam_benchmarks/qcla_mod_7_before";
  "nam_benchmarks/gf2^E10_mult_before";
  "nam_benchmarks/barenco_tof_10_before";
  "nam_benchmarks/rc_adder_6_before";
  "nam_benchmarks/mod5_4_before";
  "nam_benchmarks/gf2^E9_mult_before";
  (* Results in overflow: *)
  (* "nam_benchmarks/gf2^E163_mult_before"; *)
  "nam_benchmarks/gf2^E5_mult_before";
  "nam_benchmarks/gf2^E8_mult_before";
  "nam_benchmarks/gf2^E64_mult_before";
  "nam_benchmarks/qcla_adder_10_before";
  "nam_benchmarks/adder_8_before";
  "nam_benchmarks/qcla_com_7_before";
  "nam_benchmarks/barenco_tof_3_before";
  "nam_benchmarks/mod_adder_1024_before";
  "nam_benchmarks/mod_mult_55_before";
  "nam_benchmarks/tof_3_before";
  "nam_benchmarks/csum_mux_9_before_corrected";
  (* Results in overflow: *)
  (* "nam_benchmarks/gf2^E131_mult_before"; *)
  "nam_benchmarks/gf2^E32_mult_before";
  "nam_benchmarks/vbe_adder_3_before";
  "nam_benchmarks/barenco_tof_4_before";
  "nam_benchmarks/gf2^E4_mult_before";
  "nam_benchmarks/tof_5_before";
  "nam_benchmarks/barenco_tof_5_before";
  "nam_benchmarks/gf2^E6_mult_before";
  "nam_benchmarks/gf2^E16_mult_before";
  (* Results in overflow: *)
  (* "nam_benchmarks/gf2^E128_mult_before" *)
]

type counts = {h:int; x:int; rz:int; cnot:int; total:int}

let get_counts progs : counts list =
  let tot p = (count_H_gates p) + (count_X_gates p) + (count_rotation_gates p) + (count_CNOT_gates p) in
  List.map (fun p -> {h=count_H_gates p; x=count_X_gates p; rz=count_rotation_gates p; cnot=count_CNOT_gates p; total=tot p}) progs

let benchmarks = List.map (fun x -> parse x) benchmark_filenames

let sqire_to_qasm_gate oc g =
  match g with
  | App1 (FU_H, q) -> fprintf oc "h q%d;\n" q
  | App1 (FU_X, q) -> fprintf oc "x q%d;\n" q
  | App1 (FU_PI4(4), q) -> fprintf oc "z q%d;\n" q
  | App1 (FU_PI4(2), q) -> fprintf oc "s q%d;\n" q
  | App1 (FU_PI4(6), q) -> fprintf oc "sdg q%d;\n" q
  | App1 (FU_PI4(1), q) -> fprintf oc "t q%d;\n" q
  | App1 (FU_PI4(7), q) -> fprintf oc "tdg q%d;\n" q
  | App2 (FU_CNOT, q1, q2) -> fprintf oc "cx q%d, q%d;\n" q1 q2
  | _ -> ()

let benchmark_to_qasm_file b n f =
  let oc = open_out f in
  (fprintf oc "OPENQASM 2.0;\ninclude \"qelib1.inc\";\n\n";
   for i = 0 to n do
     fprintf oc "qreg q%d[1];\n" i
   done;
   fprintf oc "\n";
   ignore(List.map (sqire_to_qasm_gate oc) b);
   close_out oc;
   printf "Done.\n")

let write_all_files () =
  benchmark_to_qasm_file (List.nth benchmarks 0) 14 "qasm_benchmarks/benchmark0.qasm";
  benchmark_to_qasm_file (List.nth benchmarks 1) 20 "qasm_benchmarks/benchmark1.qasm";
  benchmark_to_qasm_file (List.nth benchmarks 2) 10 "qasm_benchmarks/benchmark2.qasm";
  benchmark_to_qasm_file (List.nth benchmarks 3) 6 "qasm_benchmarks/benchmark3.qasm";
  benchmark_to_qasm_file (List.nth benchmarks 4) 18 "qasm_benchmarks/benchmark4.qasm";
  benchmark_to_qasm_file (List.nth benchmarks 5) 25 "qasm_benchmarks/benchmark5.qasm";
  benchmark_to_qasm_file (List.nth benchmarks 6) 29 "qasm_benchmarks/benchmark6.qasm";
  benchmark_to_qasm_file (List.nth benchmarks 7) 18 "qasm_benchmarks/benchmark7.qasm";
  benchmark_to_qasm_file (List.nth benchmarks 8) 13 "qasm_benchmarks/benchmark8.qasm";
  benchmark_to_qasm_file (List.nth benchmarks 9) 4 "qasm_benchmarks/benchmark9.qasm";
  benchmark_to_qasm_file (List.nth benchmarks 10) 26 "qasm_benchmarks/benchmark10.qasm";
  benchmark_to_qasm_file (List.nth benchmarks 11) 14 "qasm_benchmarks/benchmark11.qasm";
  benchmark_to_qasm_file (List.nth benchmarks 12) 23 "qasm_benchmarks/benchmark12.qasm";
  benchmark_to_qasm_file (List.nth benchmarks 13) 191 "qasm_benchmarks/benchmark13.qasm";
  benchmark_to_qasm_file (List.nth benchmarks 14) 35 "qasm_benchmarks/benchmark14.qasm";
  benchmark_to_qasm_file (List.nth benchmarks 15) 23 "qasm_benchmarks/benchmark15.qasm";
  benchmark_to_qasm_file (List.nth benchmarks 16) 23 "qasm_benchmarks/benchmark16.qasm";
  benchmark_to_qasm_file (List.nth benchmarks 17) 4 "qasm_benchmarks/benchmark17.qasm";
  benchmark_to_qasm_file (List.nth benchmarks 18) 27 "qasm_benchmarks/benchmark18.qasm";
  benchmark_to_qasm_file (List.nth benchmarks 19) 8 "qasm_benchmarks/benchmark19.qasm";
  benchmark_to_qasm_file (List.nth benchmarks 20) 4 "qasm_benchmarks/benchmark20.qasm";
  benchmark_to_qasm_file (List.nth benchmarks 21) 29 "qasm_benchmarks/benchmark21.qasm";
  benchmark_to_qasm_file (List.nth benchmarks 22) 95 "qasm_benchmarks/benchmark22.qasm";
  benchmark_to_qasm_file (List.nth benchmarks 23) 9 "qasm_benchmarks/benchmark23.qasm";
  benchmark_to_qasm_file (List.nth benchmarks 24) 6 "qasm_benchmarks/benchmark24.qasm";
  benchmark_to_qasm_file (List.nth benchmarks 25) 11 "qasm_benchmarks/benchmark25.qasm";
  benchmark_to_qasm_file (List.nth benchmarks 26) 8 "qasm_benchmarks/benchmark26.qasm";
  benchmark_to_qasm_file (List.nth benchmarks 27) 8 "qasm_benchmarks/benchmark27.qasm";
  benchmark_to_qasm_file (List.nth benchmarks 28) 17 "qasm_benchmarks/benchmark28.qasm";
  benchmark_to_qasm_file (List.nth benchmarks 29) 47 "qasm_benchmarks/benchmark29.qasm"
(*
(** Small Example Programs **)

(* rm_nots example1 --> [_H 1; _CNOT 2 1] *)
let example1 = [_X 0; _H 1; _X 0;  _X 1; _CNOT 2 1; _X 1]

(* rm_nots example2 --> [_X 0; _X 1; _X 2] *)
let example2 = [_X 0; _X 1; _X 2]

(* next_single_qubit_gate example3 0 --> Some (_X 0, ...) *)
(* next_single_qubit_gate example3 1 --> Some (_H 1, ...) *)
(* next_two_qubit_gate example3 3 --> Some ([_H 1; _X 0], 2, 3, ...) *)
(* replace_single_qubit_pattern example3 0 [_X 0; _X 0] [_H 0; _H 0]
    --> [_H 0; _H 0; _H 1; _CNOT 2 3; _H 0; _P 1; _P 2; _CNOT 0 2] *)
(* replace_single_qubit_pattern example3 0 [_X 0; _H 0] [_H 0; _H 0]
    --> None *)
let example3 = [_H 1; _X 0; _CNOT 2 3; _X 0; _H 0; _P 1; _P 2; _CNOT 0 2]

(* hadamard_reduction example4 --> [_PDAG 1; _H 1; _PDAG 1; _CNOT 3 0; _X 2] *)
let example4 = [_H 1; _H 3; _H 0; _P 1; _CNOT 0 3; _H 0; _H 1; _H 3; _X 2]

(* benchmark_to_list example5 -->
        [App2 (FU_CNOT, 0, 1); App1 (FU_H, 2); App2 (FU_CNOT, 1, 2);
        App1 (FU_TDAG, 2); App2 (FU_CNOT, 0, 2); App1 (FU_T, 2);
        App2 (FU_CNOT, 1, 2); App1 (FU_TDAG, 2); App2 (FU_CNOT, 0, 2);
        App2 (FU_CNOT, 0, 1); App1 (FU_TDAG, 1); App2 (FU_CNOT, 0, 1);
        App1 (FU_T, 0); App1 (FU_T, 1); App1 (FU_T, 2); App1 (FU_H, 2);
        App1 (FU_H, 3); App1 (FU_X, 4)]
*)
let example5 = [Bench_CNOT(0,1); Bench_TOFF(0,1,2); Bench_H(3); Bench_X(4)]
*)
