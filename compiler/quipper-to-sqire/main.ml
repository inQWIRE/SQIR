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

(*
let parse f =
  let p = parse_file f in 
    let q = parse_program p in
	  benchmark_to_list q
*)

