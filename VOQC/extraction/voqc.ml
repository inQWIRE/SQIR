open Qasm2sqir
open Printf

module E = ExtractedCode

(* Only relevant for the benchmarks using the Clifford+T set! *)
let rec get_t_count l = 
  match l with
  | [] -> 0
  | E.App1 (E.URzk_Rz(k), _) :: t -> 
      let inc = match k with
                | 8192 | 24576 | 40960 | 57344 -> 1
                | _ -> 0 in
      inc + get_t_count t
  | _ :: t -> get_t_count t;;

if (Array.length Sys.argv <> 3)
then print_endline "Expected usage: voqc <prog> <out>"
else let fname = Sys.argv.(1) in
     let outf = Sys.argv.(2) in
     let _ = printf "./voqc %s %s\n" fname outf in
     let (p, n) = get_gate_list fname in
     let p' = E.optimize p in
     printf "Original gates: %d (T count: %d)\nOptimized gates: %d (T count: %d)\n\n%!" (List.length p) (get_t_count p) (List.length p') (get_t_count p'); 
     write_qasm_file outf p' n

   
