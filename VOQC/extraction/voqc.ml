open Qasm2sqir
open Printf

open ListRepresentation
open RzQGateSet
open Optimize

let get_rz_count l = 
  let f a x = match x with
              | App1 (RzQGateSet.URzQ_Rz(_), _) -> a + 1
              | _ -> a in
  List.fold_left f 0 l;;

let rec get_x_count l = 
  let f a x = match x with
              | App1 (RzQGateSet.URzQ_X, _) -> a + 1
              | _ -> a in
  List.fold_left f 0 l;;
  
let rec get_h_count l = 
  let f a x = match x with
              | App1 (RzQGateSet.URzQ_H, _) -> a + 1
              | _ -> a in
  List.fold_left f 0 l;;
  
let rec get_cnot_count l = 
  let f a x = match x with
              | App2 (RzQGateSet.URzQ_CNOT, _, _) -> a + 1
              | _ -> a in
  List.fold_left f 0 l;;

(* Returns (Some true) if a is an odd multiple of 1/4 and (Some false) if a 
   is an even mulitple of 1/4. Returns None if a does not correspond to a 
   rotation by 1/4. *)
let is_odd_multiple_of_1_4 a =
  let prod = Q.mul a (Q.of_int 4) in
  let (num, den) = (Q.num prod, Q.den prod) in
  if Z.equal den (Z.of_int 1)
  then Some (Z.equal (Z.rem num (Z.of_int 2)) Z.one) 
  else None;;

(* Only relevant for the benchmarks using the Clifford+T set. *)
let rec get_t_count' l acc = 
  match l with
  | [] -> Some acc
  | App1 (RzQGateSet.URzQ_Rz(a), _) :: t ->
      (match is_odd_multiple_of_1_4 a with
       | Some true -> get_t_count' t (1 + acc)
       | Some false -> get_t_count' t acc
       | None -> None)
  | _ :: t -> get_t_count' t acc;;
  
let get_t_count l = get_t_count' l 0;;

if (Array.length Sys.argv <> 3)
then print_endline "Expected usage: voqc <prog> <out>"
else let fname = Sys.argv.(1) in
     let outf = Sys.argv.(2) in
     let _ = printf "./voqc %s %s\n" fname outf in
     let (p, n) = get_gate_list fname in
     let origT = match get_t_count p with
                 | None -> "N/A"
                 | Some x -> string_of_int x in
     let _ = printf "Original:\t Total %d, Rz %d, T %s, H %d, X %d, CNOT %d\n%!" 
               (List.length p) (get_rz_count p) origT (get_h_count p) (get_x_count p) (get_cnot_count p) in
     let p' = optimize p in
     let finalT = match get_t_count p' with
                 | None -> "N/A"
                 | Some x -> string_of_int x in
     printf "Final:\t Total %d, Rz %d, T %s, H %d, X %d, CNOT %d\n\n%!" 
               (List.length p') (get_rz_count p') finalT (get_h_count p') (get_x_count p') (get_cnot_count p');
     write_qasm_file outf p' n

   
