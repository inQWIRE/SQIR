open Qasm2sqir
open Printf
open Unix

open UnitaryListRepresentation
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

(* Counts Clifford rotation gates (multiples of pi/2). *)
let is_multiple_of_2 a =
  let prod = Q.mul a (Q.of_int 2) in
  let den = Q.den prod in
  Z.equal den (Z.of_int 1)
 
let rec get_clifford_rot_count' l acc = 
  match l with
  | [] -> acc
  | App1 (RzQGateSet.URzQ_Rz(a), _) :: t ->
      if is_multiple_of_2 a 
      then get_clifford_rot_count' t (1 + acc) 
      else get_clifford_rot_count' t acc
  | _ :: t -> get_clifford_rot_count' t acc;;
  
let get_clifford_rot_count l = get_clifford_rot_count' l 0;;

(* light argument parsing *)
let niter = ref 1
let fname = ref ""
let outf = ref ""
let usage = "usage: " ^ Sys.argv.(0) ^ " [-i string] [-o string] [-n int]"
let speclist = [
    ("-i", Arg.Set_string fname, ": input filename");
    ("-o", Arg.Set_string outf, ": output filename");
    ("-n", Arg.Set_int niter, ": number of iterations");
  ]
let () =
  Arg.parse
    speclist
    (fun x -> raise (Arg.Bad ("Bad argument : " ^ x)))
    usage;
if !fname = "" then printf "Input filename required.\n%!" else 
let _ = if !outf = "" then outf := !fname ^ "_opt" else () in
let _ = printf "Input file: %s\nOutput file: %s\n%!" !fname !outf in
let _ = if !niter > 2 then printf "Number of iterations: %d\n%!" !niter else () in
let t1 = Unix.gettimeofday () in
let (p, n) = get_gate_list !fname in
let _ = printf "Time to parse: %fs\n" (Unix.gettimeofday () -. t1) in
let origTotal = List.length p in
let origRz = get_rz_count p in
let origCliff = get_clifford_rot_count p in
let origT = match get_t_count p with
            | None -> "N/A"
            | Some x -> string_of_int x in
let origH = get_h_count p in
let origX = get_x_count p in
let origCNOT = get_cnot_count p in
if !niter < 3 
then 
  let _ = printf "Original:\t Total %d, Rz %d, Clifford %d, T %s, H %d, X %d, CNOT %d\n%!" 
            origTotal origRz origCliff origT origH origX origCNOT in
  let t2 = Unix.gettimeofday () in
  let p' = optimize p in
  let _ = printf "Time to optimize: %fs\n" (Unix.gettimeofday () -. t2) in
  let finalTotal = List.length p' in
  let finalRz = get_rz_count p' in
  let finalCliff = get_clifford_rot_count p' in
  let finalT = match get_t_count p' with
               | None -> "N/A"
               | Some x -> string_of_int x in
  let finalH = get_h_count p' in
  let finalX = get_x_count p' in
  let finalCNOT = get_cnot_count p' in
  let _ = printf "Final:\t Total %d, Rz %d, Clifford %d, T %s, H %d, X %d, CNOT %d\n%!" 
            finalTotal finalRz finalCliff finalT finalH finalX finalCNOT in
  let t3 = Unix.gettimeofday () in
  (write_qasm_file !outf p' n;
   printf "Time to write out: %fs\n" (Unix.gettimeofday () -. t3))
else 
  let _ = printf "Original (n iter.):\t Total %d, Rz %d, Clifford %d, H %d, X %d, CNOT %d\n%!" 
            (!niter * origTotal) (!niter * origRz) (!niter * origCliff) (!niter * origH) (!niter * origX) (!niter * origCNOT) in
  let t2 = Unix.gettimeofday () in
  match optimize_lcr p with
     | Some ((l, c), r) ->
         let _ = printf "Time to optimize: %fs\n" (Unix.gettimeofday () -. t2) in
         let finalTotal = (List.length l) + (!niter - 2) * (List.length c) + (List.length r)  in
         let finalRz = (get_rz_count l) + (!niter - 2) * (get_rz_count c) + (get_rz_count r) in
         let finalCliff = (get_clifford_rot_count l) + (!niter - 2) * (get_clifford_rot_count c) + (get_clifford_rot_count r) in
         let finalH = (get_h_count l) + (!niter - 2) * (get_h_count c) + (get_h_count r) in
         let finalX = (get_x_count l) + (!niter - 2) * (get_x_count c) + (get_x_count r) in
         let finalCNOT = (get_cnot_count l) + (!niter - 2) * (get_cnot_count c) + (get_cnot_count r) in
         let _ = printf "Final (n iter. w/ LCR):\t Total %d, Rz %d, Clifford %d, H %d, X %d, CNOT %d\n%!" 
                   finalTotal finalRz finalCliff finalH finalX finalCNOT in
         let t3 = Unix.gettimeofday () in
         (write_qasm_file (!outf ^ "_L") l n;
          write_qasm_file (!outf ^ "_C") c n;
          write_qasm_file (!outf ^ "_R") r n;
          printf "Time to write out: %fs\n" (Unix.gettimeofday () -. t3))
     | _ -> printf "LCR optimization failed.\n%!"

   
