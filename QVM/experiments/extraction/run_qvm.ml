open Printf

open AltGateSet2
open AltVSQIR

(* Goal: Generate circuits for the following .... 

    bc2ucom (ModMult.modmult_rev m c cinv n)
    trans_pexp (RZArith.rz_modmult_full y x n c a ainv n0)
    trans_pexp (CLArith.modmult_rev m c cinv n x y z s c1 c2)
    
c and m are random 16-bit primes from this website: https://asecuritysite.com/encryption/random3?val=16

*)

(* write to qasm file *)
let rec sqir_to_qasm oc (u : coq_U ucom) k =
  match u with
  | Coq_useq (u1, u2) -> sqir_to_qasm oc u1 (fun _ -> sqir_to_qasm oc u2 k)
  | Coq_uapp (1, U_X, [a]) -> (fprintf oc "x q[%d];\n" a ; k ())
  | Coq_uapp (1, U_H, [a]) -> (fprintf oc "h q[%d];\n" a ; k ())
  | Coq_uapp (1, U_U1 (r), [a]) -> (fprintf oc "u1(%f) q[%d];\n" r a ; k ())
  | Coq_uapp (1, U_U2 (r1,r2), [a]) -> (fprintf oc "u2(%f,%f) q[%d];\n" r1 r2 a ; k ())
  | Coq_uapp (1, U_U3 (r1,r2,r3), [a]) -> (fprintf oc "u3(%f,%f,%f) q[%d];\n" r1 r2 r3 a ; k ())
  | Coq_uapp (2, U_CX, [a;b]) -> (fprintf oc "cx q[%d], q[%d];\n" a b ; k ())
  | Coq_uapp (3, U_CCX, [a;b;c]) -> (fprintf oc "ccx q[%d], q[%d], q[%d];\n" a b c ; k ())
  | _ -> raise (Failure ("ERROR: Failed to write qasm file")) (* badly typed case (e.g. App2 of U_H) *)

(* inserting measurement to get simulation results *)
let rec write_measurements oc dim =
  if dim = 0 then ()
  else (write_measurements oc (dim - 1) ; fprintf oc "measure q[%d] -> c[%d];\n" (dim - 1) (dim - 1))

let write_qasm_file fname (u : coq_U ucom) dim =
  let oc = open_out fname in
  (fprintf oc "OPENQASM 2.0;\ninclude \"qelib1.inc\";\n\n";
   fprintf oc "qreg q[%d];\n" dim;
   fprintf oc "creg c[%d];\n" dim;
   fprintf oc "\n";
   ignore(sqir_to_qasm oc u (fun _ -> ()));
   ignore(write_measurements oc dim);
   ignore(fprintf oc "\n"); (* ddsim is fussy about having a newline at the end *)
   close_out oc)

(* function to count gates *)
let rec count_gates_aux (u : coq_U ucom) acc =
  match u with
  | Coq_useq (u1, u2) -> count_gates_aux u1 (count_gates_aux u2 acc)
  | Coq_uapp (_, _, _) -> 1 + acc
let count_gates u = count_gates_aux u 0

let c = 7;;
let cinv = 13;;
let m = 15;;
let n = 5;; (* number of bits needed + 1 *)

let id_nat = fun i : int -> i;;
let vars_for_rz = fun x -> if x = 0 then (((0, n), id_nat), id_nat)
                           else if x = 1 then (((n, n), id_nat), id_nat)
                           else if x = 2 then (((2 * n, 1), id_nat), id_nat)
                           else (((0, 0), id_nat), id_nat);;
let vars_for_cl = fun x -> if x = 0 then (((0, n), id_nat), id_nat)
                           else if x = 1 then (((n, n), id_nat), id_nat)
                           else if x = 2 then (((2 * n, n), id_nat), id_nat)
                           else if x = 3 then (((3 * n, n), id_nat), id_nat)
                           else if x = 4 then (((3 * n, 2), id_nat), id_nat)
                           else (((0, 0), id_nat), id_nat);;
let dim_for_rz = 2 * n + 1;;
let dim_for_cl = 4 * n + 2;;
let avs_for_both = fun x -> (x/n, x mod n);;

let dim_for_old = 4 * n + 11;; (* I think? -KH *)

printf "Generating circuit for ModMult.modmult_rev...\n%!";;
let old_circ = bc2ucom (ModMult.modmult_rev m c cinv n);;
printf "\t%d gates\n%!" (count_gates old_circ);;
write_qasm_file "old_circ.qasm" old_circ dim_for_old;;

printf "Generating circuit for RZArith.rz_modmult_full...\n%!";;
let rz_circ = trans_pexp vars_for_rz dim_for_rz (RZArith.rz_modmult_full 0 1 n (2,0) c cinv m) avs_for_both;;
printf "\t%d gates\n%!" (count_gates (fst (fst rz_circ)));;
write_qasm_file "rz_circ.qasm" (fst (fst rz_circ)) dim_for_rz;;

printf "Generating circuit for CLArith.modmult_rev...\n%!";;
let cl_circ = trans_pexp vars_for_cl dim_for_cl (CLArith.modmult_rev (VSQIR.nat2fb m) c cinv n 0 1 2 3 (4,0) (4,1)) avs_for_both;;
printf "\t%d gates\n%!" (count_gates (fst (fst cl_circ)));;
write_qasm_file "cl_circ.qasm" (fst (fst cl_circ)) dim_for_cl;;

printf "Finished\n%!";;