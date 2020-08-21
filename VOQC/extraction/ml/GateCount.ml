open UnitaryListRepresentation
open RzQGateSet
let get_rz_count l = 
  let f a x = match x with
              | App1 (RzQGateSet.URzQ_Rz(_), _) -> a + 1
              | _ -> a in
  List.fold_left f 0 l;;

let get_x_count l = 
  let f a x = match x with
              | App1 (RzQGateSet.URzQ_X, _) -> a + 1
              | _ -> a in
  List.fold_left f 0 l;;
  
let get_h_count l = 
  let f a x = match x with
              | App1 (RzQGateSet.URzQ_H, _) -> a + 1
              | _ -> a in
  List.fold_left f 0 l;;
  
let get_cnot_count l = 
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

