open Datatypes
open FSetAVL
open OrderedTypeEx
open PeanoNat

module FSet = Make(Nat_as_OT)

type 'u gate_app =
| App1 of 'u * int
| App2 of 'u * int * int
| App3 of 'u * int * int * int

type 'u gate_list = 'u gate_app list

(** val uc_well_typed_l_b : int -> 'a1 gate_list -> bool **)

let rec uc_well_typed_l_b dim = function
| [] -> Nat.ltb 0 dim
| g :: t0 ->
  (match g with
   | App1 (_, n) -> (&&) (Nat.ltb n dim) (uc_well_typed_l_b dim t0)
   | App2 (_, m, n) ->
     (&&) ((&&) ((&&) (Nat.ltb m dim) (Nat.ltb n dim)) (not ((=) m n)))
       (uc_well_typed_l_b dim t0)
   | App3 (_, m, n, p) ->
     (&&)
       ((&&)
         ((&&)
           ((&&)
             ((&&) ((&&) (Nat.ltb m dim) (Nat.ltb n dim)) (Nat.ltb p dim))
             (not ((=) m n))) (not ((=) n p))) (not ((=) m p)))
       (uc_well_typed_l_b dim t0))

(** val next_single_qubit_gate' :
    'a1 gate_list -> int -> 'a1 gate_app list -> (('a1 gate_list * 'a1) * 'a1
    gate_list) option **)

let rec next_single_qubit_gate' l q acc =
  match l with
  | [] -> None
  | g :: t0 ->
    (match g with
     | App1 (u, n) ->
       if (=) n q
       then Some (((List.rev_append acc []), u), t0)
       else next_single_qubit_gate' t0 q ((App1 (u, n)) :: acc)
     | App2 (u, m, n) ->
       if (||) ((=) m q) ((=) n q)
       then None
       else next_single_qubit_gate' t0 q ((App2 (u, m, n)) :: acc)
     | App3 (u, m, n, p) ->
       if (||) ((||) ((=) m q) ((=) n q)) ((=) p q)
       then None
       else next_single_qubit_gate' t0 q ((App3 (u, m, n, p)) :: acc))

(** val next_single_qubit_gate :
    'a1 gate_list -> int -> (('a1 gate_list * 'a1) * 'a1 gate_list) option **)

let next_single_qubit_gate l q =
  next_single_qubit_gate' l q []

(** val last_single_qubit_gate :
    'a1 gate_list -> int -> (('a1 gate_list * 'a1) * 'a1 gate_list) option **)

let last_single_qubit_gate l q =
  match next_single_qubit_gate (List.rev_append l []) q with
  | Some p ->
    let (p0, l2) = p in
    let (l1, u) = p0 in
    Some (((List.rev_append l2 []), u), (List.rev_append l1 []))
  | None -> None

(** val next_two_qubit_gate' :
    'a1 gate_list -> int -> 'a1 gate_app list -> (((('a1
    gate_list * 'a1) * int) * int) * 'a1 gate_list) option **)

let rec next_two_qubit_gate' l q acc =
  match l with
  | [] -> None
  | g :: t0 ->
    (match g with
     | App1 (u, n) ->
       if (=) n q
       then None
       else next_two_qubit_gate' t0 q ((App1 (u, n)) :: acc)
     | App2 (u, m, n) ->
       if (||) ((=) m q) ((=) n q)
       then Some (((((List.rev_append acc []), u), m), n), t0)
       else next_two_qubit_gate' t0 q ((App2 (u, m, n)) :: acc)
     | App3 (u, m, n, p) ->
       if (||) ((||) ((=) m q) ((=) n q)) ((=) p q)
       then None
       else next_two_qubit_gate' t0 q ((App3 (u, m, n, p)) :: acc))

(** val next_two_qubit_gate :
    'a1 gate_list -> int -> (((('a1 gate_list * 'a1) * int) * int) * 'a1
    gate_list) option **)

let next_two_qubit_gate l q =
  next_two_qubit_gate' l q []

(** val next_gate' :
    'a1 gate_list -> (int -> bool) -> 'a1 gate_app list -> (('a1
    gate_list * 'a1 gate_app) * 'a1 gate_list) option **)

let rec next_gate' l f acc =
  match l with
  | [] -> None
  | g :: t0 ->
    (match g with
     | App1 (u, q) ->
       if f q
       then Some (((List.rev_append acc []), (App1 (u, q))), t0)
       else next_gate' t0 f ((App1 (u, q)) :: acc)
     | App2 (u, q1, q2) ->
       if (||) (f q1) (f q2)
       then Some (((List.rev_append acc []), (App2 (u, q1, q2))), t0)
       else next_gate' t0 f ((App2 (u, q1, q2)) :: acc)
     | App3 (u, q1, q2, q3) ->
       if (||) ((||) (f q1) (f q2)) (f q3)
       then Some (((List.rev_append acc []), (App3 (u, q1, q2, q3))), t0)
       else next_gate' t0 f ((App3 (u, q1, q2, q3)) :: acc))

(** val next_gate :
    'a1 gate_list -> (int -> bool) -> (('a1 gate_list * 'a1 gate_app) * 'a1
    gate_list) option **)

let next_gate l f =
  next_gate' l f []

(** val does_not_reference_appl : int -> 'a1 gate_app -> bool **)

let does_not_reference_appl q = function
| App1 (_, n) -> not ((=) n q)
| App2 (_, m, n) -> not ((||) ((=) m q) ((=) n q))
| App3 (_, m, n, p) -> not ((||) ((||) ((=) m q) ((=) n q)) ((=) p q))

(** val does_not_reference : 'a1 gate_list -> int -> bool **)

let does_not_reference l q =
  List.for_all (does_not_reference_appl q) l

(** val try_rewrites :
    'a1 gate_list -> ('a1 gate_list -> 'a1 gate_list option) list -> 'a1
    gate_list option **)

let rec try_rewrites l = function
| [] -> None
| h :: t0 -> (match h l with
              | Some l' -> Some l'
              | None -> try_rewrites l t0)

(** val try_rewrites2 :
    'a1 gate_list -> ('a1 gate_list -> ('a1 gate_list * 'a1 gate_list)
    option) list -> ('a1 gate_list * 'a1 gate_list) option **)

let rec try_rewrites2 l = function
| [] -> None
| h :: t0 -> (match h l with
              | Some l' -> Some l'
              | None -> try_rewrites2 l t0)

(** val propagate' :
    'a1 gate_list -> ('a1 gate_list -> ('a1 gate_list * 'a1 gate_list)
    option) list -> ('a1 gate_list -> 'a1 gate_list option) list -> int ->
    'a1 gate_app list -> 'a1 gate_app list option **)

let rec propagate' l commute_rules cancel_rules n acc =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> None)
    (fun n' ->
    match try_rewrites l cancel_rules with
    | Some l' -> Some (List.rev_append acc l')
    | None ->
      (match try_rewrites2 l commute_rules with
       | Some p ->
         let (l1, l2) = p in
         propagate' l2 commute_rules cancel_rules n' (List.rev_append l1 acc)
       | None -> None))
    n

(** val propagate :
    'a1 gate_list -> ('a1 gate_list -> ('a1 gate_list * 'a1 gate_list)
    option) list -> ('a1 gate_list -> 'a1 gate_list option) list -> int ->
    'a1 gate_app list option **)

let propagate l commute_rules cancel_rules n =
  propagate' l commute_rules cancel_rules n []

(** val remove_prefix :
    'a1 gate_list -> 'a1 gate_list -> (int -> 'a1 -> 'a1 -> bool) -> 'a1
    gate_list option **)

let rec remove_prefix l pfx match_gate =
  match pfx with
  | [] -> Some l
  | y :: t0 ->
    (match y with
     | App1 (u, q) ->
       (match next_single_qubit_gate l q with
        | Some p ->
          let (p0, l2) = p in
          let (l1, u') = p0 in
          if match_gate (Pervasives.succ 0) u u'
          then remove_prefix (List.append l1 l2) t0 match_gate
          else None
        | None -> None)
     | App2 (u, q1, q2) ->
       (match next_gate l (fun q -> (||) ((=) q q1) ((=) q q2)) with
        | Some p ->
          let (p0, l2) = p in
          let (l1, g) = p0 in
          (match g with
           | App2 (u', q1', q2') ->
             if (&&) ((&&) ((=) q1 q1') ((=) q2 q2'))
                  (match_gate (Pervasives.succ (Pervasives.succ 0)) u u')
             then remove_prefix (List.append l1 l2) t0 match_gate
             else None
           | _ -> None)
        | None -> None)
     | App3 (_, _, _, _) -> None)

(** val remove_suffix :
    'a1 gate_list -> 'a1 gate_list -> (int -> 'a1 -> 'a1 -> bool) -> 'a1
    gate_app list option **)

let remove_suffix l sfx match_gate =
  match remove_prefix (List.rev_append l []) (List.rev_append sfx [])
          match_gate with
  | Some l0 -> Some (List.rev_append l0 [])
  | None -> None

(** val replace_pattern :
    'a1 gate_list -> 'a1 gate_list -> 'a1 gate_list -> (int -> 'a1 -> 'a1 ->
    bool) -> 'a1 gate_list option **)

let replace_pattern l pat rep match_gate =
  match remove_prefix l pat match_gate with
  | Some l' -> Some (List.append rep l')
  | None -> None

(** val get_matching_prefix' :
    'a1 gate_list -> 'a1 gate_list -> 'a1 gate_list -> 'a1 gate_list ->
    FSet.t -> int -> (int -> 'a1 -> 'a1 -> bool) -> ('a1 gate_app list * 'a1
    gate_app list) * 'a1 gate_list **)

let rec get_matching_prefix' l1 l2 pacc lacc blst n match_gate =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> (((List.rev_append pacc []), (List.rev_append lacc l1)),
    l2))
    (fun n' ->
    match next_gate l1 (fun q -> not (FSet.mem q blst)) with
    | Some p ->
      let (p0, l1b) = p in
      let (l1a, g) = p0 in
      (match g with
       | App1 (u1, q) ->
         let lacc0 = List.rev_append l1a lacc in
         let pacc' = (App1 (u1, q)) :: pacc in
         let lacc' = (App1 (u1, q)) :: lacc0 in
         let blst' = FSet.add q blst in
         (match next_single_qubit_gate l2 q with
          | Some p1 ->
            let (p2, l2b) = p1 in
            let (l2a, u2) = p2 in
            if match_gate (Pervasives.succ 0) u1 u2
            then get_matching_prefix' l1b (List.append l2a l2b) pacc' lacc0
                   blst n' match_gate
            else get_matching_prefix' l1b l2 pacc lacc' blst' n' match_gate
          | None -> get_matching_prefix' l1b l2 pacc lacc' blst' n' match_gate)
       | App2 (u1, q1, q2) ->
         let lacc0 = List.rev_append l1a lacc in
         let pacc' = (App2 (u1, q1, q2)) :: pacc in
         let lacc' = (App2 (u1, q1, q2)) :: lacc0 in
         let blst' = FSet.add q1 (FSet.add q2 blst) in
         (match next_gate l2 (fun q -> (||) ((=) q q1) ((=) q q2)) with
          | Some p1 ->
            let (p2, l2b) = p1 in
            let (l2a, g0) = p2 in
            (match g0 with
             | App2 (u2, q1', q2') ->
               if (&&)
                    ((&&)
                      ((&&)
                        ((&&)
                          (match_gate (Pervasives.succ (Pervasives.succ 0))
                            u1 u2) ((=) q1 q1')) ((=) q2 q2'))
                      (not (FSet.mem q1 blst))) (not (FSet.mem q2 blst))
               then get_matching_prefix' l1b (List.append l2a l2b) pacc'
                      lacc0 blst n' match_gate
               else get_matching_prefix' l1b l2 pacc lacc' blst' n' match_gate
             | _ -> get_matching_prefix' l1b l2 pacc lacc' blst' n' match_gate)
          | None -> get_matching_prefix' l1b l2 pacc lacc' blst' n' match_gate)
       | App3 (_, _, _, _) ->
         (((List.rev_append pacc []), (List.rev_append lacc l1)), l2))
    | None -> (((List.rev_append pacc []), (List.rev_append lacc l1)), l2))
    n

(** val get_matching_prefix :
    'a1 gate_list -> 'a1 gate_list -> (int -> 'a1 -> 'a1 -> bool) -> ('a1
    gate_app list * 'a1 gate_app list) * 'a1 gate_list **)

let get_matching_prefix l1 l2 match_gate =
  get_matching_prefix' l1 l2 [] [] FSet.empty (List.length l1) match_gate

(** val coq_LCR :
    'a1 gate_list -> ('a1 gate_list -> 'a1 gate_list) -> (int -> 'a1 -> 'a1
    -> bool) -> (('a1 gate_app list * 'a1 gate_app list) * 'a1 gate_list)
    option **)

let coq_LCR b opt match_gate =
  let o = opt b in
  let o2 = opt (List.append o o) in
  let (tmp, r) = get_matching_prefix o o2 match_gate in
  let (l, _) = tmp in
  let o3 = opt (List.append o (List.append o o)) in
  (match remove_prefix o3 l match_gate with
   | Some cr ->
     (match remove_suffix cr r match_gate with
      | Some c -> Some ((l, c), r)
      | None -> None)
   | None -> None)
