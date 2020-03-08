
type 'u gate_app =
| App1 of 'u * int
| App2 of 'u * int * int
| App3 of 'u * int * int * int

type 'u gate_list = 'u gate_app list

(** val next_single_qubit_gate' :
    'a1 gate_list -> int -> 'a1 gate_app list -> (('a1 gate_list * 'a1) * 'a1
    gate_list) option **)

let rec next_single_qubit_gate' l q acc =
  match l with
  | [] -> None
  | g :: t ->
    (match g with
     | App1 (u, n) ->
       if (=) n q
       then Some (((List.rev_append acc []), u), t)
       else next_single_qubit_gate' t q ((App1 (u, n)) :: acc)
     | App2 (u, m, n) ->
       if (||) ((=) m q) ((=) n q)
       then None
       else next_single_qubit_gate' t q ((App2 (u, m, n)) :: acc)
     | App3 (u, m, n, p) ->
       if (||) ((||) ((=) m q) ((=) n q)) ((=) p q)
       then None
       else next_single_qubit_gate' t q ((App3 (u, m, n, p)) :: acc))

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
  | g :: t ->
    (match g with
     | App1 (u, n) ->
       if (=) n q
       then None
       else next_two_qubit_gate' t q ((App1 (u, n)) :: acc)
     | App2 (u, m, n) ->
       if (||) ((=) m q) ((=) n q)
       then Some (((((List.rev_append acc []), u), m), n), t)
       else next_two_qubit_gate' t q ((App2 (u, m, n)) :: acc)
     | App3 (u, m, n, p) ->
       if (||) ((||) ((=) m q) ((=) n q)) ((=) p q)
       then None
       else next_two_qubit_gate' t q ((App3 (u, m, n, p)) :: acc))

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
  | g :: t ->
    (match g with
     | App1 (u, q) ->
       if f q
       then Some (((List.rev_append acc []), (App1 (u, q))), t)
       else next_gate' t f ((App1 (u, q)) :: acc)
     | App2 (u, q1, q2) ->
       if (||) (f q1) (f q2)
       then Some (((List.rev_append acc []), (App2 (u, q1, q2))), t)
       else next_gate' t f ((App2 (u, q1, q2)) :: acc)
     | App3 (u, q1, q2, q3) ->
       if (||) ((||) (f q1) (f q2)) (f q3)
       then Some (((List.rev_append acc []), (App3 (u, q1, q2, q3))), t)
       else next_gate' t f ((App3 (u, q1, q2, q3)) :: acc))

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
| h :: t -> (match h l with
             | Some l' -> Some l'
             | None -> try_rewrites l t)

(** val try_rewrites2 :
    'a1 gate_list -> ('a1 gate_list -> ('a1 gate_list * 'a1 gate_list)
    option) list -> ('a1 gate_list * 'a1 gate_list) option **)

let rec try_rewrites2 l = function
| [] -> None
| h :: t -> (match h l with
             | Some l' -> Some l'
             | None -> try_rewrites2 l t)

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
  | y :: t ->
    (match y with
     | App1 (u, q) ->
       (match next_single_qubit_gate l q with
        | Some p ->
          let (p0, l2) = p in
          let (l1, u') = p0 in
          if match_gate (Pervasives.succ 0) u u'
          then remove_prefix (List.append l1 l2) t match_gate
          else None
        | None -> None)
     | App2 (u, q1, q2) ->
       (match next_two_qubit_gate l q1 with
        | Some p ->
          let (p0, l2) = p in
          let (p1, q2') = p0 in
          let (p2, q1') = p1 in
          let (l1, u') = p2 in
          if (&&)
               ((&&) ((&&) ((=) q1 q1') ((=) q2 q2'))
                 (match_gate (Pervasives.succ (Pervasives.succ 0)) u u'))
               (does_not_reference l1 q2)
          then remove_prefix (List.append l1 l2) t match_gate
          else None
        | None -> None)
     | App3 (_, _, _, _) -> None)

(** val replace_pattern :
    'a1 gate_list -> 'a1 gate_list -> 'a1 gate_list -> (int -> 'a1 -> 'a1 ->
    bool) -> 'a1 gate_list option **)

let replace_pattern l pat rep match_gate =
  match remove_prefix l pat match_gate with
  | Some l' -> Some (List.append rep l')
  | None -> None
