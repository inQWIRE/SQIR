open FMapAVL
open ListRepresentation
open OrderedTypeEx
open RzQGateSet

type __ = Obj.t

module FMap = Make(Nat_as_OT)

(** val xor : FSet.t -> FSet.t -> FSet.t **)

let xor s1 s2 =
  FSet.diff (FSet.union s1 s2) (FSet.inter s1 s2)

(** val get_set : FSet.t FMap.t -> FMap.key -> FSet.t **)

let get_set smap q =
  match FMap.find q smap with
  | Some s -> s
  | None -> FSet.add q FSet.empty

(** val find_merge' :
    coq_RzQ_ucom_l -> FSet.t -> FSet.t -> FSet.elt -> FSet.t FMap.t -> int ->
    coq_RzQ_Unitary gate_app list -> (((coq_RzQ_Unitary gate_app
    list * Q.t) * int) * coq_RzQ_Unitary gate_list) option **)

let rec find_merge' l qs blst q smap n acc =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> None)
    (fun n' ->
    if FSet.equal qs blst
    then None
    else (match next_gate l qs with
          | Some p ->
            let (p0, l2) = p in
            let (l1, g) = p0 in
            (match g with
             | App1 (r, q') ->
               (match r with
                | URzQ_H ->
                  find_merge' l2 qs (FSet.add q' blst) q smap n'
                    (List.append ((coq_H q') :: []) (List.rev_append l1 acc))
                | URzQ_Rz a ->
                  let s = get_set smap q' in
                  let sorig = FSet.add q FSet.empty in
                  if (&&) (not (FSet.mem q' blst)) (FSet.equal s sorig)
                  then Some ((((List.rev_append acc l1), a), q'), l2)
                  else find_merge' l2 qs blst q smap n'
                         (List.append ((coq_Rz a q') :: [])
                           (List.rev_append l1 acc))
                | _ -> None)
             | App2 (r, q1, q2) ->
               (match r with
                | URzQ_CNOT ->
                  let qs' = FSet.add q1 (FSet.add q2 qs) in
                  if (||) (FSet.mem q1 blst) (FSet.mem q2 blst)
                  then let blst' =
                         if FSet.mem q1 blst then FSet.add q2 blst else blst
                       in
                       find_merge' l2 qs' blst' q smap n'
                         (List.append ((coq_CNOT q1 q2) :: [])
                           (List.rev_append l1 acc))
                  else let s1 = get_set smap q1 in
                       let s2 = get_set smap q2 in
                       let smap' = FMap.add q2 (xor s1 s2) smap in
                       find_merge' l2 qs' blst q smap' n'
                         (List.append ((coq_CNOT q1 q2) :: [])
                           (List.rev_append l1 acc))
                | _ -> None)
             | App3 (_, _, _, _) -> None)
          | None -> None))
    n

(** val find_merge :
    coq_RzQ_ucom_l -> FSet.elt -> (((coq_RzQ_Unitary gate_app
    list * Q.t) * int) * coq_RzQ_Unitary gate_list) option **)

let find_merge l q =
  find_merge' l (FSet.add q FSet.empty) FSet.empty q FMap.empty
    (List.length l) []

(** val merge_at_beginning :
    coq_RzQ_ucom_l -> Q.t -> FSet.elt -> coq_RzQ_Unitary gate_app list option **)

let merge_at_beginning l a q =
  match find_merge l q with
  | Some p ->
    let (p0, l2) = p in
    let (p1, _) = p0 in
    let (l1, a') = p1 in
    Some (List.append (combine_rotations a a' q) (List.append l1 l2))
  | None -> None

(** val merge_at_end :
    coq_RzQ_ucom_l -> Q.t -> FSet.elt -> coq_RzQ_Unitary gate_app list option **)

let merge_at_end l a q =
  match find_merge l q with
  | Some p ->
    let (p0, l2) = p in
    let (p1, q') = p0 in
    let (l1, a') = p1 in
    Some (List.append l1 (List.append (combine_rotations a a' q') l2))
  | None -> None

(** val merge_rotations_at_beginning :
    coq_RzQ_ucom_l -> int -> coq_RzQ_Unitary gate_app list -> coq_RzQ_Unitary
    gate_app list **)

let rec merge_rotations_at_beginning l n acc =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> List.rev_append acc l)
    (fun n' ->
    match l with
    | [] -> List.rev_append acc []
    | g :: t0 ->
      (match g with
       | App1 (r, q) ->
         (match r with
          | URzQ_Rz a ->
            (match merge_at_beginning t0 a q with
             | Some t' -> merge_rotations_at_beginning t' n' acc
             | None ->
               merge_rotations_at_beginning t0 n' ((coq_Rz a q) :: acc))
          | _ -> merge_rotations_at_beginning t0 n' (g :: acc))
       | _ -> merge_rotations_at_beginning t0 n' (g :: acc)))
    n

(** val merge_rotations_at_end :
    coq_RzQ_ucom_l -> int -> coq_RzQ_Unitary gate_app list -> coq_RzQ_Unitary
    gate_app list **)

let rec merge_rotations_at_end l n acc =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> List.rev_append acc l)
    (fun n' ->
    match l with
    | [] -> List.rev_append acc []
    | g :: t0 ->
      (match g with
       | App1 (r, q) ->
         (match r with
          | URzQ_Rz a ->
            (match merge_at_end t0 a q with
             | Some t' -> merge_rotations_at_end t' n' acc
             | None -> merge_rotations_at_end t0 n' ((coq_Rz a q) :: acc))
          | _ -> merge_rotations_at_end t0 n' (g :: acc))
       | _ -> merge_rotations_at_end t0 n' (g :: acc)))
    n

(** val invert_gate : coq_RzQ_Unitary gate_app -> coq_RzQ_Unitary gate_app **)

let invert_gate g = match g with
| App1 (y, q) -> (match y with
                  | URzQ_Rz a -> invert_rotation a q
                  | _ -> g)
| _ -> g

(** val rev_append_w_map :
    ('a1 -> 'a1) -> 'a1 list -> 'a1 list -> 'a1 list **)

let rec rev_append_w_map f l l' =
  match l with
  | [] -> l'
  | a :: l0 -> rev_append_w_map f l0 ((f a) :: l')

(** val invert : coq_RzQ_ucom_l -> coq_RzQ_Unitary gate_app list **)

let invert l =
  rev_append_w_map invert_gate l []

(** val merge_rotations : coq_RzQ_ucom_l -> coq_RzQ_Unitary gate_app list **)

let merge_rotations l =
  let l' = merge_rotations_at_beginning l (List.length l) [] in
  let l'' = merge_rotations_at_end (invert l') (List.length l') [] in
  invert l''
