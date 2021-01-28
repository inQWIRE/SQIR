open PeanoNat
open UnitaryListRepresentation

type qmap = (int -> int) * (int -> int option)

(** val log2phys : qmap -> int -> int **)

let log2phys m q =
  let (m0, _) = m in m0 q

(** val phys2log : qmap -> int -> int option **)

let phys2log m q =
  let (_, m0) = m in m0 q

(** val swap_in_map : qmap -> int -> int -> qmap **)

let swap_in_map m phys1 phys2 =
  let (m1, m2) = m in
  let olog1 = m2 phys1 in
  let olog2 = m2 phys2 in
  let m1' = fun q ->
    match olog1 with
    | Some log1 ->
      (match olog2 with
       | Some log2 ->
         if (=) q log1 then phys2 else if (=) q log2 then phys1 else m1 q
       | None -> if (=) q log1 then phys2 else m1 q)
    | None ->
      (match olog2 with
       | Some log2 -> if (=) q log2 then phys1 else m1 q
       | None -> m1 q)
  in
  let m2' = fun q ->
    if (=) q phys1 then olog2 else if (=) q phys2 then olog1 else m2 q
  in
  (m1', m2')

(** val check_log2phys : int -> int -> int -> qmap -> bool **)

let rec check_log2phys ldim pdim x m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> true)
    (fun x' ->
    let y = log2phys m x' in
    (&&)
      ((&&) (Nat.ltb y pdim)
        (match phys2log m y with
         | Some x0 -> (=) x0 x'
         | None -> false)) (check_log2phys ldim pdim x' m))
    x

(** val check_phys2log : int -> int -> int -> qmap -> bool **)

let rec check_phys2log ldim pdim y m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> true)
    (fun y' ->
    let ox = phys2log m y' in
    (&&)
      (match ox with
       | Some x -> (&&) (Nat.ltb x ldim) ((=) (log2phys m x) y')
       | None -> true) (check_phys2log ldim pdim y' m))
    y

(** val layout_well_formed_b : int -> int -> qmap -> bool **)

let layout_well_formed_b ldim pdim m =
  (&&) (check_log2phys ldim pdim ldim m) (check_phys2log ldim pdim pdim m)

(** val layout_to_list' : int -> int -> int -> qmap -> int option list **)

let rec layout_to_list' ldim pdim x m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun x' ->
    List.append (layout_to_list' ldim pdim x' m) ((phys2log m x') :: []))
    x

(** val layout_to_list : int -> int -> qmap -> int option list **)

let layout_to_list ldim pdim m =
  layout_to_list' ldim pdim pdim m

(** val trivial_layout : int -> int -> qmap **)

let trivial_layout ldim _ =
  ((fun x -> x), (fun x -> if Nat.ltb x ldim then Some x else None))

(** val path_to_swaps :
    int list -> qmap -> (int -> int -> 'a1 gate_list) -> 'a1 gate_list * qmap **)

let rec path_to_swaps p m sWAP =
  match p with
  | [] -> ([], m)
  | n1 :: t ->
    (match t with
     | [] -> ([], m)
     | n2 :: l ->
       (match l with
        | [] -> ([], m)
        | _ :: _ ->
          let (l0, m') = path_to_swaps t (swap_in_map m n1 n2) sWAP in
          ((List.append (sWAP n1 n2) l0), m')))

(** val fix_cnots :
    'a1 gate_list -> (int -> int -> bool) -> (int -> int -> 'a1 gate_app) ->
    (int -> 'a1 gate_app) -> 'a1 gate_list **)

let rec fix_cnots l is_in_graph_b cNOT h =
  match l with
  | [] -> l
  | h0 :: t ->
    (match h0 with
     | App2 (_, n1, n2) ->
       if is_in_graph_b n1 n2
       then (cNOT n1 n2) :: (fix_cnots t is_in_graph_b cNOT h)
       else (h n1) :: ((h n2) :: ((cNOT n2 n1) :: ((h n1) :: ((h n2) :: 
              (fix_cnots t is_in_graph_b cNOT h)))))
     | _ -> h0 :: (fix_cnots t is_in_graph_b cNOT h))

(** val simple_map :
    'a1 gate_list -> qmap -> (int -> int -> int list) -> (int -> int -> bool)
    -> (int -> int -> 'a1 gate_app) -> (int -> int -> 'a1 gate_list) -> (int
    -> 'a1 gate_app) -> 'a1 gate_list * qmap **)

let rec simple_map l m get_path is_in_graph_b cNOT sWAP h =
  match l with
  | [] -> ([], m)
  | g :: t ->
    (match g with
     | App1 (u, n) ->
       let (t', m') = simple_map t m get_path is_in_graph_b cNOT sWAP h in
       (((App1 (u, (log2phys m n))) :: t'), m')
     | App2 (_, n1, n2) ->
       let p = get_path (log2phys m n1) (log2phys m n2) in
       let (swaps, m') = path_to_swaps p m sWAP in
       let mapped_cnot =
         fix_cnots
           (List.append swaps
             ((cNOT (log2phys m' n1) (log2phys m' n2)) :: [])) is_in_graph_b
           cNOT h
       in
       let (t', m'') = simple_map t m' get_path is_in_graph_b cNOT sWAP h in
       ((List.append mapped_cnot t'), m'')
     | App3 (_, _, _, _) -> ([], m))

(** val simple_map_rzq :
    RzQGateSet.coq_RzQ_ucom_l -> qmap -> (int -> int -> int list) -> (int ->
    int -> bool) -> RzQGateSet.coq_RzQ_ucom_l * qmap **)

let simple_map_rzq l m get_path is_in_graph_b =
  simple_map l m get_path is_in_graph_b RzQGateSet.coq_CNOT
    RzQGateSet.coq_SWAP RzQGateSet.coq_H
