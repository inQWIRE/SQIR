open Layouts
open UnitaryListRepresentation

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

let rec fix_cnots l is_in_graph cNOT h =
  match l with
  | [] -> l
  | h0 :: t ->
    (match h0 with
     | App2 (_, n1, n2) ->
       if is_in_graph n1 n2
       then (cNOT n1 n2) :: (fix_cnots t is_in_graph cNOT h)
       else (h n1) :: ((h n2) :: ((cNOT n2 n1) :: ((h n1) :: ((h n2) :: 
              (fix_cnots t is_in_graph cNOT h)))))
     | _ -> h0 :: (fix_cnots t is_in_graph cNOT h))

(** val simple_map :
    'a1 gate_list -> qmap -> (int -> int -> int list) -> (int -> int -> bool)
    -> (int -> int -> 'a1 gate_app) -> (int -> int -> 'a1 gate_list) -> (int
    -> 'a1 gate_app) -> 'a1 gate_list * qmap **)

let rec simple_map l m get_path is_in_graph cNOT sWAP h =
  match l with
  | [] -> ([], m)
  | g :: t ->
    (match g with
     | App1 (u, n) ->
       let (t', m') = simple_map t m get_path is_in_graph cNOT sWAP h in
       (((App1 (u, (log2phys m n))) :: t'), m')
     | App2 (_, n1, n2) ->
       let p = get_path (log2phys m n1) (log2phys m n2) in
       let (swaps, m') = path_to_swaps p m sWAP in
       let mapped_cnot =
         fix_cnots
           (List.append swaps
             ((cNOT (log2phys m' n1) (log2phys m' n2)) :: [])) is_in_graph
           cNOT h
       in
       let (t', m'') = simple_map t m' get_path is_in_graph cNOT sWAP h in
       ((List.append mapped_cnot t'), m'')
     | App3 (_, _, _, _) -> ([], m))
