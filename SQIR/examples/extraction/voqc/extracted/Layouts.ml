open PeanoNat

type qmap = (int -> int) * (int -> int)

(** val log2phys : qmap -> int -> int **)

let log2phys m q =
  let (m0, _) = m in m0 q

(** val phys2log : qmap -> int -> int **)

let phys2log m q =
  let (_, m0) = m in m0 q

(** val swap_in_map : qmap -> int -> int -> qmap **)

let swap_in_map m phys1 phys2 =
  let (m1, m2) = m in
  let log1 = m2 phys1 in
  let log2 = m2 phys2 in
  let m1' = fun q ->
    if (=) q log1 then phys2 else if (=) q log2 then phys1 else m1 q
  in
  let m2' = fun q ->
    if (=) q phys1 then log2 else if (=) q phys2 then log1 else m2 q
  in
  (m1', m2')

(** val layout_well_formed_b' : int -> int -> qmap -> bool **)

let rec layout_well_formed_b' dim n m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> true)
    (fun n' ->
    (&&)
      ((&&)
        ((&&)
          ((&&) (Nat.ltb (log2phys m n') dim) (Nat.ltb (phys2log m n') dim))
          ((=) (phys2log m (log2phys m n')) n'))
        ((=) (log2phys m (phys2log m n')) n'))
      (layout_well_formed_b' dim n' m))
    n

(** val layout_well_formed_b : int -> qmap -> bool **)

let layout_well_formed_b dim m =
  layout_well_formed_b' dim dim m

(** val layout_to_list' : int -> int -> qmap -> int list **)

let rec layout_to_list' dim x m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun x' ->
    List.append (layout_to_list' dim x' m) ((phys2log m x') :: []))
    x

(** val layout_to_list : int -> qmap -> int list **)

let layout_to_list dim m =
  layout_to_list' dim dim m

(** val trivial_layout : int -> qmap **)

let trivial_layout _ =
  ((fun x -> x), (fun x -> x))
