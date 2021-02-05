open PeanoNat

module LNN =
 struct
  (** val is_in_graph : int -> int -> int -> bool **)

  let is_in_graph dim n1 n2 =
    (||)
      ((&&) (Nat.ltb ((+) n1 (Pervasives.succ 0)) dim)
        ((=) n2 ((+) n1 (Pervasives.succ 0))))
      ((&&) (Nat.ltb ((+) n2 (Pervasives.succ 0)) dim)
        ((=) n1 ((+) n2 (Pervasives.succ 0))))

  (** val move_left : int -> int -> int list **)

  let rec move_left n dist =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n :: [])
      (fun n' -> n :: (move_left (Nat.sub n (Pervasives.succ 0)) n'))
      dist

  (** val move_right : int -> int -> int list **)

  let rec move_right n dist =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n :: [])
      (fun n' -> n :: (move_right ((+) n (Pervasives.succ 0)) n'))
      dist

  (** val get_path : int -> int -> int list **)

  let get_path n1 n2 =
    if Nat.ltb n1 n2
    then move_right n1 (Nat.sub n2 n1)
    else if Nat.ltb n2 n1 then move_left n1 (Nat.sub n1 n2) else []
 end

module LNNRing =
 struct
  (** val is_in_graph : int -> int -> int -> bool **)

  let is_in_graph dim n1 n2 =
    (&&) (Nat.ltb (Pervasives.succ 0) dim)
      ((||)
        ((&&) (Nat.ltb n1 dim)
          ((=) n2 (Nat.modulo ((+) n1 (Pervasives.succ 0)) dim)))
        ((&&) (Nat.ltb n2 dim)
          ((=) n1 (Nat.modulo ((+) n2 (Pervasives.succ 0)) dim))))

  (** val move_cw : int -> int -> int -> int list **)

  let rec move_cw dim n dist =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n :: [])
      (fun dist' ->
      n :: (move_cw dim (Nat.modulo ((+) n (Pervasives.succ 0)) dim) dist'))
      dist

  (** val move_ccw : int -> int -> int -> int list **)

  let rec move_ccw dim n dist =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n :: [])
      (fun dist' ->
      n :: (move_ccw dim
             (Nat.modulo (Nat.sub ((+) dim n) (Pervasives.succ 0)) dim) dist'))
      dist

  (** val get_path : int -> int -> int -> int list **)

  let get_path dim n1 n2 =
    if Nat.ltb n1 n2
    then let dist_cw = Nat.sub n2 n1 in
         let dist_ccw = Nat.sub ((+) dim n1) n2 in
         if Nat.ltb dist_cw dist_ccw
         then move_cw dim n1 dist_cw
         else move_ccw dim n1 dist_ccw
    else if Nat.ltb n2 n1
         then let dist_cw = Nat.sub ((+) dim n2) n1 in
              let dist_ccw = Nat.sub n1 n2 in
              if Nat.ltb dist_cw dist_ccw
              then move_cw dim n1 dist_cw
              else move_ccw dim n1 dist_ccw
         else []
 end
