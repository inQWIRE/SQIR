open PeanoNat

(** val merge_path : int list -> int list -> int list **)

let rec merge_path p1 p2 =
  match p1 with
  | [] -> p2
  | h :: t -> (match t with
               | [] -> p2
               | _ :: _ -> h :: (merge_path t p2))

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

module Grid =
 struct
  (** val is_in_graph : int -> int -> int -> int -> bool **)

  let is_in_graph numRows numCols i i' =
    (||)
      ((||)
        ((||)
          ((&&) (Nat.ltb ((+) i numCols) (( * ) numRows numCols))
            ((=) i' ((+) i numCols)))
          ((&&) (Nat.ltb ((+) i' numCols) (( * ) numRows numCols))
            ((=) i ((+) i' numCols))))
        ((&&) (Nat.ltb ((+) i (Pervasives.succ 0)) (( * ) numRows numCols))
          ((=) i' ((+) i (Pervasives.succ 0)))))
      ((&&) (Nat.ltb ((+) i' (Pervasives.succ 0)) (( * ) numRows numCols))
        ((=) i ((+) i' (Pervasives.succ 0))))

  (** val row : int -> int -> int **)

  let row numCols i =
    Nat.div i numCols

  (** val col : int -> int -> int **)

  let col numCols i =
    Nat.modulo i numCols

  (** val move_up : int -> int -> int **)

  let move_up numCols i =
    Nat.sub i numCols

  (** val move_down : int -> int -> int **)

  let move_down numCols i =
    (+) i numCols

  (** val move_left : int -> int **)

  let move_left i =
    Nat.sub i (Pervasives.succ 0)

  (** val move_right : int -> int **)

  let move_right i =
    (+) i (Pervasives.succ 0)

  (** val repeat_move : (int -> int) -> int -> int -> int list **)

  let rec repeat_move f i dist =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> i :: [])
      (fun dist' -> i :: (repeat_move f (f i) dist'))
      dist

  (** val get_path : int -> int -> int -> int list **)

  let get_path numCols i1 i2 =
    let r1 = row numCols i1 in
    let c1 = col numCols i1 in
    let r2 = row numCols i2 in
    let c2 = col numCols i2 in
    if (&&) (Nat.ltb r1 r2) (Nat.ltb c1 c2)
    then let p1 = repeat_move (move_down numCols) i1 (Nat.sub r2 r1) in
         let p2 =
           repeat_move move_right ((+) i1 (( * ) (Nat.sub r2 r1) numCols))
             (Nat.sub c2 c1)
         in
         merge_path p1 p2
    else if (&&) (Nat.ltb r1 r2) ((=) c1 c2)
         then repeat_move (move_down numCols) i1 (Nat.sub r2 r1)
         else if (&&) (Nat.ltb r1 r2) (Nat.ltb c2 c1)
              then let p1 = repeat_move move_left i1 (Nat.sub c1 c2) in
                   let p2 =
                     repeat_move (move_down numCols)
                       (Nat.sub i1 (Nat.sub c1 c2)) (Nat.sub r2 r1)
                   in
                   merge_path p1 p2
              else if (&&) ((=) r1 r2) (Nat.ltb c1 c2)
                   then repeat_move move_right i1 (Nat.sub c2 c1)
                   else if (&&) ((=) r1 r2) ((=) c1 c2)
                        then []
                        else if (&&) ((=) r1 r2) (Nat.ltb c2 c1)
                             then repeat_move move_left i1 (Nat.sub c1 c2)
                             else if (&&) (Nat.ltb r2 r1) (Nat.ltb c1 c2)
                                  then let p1 =
                                         repeat_move (move_up numCols) i1
                                           (Nat.sub r1 r2)
                                       in
                                       let p2 =
                                         repeat_move move_right
                                           (Nat.sub i1
                                             (( * ) (Nat.sub r1 r2) numCols))
                                           (Nat.sub c2 c1)
                                       in
                                       merge_path p1 p2
                                  else if (&&) (Nat.ltb r2 r1) ((=) c1 c2)
                                       then repeat_move (move_up numCols) i1
                                              (Nat.sub r1 r2)
                                       else if (&&) (Nat.ltb r2 r1)
                                                 (Nat.ltb c2 c1)
                                            then let p1 =
                                                   repeat_move
                                                     (move_up numCols) i1
                                                     (Nat.sub r1 r2)
                                                 in
                                                 let p2 =
                                                   repeat_move move_left
                                                     (Nat.sub i1
                                                       (( * ) (Nat.sub r1 r2)
                                                         numCols))
                                                     (Nat.sub c1 c2)
                                                 in
                                                 merge_path p1 p2
                                            else []
 end

module Tenerife =
 struct
  (** val tenerife_graph : (int * int) list **)

  let tenerife_graph =
    ((Pervasives.succ 0), 0) :: (((Pervasives.succ (Pervasives.succ 0)),
      0) :: (((Pervasives.succ (Pervasives.succ 0)), (Pervasives.succ
      0)) :: (((Pervasives.succ (Pervasives.succ (Pervasives.succ 0))),
      (Pervasives.succ (Pervasives.succ 0))) :: (((Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))), (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0))))) :: (((Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0)))), (Pervasives.succ (Pervasives.succ
      0))) :: [])))))

  (** val beq_tup : (int * int) -> (int * int) -> bool **)

  let beq_tup t t' =
    let (n1, n2) = t in let (n1', n2') = t' in (&&) ((=) n1 n1') ((=) n2 n2')

  (** val is_in_graph : int -> int -> bool **)

  let is_in_graph n1 n2 =
    List.exists (beq_tup (n1, n2)) tenerife_graph

  (** val get_path : int -> int -> int list **)

  let get_path n1 n2 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> [])
        (fun n ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> 0 :: ((Pervasives.succ 0) :: []))
          (fun n0 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> 0 :: ((Pervasives.succ (Pervasives.succ
            0)) :: []))
            (fun n3 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> 0 :: ((Pervasives.succ (Pervasives.succ
              0)) :: ((Pervasives.succ (Pervasives.succ (Pervasives.succ
              0))) :: [])))
              (fun n4 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> 0 :: ((Pervasives.succ (Pervasives.succ
                0)) :: ((Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ 0)))) :: [])))
                (fun _ -> [])
                n4)
              n3)
            n0)
          n)
        n2)
      (fun n ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> (Pervasives.succ 0) :: (0 :: []))
          (fun n0 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> [])
            (fun n3 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> (Pervasives.succ 0) :: ((Pervasives.succ
              (Pervasives.succ 0)) :: []))
              (fun n4 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> (Pervasives.succ 0) :: ((Pervasives.succ
                (Pervasives.succ 0)) :: ((Pervasives.succ (Pervasives.succ
                (Pervasives.succ 0))) :: [])))
                (fun n5 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> (Pervasives.succ 0) :: ((Pervasives.succ
                  (Pervasives.succ 0)) :: ((Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ 0)))) :: [])))
                  (fun _ -> [])
                  n5)
                n4)
              n3)
            n0)
          n2)
        (fun n0 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> (Pervasives.succ (Pervasives.succ
            0)) :: (0 :: []))
            (fun n3 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> (Pervasives.succ (Pervasives.succ
              0)) :: ((Pervasives.succ 0) :: []))
              (fun n4 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> [])
                (fun n5 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> (Pervasives.succ (Pervasives.succ
                  0)) :: ((Pervasives.succ (Pervasives.succ (Pervasives.succ
                  0))) :: []))
                  (fun n6 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ -> (Pervasives.succ (Pervasives.succ
                    0)) :: ((Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ 0)))) :: []))
                    (fun _ -> [])
                    n6)
                  n5)
                n4)
              n3)
            n2)
          (fun n3 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> (Pervasives.succ (Pervasives.succ (Pervasives.succ
              0))) :: ((Pervasives.succ (Pervasives.succ
              0)) :: (0 :: [])))
              (fun n4 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> (Pervasives.succ (Pervasives.succ (Pervasives.succ
                0))) :: ((Pervasives.succ (Pervasives.succ
                0)) :: ((Pervasives.succ 0) :: [])))
                (fun n5 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ 0))) :: ((Pervasives.succ (Pervasives.succ
                  0)) :: []))
                  (fun n6 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ -> [])
                    (fun n7 ->
                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                      (fun _ -> (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ 0))) :: ((Pervasives.succ
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      0)))) :: []))
                      (fun _ -> [])
                      n7)
                    n6)
                  n5)
                n4)
              n2)
            (fun n4 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ 0)))) :: ((Pervasives.succ (Pervasives.succ
                0)) :: (0 :: [])))
                (fun n5 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ
                  0)))) :: ((Pervasives.succ (Pervasives.succ
                  0)) :: ((Pervasives.succ 0) :: [])))
                  (fun n6 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ -> (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ
                    0)))) :: ((Pervasives.succ (Pervasives.succ
                    0)) :: []))
                    (fun n7 ->
                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                      (fun _ -> (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ
                      0)))) :: ((Pervasives.succ (Pervasives.succ
                      (Pervasives.succ 0))) :: []))
                      (fun _ -> [])
                      n7)
                    n6)
                  n5)
                n2)
              (fun _ -> [])
              n4)
            n3)
          n0)
        n)
      n1
 end
