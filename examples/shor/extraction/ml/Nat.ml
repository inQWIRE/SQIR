
(** val add : Z.t -> Z.t -> Z.t **)

let rec add n m =
  (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
    (fun _ -> m)
    (fun p -> Z.succ (add p m))
    n

(** val mul : Z.t -> Z.t -> Z.t **)

let rec mul n m =
  (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
    (fun _ -> Z.zero)
    (fun p -> add m (mul p m))
    n

(** val sub : Z.t -> Z.t -> Z.t **)

let rec sub n m =
  (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
    (fun _ -> n)
    (fun k ->
    (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
      (fun _ -> n)
      (fun l -> sub k l)
      m)
    n

(** val max : Z.t -> Z.t -> Z.t **)

let rec max n m =
  (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
    (fun _ -> m)
    (fun n' ->
    (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
      (fun _ -> n)
      (fun m' -> Z.succ (max n' m'))
      m)
    n
