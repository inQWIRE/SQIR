
type var = int

type posi = var * int

(** val posi_eq : posi -> posi -> bool **)

let posi_eq r1 r2 =
  let (x1, y1) = r1 in let (x2, y2) = r2 in (&&) ((=) x1 x2) ((=) y1 y2)
