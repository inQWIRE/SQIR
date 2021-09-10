open BasicUtility
open Datatypes
open MathSpec
open Nat0
open PeanoNat

type exp =
| SKIP of posi
| X of posi
| CU of posi * exp
| RZ of int * posi
| RRZ of int * posi
| SR of int * var
| SRR of int * var
| HCNOT of posi * posi
| Lshift of var
| Rshift of var
| Rev of var
| QFT of var
| RQFT of var
| H of var
| Seq of exp * exp

(** val inv_exp : exp -> exp **)

let rec inv_exp = function
| CU (n, p0) -> CU (n, (inv_exp p0))
| RZ (q, p1) -> RRZ (q, p1)
| RRZ (q, p1) -> RZ (q, p1)
| SR (n, x) -> SRR (n, x)
| SRR (n, x) -> SR (n, x)
| Lshift x -> Rshift x
| Rshift x -> Lshift x
| QFT x -> RQFT x
| RQFT x -> QFT x
| Seq (p1, p2) -> Seq ((inv_exp p2), (inv_exp p1))
| x -> x

(** val init_v : int -> var -> (int -> bool) -> exp **)

let rec init_v n x m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (x, 0))
    (fun m0 ->
    if m m0 then Seq ((init_v m0 x m), (X (x, m0))) else init_v m0 x m)
    n

type vars = int -> ((int * int) * (int -> int)) * (int -> int)

(** val start : vars -> var -> int **)

let start vs x =
  fst (fst (fst (vs x)))

(** val vsize : vars -> var -> int **)

let vsize vs x =
  snd (fst (fst (vs x)))

(** val vmap : vars -> var -> int -> int **)

let vmap vs x =
  snd (fst (vs x))

(** val avmap : vars -> var -> int -> int **)

let avmap vs x =
  snd (vs x)

(** val find_pos : vars -> posi -> int **)

let find_pos f = function
| (a, b) -> add (start f a) (vmap f a b)

(** val shift_fun : (int -> int) -> int -> int -> int -> int **)

let shift_fun f offset size i =
  if Nat.ltb i size then f (Nat.modulo (add i offset) size) else f i

(** val ashift_fun : (int -> int) -> int -> int -> int -> int **)

let ashift_fun f offset size i =
  if Nat.ltb i size then Nat.modulo (add (f i) offset) size else f i

(** val afbrev : (int -> int) -> int -> int -> int **)

let afbrev f size x =
  if Nat.ltb x size then sub (sub size (Pervasives.succ 0)) (f x) else f x

(** val trans_lshift :
    vars -> var -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let trans_lshift f x i =
  let (p, ag) = f x in
  let (p0, g) = p in
  let (start0, size) = p0 in
  if (=) i x
  then (((start0, size), (shift_fun g (sub size (Pervasives.succ 0)) size)),
         (ashift_fun ag (Pervasives.succ 0) size))
  else f i

(** val trans_rshift :
    vars -> var -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let trans_rshift f x i =
  let (p, ag) = f x in
  let (p0, g) = p in
  let (start0, size) = p0 in
  if (=) i x
  then (((start0, size), (shift_fun g (Pervasives.succ 0) size)),
         (ashift_fun ag (sub size (Pervasives.succ 0)) size))
  else f i

(** val lshift_avs :
    int -> vars -> (int -> posi) -> var -> int -> var * int **)

let lshift_avs dim f avs x i =
  if (&&) ((&&) (Nat.ltb i dim) ((<=) (start f x) i))
       (Nat.ltb (sub i (start f x)) (vsize f x))
  then (x, (avmap (trans_lshift f x) x (sub i (start f x))))
  else avs i

(** val rshift_avs :
    int -> vars -> (int -> posi) -> var -> int -> var * int **)

let rshift_avs dim f avs x i =
  if (&&) ((&&) (Nat.ltb i dim) ((<=) (start f x) i))
       (Nat.ltb (sub i (start f x)) (vsize f x))
  then (x, (avmap (trans_rshift f x) x (sub i (start f x))))
  else avs i

(** val trans_rev :
    vars -> var -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let trans_rev f x i =
  let (p, ag) = f x in
  let (p0, g) = p in
  let (start0, size) = p0 in
  if (=) i x
  then (((start0, size), (fbrev size g)), (afbrev ag size))
  else f i

(** val rev_avs : int -> vars -> (int -> posi) -> var -> int -> var * int **)

let rev_avs dim f avs x i =
  if (&&) ((&&) (Nat.ltb i dim) ((<=) (start f x) i))
       (Nat.ltb (sub i (start f x)) (vsize f x))
  then (x, (avmap (trans_rev f x) x (sub i (start f x))))
  else avs i

(** val coq_CNOT : posi -> posi -> exp **)

let coq_CNOT x y =
  CU (x, (X y))

(** val coq_SWAP : posi -> posi -> exp **)

let coq_SWAP x y =
  if posi_eq x y
  then SKIP x
  else Seq ((Seq ((coq_CNOT x y), (coq_CNOT y x))), (coq_CNOT x y))

(** val coq_CCX : posi -> posi -> posi -> exp **)

let coq_CCX x y z =
  CU (x, (coq_CNOT y z))

(** val id_nat : int -> int **)

let id_nat i =
  i

(** val avs_for_arith : int -> int -> int * int **)

let avs_for_arith size x =
  ((Nat.div x size), (Nat.modulo x size))

(** val gen_vars' :
    int -> var list -> int -> int -> ((int * int) * (int -> int)) * (int ->
    int) **)

let rec gen_vars' size l start0 x =
  match l with
  | [] -> (((0, 0), id_nat), id_nat)
  | x0 :: xl ->
    if (=) x0 x
    then (((start0, size), id_nat), id_nat)
    else gen_vars' size xl (add start0 size) x

(** val gen_vars :
    int -> var list -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let gen_vars size l =
  gen_vars' size l 0

(** val findnum' : int -> int -> int -> int -> int **)

let rec findnum' size x y i =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> i)
    (fun n ->
    if (<=) y x
    then i
    else findnum' n (mul (Pervasives.succ (Pervasives.succ 0)) x) y
           (add i (Pervasives.succ 0)))
    size

(** val findnum : int -> int -> int **)

let findnum x n =
  findnum' n x
    (Nat.pow (Pervasives.succ (Pervasives.succ 0))
      (sub n (Pervasives.succ 0))) 0

(** val copyto : var -> var -> int -> exp **)

let rec copyto x y size =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (x, 0))
    (fun m -> Seq ((copyto x y m), (coq_CNOT (x, m) (y, m))))
    size

(** val div_two_spec : (int -> bool) -> int -> bool **)

let div_two_spec f i =
  f (add i (Pervasives.succ 0))

(** val bin_xor : (int -> bool) -> (int -> bool) -> int -> int -> bool **)

let bin_xor f1 f2 size =
  cut_n (fun x -> xorb (f1 x) (f2 x)) size
