
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x0, _) -> x0

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> int **)

let rec length = List.length

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app = List.append

type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

(** val compareSpec2Type : comparison -> compareSpecT **)

let compareSpec2Type = function
| Eq -> CompEqT
| Lt -> CompLtT
| Gt -> CompGtT

type 'a compSpecT = compareSpecT

(** val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT **)

let compSpec2Type _ _ =
  compareSpec2Type

(** val add : int -> int -> int **)

let rec add = (+)

(** val mul : int -> int -> int **)

let rec mul = ( * )



module type EqLtLe =
 sig
  type t
 end

module type OrderedType =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> bool
 end

module type OrderedType' =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> bool
 end

module OT_to_Full =
 functor (O:OrderedType') ->
 struct
  type t = O.t

  (** val compare : t -> t -> comparison **)

  let compare =
    O.compare

  (** val eq_dec : t -> t -> bool **)

  let eq_dec =
    O.eq_dec
 end

module MakeOrderTac =
 functor (O:EqLtLe) ->
 functor (P:sig
 end) ->
 struct
 end

module OT_to_OrderTac =
 functor (OT:OrderedType) ->
 struct
  module OTF = OT_to_Full(OT)

  module TO =
   struct
    type t = OTF.t

    (** val compare : t -> t -> comparison **)

    let compare =
      OTF.compare

    (** val eq_dec : t -> t -> bool **)

    let eq_dec =
      OTF.eq_dec
   end
 end

module OrderedTypeFacts =
 functor (O:OrderedType') ->
 struct
  module OrderTac = OT_to_OrderTac(O)

  (** val eq_dec : O.t -> O.t -> bool **)

  let eq_dec =
    O.eq_dec

  (** val lt_dec : O.t -> O.t -> bool **)

  let lt_dec x0 y =
    let c = compSpec2Type x0 y (O.compare x0 y) in
    (match c with
     | CompLtT -> true
     | _ -> false)

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x0 y =
    if eq_dec x0 y then true else false
 end

module Nat =
 struct
  (** val compare : int -> int -> comparison **)

  let rec compare = fun n m -> if n=m then Eq else if n<m then Lt else Gt
 end

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = List.rev

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t1 -> (f a) :: (map f t1)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: t1 -> f b (fold_right f a0 t1)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| [] -> true
| a :: l0 -> (&&) (f a) (forallb f l0)

module Pos =
 struct
  (** val succ : int -> int **)

  let rec succ = Pervasives.succ

  (** val add : int -> int -> int **)

  let rec add = (+)

  (** val add_carry : int -> int -> int **)

  and add_carry x0 y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add_carry p0 q))
        (fun q -> (fun p->2*p) (add_carry p0 q))
        (fun _ -> (fun p->1+2*p) (succ p0))
        y)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p0 q))
        (fun q -> (fun p->1+2*p) (add p0 q))
        (fun _ -> (fun p->2*p) (succ p0))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (succ q))
        (fun q -> (fun p->2*p) (succ q))
        (fun _ -> (fun p->1+2*p) 1)
        y)
      x0

  (** val pred_double : int -> int **)

  let rec pred_double x0 =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> (fun p->1+2*p) ((fun p->2*p) p0))
      (fun p0 -> (fun p->1+2*p) (pred_double p0))
      (fun _ -> 1)
      x0

  (** val mul : int -> int -> int **)

  let rec mul = ( * )

  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont = fun c x y -> if x=y then c else if x<y then Lt else Gt

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val eqb : int -> int -> bool **)

  let rec eqb p0 q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p1 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> eqb p1 q0)
        (fun _ -> false)
        (fun _ -> false)
        q)
      (fun p1 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun q0 -> eqb p1 q0)
        (fun _ -> false)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        q)
      p0

  (** val eq_dec : int -> int -> bool **)

  let rec eq_dec p0 x0 =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p1 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p2 -> eq_dec p1 p2)
        (fun _ -> false)
        (fun _ -> false)
        x0)
      (fun p1 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun p2 -> eq_dec p1 p2)
        (fun _ -> false)
        x0)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        x0)
      p0
 end

module Z =
 struct
  (** val double : int -> int **)

  let double x0 =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p0 -> ((fun p->2*p) p0))
      (fun p0 -> (~-) ((fun p->2*p) p0))
      x0

  (** val succ_double : int -> int **)

  let succ_double x0 =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p0 -> ((fun p->1+2*p) p0))
      (fun p0 -> (~-) (Pos.pred_double p0))
      x0

  (** val pred_double : int -> int **)

  let pred_double x0 =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (~-) 1)
      (fun p0 -> (Pos.pred_double p0))
      (fun p0 -> (~-) ((fun p->1+2*p) p0))
      x0

  (** val pos_sub : int -> int -> int **)

  let rec pos_sub x0 y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double (pos_sub p0 q))
        (fun q -> succ_double (pos_sub p0 q))
        (fun _ -> ((fun p->2*p) p0))
        y)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> pred_double (pos_sub p0 q))
        (fun q -> double (pos_sub p0 q))
        (fun _ -> (Pos.pred_double p0))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (~-) ((fun p->2*p) q))
        (fun q -> (~-) (Pos.pred_double q))
        (fun _ -> 0)
        y)
      x0

  (** val add : int -> int -> int **)

  let add = (+)

  (** val opp : int -> int **)

  let opp = (~-)

  (** val sub : int -> int -> int **)

  let sub = (-)

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val leb : int -> int -> bool **)

  let leb x0 y =
    match compare x0 y with
    | Gt -> false
    | _ -> true

  (** val ltb : int -> int -> bool **)

  let ltb x0 y =
    match compare x0 y with
    | Lt -> true
    | _ -> false

  (** val eqb : int -> int -> bool **)

  let rec eqb x0 y =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> false)
        y)
      (fun p0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun q -> Pos.eqb p0 q)
        (fun _ -> false)
        y)
      (fun p0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun _ -> false)
        (fun q -> Pos.eqb p0 q)
        y)
      x0

  (** val max : int -> int -> int **)

  let max = Pervasives.max

  (** val eq_dec : int -> int -> bool **)

  let eq_dec x0 y =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> false)
        y)
      (fun x1 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun p0 -> Pos.eq_dec x1 p0)
        (fun _ -> false)
        y)
      (fun x1 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun _ -> false)
        (fun p0 -> Pos.eq_dec x1 p0)
        y)
      x0
 end

type 'x compare0 =
| LT
| EQ
| GT

module type Coq_OrderedType =
 sig
  type t

  val compare : t -> t -> t compare0

  val eq_dec : t -> t -> bool
 end

module Coq_OrderedTypeFacts =
 functor (O:Coq_OrderedType) ->
 struct
  module TO =
   struct
    type t = O.t
   end

  module IsTO =
   struct
   end

  module OrderTac = MakeOrderTac(TO)(IsTO)

  (** val eq_dec : O.t -> O.t -> bool **)

  let eq_dec =
    O.eq_dec

  (** val lt_dec : O.t -> O.t -> bool **)

  let lt_dec x0 y =
    match O.compare x0 y with
    | LT -> true
    | _ -> false

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x0 y =
    if eq_dec x0 y then true else false
 end

module KeyOrderedType =
 functor (O:Coq_OrderedType) ->
 struct
  module MO = Coq_OrderedTypeFacts(O)
 end

module Nat_as_OT =
 struct
  type t = int

  (** val compare : int -> int -> int compare0 **)

  let compare x0 y =
    match Nat.compare x0 y with
    | Eq -> EQ
    | Lt -> LT
    | Gt -> GT

  (** val eq_dec : int -> int -> bool **)

  let eq_dec =
    (=)
 end

module type Int =
 sig
  type t

  val i2z : t -> int

  val _0 : t

  val _1 : t

  val _2 : t

  val _3 : t

  val add : t -> t -> t

  val opp : t -> t

  val sub : t -> t -> t

  val mul : t -> t -> t

  val max : t -> t -> t

  val eqb : t -> t -> bool

  val ltb : t -> t -> bool

  val leb : t -> t -> bool

  val gt_le_dec : t -> t -> bool

  val ge_lt_dec : t -> t -> bool

  val eq_dec : t -> t -> bool
 end

module Z_as_Int =
 struct
  type t = int

  (** val _0 : int **)

  let _0 =
    0

  (** val _1 : int **)

  let _1 =
    1

  (** val _2 : int **)

  let _2 =
    ((fun p->2*p) 1)

  (** val _3 : int **)

  let _3 =
    ((fun p->1+2*p) 1)

  (** val add : int -> int -> int **)

  let add =
    Z.add

  (** val opp : int -> int **)

  let opp =
    Z.opp

  (** val sub : int -> int -> int **)

  let sub =
    Z.sub

  (** val mul : int -> int -> int **)

  let mul =
    Z.mul

  (** val max : int -> int -> int **)

  let max =
    Z.max

  (** val eqb : int -> int -> bool **)

  let eqb =
    Z.eqb

  (** val ltb : int -> int -> bool **)

  let ltb =
    Z.ltb

  (** val leb : int -> int -> bool **)

  let leb =
    Z.leb

  (** val eq_dec : int -> int -> bool **)

  let eq_dec =
    Z.eq_dec

  (** val gt_le_dec : int -> int -> bool **)

  let gt_le_dec i j =
    let b = Z.ltb j i in if b then true else false

  (** val ge_lt_dec : int -> int -> bool **)

  let ge_lt_dec i j =
    let b = Z.ltb i j in if b then false else true

  (** val i2z : t -> int **)

  let i2z n =
    n
 end

module MakeListOrdering =
 functor (O:OrderedType) ->
 struct
  module MO = OrderedTypeFacts(O)
 end

module MakeRaw =
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct
  type elt = X.t

  type tree =
  | Leaf
  | Node of I.t * tree * X.t * tree

  (** val empty : tree **)

  let empty =
    Leaf

  (** val is_empty : tree -> bool **)

  let is_empty = function
  | Leaf -> true
  | Node (_, _, _, _) -> false

  (** val mem : X.t -> tree -> bool **)

  let rec mem x0 = function
  | Leaf -> false
  | Node (_, l, k, r) ->
    (match X.compare x0 k with
     | Eq -> true
     | Lt -> mem x0 l
     | Gt -> mem x0 r)

  (** val min_elt : tree -> elt option **)

  let rec min_elt = function
  | Leaf -> None
  | Node (_, l, x0, _) ->
    (match l with
     | Leaf -> Some x0
     | Node (_, _, _, _) -> min_elt l)

  (** val max_elt : tree -> elt option **)

  let rec max_elt = function
  | Leaf -> None
  | Node (_, _, x0, r) ->
    (match r with
     | Leaf -> Some x0
     | Node (_, _, _, _) -> max_elt r)

  (** val choose : tree -> elt option **)

  let choose =
    min_elt

  (** val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1 **)

  let rec fold f t1 base =
    match t1 with
    | Leaf -> base
    | Node (_, l, x0, r) -> fold f r (f x0 (fold f l base))

  (** val elements_aux : X.t list -> tree -> X.t list **)

  let rec elements_aux acc = function
  | Leaf -> acc
  | Node (_, l, x0, r) -> elements_aux (x0 :: (elements_aux acc r)) l

  (** val elements : tree -> X.t list **)

  let elements =
    elements_aux []

  (** val rev_elements_aux : X.t list -> tree -> X.t list **)

  let rec rev_elements_aux acc = function
  | Leaf -> acc
  | Node (_, l, x0, r) -> rev_elements_aux (x0 :: (rev_elements_aux acc l)) r

  (** val rev_elements : tree -> X.t list **)

  let rev_elements =
    rev_elements_aux []

  (** val cardinal : tree -> int **)

  let rec cardinal = function
  | Leaf -> 0
  | Node (_, l, _, r) -> Pervasives.succ (add (cardinal l) (cardinal r))

  (** val maxdepth : tree -> int **)

  let rec maxdepth = function
  | Leaf -> 0
  | Node (_, l, _, r) ->
    Pervasives.succ (Pervasives.max (maxdepth l) (maxdepth r))

  (** val mindepth : tree -> int **)

  let rec mindepth = function
  | Leaf -> 0
  | Node (_, l, _, r) ->
    Pervasives.succ (Pervasives.min (mindepth l) (mindepth r))

  (** val for_all : (elt -> bool) -> tree -> bool **)

  let rec for_all f = function
  | Leaf -> true
  | Node (_, l, x0, r) ->
    if if f x0 then for_all f l else false then for_all f r else false

  (** val exists_ : (elt -> bool) -> tree -> bool **)

  let rec exists_ f = function
  | Leaf -> false
  | Node (_, l, x0, r) ->
    if if f x0 then true else exists_ f l then true else exists_ f r

  type enumeration =
  | End
  | More of elt * tree * enumeration

  (** val cons : tree -> enumeration -> enumeration **)

  let rec cons s e =
    match s with
    | Leaf -> e
    | Node (_, l, x0, r) -> cons l (More (x0, r, e))

  (** val compare_more :
      X.t -> (enumeration -> comparison) -> enumeration -> comparison **)

  let compare_more x1 cont = function
  | End -> Gt
  | More (x2, r2, e3) ->
    (match X.compare x1 x2 with
     | Eq -> cont (cons r2 e3)
     | x0 -> x0)

  (** val compare_cont :
      tree -> (enumeration -> comparison) -> enumeration -> comparison **)

  let rec compare_cont s1 cont e2 =
    match s1 with
    | Leaf -> cont e2
    | Node (_, l1, x1, r1) ->
      compare_cont l1 (compare_more x1 (compare_cont r1 cont)) e2

  (** val compare_end : enumeration -> comparison **)

  let compare_end = function
  | End -> Eq
  | More (_, _, _) -> Lt

  (** val compare : tree -> tree -> comparison **)

  let compare s1 s2 =
    compare_cont s1 compare_end (cons s2 End)

  (** val equal : tree -> tree -> bool **)

  let equal s1 s2 =
    match compare s1 s2 with
    | Eq -> true
    | _ -> false

  (** val subsetl : (tree -> bool) -> X.t -> tree -> bool **)

  let rec subsetl subset_l1 x1 s2 = match s2 with
  | Leaf -> false
  | Node (_, l2, x2, r2) ->
    (match X.compare x1 x2 with
     | Eq -> subset_l1 l2
     | Lt -> subsetl subset_l1 x1 l2
     | Gt -> if mem x1 r2 then subset_l1 s2 else false)

  (** val subsetr : (tree -> bool) -> X.t -> tree -> bool **)

  let rec subsetr subset_r1 x1 s2 = match s2 with
  | Leaf -> false
  | Node (_, l2, x2, r2) ->
    (match X.compare x1 x2 with
     | Eq -> subset_r1 r2
     | Lt -> if mem x1 l2 then subset_r1 s2 else false
     | Gt -> subsetr subset_r1 x1 r2)

  (** val subset : tree -> tree -> bool **)

  let rec subset s1 s2 =
    match s1 with
    | Leaf -> true
    | Node (_, l1, x1, r1) ->
      (match s2 with
       | Leaf -> false
       | Node (_, l2, x2, r2) ->
         (match X.compare x1 x2 with
          | Eq -> if subset l1 l2 then subset r1 r2 else false
          | Lt -> if subsetl (subset l1) x1 l2 then subset r1 s2 else false
          | Gt -> if subsetr (subset r1) x1 r2 then subset l1 s2 else false))

  type t = tree

  (** val height : t -> I.t **)

  let height = function
  | Leaf -> I._0
  | Node (h0, _, _, _) -> h0

  (** val singleton : X.t -> tree **)

  let singleton x0 =
    Node (I._1, Leaf, x0, Leaf)

  (** val create : t -> X.t -> t -> tree **)

  let create l x0 r =
    Node ((I.add (I.max (height l) (height r)) I._1), l, x0, r)

  (** val assert_false : t -> X.t -> t -> tree **)

  let assert_false =
    create

  (** val bal : t -> X.t -> t -> tree **)

  let bal l x0 r =
    let hl = height l in
    let hr = height r in
    if I.ltb (I.add hr I._2) hl
    then (match l with
          | Leaf -> assert_false l x0 r
          | Node (_, ll, lx, lr) ->
            if I.leb (height lr) (height ll)
            then create ll lx (create lr x0 r)
            else (match lr with
                  | Leaf -> assert_false l x0 r
                  | Node (_, lrl, lrx, lrr) ->
                    create (create ll lx lrl) lrx (create lrr x0 r)))
    else if I.ltb (I.add hl I._2) hr
         then (match r with
               | Leaf -> assert_false l x0 r
               | Node (_, rl, rx, rr) ->
                 if I.leb (height rl) (height rr)
                 then create (create l x0 rl) rx rr
                 else (match rl with
                       | Leaf -> assert_false l x0 r
                       | Node (_, rll, rlx, rlr) ->
                         create (create l x0 rll) rlx (create rlr rx rr)))
         else create l x0 r

  (** val add : X.t -> tree -> tree **)

  let rec add x0 = function
  | Leaf -> Node (I._1, Leaf, x0, Leaf)
  | Node (h0, l, y, r) ->
    (match X.compare x0 y with
     | Eq -> Node (h0, l, y, r)
     | Lt -> bal (add x0 l) y r
     | Gt -> bal l y (add x0 r))

  (** val join : tree -> elt -> t -> t **)

  let rec join l = match l with
  | Leaf -> add
  | Node (lh, ll, lx, lr) ->
    (fun x0 ->
      let rec join_aux r = match r with
      | Leaf -> add x0 l
      | Node (rh, rl, rx, rr) ->
        if I.ltb (I.add rh I._2) lh
        then bal ll lx (join lr x0 r)
        else if I.ltb (I.add lh I._2) rh
             then bal (join_aux rl) rx rr
             else create l x0 r
      in join_aux)

  (** val remove_min : tree -> elt -> t -> t * elt **)

  let rec remove_min l x0 r =
    match l with
    | Leaf -> (r, x0)
    | Node (_, ll, lx, lr) ->
      let (l', m) = remove_min ll lx lr in ((bal l' x0 r), m)

  (** val merge : tree -> tree -> tree **)

  let merge s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (_, _, _, _) ->
      (match s2 with
       | Leaf -> s1
       | Node (_, l2, x2, r2) ->
         let (s2', m) = remove_min l2 x2 r2 in bal s1 m s2')

  (** val remove : X.t -> tree -> tree **)

  let rec remove x0 = function
  | Leaf -> Leaf
  | Node (_, l, y, r) ->
    (match X.compare x0 y with
     | Eq -> merge l r
     | Lt -> bal (remove x0 l) y r
     | Gt -> bal l y (remove x0 r))

  (** val concat : tree -> tree -> tree **)

  let concat s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (_, _, _, _) ->
      (match s2 with
       | Leaf -> s1
       | Node (_, l2, x2, r2) ->
         let (s2', m) = remove_min l2 x2 r2 in join s1 m s2')

  type triple = { t_left : t; t_in : bool; t_right : t }

  (** val t_left : triple -> t **)

  let t_left t1 =
    t1.t_left

  (** val t_in : triple -> bool **)

  let t_in t1 =
    t1.t_in

  (** val t_right : triple -> t **)

  let t_right t1 =
    t1.t_right

  (** val split : X.t -> tree -> triple **)

  let rec split x0 = function
  | Leaf -> { t_left = Leaf; t_in = false; t_right = Leaf }
  | Node (_, l, y, r) ->
    (match X.compare x0 y with
     | Eq -> { t_left = l; t_in = true; t_right = r }
     | Lt ->
       let { t_left = ll; t_in = b; t_right = rl } = split x0 l in
       { t_left = ll; t_in = b; t_right = (join rl y r) }
     | Gt ->
       let { t_left = rl; t_in = b; t_right = rr } = split x0 r in
       { t_left = (join l y rl); t_in = b; t_right = rr })

  (** val inter : tree -> tree -> tree **)

  let rec inter s1 s2 =
    match s1 with
    | Leaf -> Leaf
    | Node (_, l1, x1, r1) ->
      (match s2 with
       | Leaf -> Leaf
       | Node (_, _, _, _) ->
         let { t_left = l2'; t_in = pres; t_right = r2' } = split x1 s2 in
         if pres
         then join (inter l1 l2') x1 (inter r1 r2')
         else concat (inter l1 l2') (inter r1 r2'))

  (** val diff : tree -> tree -> tree **)

  let rec diff s1 s2 =
    match s1 with
    | Leaf -> Leaf
    | Node (_, l1, x1, r1) ->
      (match s2 with
       | Leaf -> s1
       | Node (_, _, _, _) ->
         let { t_left = l2'; t_in = pres; t_right = r2' } = split x1 s2 in
         if pres
         then concat (diff l1 l2') (diff r1 r2')
         else join (diff l1 l2') x1 (diff r1 r2'))

  (** val union : tree -> tree -> tree **)

  let rec union s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (_, l1, x1, r1) ->
      (match s2 with
       | Leaf -> s1
       | Node (_, _, _, _) ->
         let { t_left = l2'; t_in = _; t_right = r2' } = split x1 s2 in
         join (union l1 l2') x1 (union r1 r2'))

  (** val filter : (elt -> bool) -> tree -> tree **)

  let rec filter f = function
  | Leaf -> Leaf
  | Node (_, l, x0, r) ->
    let l' = filter f l in
    let r' = filter f r in if f x0 then join l' x0 r' else concat l' r'

  (** val partition : (elt -> bool) -> t -> t * t **)

  let rec partition f = function
  | Leaf -> (Leaf, Leaf)
  | Node (_, l, x0, r) ->
    let (l1, l2) = partition f l in
    let (r1, r2) = partition f r in
    if f x0
    then ((join l1 x0 r1), (concat l2 r2))
    else ((concat l1 r1), (join l2 x0 r2))

  (** val ltb_tree : X.t -> tree -> bool **)

  let rec ltb_tree x0 = function
  | Leaf -> true
  | Node (_, l, y, r) ->
    (match X.compare x0 y with
     | Gt -> (&&) (ltb_tree x0 l) (ltb_tree x0 r)
     | _ -> false)

  (** val gtb_tree : X.t -> tree -> bool **)

  let rec gtb_tree x0 = function
  | Leaf -> true
  | Node (_, l, y, r) ->
    (match X.compare x0 y with
     | Lt -> (&&) (gtb_tree x0 l) (gtb_tree x0 r)
     | _ -> false)

  (** val isok : tree -> bool **)

  let rec isok = function
  | Leaf -> true
  | Node (_, l, x0, r) ->
    (&&) ((&&) ((&&) (isok l) (isok r)) (ltb_tree x0 l)) (gtb_tree x0 r)

  module MX = OrderedTypeFacts(X)

  type coq_R_min_elt =
  | R_min_elt_0 of tree
  | R_min_elt_1 of tree * I.t * tree * X.t * tree
  | R_min_elt_2 of tree * I.t * tree * X.t * tree * I.t * tree * X.t * 
     tree * elt option * coq_R_min_elt

  type coq_R_max_elt =
  | R_max_elt_0 of tree
  | R_max_elt_1 of tree * I.t * tree * X.t * tree
  | R_max_elt_2 of tree * I.t * tree * X.t * tree * I.t * tree * X.t * 
     tree * elt option * coq_R_max_elt

  module L = MakeListOrdering(X)

  (** val flatten_e : enumeration -> elt list **)

  let rec flatten_e = function
  | End -> []
  | More (x0, t1, r) -> x0 :: (app (elements t1) (flatten_e r))

  type coq_R_bal =
  | R_bal_0 of t * X.t * t
  | R_bal_1 of t * X.t * t * I.t * tree * X.t * tree
  | R_bal_2 of t * X.t * t * I.t * tree * X.t * tree
  | R_bal_3 of t * X.t * t * I.t * tree * X.t * tree * I.t * tree * X.t * tree
  | R_bal_4 of t * X.t * t
  | R_bal_5 of t * X.t * t * I.t * tree * X.t * tree
  | R_bal_6 of t * X.t * t * I.t * tree * X.t * tree
  | R_bal_7 of t * X.t * t * I.t * tree * X.t * tree * I.t * tree * X.t * tree
  | R_bal_8 of t * X.t * t

  type coq_R_remove_min =
  | R_remove_min_0 of tree * elt * t
  | R_remove_min_1 of tree * elt * t * I.t * tree * X.t * tree * (t * elt)
     * coq_R_remove_min * t * elt

  type coq_R_merge =
  | R_merge_0 of tree * tree
  | R_merge_1 of tree * tree * I.t * tree * X.t * tree
  | R_merge_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
     X.t * tree * t * elt

  type coq_R_concat =
  | R_concat_0 of tree * tree
  | R_concat_1 of tree * tree * I.t * tree * X.t * tree
  | R_concat_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
     X.t * tree * t * elt

  type coq_R_inter =
  | R_inter_0 of tree * tree
  | R_inter_1 of tree * tree * I.t * tree * X.t * tree
  | R_inter_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
     X.t * tree * t * bool * t * tree * coq_R_inter * tree * coq_R_inter
  | R_inter_3 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
     X.t * tree * t * bool * t * tree * coq_R_inter * tree * coq_R_inter

  type coq_R_diff =
  | R_diff_0 of tree * tree
  | R_diff_1 of tree * tree * I.t * tree * X.t * tree
  | R_diff_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
     X.t * tree * t * bool * t * tree * coq_R_diff * tree * coq_R_diff
  | R_diff_3 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
     X.t * tree * t * bool * t * tree * coq_R_diff * tree * coq_R_diff

  type coq_R_union =
  | R_union_0 of tree * tree
  | R_union_1 of tree * tree * I.t * tree * X.t * tree
  | R_union_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
     X.t * tree * t * bool * t * tree * coq_R_union * tree * coq_R_union
 end

module IntMake =
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct
  module Raw = MakeRaw(I)(X)

  module E =
   struct
    type t = X.t

    (** val compare : t -> t -> comparison **)

    let compare =
      X.compare

    (** val eq_dec : t -> t -> bool **)

    let eq_dec =
      X.eq_dec
   end

  type elt = X.t

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  (** val this : t_ -> Raw.t **)

  let this t1 =
    t1

  type t = t_

  (** val mem : elt -> t -> bool **)

  let mem x0 s =
    Raw.mem x0 (this s)

  (** val add : elt -> t -> t **)

  let add x0 s =
    Raw.add x0 (this s)

  (** val remove : elt -> t -> t **)

  let remove x0 s =
    Raw.remove x0 (this s)

  (** val singleton : elt -> t **)

  let singleton =
    Raw.singleton

  (** val union : t -> t -> t **)

  let union s s' =
    Raw.union (this s) (this s')

  (** val inter : t -> t -> t **)

  let inter s s' =
    Raw.inter (this s) (this s')

  (** val diff : t -> t -> t **)

  let diff s s' =
    Raw.diff (this s) (this s')

  (** val equal : t -> t -> bool **)

  let equal s s' =
    Raw.equal (this s) (this s')

  (** val subset : t -> t -> bool **)

  let subset s s' =
    Raw.subset (this s) (this s')

  (** val empty : t **)

  let empty =
    Raw.empty

  (** val is_empty : t -> bool **)

  let is_empty s =
    Raw.is_empty (this s)

  (** val elements : t -> elt list **)

  let elements s =
    Raw.elements (this s)

  (** val choose : t -> elt option **)

  let choose s =
    Raw.choose (this s)

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold f s =
    Raw.fold f (this s)

  (** val cardinal : t -> int **)

  let cardinal s =
    Raw.cardinal (this s)

  (** val filter : (elt -> bool) -> t -> t **)

  let filter f s =
    Raw.filter f (this s)

  (** val for_all : (elt -> bool) -> t -> bool **)

  let for_all f s =
    Raw.for_all f (this s)

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let exists_ f s =
    Raw.exists_ f (this s)

  (** val partition : (elt -> bool) -> t -> t * t **)

  let partition f s =
    let p0 = Raw.partition f (this s) in ((fst p0), (snd p0))

  (** val eq_dec : t -> t -> bool **)

  let eq_dec s0 s'0 =
    let b = Raw.equal s0 s'0 in if b then true else false

  (** val compare : t -> t -> comparison **)

  let compare s s' =
    Raw.compare (this s) (this s')

  (** val min_elt : t -> elt option **)

  let min_elt s =
    Raw.min_elt (this s)

  (** val max_elt : t -> elt option **)

  let max_elt s =
    Raw.max_elt (this s)
 end

module type OrderedTypeOrig =
 Coq_OrderedType

module Update_OT =
 functor (O:OrderedTypeOrig) ->
 struct
  type t = O.t

  (** val eq_dec : t -> t -> bool **)

  let eq_dec =
    O.eq_dec

  (** val compare : O.t -> O.t -> comparison **)

  let compare x0 y =
    match O.compare x0 y with
    | LT -> Lt
    | EQ -> Eq
    | GT -> Gt
 end

module Coq_IntMake =
 functor (I:Int) ->
 functor (X:Coq_OrderedType) ->
 struct
  module X' = Update_OT(X)

  module MSet = IntMake(I)(X')

  type elt = X.t

  type t = MSet.t

  (** val empty : t **)

  let empty =
    MSet.empty

  (** val is_empty : t -> bool **)

  let is_empty =
    MSet.is_empty

  (** val mem : elt -> t -> bool **)

  let mem =
    MSet.mem

  (** val add : elt -> t -> t **)

  let add =
    MSet.add

  (** val singleton : elt -> t **)

  let singleton =
    MSet.singleton

  (** val remove : elt -> t -> t **)

  let remove =
    MSet.remove

  (** val union : t -> t -> t **)

  let union =
    MSet.union

  (** val inter : t -> t -> t **)

  let inter =
    MSet.inter

  (** val diff : t -> t -> t **)

  let diff =
    MSet.diff

  (** val eq_dec : t -> t -> bool **)

  let eq_dec =
    MSet.eq_dec

  (** val equal : t -> t -> bool **)

  let equal =
    MSet.equal

  (** val subset : t -> t -> bool **)

  let subset =
    MSet.subset

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold =
    MSet.fold

  (** val for_all : (elt -> bool) -> t -> bool **)

  let for_all =
    MSet.for_all

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let exists_ =
    MSet.exists_

  (** val filter : (elt -> bool) -> t -> t **)

  let filter =
    MSet.filter

  (** val partition : (elt -> bool) -> t -> t * t **)

  let partition =
    MSet.partition

  (** val cardinal : t -> int **)

  let cardinal =
    MSet.cardinal

  (** val elements : t -> elt list **)

  let elements =
    MSet.elements

  (** val choose : t -> elt option **)

  let choose =
    MSet.choose

  module MF =
   struct
    (** val eqb : X.t -> X.t -> bool **)

    let eqb x0 y =
      if MSet.E.eq_dec x0 y then true else false
   end

  (** val min_elt : t -> elt option **)

  let min_elt =
    MSet.min_elt

  (** val max_elt : t -> elt option **)

  let max_elt =
    MSet.max_elt

  (** val compare : t -> t -> t compare0 **)

  let compare s s' =
    let c = compSpec2Type s s' (MSet.compare s s') in
    (match c with
     | CompEqT -> EQ
     | CompLtT -> LT
     | CompGtT -> GT)

  module E =
   struct
    type t = X.t

    (** val compare : t -> t -> t compare0 **)

    let compare =
      X.compare

    (** val eq_dec : t -> t -> bool **)

    let eq_dec =
      X.eq_dec
   end
 end

module Make =
 functor (X:Coq_OrderedType) ->
 Coq_IntMake(Z_as_Int)(X)

module FSet = Make(Nat_as_OT)

type 'u gate_app =
| App1 of 'u * int
| App2 of 'u * int * int
| App3 of 'u * int * int * int

type 'u gate_list = 'u gate_app list

(** val next_single_qubit_gate :
    'a1 gate_list -> int -> (('a1 gate_list * 'a1) * 'a1 gate_list) option **)

let rec next_single_qubit_gate l q =
  match l with
  | [] -> None
  | g :: t1 ->
    (match g with
     | App1 (u, n) ->
       if (=) n q
       then Some (([], u), t1)
       else (match next_single_qubit_gate t1 q with
             | Some p0 ->
               let (p1, l2) = p0 in
               let (l1, u') = p1 in Some ((((App1 (u, n)) :: l1), u'), l2)
             | None -> None)
     | App2 (u, m, n) ->
       if (||) ((=) m q) ((=) n q)
       then None
       else (match next_single_qubit_gate t1 q with
             | Some p0 ->
               let (p1, l2) = p0 in
               let (l1, u') = p1 in Some ((((App2 (u, m, n)) :: l1), u'), l2)
             | None -> None)
     | App3 (u, m, n, p0) ->
       if (||) ((||) ((=) m q) ((=) n q)) ((=) p0 q)
       then None
       else (match next_single_qubit_gate t1 q with
             | Some p1 ->
               let (p2, l2) = p1 in
               let (l1, u') = p2 in
               Some ((((App3 (u, m, n, p0)) :: l1), u'), l2)
             | None -> None))

(** val last_single_qubit_gate :
    'a1 gate_list -> int -> (('a1 gate_list * 'a1) * 'a1 gate_list) option **)

let last_single_qubit_gate l q =
  match next_single_qubit_gate (rev l) q with
  | Some p0 ->
    let (p1, l2) = p0 in let (l1, u) = p1 in Some (((rev l2), u), (rev l1))
  | None -> None

(** val next_two_qubit_gate :
    'a1 gate_list -> int -> (((('a1 gate_list * 'a1) * int) * int) * 'a1
    gate_list) option **)

let rec next_two_qubit_gate l q =
  match l with
  | [] -> None
  | g :: t1 ->
    (match g with
     | App1 (u, n) ->
       if (=) n q
       then None
       else (match next_two_qubit_gate t1 q with
             | Some p0 ->
               let (p1, l2) = p0 in
               let (p2, n') = p1 in
               let (p3, m') = p2 in
               let (l1, u') = p3 in
               Some ((((((App1 (u, n)) :: l1), u'), m'), n'), l2)
             | None -> None)
     | App2 (u, m, n) ->
       if (||) ((=) m q) ((=) n q)
       then Some (((([], u), m), n), t1)
       else (match next_two_qubit_gate t1 q with
             | Some p0 ->
               let (p1, l2) = p0 in
               let (p2, n') = p1 in
               let (p3, m') = p2 in
               let (l1, u') = p3 in
               Some ((((((App2 (u, m, n)) :: l1), u'), m'), n'), l2)
             | None -> None)
     | App3 (u, m, n, p0) ->
       if (||) ((||) ((=) m q) ((=) n q)) ((=) p0 q)
       then None
       else (match next_two_qubit_gate t1 q with
             | Some p1 ->
               let (p2, l2) = p1 in
               let (p3, n') = p2 in
               let (p4, m') = p3 in
               let (l1, u') = p4 in
               Some ((((((App3 (u, m, n, p0)) :: l1), u'), m'), n'), l2)
             | None -> None))

(** val next_gate :
    'a1 gate_list -> FSet.t -> (('a1 gate_list * 'a1 gate_app) * 'a1
    gate_list) option **)

let rec next_gate l qs =
  match l with
  | [] -> None
  | g :: t1 ->
    (match g with
     | App1 (u, q) ->
       if FSet.mem q qs
       then Some (([], (App1 (u, q))), t1)
       else (match next_gate t1 qs with
             | Some p0 ->
               let (p1, l2) = p0 in
               let (l1, g0) = p1 in Some ((((App1 (u, q)) :: l1), g0), l2)
             | None -> None)
     | App2 (u, q1, q2) ->
       if (||) (FSet.mem q1 qs) (FSet.mem q2 qs)
       then Some (([], (App2 (u, q1, q2))), t1)
       else (match next_gate t1 qs with
             | Some p0 ->
               let (p1, l2) = p0 in
               let (l1, g0) = p1 in
               Some ((((App2 (u, q1, q2)) :: l1), g0), l2)
             | None -> None)
     | App3 (u, q1, q2, q3) ->
       if (||) ((||) (FSet.mem q1 qs) (FSet.mem q2 qs)) (FSet.mem q3 qs)
       then Some (([], (App3 (u, q1, q2, q3))), t1)
       else (match next_gate t1 qs with
             | Some p0 ->
               let (p1, l2) = p0 in
               let (l1, g0) = p1 in
               Some ((((App3 (u, q1, q2, q3)) :: l1), g0), l2)
             | None -> None))

(** val does_not_reference_appl : int -> 'a1 gate_app -> bool **)

let does_not_reference_appl q = function
| App1 (_, n) -> negb ((=) n q)
| App2 (_, m, n) -> negb ((||) ((=) m q) ((=) n q))
| App3 (_, m, n, p0) -> negb ((||) ((||) ((=) m q) ((=) n q)) ((=) p0 q))

(** val does_not_reference : 'a1 gate_list -> int -> bool **)

let does_not_reference l q =
  forallb (does_not_reference_appl q) l

(** val try_rewrites :
    'a1 gate_list -> ('a1 gate_list -> 'a1 gate_list option) list -> 'a1
    gate_list option **)

let rec try_rewrites l = function
| [] -> None
| h0 :: t1 -> (match h0 l with
               | Some l' -> Some l'
               | None -> try_rewrites l t1)

(** val try_rewrites2 :
    'a1 gate_list -> ('a1 gate_list -> ('a1 gate_list * 'a1 gate_list)
    option) list -> ('a1 gate_list * 'a1 gate_list) option **)

let rec try_rewrites2 l = function
| [] -> None
| h0 :: t1 ->
  (match h0 l with
   | Some l' -> Some l'
   | None -> try_rewrites2 l t1)

(** val propagate :
    'a1 gate_list -> ('a1 gate_list -> ('a1 gate_list * 'a1 gate_list)
    option) list -> ('a1 gate_list -> 'a1 gate_list option) list -> int ->
    'a1 gate_list option **)

let rec propagate l commute_rules cancel_rules n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> None)
    (fun n' ->
    match try_rewrites l cancel_rules with
    | Some l' -> Some l'
    | None ->
      (match try_rewrites2 l commute_rules with
       | Some p0 ->
         let (l1, l2) = p0 in
         (match propagate l2 commute_rules cancel_rules n' with
          | Some l2' -> Some (app l1 l2')
          | None -> None)
       | None -> None))
    n

type 'u single_qubit_pattern = 'u list

(** val single_qubit_pattern_to_program :
    'a1 single_qubit_pattern -> int -> 'a1 gate_list **)

let rec single_qubit_pattern_to_program pat q =
  match pat with
  | [] -> []
  | u :: t1 -> (App1 (u, q)) :: (single_qubit_pattern_to_program t1 q)

(** val remove_single_qubit_pattern :
    'a1 gate_list -> int -> 'a1 single_qubit_pattern -> ('a1 -> 'a1 -> bool)
    -> 'a1 gate_list option **)

let rec remove_single_qubit_pattern l q pat match_gate0 =
  match pat with
  | [] -> Some l
  | u :: t1 ->
    (match next_single_qubit_gate l q with
     | Some p0 ->
       let (p1, l2) = p0 in
       let (l1, u') = p1 in
       if match_gate0 u u'
       then remove_single_qubit_pattern (app l1 l2) q t1 match_gate0
       else None
     | None -> None)

(** val replace_single_qubit_pattern :
    'a1 gate_list -> int -> 'a1 single_qubit_pattern -> 'a1
    single_qubit_pattern -> ('a1 -> 'a1 -> bool) -> 'a1 gate_list option **)

let replace_single_qubit_pattern l q pat rep match_gate0 =
  match remove_single_qubit_pattern l q pat match_gate0 with
  | Some l' -> Some (app (single_qubit_pattern_to_program rep q) l')
  | None -> None

type pI4_Unitary =
| UPI4_H
| UPI4_X
| UPI4_PI4 of int
| UPI4_CNOT

(** val uPI4_T : pI4_Unitary **)

let uPI4_T =
  UPI4_PI4 1

(** val uPI4_P : pI4_Unitary **)

let uPI4_P =
  UPI4_PI4 ((fun p->2*p) 1)

(** val uPI4_Z : pI4_Unitary **)

let uPI4_Z =
  UPI4_PI4 ((fun p->2*p) ((fun p->2*p) 1))

(** val uPI4_PDAG : pI4_Unitary **)

let uPI4_PDAG =
  UPI4_PI4 ((fun p->2*p) ((fun p->1+2*p) 1))

(** val uPI4_TDAG : pI4_Unitary **)

let uPI4_TDAG =
  UPI4_PI4 ((fun p->1+2*p) ((fun p->1+2*p) 1))

(** val t0 : int -> pI4_Unitary gate_app **)

let t0 q =
  App1 (uPI4_T, q)

(** val tDAG : int -> pI4_Unitary gate_app **)

let tDAG q =
  App1 (uPI4_TDAG, q)

(** val p : int -> pI4_Unitary gate_app **)

let p q =
  App1 (uPI4_P, q)

(** val pDAG : int -> pI4_Unitary gate_app **)

let pDAG q =
  App1 (uPI4_PDAG, q)

(** val z : int -> pI4_Unitary gate_app **)

let z q =
  App1 (uPI4_Z, q)

(** val h : int -> pI4_Unitary gate_app **)

let h q =
  App1 (UPI4_H, q)

(** val x : int -> pI4_Unitary gate_app **)

let x q =
  App1 (UPI4_X, q)

(** val cNOT : int -> int -> pI4_Unitary gate_app **)

let cNOT q1 q2 =
  App2 (UPI4_CNOT, q1, q2)

type pI4_ucom_l = pI4_Unitary gate_list

(** val cCX : int -> int -> int -> pI4_ucom_l **)

let cCX a b c =
  (h c) :: ((cNOT b c) :: ((tDAG c) :: ((cNOT a c) :: ((t0 c) :: ((cNOT b c) :: (
    (tDAG c) :: ((cNOT a c) :: ((cNOT a b) :: ((tDAG b) :: ((cNOT a b) :: (
    (t0 a) :: ((t0 b) :: ((t0 c) :: ((h c) :: []))))))))))))))

(** val cCZ : int -> int -> int -> pI4_ucom_l **)

let cCZ a b c =
  (cNOT b c) :: ((tDAG c) :: ((cNOT a c) :: ((t0 c) :: ((cNOT b c) :: (
    (tDAG c) :: ((cNOT a c) :: ((cNOT a b) :: ((tDAG b) :: ((cNOT a b) :: (
    (t0 a) :: ((t0 b) :: ((t0 c) :: []))))))))))))

(** val match_gate : pI4_Unitary -> pI4_Unitary -> bool **)

let match_gate u u' =
  match u with
  | UPI4_H -> (match u' with
               | UPI4_H -> true
               | _ -> false)
  | UPI4_X -> (match u' with
               | UPI4_X -> true
               | _ -> false)
  | UPI4_PI4 k -> (match u' with
                   | UPI4_PI4 k' -> Z.eqb k k'
                   | _ -> false)
  | UPI4_CNOT -> (match u' with
                  | UPI4_CNOT -> true
                  | _ -> false)

(** val rz_commute_rule1 :
    int -> pI4_ucom_l -> (pI4_Unitary gate_app list * pI4_Unitary gate_list)
    option **)

let rz_commute_rule1 q l =
  match next_single_qubit_gate l q with
  | Some p0 ->
    let (p1, l2) = p0 in
    let (l1, p2) = p1 in
    (match p2 with
     | UPI4_H ->
       (match next_two_qubit_gate l2 q with
        | Some p3 ->
          let (p4, l4) = p3 in
          let (p5, q2) = p4 in
          let (p6, q1) = p5 in
          let (l3, p7) = p6 in
          (match p7 with
           | UPI4_CNOT ->
             if (=) q q2
             then (match next_single_qubit_gate l4 q with
                   | Some p8 ->
                     let (p9, l6) = p8 in
                     let (l5, p10) = p9 in
                     (match p10 with
                      | UPI4_H ->
                        Some
                          ((app l1
                             (app ((h q) :: [])
                               (app l3
                                 (app ((cNOT q1 q) :: [])
                                   (app l5 ((h q) :: [])))))), l6)
                      | _ -> None)
                   | None -> None)
             else None
           | _ -> None)
        | None -> None)
     | _ -> None)
  | None -> None

(** val rz_commute_rule2 :
    int -> pI4_ucom_l -> (pI4_Unitary gate_app list * pI4_Unitary gate_list)
    option **)

let rz_commute_rule2 q l =
  match next_two_qubit_gate l q with
  | Some p0 ->
    let (p1, l2) = p0 in
    let (p2, q2) = p1 in
    let (p3, q1) = p2 in
    let (l1, p4) = p3 in
    (match p4 with
     | UPI4_CNOT ->
       if (=) q q2
       then (match next_single_qubit_gate l2 q with
             | Some p5 ->
               let (p6, l4) = p5 in
               let (l3, u) = p6 in
               (match u with
                | UPI4_PI4 _ ->
                  (match next_two_qubit_gate l4 q with
                   | Some p7 ->
                     let (p8, l6) = p7 in
                     let (p9, q4) = p8 in
                     let (p10, q3) = p9 in
                     let (l5, p11) = p10 in
                     (match p11 with
                      | UPI4_CNOT ->
                        if (&&) ((&&) ((=) q q4) ((=) q1 q3))
                             (does_not_reference (app l3 l5) q3)
                        then Some
                               ((app l1
                                  (app ((cNOT q1 q) :: [])
                                    (app l3
                                      (app ((App1 (u, q)) :: [])
                                        (app l5 ((cNOT q1 q) :: [])))))), l6)
                        else None
                      | _ -> None)
                   | None -> None)
                | _ -> None)
             | None -> None)
       else None
     | _ -> None)
  | None -> None

(** val rz_commute_rule3 :
    int -> pI4_ucom_l -> (pI4_Unitary gate_app list * pI4_Unitary gate_list)
    option **)

let rz_commute_rule3 q l =
  match next_two_qubit_gate l q with
  | Some p0 ->
    let (p1, l2) = p0 in
    let (p2, q2) = p1 in
    let (p3, q1) = p2 in
    let (l1, p4) = p3 in
    (match p4 with
     | UPI4_CNOT ->
       if (=) q q1 then Some ((app l1 ((cNOT q1 q2) :: [])), l2) else None
     | _ -> None)
  | None -> None

(** val rz_commute_rules :
    int -> (pI4_ucom_l -> (pI4_Unitary gate_app list * pI4_Unitary gate_list)
    option) list **)

let rz_commute_rules q =
  (rz_commute_rule1 q) :: ((rz_commute_rule2 q) :: ((rz_commute_rule3 q) :: []))

(** val rz_cancel_rule :
    int -> int -> pI4_ucom_l -> pI4_Unitary gate_app list option **)

let rz_cancel_rule q k l =
  match next_single_qubit_gate l q with
  | Some p0 ->
    let (p1, l2) = p0 in
    let (l1, p2) = p1 in
    (match p2 with
     | UPI4_PI4 k' ->
       let k'' = Z.add k k' in
       if Z.eqb k'' ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))
       then Some (app l1 l2)
       else if Z.ltb k'' ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))
            then Some ((App1 ((UPI4_PI4 k''), q)) :: (app l1 l2))
            else Some ((App1 ((UPI4_PI4
                   (Z.sub k'' ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))),
                   q)) :: (app l1 l2))
     | _ -> None)
  | None -> None

(** val h_cancel_rule :
    int -> pI4_ucom_l -> pI4_Unitary gate_app list option **)

let h_cancel_rule q l =
  match next_single_qubit_gate l q with
  | Some p0 ->
    let (p1, l2) = p0 in
    let (l1, p2) = p1 in
    (match p2 with
     | UPI4_H -> Some (app l1 l2)
     | _ -> None)
  | None -> None

(** val x_commute_rule :
    int -> pI4_ucom_l -> (pI4_Unitary gate_app list * pI4_Unitary gate_list)
    option **)

let x_commute_rule q l =
  match next_two_qubit_gate l q with
  | Some p0 ->
    let (p1, l2) = p0 in
    let (p2, q2) = p1 in
    let (p3, q1) = p2 in
    let (l1, p4) = p3 in
    (match p4 with
     | UPI4_CNOT ->
       if (=) q q2 then Some ((app l1 ((cNOT q1 q2) :: [])), l2) else None
     | _ -> None)
  | None -> None

(** val x_cancel_rule :
    int -> pI4_ucom_l -> pI4_Unitary gate_app list option **)

let x_cancel_rule q l =
  match next_single_qubit_gate l q with
  | Some p0 ->
    let (p1, l2) = p0 in
    let (l1, p2) = p1 in
    (match p2 with
     | UPI4_X -> Some (app l1 l2)
     | _ -> None)
  | None -> None

(** val cNOT_commute_rule1 :
    int -> pI4_ucom_l -> (pI4_ucom_l * pI4_ucom_l) option **)

let cNOT_commute_rule1 q1 l =
  match next_single_qubit_gate l q1 with
  | Some p0 ->
    let (p1, l2) = p0 in
    let (l1, u) = p1 in
    (match u with
     | UPI4_PI4 _ -> Some (((App1 (u, q1)) :: []), (app l1 l2))
     | _ -> None)
  | None -> None

(** val cNOT_commute_rule2 :
    int -> int -> pI4_ucom_l -> (pI4_Unitary gate_app list * pI4_Unitary
    gate_list) option **)

let cNOT_commute_rule2 q1 q2 l =
  match next_two_qubit_gate l q2 with
  | Some p0 ->
    let (p1, l2) = p0 in
    let (p2, q2') = p1 in
    let (p3, q1') = p2 in
    let (l1, p4) = p3 in
    (match p4 with
     | UPI4_CNOT ->
       if (=) q2 q2'
       then if does_not_reference l1 q1
            then Some ((app l1 ((cNOT q1' q2) :: [])), l2)
            else None
       else None
     | _ -> None)
  | None -> None

(** val cNOT_commute_rule3 :
    int -> int -> pI4_ucom_l -> (pI4_Unitary gate_app list * pI4_Unitary
    gate_list) option **)

let cNOT_commute_rule3 q1 q2 l =
  match next_two_qubit_gate l q1 with
  | Some p0 ->
    let (p1, l2) = p0 in
    let (p2, q2') = p1 in
    let (p3, q1') = p2 in
    let (l1, p4) = p3 in
    (match p4 with
     | UPI4_CNOT ->
       if (=) q1 q1'
       then if does_not_reference l1 q2
            then Some ((app l1 ((cNOT q1 q2') :: [])), l2)
            else None
       else None
     | _ -> None)
  | None -> None

(** val cNOT_commute_rule4 :
    int -> int -> pI4_ucom_l -> (pI4_Unitary gate_app list * pI4_Unitary
    gate_app list) option **)

let cNOT_commute_rule4 q1 q2 l =
  match next_single_qubit_gate l q2 with
  | Some p0 ->
    let (p1, l2) = p0 in
    let (l1, p2) = p1 in
    (match p2 with
     | UPI4_H ->
       (match next_two_qubit_gate l2 q2 with
        | Some p3 ->
          let (p4, l4) = p3 in
          let (p5, q2') = p4 in
          let (p6, q1') = p5 in
          let (l3, p7) = p6 in
          (match p7 with
           | UPI4_CNOT ->
             if (&&) ((&&) ((=) q2 q1') (negb ((=) q1 q2')))
                  (does_not_reference (app l1 l3) q1)
             then (match next_single_qubit_gate l4 q2 with
                   | Some p8 ->
                     let (p9, l6) = p8 in
                     let (l5, p10) = p9 in
                     (match p10 with
                      | UPI4_H ->
                        Some
                          ((app l1
                             (app ((h q2) :: [])
                               (app l3
                                 (app ((cNOT q2 q2') :: []) ((h q2) :: []))))),
                          (app l5 l6))
                      | _ -> None)
                   | None -> None)
             else None
           | _ -> None)
        | None -> None)
     | _ -> None)
  | None -> None

(** val cNOT_commute_rule5 :
    int -> int -> pI4_ucom_l -> (pI4_Unitary gate_app list * pI4_Unitary
    gate_app list) option **)

let cNOT_commute_rule5 q1 q2 l =
  match next_single_qubit_gate l q2 with
  | Some p0 ->
    let (p1, l2) = p0 in
    let (l1, p2) = p1 in
    (match p2 with
     | UPI4_PI4 k ->
       (match next_two_qubit_gate l2 q2 with
        | Some p3 ->
          let (p4, l4) = p3 in
          let (p5, q2') = p4 in
          let (p6, q1') = p5 in
          let (l3, p7) = p6 in
          (match p7 with
           | UPI4_CNOT ->
             if (&&) ((&&) ((=) q1 q1') ((=) q2 q2'))
                  (does_not_reference (app l1 l3) q1)
             then (match next_single_qubit_gate l4 q2 with
                   | Some p8 ->
                     let (p9, l6) = p8 in
                     let (l5, p10) = p9 in
                     (match p10 with
                      | UPI4_PI4 k' ->
                        Some
                          ((app l1
                             (app ((App1 ((UPI4_PI4 k'), q2)) :: [])
                               (app l3
                                 (app ((cNOT q1' q2') :: []) ((App1
                                   ((UPI4_PI4 k), q2)) :: []))))),
                          (app l5 l6))
                      | _ -> None)
                   | None -> None)
             else None
           | _ -> None)
        | None -> None)
     | _ -> None)
  | None -> None

(** val cNOT_commute_rules :
    int -> int -> (pI4_ucom_l -> (pI4_ucom_l * pI4_ucom_l) option) list **)

let cNOT_commute_rules q1 q2 =
  (cNOT_commute_rule1 q1) :: ((cNOT_commute_rule2 q1 q2) :: ((cNOT_commute_rule3
                                                               q1 q2) :: (
    (cNOT_commute_rule4 q1 q2) :: ((cNOT_commute_rule5 q1 q2) :: []))))

(** val cNOT_cancel_rule :
    int -> int -> pI4_ucom_l -> pI4_Unitary gate_app list option **)

let cNOT_cancel_rule q1 q2 l =
  match next_two_qubit_gate l q1 with
  | Some p0 ->
    let (p1, l2) = p0 in
    let (p2, q2') = p1 in
    let (p3, q1') = p2 in
    let (l1, p4) = p3 in
    (match p4 with
     | UPI4_CNOT ->
       if (&&) ((&&) ((=) q1 q1') ((=) q2 q2')) (does_not_reference l1 q2)
       then Some (app l1 l2)
       else None
     | _ -> None)
  | None -> None

(** val propagate_PI4 :
    int -> pI4_ucom_l -> int -> int -> pI4_Unitary gate_list option **)

let propagate_PI4 k l q n =
  propagate l (rz_commute_rules q) ((rz_cancel_rule q k) :: []) n

(** val propagate_H : pI4_ucom_l -> int -> pI4_Unitary gate_list option **)

let propagate_H l q =
  propagate l [] ((h_cancel_rule q) :: []) (Pervasives.succ 0)

(** val propagate_X :
    pI4_ucom_l -> int -> int -> pI4_Unitary gate_list option **)

let propagate_X l q n =
  propagate l ((x_commute_rule q) :: []) ((x_cancel_rule q) :: []) n

(** val propagate_CNOT :
    pI4_ucom_l -> int -> int -> int -> pI4_Unitary gate_list option **)

let propagate_CNOT l q1 q2 n =
  propagate l (cNOT_commute_rules q1 q2) ((cNOT_cancel_rule q1 q2) :: []) n

(** val cancel_single_qubit_gates' : pI4_ucom_l -> int -> pI4_ucom_l **)

let rec cancel_single_qubit_gates' l n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> l)
    (fun n' ->
    match l with
    | [] -> []
    | u :: t1 ->
      (match u with
       | App1 (p0, q) ->
         (match p0 with
          | UPI4_H ->
            (match propagate_H t1 q with
             | Some l' -> cancel_single_qubit_gates' l' n'
             | None -> (h q) :: (cancel_single_qubit_gates' t1 n'))
          | UPI4_X ->
            (match propagate_X t1 q (length t1) with
             | Some l' -> cancel_single_qubit_gates' l' n'
             | None -> (x q) :: (cancel_single_qubit_gates' t1 n'))
          | UPI4_PI4 k ->
            (match propagate_PI4 k t1 q (length t1) with
             | Some l' -> cancel_single_qubit_gates' l' n'
             | None ->
               (App1 ((UPI4_PI4 k), q)) :: (cancel_single_qubit_gates' t1 n'))
          | UPI4_CNOT -> u :: (cancel_single_qubit_gates' t1 n'))
       | _ -> u :: (cancel_single_qubit_gates' t1 n')))
    n

(** val cancel_single_qubit_gates : pI4_ucom_l -> pI4_ucom_l **)

let cancel_single_qubit_gates l =
  cancel_single_qubit_gates' l (length l)

(** val cancel_two_qubit_gates' : pI4_ucom_l -> int -> pI4_ucom_l **)

let rec cancel_two_qubit_gates' l n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> l)
    (fun n' ->
    match l with
    | [] -> []
    | u :: t1 ->
      (match u with
       | App2 (p0, q1, q2) ->
         (match p0 with
          | UPI4_CNOT ->
            (match propagate_CNOT t1 q1 q2 (length t1) with
             | Some l' -> cancel_two_qubit_gates' l' n'
             | None -> (cNOT q1 q2) :: (cancel_two_qubit_gates' t1 n'))
          | _ -> u :: (cancel_two_qubit_gates' t1 n'))
       | _ -> u :: (cancel_two_qubit_gates' t1 n')))
    n

(** val cancel_two_qubit_gates : pI4_ucom_l -> pI4_ucom_l **)

let cancel_two_qubit_gates l =
  cancel_two_qubit_gates' l (length l)

(** val apply_H_equivalence1 :
    int -> pI4_ucom_l -> pI4_Unitary gate_list option **)

let apply_H_equivalence1 q l =
  replace_single_qubit_pattern l q (UPI4_H :: (uPI4_P :: (UPI4_H :: [])))
    (uPI4_PDAG :: (UPI4_H :: (uPI4_PDAG :: []))) match_gate

(** val apply_H_equivalence2 :
    int -> pI4_ucom_l -> pI4_Unitary gate_list option **)

let apply_H_equivalence2 q l =
  replace_single_qubit_pattern l q (UPI4_H :: (uPI4_PDAG :: (UPI4_H :: [])))
    (uPI4_P :: (UPI4_H :: (uPI4_P :: []))) match_gate

(** val apply_H_equivalence3 :
    int -> pI4_ucom_l -> pI4_Unitary gate_app list option **)

let apply_H_equivalence3 q l =
  match next_single_qubit_gate l q with
  | Some p0 ->
    let (p1, l2) = p0 in
    let (l1, p2) = p1 in
    (match p2 with
     | UPI4_H ->
       let l0 = app l1 l2 in
       (match next_two_qubit_gate l0 q with
        | Some p3 ->
          let (p4, l3) = p3 in
          let (p5, n) = p4 in
          let (p6, m) = p5 in
          let (l4, p7) = p6 in
          (match p7 with
           | UPI4_CNOT ->
             if (=) q m
             then (match last_single_qubit_gate l4 n with
                   | Some p8 ->
                     let (p9, l1_2) = p8 in
                     let (l1_1, p10) = p9 in
                     (match p10 with
                      | UPI4_H ->
                        let l5 = app l1_1 l1_2 in
                        (match next_single_qubit_gate l3 q with
                         | Some p11 ->
                           let (p12, l2_2) = p11 in
                           let (l2_1, p13) = p12 in
                           (match p13 with
                            | UPI4_H ->
                              let l6 = app l2_1 l2_2 in
                              (match next_single_qubit_gate l6 n with
                               | Some p14 ->
                                 let (p15, l2_3) = p14 in
                                 let (l2_4, p16) = p15 in
                                 (match p16 with
                                  | UPI4_H ->
                                    let l7 = app l2_4 l2_3 in
                                    Some (app l5 (app ((cNOT n q) :: []) l7))
                                  | _ -> None)
                               | None -> None)
                            | _ -> None)
                         | None -> None)
                      | _ -> None)
                   | None -> None)
             else (match last_single_qubit_gate l4 m with
                   | Some p8 ->
                     let (p9, l1_2) = p8 in
                     let (l1_1, p10) = p9 in
                     (match p10 with
                      | UPI4_H ->
                        let l5 = app l1_1 l1_2 in
                        (match next_single_qubit_gate l3 q with
                         | Some p11 ->
                           let (p12, l2_2) = p11 in
                           let (l2_1, p13) = p12 in
                           (match p13 with
                            | UPI4_H ->
                              let l6 = app l2_1 l2_2 in
                              (match next_single_qubit_gate l6 m with
                               | Some p14 ->
                                 let (p15, l2_3) = p14 in
                                 let (l2_4, p16) = p15 in
                                 (match p16 with
                                  | UPI4_H ->
                                    let l7 = app l2_4 l2_3 in
                                    Some (app l5 (app ((cNOT q m) :: []) l7))
                                  | _ -> None)
                               | None -> None)
                            | _ -> None)
                         | None -> None)
                      | _ -> None)
                   | None -> None)
           | _ -> None)
        | None -> None)
     | _ -> None)
  | None -> None

(** val apply_H_equivalence4 :
    int -> pI4_ucom_l -> pI4_Unitary gate_app list option **)

let apply_H_equivalence4 q l =
  match remove_single_qubit_pattern l q (UPI4_H :: (uPI4_P :: [])) match_gate with
  | Some l1 ->
    (match next_two_qubit_gate l1 q with
     | Some p0 ->
       let (p1, l3) = p0 in
       let (p2, q2) = p1 in
       let (p3, q1) = p2 in
       let (l2, p4) = p3 in
       (match p4 with
        | UPI4_CNOT ->
          if (=) q q2
          then (match remove_single_qubit_pattern l3 q
                        (uPI4_PDAG :: (UPI4_H :: [])) match_gate with
                | Some l4 ->
                  Some
                    (app l2
                      (app ((pDAG q2) :: ((cNOT q1 q2) :: ((p q2) :: []))) l4))
                | None -> None)
          else None
        | _ -> None)
     | None -> None)
  | None -> None

(** val apply_H_equivalence5 :
    int -> pI4_ucom_l -> pI4_Unitary gate_app list option **)

let apply_H_equivalence5 q l =
  match remove_single_qubit_pattern l q (UPI4_H :: (uPI4_PDAG :: []))
          match_gate with
  | Some l1 ->
    (match next_two_qubit_gate l1 q with
     | Some p0 ->
       let (p1, l3) = p0 in
       let (p2, q2) = p1 in
       let (p3, q1) = p2 in
       let (l2, p4) = p3 in
       (match p4 with
        | UPI4_CNOT ->
          if (=) q q2
          then (match remove_single_qubit_pattern l3 q
                        (uPI4_P :: (UPI4_H :: [])) match_gate with
                | Some l4 ->
                  Some
                    (app l2
                      (app ((p q2) :: ((cNOT q1 q2) :: ((pDAG q2) :: []))) l4))
                | None -> None)
          else None
        | _ -> None)
     | None -> None)
  | None -> None

(** val apply_H_equivalence : pI4_ucom_l -> int -> pI4_ucom_l option **)

let apply_H_equivalence l q =
  try_rewrites l
    ((apply_H_equivalence1 q) :: ((apply_H_equivalence2 q) :: ((apply_H_equivalence3
                                                                 q) :: (
    (apply_H_equivalence4 q) :: ((apply_H_equivalence5 q) :: [])))))

(** val apply_H_equivalences : pI4_ucom_l -> int -> pI4_ucom_l **)

let rec apply_H_equivalences l n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> l)
    (fun n' ->
    match l with
    | [] -> []
    | g :: t1 ->
      (match g with
       | App1 (p0, q) ->
         (match p0 with
          | UPI4_H ->
            (match apply_H_equivalence l q with
             | Some l' -> apply_H_equivalences l' n'
             | None -> (h q) :: (apply_H_equivalences t1 n'))
          | _ -> g :: (apply_H_equivalences t1 n'))
       | _ -> g :: (apply_H_equivalences t1 n')))
    n

(** val hadamard_reduction : pI4_ucom_l -> pI4_ucom_l **)

let hadamard_reduction l =
  apply_H_equivalences l
    (mul (Pervasives.succ (Pervasives.succ 0)) (length l))

module Raw =
 functor (X:Coq_OrderedType) ->
 struct
  module MX = Coq_OrderedTypeFacts(X)

  module PX = KeyOrderedType(X)

  type key = X.t

  type 'elt t = (X.t * 'elt) list

  (** val empty : 'a1 t **)

  let empty =
    []

  (** val is_empty : 'a1 t -> bool **)

  let is_empty = function
  | [] -> true
  | _ :: _ -> false

  (** val mem : key -> 'a1 t -> bool **)

  let rec mem k = function
  | [] -> false
  | p0 :: l ->
    let (k', _) = p0 in
    (match X.compare k k' with
     | LT -> false
     | EQ -> true
     | GT -> mem k l)

  type 'elt coq_R_mem =
  | R_mem_0 of 'elt t
  | R_mem_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_mem_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_mem_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_mem

  (** val coq_R_mem_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t ->
      bool -> 'a1 coq_R_mem -> 'a2 **)

  let rec coq_R_mem_rect k f f0 f1 f2 _ _ = function
  | R_mem_0 s -> f s __
  | R_mem_1 (s, k', _x, l) -> f0 s k' _x l __ __ __
  | R_mem_2 (s, k', _x, l) -> f1 s k' _x l __ __ __
  | R_mem_3 (s, k', _x, l, _res, r0) ->
    f2 s k' _x l __ __ __ _res r0 (coq_R_mem_rect k f f0 f1 f2 l _res r0)

  (** val coq_R_mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t ->
      bool -> 'a1 coq_R_mem -> 'a2 **)

  let rec coq_R_mem_rec k f f0 f1 f2 _ _ = function
  | R_mem_0 s -> f s __
  | R_mem_1 (s, k', _x, l) -> f0 s k' _x l __ __ __
  | R_mem_2 (s, k', _x, l) -> f1 s k' _x l __ __ __
  | R_mem_3 (s, k', _x, l, _res, r0) ->
    f2 s k' _x l __ __ __ _res r0 (coq_R_mem_rec k f f0 f1 f2 l _res r0)

  (** val mem_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec mem_rect k f2 f1 f0 f s =
    let f3 = f2 s in
    let f4 = f1 s in
    let f5 = f0 s in
    let f6 = f s in
    (match s with
     | [] -> f3 __
     | p0 :: l ->
       let (t1, e) = p0 in
       let f7 = f6 t1 e l __ in
       let f8 = fun _ _ -> let hrec = mem_rect k f2 f1 f0 f l in f7 __ __ hrec
       in
       let f9 = f5 t1 e l __ in
       let f10 = f4 t1 e l __ in
       (match X.compare k t1 with
        | LT -> f10 __ __
        | EQ -> f9 __ __
        | GT -> f8 __ __))

  (** val mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let mem_rec =
    mem_rect

  (** val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem **)

  let coq_R_mem_correct k s _res =
    Obj.magic mem_rect k (fun y _ _ _ -> R_mem_0 y)
      (fun y y0 y1 y2 _ _ _ _ _ -> R_mem_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ _ _ -> R_mem_2 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_mem_3 (y, y0, y1, y2, (mem k y2),
      (y6 (mem k y2) __))) s _res __

  (** val find : key -> 'a1 t -> 'a1 option **)

  let rec find k = function
  | [] -> None
  | p0 :: s' ->
    let (k', x0) = p0 in
    (match X.compare k k' with
     | LT -> None
     | EQ -> Some x0
     | GT -> find k s')

  type 'elt coq_R_find =
  | R_find_0 of 'elt t
  | R_find_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_find_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_find_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt option
     * 'elt coq_R_find

  (** val coq_R_find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1
      t -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

  let rec coq_R_find_rect k f f0 f1 f2 _ _ = function
  | R_find_0 s -> f s __
  | R_find_1 (s, k', x0, s') -> f0 s k' x0 s' __ __ __
  | R_find_2 (s, k', x0, s') -> f1 s k' x0 s' __ __ __
  | R_find_3 (s, k', x0, s', _res, r0) ->
    f2 s k' x0 s' __ __ __ _res r0 (coq_R_find_rect k f f0 f1 f2 s' _res r0)

  (** val coq_R_find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1
      t -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

  let rec coq_R_find_rec k f f0 f1 f2 _ _ = function
  | R_find_0 s -> f s __
  | R_find_1 (s, k', x0, s') -> f0 s k' x0 s' __ __ __
  | R_find_2 (s, k', x0, s') -> f1 s k' x0 s' __ __ __
  | R_find_3 (s, k', x0, s', _res, r0) ->
    f2 s k' x0 s' __ __ __ _res r0 (coq_R_find_rec k f f0 f1 f2 s' _res r0)

  (** val find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec find_rect k f2 f1 f0 f s =
    let f3 = f2 s in
    let f4 = f1 s in
    let f5 = f0 s in
    let f6 = f s in
    (match s with
     | [] -> f3 __
     | p0 :: l ->
       let (t1, e) = p0 in
       let f7 = f6 t1 e l __ in
       let f8 = fun _ _ ->
         let hrec = find_rect k f2 f1 f0 f l in f7 __ __ hrec
       in
       let f9 = f5 t1 e l __ in
       let f10 = f4 t1 e l __ in
       (match X.compare k t1 with
        | LT -> f10 __ __
        | EQ -> f9 __ __
        | GT -> f8 __ __))

  (** val find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let find_rec =
    find_rect

  (** val coq_R_find_correct :
      key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find **)

  let coq_R_find_correct k s _res =
    Obj.magic find_rect k (fun y _ _ _ -> R_find_0 y)
      (fun y y0 y1 y2 _ _ _ _ _ -> R_find_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ _ _ -> R_find_2 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_find_3 (y, y0, y1, y2, (find k y2),
      (y6 (find k y2) __))) s _res __

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let rec add k x0 s = match s with
  | [] -> (k, x0) :: []
  | p0 :: l ->
    let (k', y) = p0 in
    (match X.compare k k' with
     | LT -> (k, x0) :: s
     | EQ -> (k, x0) :: l
     | GT -> (k', y) :: (add k x0 l))

  type 'elt coq_R_add =
  | R_add_0 of 'elt t
  | R_add_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_add_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_add_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
     * 'elt coq_R_add

  (** val coq_R_add_rect :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 ->
      'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2 **)

  let rec coq_R_add_rect k x0 f f0 f1 f2 _ _ = function
  | R_add_0 s -> f s __
  | R_add_1 (s, k', y, l) -> f0 s k' y l __ __ __
  | R_add_2 (s, k', y, l) -> f1 s k' y l __ __ __
  | R_add_3 (s, k', y, l, _res, r0) ->
    f2 s k' y l __ __ __ _res r0 (coq_R_add_rect k x0 f f0 f1 f2 l _res r0)

  (** val coq_R_add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 ->
      'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2 **)

  let rec coq_R_add_rec k x0 f f0 f1 f2 _ _ = function
  | R_add_0 s -> f s __
  | R_add_1 (s, k', y, l) -> f0 s k' y l __ __ __
  | R_add_2 (s, k', y, l) -> f1 s k' y l __ __ __
  | R_add_3 (s, k', y, l, _res, r0) ->
    f2 s k' y l __ __ __ _res r0 (coq_R_add_rec k x0 f f0 f1 f2 l _res r0)

  (** val add_rect :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec add_rect k x0 f2 f1 f0 f s =
    let f3 = f2 s in
    let f4 = f1 s in
    let f5 = f0 s in
    let f6 = f s in
    (match s with
     | [] -> f3 __
     | p0 :: l ->
       let (t1, e) = p0 in
       let f7 = f6 t1 e l __ in
       let f8 = fun _ _ ->
         let hrec = add_rect k x0 f2 f1 f0 f l in f7 __ __ hrec
       in
       let f9 = f5 t1 e l __ in
       let f10 = f4 t1 e l __ in
       (match X.compare k t1 with
        | LT -> f10 __ __
        | EQ -> f9 __ __
        | GT -> f8 __ __))

  (** val add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let add_rec =
    add_rect

  (** val coq_R_add_correct :
      key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add **)

  let coq_R_add_correct k x0 s _res =
    add_rect k x0 (fun y _ _ _ -> R_add_0 y) (fun y y0 y1 y2 _ _ _ _ _ ->
      R_add_1 (y, y0, y1, y2)) (fun y y0 y1 y2 _ _ _ _ _ -> R_add_2 (y, y0,
      y1, y2)) (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_add_3 (y, y0, y1, y2,
      (add k x0 y2), (y6 (add k x0 y2) __))) s _res __

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let rec remove k s = match s with
  | [] -> []
  | p0 :: l ->
    let (k', x0) = p0 in
    (match X.compare k k' with
     | LT -> s
     | EQ -> l
     | GT -> (k', x0) :: (remove k l))

  type 'elt coq_R_remove =
  | R_remove_0 of 'elt t
  | R_remove_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_remove_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_remove_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
     * 'elt coq_R_remove

  (** val coq_R_remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t
      -> 'a1 t -> 'a1 coq_R_remove -> 'a2 **)

  let rec coq_R_remove_rect k f f0 f1 f2 _ _ = function
  | R_remove_0 s -> f s __
  | R_remove_1 (s, k', x0, l) -> f0 s k' x0 l __ __ __
  | R_remove_2 (s, k', x0, l) -> f1 s k' x0 l __ __ __
  | R_remove_3 (s, k', x0, l, _res, r0) ->
    f2 s k' x0 l __ __ __ _res r0 (coq_R_remove_rect k f f0 f1 f2 l _res r0)

  (** val coq_R_remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t
      -> 'a1 t -> 'a1 coq_R_remove -> 'a2 **)

  let rec coq_R_remove_rec k f f0 f1 f2 _ _ = function
  | R_remove_0 s -> f s __
  | R_remove_1 (s, k', x0, l) -> f0 s k' x0 l __ __ __
  | R_remove_2 (s, k', x0, l) -> f1 s k' x0 l __ __ __
  | R_remove_3 (s, k', x0, l, _res, r0) ->
    f2 s k' x0 l __ __ __ _res r0 (coq_R_remove_rec k f f0 f1 f2 l _res r0)

  (** val remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec remove_rect k f2 f1 f0 f s =
    let f3 = f2 s in
    let f4 = f1 s in
    let f5 = f0 s in
    let f6 = f s in
    (match s with
     | [] -> f3 __
     | p0 :: l ->
       let (t1, e) = p0 in
       let f7 = f6 t1 e l __ in
       let f8 = fun _ _ ->
         let hrec = remove_rect k f2 f1 f0 f l in f7 __ __ hrec
       in
       let f9 = f5 t1 e l __ in
       let f10 = f4 t1 e l __ in
       (match X.compare k t1 with
        | LT -> f10 __ __
        | EQ -> f9 __ __
        | GT -> f8 __ __))

  (** val remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let remove_rec =
    remove_rect

  (** val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove **)

  let coq_R_remove_correct k s _res =
    Obj.magic remove_rect k (fun y _ _ _ -> R_remove_0 y)
      (fun y y0 y1 y2 _ _ _ _ _ -> R_remove_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ _ _ -> R_remove_2 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_remove_3 (y, y0, y1, y2,
      (remove k y2), (y6 (remove k y2) __))) s _res __

  (** val elements : 'a1 t -> 'a1 t **)

  let elements m =
    m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let rec fold f m acc =
    match m with
    | [] -> acc
    | p0 :: m' -> let (k, e) = p0 in fold f m' (f k e acc)

  type ('elt, 'a) coq_R_fold =
  | R_fold_0 of 'elt t * 'a
  | R_fold_1 of 'elt t * 'a * X.t * 'elt * (X.t * 'elt) list * 'a
     * ('elt, 'a) coq_R_fold

  (** val coq_R_fold_rect :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 **)

  let rec coq_R_fold_rect f f0 f1 _ _ _ = function
  | R_fold_0 (m, acc) -> f0 m acc __
  | R_fold_1 (m, acc, k, e, m', _res, r0) ->
    f1 m acc k e m' __ _res r0
      (coq_R_fold_rect f f0 f1 m' (f k e acc) _res r0)

  (** val coq_R_fold_rec :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 **)

  let rec coq_R_fold_rec f f0 f1 _ _ _ = function
  | R_fold_0 (m, acc) -> f0 m acc __
  | R_fold_1 (m, acc, k, e, m', _res, r0) ->
    f1 m acc k e m' __ _res r0 (coq_R_fold_rec f f0 f1 m' (f k e acc) _res r0)

  (** val fold_rect :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t ->
      'a2 -> 'a3 **)

  let rec fold_rect f1 f0 f m acc =
    let f2 = f0 m acc in
    let f3 = f m acc in
    (match m with
     | [] -> f2 __
     | p0 :: l ->
       let (t1, e) = p0 in
       let f4 = f3 t1 e l __ in
       let hrec = fold_rect f1 f0 f l (f1 t1 e acc) in f4 hrec)

  (** val fold_rec :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t ->
      'a2 -> 'a3 **)

  let fold_rec =
    fold_rect

  (** val coq_R_fold_correct :
      (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
      coq_R_fold **)

  let coq_R_fold_correct f m acc _res =
    fold_rect f (fun y y0 _ _ _ -> R_fold_0 (y, y0))
      (fun y y0 y1 y2 y3 _ y5 _ _ -> R_fold_1 (y, y0, y1, y2, y3,
      (fold f y3 (f y1 y2 y0)), (y5 (fold f y3 (f y1 y2 y0)) __))) m acc _res
      __

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let rec equal cmp m m' =
    match m with
    | [] -> (match m' with
             | [] -> true
             | _ :: _ -> false)
    | p0 :: l ->
      let (x0, e) = p0 in
      (match m' with
       | [] -> false
       | p1 :: l' ->
         let (x', e') = p1 in
         (match X.compare x0 x' with
          | EQ -> (&&) (cmp e e') (equal cmp l l')
          | _ -> false))

  type 'elt coq_R_equal =
  | R_equal_0 of 'elt t * 'elt t
  | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * X.t
     * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_equal
  | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * X.t
     * 'elt * (X.t * 'elt) list * X.t compare0
  | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

  (** val coq_R_equal_rect :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
      'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t
      -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare0 -> __ -> __ -> 'a2) ->
      ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
      'a1 t -> bool -> 'a1 coq_R_equal -> 'a2 **)

  let rec coq_R_equal_rect cmp f f0 f1 f2 _ _ _ = function
  | R_equal_0 (m, m') -> f m m' __ __
  | R_equal_1 (m, m', x0, e, l, x', e', l', _res, r0) ->
    f0 m m' x0 e l __ x' e' l' __ __ __ _res r0
      (coq_R_equal_rect cmp f f0 f1 f2 l l' _res r0)
  | R_equal_2 (m, m', x0, e, l, x', e', l', _x) ->
    f1 m m' x0 e l __ x' e' l' __ _x __ __
  | R_equal_3 (m, m', _x, _x0) -> f2 m m' _x __ _x0 __ __

  (** val coq_R_equal_rec :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
      'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t
      -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare0 -> __ -> __ -> 'a2) ->
      ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
      'a1 t -> bool -> 'a1 coq_R_equal -> 'a2 **)

  let rec coq_R_equal_rec cmp f f0 f1 f2 _ _ _ = function
  | R_equal_0 (m, m') -> f m m' __ __
  | R_equal_1 (m, m', x0, e, l, x', e', l', _res, r0) ->
    f0 m m' x0 e l __ x' e' l' __ __ __ _res r0
      (coq_R_equal_rec cmp f f0 f1 f2 l l' _res r0)
  | R_equal_2 (m, m', x0, e, l, x', e', l', _x) ->
    f1 m m' x0 e l __ x' e' l' __ _x __ __
  | R_equal_3 (m, m', _x, _x0) -> f2 m m' _x __ _x0 __ __

  (** val equal_rect :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
      X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t
      -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2 **)

  let rec equal_rect cmp f2 f1 f0 f m m' =
    let f3 = f2 m m' in
    let f4 = f1 m m' in
    let f5 = f0 m m' in
    let f6 = f m m' in
    let f7 = f6 m __ in
    let f8 = f7 m' __ in
    (match m with
     | [] -> let f9 = f3 __ in (match m' with
                                | [] -> f9 __
                                | _ :: _ -> f8 __)
     | p0 :: l ->
       let (t1, e) = p0 in
       let f9 = f5 t1 e l __ in
       let f10 = f4 t1 e l __ in
       (match m' with
        | [] -> f8 __
        | p1 :: l0 ->
          let (t2, e0) = p1 in
          let f11 = f9 t2 e0 l0 __ in
          let f12 = let _x = X.compare t1 t2 in f11 _x __ in
          let f13 = f10 t2 e0 l0 __ in
          let f14 = fun _ _ ->
            let hrec = equal_rect cmp f2 f1 f0 f l l0 in f13 __ __ hrec
          in
          (match X.compare t1 t2 with
           | EQ -> f14 __ __
           | _ -> f12 __)))

  (** val equal_rec :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
      X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t
      -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2 **)

  let equal_rec =
    equal_rect

  (** val coq_R_equal_correct :
      ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal **)

  let coq_R_equal_correct cmp m m' _res =
    equal_rect cmp (fun y y0 _ _ _ _ -> R_equal_0 (y, y0))
      (fun y y0 y1 y2 y3 _ y5 y6 y7 _ _ _ y11 _ _ -> R_equal_1 (y, y0, y1,
      y2, y3, y5, y6, y7, (equal cmp y3 y7), (y11 (equal cmp y3 y7) __)))
      (fun y y0 y1 y2 y3 _ y5 y6 y7 _ y9 _ _ _ _ -> R_equal_2 (y, y0, y1, y2,
      y3, y5, y6, y7, y9)) (fun y y0 y1 _ y3 _ _ _ _ -> R_equal_3 (y, y0, y1,
      y3)) m m' _res __

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec map f = function
  | [] -> []
  | p0 :: m' -> let (k, e) = p0 in (k, (f e)) :: (map f m')

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec mapi f = function
  | [] -> []
  | p0 :: m' -> let (k, e) = p0 in (k, (f k e)) :: (mapi f m')

  (** val option_cons :
      key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list **)

  let option_cons k o l =
    match o with
    | Some e -> (k, e) :: l
    | None -> l

  (** val map2_l :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t **)

  let rec map2_l f = function
  | [] -> []
  | p0 :: l -> let (k, e) = p0 in option_cons k (f (Some e) None) (map2_l f l)

  (** val map2_r :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t **)

  let rec map2_r f = function
  | [] -> []
  | p0 :: l' ->
    let (k, e') = p0 in option_cons k (f None (Some e')) (map2_r f l')

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let rec map2 f m = match m with
  | [] -> map2_r f
  | p0 :: l ->
    let (k, e) = p0 in
    let rec map2_aux m' = match m' with
    | [] -> map2_l f m
    | p1 :: l' ->
      let (k', e') = p1 in
      (match X.compare k k' with
       | LT -> option_cons k (f (Some e) None) (map2 f l m')
       | EQ -> option_cons k (f (Some e) (Some e')) (map2 f l l')
       | GT -> option_cons k' (f None (Some e')) (map2_aux l'))
    in map2_aux

  (** val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t **)

  let rec combine m = match m with
  | [] -> map (fun e' -> (None, (Some e')))
  | p0 :: l ->
    let (k, e) = p0 in
    let rec combine_aux m' = match m' with
    | [] -> map (fun e0 -> ((Some e0), None)) m
    | p1 :: l' ->
      let (k', e') = p1 in
      (match X.compare k k' with
       | LT -> (k, ((Some e), None)) :: (combine l m')
       | EQ -> (k, ((Some e), (Some e'))) :: (combine l l')
       | GT -> (k', (None, (Some e'))) :: (combine_aux l'))
    in combine_aux

  (** val fold_right_pair :
      ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3 **)

  let fold_right_pair f l i =
    fold_right (fun p0 -> f (fst p0) (snd p0)) i l

  (** val map2_alt :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
      (key * 'a3) list **)

  let map2_alt f m m' =
    let m0 = combine m m' in
    let m1 = map (fun p0 -> f (fst p0) (snd p0)) m0 in
    fold_right_pair option_cons m1 []

  (** val at_least_one :
      'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option **)

  let at_least_one o o' =
    match o with
    | Some _ -> Some (o, o')
    | None -> (match o' with
               | Some _ -> Some (o, o')
               | None -> None)

  (** val at_least_one_then_f :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
      'a3 option **)

  let at_least_one_then_f f o o' =
    match o with
    | Some _ -> f o o'
    | None -> (match o' with
               | Some _ -> f o o'
               | None -> None)
 end

module Coq_Raw =
 functor (I:Int) ->
 functor (X:Coq_OrderedType) ->
 struct
  type key = X.t

  type 'elt tree =
  | Leaf
  | Node of 'elt tree * key * 'elt * 'elt tree * I.t

  (** val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)

  let rec tree_rect f f0 = function
  | Leaf -> f
  | Node (t2, k, y, t3, t4) ->
    f0 t2 (tree_rect f f0 t2) k y t3 (tree_rect f f0 t3) t4

  (** val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)

  let rec tree_rec f f0 = function
  | Leaf -> f
  | Node (t2, k, y, t3, t4) ->
    f0 t2 (tree_rec f f0 t2) k y t3 (tree_rec f f0 t3) t4

  (** val height : 'a1 tree -> I.t **)

  let height = function
  | Leaf -> I._0
  | Node (_, _, _, _, h0) -> h0

  (** val cardinal : 'a1 tree -> int **)

  let rec cardinal = function
  | Leaf -> 0
  | Node (l, _, _, r, _) -> Pervasives.succ (add (cardinal l) (cardinal r))

  (** val empty : 'a1 tree **)

  let empty =
    Leaf

  (** val is_empty : 'a1 tree -> bool **)

  let is_empty = function
  | Leaf -> true
  | Node (_, _, _, _, _) -> false

  (** val mem : X.t -> 'a1 tree -> bool **)

  let rec mem x0 = function
  | Leaf -> false
  | Node (l, y, _, r, _) ->
    (match X.compare x0 y with
     | LT -> mem x0 l
     | EQ -> true
     | GT -> mem x0 r)

  (** val find : X.t -> 'a1 tree -> 'a1 option **)

  let rec find x0 = function
  | Leaf -> None
  | Node (l, y, d, r, _) ->
    (match X.compare x0 y with
     | LT -> find x0 l
     | EQ -> Some d
     | GT -> find x0 r)

  (** val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let create l x0 e r =
    Node (l, x0, e, r, (I.add (I.max (height l) (height r)) I._1))

  (** val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let assert_false =
    create

  (** val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let bal l x0 d r =
    let hl = height l in
    let hr = height r in
    if I.gt_le_dec hl (I.add hr I._2)
    then (match l with
          | Leaf -> assert_false l x0 d r
          | Node (ll, lx, ld, lr, _) ->
            if I.ge_lt_dec (height ll) (height lr)
            then create ll lx ld (create lr x0 d r)
            else (match lr with
                  | Leaf -> assert_false l x0 d r
                  | Node (lrl, lrx, lrd, lrr, _) ->
                    create (create ll lx ld lrl) lrx lrd (create lrr x0 d r)))
    else if I.gt_le_dec hr (I.add hl I._2)
         then (match r with
               | Leaf -> assert_false l x0 d r
               | Node (rl, rx, rd, rr, _) ->
                 if I.ge_lt_dec (height rr) (height rl)
                 then create (create l x0 d rl) rx rd rr
                 else (match rl with
                       | Leaf -> assert_false l x0 d r
                       | Node (rll, rlx, rld, rlr, _) ->
                         create (create l x0 d rll) rlx rld
                           (create rlr rx rd rr)))
         else create l x0 d r

  (** val add : key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec add x0 d = function
  | Leaf -> Node (Leaf, x0, d, Leaf, I._1)
  | Node (l, y, d', r, h0) ->
    (match X.compare x0 y with
     | LT -> bal (add x0 d l) y d' r
     | EQ -> Node (l, y, d, r, h0)
     | GT -> bal l y d' (add x0 d r))

  (** val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1) **)

  let rec remove_min l x0 d r =
    match l with
    | Leaf -> (r, (x0, d))
    | Node (ll, lx, ld, lr, _) ->
      let (l', m) = remove_min ll lx ld lr in ((bal l' x0 d r), m)

  (** val merge : 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let merge s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (_, _, _, _, _) ->
      (match s2 with
       | Leaf -> s1
       | Node (l2, x2, d2, r2, _) ->
         let (s2', p0) = remove_min l2 x2 d2 r2 in
         let (x0, d) = p0 in bal s1 x0 d s2')

  (** val remove : X.t -> 'a1 tree -> 'a1 tree **)

  let rec remove x0 = function
  | Leaf -> Leaf
  | Node (l, y, d, r, _) ->
    (match X.compare x0 y with
     | LT -> bal (remove x0 l) y d r
     | EQ -> merge l r
     | GT -> bal l y d (remove x0 r))

  (** val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec join l = match l with
  | Leaf -> add
  | Node (ll, lx, ld, lr, lh) ->
    (fun x0 d ->
      let rec join_aux r = match r with
      | Leaf -> add x0 d l
      | Node (rl, rx, rd, rr, rh) ->
        if I.gt_le_dec lh (I.add rh I._2)
        then bal ll lx ld (join lr x0 d r)
        else if I.gt_le_dec rh (I.add lh I._2)
             then bal (join_aux rl) rx rd rr
             else create l x0 d r
      in join_aux)

  type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                       t_right : 'elt tree }

  (** val t_left : 'a1 triple -> 'a1 tree **)

  let t_left t1 =
    t1.t_left

  (** val t_opt : 'a1 triple -> 'a1 option **)

  let t_opt t1 =
    t1.t_opt

  (** val t_right : 'a1 triple -> 'a1 tree **)

  let t_right t1 =
    t1.t_right

  (** val split : X.t -> 'a1 tree -> 'a1 triple **)

  let rec split x0 = function
  | Leaf -> { t_left = Leaf; t_opt = None; t_right = Leaf }
  | Node (l, y, d, r, _) ->
    (match X.compare x0 y with
     | LT ->
       let { t_left = ll; t_opt = o; t_right = rl } = split x0 l in
       { t_left = ll; t_opt = o; t_right = (join rl y d r) }
     | EQ -> { t_left = l; t_opt = (Some d); t_right = r }
     | GT ->
       let { t_left = rl; t_opt = o; t_right = rr } = split x0 r in
       { t_left = (join l y d rl); t_opt = o; t_right = rr })

  (** val concat : 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let concat m1 m2 =
    match m1 with
    | Leaf -> m2
    | Node (_, _, _, _, _) ->
      (match m2 with
       | Leaf -> m1
       | Node (l2, x2, d2, r2, _) ->
         let (m2', xd) = remove_min l2 x2 d2 r2 in
         join m1 (fst xd) (snd xd) m2')

  (** val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list **)

  let rec elements_aux acc = function
  | Leaf -> acc
  | Node (l, x0, d, r, _) -> elements_aux ((x0, d) :: (elements_aux acc r)) l

  (** val elements : 'a1 tree -> (key * 'a1) list **)

  let elements m =
    elements_aux [] m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)

  let rec fold f m a =
    match m with
    | Leaf -> a
    | Node (l, x0, d, r, _) -> fold f r (f x0 d (fold f l a))

  type 'elt enumeration =
  | End
  | More of key * 'elt * 'elt tree * 'elt enumeration

  (** val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)

  let rec enumeration_rect f f0 = function
  | End -> f
  | More (k, e0, t1, e1) -> f0 k e0 t1 e1 (enumeration_rect f f0 e1)

  (** val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)

  let rec enumeration_rec f f0 = function
  | End -> f
  | More (k, e0, t1, e1) -> f0 k e0 t1 e1 (enumeration_rec f f0 e1)

  (** val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration **)

  let rec cons m e =
    match m with
    | Leaf -> e
    | Node (l, x0, d, r, _) -> cons l (More (x0, d, r, e))

  (** val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)

  let equal_more cmp x1 d1 cont = function
  | End -> false
  | More (x2, d2, r2, e3) ->
    (match X.compare x1 x2 with
     | EQ -> if cmp d1 d2 then cont (cons r2 e3) else false
     | _ -> false)

  (** val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)

  let rec equal_cont cmp m1 cont e2 =
    match m1 with
    | Leaf -> cont e2
    | Node (l1, x1, d1, r1, _) ->
      equal_cont cmp l1 (equal_more cmp x1 d1 (equal_cont cmp r1 cont)) e2

  (** val equal_end : 'a1 enumeration -> bool **)

  let equal_end = function
  | End -> true
  | More (_, _, _, _) -> false

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool **)

  let equal cmp m1 m2 =
    equal_cont cmp m1 equal_end (cons m2 End)

  (** val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)

  let rec map f = function
  | Leaf -> Leaf
  | Node (l, x0, d, r, h0) -> Node ((map f l), x0, (f d), (map f r), h0)

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)

  let rec mapi f = function
  | Leaf -> Leaf
  | Node (l, x0, d, r, h0) -> Node ((mapi f l), x0, (f x0 d), (mapi f r), h0)

  (** val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree **)

  let rec map_option f = function
  | Leaf -> Leaf
  | Node (l, x0, d, r, _) ->
    (match f x0 d with
     | Some d' -> join (map_option f l) x0 d' (map_option f r)
     | None -> concat (map_option f l) (map_option f r))

  (** val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree **)

  let rec map2_opt f mapl mapr m1 m2 =
    match m1 with
    | Leaf -> mapr m2
    | Node (l1, x1, d1, r1, _) ->
      (match m2 with
       | Leaf -> mapl m1
       | Node (_, _, _, _, _) ->
         let { t_left = l2'; t_opt = o2; t_right = r2' } = split x1 m2 in
         (match f x1 d1 o2 with
          | Some e ->
            join (map2_opt f mapl mapr l1 l2') x1 e
              (map2_opt f mapl mapr r1 r2')
          | None ->
            concat (map2_opt f mapl mapr l1 l2') (map2_opt f mapl mapr r1 r2')))

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree **)

  let map2 f =
    map2_opt (fun _ d o -> f (Some d) o)
      (map_option (fun _ d -> f (Some d) None))
      (map_option (fun _ d' -> f None (Some d')))

  module Proofs =
   struct
    module MX = Coq_OrderedTypeFacts(X)

    module PX = KeyOrderedType(X)

    module L = Raw(X)

    type 'elt coq_R_mem =
    | R_mem_0 of 'elt tree
    | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t * 
       bool * 'elt coq_R_mem
    | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t * 
       bool * 'elt coq_R_mem

    (** val coq_R_mem_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2 **)

    let rec coq_R_mem_rect x0 f f0 f1 f2 _ _ = function
    | R_mem_0 m -> f m __
    | R_mem_1 (m, l, y, _x, r0, _x0, _res, r1) ->
      f0 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rect x0 f f0 f1 f2 l _res r1)
    | R_mem_2 (m, l, y, _x, r0, _x0) -> f1 m l y _x r0 _x0 __ __ __
    | R_mem_3 (m, l, y, _x, r0, _x0, _res, r1) ->
      f2 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rect x0 f f0 f1 f2 r0 _res r1)

    (** val coq_R_mem_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2 **)

    let rec coq_R_mem_rec x0 f f0 f1 f2 _ _ = function
    | R_mem_0 m -> f m __
    | R_mem_1 (m, l, y, _x, r0, _x0, _res, r1) ->
      f0 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rec x0 f f0 f1 f2 l _res r1)
    | R_mem_2 (m, l, y, _x, r0, _x0) -> f1 m l y _x r0 _x0 __ __ __
    | R_mem_3 (m, l, y, _x, r0, _x0, _res, r1) ->
      f2 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rec x0 f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_find =
    | R_find_0 of 'elt tree
    | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find
    | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find

    (** val coq_R_find_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

    let rec coq_R_find_rect x0 f f0 f1 f2 _ _ = function
    | R_find_0 m -> f m __
    | R_find_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rect x0 f f0 f1 f2 l _res r1)
    | R_find_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_find_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rect x0 f f0 f1 f2 r0 _res r1)

    (** val coq_R_find_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

    let rec coq_R_find_rec x0 f f0 f1 f2 _ _ = function
    | R_find_0 m -> f m __
    | R_find_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rec x0 f f0 f1 f2 l _res r1)
    | R_find_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_find_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rec x0 f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_bal =
    | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
       I.t
    | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
       I.t
    | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

    (** val coq_R_bal_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
        'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2 **)

    let coq_R_bal_rect f f0 f1 f2 f3 f4 f5 f6 f7 _ _ _ _ _ = function
    | R_bal_0 (x0, x1, x2, x3) -> f x0 x1 x2 x3 __ __ __
    | R_bal_1 (x0, x1, x2, x3, x4, x5, x6, x7, x8) ->
      f0 x0 x1 x2 x3 __ __ x4 x5 x6 x7 x8 __ __ __
    | R_bal_2 (x0, x1, x2, x3, x4, x5, x6, x7, x8) ->
      f1 x0 x1 x2 x3 __ __ x4 x5 x6 x7 x8 __ __ __ __
    | R_bal_3 (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13) ->
      f2 x0 x1 x2 x3 __ __ x4 x5 x6 x7 x8 __ __ __ x9 x10 x11 x12 x13 __
    | R_bal_4 (x0, x1, x2, x3) -> f3 x0 x1 x2 x3 __ __ __ __ __
    | R_bal_5 (x0, x1, x2, x3, x4, x5, x6, x7, x8) ->
      f4 x0 x1 x2 x3 __ __ __ __ x4 x5 x6 x7 x8 __ __ __
    | R_bal_6 (x0, x1, x2, x3, x4, x5, x6, x7, x8) ->
      f5 x0 x1 x2 x3 __ __ __ __ x4 x5 x6 x7 x8 __ __ __ __
    | R_bal_7 (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13) ->
      f6 x0 x1 x2 x3 __ __ __ __ x4 x5 x6 x7 x8 __ __ __ x9 x10 x11 x12 x13 __
    | R_bal_8 (x0, x1, x2, x3) -> f7 x0 x1 x2 x3 __ __ __ __

    (** val coq_R_bal_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
        'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2 **)

    let coq_R_bal_rec f f0 f1 f2 f3 f4 f5 f6 f7 _ _ _ _ _ = function
    | R_bal_0 (x0, x1, x2, x3) -> f x0 x1 x2 x3 __ __ __
    | R_bal_1 (x0, x1, x2, x3, x4, x5, x6, x7, x8) ->
      f0 x0 x1 x2 x3 __ __ x4 x5 x6 x7 x8 __ __ __
    | R_bal_2 (x0, x1, x2, x3, x4, x5, x6, x7, x8) ->
      f1 x0 x1 x2 x3 __ __ x4 x5 x6 x7 x8 __ __ __ __
    | R_bal_3 (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13) ->
      f2 x0 x1 x2 x3 __ __ x4 x5 x6 x7 x8 __ __ __ x9 x10 x11 x12 x13 __
    | R_bal_4 (x0, x1, x2, x3) -> f3 x0 x1 x2 x3 __ __ __ __ __
    | R_bal_5 (x0, x1, x2, x3, x4, x5, x6, x7, x8) ->
      f4 x0 x1 x2 x3 __ __ __ __ x4 x5 x6 x7 x8 __ __ __
    | R_bal_6 (x0, x1, x2, x3, x4, x5, x6, x7, x8) ->
      f5 x0 x1 x2 x3 __ __ __ __ x4 x5 x6 x7 x8 __ __ __ __
    | R_bal_7 (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13) ->
      f6 x0 x1 x2 x3 __ __ __ __ x4 x5 x6 x7 x8 __ __ __ x9 x10 x11 x12 x13 __
    | R_bal_8 (x0, x1, x2, x3) -> f7 x0 x1 x2 x3 __ __ __ __

    type 'elt coq_R_add =
    | R_add_0 of 'elt tree
    | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add
    | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add

    (** val coq_R_add_rect :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2 **)

    let rec coq_R_add_rect x0 d f f0 f1 f2 _ _ = function
    | R_add_0 m -> f m __
    | R_add_1 (m, l, y, d', r0, h0, _res, r1) ->
      f0 m l y d' r0 h0 __ __ __ _res r1
        (coq_R_add_rect x0 d f f0 f1 f2 l _res r1)
    | R_add_2 (m, l, y, d', r0, h0) -> f1 m l y d' r0 h0 __ __ __
    | R_add_3 (m, l, y, d', r0, h0, _res, r1) ->
      f2 m l y d' r0 h0 __ __ __ _res r1
        (coq_R_add_rect x0 d f f0 f1 f2 r0 _res r1)

    (** val coq_R_add_rec :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2 **)

    let rec coq_R_add_rec x0 d f f0 f1 f2 _ _ = function
    | R_add_0 m -> f m __
    | R_add_1 (m, l, y, d', r0, h0, _res, r1) ->
      f0 m l y d' r0 h0 __ __ __ _res r1
        (coq_R_add_rec x0 d f f0 f1 f2 l _res r1)
    | R_add_2 (m, l, y, d', r0, h0) -> f1 m l y d' r0 h0 __ __ __
    | R_add_3 (m, l, y, d', r0, h0, _res, r1) ->
      f2 m l y d' r0 h0 __ __ __ _res r1
        (coq_R_add_rec x0 d f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_remove_min =
    | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
    | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
       key * 'elt * 'elt tree * I.t * ('elt tree * (key * 'elt))
       * 'elt coq_R_remove_min * 'elt tree * (key * 'elt)

    (** val coq_R_remove_min_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1
        tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 **)

    let rec coq_R_remove_min_rect f f0 _ _ _ _ _ = function
    | R_remove_min_0 (l, x0, d, r0) -> f l x0 d r0 __
    | R_remove_min_1 (l, x0, d, r0, ll, lx, ld, lr, _x, _res, r1, l', m) ->
      f0 l x0 d r0 ll lx ld lr _x __ _res r1
        (coq_R_remove_min_rect f f0 ll lx ld lr _res r1) l' m __

    (** val coq_R_remove_min_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1
        tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 **)

    let rec coq_R_remove_min_rec f f0 _ _ _ _ _ = function
    | R_remove_min_0 (l, x0, d, r0) -> f l x0 d r0 __
    | R_remove_min_1 (l, x0, d, r0, ll, lx, ld, lr, _x, _res, r1, l', m) ->
      f0 l x0 d r0 ll lx ld lr _x __ _res r1
        (coq_R_remove_min_rec f f0 ll lx ld lr _res r1) l' m __

    type 'elt coq_R_merge =
    | R_merge_0 of 'elt tree * 'elt tree
    | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t
    | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t * 'elt tree * key * 'elt * 'elt tree * I.t * 'elt tree
       * (key * 'elt) * key * 'elt

    (** val coq_R_merge_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_merge -> 'a2 **)

    let coq_R_merge_rect f f0 f1 _ _ _ = function
    | R_merge_0 (x0, x1) -> f x0 x1 __
    | R_merge_1 (x0, x1, x2, x3, x4, x5, x6) -> f0 x0 x1 x2 x3 x4 x5 x6 __ __
    | R_merge_2 (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13,
                 x14, x15) ->
      f1 x0 x1 x2 x3 x4 x5 x6 __ x7 x8 x9 x10 x11 __ x12 x13 __ x14 x15 __

    (** val coq_R_merge_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_merge -> 'a2 **)

    let coq_R_merge_rec f f0 f1 _ _ _ = function
    | R_merge_0 (x0, x1) -> f x0 x1 __
    | R_merge_1 (x0, x1, x2, x3, x4, x5, x6) -> f0 x0 x1 x2 x3 x4 x5 x6 __ __
    | R_merge_2 (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13,
                 x14, x15) ->
      f1 x0 x1 x2 x3 x4 x5 x6 __ x7 x8 x9 x10 x11 __ x12 x13 __ x14 x15 __

    type 'elt coq_R_remove =
    | R_remove_0 of 'elt tree
    | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt tree * 'elt coq_R_remove
    | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt tree * 'elt coq_R_remove

    (** val coq_R_remove_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 **)

    let rec coq_R_remove_rect x0 f f0 f1 f2 _ _ = function
    | R_remove_0 m -> f m __
    | R_remove_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rect x0 f f0 f1 f2 l _res r1)
    | R_remove_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_remove_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rect x0 f f0 f1 f2 r0 _res r1)

    (** val coq_R_remove_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 **)

    let rec coq_R_remove_rec x0 f f0 f1 f2 _ _ = function
    | R_remove_0 m -> f m __
    | R_remove_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rec x0 f f0 f1 f2 l _res r1)
    | R_remove_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_remove_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rec x0 f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_concat =
    | R_concat_0 of 'elt tree * 'elt tree
    | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.t
    | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * (key * 'elt)

    (** val coq_R_concat_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_concat -> 'a2 **)

    let coq_R_concat_rect f f0 f1 _ _ _ = function
    | R_concat_0 (x0, x1) -> f x0 x1 __
    | R_concat_1 (x0, x1, x2, x3, x4, x5, x6) -> f0 x0 x1 x2 x3 x4 x5 x6 __ __
    | R_concat_2 (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13) ->
      f1 x0 x1 x2 x3 x4 x5 x6 __ x7 x8 x9 x10 x11 __ x12 x13 __

    (** val coq_R_concat_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_concat -> 'a2 **)

    let coq_R_concat_rec f f0 f1 _ _ _ = function
    | R_concat_0 (x0, x1) -> f x0 x1 __
    | R_concat_1 (x0, x1, x2, x3, x4, x5, x6) -> f0 x0 x1 x2 x3 x4 x5 x6 __ __
    | R_concat_2 (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13) ->
      f1 x0 x1 x2 x3 x4 x5 x6 __ x7 x8 x9 x10 x11 __ x12 x13 __

    type 'elt coq_R_split =
    | R_split_0 of 'elt tree
    | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree
    | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree

    (** val coq_R_split_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
        'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 **)

    let rec coq_R_split_rect x0 f f0 f1 f2 _ _ = function
    | R_split_0 m -> f m __
    | R_split_1 (m, l, y, d, r0, _x, _res, r1, ll, o, rl) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rect x0 f f0 f1 f2 l _res r1) ll o rl __
    | R_split_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_split_3 (m, l, y, d, r0, _x, _res, r1, rl, o, rr) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rect x0 f f0 f1 f2 r0 _res r1) rl o rr __

    (** val coq_R_split_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
        'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 **)

    let rec coq_R_split_rec x0 f f0 f1 f2 _ _ = function
    | R_split_0 m -> f m __
    | R_split_1 (m, l, y, d, r0, _x, _res, r1, ll, o, rl) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rec x0 f f0 f1 f2 l _res r1) ll o rl __
    | R_split_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_split_3 (m, l, y, d, r0, _x, _res, r1, rl, o, rr) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rec x0 f f0 f1 f2 r0 _res r1) rl o rr __

    type ('elt, 'x) coq_R_map_option =
    | R_map_option_0 of 'elt tree
    | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
       * ('elt, 'x) coq_R_map_option
    | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
       * ('elt, 'x) coq_R_map_option

    (** val coq_R_map_option_rect :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 **)

    let rec coq_R_map_option_rect f f0 f1 f2 _ _ = function
    | R_map_option_0 m -> f0 m __
    | R_map_option_1 (m, l, x0, d, r0, _x, d', _res0, r1, _res, r2) ->
      f1 m l x0 d r0 _x __ d' __ _res0 r1
        (coq_R_map_option_rect f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rect f f0 f1 f2 r0 _res r2)
    | R_map_option_2 (m, l, x0, d, r0, _x, _res0, r1, _res, r2) ->
      f2 m l x0 d r0 _x __ __ _res0 r1
        (coq_R_map_option_rect f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rect f f0 f1 f2 r0 _res r2)

    (** val coq_R_map_option_rec :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 **)

    let rec coq_R_map_option_rec f f0 f1 f2 _ _ = function
    | R_map_option_0 m -> f0 m __
    | R_map_option_1 (m, l, x0, d, r0, _x, d', _res0, r1, _res, r2) ->
      f1 m l x0 d r0 _x __ d' __ _res0 r1
        (coq_R_map_option_rec f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rec f f0 f1 f2 r0 _res r2)
    | R_map_option_2 (m, l, x0, d, r0, _x, _res0, r1, _res, r2) ->
      f2 m l x0 d r0 _x __ __ _res0 r1
        (coq_R_map_option_rec f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rec f f0 f1 f2 r0 _res r2)

    type ('elt, 'x0, 'x) coq_R_map2_opt =
    | R_map2_opt_0 of 'elt tree * 'x0 tree
    | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t
    | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 'x0 tree
       * 'x0 option * 'x0 tree * 'x * 'x tree
       * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
       * ('elt, 'x0, 'x) coq_R_map2_opt
    | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 'x0 tree
       * 'x0 option * 'x0 tree * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt
       * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt

    (** val coq_R_map2_opt_rect :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t ->
        __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key ->
        'a2 -> 'a2 tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
        __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree ->
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 **)

    let rec coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 _ _ _ = function
    | R_map2_opt_0 (m1, m2) -> f0 m1 m2 __
    | R_map2_opt_1 (m1, m2, l1, x1, d1, r1, _x) ->
      f1 m1 m2 l1 x1 d1 r1 _x __ __
    | R_map2_opt_2 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', e, _res0, r0, _res, r2) ->
      f2 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ e __
        _res0 r0
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0) _res r2
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)
    | R_map2_opt_3 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', _res0, r0, _res, r2) ->
      f3 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ __
        _res0 r0
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0) _res r2
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)

    (** val coq_R_map2_opt_rec :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t ->
        __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key ->
        'a2 -> 'a2 tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
        __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree ->
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 **)

    let rec coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 _ _ _ = function
    | R_map2_opt_0 (m1, m2) -> f0 m1 m2 __
    | R_map2_opt_1 (m1, m2, l1, x1, d1, r1, _x) ->
      f1 m1 m2 l1 x1 d1 r1 _x __ __
    | R_map2_opt_2 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', e, _res0, r0, _res, r2) ->
      f2 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ e __
        _res0 r0 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0)
        _res r2 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)
    | R_map2_opt_3 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', _res0, r0, _res, r2) ->
      f3 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ __
        _res0 r0 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0)
        _res r2 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)

    (** val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)

    let fold' f s =
      L.fold f (elements s)

    (** val flatten_e : 'a1 enumeration -> (key * 'a1) list **)

    let rec flatten_e = function
    | End -> []
    | More (x0, e0, t1, r) -> (x0, e0) :: (app (elements t1) (flatten_e r))
   end
 end

module Coq0_IntMake =
 functor (I:Int) ->
 functor (X:Coq_OrderedType) ->
 struct
  module E = X

  module Raw = Coq_Raw(I)(X)

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  (** val this : 'a1 bst -> 'a1 Raw.tree **)

  let this b =
    b

  type 'elt t = 'elt bst

  type key = E.t

  (** val empty : 'a1 t **)

  let empty =
    Raw.empty

  (** val is_empty : 'a1 t -> bool **)

  let is_empty m =
    Raw.is_empty (this m)

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let add x0 e m =
    Raw.add x0 e (this m)

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let remove x0 m =
    Raw.remove x0 (this m)

  (** val mem : key -> 'a1 t -> bool **)

  let mem x0 m =
    Raw.mem x0 (this m)

  (** val find : key -> 'a1 t -> 'a1 option **)

  let find x0 m =
    Raw.find x0 (this m)

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map f m =
    Raw.map f (this m)

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let mapi f m =
    Raw.mapi f (this m)

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let map2 f m m' =
    Raw.map2 f (this m) (this m')

  (** val elements : 'a1 t -> (key * 'a1) list **)

  let elements m =
    Raw.elements (this m)

  (** val cardinal : 'a1 t -> int **)

  let cardinal m =
    Raw.cardinal (this m)

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let fold f m i =
    Raw.fold f (this m) i

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let equal cmp m m' =
    Raw.equal cmp (this m) (this m')
 end

module Coq_Make =
 functor (X:Coq_OrderedType) ->
 Coq0_IntMake(Z_as_Int)(X)

module FMap = Coq_Make(Nat_as_OT)

(** val get_subcircuit' :
    pI4_ucom_l -> FSet.t -> FSet.t -> int -> (pI4_Unitary gate_app
    list * pI4_Unitary gate_app list) * pI4_ucom_l **)

let rec get_subcircuit' l qs blst n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> (([], []), l))
    (fun n' ->
    if FSet.equal qs blst
    then (([], []), l)
    else (match next_gate l qs with
          | Some p0 ->
            let (p1, l2) = p0 in
            let (l1, g) = p1 in
            (match g with
             | App1 (u, q) ->
               (match u with
                | UPI4_H ->
                  let (p2, l2') = get_subcircuit' l2 qs (FSet.add q blst) n'
                  in
                  let (l1', s) = p2 in
                  (((app l1 l1'), (app ((h q) :: []) s)), l2')
                | _ ->
                  let (p2, l2') = get_subcircuit' l2 qs blst n' in
                  let (l1', s) = p2 in
                  (((app l1 l1'), (app ((App1 (u, q)) :: []) s)), l2'))
             | App2 (p2, q1, q2) ->
               (match p2 with
                | UPI4_CNOT ->
                  let qs' = FSet.add q1 (FSet.add q2 qs) in
                  let blst' =
                    if FSet.mem q1 blst then FSet.add q2 blst else blst
                  in
                  let (p3, l2') = get_subcircuit' l2 qs' blst' n' in
                  let (l1', s) = p3 in
                  (((app l1 l1'), (app ((cNOT q1 q2) :: []) s)), l2')
                | _ -> (([], []), l))
             | App3 (_, _, _, _) -> (([], []), l))
          | None -> (([], []), l)))
    n

(** val get_subcircuit :
    pI4_ucom_l -> FSet.elt -> (pI4_Unitary gate_app list * pI4_Unitary
    gate_app list) * pI4_ucom_l **)

let get_subcircuit l q =
  get_subcircuit' l (FSet.add q FSet.empty) FSet.empty (length l)

(** val pI4 : int -> int -> pI4_Unitary gate_app **)

let pI4 k q =
  App1 ((UPI4_PI4 k), q)

(** val xor : FSet.t -> FSet.t -> FSet.t **)

let xor s1 s2 =
  FSet.diff (FSet.union s1 s2) (FSet.inter s1 s2)

(** val combine_gates : int -> int -> int -> pI4_Unitary gate_app list **)

let combine_gates k k' q =
  let k'' = Z.add k k' in
  if Z.eqb k'' ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))
  then []
  else if Z.ltb k'' ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))
       then (pI4 k'' q) :: []
       else (pI4 (Z.sub k'' ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))) q) :: []

(** val get_set : FSet.t FMap.t -> FMap.key -> FSet.t **)

let get_set smap q =
  match FMap.find q smap with
  | Some s -> s
  | None -> FSet.add q FSet.empty

(** val find_merge :
    pI4_ucom_l -> FSet.t -> FSet.elt -> FSet.t FMap.t ->
    (((pI4_ucom_l * int) * int) * pI4_ucom_l) option **)

let rec find_merge l blst q smap =
  match l with
  | [] -> None
  | g :: t1 ->
    (match g with
     | App1 (p0, q') ->
       (match p0 with
        | UPI4_H ->
          (match find_merge t1 (FSet.add q' blst) q smap with
           | Some p1 ->
             let (p2, l2) = p1 in
             let (p3, q'') = p2 in
             let (l1, k) = p3 in Some (((((h q') :: l1), k), q''), l2)
           | None -> None)
        | UPI4_PI4 k ->
          let s = get_set smap q' in
          let sorig = FSet.add q FSet.empty in
          if (&&) (negb (FSet.mem q' blst)) (FSet.equal s sorig)
          then Some ((([], k), q'), t1)
          else (match find_merge t1 blst q smap with
                | Some p1 ->
                  let (p2, l2) = p1 in
                  let (p3, q'') = p2 in
                  let (l1, k') = p3 in
                  Some (((((pI4 k q') :: l1), k'), q''), l2)
                | None -> None)
        | _ -> None)
     | App2 (p0, q1, q2) ->
       (match p0 with
        | UPI4_CNOT ->
          if (||) (FSet.mem q1 blst) (FSet.mem q2 blst)
          then let blst' = if FSet.mem q1 blst then FSet.add q2 blst else blst
               in
               (match find_merge t1 blst' q smap with
                | Some p1 ->
                  let (p2, l2) = p1 in
                  let (p3, q') = p2 in
                  let (l1, k) = p3 in
                  Some (((((cNOT q1 q2) :: l1), k), q'), l2)
                | None -> None)
          else let s1 = get_set smap q1 in
               let s2 = get_set smap q2 in
               let smap' = FMap.add q2 (xor s1 s2) smap in
               (match find_merge t1 blst q smap' with
                | Some p1 ->
                  let (p2, l2) = p1 in
                  let (p3, q') = p2 in
                  let (l1, k) = p3 in
                  Some (((((cNOT q1 q2) :: l1), k), q'), l2)
                | None -> None)
        | _ -> None)
     | App3 (_, _, _, _) -> None)

(** val merge_at_beginning :
    pI4_ucom_l -> int -> FSet.elt -> pI4_Unitary gate_app list option **)

let merge_at_beginning l k q =
  match find_merge l FSet.empty q FMap.empty with
  | Some p0 ->
    let (p1, l2) = p0 in
    let (p2, _) = p1 in
    let (l1, k') = p2 in Some (app (combine_gates k k' q) (app l1 l2))
  | None -> None

(** val merge_at_end :
    pI4_ucom_l -> int -> FSet.elt -> pI4_Unitary gate_app list option **)

let merge_at_end l k q =
  match find_merge l FSet.empty q FMap.empty with
  | Some p0 ->
    let (p1, l2) = p0 in
    let (p2, q') = p1 in
    let (l1, k') = p2 in Some (app l1 (app (combine_gates k k' q') l2))
  | None -> None

(** val merge_rotations_at_beginning : pI4_ucom_l -> int -> pI4_ucom_l **)

let rec merge_rotations_at_beginning l n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> l)
    (fun n' ->
    match l with
    | [] -> []
    | g :: t1 ->
      (match g with
       | App1 (p0, q) ->
         (match p0 with
          | UPI4_PI4 k ->
            let (p1, l2) = get_subcircuit t1 q in
            let (l1, s) = p1 in
            (match merge_at_beginning s k q with
             | Some s' -> merge_rotations_at_beginning (app l1 (app s' l2)) n'
             | None ->
               (App1 ((UPI4_PI4 k),
                 q)) :: (merge_rotations_at_beginning t1 n'))
          | _ -> g :: (merge_rotations_at_beginning t1 n'))
       | _ -> g :: (merge_rotations_at_beginning t1 n')))
    n

(** val merge_rotations_at_end : pI4_ucom_l -> int -> pI4_ucom_l **)

let rec merge_rotations_at_end l n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> l)
    (fun n' ->
    match l with
    | [] -> []
    | g :: t1 ->
      (match g with
       | App1 (p0, q) ->
         (match p0 with
          | UPI4_PI4 k ->
            let (p1, l2) = get_subcircuit t1 q in
            let (l1, s) = p1 in
            (match merge_at_end s k q with
             | Some s' -> merge_rotations_at_end (app l1 (app s' l2)) n'
             | None ->
               (App1 ((UPI4_PI4 k), q)) :: (merge_rotations_at_end t1 n'))
          | _ -> g :: (merge_rotations_at_end t1 n'))
       | _ -> g :: (merge_rotations_at_end t1 n')))
    n

(** val invert_gate : pI4_Unitary gate_app -> pI4_Unitary gate_app **)

let invert_gate g = match g with
| App1 (y, q) ->
  (match y with
   | UPI4_PI4 k ->
     App1 ((UPI4_PI4
       (Z.sub ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) k)), q)
   | _ -> g)
| _ -> g

(** val invert : pI4_ucom_l -> pI4_Unitary gate_app list **)

let invert l =
  map invert_gate (rev l)

(** val merge_rotations : pI4_ucom_l -> pI4_Unitary gate_app list **)

let merge_rotations l =
  let l' = merge_rotations_at_beginning l (length l) in
  let l'' = merge_rotations_at_end (invert l') (length l') in invert l''

(** val propagate_X0 :
    pI4_ucom_l -> int -> int -> pI4_Unitary gate_app list **)

let rec propagate_X0 l q n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> (x q) :: l)
    (fun n' ->
    match l with
    | [] -> (x q) :: []
    | u :: t1 ->
      if does_not_reference_appl q u
      then u :: (propagate_X0 t1 q n')
      else (match u with
            | App1 (p0, n0) ->
              (match p0 with
               | UPI4_H -> u :: ((z q) :: t1)
               | UPI4_X -> t1
               | UPI4_PI4 k ->
                 (App1 ((UPI4_PI4
                   (Z.sub ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) k)),
                   n0)) :: (propagate_X0 t1 q n')
               | UPI4_CNOT -> (x q) :: l)
            | App2 (p0, m, n0) ->
              (match p0 with
               | UPI4_CNOT ->
                 if (=) q m
                 then u :: (propagate_X0 (propagate_X0 t1 m n') n0 n')
                 else u :: (propagate_X0 t1 q n')
               | _ -> (x q) :: l)
            | App3 (_, _, _, _) -> (x q) :: l))
    n

(** val not_propagation' : pI4_ucom_l -> int -> pI4_ucom_l **)

let rec not_propagation' l n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> l)
    (fun n' ->
    match l with
    | [] -> []
    | u :: t1 ->
      (match u with
       | App1 (p0, q) ->
         (match p0 with
          | UPI4_X -> let l' = propagate_X0 t1 q n in not_propagation' l' n'
          | _ -> u :: (not_propagation' t1 n'))
       | _ -> u :: (not_propagation' t1 n')))
    n

(** val not_propagation : pI4_ucom_l -> pI4_ucom_l **)

let not_propagation l =
  not_propagation' l (mul (Pervasives.succ (Pervasives.succ 0)) (length l))

(** val optimize : pI4_ucom_l -> pI4_ucom_l **)

let optimize l =
  cancel_single_qubit_gates
    (cancel_two_qubit_gates
      (merge_rotations
        (cancel_single_qubit_gates
          (hadamard_reduction
            (cancel_two_qubit_gates
              (cancel_single_qubit_gates
                (cancel_two_qubit_gates
                  (hadamard_reduction (not_propagation l)))))))))
