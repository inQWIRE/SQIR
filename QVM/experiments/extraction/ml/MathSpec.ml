open BinNat
open Datatypes
open Nat0
open PeanoNat

(** val allfalse : int -> bool **)

let allfalse _ =
  false

(** val fb_push : bool -> (int -> bool) -> int -> bool **)

let fb_push b f x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> b)
    (fun n -> f n)
    x

(** val pos2fb : int -> int -> bool **)

let rec pos2fb p =
  (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
    (fun p' -> fb_push true (pos2fb p'))
    (fun p' -> fb_push false (pos2fb p'))
    (fun _ -> fb_push true allfalse)
    p

(** val coq_N2fb : int -> int -> bool **)

let coq_N2fb n =
  (fun f0 fp n -> if n=0 then f0 () else fp n)
    (fun _ -> allfalse)
    (fun p -> pos2fb p)
    n

(** val nat2fb : int -> int -> bool **)

let nat2fb n =
  coq_N2fb (N.of_nat n)

(** val carry : bool -> int -> (int -> bool) -> (int -> bool) -> bool **)

let rec carry b n f g =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> b)
    (fun n' ->
    let c = carry b n' f g in
    let a = f n' in
    let b0 = g n' in xorb (xorb ((&&) a b0) ((&&) b0 c)) ((&&) a c))
    n

(** val sumfb : bool -> (int -> bool) -> (int -> bool) -> int -> bool **)

let sumfb b f g x =
  xorb (xorb (carry b x f g) (f x)) (g x)

(** val negatem : int -> (int -> bool) -> int -> bool **)

let negatem i f x =
  if Nat.ltb x i then negb (f x) else f x

(** val cut_n : (int -> bool) -> int -> int -> bool **)

let cut_n f n i =
  if Nat.ltb i n then f i else allfalse i

(** val fbrev : int -> (int -> 'a1) -> int -> 'a1 **)

let fbrev n f x =
  if Nat.ltb x n then f (sub (sub n (Pervasives.succ 0)) x) else f x

(** val times_two_spec : (int -> bool) -> int -> bool **)

let times_two_spec f i =
  if (=) i 0 then false else f (sub i (Pervasives.succ 0))
