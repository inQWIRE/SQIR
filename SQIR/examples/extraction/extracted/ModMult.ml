open BinNat
open BinNums
open Nat
open RCIR

(** val modmult_rev_anc : int -> int **)

let modmult_rev_anc n =
  add (mul (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))) n)
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))

(** val fb_push : bool -> (int -> bool) -> int -> bool **)

let fb_push b f x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> b)
    (fun n -> f n)
    x

(** val allfalse : int -> bool **)

let allfalse _ =
  false

(** val pos2fb : positive -> int -> bool **)

let rec pos2fb = function
| Coq_xI p' -> fb_push true (pos2fb p')
| Coq_xO p' -> fb_push false (pos2fb p')
| Coq_xH -> fb_push true allfalse

(** val coq_N2fb : coq_N -> int -> bool **)

let coq_N2fb = function
| N0 -> allfalse
| Npos p -> pos2fb p

(** val nat2fb : int -> int -> bool **)

let nat2fb n =
  coq_N2fb (N.of_nat n)

(** val coq_MAJ : int -> int -> int -> bccom **)

let coq_MAJ a b c =
  Coq_bcseq ((Coq_bcseq ((bccnot c b), (bccnot c a))), (bcccnot a b c))

(** val coq_UMA : int -> int -> int -> bccom **)

let coq_UMA a b c =
  Coq_bcseq ((Coq_bcseq ((bcccnot a b c), (bccnot c a))), (bccnot a b))

(** val coq_MAJseq' : int -> int -> int -> bccom **)

let rec coq_MAJseq' i n c0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    coq_MAJ c0 (add (Pervasives.succ (Pervasives.succ 0)) n) (Pervasives.succ
      (Pervasives.succ 0)))
    (fun i' -> Coq_bcseq ((coq_MAJseq' i' n c0),
    (coq_MAJ (add (Pervasives.succ (Pervasives.succ 0)) i')
      (add (add (Pervasives.succ (Pervasives.succ 0)) n) i)
      (add (Pervasives.succ (Pervasives.succ 0)) i))))
    i

(** val coq_MAJseq : int -> bccom **)

let coq_MAJseq n =
  coq_MAJseq' (sub n (Pervasives.succ 0)) n 0

(** val coq_UMAseq' : int -> int -> int -> bccom **)

let rec coq_UMAseq' i n c0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    coq_UMA c0 (add (Pervasives.succ (Pervasives.succ 0)) n) (Pervasives.succ
      (Pervasives.succ 0)))
    (fun i' -> Coq_bcseq
    ((coq_UMA (add (Pervasives.succ (Pervasives.succ 0)) i')
       (add (add (Pervasives.succ (Pervasives.succ 0)) n) i)
       (add (Pervasives.succ (Pervasives.succ 0)) i)),
    (coq_UMAseq' i' n c0)))
    i

(** val coq_UMAseq : int -> bccom **)

let coq_UMAseq n =
  coq_UMAseq' (sub n (Pervasives.succ 0)) n 0

(** val adder01 : int -> bccom **)

let adder01 n =
  Coq_bcseq ((coq_MAJseq n), (coq_UMAseq n))

(** val swapper02' : int -> int -> bccom **)

let rec swapper02' i n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Coq_bcskip)
    (fun i' -> Coq_bcseq ((swapper02' i' n),
    (bcswap (add (Pervasives.succ (Pervasives.succ 0)) i')
      (add (add (add (Pervasives.succ (Pervasives.succ 0)) n) n) i'))))
    i

(** val swapper02 : int -> bccom **)

let swapper02 n =
  swapper02' n n

(** val negator0' : int -> bccom **)

let rec negator0' i =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Coq_bcskip)
    (fun i' -> Coq_bcseq ((negator0' i'), (Coq_bcx
    (add (Pervasives.succ (Pervasives.succ 0)) i'))))
    i

(** val negator0 : int -> bccom **)

let negator0 =
  negator0'

(** val highb01 : int -> bccom **)

let highb01 n =
  Coq_bcseq ((Coq_bcseq ((coq_MAJseq n),
    (bccnot (add (Pervasives.succ 0) n) (Pervasives.succ 0)))),
    (bcinv (coq_MAJseq n)))

(** val comparator01 : int -> bccom **)

let comparator01 n =
  Coq_bcseq ((Coq_bcseq ((Coq_bcseq ((Coq_bcx 0), (negator0 n))),
    (highb01 n))), (bcinv (Coq_bcseq ((Coq_bcx 0), (negator0 n)))))

(** val substractor01 : int -> bccom **)

let substractor01 n =
  Coq_bcseq ((Coq_bcseq ((Coq_bcseq ((Coq_bcx 0), (negator0 n))),
    (adder01 n))), (bcinv (Coq_bcseq ((Coq_bcx 0), (negator0 n)))))

(** val modadder21 : int -> bccom **)

let modadder21 n =
  Coq_bcseq ((Coq_bcseq ((Coq_bcseq ((Coq_bcseq ((Coq_bcseq ((Coq_bcseq
    ((Coq_bcseq ((swapper02 n), (adder01 n))), (swapper02 n))),
    (comparator01 n))), (Coq_bcseq ((Coq_bccont ((Pervasives.succ 0),
    (substractor01 n))), (Coq_bcx (Pervasives.succ 0)))))), (swapper02 n))),
    (bcinv (comparator01 n)))), (swapper02 n))

(** val swapper12' : int -> int -> bccom **)

let rec swapper12' i n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Coq_bcskip)
    (fun i' -> Coq_bcseq ((swapper12' i' n),
    (bcswap (add (add (Pervasives.succ (Pervasives.succ 0)) n) i')
      (add (add (add (Pervasives.succ (Pervasives.succ 0)) n) n) i'))))
    i

(** val swapper12 : int -> bccom **)

let swapper12 n =
  swapper12' n n

(** val doubler1' : int -> int -> bccom **)

let rec doubler1' i n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Coq_bcskip)
    (fun i' -> Coq_bcseq ((bcswap (add n i') (add n i)), (doubler1' i' n)))
    i

(** val doubler1 : int -> bccom **)

let doubler1 n =
  doubler1' (sub n (Pervasives.succ 0))
    (add (Pervasives.succ (Pervasives.succ 0)) n)

(** val moddoubler01 : int -> bccom **)

let moddoubler01 n =
  Coq_bcseq ((Coq_bcseq ((doubler1 n), (comparator01 n))), (Coq_bccont
    ((Pervasives.succ 0), (substractor01 n))))

(** val modadder12 : int -> bccom **)

let modadder12 n =
  Coq_bcseq ((Coq_bcseq ((swapper12 n), (modadder21 n))), (swapper12 n))

(** val modsummer' : int -> int -> (int -> bool) -> bccom **)

let rec modsummer' i n fC =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> if fC 0 then modadder12 n else Coq_bcskip)
    (fun i' -> Coq_bcseq ((Coq_bcseq ((Coq_bcseq ((modsummer' i' n fC),
    (moddoubler01 n))),
    (bcswap (Pervasives.succ 0)
      (add (add (add (add (Pervasives.succ (Pervasives.succ 0)) n) n) n) i)))),
    (if fC i then modadder12 n else Coq_bcskip)))
    i

(** val modsummer : int -> int -> bccom **)

let modsummer n c =
  modsummer' (sub n (Pervasives.succ 0)) n (nat2fb c)

(** val modmult_half : int -> int -> bccom **)

let modmult_half n c =
  Coq_bcseq ((modsummer n c), (bcinv (modsummer n 0)))

(** val modmult_full : int -> int -> int -> bccom **)

let modmult_full c cinv n =
  Coq_bcseq ((Coq_bcseq ((modmult_half n c), (swapper12 n))),
    (bcinv (modmult_half n cinv)))

(** val swapperh1' : int -> int -> bccom **)

let rec swapperh1' j n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Coq_bcskip)
    (fun j' -> Coq_bcseq ((swapperh1' j' n),
    (bcswap j' (add (add (Pervasives.succ (Pervasives.succ 0)) n) j'))))
    j

(** val swapperh1 : int -> bccom **)

let swapperh1 n =
  swapperh1' n n

(** val genM0' : int -> (int -> bool) -> bccom **)

let rec genM0' i f =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Coq_bcskip)
    (fun i' -> Coq_bcseq ((genM0' i' f),
    (if f i'
     then Coq_bcx (add (Pervasives.succ (Pervasives.succ 0)) i')
     else Coq_bcskip)))
    i

(** val genM0 : int -> int -> bccom **)

let genM0 m n =
  genM0' n (nat2fb m)

(** val modmult : int -> int -> int -> int -> bccom **)

let modmult m c cinv n =
  Coq_bcseq ((Coq_bcseq ((Coq_bcseq ((swapperh1 n), (genM0 m n))),
    (modmult_full c cinv n))),
    (bcinv (Coq_bcseq ((swapperh1 n), (genM0 m n)))))

(** val reverser' : int -> int -> bccom **)

let rec reverser' i n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> bcswap 0 (sub n (Pervasives.succ 0)))
    (fun i' -> Coq_bcseq ((reverser' i' n),
    (bcswap i (sub (sub n (Pervasives.succ 0)) i))))
    i

(** val reverser : int -> bccom **)

let reverser n =
  reverser'
    (PeanoNat.Nat.div (sub n (Pervasives.succ 0)) (Pervasives.succ
      (Pervasives.succ 0))) n

(** val modmult_rev : int -> int -> int -> int -> bccom **)

let modmult_rev m c cinv n =
  Coq_bcseq ((Coq_bcseq ((bcinv (reverser n)),
    (modmult m c cinv (Pervasives.succ (Pervasives.succ n))))), (reverser n))
