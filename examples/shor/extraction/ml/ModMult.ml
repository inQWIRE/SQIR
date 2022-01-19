open Nat
open RCIR

(** val fb_push : bool -> (Z.t -> bool) -> Z.t -> bool **)

let fb_push b f x =
  (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
    (fun _ -> b)
    (fun n -> f n)
    x

(** val allfalse : Z.t -> bool **)

let allfalse _ =
  false

(** val pos2fb : Z.t -> Z.t -> bool **)

let rec pos2fb p =
  (fun f2p1 f2p f1 p -> if Z.leq p Z.one then f1 () else if Z.is_even p then f2p (Z.div p (Z.of_int 2)) else f2p1 (Z.div p (Z.of_int 2)))
    (fun p' -> fb_push true (pos2fb p'))
    (fun p' -> fb_push false (pos2fb p'))
    (fun _ -> fb_push true allfalse)
    p

(** val coq_N2fb : Z.t -> Z.t -> bool **)

let coq_N2fb n =
  (fun f0 fp n -> if Z.equal n Z.zero then f0 () else fp n)
    (fun _ -> allfalse)
    (fun p -> pos2fb p)
    n

(** val nat2fb : Z.t -> Z.t -> bool **)

let nat2fb n =
  coq_N2fb ( n)

(** val modmult_rev_anc : Z.t -> Z.t **)

let modmult_rev_anc n =
  add (mul (Z.succ (Z.succ (Z.succ Z.zero))) n) (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    Z.zero)))))))))))

(** val coq_MAJ : Z.t -> Z.t -> Z.t -> bccom **)

let coq_MAJ a b c =
  Coq_bcseq ((Coq_bcseq ((bccnot c b), (bccnot c a))), (bcccnot a b c))

(** val coq_UMA : Z.t -> Z.t -> Z.t -> bccom **)

let coq_UMA a b c =
  Coq_bcseq ((Coq_bcseq ((bcccnot a b c), (bccnot c a))), (bccnot a b))

(** val coq_MAJseq' : Z.t -> Z.t -> Z.t -> bccom **)

let rec coq_MAJseq' i n c0 =
  (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
    (fun _ ->
    coq_MAJ c0 (add (Z.succ (Z.succ Z.zero)) n) (Z.succ (Z.succ Z.zero)))
    (fun i' -> Coq_bcseq ((coq_MAJseq' i' n c0),
    (coq_MAJ (add (Z.succ (Z.succ Z.zero)) i')
      (add (add (Z.succ (Z.succ Z.zero)) n) i)
      (add (Z.succ (Z.succ Z.zero)) i))))
    i

(** val coq_MAJseq : Z.t -> bccom **)

let coq_MAJseq n =
  coq_MAJseq' (sub n (Z.succ Z.zero)) n Z.zero

(** val coq_UMAseq' : Z.t -> Z.t -> Z.t -> bccom **)

let rec coq_UMAseq' i n c0 =
  (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
    (fun _ ->
    coq_UMA c0 (add (Z.succ (Z.succ Z.zero)) n) (Z.succ (Z.succ Z.zero)))
    (fun i' -> Coq_bcseq
    ((coq_UMA (add (Z.succ (Z.succ Z.zero)) i')
       (add (add (Z.succ (Z.succ Z.zero)) n) i)
       (add (Z.succ (Z.succ Z.zero)) i)), (coq_UMAseq' i' n c0)))
    i

(** val coq_UMAseq : Z.t -> bccom **)

let coq_UMAseq n =
  coq_UMAseq' (sub n (Z.succ Z.zero)) n Z.zero

(** val adder01 : Z.t -> bccom **)

let adder01 n =
  Coq_bcseq ((coq_MAJseq n), (coq_UMAseq n))

(** val swapper02' : Z.t -> Z.t -> bccom **)

let rec swapper02' i n =
  (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
    (fun _ -> Coq_bcskip)
    (fun i' -> Coq_bcseq ((swapper02' i' n), (Coq_bcswap
    ((add (Z.succ (Z.succ Z.zero)) i'),
    (add (add (add (Z.succ (Z.succ Z.zero)) n) n) i')))))
    i

(** val swapper02 : Z.t -> bccom **)

let swapper02 n =
  swapper02' n n

(** val negator0' : Z.t -> bccom **)

let rec negator0' i =
  (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
    (fun _ -> Coq_bcskip)
    (fun i' -> Coq_bcseq ((negator0' i'), (Coq_bcx
    (add (Z.succ (Z.succ Z.zero)) i'))))
    i

(** val negator0 : Z.t -> bccom **)

let negator0 =
  negator0'

(** val highb01 : Z.t -> bccom **)

let highb01 n =
  Coq_bcseq ((Coq_bcseq ((coq_MAJseq n),
    (bccnot (add (Z.succ Z.zero) n) (Z.succ Z.zero)))),
    (bcinv (coq_MAJseq n)))

(** val comparator01 : Z.t -> bccom **)

let comparator01 n =
  Coq_bcseq ((Coq_bcseq ((Coq_bcseq ((Coq_bcx Z.zero), (negator0 n))),
    (highb01 n))), (bcinv (Coq_bcseq ((Coq_bcx Z.zero), (negator0 n)))))

(** val subtractor01 : Z.t -> bccom **)

let subtractor01 n =
  Coq_bcseq ((Coq_bcseq ((Coq_bcseq ((Coq_bcx Z.zero), (negator0 n))),
    (adder01 n))), (bcinv (Coq_bcseq ((Coq_bcx Z.zero), (negator0 n)))))

(** val modadder21 : Z.t -> bccom **)

let modadder21 n =
  Coq_bcseq ((Coq_bcseq ((Coq_bcseq ((Coq_bcseq ((Coq_bcseq ((Coq_bcseq
    ((Coq_bcseq ((swapper02 n), (adder01 n))), (swapper02 n))),
    (comparator01 n))), (Coq_bcseq
    ((bygatectrl (Z.succ Z.zero) (subtractor01 n)), (Coq_bcx (Z.succ
    Z.zero)))))), (swapper02 n))), (bcinv (comparator01 n)))), (swapper02 n))

(** val swapper12' : Z.t -> Z.t -> bccom **)

let rec swapper12' i n =
  (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
    (fun _ -> Coq_bcskip)
    (fun i' -> Coq_bcseq ((swapper12' i' n), (Coq_bcswap
    ((add (add (Z.succ (Z.succ Z.zero)) n) i'),
    (add (add (add (Z.succ (Z.succ Z.zero)) n) n) i')))))
    i

(** val swapper12 : Z.t -> bccom **)

let swapper12 n =
  swapper12' n n

(** val doubler1' : Z.t -> Z.t -> bccom **)

let rec doubler1' i n =
  (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
    (fun _ -> Coq_bcskip)
    (fun i' -> Coq_bcseq ((Coq_bcswap ((add n i'), (add n i))),
    (doubler1' i' n)))
    i

(** val doubler1 : Z.t -> bccom **)

let doubler1 n =
  doubler1' (sub n (Z.succ Z.zero)) (add (Z.succ (Z.succ Z.zero)) n)

(** val moddoubler01 : Z.t -> bccom **)

let moddoubler01 n =
  Coq_bcseq ((Coq_bcseq ((doubler1 n), (comparator01 n))),
    (bygatectrl (Z.succ Z.zero) (subtractor01 n)))

(** val modadder12 : Z.t -> bccom **)

let modadder12 n =
  Coq_bcseq ((Coq_bcseq ((swapper12 n), (modadder21 n))), (swapper12 n))

(** val modsummer' : Z.t -> Z.t -> (Z.t -> bool) -> bccom **)

let rec modsummer' i n fC =
  (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
    (fun _ -> if fC Z.zero then modadder12 n else Coq_bcskip)
    (fun i' -> Coq_bcseq ((Coq_bcseq ((Coq_bcseq ((modsummer' i' n fC),
    (moddoubler01 n))), (Coq_bcswap ((Z.succ Z.zero),
    (add (add (add (add (Z.succ (Z.succ Z.zero)) n) n) n) i))))),
    (if fC i then modadder12 n else Coq_bcskip)))
    i

(** val modsummer : Z.t -> Z.t -> bccom **)

let modsummer n c =
  modsummer' (sub n (Z.succ Z.zero)) n (nat2fb c)

(** val modmult_half : Z.t -> Z.t -> bccom **)

let modmult_half n c =
  Coq_bcseq ((modsummer n c), (bcinv (modsummer n Z.zero)))

(** val modmult_full : Z.t -> Z.t -> Z.t -> bccom **)

let modmult_full c cinv n =
  Coq_bcseq ((Coq_bcseq ((modmult_half n c), (swapper12 n))),
    (bcinv (modmult_half n cinv)))

(** val swapperh1' : Z.t -> Z.t -> bccom **)

let rec swapperh1' j n =
  (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
    (fun _ -> Coq_bcskip)
    (fun j' -> Coq_bcseq ((swapperh1' j' n), (Coq_bcswap (j',
    (add (add (Z.succ (Z.succ Z.zero)) n) j')))))
    j

(** val swapperh1 : Z.t -> bccom **)

let swapperh1 n =
  swapperh1' n n

(** val genM0' : Z.t -> (Z.t -> bool) -> bccom **)

let rec genM0' i f =
  (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
    (fun _ -> Coq_bcskip)
    (fun i' -> Coq_bcseq ((genM0' i' f),
    (if f i' then Coq_bcx (add (Z.succ (Z.succ Z.zero)) i') else Coq_bcskip)))
    i

(** val genM0 : Z.t -> Z.t -> bccom **)

let genM0 m n =
  genM0' n (nat2fb m)

(** val modmult : Z.t -> Z.t -> Z.t -> Z.t -> bccom **)

let modmult m c cinv n =
  Coq_bcseq ((Coq_bcseq ((Coq_bcseq ((swapperh1 n), (genM0 m n))),
    (modmult_full c cinv n))),
    (bcinv (Coq_bcseq ((swapperh1 n), (genM0 m n)))))

(** val safe_swap : Z.t -> Z.t -> bccom **)

let safe_swap a b =
  if Z.equal a b then Coq_bcskip else Coq_bcswap (a, b)

(** val reverser' : Z.t -> Z.t -> bccom **)

let rec reverser' i n =
  (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
    (fun _ -> safe_swap Z.zero (sub n (Z.succ Z.zero)))
    (fun i' -> Coq_bcseq ((reverser' i' n),
    (safe_swap i (sub (sub n (Z.succ Z.zero)) i))))
    i

(** val reverser : Z.t -> bccom **)

let reverser n =
  reverser' (Z.div (sub n (Z.succ Z.zero)) (Z.succ (Z.succ Z.zero))) n

(** val modmult_rev : Z.t -> Z.t -> Z.t -> Z.t -> bccom **)

let modmult_rev m c cinv n =
  Coq_bcseq ((Coq_bcseq ((bcinv (reverser n)),
    (modmult m c cinv (Z.succ (Z.succ n))))), (reverser n))
