open BinNat
open BinNums
open Nat
open Rdefinitions
open Rpow_def
open Rtrigo1
open SQIR
open UnitaryOps

let __ = let rec f _ = Obj.repr f in Obj.repr f

type var = int

type posi = var * int

(** val posi_eq : posi -> posi -> bool **)

let posi_eq r1 r2 =
  let (x1, y1) = r1 in let (x2, y2) = r2 in (&&) ((=) x1 x2) ((=) y1 y2)

type scom =
| SKIP
| X of posi
| CU of posi * scom
| RZ of int * posi
| RRZ of int * posi
| Lshift of var
| Rshift of var
| Seq of scom * scom

type face =
| Exp of scom
| QFT of var
| RQFT of var
| Reset of var
| Rev of var
| H of var
| FSeq of face * face

(** val allfalse : int -> bool **)

let allfalse _ =
  false

(** val coq_CNOT : posi -> posi -> scom **)

let coq_CNOT x0 y0 =
  CU (x0, (X y0))

(** val coq_SWAP : posi -> posi -> scom **)

let coq_SWAP x0 y0 =
  if posi_eq x0 y0
  then SKIP
  else Seq ((Seq ((coq_CNOT x0 y0), (coq_CNOT y0 x0))), (coq_CNOT x0 y0))

(** val coq_CCX : posi -> posi -> posi -> scom **)

let coq_CCX x0 y0 z0 =
  CU (x0, (coq_CNOT y0 z0))

(** val init_v : int -> var -> (int -> bool) -> scom **)

let rec init_v n x0 m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP)
    (fun m0 ->
    if m m0 then Seq ((X (x0, m0)), (init_v m0 x0 m)) else init_v m0 x0 m)
    n

(** val coq_MAJ : posi -> posi -> posi -> scom **)

let coq_MAJ a b c =
  Seq ((Seq ((coq_CNOT c b), (coq_CNOT c a))), (coq_CCX a b c))

(** val coq_UMA : posi -> posi -> posi -> scom **)

let coq_UMA a b c =
  Seq ((Seq ((coq_CCX a b c), (coq_CNOT c a))), (coq_CNOT a b))

(** val coq_MAJseq' : int -> var -> var -> posi -> scom **)

let rec coq_MAJseq' n x0 y0 c =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_MAJ c (y0, 0) (x0, 0))
    (fun m -> Seq ((coq_MAJseq' m x0 y0 c),
    (coq_MAJ (x0, m) (y0, n) (x0, n))))
    n

(** val coq_MAJseq : int -> var -> var -> posi -> scom **)

let coq_MAJseq n x0 y0 c =
  coq_MAJseq' (sub n (Pervasives.succ 0)) x0 y0 c

(** val coq_UMAseq' : int -> var -> var -> posi -> scom **)

let rec coq_UMAseq' n x0 y0 c =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_UMA c (y0, 0) (x0, 0))
    (fun m -> Seq ((coq_UMA (x0, m) (y0, n) (x0, n)),
    (coq_UMAseq' m x0 y0 c)))
    n

(** val coq_UMAseq : int -> var -> var -> posi -> scom **)

let coq_UMAseq n x0 y0 c =
  coq_UMAseq' (sub n (Pervasives.succ 0)) x0 y0 c

(** val adder01 : int -> var -> var -> posi -> scom **)

let adder01 n x0 y0 c =
  Seq ((coq_MAJseq n x0 y0 c), (coq_UMAseq n x0 y0 c))

(** val negator0 : int -> var -> scom **)

let rec negator0 i x0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP)
    (fun i' -> Seq ((negator0 i' x0), (X (x0, i'))))
    i

(** val sinv : scom -> scom **)

let rec sinv = function
| CU (n, p0) -> CU (n, (sinv p0))
| RZ (q, p1) -> RRZ (q, p1)
| RRZ (q, p1) -> RZ (q, p1)
| Lshift x0 -> Rshift x0
| Rshift x0 -> Lshift x0
| Seq (p1, p2) -> Seq ((sinv p2), (sinv p1))
| x0 -> x0

(** val finv : face -> face **)

let rec finv = function
| Exp s0 -> Exp (sinv s0)
| QFT x0 -> RQFT x0
| RQFT x0 -> QFT x0
| FSeq (p1, p2) -> FSeq ((finv p2), (finv p1))
| x0 -> x0

(** val highb01 : int -> var -> var -> posi -> posi -> scom **)

let highb01 n x0 y0 c3 c4 =
  Seq ((Seq ((coq_MAJseq n x0 y0 c3), (coq_CNOT (x0, n) c4))),
    (sinv (coq_MAJseq n x0 y0 c3)))

(** val comparator01 : int -> var -> var -> posi -> posi -> scom **)

let comparator01 n x0 y0 c3 c4 =
  Seq ((Seq ((Seq ((X c3), (negator0 n x0))), (highb01 n x0 y0 c3 c4))),
    (sinv (Seq ((X c3), (negator0 n x0)))))

(** val substractor01 : int -> var -> var -> posi -> scom **)

let substractor01 n x0 y0 c3 =
  Seq ((Seq ((Seq ((X c3), (negator0 n x0))), (adder01 n x0 y0 c3))),
    (sinv (Seq ((X c3), (negator0 n x0)))))

(** val modadder21 : int -> var -> var -> var -> posi -> posi -> scom **)

let modadder21 n x0 y0 m c3 c4 =
  Seq ((Seq ((Seq ((Seq ((adder01 n y0 x0 c3), (comparator01 n m x0 c3 c4))),
    (CU (c4, (substractor01 n m x0 c3))))), (X c4))),
    (comparator01 n y0 x0 c3 c4))

(** val doubler1 : var -> scom **)

let doubler1 y0 =
  Rshift y0

(** val moddoubler01 : int -> var -> var -> posi -> posi -> scom **)

let moddoubler01 n x0 m c3 c4 =
  Seq ((Seq ((doubler1 x0), (comparator01 n x0 m c3 c4))), (CU (c4,
    (substractor01 n x0 m c3))))

(** val fb_push : bool -> (int -> bool) -> int -> bool **)

let fb_push b f x0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> b)
    (fun n -> f n)
    x0

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

(** val modsummer' :
    int -> int -> var -> var -> var -> posi -> posi -> var -> (int -> bool)
    -> scom **)

let rec modsummer' i n m x0 y0 c3 c4 s0 fC =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> if fC 0 then adder01 n x0 y0 c3 else SKIP)
    (fun i' -> Seq ((Seq ((Seq ((modsummer' i' n m x0 y0 c3 c4 s0 fC),
    (moddoubler01 n x0 m c3 c4))), (coq_SWAP c4 (s0, i)))),
    (if fC i then modadder21 n y0 x0 m c3 c4 else SKIP)))
    i

(** val modsummer :
    int -> var -> var -> var -> posi -> posi -> var -> int -> scom **)

let modsummer n m x0 y0 c3 c4 s0 c =
  modsummer' (sub n (Pervasives.succ 0)) n m x0 y0 c3 c4 s0 (nat2fb c)

(** val modmult_half :
    int -> var -> var -> var -> posi -> posi -> var -> int -> scom **)

let modmult_half n m x0 y0 c3 c4 s0 c =
  Seq ((modsummer n m x0 y0 c3 c4 s0 c),
    (sinv (modsummer n m x0 y0 c3 c4 s0 0)))

(** val modmult_full :
    int -> int -> int -> var -> var -> var -> posi -> posi -> var -> scom **)

let modmult_full c cinv n m x0 y0 c3 c4 s0 =
  Seq ((modmult_half n m x0 y0 c3 c4 s0 c),
    (sinv (modmult_half n m x0 y0 c3 c4 s0 cinv)))

(** val modmult :
    (int -> bool) -> int -> int -> int -> var -> var -> var -> var -> posi ->
    posi -> scom **)

let modmult m c cinv n x0 y0 z0 s0 c3 c4 =
  Seq ((Seq ((init_v n z0 m), (modmult_full c cinv n z0 x0 y0 c3 c4 s0))),
    (sinv (init_v n z0 m)))

(** val modmult_rev :
    (int -> bool) -> int -> int -> int -> var -> var -> var -> var -> posi ->
    posi -> face **)

let modmult_rev m c cinv n x0 y0 z0 s0 c3 c4 =
  FSeq ((FSeq ((Rev x0), (Exp (modmult m c cinv n x0 y0 z0 s0 c3 c4)))), (Rev
    x0))

(** val rz_adding : var -> int -> int -> (int -> bool) -> scom **)

let rec rz_adding x0 n pos m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP)
    (fun m0 -> Seq ((if m (add pos m0) then RZ (n, (x0, pos)) else SKIP),
    (rz_adding x0 m0 pos m)))
    n

(** val rz_adder' : var -> int -> int -> (int -> bool) -> scom **)

let rec rz_adder' x0 n pos m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP)
    (fun m0 -> Seq ((rz_adding x0 n pos m),
    (rz_adder' x0 m0 (add pos (Pervasives.succ 0)) m)))
    n

(** val rz_adder : var -> int -> (int -> bool) -> scom **)

let rz_adder x0 n m =
  rz_adder' x0 n 0 m

(** val one_cu_adder : var -> int -> posi -> (int -> bool) -> scom **)

let one_cu_adder x0 n c3 m =
  CU (c3, (rz_adder x0 n m))

(** val rz_modadder :
    var -> int -> posi -> posi -> (int -> bool) -> (int -> bool) -> face **)

let rz_modadder x0 n y0 c a n0 =
  FSeq ((FSeq ((FSeq ((FSeq ((FSeq ((FSeq ((FSeq ((FSeq ((Exp (Seq
    ((one_cu_adder x0 n y0 a), (rz_adder x0 n n0)))), (RQFT x0))), (Exp
    (coq_CNOT (x0, (sub n (Pervasives.succ 0))) c)))), (QFT x0))), (Exp (Seq
    ((one_cu_adder x0 n c n0), (one_cu_adder x0 n y0 a)))))), (RQFT x0))),
    (Exp (Seq ((Seq ((X (x0, (sub n (Pervasives.succ 0)))),
    (coq_CNOT (x0, (sub n (Pervasives.succ 0))) c))), (X (x0,
    (sub n (Pervasives.succ 0))))))))), (QFT x0))), (Exp
    (one_cu_adder x0 n y0 a)))

(** val rz_modmult' :
    var -> var -> int -> int -> posi -> (int -> bool) -> (int -> bool) -> face **)

let rec rz_modmult' y0 x0 n size c a n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Exp SKIP)
    (fun m -> FSeq ((rz_modadder x0 size (y0, m) c a n0),
    (rz_modmult' y0 x0 m size c a n0)))
    n

(** val rz_modmult_half :
    var -> var -> int -> posi -> (int -> bool) -> (int -> bool) -> face **)

let rz_modmult_half y0 x0 n c a n0 =
  FSeq ((FSeq ((QFT x0), (rz_modmult' y0 x0 n n c a n0))), (RQFT x0))

(** val rz_modmult_full :
    var -> var -> int -> posi -> (int -> bool) -> (int -> bool) -> (int ->
    bool) -> face **)

let rz_modmult_full y0 x0 n c c0 cinv n0 =
  FSeq ((rz_modmult_half y0 x0 n c c0 n0),
    (finv (rz_modmult_half y0 x0 n c cinv n0)))

type varType =
| NType
| SType

(** val id_fun : int -> int **)

let id_fun i =
  i

(** val compile_var' :
    ((var * int) * varType) list -> int -> int ->
    (((int * int) * varType) * int) * (int -> int) **)

let rec compile_var' l dim x0 =
  match l with
  | [] -> ((((0, 0), NType), 0), id_fun)
  | p :: l' ->
    let (p0, v) = p in
    let (x1, n) = p0 in
    (match v with
     | NType ->
       if (=) x1 x0
       then ((((dim, n), NType), 0), id_fun)
       else compile_var' l' (add dim n) x0
     | SType ->
       if (=) x1 x0
       then ((((dim, n), SType), 0), id_fun)
       else compile_var' l' (add (add dim n) (Pervasives.succ 0)) x0)

(** val compile_var :
    ((var * int) * varType) list -> int ->
    (((int * int) * varType) * int) * (int -> int) **)

let compile_var l =
  compile_var' l 0

(** val get_dim : ((var * int) * varType) list -> int **)

let rec get_dim = function
| [] -> 0
| p :: l' ->
  let (p0, v) = p in
  let (_, n) = p0 in
  (match v with
   | NType -> add n (get_dim l')
   | SType -> add (add n (Pervasives.succ 0)) (get_dim l'))

(** val inter_num : int -> varType -> int **)

let inter_num size = function
| NType -> size
| SType -> add size (Pervasives.succ 0)

(** val rz_ang : int -> coq_R **)

let rz_ang n =
  coq_Rdiv (coq_Rmult (coq_IZR (Zpos (Coq_xO Coq_xH))) coq_PI)
    (pow (coq_IZR (Zpos (Coq_xO Coq_xH))) n)

(** val rrz_ang : int -> coq_R **)

let rrz_ang n =
  coq_Rminus (coq_IZR (Zpos Coq_xH))
    (coq_Rdiv (coq_Rmult (coq_IZR (Zpos (Coq_xO Coq_xH))) coq_PI)
      (pow (coq_IZR (Zpos (Coq_xO Coq_xH))) n))

type vars = int -> (((int * int) * varType) * int) * (int -> int)

(** val shift_fun : (int -> int) -> int -> int -> int -> int **)

let shift_fun f offset size i =
  f (PeanoNat.Nat.modulo (add i offset) size)

(** val trans_lshift :
    vars -> var -> int -> (((int * int) * varType) * int) * (int -> int) **)

let trans_lshift f x0 i =
  let (p, g) = f x0 in
  let (p0, offset) = p in
  let (p1, t) = p0 in
  let (start, size) = p1 in
  if (=) i x0
  then ((((start, size), t),
         (PeanoNat.Nat.modulo (add offset (Pervasives.succ 0))
           (inter_num size t))),
         (shift_fun g (add offset (Pervasives.succ 0)) (inter_num size t)))
  else f i

(** val trans_rshift :
    vars -> var -> int -> (((int * int) * varType) * int) * (int -> int) **)

let trans_rshift f x0 i =
  let (p, g) = f x0 in
  let (p0, offset) = p in
  let (p1, t) = p0 in
  let (start, size) = p1 in
  if (=) i x0
  then ((((start, size), t),
         (PeanoNat.Nat.modulo
           (sub (add offset (inter_num size t)) (Pervasives.succ 0))
           (inter_num size t))),
         (shift_fun g
           (sub (add offset (inter_num size t)) (Pervasives.succ 0))
           (inter_num size t)))
  else f i

(** val find_pos : vars -> var -> int -> int **)

let find_pos f a b =
  let (p, g) = f a in
  let (p0, _) = p in
  let (p1, _) = p0 in let (start, _) = p1 in add start (g b)

(** val trans_exp : vars -> int -> scom -> base_ucom * vars **)

let rec trans_exp f dim = function
| SKIP -> ((coq_SKIP __), f)
| X p -> let (a, b) = p in ((coq_X (find_pos f a b)), f)
| CU (p, e1) ->
  let (a, b) = p in
  (match e1 with
   | X p0 ->
     let (c, d) = p0 in ((SQIR.coq_CNOT (find_pos f a b) (find_pos f c d)), f)
   | _ ->
     let (e1', f') = trans_exp f dim e1 in
     ((control dim (find_pos f a b) e1'), f'))
| RZ (q, p) -> let (a, b) = p in ((coq_Rz (rz_ang q) (find_pos f a b)), f)
| RRZ (q, p) -> let (a, b) = p in ((coq_Rz (rrz_ang q) (find_pos f a b)), f)
| Lshift x0 -> ((coq_SKIP __), (trans_lshift f x0))
| Rshift x0 -> ((coq_SKIP __), (trans_rshift f x0))
| Seq (e1, e2) ->
  let (e1', f') = trans_exp f dim e1 in
  let (e2', f'') = trans_exp f' dim e2 in ((Coq_useq (e1', e2')), f'')

(** val controlled_rotations_gen : int -> int -> int -> base_ucom **)

let rec controlled_rotations_gen dim start n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP __)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> coq_SKIP __)
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        control dim (add start (Pervasives.succ 0))
          (coq_Rz
            (coq_Rdiv (coq_Rmult (coq_IZR (Zpos (Coq_xO Coq_xH))) coq_PI)
              (pow (coq_IZR (Zpos (Coq_xO Coq_xH))) n)) start))
        (fun _ -> Coq_useq ((controlled_rotations_gen dim start n'),
        (control dim (add start n')
          (coq_Rz
            (coq_Rdiv (coq_Rmult (coq_IZR (Zpos (Coq_xO Coq_xH))) coq_PI)
              (pow (coq_IZR (Zpos (Coq_xO Coq_xH))) n)) start))))
        n0)
      n')
    n

(** val coq_QFT_gen : int -> int -> int -> base_ucom **)

let rec coq_QFT_gen dim start n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP __)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> coq_H start)
      (fun _ -> Coq_useq ((coq_H start), (Coq_useq
      ((controlled_rotations_gen dim start n),
      (map_qubits dim (fun x0 -> Pervasives.succ x0)
        (coq_QFT_gen dim start n'))))))
      n')
    n

(** val trans_qft : int -> vars -> var -> base_ucom **)

let trans_qft dim f x0 =
  let (p, _) = f x0 in
  let (p0, _) = p in
  let (p1, _) = p0 in let (start, size) = p1 in coq_QFT_gen dim start size

(** val nH : int -> int -> int -> int -> int -> base_ucom **)

let rec nH dim start offset size n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP __)
    (fun m -> Coq_useq
    ((coq_H (add (PeanoNat.Nat.modulo (add start offset) size) m)),
    (nH dim start offset size m)))
    n

(** val trans_h : int -> vars -> var -> base_ucom **)

let trans_h dim f x0 =
  let (p, _) = f x0 in
  let (p0, offset) = p in
  let (p1, t) = p0 in
  let (start, size) = p1 in nH dim start offset (inter_num size t) size

(** val rev_meaning : (int -> int) -> int -> int -> int -> int **)

let rev_meaning g offset size i =
  g
    (add
      (sub (sub size (Pervasives.succ 0))
        (PeanoNat.Nat.modulo (sub (add i size) offset) size)) offset)

(** val trans_rev :
    vars -> var -> int -> (((int * int) * varType) * int) * (int -> int) **)

let trans_rev f x0 i =
  let (p, g) = f x0 in
  let (p0, offset) = p in
  let (p1, t) = p0 in
  let (start, size) = p1 in
  if (=) x0 i
  then ((((start, size), t), offset),
         (rev_meaning g offset (inter_num size t)))
  else f i

(** val move_bits : int -> int -> int -> int -> base_ucom **)

let rec move_bits dim lstart rstart n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP __)
    (fun m -> Coq_useq ((SQIR.coq_SWAP (add lstart m) (add rstart m)),
    (move_bits dim lstart rstart m)))
    n

(** val move_left' : int -> int -> int -> int -> base_ucom **)

let rec move_left' dim n start m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP __)
    (fun i -> Coq_useq ((move_bits dim start (add start m) m),
    (move_left' dim i (add start m) m)))
    n

(** val move_left : int -> int -> int -> int -> base_ucom **)

let move_left dim start m size =
  move_left' dim (PeanoNat.Nat.div size m) start m

(** val move_right' : int -> int -> int -> int -> base_ucom **)

let rec move_right' dim n start m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP __)
    (fun i -> Coq_useq ((move_bits dim (sub start m) start m),
    (move_right' dim i (sub start m) m)))
    n

(** val move_right : int -> int -> int -> int -> base_ucom **)

let move_right dim start m size =
  move_right' dim (PeanoNat.Nat.div size m) (add start size) m

(** val small_move_left' : int -> int -> int -> base_ucom **)

let rec small_move_left' dim start n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP __)
    (fun m -> Coq_useq ((SQIR.coq_SWAP (add start m) (add start n)),
    (small_move_left' dim start m)))
    n

(** val small_move_left : int -> int -> int -> int -> base_ucom **)

let rec small_move_left dim start m size =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP __)
    (fun i -> Coq_useq ((small_move_left' dim start m),
    (small_move_left dim (add start (Pervasives.succ 0)) m i)))
    size

(** val small_move_right' : int -> int -> int -> base_ucom **)

let rec small_move_right' dim start n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP __)
    (fun m -> Coq_useq ((small_move_right' dim start m),
    (SQIR.coq_SWAP (add start m) (add start n))))
    n

(** val small_move_right : int -> int -> int -> int -> base_ucom **)

let rec small_move_right dim start m size =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP __)
    (fun i -> Coq_useq ((small_move_right' dim start m),
    (small_move_right dim (sub start (Pervasives.succ 0)) m i)))
    size

(** val move_reset : int -> int -> int -> int -> base_ucom **)

let move_reset dim start offset size =
  if PeanoNat.Nat.ltb offset (sub size offset)
  then Coq_useq ((move_left dim start offset size),
         (small_move_left dim
           (add start (mul (PeanoNat.Nat.div size offset) offset)) offset
           (PeanoNat.Nat.modulo size offset)))
  else Coq_useq ((move_right dim start offset size),
         (small_move_right dim
           (sub (add start (PeanoNat.Nat.modulo size offset))
             (Pervasives.succ 0)) offset (PeanoNat.Nat.modulo size offset)))

(** val set_reset_fun :
    vars -> var -> int -> int -> varType -> int ->
    (((int * int) * varType) * int) * (int -> int) **)

let set_reset_fun f x0 start size t i =
  if (=) i x0 then ((((start, size), t), 0), id_fun) else f i

(** val trans_reset : int -> vars -> var -> base_ucom * vars **)

let trans_reset dim f x0 =
  let (p, _) = f x0 in
  let (p0, offset) = p in
  let (p1, t) = p0 in
  let (start, size) = p1 in
  ((move_reset dim start offset (inter_num size t)),
  (set_reset_fun f x0 start size t))

(** val trans_face : vars -> int -> face -> base_ucom * vars **)

let rec trans_face f dim = function
| Exp s0 -> trans_exp f dim s0
| QFT x0 -> ((trans_qft dim f x0), f)
| RQFT x0 -> ((trans_qft dim f x0), f)
| Reset x0 -> trans_reset dim f x0
| Rev x0 -> ((coq_SKIP __), (trans_rev f x0))
| H x0 -> ((trans_h dim f x0), f)
| FSeq (e1, e2) ->
  let (e1', f') = trans_face f dim e1 in
  let (e2', f'') = trans_face f' dim e2 in ((Coq_useq (e1', e2')), f'')

(** val x : int **)

let x =
  Pervasives.succ 0

(** val y : int **)

let y =
  Pervasives.succ (Pervasives.succ 0)

(** val z : int **)

let z =
  Pervasives.succ (Pervasives.succ (Pervasives.succ 0))

(** val s : int **)

let s =
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))

(** val c1 : int **)

let c1 =
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))

(** val c2 : int **)

let c2 =
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))

(** val csplit : scom -> scom **)

let csplit = function
| CU (n, p0) ->
  (match p0 with
   | Seq (p1, p2) -> Seq ((CU (n, p1)), (CU (n, p2)))
   | _ -> CU (n, p0))
| x0 -> x0

(** val csplit_face : face -> face **)

let rec csplit_face p = match p with
| Exp s0 -> Exp (csplit s0)
| FSeq (e1, e2) -> FSeq ((csplit_face e1), (csplit_face e2))
| _ -> p

(** val bcelim : scom -> scom **)

let rec bcelim = function
| CU (q, p0) -> (match bcelim p0 with
                 | SKIP -> SKIP
                 | x0 -> CU (q, x0))
| Seq (p1, p2) ->
  (match bcelim p1 with
   | SKIP -> bcelim p2
   | x0 -> (match bcelim p2 with
            | SKIP -> x0
            | x1 -> Seq (x0, x1)))
| x0 -> x0

(** val bcelim_face : face -> face **)

let rec bcelim_face p = match p with
| Exp s0 -> Exp (bcelim s0)
| FSeq (e1, e2) ->
  (match bcelim_face e1 with
   | Exp s0 ->
     (match s0 with
      | SKIP -> bcelim_face e2
      | x0 ->
        let e1' = Exp x0 in
        (match bcelim_face e2 with
         | Exp s1 -> (match s1 with
                      | SKIP -> e1'
                      | x1 -> FSeq (e1', (Exp x1)))
         | x1 -> FSeq (e1', x1)))
   | x0 ->
     (match bcelim_face e2 with
      | Exp s0 -> (match s0 with
                   | SKIP -> x0
                   | x1 -> FSeq (x0, (Exp x1)))
      | x1 -> FSeq (x0, x1)))
| _ -> p

(** val modmult_vars : int -> ((int * int) * varType) list **)

let modmult_vars n =
  ((x, n), SType) :: (((y, n), NType) :: (((z, n), NType) :: (((s, n),
    NType) :: (((c1, (Pervasives.succ 0)), NType) :: (((c2, (Pervasives.succ
    0)), NType) :: [])))))

(** val modmult_var_fun :
    int -> int -> (((int * int) * varType) * int) * (int -> int) **)

let modmult_var_fun n =
  compile_var (modmult_vars n)

(** val modmult_sqir : int -> int -> int -> int -> base_ucom * vars **)

let modmult_sqir m c cinv n =
  trans_face (modmult_var_fun n) (get_dim (modmult_vars n))
    (csplit_face
      (bcelim_face (modmult_rev (nat2fb m) c cinv n x y z s (c1, 0) (c2, 0))))

(** val rz_mod_vars : int -> ((int * int) * varType) list **)

let rz_mod_vars n =
  ((x, n), NType) :: (((y, n), NType) :: (((c1, (Pervasives.succ 0)),
    NType) :: []))

(** val rz_var_fun :
    int -> int -> (((int * int) * varType) * int) * (int -> int) **)

let rz_var_fun n =
  compile_var (rz_mod_vars n)

(** val rz_mod_sqir : int -> int -> int -> int -> base_ucom * vars **)

let rz_mod_sqir m c cinv n =
  trans_face (rz_var_fun n) (get_dim (rz_mod_vars n))
    (csplit_face
      (bcelim_face
        (rz_modmult_full x y n (c1, 0) (nat2fb c) (nat2fb cinv) (nat2fb m))))
