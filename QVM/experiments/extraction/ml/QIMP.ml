open Bool
open CLArith
open Datatypes
open FMapList
open Factorial
open Nat
open PQASM
open Prelim
open RZArith

type __ = Obj.t

type fvar = int

type flag =
| QFTA
| Classic

(** val flag_eq : flag -> flag -> bool **)

let flag_eq t1 t2 =
  match t1 with
  | QFTA -> (match t2 with
             | QFTA -> true
             | Classic -> false)
  | Classic -> (match t2 with
                | QFTA -> false
                | Classic -> true)

type qvar =
| G of var
| L of var

(** val qty_eq : qvar -> qvar -> bool **)

let qty_eq t1 t2 =
  match t1 with
  | G x -> (match t2 with
            | G y -> (=) x y
            | L _ -> false)
  | L x -> (match t2 with
            | G _ -> false
            | L y -> (=) x y)

(** val qdty_eq : (qvar * int) -> (qvar * int) -> bool **)

let qdty_eq t1 t2 =
  (&&) (qty_eq (fst t1) (fst t2)) ((=) (snd t1) (snd t2))

type btype =
| Nat
| FixedP
| Bl

(** val bty_eq : btype -> btype -> bool **)

let bty_eq t1 t2 =
  match t1 with
  | Nat -> (match t2 with
            | Nat -> true
            | _ -> false)
  | FixedP -> (match t2 with
               | FixedP -> true
               | _ -> false)
  | Bl -> (match t2 with
           | Bl -> true
           | _ -> false)

type atype =
| C
| Q

(** val aty_eq : atype -> atype -> bool **)

let aty_eq t1 t2 =
  match t1 with
  | C -> (match t2 with
          | C -> true
          | Q -> false)
  | Q -> (match t2 with
          | C -> false
          | Q -> true)

type typ =
| TArray of atype * btype * int
| TNor of atype * btype

module QvarType =
 struct
  type t = qvar

  (** val compare : t -> t -> qvar OrderedType.coq_Compare **)

  let compare x y =
    match x with
    | G v ->
      (match y with
       | G v0 ->
         let h = blt_reflect v v0 in
         (match h with
          | ReflectT -> OrderedType.LT
          | ReflectF ->
            let h0 = beq_reflect v v0 in
            (match h0 with
             | ReflectT -> OrderedType.EQ
             | ReflectF -> OrderedType.GT))
       | L _ -> OrderedType.GT)
    | L v ->
      (match y with
       | G _ -> OrderedType.LT
       | L v0 ->
         let h = blt_reflect v v0 in
         (match h with
          | ReflectT -> OrderedType.LT
          | ReflectF ->
            let h0 = beq_reflect v v0 in
            (match h0 with
             | ReflectT -> OrderedType.EQ
             | ReflectF -> OrderedType.GT)))

  (** val eq_dec : t -> t -> bool **)

  let eq_dec x y =
    match compare x y with
    | OrderedType.EQ -> true
    | _ -> false
 end

module QvarNatType =
 struct
  type t = qvar * int

  (** val compare : t -> t -> (qvar * int) OrderedType.coq_Compare **)

  let compare x y =
    let (q, n) = x in
    let (q0, n0) = y in
    (match q with
     | G v ->
       (match q0 with
        | G v0 ->
          let h = blt_reflect v v0 in
          (match h with
           | ReflectT -> OrderedType.LT
           | ReflectF ->
             let h0 = beq_reflect v v0 in
             (match h0 with
              | ReflectT ->
                let h1 = blt_reflect n n0 in
                (match h1 with
                 | ReflectT -> OrderedType.LT
                 | ReflectF ->
                   let h2 = beq_reflect n n0 in
                   (match h2 with
                    | ReflectT -> OrderedType.EQ
                    | ReflectF -> OrderedType.GT))
              | ReflectF -> OrderedType.GT))
        | L _ -> OrderedType.GT)
     | L v ->
       (match q0 with
        | G _ -> OrderedType.LT
        | L v0 ->
          let h = beq_reflect v v0 in
          (match h with
           | ReflectT ->
             let h0 = blt_reflect n n0 in
             (match h0 with
              | ReflectT -> OrderedType.LT
              | ReflectF ->
                let h1 = beq_reflect n n0 in
                (match h1 with
                 | ReflectT -> OrderedType.EQ
                 | ReflectF -> OrderedType.GT))
           | ReflectF ->
             let h0 = blt_reflect v v0 in
             (match h0 with
              | ReflectT -> OrderedType.LT
              | ReflectF -> OrderedType.GT))))

  (** val eq_dec : t -> t -> bool **)

  let eq_dec x y =
    match compare x y with
    | OrderedType.EQ -> true
    | _ -> false
 end

type factor =
| Var of qvar
| Num of (int -> bool)

type cfac =
| Index of qvar * factor
| Nor of factor

type cexp =
| Coq_clt of btype * cfac * cfac
| Coq_ceq of btype * cfac * cfac
| Coq_iseven of cfac

type qexp =
| Coq_qinv of cfac
| Coq_call of fvar * cfac
| Coq_qif of cexp * qexp * qexp
| Coq_qfor of var * cfac * qexp
| Coq_qseq of qexp * qexp
| Coq_skip
| Coq_init of cfac * cfac
| Coq_nadd of cfac * cfac
| Coq_nsub of cfac * cfac
| Coq_nmul of cfac * cfac * cfac
| Coq_fadd of cfac * cfac
| Coq_fsub of cfac * cfac
| Coq_fmul of cfac * cfac * cfac
| Coq_qxor of cfac * cfac
| Coq_slrot of cfac
| Coq_ndiv of cfac * cfac * cfac
| Coq_nmod of cfac * cfac * cfac
| Coq_nfac of cfac * cfac
| Coq_fdiv of cfac * cfac
| Coq_ncsub of cfac * cfac * cfac
| Coq_ncadd of cfac * cfac * cfac
| Coq_fcsub of cfac * cfac * cfac
| Coq_fcadd of cfac * cfac * cfac
| Coq_ncmul of cfac * cfac * cfac
| Coq_fndiv of cfac * cfac * cfac

module BEnv = Make(QvarType)

type benv = typ BEnv.t

(** val empty_benv : typ BEnv.t **)

let empty_benv =
  BEnv.empty

(** val bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option **)

let bind a f =
  match a with
  | Some a0 -> f a0
  | None -> None

(** val typ_factor : benv -> btype -> factor -> (atype * btype) option **)

let typ_factor bv t0 = function
| Var x ->
  bind (BEnv.find x bv) (fun re ->
    match re with
    | TArray (_, _, _) -> None
    | TNor (x0, y) -> if bty_eq y t0 then Some (x0, y) else None)
| Num _ -> Some (C, t0)

(** val typ_factor_full :
    benv -> atype -> btype -> factor -> (atype * btype) option **)

let typ_factor_full bv a t0 = function
| Var x ->
  bind (BEnv.find x bv) (fun re ->
    match re with
    | TArray (_, _, _) -> None
    | TNor (x0, y) ->
      if (&&) (aty_eq a x0) (bty_eq y t0) then Some (x0, y) else None)
| Num _ -> if aty_eq a C then Some (C, t0) else None

(** val type_factor : benv -> btype -> cfac -> (atype * btype) option **)

let type_factor bv t0 = function
| Index (x, ic) ->
  bind (BEnv.find x bv) (fun re ->
    match re with
    | TArray (a, b, _) ->
      if bty_eq b t0
      then bind (typ_factor_full bv C Nat ic) (fun _ -> Some (a, t0))
      else None
    | TNor (_, _) -> None)
| Nor c -> typ_factor bv t0 c

(** val a_nat2fb : (int -> bool) -> int -> int **)

let rec a_nat2fb f n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> 0)
    (fun m ->
    add
      (mul (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) m)
        (PeanoNat.Nat.b2n (f m))) (a_nat2fb f m))
    n

(** val is_q : typ -> bool **)

let is_q = function
| TArray (a, _, _) -> (match a with
                       | C -> false
                       | Q -> true)
| TNor (a, _) -> (match a with
                  | C -> false
                  | Q -> true)

(** val is_c : typ -> bool **)

let is_c = function
| TArray (a, _, _) -> (match a with
                       | C -> true
                       | Q -> false)
| TNor (a, _) -> (match a with
                  | C -> true
                  | Q -> false)

(** val get_ct : typ -> btype **)

let get_ct = function
| TArray (_, y, _) -> y
| TNor (_, y) -> y

(** val no_zero : typ -> bool **)

let no_zero = function
| TArray (_, _, n) -> if (=) n 0 then false else true
| TNor (_, _) -> true

(** val gen_env : (typ * var) list -> benv -> benv option **)

let rec gen_env l bv =
  match l with
  | [] -> Some bv
  | p :: xl ->
    let (t0, x) = p in
    bind (gen_env xl bv) (fun new_env ->
      if no_zero t0 then Some (BEnv.add (L x) t0 new_env) else None)

module Store = Make(QvarNatType)

type 'a value =
| Value of 'a
| Error

(** val get_type_num : typ -> int **)

let get_type_num = function
| TArray (_, _, n) -> n
| TNor (_, _) -> Pervasives.succ 0

(** val l_rotate : (int -> bool) -> int -> int -> bool **)

let l_rotate f n i =
  f (PeanoNat.Nat.modulo (sub (add i n) (Pervasives.succ 0)) n)

type cstore = (int -> bool) Store.t

(** val empty_cstore : (int -> bool) Store.t **)

let empty_cstore =
  Store.empty

(** val make_value :
    int -> btype -> (int -> bool) option -> (int -> bool) option **)

let make_value size b c =
  bind c (fun cv ->
    match b with
    | Nat -> Some (cut_n cv size)
    | FixedP -> Some (fbrev size (cut_n cv size))
    | Bl -> Some (cut_n cv (Pervasives.succ 0)))

(** val par_eval_fc :
    benv -> int -> cstore -> btype -> factor -> (int -> bool) option **)

let par_eval_fc bv size r b = function
| Var x ->
  bind (BEnv.find x bv) (fun re ->
    if is_q re then None else make_value size b (Store.find (x, 0) r))
| Num n -> make_value size b (Some n)

(** val par_eval_cfac_check :
    (qvar -> int) -> benv -> int -> cstore -> btype -> cfac -> (int -> bool)
    value option **)

let par_eval_cfac_check smap bv size r b = function
| Index (x, n) ->
  bind (par_eval_fc bv size r Nat n) (fun v ->
    if PeanoNat.Nat.ltb (a_nat2fb v size) (smap x)
    then bind (BEnv.find x bv) (fun re ->
           if is_q re
           then None
           else bind
                  (make_value size b (Store.find (x, (a_nat2fb v size)) r))
                  (fun val0 -> Some (Value val0)))
    else Some Error)
| Nor x -> bind (par_eval_fc bv size r b x) (fun val0 -> Some (Value val0))

(** val par_find_var :
    benv -> int -> cstore -> cfac -> (qvar * int) option **)

let par_find_var bv size r = function
| Index (x, n) ->
  bind (par_eval_fc bv size r Nat n) (fun val0 -> Some (x,
    (a_nat2fb val0 size)))
| Nor v -> (match v with
            | Var x -> Some (x, 0)
            | Num _ -> None)

(** val par_find_var_check :
    (qvar -> int) -> benv -> int -> cstore -> cfac -> (qvar * int) value
    option **)

let par_find_var_check smap bv size r = function
| Index (x, n) ->
  bind (par_eval_fc bv size r Nat n) (fun val0 ->
    if PeanoNat.Nat.ltb (a_nat2fb val0 size) (smap x)
    then Some (Value (x, (a_nat2fb val0 size)))
    else Some Error)
| Nor v -> (match v with
            | Var x -> Some (Value (x, 0))
            | Num _ -> None)

(** val qvar_eq : benv -> int -> cstore -> cfac -> cfac -> bool **)

let qvar_eq bv size r x y =
  match par_find_var bv size r x with
  | Some a ->
    (match par_find_var bv size r y with
     | Some b -> qdty_eq a b
     | None -> false)
  | None -> false

(** val get_size : int -> btype -> int **)

let get_size size t0 =
  if bty_eq t0 Bl then Pervasives.succ 0 else size

(** val clt_circuit_two :
    int -> flag -> btype -> ((qvar * int) -> var) -> (qvar * int) ->
    (qvar * int) -> var -> int -> pexp **)

let clt_circuit_two size f b vmap x y stack sn =
  if flag_eq f Classic
  then Exp
         (comparator01 (get_size size b) (vmap x) (vmap y) (stack,
           (Pervasives.succ sn)) (stack, sn))
  else rz_full_comparator (vmap x) (get_size size b) (stack, sn) (vmap y)

(** val clt_circuit_left :
    int -> flag -> btype -> ((qvar * int) -> var) -> (qvar * int) -> (int ->
    bool) -> var -> var -> int -> pexp **)

let clt_circuit_left size f b vmap x y stack temp sn =
  if flag_eq f Classic
  then Exp (Seq ((Seq ((init_v (get_size size b) temp y),
         (comparator01 (get_size size b) (vmap x) temp (stack,
           (Pervasives.succ sn)) (stack, sn)))),
         (init_v (get_size size b) temp y)))
  else rz_comparator (vmap x) (get_size size b) (stack, sn)
         (a_nat2fb y (get_size size b))

(** val clt_circuit_right :
    int -> flag -> btype -> ((qvar * int) -> var) -> (int -> bool) ->
    (qvar * int) -> var -> var -> int -> pexp **)

let clt_circuit_right size f b vmap x y stack temp sn =
  if flag_eq f Classic
  then Exp (Seq ((Seq ((init_v (get_size size b) temp x),
         (comparator01 (get_size size b) temp (vmap y) (stack,
           (Pervasives.succ sn)) (stack, sn)))),
         (init_v (get_size size b) temp x)))
  else PSeq ((PSeq ((Exp (init_v (get_size size b) temp x)),
         (rz_full_comparator temp (get_size size b) (stack, sn) (vmap y)))),
         (Exp (init_v (get_size size b) temp x)))

(** val gen_clt_c :
    (qvar -> int) -> ((qvar * int) -> var) -> benv -> int -> flag -> cstore
    -> btype -> var -> var -> int -> cfac -> cfac -> ((pexp
    option * int) * bool option) value option **)

let gen_clt_c smap vmap bv size f r b stack temp sn x y =
  bind (type_factor bv b x) (fun t1 ->
    bind (type_factor bv b y) (fun t2 ->
      if (&&) (aty_eq (fst t1) Q) (aty_eq (fst t2) C)
      then (match par_find_var_check smap bv (get_size size b) r x with
            | Some v ->
              (match v with
               | Value vx ->
                 bind (par_eval_cfac_check smap bv size r b y) (fun t2v ->
                   match t2v with
                   | Value t2v' ->
                     Some (Value (((Some
                       (clt_circuit_left size f b vmap vx t2v' stack temp sn)),
                       (Pervasives.succ sn)), None))
                   | Error -> Some Error)
               | Error -> Some Error)
            | None -> None)
      else if (&&) (aty_eq (fst t1) Q) (aty_eq (fst t2) Q)
           then bind (par_find_var_check smap bv (get_size size b) r x)
                  (fun vxv ->
                  bind (par_find_var_check smap bv (get_size size b) r y)
                    (fun vyv ->
                    match vxv with
                    | Value vx ->
                      (match vyv with
                       | Value vy ->
                         Some (Value (((Some
                           (clt_circuit_two size f b vmap vx vy stack sn)),
                           (Pervasives.succ sn)), None))
                       | Error -> Some Error)
                    | Error -> Some Error))
           else if (&&) (aty_eq (fst t1) C) (aty_eq (fst t2) Q)
                then (match par_find_var_check smap bv (get_size size b) r y with
                      | Some v ->
                        (match v with
                         | Value vy ->
                           bind (par_eval_cfac_check smap bv size r b x)
                             (fun t1v ->
                             match t1v with
                             | Value t1v' ->
                               Some (Value (((Some
                                 (clt_circuit_right size f b vmap t1v' vy
                                   stack temp sn)), (Pervasives.succ sn)),
                                 None))
                             | Error -> Some Error)
                         | Error -> Some Error)
                      | None -> None)
                else bind (par_eval_cfac_check smap bv size r b x)
                       (fun t1v ->
                       bind (par_eval_cfac_check smap bv size r b y)
                         (fun t2v ->
                         match t1v with
                         | Value t1v' ->
                           (match t2v with
                            | Value t2v' ->
                              Some (Value ((None, sn), (Some
                                (PeanoNat.Nat.ltb (a_nat2fb t1v' size)
                                  (a_nat2fb t2v' size)))))
                            | Error -> Some Error)
                         | Error -> Some Error))))

(** val ceq_circuit_two :
    int -> flag -> btype -> ((qvar * int) -> var) -> (qvar * int) ->
    (qvar * int) -> var -> int -> pexp **)

let ceq_circuit_two size f b vmap x y stack sn =
  if flag_eq f Classic
  then Exp (Seq ((Seq
         ((comparator01 (get_size size b) (vmap y) (vmap x) (stack,
            (Pervasives.succ sn)) (stack, sn)),
         (comparator01 (get_size size b) (vmap x) (vmap y) (stack,
           (Pervasives.succ sn)) (stack, sn)))), (X (stack, sn))))
  else PSeq ((PSeq
         ((rz_full_comparator (vmap x) (get_size size b) (stack, sn) (vmap y)),
         (rz_full_comparator (vmap y) (get_size size b) (stack, sn) (vmap x)))),
         (Exp (X (stack, sn))))

(** val ceq_circuit_left :
    int -> flag -> btype -> ((qvar * int) -> var) -> (qvar * int) -> (int ->
    bool) -> var -> var -> int -> pexp **)

let ceq_circuit_left size f b vmap x y stack temp sn =
  if flag_eq f Classic
  then Exp (Seq ((Seq ((Seq ((Seq ((init_v (get_size size b) temp y),
         (comparator01 (get_size size b) (vmap x) temp (stack,
           (Pervasives.succ sn)) (stack, sn)))),
         (comparator01 (get_size size b) temp (vmap x) (stack,
           (Pervasives.succ sn)) (stack, sn)))), (X (stack, sn)))),
         (init_v (get_size size b) temp y)))
  else PSeq ((PSeq ((PSeq ((Exp (init_v (get_size size b) temp y)),
         (rz_comparator (vmap x) (get_size size b) (stack, sn)
           (a_nat2fb y (get_size size b))))),
         (rz_full_comparator temp (get_size size b) (stack, sn) (vmap x)))),
         (Exp (Seq ((X (stack, sn)), (init_v (get_size size b) temp y)))))

(** val ceq_circuit_right :
    int -> flag -> btype -> ((qvar * int) -> var) -> (int -> bool) ->
    (qvar * int) -> var -> var -> int -> pexp **)

let ceq_circuit_right size f b vmap x y stack temp sn =
  if flag_eq f Classic
  then Exp (Seq ((Seq ((Seq ((Seq ((init_v (get_size size b) temp x),
         (comparator01 (get_size size b) temp (vmap y) (stack,
           (Pervasives.succ sn)) (stack, sn)))),
         (comparator01 (get_size size b) (vmap y) temp (stack,
           (Pervasives.succ sn)) (stack, sn)))), (X (stack, sn)))),
         (init_v (get_size size b) temp x)))
  else PSeq ((PSeq ((PSeq ((Exp (init_v (get_size size b) temp x)),
         (rz_full_comparator temp (get_size size b) (stack, sn) (vmap y)))),
         (rz_comparator (vmap y) (get_size size b) (stack, sn)
           (a_nat2fb x (get_size size b))))), (Exp (Seq ((X (stack, sn)),
         (init_v (get_size size b) temp x)))))

(** val gen_ceq_c :
    (qvar -> int) -> ((qvar * int) -> var) -> benv -> int -> flag -> cstore
    -> btype -> var -> var -> int -> cfac -> cfac -> ((pexp
    option * int) * bool option) value option **)

let gen_ceq_c smap vmap bv size f r b stack temp sn x y =
  bind (type_factor bv b x) (fun t1 ->
    bind (type_factor bv b y) (fun t2 ->
      if (&&) (aty_eq (fst t1) Q) (aty_eq (fst t2) C)
      then (match par_find_var_check smap bv (get_size size b) r x with
            | Some v ->
              (match v with
               | Value vx ->
                 bind (par_eval_cfac_check smap bv size r b y) (fun t2v ->
                   match t2v with
                   | Value t2v' ->
                     Some (Value (((Some
                       (ceq_circuit_left size f b vmap vx t2v' stack temp sn)),
                       (Pervasives.succ sn)), None))
                   | Error -> Some Error)
               | Error -> Some Error)
            | None -> None)
      else if (&&) (aty_eq (fst t1) Q) (aty_eq (fst t2) Q)
           then bind (par_find_var_check smap bv (get_size size b) r x)
                  (fun vxv ->
                  bind (par_find_var_check smap bv (get_size size b) r y)
                    (fun vyv ->
                    match vxv with
                    | Value vx ->
                      (match vyv with
                       | Value vy ->
                         Some (Value (((Some
                           (ceq_circuit_two size f b vmap vx vy stack sn)),
                           (Pervasives.succ sn)), None))
                       | Error -> Some Error)
                    | Error -> Some Error))
           else if (&&) (aty_eq (fst t1) C) (aty_eq (fst t2) Q)
                then (match par_find_var_check smap bv (get_size size b) r y with
                      | Some v ->
                        (match v with
                         | Value vy ->
                           bind (par_eval_cfac_check smap bv size r b x)
                             (fun t1v ->
                             match t1v with
                             | Value t1v' ->
                               Some (Value (((Some
                                 (ceq_circuit_right size f b vmap t1v' vy
                                   stack temp sn)), (Pervasives.succ sn)),
                                 None))
                             | Error -> Some Error)
                         | Error -> Some Error)
                      | None -> None)
                else bind (par_eval_cfac_check smap bv size r b x)
                       (fun t1v ->
                       bind (par_eval_cfac_check smap bv size r b y)
                         (fun t2v ->
                         match t1v with
                         | Value t1v' ->
                           (match t2v with
                            | Value t2v' ->
                              Some (Value ((None, sn), (Some
                                ((=) (a_nat2fb t1v' size)
                                  (a_nat2fb t2v' size)))))
                            | Error -> Some Error)
                         | Error -> Some Error))))

(** val compile_cexp :
    int -> (qvar -> int) -> ((qvar * int) -> var) -> benv -> flag -> cstore
    -> var -> var -> int -> cexp -> ((pexp option * int) * bool option) value
    option **)

let compile_cexp size smap vmap bv f r temp stack sn = function
| Coq_clt (b, x, y) ->
  if negb (qvar_eq bv size r x y)
  then gen_clt_c smap vmap bv size f r b temp stack sn x y
  else None
| Coq_ceq (b, x, y) ->
  if negb (qvar_eq bv size r x y)
  then gen_ceq_c smap vmap bv size f r b temp stack sn x y
  else None
| Coq_iseven x ->
  bind (type_factor bv Nat x) (fun t1 ->
    if aty_eq (fst t1) Q
    then None
    else bind (par_eval_cfac_check smap bv size r Nat x) (fun t2v ->
           match t2v with
           | Value t2v' ->
             Some (Value ((None, sn), (Some
               ((=)
                 (PeanoNat.Nat.modulo (a_nat2fb t2v' size) (Pervasives.succ
                   (Pervasives.succ 0))) 0))))
           | Error -> Some Error))

type fmap =
  ((((((fvar * cfac) * pexp) * (qvar -> int)) * ((qvar * int) ->
  var)) * benv) * cstore) list

(** val lookup_fmap :
    fmap -> fvar -> (((((cfac * pexp) * (qvar -> int)) * ((qvar * int) ->
    var)) * benv) * cstore) option **)

let rec lookup_fmap l x =
  match l with
  | [] -> None
  | p0 :: xl ->
    let (p1, r) = p0 in
    let (p2, bv) = p1 in
    let (p3, vmap) = p2 in
    let (p4, smap) = p3 in
    let (p5, p) = p4 in
    let (y, a) = p5 in
    if (=) x y
    then Some (((((a, p), smap), vmap), bv), r)
    else lookup_fmap xl x

(** val combine_c : pexp option -> pexp option -> pexp option **)

let combine_c e1 e2 =
  match e1 with
  | Some e1' ->
    (match e2 with
     | Some e2' -> Some (PSeq (e1', e2'))
     | None -> Some e1')
  | None -> e2

(** val combine_seq : pexp option -> pexp option -> pexp option **)

let combine_seq e1 e2 =
  match e1 with
  | Some e1' ->
    (match e2 with
     | Some e2' -> Some (PSeq (e1', e2'))
     | None -> Some e1')
  | None -> e2

type estore = pexp list Store.t

(** val empty_estore : pexp list Store.t **)

let empty_estore =
  Store.empty

(** val nadd_circuit_two :
    int -> flag -> ((qvar * int) -> var) -> (qvar * int) -> (qvar * int) ->
    var -> int -> pexp **)

let nadd_circuit_two size f vmap x y stack sn =
  if flag_eq f Classic
  then Exp (adder01 size (vmap x) (vmap y) (stack, (Pervasives.succ sn)))
  else rz_full_adder_form (vmap x) size (vmap y)

(** val nadd_circuit_left :
    int -> flag -> ((qvar * int) -> var) -> (qvar * int) -> (int -> bool) ->
    var -> var -> int -> pexp **)

let nadd_circuit_left size f vmap x y stack temp sn =
  if flag_eq f Classic
  then Exp (Seq ((Seq ((init_v size temp y),
         (adder01 size (vmap x) temp (stack, (Pervasives.succ sn))))),
         (init_v size temp y)))
  else rz_adder_form (vmap x) size y

(** val nadd_c :
    int -> (qvar -> int) -> ((qvar * int) -> var) -> benv -> flag -> cstore
    -> var -> var -> int -> estore -> cfac -> cfac -> (((pexp
    option * int) * cstore) * estore) value option **)

let nadd_c size smap vmap bv f r temp stack sn es x y =
  bind (type_factor bv Nat x) (fun t1 ->
    bind (type_factor bv Nat y) (fun t2 ->
      match par_find_var_check smap bv size r x with
      | Some v ->
        (match v with
         | Value vx ->
           if (&&) (aty_eq (fst t1) Q) (aty_eq (fst t2) C)
           then bind (par_eval_cfac_check smap bv size r Nat y) (fun t2v ->
                  match t2v with
                  | Value t2v' ->
                    bind (Store.find vx es) (fun exps -> Some (Value ((((Some
                      (nadd_circuit_left size f vmap vx t2v' stack temp sn)),
                      sn), r),
                      (Store.add vx
                        ((nadd_circuit_left size f vmap vx t2v' stack temp sn) :: exps)
                        es))))
                  | Error -> Some Error)
           else if (&&) (aty_eq (fst t1) Q) (aty_eq (fst t2) Q)
                then bind (par_find_var_check smap bv size r y) (fun vyv ->
                       match vyv with
                       | Value vy ->
                         bind (Store.find vx es) (fun exps -> Some (Value
                           ((((Some
                           (nadd_circuit_two size f vmap vx vy stack sn)),
                           sn), r),
                           (Store.add vx
                             ((nadd_circuit_two size f vmap vx vy stack sn) :: exps)
                             es))))
                       | Error -> Some Error)
                else None
         | Error -> Some Error)
      | None -> None))

(** val nsub_circuit_two :
    int -> flag -> ((qvar * int) -> var) -> (qvar * int) -> (qvar * int) ->
    var -> int -> pexp **)

let nsub_circuit_two size f vmap x y stack sn =
  if flag_eq f Classic
  then Exp (subtractor01 size (vmap x) (vmap y) (stack, (Pervasives.succ sn)))
  else rz_full_sub_form (vmap x) size (vmap y)

(** val nsub_circuit_left :
    int -> flag -> ((qvar * int) -> var) -> (qvar * int) -> (int -> bool) ->
    var -> var -> int -> pexp **)

let nsub_circuit_left size f vmap x y stack temp sn =
  if flag_eq f Classic
  then Exp (Seq ((Seq ((init_v size temp y),
         (subtractor01 size (vmap x) temp (stack, (Pervasives.succ sn))))),
         (init_v size temp y)))
  else rz_sub_right (vmap x) size y

(** val nsub_c :
    int -> (qvar -> int) -> ((qvar * int) -> var) -> benv -> flag -> cstore
    -> var -> var -> int -> estore -> cfac -> cfac -> (((pexp
    option * int) * cstore) * estore) value option **)

let nsub_c size smap vmap bv f r temp stack sn es x y =
  bind (type_factor bv Nat x) (fun t1 ->
    bind (type_factor bv Nat y) (fun t2 ->
      match par_find_var_check smap bv size r x with
      | Some v ->
        (match v with
         | Value vx ->
           if (&&) (aty_eq (fst t1) Q) (aty_eq (fst t2) C)
           then bind (par_eval_cfac_check smap bv size r Nat y) (fun t2v ->
                  match t2v with
                  | Value t2v' ->
                    bind (Store.find vx es) (fun exps -> Some (Value ((((Some
                      (nsub_circuit_left size f vmap vx t2v' stack temp sn)),
                      sn), r),
                      (Store.add vx
                        ((nsub_circuit_left size f vmap vx t2v' stack temp sn) :: exps)
                        es))))
                  | Error -> Some Error)
           else if (&&) (aty_eq (fst t1) Q) (aty_eq (fst t2) Q)
                then bind (par_find_var_check smap bv size r y) (fun vyv ->
                       match vyv with
                       | Value vy ->
                         bind (Store.find vx es) (fun exps -> Some (Value
                           ((((Some
                           (nsub_circuit_two size f vmap vx vy stack sn)),
                           sn), r),
                           (Store.add vx
                             ((nsub_circuit_two size f vmap vx vy stack sn) :: exps)
                             es))))
                       | Error -> Some Error)
                else None
         | Error -> Some Error)
      | None -> None))

(** val fadd_circuit_two :
    int -> flag -> ((qvar * int) -> var) -> (qvar * int) -> (qvar * int) ->
    var -> int -> pexp **)

let fadd_circuit_two size f vmap x y stack sn =
  if flag_eq f Classic
  then Exp (Seq ((Seq ((Seq ((Rev (vmap x)), (Rev (vmap y)))),
         (adder01 size (vmap x) (vmap y) (stack, (Pervasives.succ sn))))),
         (inv_exp (Seq ((Rev (vmap x)), (Rev (vmap y)))))))
  else PSeq ((PSeq ((Exp (Seq ((Rev (vmap x)), (Rev (vmap y))))),
         (rz_full_adder_form (vmap x) size (vmap y)))),
         (inv_pexp (Exp (Seq ((Rev (vmap x)), (Rev (vmap y)))))))

(** val fadd_circuit_left :
    int -> flag -> ((qvar * int) -> var) -> (qvar * int) -> (int -> bool) ->
    var -> var -> int -> pexp **)

let fadd_circuit_left size f vmap x y stack temp sn =
  if flag_eq f Classic
  then Exp (Seq ((Seq ((Seq ((Seq ((Seq ((init_v size temp y), (Rev
         (vmap x)))), (Rev temp))),
         (adder01 size (vmap x) temp (stack, (Pervasives.succ sn))))),
         (inv_exp (Seq ((Rev (vmap x)), (Rev temp)))))),
         (init_v size temp y)))
  else PSeq ((PSeq ((Exp (Rev (vmap x))),
         (rz_adder_form (vmap x) size (fbrev size y)))),
         (inv_pexp (Exp (Rev (vmap x)))))

(** val fadd_c :
    int -> (qvar -> int) -> ((qvar * int) -> var) -> benv -> flag -> cstore
    -> var -> var -> int -> estore -> cfac -> cfac -> (((pexp
    option * int) * cstore) * estore) value option **)

let fadd_c size smap vmap bv f r temp stack sn es x y =
  bind (type_factor bv FixedP x) (fun t1 ->
    bind (type_factor bv FixedP y) (fun t2 ->
      match par_find_var_check smap bv size r x with
      | Some v ->
        (match v with
         | Value vx ->
           if (&&) (aty_eq (fst t1) Q) (aty_eq (fst t2) C)
           then bind (par_eval_cfac_check smap bv size r FixedP y)
                  (fun t2v ->
                  match t2v with
                  | Value t2v' ->
                    bind (Store.find vx es) (fun exps -> Some (Value ((((Some
                      (fadd_circuit_left size f vmap vx t2v' stack temp sn)),
                      sn), r),
                      (Store.add vx
                        ((fadd_circuit_left size f vmap vx t2v' stack temp sn) :: exps)
                        es))))
                  | Error -> Some Error)
           else if (&&) (aty_eq (fst t1) Q) (aty_eq (fst t2) Q)
                then bind (par_find_var_check smap bv size r y) (fun vyv ->
                       match vyv with
                       | Value vy ->
                         bind (Store.find vx es) (fun exps -> Some (Value
                           ((((Some
                           (fadd_circuit_two size f vmap vx vy stack sn)),
                           sn), r),
                           (Store.add vx
                             ((fadd_circuit_two size f vmap vx vy stack sn) :: exps)
                             es))))
                       | Error -> Some Error)
                else None
         | Error -> Some Error)
      | None -> None))

(** val fsub_circuit_two :
    int -> flag -> ((qvar * int) -> var) -> (qvar * int) -> (qvar * int) ->
    var -> int -> pexp **)

let fsub_circuit_two size f vmap x y stack sn =
  if flag_eq f Classic
  then Exp (Seq ((Seq ((Seq ((Rev (vmap x)), (Rev (vmap y)))),
         (subtractor01 size (vmap x) (vmap y) (stack, (Pervasives.succ sn))))),
         (inv_exp (Seq ((Rev (vmap x)), (Rev (vmap y)))))))
  else PSeq ((PSeq ((Exp (Seq ((Rev (vmap x)), (Rev (vmap y))))),
         (rz_full_sub_form (vmap x) size (vmap y)))),
         (inv_pexp (Exp (Seq ((Rev (vmap x)), (Rev (vmap y)))))))

(** val fsub_circuit_left :
    int -> flag -> ((qvar * int) -> var) -> (qvar * int) -> (int -> bool) ->
    var -> var -> int -> pexp **)

let fsub_circuit_left size f vmap x y stack temp sn =
  if flag_eq f Classic
  then Exp (Seq ((Seq ((Seq ((Seq ((Seq ((init_v size temp y), (Rev
         (vmap x)))), (Rev temp))),
         (subtractor01 size (vmap x) temp (stack, (Pervasives.succ sn))))),
         (inv_exp (Seq ((Rev (vmap x)), (Rev temp)))))),
         (init_v size temp y)))
  else PSeq ((PSeq ((Exp (Rev (vmap x))),
         (rz_sub_right (vmap x) size (fbrev size y)))),
         (inv_pexp (Exp (Rev (vmap x)))))

(** val fsub_c :
    int -> (qvar -> int) -> ((qvar * int) -> var) -> benv -> flag -> cstore
    -> var -> var -> int -> estore -> cfac -> cfac -> (((pexp
    option * int) * cstore) * estore) value option **)

let fsub_c size smap vmap bv f r temp stack sn es x y =
  bind (type_factor bv FixedP x) (fun t1 ->
    bind (type_factor bv FixedP y) (fun t2 ->
      match par_find_var_check smap bv size r x with
      | Some v ->
        (match v with
         | Value vx ->
           if (&&) (aty_eq (fst t1) Q) (aty_eq (fst t2) C)
           then bind (par_eval_cfac_check smap bv size r FixedP y)
                  (fun t2v ->
                  match t2v with
                  | Value t2v' ->
                    bind (Store.find vx es) (fun exps -> Some (Value ((((Some
                      (fsub_circuit_left size f vmap vx t2v' stack temp sn)),
                      sn), r),
                      (Store.add vx
                        ((fsub_circuit_left size f vmap vx t2v' stack temp sn) :: exps)
                        es))))
                  | Error -> Some Error)
           else if (&&) (aty_eq (fst t1) Q) (aty_eq (fst t2) Q)
                then bind (par_find_var_check smap bv size r y) (fun vyv ->
                       match vyv with
                       | Value vy ->
                         bind (Store.find vx es) (fun exps -> Some (Value
                           ((((Some
                           (fsub_circuit_two size f vmap vx vy stack sn)),
                           sn), r),
                           (Store.add vx
                             ((fsub_circuit_two size f vmap vx vy stack sn) :: exps)
                             es))))
                       | Error -> Some Error)
                else None
         | Error -> Some Error)
      | None -> None))

(** val nmul_circuit_two :
    int -> flag -> ((qvar * int) -> var) -> (qvar * int) -> (qvar * int) ->
    (qvar * int) -> var -> int -> pexp **)

let nmul_circuit_two size f vmap x y z stack sn =
  if flag_eq f Classic
  then cl_full_mult size (vmap y) (vmap z) (vmap x) (stack, sn)
  else nat_full_mult size (vmap y) (vmap z) (vmap x)

(** val nmul_circuit_one :
    int -> flag -> ((qvar * int) -> var) -> (qvar * int) -> (qvar * int) ->
    (int -> bool) -> var -> int -> pexp **)

let nmul_circuit_one size f vmap x y z stack sn =
  if flag_eq f Classic
  then cl_nat_mult size (vmap y) (vmap x) (stack, sn) z
  else nat_mult size (vmap y) (vmap x) z

(** val nqmul_c :
    int -> (qvar -> int) -> ((qvar * int) -> var) -> benv -> flag -> cstore
    -> var -> var -> int -> estore -> cfac -> cfac -> cfac -> (((pexp
    option * int) * cstore) * estore) value option **)

let nqmul_c size smap vmap bv f r _ stack sn es x y z =
  bind (type_factor bv Nat x) (fun _ ->
    bind (type_factor bv Nat y) (fun t2 ->
      bind (type_factor bv Nat z) (fun t3 ->
        bind (par_find_var bv size r x) (fun vx ->
          if (&&) (aty_eq (fst t2) Q) (aty_eq (fst t3) Q)
          then bind (par_find_var_check smap bv size r y) (fun vyv ->
                 bind (par_find_var_check smap bv size r z) (fun vzv ->
                   match vyv with
                   | Value vy ->
                     (match vzv with
                      | Value vz ->
                        bind (Store.find vx es) (fun exps -> Some (Value
                          ((((Some
                          (nmul_circuit_two size f vmap vy vz vx stack sn)),
                          sn), r),
                          (Store.add vx
                            ((nmul_circuit_two size f vmap vy vz vx stack sn) :: exps)
                            es))))
                      | Error -> Some Error)
                   | Error -> Some Error))
          else if (&&) (aty_eq (fst t2) Q) (aty_eq (fst t3) C)
               then bind (par_find_var_check smap bv size r y) (fun vyv ->
                      bind (par_eval_cfac_check smap bv size r Nat z)
                        (fun vzv ->
                        match vyv with
                        | Value vy ->
                          (match vzv with
                           | Value tzv ->
                             bind (Store.find vx es) (fun exps -> Some (Value
                               ((((Some
                               (nmul_circuit_one size f vmap vx vy tzv stack
                                 sn)), sn), r),
                               (Store.add vx
                                 ((nmul_circuit_one size f vmap vx vy tzv
                                    stack sn) :: exps) es))))
                           | Error -> Some Error)
                        | Error -> Some Error))
               else if (&&) (aty_eq (fst t2) C) (aty_eq (fst t3) Q)
                    then bind (par_find_var_check smap bv size r z)
                           (fun vzv ->
                           bind (par_eval_cfac_check smap bv size r Nat y)
                             (fun vyv ->
                             match vzv with
                             | Value vz ->
                               (match vyv with
                                | Value tyv ->
                                  bind (Store.find vx es) (fun exps -> Some
                                    (Value ((((Some
                                    (nmul_circuit_one size f vmap vx vz tyv
                                      stack sn)), sn), r),
                                    (Store.add vx
                                      ((nmul_circuit_one size f vmap vx vz
                                         tyv stack sn) :: exps) es))))
                                | Error -> Some Error)
                             | Error -> Some Error))
                    else bind (par_eval_cfac_check smap bv size r Nat y)
                           (fun vyv ->
                           bind (par_eval_cfac_check smap bv size r Nat z)
                             (fun vzv ->
                             match vyv with
                             | Value tyv ->
                               (match vzv with
                                | Value tzv ->
                                  bind (Store.find vx es) (fun exps -> Some
                                    (Value ((((Some (Exp
                                    (init_v size (vmap vx)
                                      (nat2fb
                                        (PeanoNat.Nat.modulo
                                          (mul (a_nat2fb tyv size)
                                            (a_nat2fb tzv size))
                                          (PeanoNat.Nat.pow (Pervasives.succ
                                            (Pervasives.succ 0)) size)))))),
                                    sn), r),
                                    (Store.add vx ((Exp
                                      (init_v size (vmap vx)
                                        (nat2fb
                                          (PeanoNat.Nat.modulo
                                            (mul (a_nat2fb tyv size)
                                              (a_nat2fb tzv size))
                                            (PeanoNat.Nat.pow
                                              (Pervasives.succ
                                              (Pervasives.succ 0)) size))))) :: exps)
                                      es))))
                                | Error -> Some Error)
                             | Error -> Some Error))))))

(** val fmul_circuit_two :
    int -> flag -> ((qvar * int) -> var) -> (qvar * int) -> (qvar * int) ->
    (qvar * int) -> var -> var -> int -> pexp **)

let fmul_circuit_two size f vmap x y z temp stack sn =
  if flag_eq f Classic
  then PSeq ((PSeq ((Exp (Seq ((Seq ((Rev (vmap y)), (Rev (vmap z)))), (Rev
         (vmap x))))),
         (clf_full_mult size (vmap y) (vmap z) (vmap x) temp (stack, sn)))),
         (inv_pexp (Exp (Seq ((Seq ((Rev (vmap y)), (Rev (vmap z)))), (Rev
           (vmap x)))))))
  else PSeq ((PSeq ((Exp (Seq ((Seq ((Rev (vmap y)), (Rev (vmap z)))), (Rev
         (vmap x))))),
         (flt_full_mult size (vmap y) (vmap z) (vmap x) temp))),
         (inv_pexp (Exp (Seq ((Seq ((Rev (vmap y)), (Rev (vmap z)))), (Rev
           (vmap x)))))))

(** val fmul_circuit_one :
    int -> flag -> ((qvar * int) -> var) -> (qvar * int) -> (qvar * int) ->
    (int -> bool) -> var -> var -> int -> pexp **)

let fmul_circuit_one size f vmap x y z stack temp sn =
  if flag_eq f Classic
  then Exp (cl_flt_mult size (vmap y) (vmap x) temp (stack, sn) z)
  else flt_mult size (vmap y) (vmap x) z

(** val fmul_c :
    int -> (qvar -> int) -> ((qvar * int) -> var) -> benv -> flag -> cstore
    -> var -> var -> int -> estore -> cfac -> cfac -> cfac -> (((pexp
    option * int) * cstore) * estore) value option **)

let fmul_c size smap vmap bv f r temp stack sn es x y z =
  bind (type_factor bv FixedP x) (fun _ ->
    bind (type_factor bv FixedP y) (fun t2 ->
      bind (type_factor bv FixedP z) (fun t3 ->
        bind (par_find_var bv size r x) (fun vx ->
          if (&&) (aty_eq (fst t2) Q) (aty_eq (fst t3) Q)
          then bind (par_find_var_check smap bv size r y) (fun vyv ->
                 bind (par_find_var_check smap bv size r z) (fun vzv ->
                   match vyv with
                   | Value vy ->
                     (match vzv with
                      | Value vz ->
                        bind (Store.find vx es) (fun exps -> Some (Value
                          ((((Some
                          (fmul_circuit_two size f vmap vy vz vx temp stack
                            sn)), sn), r),
                          (Store.add vx
                            ((fmul_circuit_two size f vmap vy vz vx temp
                               stack sn) :: exps) es))))
                      | Error -> Some Error)
                   | Error -> Some Error))
          else if (&&) (aty_eq (fst t2) Q) (aty_eq (fst t3) C)
               then bind (par_find_var_check smap bv size r y) (fun vyv ->
                      bind (par_eval_cfac_check smap bv size r FixedP z)
                        (fun vzv ->
                        match vyv with
                        | Value vy ->
                          (match vzv with
                           | Value tzv ->
                             bind (Store.find vx es) (fun exps -> Some (Value
                               ((((Some
                               (fmul_circuit_one size f vmap vx vy tzv stack
                                 temp sn)), sn), r),
                               (Store.add vx
                                 ((fmul_circuit_one size f vmap vx vy tzv
                                    stack temp sn) :: exps) es))))
                           | Error -> Some Error)
                        | Error -> Some Error))
               else if (&&) (aty_eq (fst t2) C) (aty_eq (fst t3) Q)
                    then bind (par_find_var_check smap bv size r z)
                           (fun vzv ->
                           bind (par_eval_cfac_check smap bv size r FixedP y)
                             (fun vyv ->
                             match vzv with
                             | Value vz ->
                               (match vyv with
                                | Value tyv ->
                                  bind (Store.find vx es) (fun exps -> Some
                                    (Value ((((Some
                                    (fmul_circuit_one size f vmap vx vz tyv
                                      stack temp sn)), sn), r),
                                    (Store.add vx
                                      ((fmul_circuit_one size f vmap vx vz
                                         tyv stack temp sn) :: exps) es))))
                                | Error -> Some Error)
                             | Error -> Some Error))
                    else bind (par_eval_cfac_check smap bv size r FixedP y)
                           (fun vyv ->
                           bind (par_eval_cfac_check smap bv size r FixedP z)
                             (fun vzv ->
                             match vyv with
                             | Value tyv ->
                               (match vzv with
                                | Value tzv ->
                                  bind (Store.find vx es) (fun exps -> Some
                                    (Value ((((Some (Exp
                                    (init_v size (vmap vx)
                                      (nat2fb
                                        (PeanoNat.Nat.modulo
                                          (mul (a_nat2fb tyv size)
                                            (a_nat2fb tzv size))
                                          (PeanoNat.Nat.pow (Pervasives.succ
                                            (Pervasives.succ 0)) size)))))),
                                    sn), r),
                                    (Store.add vx ((Exp
                                      (init_v size (vmap vx)
                                        (nat2fb
                                          (PeanoNat.Nat.modulo
                                            (mul (a_nat2fb tyv size)
                                              (a_nat2fb tzv size))
                                            (PeanoNat.Nat.pow
                                              (Pervasives.succ
                                              (Pervasives.succ 0)) size))))) :: exps)
                                      es))))
                                | Error -> Some Error)
                             | Error -> Some Error))))))

(** val bin_xor_q : int -> var -> var -> exp **)

let rec bin_xor_q n x y =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (x, 0))
    (fun m -> Seq ((coq_CNOT (x, m) (y, m)), (bin_xor_q m x y)))
    n

(** val bin_xor_c : int -> var -> (int -> bool) -> exp **)

let rec bin_xor_c n x y =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (x, 0))
    (fun m ->
    if y m then Seq ((X (x, m)), (bin_xor_c m x y)) else bin_xor_c m x y)
    n

(** val init_c :
    int -> (qvar -> int) -> ((qvar * int) -> var) -> benv -> cstore -> int ->
    estore -> cfac -> cfac -> (((pexp option * int) * cstore) * estore) value
    option **)

let init_c size smap vmap bv r sn es x y =
  bind (par_find_var_check smap bv size r x) (fun vxv ->
    match vxv with
    | Value vx ->
      bind (BEnv.find (fst vx) bv) (fun t0 ->
        if is_q t0
        then bind (type_factor bv (get_ct t0) y) (fun t2 ->
               if aty_eq (fst t2) Q
               then bind (par_find_var_check smap bv size r y) (fun vyv ->
                      match vyv with
                      | Value vy ->
                        bind (Store.find vx es) (fun exps -> Some (Value
                          ((((Some (Exp
                          (bin_xor_q (get_size size (get_ct t0)) (vmap vy)
                            (vmap vx)))), sn), r),
                          (Store.add vx ((Exp
                            (bin_xor_q (get_size size (get_ct t0)) (vmap vy)
                              (vmap vx))) :: exps) es))))
                      | Error -> Some Error)
               else bind (par_eval_cfac_check smap bv size r (snd t2) y)
                      (fun t2v ->
                      match t2v with
                      | Value t2v' ->
                        bind (Store.find vx es) (fun exps -> Some (Value
                          ((((Some (Exp
                          (bin_xor_c (get_size size (get_ct t0)) (vmap vx)
                            t2v'))), sn), r),
                          (Store.add vx ((Exp
                            (bin_xor_c (get_size size (get_ct t0)) (vmap vx)
                              t2v')) :: exps) es))))
                      | Error -> Some Error))
        else None)
    | Error -> Some Error)

(** val div_c :
    int -> (qvar -> int) -> ((qvar * int) -> var) -> benv -> flag -> cstore
    -> var -> var -> var -> int -> estore -> cfac -> cfac -> (int -> bool) ->
    (((pexp option * int) * cstore) * estore) value option **)

let div_c size smap vmap bv fl r temp temp1 stack sn es x y z =
  bind (par_find_var_check smap bv size r x) (fun vxv ->
    match vxv with
    | Value vx ->
      bind (BEnv.find (fst vx) bv) (fun t0 ->
        if is_q t0
        then bind (type_factor bv (get_ct t0) y) (fun t2 ->
               if aty_eq (fst t2) Q
               then bind (par_find_var_check smap bv size r y) (fun vyv ->
                      match vyv with
                      | Value vy ->
                        bind (Store.find vx es) (fun exps ->
                          if flag_eq fl QFTA
                          then Some (Value ((((Some
                                 (rz_div size (vmap vy) (vmap vx) temp
                                   (a_nat2fb z size))), sn), r),
                                 (Store.add vx
                                   ((rz_div size (vmap vy) (vmap vx) temp
                                      (a_nat2fb z size)) :: exps) es)))
                          else Some (Value ((((Some (Exp
                                 (cl_div size (vmap vy) (vmap vx) temp temp1
                                   (stack, sn) (a_nat2fb z size)))), sn), r),
                                 (Store.add vx ((Exp
                                   (cl_div size (vmap vy) (vmap vx) temp
                                     temp1 (stack, sn) (a_nat2fb z size))) :: exps)
                                   es))))
                      | Error -> Some Error)
               else bind (par_eval_cfac_check smap bv size r (snd t2) y)
                      (fun t2v ->
                      match t2v with
                      | Value t2v' ->
                        bind (Store.find vx es) (fun exps -> Some (Value
                          ((((Some (Exp
                          (bin_xor_c (get_size size (get_ct t0)) (vmap vx)
                            t2v'))), sn), r),
                          (Store.add vx ((Exp
                            (bin_xor_c (get_size size (get_ct t0)) (vmap vx)
                              t2v')) :: exps) es))))
                      | Error -> Some Error))
        else bind (par_eval_cfac_check smap bv size r Nat y) (fun t2v ->
               match t2v with
               | Value t2v' ->
                 Some (Value (((None, sn),
                   (Store.add vx
                     (nat2fb
                       (PeanoNat.Nat.div (a_nat2fb t2v' size)
                         (a_nat2fb z size))) r)), es))
               | Error -> Some Error))
    | Error -> Some Error)

(** val lrot_c :
    int -> (qvar -> int) -> ((qvar * int) -> var) -> benv -> cstore -> int ->
    estore -> cfac -> (((pexp option * int) * cstore) * pexp list Store.t)
    value option **)

let lrot_c size smap vmap bv r sn es x =
  bind (par_find_var_check smap bv size r x) (fun vxv ->
    match vxv with
    | Value vx ->
      bind (BEnv.find (fst vx) bv) (fun t0 ->
        if is_q t0
        then bind (Store.find vx es) (fun exps -> Some (Value ((((Some (Exp
               (Rshift (vmap vx)))), sn), r),
               (Store.add vx ((Exp (Rshift (vmap vx))) :: exps) es))))
        else bind (Store.find vx r) (fun t1v -> Some (Value (((None, sn),
               (Store.add vx (l_rotate t1v (get_size size (get_ct t0))) r)),
               es))))
    | Error -> Some Error)

(** val combine_if :
    var -> int -> pexp -> pexp option -> pexp option -> pexp option **)

let combine_if sv sn p1 e1 e2 =
  match e1 with
  | Some e1' ->
    (match e2 with
     | Some e2' ->
       Some (PSeq ((PSeq ((PSeq (p1, (PCU ((sv, sn), e1')))), (Exp (X (sv,
         sn))))), (PCU ((sv, sn), e2'))))
     | None -> Some (PSeq (p1, (PCU ((sv, sn), e1')))))
  | None ->
    (match e2 with
     | Some e2' ->
       Some (PSeq ((PSeq (p1, (Exp (X (sv, sn))))), (PCU ((sv, sn), e2'))))
     | None -> Some p1)

(** val trans_qexp :
    int -> (qvar -> int) -> ((qvar * int) -> var) -> benv -> flag -> cstore
    -> var -> var -> var -> int -> fmap -> estore -> estore -> qexp ->
    (((pexp option * int) * cstore) * estore) value option **)

let rec trans_qexp size smap vmap bv fl r temp temp1 stack sn fv es bases = function
| Coq_qinv x ->
  bind (par_find_var_check smap bv size r x) (fun vx ->
    match vx with
    | Value vx' ->
      bind (Store.find vx' es) (fun exps ->
        bind ((fun l -> List.nth_opt l 0) exps) (fun exp0 -> Some (Value
          ((((Some (inv_pexp exp0)), sn), r),
          (Store.add vx' (List.tl exps) es)))))
    | Error -> Some Error)
| Coq_call (f, x) ->
  (match lookup_fmap fv f with
   | Some p ->
     let (p0, r') = p in
     let (p1, bv') = p0 in
     let (p2, vmap') = p1 in
     let (p3, smap') = p2 in
     let (u, e') = p3 in
     bind (par_find_var_check smap' bv' size r' u) (fun vuv ->
       match vuv with
       | Value vu ->
         bind (BEnv.find (fst vu) bv') (fun t0 ->
           bind (par_find_var_check smap bv size r x) (fun vxv ->
             match vxv with
             | Value vx ->
               bind (BEnv.find (fst vx) bv) (fun t' ->
                 if (&&) (is_q t') (is_q t0)
                 then bind (Store.find vx es) (fun exps -> Some (Value
                        ((((Some (PSeq ((PSeq (e', (Exp
                        (copyto (vmap' vu) (vmap vx)
                          (get_size size (get_ct t0)))))), (inv_pexp e')))),
                        sn), r),
                        (Store.add vx ((PSeq ((PSeq (e', (Exp
                          (copyto (vmap' vu) (vmap vx)
                            (get_size size (get_ct t0)))))),
                          (inv_pexp e'))) :: exps) es))))
                 else if (&&) (is_q t') (is_c t0)
                      then bind (Store.find vx es) (fun exps ->
                             bind (Store.find vu r') (fun uv -> Some (Value
                               ((((Some (Exp
                               (init_v (get_size size (get_ct t0)) (vmap vx)
                                 uv))), sn), r),
                               (Store.add vx ((Exp
                                 (init_v (get_size size (get_ct t0))
                                   (vmap vx) uv)) :: exps) es)))))
                      else bind (Store.find vu r') (fun _ ->
                             bind (Store.find vx r) (fun xv -> Some (Value
                               (((None, sn), (Store.add vx xv r)), es)))))
             | Error -> Some Error))
       | Error -> Some Error)
   | None -> None)
| Coq_qif (ce, e1, e2) ->
  bind (compile_cexp size smap vmap bv fl r temp stack sn ce) (fun ce_val ->
    match ce_val with
    | Value x ->
      let (p, o) = x in
      let (cir, sn') = p in
      (match cir with
       | Some cir0 ->
         (match o with
          | Some b ->
            if b
            then trans_qexp size smap vmap bv fl r temp temp1 stack sn' fv
                   bases bases e1
            else trans_qexp size smap vmap bv fl r temp temp1 stack sn' fv
                   bases bases e2
          | None ->
            bind
              (trans_qexp size smap vmap bv fl r temp temp1 stack sn' fv
                bases bases e1) (fun e1_val ->
              match e1_val with
              | Value x0 ->
                let (p0, _) = x0 in
                let (p1, r1) = p0 in
                let (e1_cir, sn1) = p1 in
                bind
                  (trans_qexp size smap vmap bv fl r1 temp temp1 stack sn1 fv
                    bases bases e2) (fun e2_val ->
                  match e2_val with
                  | Value x1 ->
                    let (p2, _) = x1 in
                    let (p3, r2) = p2 in
                    let (e2_cir, sn2) = p3 in
                    Some (Value ((((combine_if stack sn cir0 e1_cir e2_cir),
                    sn2), r2), es))
                  | Error -> Some Error)
              | Error -> Some Error))
       | None ->
         (match o with
          | Some b ->
            if b
            then trans_qexp size smap vmap bv fl r temp temp1 stack sn' fv
                   bases bases e1
            else trans_qexp size smap vmap bv fl r temp temp1 stack sn' fv
                   bases bases e2
          | None -> Some Error))
    | Error -> Some Error)
| Coq_qfor (x, n, e') ->
  bind (par_eval_cfac_check smap bv size r Nat n) (fun t2v' ->
    match t2v' with
    | Value t2v ->
      let rec trans_while r0 sn0 i =
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> Some (Value (((None, sn0), r0), es)))
          (fun m ->
          bind
            (trans_qexp size smap vmap bv fl r0 temp temp1 stack sn0 fv bases
              bases e') (fun re ->
            match re with
            | Value x0 ->
              let (p, _) = x0 in
              let (p0, r') = p in
              let (cir, sn') = p0 in
              bind (trans_while r' sn' m) (fun re' ->
                match re' with
                | Value x1 ->
                  let (p1, _) = x1 in
                  let (p2, r'') = p1 in
                  let (cir', sn'') = p2 in
                  Some (Value ((((combine_c cir cir'), sn''), r''), bases))
                | Error -> Some Error)
            | Error -> Some Error))
          i
      in trans_while (Store.add ((L x), 0) (nat2fb 0) r) sn
           (a_nat2fb t2v size)
    | Error -> Some Error)
| Coq_qseq (e1, e2) ->
  (match trans_qexp size smap vmap bv fl r temp temp1 stack sn fv es bases e1 with
   | Some v ->
     (match v with
      | Value x ->
        let (p, es1) = x in
        let (p0, store1) = p in
        let (e1', sn1) = p0 in
        (match trans_qexp size smap vmap bv fl store1 temp temp1 stack sn1 fv
                 es1 bases e2 with
         | Some v0 ->
           (match v0 with
            | Value x0 ->
              let (p1, es2) = x0 in
              let (p2, store2) = p1 in
              let (e2', sn2) = p2 in
              Some (Value ((((combine_seq e1' e2'), sn2), store2), es2))
            | Error -> Some Error)
         | None -> None)
      | Error -> Some Error)
   | None -> None)
| Coq_skip -> Some (Value (((None, sn), r), es))
| Coq_init (x, v) ->
  if negb (qvar_eq bv size r x v)
  then init_c size smap vmap bv r sn es x v
  else Some Error
| Coq_nadd (x, y) ->
  if negb (qvar_eq bv size r x y)
  then nadd_c size smap vmap bv fl r temp stack sn es x y
  else Some Error
| Coq_nsub (x, y) ->
  if negb (qvar_eq bv size r x y)
  then nsub_c size smap vmap bv fl r temp stack sn es x y
  else Some Error
| Coq_nmul (x, y, z) ->
  if (&&) (negb (qvar_eq bv size r x z)) (negb (qvar_eq bv size r y z))
  then nqmul_c size smap vmap bv fl r temp stack sn es x y z
  else Some Error
| Coq_fadd (x, y) ->
  if negb (qvar_eq bv size r x y)
  then fadd_c size smap vmap bv fl r temp stack sn es x y
  else Some Error
| Coq_fsub (x, y) ->
  if negb (qvar_eq bv size r x y)
  then fsub_c size smap vmap bv fl r temp stack sn es x y
  else Some Error
| Coq_fmul (x, y, z) ->
  if (&&) (negb (qvar_eq bv size r x z)) (negb (qvar_eq bv size r y z))
  then fmul_c size smap vmap bv fl r temp stack sn es x y z
  else Some Error
| Coq_qxor (x, y) ->
  if negb (qvar_eq bv size r x y)
  then init_c size smap vmap bv r sn es x y
  else Some Error
| Coq_slrot x -> lrot_c size smap vmap bv r sn es x
| Coq_ndiv (x, y, n) ->
  bind (par_eval_cfac_check smap bv size r Nat n) (fun t2v ->
    match t2v with
    | Value t2v' ->
      div_c size smap vmap bv fl r temp temp1 stack sn es x y t2v'
    | Error -> Some Error)
| Coq_nmod (x, y, n) ->
  bind (par_eval_cfac_check smap bv size r Nat y) (fun t2v ->
    bind (par_eval_cfac_check smap bv size r Nat n) (fun t3v ->
      bind (par_find_var_check smap bv size r x) (fun vx ->
        match t2v with
        | Value t2v' ->
          (match t3v with
           | Value t3v' ->
             (match vx with
              | Value vx' ->
                Some (Value (((None, sn),
                  (Store.add vx'
                    (nat2fb
                      (PeanoNat.Nat.modulo (a_nat2fb t2v' size)
                        (a_nat2fb t3v' size))) r)), es))
              | Error -> Some Error)
           | Error -> Some Error)
        | Error -> Some Error)))
| Coq_nfac (x, n) ->
  bind (par_eval_cfac_check smap bv size r Nat n) (fun t3v ->
    bind (par_find_var_check smap bv size r x) (fun vx ->
      match t3v with
      | Value t3v' ->
        (match vx with
         | Value vx' ->
           Some (Value (((None, sn),
             (Store.add vx' (nat2fb (fact (a_nat2fb t3v' size))) r)), es))
         | Error -> Some Error)
      | Error -> Some Error))
| Coq_fdiv (x, n) ->
  bind (par_eval_cfac_check smap bv size r Nat n) (fun t3v ->
    bind (par_find_var_check smap bv size r x) (fun vx ->
      match t3v with
      | Value t3v' ->
        (match vx with
         | Value vx' ->
           bind (Store.find vx' r) (fun txv -> Some (Value (((None, sn),
             (Store.add vx'
               (fbrev size
                 (nat2fb
                   (PeanoNat.Nat.div (a_nat2fb (fbrev size txv) size)
                     (a_nat2fb t3v' size)))) r)), es)))
         | Error -> Some Error)
      | Error -> Some Error))
| Coq_ncsub (x, y, n) ->
  bind (par_eval_cfac_check smap bv size r Nat y) (fun t2v ->
    bind (par_eval_cfac_check smap bv size r Nat n) (fun t3v ->
      bind (par_find_var_check smap bv size r x) (fun vx ->
        match t2v with
        | Value t2v' ->
          (match t3v with
           | Value t3v' ->
             (match vx with
              | Value vx' ->
                Some (Value (((None, sn),
                  (Store.add vx'
                    (nat2fb
                      (PeanoNat.Nat.modulo
                        (sub (a_nat2fb t2v' size) (a_nat2fb t3v' size))
                        (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ
                          0)) size))) r)), es))
              | Error -> Some Error)
           | Error -> Some Error)
        | Error -> Some Error)))
| Coq_ncadd (x, y, n) ->
  bind (par_eval_cfac_check smap bv size r Nat y) (fun t2v ->
    bind (par_eval_cfac_check smap bv size r Nat n) (fun t3v ->
      bind (par_find_var_check smap bv size r x) (fun vx ->
        match t2v with
        | Value t2v' ->
          (match t3v with
           | Value t3v' ->
             (match vx with
              | Value vx' ->
                Some (Value (((None, sn),
                  (Store.add vx'
                    (nat2fb
                      (PeanoNat.Nat.modulo
                        (add (a_nat2fb t2v' size) (a_nat2fb t3v' size))
                        (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ
                          0)) size))) r)), es))
              | Error -> Some Error)
           | Error -> Some Error)
        | Error -> Some Error)))
| Coq_fcsub (x, y, n) ->
  bind (par_eval_cfac_check smap bv size r FixedP y) (fun t2v ->
    bind (par_eval_cfac_check smap bv size r FixedP n) (fun t3v ->
      bind (par_find_var_check smap bv size r x) (fun vx ->
        match t2v with
        | Value t2v' ->
          (match t3v with
           | Value t3v' ->
             (match vx with
              | Value vx' ->
                Some (Value (((None, sn),
                  (Store.add vx'
                    (fbrev size
                      (nat2fb
                        (PeanoNat.Nat.modulo
                          (sub (a_nat2fb (fbrev size t2v') size)
                            (a_nat2fb (fbrev size t3v') size))
                          (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ
                            0)) size)))) r)), es))
              | Error -> Some Error)
           | Error -> Some Error)
        | Error -> Some Error)))
| Coq_fcadd (x, y, n) ->
  bind (par_eval_cfac_check smap bv size r FixedP y) (fun t2v ->
    bind (par_eval_cfac_check smap bv size r FixedP n) (fun t3v ->
      bind (par_find_var_check smap bv size r x) (fun vx ->
        match t2v with
        | Value t2v' ->
          (match t3v with
           | Value t3v' ->
             (match vx with
              | Value vx' ->
                Some (Value (((None, sn),
                  (Store.add vx'
                    (fbrev size
                      (nat2fb
                        (PeanoNat.Nat.modulo
                          (add (a_nat2fb (fbrev size t2v') size)
                            (a_nat2fb (fbrev size t3v') size))
                          (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ
                            0)) size)))) r)), es))
              | Error -> Some Error)
           | Error -> Some Error)
        | Error -> Some Error)))
| Coq_ncmul (x, y, n) ->
  bind (par_eval_cfac_check smap bv size r Nat y) (fun t2v ->
    bind (par_eval_cfac_check smap bv size r Nat n) (fun t3v ->
      bind (par_find_var_check smap bv size r x) (fun vx ->
        match t2v with
        | Value t2v' ->
          (match t3v with
           | Value t3v' ->
             (match vx with
              | Value vx' ->
                Some (Value (((None, sn),
                  (Store.add vx'
                    (nat2fb
                      (PeanoNat.Nat.modulo
                        (mul (a_nat2fb t2v' size) (a_nat2fb t3v' size))
                        (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ
                          0)) size))) r)), es))
              | Error -> Some Error)
           | Error -> Some Error)
        | Error -> Some Error)))
| Coq_fndiv (x, y, n) ->
  bind (par_eval_cfac_check smap bv size r Nat y) (fun t2v ->
    bind (par_eval_cfac_check smap bv size r Nat n) (fun t3v ->
      bind (par_find_var_check smap bv size r x) (fun vx ->
        match t2v with
        | Value t2v' ->
          (match t3v with
           | Value t3v' ->
             (match vx with
              | Value vx' ->
                Some (Value (((None, sn),
                  (Store.add vx'
                    (fbrev size
                      (nat2fb
                        (PeanoNat.Nat.modulo
                          (PeanoNat.Nat.div
                            (mul (a_nat2fb t2v' size)
                              (PeanoNat.Nat.pow (Pervasives.succ
                                (Pervasives.succ 0)) size))
                            (a_nat2fb t3v' size))
                          (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ
                            0)) size)))) r)), es))
              | Error -> Some Error)
           | Error -> Some Error)
        | Error -> Some Error)))

(** val init_cstore_n : cstore -> qvar -> int -> cstore **)

let rec init_cstore_n r x n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> r)
    (fun m -> Store.add (x, m) (nat2fb 0) (init_cstore_n r x m))
    n

(** val init_cstore : cstore -> (typ * var) list -> cstore **)

let rec init_cstore r = function
| [] -> r
| p :: xl ->
  let (t0, x) = p in init_cstore (init_cstore_n r (L x) (get_type_num t0)) xl

(** val init_estore_n : estore -> qvar -> int -> estore **)

let rec init_estore_n es x n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> es)
    (fun m -> Store.add (x, m) [] (init_estore_n es x m))
    n

(** val init_estore : estore -> (typ * var) list -> estore **)

let rec init_estore r = function
| [] -> r
| p :: xl ->
  let (t0, x) = p in init_estore (init_estore_n r (L x) (get_type_num t0)) xl
