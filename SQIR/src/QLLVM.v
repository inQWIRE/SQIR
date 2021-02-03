Require Import VectorStates UnitaryOps Coq.btauto.Btauto Strings.String.
Require Import Arith.
Require Import ZArith.
Require Import ZArith.BinIntDef.
(* The syntax of IR Language for classical circuit. *)
(*There are two kind of variables. type var is for local/global variables for integers,
     while fvar is for function names.*)
Definition var := nat.

Definition fvar := nat.

(*  a type for const values that cannot appear in a quantum circuit,
   and register values that can appear in a guantum circuit. *)
Inductive atype := C : nat -> atype | J : nat -> atype.

Definition ty_eq  (t1 t2:atype) : bool := 
   match t1 with C n => match t2 with C m => n =? m
                            | _ => false
                        end
               | J n => match t2 with J m => n =? m
                           | _ => false
                        end
   end.

Definition subtype (t1 t2: atype) : bool :=
   if ty_eq t1 t2 then true else
           (match t1 with C n => match t2 with J m => n =? m
                                             | _ => false
                                 end
                         | _ => false
            end).

Inductive factor := Var (v:var)
                 | Num (n:nat) (v:Z). (* n represents the C n type. *)

Inductive exp := eplus (x : factor) (y: factor)
      | eminus (x:factor) (y:factor)
      | emult (x:factor) (y:factor)
      | ediv (x:factor) (y:factor)
      | emod (x:factor) (y:factor)
      | efac (y:factor)
      | epow (x:factor) (y:factor)
      | esqrt (x:factor)
      | esin (x:factor)
      | ecos (x:factor)
      | ecall (f:fvar) (vs: list factor)
      | sigma (c1:factor) (c2:factor) (f:fvar) (vs: list factor).

Inductive inst := assign (x:var) (e:exp).

(* syntax for functions. *)
Definition ty_var : Type := (atype * var).


(* a function is a type, a function name, a list of type_with_var, a list of instruction, and a return variable.
   The QLLVM function is not the RCIR+ function. A RCIR+ function should maps to an instruction in QLLVM. *)
Inductive efun := elet (t:atype) (f:fvar) (ns : list ty_var) (ins : list inst) (ret : var).

Inductive setting :=setFixedPointNum (n: nat) | setBitLength (n:nat) | efixed (x: list var) | setUncomputeStrategy (x: string).

Inductive top := Prog (ss : list setting) (fs : list efun).


(* Define the well-formedness of exp. It is SSA + variable-dominance, as well as type match. *)
(* The following relation defines the SSA + variable dominance for expressions and instructions. *)
Inductive ssa_factor : list var -> factor -> Prop :=
   | ssa_jfactor : forall r x, In x r -> ssa_factor r (Var x)
   | ssa_cfactor_num : forall r n x, ssa_factor r (Num n x).

Inductive ssa_factors : list var -> list factor -> Prop :=
   | ssa_factors_empty : forall r, ssa_factors r []
   | ssa_factors_many : forall r x xs, ssa_factors r xs -> ssa_factor r x -> ssa_factors r (x::xs).

Inductive ssa_exp : list var -> exp -> Prop := 
  | eplus_ssa : forall r x y , ssa_factor r x -> ssa_factor r y -> ssa_exp r (eplus x y)
  | eminus_ssa : forall r x y , ssa_factor r x -> ssa_factor r y -> ssa_exp r (eminus x y)
  | emult_ssa : forall r x y , ssa_factor r x -> ssa_factor r y -> ssa_exp r (emult x y)
  | ediv_ssa : forall r x y , ssa_factor r x -> ssa_factor r y -> ssa_exp r (ediv x y)
  | emod_ssa : forall r x y , ssa_factor r x -> ssa_factor r y -> ssa_exp r (emod x y)
  | efac_ssa : forall r x, ssa_factor r x -> ssa_exp r (efac x)
  | epow_ssa : forall r x y, ssa_factor r x -> ssa_factor r y -> ssa_exp r (epow x y)
  | esqrt_ssa : forall r x, ssa_factor r x -> ssa_exp r (esqrt x)
  | esin_ssa : forall r x, ssa_factor r x -> ssa_exp r (esin x)
  | ecos_ssa : forall r x, ssa_factor r x -> ssa_exp r (ecos x)
  | ecall_ssa : forall r f xs, ssa_factors r xs -> ssa_exp r (ecall f xs)
  | sigma_ssa : forall r c1 c2 f xs,ssa_factor r c1 -> ssa_factor r c2
                     -> ssa_factors r xs -> ssa_exp r (sigma c1 c2 f xs).

Inductive ssa_inst : list var -> inst -> list var -> Prop :=
   | ssa_inst_assign : forall r x e, ssa_exp r e -> ssa_inst r (assign x e) (x::r).

Inductive ssa_insts : list var -> list inst -> list var -> Prop :=
   | ssa_inst_empty : forall r, ssa_insts r [] r
   | ssa_inst_many : forall r i is r' r'', ssa_inst r i r' -> ssa_insts r' is r'' -> ssa_insts r (i::is) r''.

Fixpoint grap_vars (l:list ty_var) : list var :=
   match l with [] => []
              | (x,y)::xs => y::grap_vars xs
   end.

Inductive ssa_efun : list var -> efun -> Prop := 
   | ssa_thefun : forall r r' t f ns ins ret, ssa_insts (r++(grap_vars ns)) ins r'
                     -> In ret r' -> ssa_efun r (elet t f ns ins ret).

Inductive ssa_efuns : list var -> list efun -> Prop :=
   | ssa_efun_empty : forall r, ssa_efuns r []
   | ssa_efun_many : forall r x xs, ssa_efun r x -> ssa_efuns r xs -> ssa_efuns r (x::xs).

Inductive ssa_top : top -> Prop :=
  | ssa_thetop : forall ss fs, ssa_efuns [] fs -> ssa_top (Prog ss fs).


(* The following relation defines the type system for expressions and instructions and functions. *)
Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.

Module Env := FMapList.Make Nat_as_OT.

Definition env := Env.t atype.

Module FEnv := FMapList.Make Nat_as_OT.

Definition fenv := FEnv.t (atype * list atype).

Inductive type_factor : env -> factor -> atype -> Prop :=
     | type_jfactor : forall r t x, Env.MapsTo x t r -> type_factor r (Var x) t
     | type_cfactor_num : forall r n x, type_factor r (Num n x) (C n).


Definition meet_type (t1 t2: atype) : option atype :=
         if subtype t1 t2 then Some t2 else if subtype t2 t1 then Some t1 else None.

Inductive type_factors : env -> list factor -> list atype -> Prop :=
    | type_factor_empty : forall r, type_factors r [] []
    | type_factor_many : forall r x xs t t' ts, type_factor r x t'
                               -> subtype t' t = true -> type_factors r (x::xs) (t::ts).

Inductive type_exp (fm : fenv) : env -> exp -> atype -> Prop := 
  | eplus_type : forall r x y t t1 t2, type_factor r x t1 -> type_factor r y t2 ->
                       meet_type t1 t2 = Some t -> type_exp fm r (eplus x y) t
  | eminus_type : forall r x y t t1 t2, type_factor r x t1 -> type_factor r y t2 ->
                       meet_type t1 t2 = Some t -> type_exp fm r (eminus x y) t
  | emult_type : forall r x y t t1 t2, type_factor r x t1 -> type_factor r y t2 ->
                       meet_type t1 t2 = Some t -> type_exp fm r (emult x y) t
  | ediv_type : forall r x y t t1 t2, type_factor r x t1 -> type_factor r y t2 ->
                       meet_type t1 t2 = Some t -> type_exp fm r (ediv x y) t
  | emod_type : forall r x y t t1 t2, type_factor r x t1 -> type_factor r y t2 ->
                       meet_type t1 t2 = Some t -> type_exp fm r (emod x y) t
  | efac_type : forall r x n, type_factor r x (C n) -> type_exp fm r (efac x) (C n)
  | epow_type : forall r x y t t1 n, type_factor r x t1 -> type_factor r y (C n) ->
                       meet_type t1 (C n) = Some t -> type_exp fm r (epow x y) t
  | esqrt_type : forall r x t, type_factor r x t -> type_exp fm r (esqrt x) t
  | esin_type : forall r x t, type_factor r x t -> type_exp fm r (esin x) t
  | ecos_type : forall r x t, type_factor r x t -> type_exp fm r (ecos x) t
  | ecall_type : forall r f xs t ts, FEnv.MapsTo f (t,ts) fm -> type_factors r xs ts 
          -> type_exp fm r (ecall f xs) t
  | sigma_type : forall r c1 n c2 m f xs t ts, type_factor r c1 (C n) -> type_factor r c2 (C m) ->
                FEnv.MapsTo f (t,ts) fm -> type_factors r xs ts -> type_exp fm r (sigma c1 c2 f xs) t.


Inductive type_inst (fm: fenv) : env -> inst -> env -> Prop :=
   | type_inst_assign : forall r x e t, type_exp fm r e t -> type_inst fm r (assign x e) (Env.add x t r).

Inductive type_insts (fm: fenv) : env -> list inst -> env -> Prop :=
   | type_inst_empty : forall r, type_insts fm r [] r
   | type_inst_many : forall r i is r' r'', type_inst fm r i r' -> type_insts fm r' is r'' -> type_insts fm r (i::is) r''.


Fixpoint gen_env (l : list ty_var) : env :=
  match l with [] => (@Env.empty atype)
            | (x,y)::xs => Env.add y x (gen_env xs)
  end.

Fixpoint grap_types (l:list ty_var) : list atype :=
   match l with [] => []
              | (x,y)::xs => x::grap_types xs
   end.

Inductive type_efun : fenv -> efun -> fenv -> Prop := 
   | type_thefun : forall fm r t t' f ns ins ret, type_insts fm (gen_env ns) ins r
                     -> Env.MapsTo ret t' r -> subtype t' t = true
                     -> type_efun fm (elet t f ns ins ret) (FEnv.add f (t,grap_types ns) fm).

Inductive type_efuns : fenv -> list efun -> fenv -> Prop :=
  | type_efun_empty : forall fm, type_efuns fm [] fm
  | type_efun_many : forall fm fm' fm'' x xs, type_efun fm x fm'
                    -> type_efuns fm' xs fm'' -> type_efuns fm (x::xs) fm''.


Inductive type_top : top -> Prop :=
  | type_thetop : forall ss fs fm, type_efuns (@FEnv.empty (atype * list atype)) fs fm -> type_top (Prog ss fs).



(* The frontend level language. QC. *)
Inductive QC := varC (v:var) | natC (n:nat).

Inductive QE := cconst (c:QC) | plusC (e1:QE) (e2:QE) 
             | minusC (e1:QE) (e2:QE) | multC (e1:QE) (e2:QE)
             | divC (e1:QE) (e2:QE) | modC (e1:QE) (e2:QE)
             | facC (e:QE) 
             | powC (e:QE) (n:QC) 
             | sinC (e:QE) | cosC (e:QE) | sqrtC (e:QE)
             | sigmaC (c1:QC) (c2:QC) (f:var) (v : QE).

Inductive cinst := letin (v:var) (e1:QE) (e2:QE).

Inductive ctop := setFixedPointNumC (n: nat) | setBitLengthC (n:nat) 
              | fixedC (x: list var) | setUncomputeStrategyC (x: string) | ins (cs : list cinst).







