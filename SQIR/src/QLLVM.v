Require Import VectorStates UnitaryOps Coq.btauto.Btauto Strings.String.

(* The syntax of IR Language for classical circuit. *)
Definition var := nat.

Definition qvar := nat.

Inductive const :=
| cvar (x : var)
| cnum (n : nat)
| cplus (c1 : const) (c2 : const)
| cminus (c1 : const) (c2 : const)
| cmult (c1 : const) (c2 : const)
| cdiv (c1 : const) (c2 : const)
| cmod (c1 : const) (c2 : const)
| cfac (c1 : const)
| cpow (c1 : const) (c2: const)
.

Inductive factor := fconst (c:const) | fvar (x : qvar).

Inductive exp := eplus (x : factor) (y: factor)
      | eminus (x:factor) (y:factor)
      | emult (x:factor) (y:factor)
      | ediv (x:factor) (y:factor)
      | emod (x:factor) (y:factor)
      | efac (y:const)
      | epow (x:factor) (y:const)
      | esqrt (x:factor)
      | esin (x:factor)
      | ecos (x:factor)
      | ecall (f:qvar) (vs: list factor)
      | sigma (c1:const) (c2:const) (f:qvar) (vs: list factor).

Inductive inst := assign (x:qvar) (e:exp) | uncompute.

Inductive efun := elet qvar (ns : list var) (qs: list qvar) (ins : list inst) (ret : qvar).

Inductive top := setFixedPointNum (n: const) | setBitLength (n:const) 
              | efixed (x: list var) | setUncomputeStrategy (x: string) | Funs (fs : list efun).
