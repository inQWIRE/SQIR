Require Import VectorStates UnitaryOps Coq.btauto.Btauto RCIR.

Local Open Scope bccom_scope.
Local Open Scope nat_scope.

Definition funbool_push b f : nat -> bool :=
  fun x => match x with
        | O => b
        | S n => f n
        end.

Definition allfalse := fun (_ : nat) => false.

Fixpoint reg_push (x : N) (n : nat) (f : nat -> bool) :=
  match n with
  | 0 => f
  | S n' => match x with
           | 0%N => funbool_push false (reg_push x n' f)
           | Npos xH => funbool_push true (reg_push 0%N n' f)
           | Npos (xO p) => funbool_push false (reg_push (Npos p) n' f)
           | Npos (xI p) => funbool_push true (reg_push (Npos p) n' f)
           end
  end.

Fixpoint pos2fb p : nat -> bool :=
  match p with
  | xH => funbool_push true allfalse
  | xI p' => funbool_push true (pos2fb p')
  | xO p' => funbool_push false (pos2fb p')
  end.

Definition N2fb n : nat -> bool :=
  match n with
  | 0%N => allfalse
  | Npos p => pos2fb p
  end.

Notation "'[' x ']_' n f" := (reg_push (N.of_nat x) n f) (at level 15, n at level 9, right associativity).
Notation "b ` f" := (funbool_push b f) (at level 20, right associativity).

Definition MAJ a b c := bccnot c b ; bccnot c a ; bcccnot a b c.
Definition UMA a b c := bcccnot a b c ; bccnot c a ; bccnot a b.

Fixpoint MAJseq' i n c0 : bccom :=
  match i with
  | 0 => MAJ c0 (2 + n) 2
  | S i' => MAJseq' i' n c0; MAJ (2 + i') (2 + n + i) (2 + i)
  end.
Definition MAJseq n c0 := MAJseq' (n - 1) n c0.

Fixpoint UMAseq' i n c0 : bccom :=
  match i with
  | 0 => UMA c0 (2 + n) 2
  | S i' => UMA (2 + i') (2 + n + i) (2 + i); UMAseq' i' n c0
  end.
Definition UMAseq n c0 := UMAseq' (n - 1) n c0.

Definition adder01 n : bccom := MAJseq n 0; UMAseq n 0.

Lemma adder01_correct_carry0 :
  forall n x y f b1,
    0 < n ->
    x < 2^(n-1) ->
    y < 2^(n-1) ->
    bcexec (adder01 n) (false ` b1 ` [x]_n [y]_n f) = (false ` b1 ` [x]_n [(x + y) mod 2^n]_n f).
Admitted.

Lemma adder01_correct_carry1 :
  forall n x y f b1,
    0 < n ->
    x < 2^(n-1) ->
    y < 2^(n-1) ->
    bcexec (adder01 n) (true ` b1 ` [x]_n [y]_n f) = (true` b1 ` [x]_n [(x + y + 1) mod 2^n]_n f).
Admitted.

Fixpoint swapper02' i n :=
  match i with
  | 0 => bcskip
  | S i' => swapper02' i' n; bcswap (2 + i') (2 + n + i')
  end.
Definition swapper02 n := swapper02' n n.

Lemma swapper02_correct :
  forall n x y z f b0 b1,
    0 < n ->
    x < 2^(n-1) ->
    y < 2^(n-1) ->
    z < 2^(n-1) ->
    bcexec (swapper02 n) (b0 ` b1 ` [x]_n [y]_n [z]_n f) = b0 ` b1 ` [z]_n [y]_n [x]_n f.
Admitted.

Fixpoint negator0' i : bccom :=
  match i with
  | 0 => bcskip
  | S i' => bcx (2 + i')
  end.
Definition negator0 n := negator0' n.

Lemma negator0_correct :
  forall n x f b0 b1,
    0 < n ->
    x < 2^n ->
    bcexec (negator0 n) (b0 ` b1 ` [x]_n f) = b0 ` b1 ` [2^n - x - 1]_n f.
Admitted.

Definition highb01 n : bccom := MAJseq n 0; bccnot (2 + n + n - 1) 1; bcinv (MAJseq n 0).
Definition comparator01 n := bcx 0; negator0 n; highb01 n; bcinv (bcx 0; negator0 n).

Lemma comparator01_correct :
  forall n x y f,
    0 < n ->
    x < 2^(n-1) ->
    y < 2^(n-1) ->
    bcexec (comparator01 n) (false ` false ` [x]_n [y]_n f) = (false ` (x <=? y) ` [x]_n [y]_n f).
Admitted.

Definition subtractor01 n := bcx 0; negator0 n; adder01 n; bcinv (bcx 0; negator0 n).

Lemma subtractor01_correct :
  forall n x y b1 f,
    0 < n ->
    x < 2^(n-1) ->
    y < 2^(n-1) ->
    bcexec (comparator01 n) (false ` b1 ` [x]_n [y]_n f) = (false ` b1 ` [x]_n [(x + (2^n - y)) mod (2^n)]_n f).
Admitted.

Definition modadder21 n := swapper02 n; adder01 n; swapper02 n; 
       comparator01 n; bccont 1 (subtractor01 n); swapper02 n; bcinv (comparator01 n); swapper02 n.

Lemma modadder21_correct :
  forall n x y M f,
    0 < n ->
    x < M <= 2^(n-1) ->
    y < M <= 2^(n-1) ->
    bcexec (modadder21 n) (false ` false ` [M]_n [y]_n [x]_n f) = false ` false ` [M]_n [(x + y) mod M]_n [x]_n  f.
Admitted.


Fixpoint copier21' i n :=
  match i with
  | 0 => bcskip
  | S i' => bccnot (2 + 2 * n + i') (2 + n + i')
  end.
Definition copier21 n := copier21' n n.

Lemma copier21_correct :
  forall n x M f,
    0 < n ->
    bcexec (copier21 n) (false ` false ` [M]_n [0]_n [x]_n f) = false ` false ` [M]_n [x]_n [x]_n f.
Admitted.

Fixpoint swapperin' j i n :=
  match j with
  | 0 => bcskip
  | S j' => bcswap (2 + i * n + j') (2 + n * n + j'); swapperin' j' i n
  end.
Definition swapperin i n := swapperin' n i n.
  
Fixpoint rotator' i n :=
  match i with
  | 0 => bcskip
  | S i' => swapperin i n; rotator' i' n
  end.
Definition rotator n := rotator' (n - 1) n.

Fixpoint regl_push (l : list nat) n f :=
  match l with
  | List.nil => f
  | x :: l' => [x]_n (regl_push l' n f)
  end.

Definition list_rotate {A} (l : list A) :=
  match rev l with
  | List.nil => l
  | a :: l' => rev l' ++ (a :: List.nil)
  end.

Lemma rotator_correct :
  forall n l M f,
    0 < n ->
    length l = n ->
    bcexec (rotator n) (false ` false ` [M]_n (regl_push l n f)) = false ` false ` [M]_n (regl_push (list_rotate l) n f).
Admitted.

Fixpoint powertower (n x M : nat) :=
  match n with
  | 0 => List.nil
  | S n' => (2^n' * x mod M) :: powertower n' x M
  end.

Fixpoint towerbuilder' i n :=
  match i with
  | 0 => bcskip
  | S i' => towerbuilder' i' n; rotator n; copier21 n; modadder21 n
  end.
Definition towerbuilder n := towerbuilder' (n - 1) n.

Lemma towerbuilder_correct :
  forall n x M f,
    0 < n ->
    x < M < 2^(n - 1) ->
    bcexec (towerbuilder n) (false ` false ` [M]_n [x]_n (regl_push (repeat 0 (n - 1)) n f))
                = false ` false ` [M]_n (regl_push (powertower n x M) n f).
Admitted.

Fixpoint swapper1C' j n :=
  match j with
  | 0 => bcskip
  | S j' => bcswap (2 + n + j') (2 + (n + 1) * n + j'); swapper1C' j' n
  end.
Fixpoint swapper1C n := swapper1C' n n.

Lemma swapper1C_correct :
  forall n l M x y f,
    0 < n ->
    length l = n - 1 ->
    bcexec (swapper1C n) (false ` false ` [M]_n [x]_n (regl_push l n ([y]_n f)))
                 = false ` false ` [M]_n [y]_n (regl_push l n ([x]_n f)).
Admitted.

Fixpoint calcmodmult' i n (f : nat -> bool) :=
  match i with
  | 0 => bcskip
  | S i' => calcmodmult' i' n f; rotator n; if (f i') then (swapper1C n; modadder21 n; swapper1C n) else bcskip
  end.
Definition calcmodmult C n := rotator n; calcmodmult' n n (N2fb (N.of_nat C)); bcinv (rotator n).

Lemma calcmodmult_correct :
  forall n M x C f,
    0 < n ->
    x < M ->
    C < M ->
    M < 2^(n-1) ->
    bcexec (calcmodmult C n) (false ` false ` [M]_n (regl_push (powertower x n M) n ([0]_n f)))
             = (false ` false ` [M]_n (regl_push (powertower x n M) n ([C * x mod M]_n f))).
Admitted.

Definition calcmodmult_half C n := towerbuilder n; calcmodmult C n; bcinv (towerbuilder n).

Lemma calcmodmult_half_correct :
  forall n M x C,
    0 < n ->
    x < M ->
    C < M ->
    M < 2^(n-1) ->
    bcexec (calcmodmult_half C n) (false ` false ` [M]_n [x]_n allfalse)
              = false ` false ` [M]_n [x]_n (regl_push (repeat 0 (n - 1)) n ([C * x mod M]_n allfalse)).
Admitted.

Definition calcmodmult_full C Cinv n := calcmodmult_half C n; swapper1C n; bcinv (calcmodmult_half Cinv n).

Lemma calcmodmult_full_correct :
  forall n M x C Cinv,
    0 < n ->
    x < M ->
    C < M ->
    Cinv < M ->
    C * Cinv mod M = 1 ->
    M < 2^(n-1) ->
    bcexec (calcmodmult_full C Cinv n) (false ` false ` [M]_n [x]_n allfalse)
                   = false ` false ` [M]_n [C * x mod M]_n allfalse.
Admitted.

(* head and register 1 *)
Fixpoint swapperh1' j n :=
  match j with
  | 0 => bcskip
  | S j' => bcswap j' (2 + n + j'); swapperh1' j' n
  end.
Definition swapperh1 n := swapperh1' n n.

Lemma swapperh1_correct :
  forall n x,
    0 < n ->
    x < 2^n ->
    bcexec (swapperh1 n) ([x]_n allfalse) = false ` false ` [0]_n [x]_n allfalse.
Admitted.


Fixpoint genM0' i (f : nat -> bool) : bccom :=
  match i with
  | 0 => bcskip
  | S i' => genM0' i' f; if (f i') then bcx (2 + i') else bcskip
  end.
Definition genM0 M n := genM0' n (N2fb (N.of_nat M)).

Lemma genM0_correct :
  forall n M f b0 b1,
    M <= 2^(n-1) ->
    bcexec (genM0 M n) (b0 ` b1 ` [0]_n f) = b0 ` b1 ` [M]_n f.
Admitted.

Definition modmult M C Cinv n := swapperh1 n; genM0 M n; calcmodmult_full C Cinv n; bcinv (swapperh1 n; genM0 M n).

Lemma modmult_correct :
  forall n x M C Cinv,
    0 < n ->
    x < M ->
    C < M ->
    Cinv < M ->
    C * Cinv mod M = 1 ->
    M < 2^(n-1) ->
    bcexec (modmult M C Cinv n) ([x]_n allfalse) = [C * x mod M]_n allfalse.
Admitted.    
