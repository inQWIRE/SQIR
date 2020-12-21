Require Import UnitaryOps.
Require Import BooleanCompilation.
Require Import Coq.NArith.NArith.
Require Import BinNums.
Require Import RCIR.
From QuickChick Require Import QuickChick. Import QcNotation.

(* Suppress some annoying warnings: *)
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Export ExtLib.Structures.Monads.
Export MonadNotation. Open Scope monad_scope.

Require Import String.  Local Open Scope string.

(*********************************)
(** Natural Number Compilation **)
(*********************************)
(* This file defines a 'compile' function that converts an arbitrary
   numeric expression into a reversible circuit that (provably) uncomputes 
   its ancillae. We use eager ancilla cleanup, which requires fewer qubits,
   but more gates, than the lazy approach. Because SQIR does not allow
   initializing / discarding qubits, we precompute the number of ancillae
   needed and include them in the global register.
 
   The numeric expression language and compilation strategy are modelled
   after the BooleanCompilation.v file, also found in VOQC, which is 
   itself based on the ReVerC reversible circuit compiler.
   In particular, this compilation process uses boolean circuits constructed
   from BooleanCompilation in order to streamline the circuit creation process.


   We prove that compilation is correct by showing that the output circuit
   has the expected behavior on any basis state. The proof requires some
   new formalisms for describing classical states (see 'f_to_vec'). *)

(** Natural Number Expressions **)

(*The general strategy to represent natural numbers is by logically 
  partitioning our bits into fixed sized registers. This size is defined
  when calling the compile function, and is passed into nearly every function. 
   *)

(*Throughout this file, Coq nats can have three different meanings:
1) nat representing a register. An example of this is the argument of 
  n_var_reg, in which a nat is used to select a register. For instance,
  n_var_reg 1 represents bits reg_size through 2*reg_size -1, where reg_size
  is the defined register size

2) nat representing a register-sized group of bits beginning with the
   argument-th bit. An example of this would be 
   n_var_bit 1, which would represent bits 1 through reg_size, where
   reg_size is the defined register size. 
   
This use of nats is prevalently used throughout the compilation process
   via parameters i and j, with i typically representing the first bit of 
   a register or a target bit and j representing the first usable ancilla bit

3) An actual number, typically representing either the size of a register 
   (or some variable which tracks the size of a number throughout a recursive
   function) or the actual value of a nexp itself, such as the output of interpret_nexp

 *)
(*As an example, here is a representation of the number 3 and 4 loaded into
  the first two registers of size 4, with 20 total bits:
  0011 0100 0000 0000 0000 

  The compilation with place a result into the first unused register, in this case most likely the third register. 

  Compiling n_var_reg 0 will leave us with bits:
  0011 0100 0011 0000 0000
  as it copies over the first register

  Compiling n_var_bit 2 will leave us with bits:
  0011 0100 1101 0000 0000
  as it copies over bits 2 through 5

  Compiling n_plus (n_var_reg 0) (n_var_reg 1) gives us:
  0011 0100 0111 0000 0000
  with 0111 = 7 being the sum of 3 and 4. Note that this would need more ancilla 
  than is shown.

  Compiling n_mult (n_var_reg 0) (n_var_reg 1) gives us:
  0011 0100 1100 0000 0000
  with 0111 = 12 being the product of 3 and 4. Note that this would need more ancilla 
  than is shown.

*)
Inductive  nexp :=
| n_var_reg : nat -> nexp (*register number 0-indexed nat -> nexp *)
| n_var_bit : nat -> nexp (*uses an arbitrary register's worth of bits beginning at nat -> nexp*)
| n_plus : nexp -> nexp -> nexp
| n_shiftr : nexp -> nat -> nexp 
| n_mult : nexp -> nexp -> nexp.

(*shift_vec_l is used in order to isolate the natural number value represented by a group of bits.
interpret_nexp shifts a group of bits to the left so that the first bit of the group is seen as 
(f 0). This is needed because funbool_to_nat (which is defined in VectorStates.v in SQIR) works
by converting our function to a list, and then calculating a natural number from the first
*size* values of that list. shift_l allows us to push our desired group of numbers to the first 
value in the list and allows funbool_to_nat to ignore any prior bits *)
Definition shift_vec_l {A} (input_vec : nat -> A) k := fun i => input_vec (i + k)%nat.
(*make lemmas for this *)   

(*calculates the value of nexps. Uses funbool_to_nat as explained above shift_l.
  the f defines the space of bit values that we want to interpret.  *)
Fixpoint interpret_nexp (n : nexp) (input_vec : nat -> bool) (register_size : nat): nat :=
  match n with
  | n_var_reg e1 => funbool_to_nat register_size (shift_vec_l input_vec (e1 * register_size))
  | n_var_bit e1 => funbool_to_nat register_size (shift_vec_l input_vec (e1))                 
  | n_plus e1 e2 => (interpret_nexp e1 input_vec register_size)
                    + (interpret_nexp e2 input_vec register_size)
  | n_shiftr e1 c => (interpret_nexp e1 input_vec register_size)
                     * (2 ^ c)
  | n_mult e1 e2 => (interpret_nexp e1 input_vec register_size)
                    * (interpret_nexp e2 input_vec register_size)
  end. 

(*
Example of interpret_nexp: 

practicef builds a space of bits with bits 0 and 1 being activated
  interpret_nexp knows that (n_var_ reg 0) represents bits 0 through 3
  because the value 4 is being passed in as register_size. 

interpret_nexp then shifts practicef by 0, because we access the 0th register.

Then, funbool_to_nat turns our f (defined below and unmodified by shift_l) 
into the list [false, false, true, true], again, because the register_size is 4. From this list
is calculated the value 3, which has a binary representation corresponding to the list
where false = 1 and true = 0.

We could define any arbitrary f to input into interpret_nexp,
and that would change the output. 
    
 *)
Definition practiceInput : nat -> bool :=
  fun n => (match n with
            |0 => false
            |S 0 => true
            |_ => true end).

Eval compute in interpret_nexp (n_var_reg 0)  practiceInput 4.

Definition f_in : nat -> bool :=
  fun n => (match n with
            |0 => false
            |S 0  => false
            |S (S 0) => false
            |S (S (S 0)) => true

                    
            |4 => false
            |5 => false
            |6 => true
            |7 => true
            |_ => true end).
Eval compute in funbool_to_list 4 (shift_vec_l f_in 1).
Eval compute in interpret_nexp (n_var_reg 0) f_in 4.
Eval compute in interpret_nexp (n_var_reg 1) f_in 4.

(*Only reversible if number is well typed for shiftr, but this is up to the user to define
a large enough register size. Could (possibly) include this in well_typed? *)                     (*A nexp is well typed if the bits it is trying to access are within the total number of input bits *)                                                          
Inductive nexp_well_typed (register_size : nat) : nat -> nexp -> Prop :=
| WT_n_var_reg : forall n q, (q * register_size < n)%nat -> nexp_well_typed register_size n (n_var_reg q )
                                                            
| WT_n_var_bit : forall n q, (q < n)%nat -> nexp_well_typed register_size n (n_var_bit q )
| WT_n_plus : forall n n1 n2, nexp_well_typed register_size n n1 ->
                              nexp_well_typed register_size n n2 ->
                              nexp_well_typed register_size n (n_plus n1 n2)
| WT_n_shiftr : forall n n1 s, nexp_well_typed register_size n n1 ->
                               nexp_well_typed register_size n (n_shiftr n1 s)
| WT_n_mult : forall n n1 n2, nexp_well_typed register_size n n1 ->
                              nexp_well_typed register_size n n2 ->
                              nexp_well_typed register_size n (n_mult n1 n2).

(*Have not fully worked out n_well_typed_increase_dim and
interpret_nexp_f yet *)
Lemma n_well_typed_increase_dim : forall e n n' size,
    (n <= n')%nat ->
    nexp_well_typed size n e ->
    nexp_well_typed size n' e.
Proof.
  intros.
  induction H0; try constructor; try lia; try auto.
Qed.
    
(*TODO. Unsure as to how I want to express these lemmas, whether with registers or bits *)
Lemma interpret_nexp_f : forall i n f f' size,
    nexp_well_typed size i n ->
    (forall k, (k < i)%nat -> f k = f' k) ->
    interpret_nexp n f = interpret_nexp n f'.
Proof.
  intros.
  induction H; simpl; try reflexivity.
  
 Admitted. (*
  intros.
  induction H; simpl; try reflexivity.
  - unfold shift_l. apply H0. (* FIX THIS*)
  rewrite IHnexp_well_typed1.
  rewrite IHnexp_well_typed2.
  reflexivity.
  apply H0.
  apply H0.*)



(** Compilation of boolean expressions to oracles **)

(* How many input variables does this expression use? *)

(*n_max_var calculates the number of inputs used by  our nexp.
  Conveniently, it will return a number which corresponds with
  the first bit of the register that will store our result.

  Perhaps could be renamed a bit more clearly. 
  
  This should align with every other register unless you use n_var_bit
 *)


Fixpoint n_num_input_bits (n : nexp) ( register_size: nat) :=
  match n with
  | n_var_reg n1 => (register_size * (n1 + 1))%nat
  | n_var_bit n1 => (n1 + register_size)%nat
  | n_plus n1 n2 =>  ((max (n_num_input_bits n1 register_size)
                           (n_num_input_bits n2 register_size)))%nat
  | n_shiftr n1 s => n_num_input_bits n1  register_size
  | n_mult n1 n2 => ((max (n_num_input_bits n1 register_size)
                          (n_num_input_bits n2 register_size)))%nat
  end.

(*n_plus will add the number stored by bits 0-3 and the number stored by bits 4-7. 
  n_num_input_bits (n_var_reg 0) returns 4 (because 0 through 3 are clearly occupied)
  n_num_input_bits (n_var_reg 1) returns 8 (because 4 through 7 are clearly occupied)
  Therefore the overrall n_num_input_bits returns 8. Meaning that we can store our output
  beginning with bit 8. *)
Eval compute in n_num_input_bits (n_plus (n_var_reg 0) (n_var_reg 1)) 4.

(*Lemma n_num_inputs_well_typed : forall n,
    nexp_well_typed (n_num_inputs n) n.
Proof.
  induction n.
  - constructor. unfold n_num_inputs; simpl. lia.  
  - constructor.
    + apply n_well_typed_increase_dim with (n:=n_num_inputs n1); try assumption.
      unfold n_num_inputs. simpl. lia.
    + apply n_well_typed_increase_dim with (n:= n_num_inputs n2); try assumption.
      unfold n_num_inputs. simpl. lia.
Qed.
*)

(*This most likely isn't needed anymore unless we decide not to use 
fixed sized registers *)
Fixpoint n_num_out n (register_size : nat): nat :=
  match n with
  | n_var_reg n1  => register_size
  | n_var_bit n1 => register_size
  | n_plus n1 n2 => register_size
  | n_shiftr n1 s => register_size
  | n_mult n1 n2 => register_size
  end.

(*These are very much incorrect but not used, will fix. This will be used to 
calculate the total number of ancilla for each circuit, which will allow us to 
precompute the total number of bits we'll used (shown by n_dim)*)

Fixpoint n_num_ancillae n (register_size : nat) : nat :=
  match n with
  | n_plus n1 n2 => register_size * 3 +2 (*Three registers (n1, n2, carries) plus 2 ancillae *)
  | n_mult n1 n2 => register_size *(3 + register_size)+ (register_size * 3) + 2 (*TODO *)
  | _ => 0
  end.
  
(* Total number of qubits required. *)
Definition n_dim (n : nexp) (register_size : nat) : nat :=
  (n_num_input_bits n register_size) +
  (n_num_out n register_size) +
  (n_num_ancillae n register_size).





(*ripple carry adder*)
Definition adder_cout_bexp (n1_bit n2_bit carry : nat) : bexp:= (b_var carry ∧ (b_var n2_bit ⊻ b_var n1_bit)) ⊻ (b_var n2_bit ∧ b_var n1_bit).
Definition adder_sum_bexp (n1_bit n2_bit carry : nat) : bexp := (b_var carry) ⊻ (b_var n2_bit ⊻ b_var n1_bit).
(*I will store carries in /the first/ register after the register I want to store my number in. Any other misc ancilla will be after the end of my carry register *)

(* 
|n0
|n1
|n2
...
|n

|n1+n2 <- i_out
|all the carries (eventually removed)
|copy of n1 (eventually removed) <- i_in1
|copy of n2 (eventually removed) <- i_in2
| <- i_anc
 *)
(*recursive compilation for adding two numbers. 

i_in1: bit we want to add of n1
i_in2: bit we want to add of n2
i_out: bit we want to store the sum in
i_anc: first ancilla bit accessible (ancilla bit layout is shown above)
n: decreasing nat showing how many bits are left to sum
sz_reg: register size *)
(*Renaming compile' to compile_bit for ease of readability *)
Definition compile_bit  (e : bexp) (i_out i_anc : nat) : bccom :=
  compile' e i_out i_anc.


(*i_in1 and i_in2 begin as rightmost bit of numbers then move left *)
Fixpoint n_compile_plus   (i_in1 i_in2 i_out i_anc n sz_reg: nat) : bccom:=
  (* *)
  match n with
  | 0 => bcskip
  (*Last bit means we don't need to store the carry *)
  | S 0 =>     compile_bit (adder_sum_bexp i_in1 i_in2 (i_out + sz_reg)%nat) i_out i_anc
  | S n' => 
    compile_bit (adder_cout_bexp i_in1 i_in2 (i_out + sz_reg)%nat) (i_out + sz_reg - 1) i_anc;
    compile_bit (adder_sum_bexp i_in1 i_in2 (i_out + sz_reg)%nat) i_out i_anc;
    n_compile_plus (i_in1 - 1) (i_in2 - 1) (i_out - 1) i_anc (n') sz_reg;
    compile_bit (adder_cout_bexp i_in1 i_in2 (i_out + sz_reg)%nat) (i_out + sz_reg - 1) i_anc
end.

(*n_compile_var is based off of BooleanCompilation.v's compilation of b_var.

It copies each bit of the desired register into the output register
 *)
Fixpoint n_compile_var   (i_in i_out i_anc n sz_reg: nat) : bccom :=

  match n with
  |S n' => compile_bit (b_var i_in) i_out i_anc;
              n_compile_var (i_in + 1) (i_out + 1) i_anc n' sz_reg
  |0 => bcskip
end.


        
(*n_compile_mult will multiply two numbers (hopefully)
I want to do this using the logic of decomposing numbers into powers of 2.
As an example, 6 = 2^2 + 2^1. My vision is for this to happen. 

This copies each number to the next free register and shifts it
it then adds this number to the last partial sum, and continues
 *)

(*n_compile_shiftl swaps each bit of a number with the bit to its left.
  This is only reversible if we assume that the number is not too big for the register.

  It performs the shift once *)
Fixpoint n_compile_shiftl   ( i_curr i_anc n sz_reg : nat) : bccom :=
  match n with
  |0 => bcskip
  |S 0 =>bcskip
  |S n' => n_compile_shiftl (i_curr - 1) i_anc n' sz_reg;
           bccnot i_curr (i_curr - 1); bccnot (i_curr - 1) i_curr
            
end.

 (*n_compile_shiftr_c (c is for constant) does n_compile_shiftr multiple times *)
Fixpoint n_compile_shiftl_c   (i_in i_anc c n sz_reg : nat) : bccom :=
  match c with
  |0 => bcskip
  |S c' => n_compile_shiftl i_in i_anc n sz_reg;
           n_compile_shiftl_c i_in i_anc c' n sz_reg
end.
(* Like shiftr but the opposite *)
Fixpoint n_compile_shiftr   ( i_curr i_anc n sz_reg : nat) : bccom :=
  match n with
  |0 => bcskip
  |S 0 =>bcskip
  |S n' => bccnot (i_curr - 1) (i_curr) ; bccnot i_curr (i_curr - 1);
                n_compile_shiftr (i_curr - 1) i_anc n' sz_reg
               
            
end.

 (*n_compile_shiftr_c (c is for constant) does n_compile_shiftr multiple times *)
Fixpoint n_compile_shiftr_c   (i_in i_anc c n sz_reg : nat) : bccom :=
  match c with
  |0 => bcskip
  |S c' => n_compile_shiftr i_in i_anc n sz_reg;
           n_compile_shiftr_c i_in i_anc c' n sz_reg
end.




Fixpoint n_compile_and_bit_reg   (i_in i_if i_out i_anc n sz_reg : nat ) : bccom :=
  match n with
  | 0=> bcskip
  | S n' => (compile_bit (b_and i_in i_if) i_out i_anc);
            n_compile_and_bit_reg (i_in-1) i_if (i_out - 1) i_anc n' sz_reg
  end.

Definition n_compile_ifb_shift   (i_in i_if i_out i_anc  c sz_reg: nat) : bccom :=
 
  n_compile_and_bit_reg i_in i_if i_out i_anc sz_reg sz_reg;
  n_compile_shiftl_c i_out i_anc c sz_reg sz_reg.
Definition n_compile_ifb_shift_rev   (i_in i_if i_out i_anc  c sz_reg: nat) : bccom :=

  n_compile_shiftr_c i_out i_anc c sz_reg sz_reg;
  n_compile_and_bit_reg i_in i_if i_out i_anc sz_reg sz_reg.
 
      
(*i_anc is first bit things should be copied to  *)
(*i_in1 and i_in2 are the rightmost bit of their numbers, i_anc is leftmost free bit which is why I do the i_anc ... + sz_reg - 1. This goes to the rightmost bit of that register 

a * b

a ? + a>>1 + a>>2?
0011 = 3
0110 = 6
1100 = 12

0011 * 0111

*)
Fixpoint n_compile_mult   (i_in1 i_in2 i_out i_anc n c sz_reg: nat) : bccom :=
  match n with
  | 0 => n_compile_var (i_anc + sz_reg * (c + 1)) i_out i_anc sz_reg sz_reg
  | S n' =>
    n_compile_ifb_shift i_in1 i_in2 (i_anc + sz_reg - 1)
                        (i_anc + sz_reg * sz_reg * 2) c sz_reg;

    n_compile_plus (i_anc +sz_reg - 1) (i_anc + sz_reg * (c+2) - 1)
               (i_anc + sz_reg * (c+3) - 1) (i_anc + sz_reg * sz_reg *2) sz_reg sz_reg; 

    n_compile_ifb_shift_rev i_in1 i_in2 (i_anc + sz_reg - 1)
                        (i_anc + sz_reg * sz_reg * 2) c sz_reg;

    n_compile_mult i_in1 (i_in2 - 1) i_out (i_anc) n' (c + 1) sz_reg    
end.

Fixpoint n_compile_mult_cleanup   (i_in1 i_in2 i_out i_anc n c sz_reg: nat) : bccom :=
  match n with
  | 0 => bcskip
           
  | S n' =>
            n_compile_ifb_shift i_in1 i_in2 (i_anc + sz_reg - 1)
                        (i_anc + sz_reg * sz_reg * 2) (c -1) sz_reg;

            n_compile_plus (i_anc +sz_reg - 1) (i_anc + sz_reg * (c+1) - 1)
               (i_anc + sz_reg * (c+2) - 1) (i_anc + sz_reg * sz_reg *2) sz_reg sz_reg;

            n_compile_ifb_shift_rev i_in1 i_in2 (i_anc + sz_reg - 1)
                        (i_anc + sz_reg * sz_reg * 2) (c - 1) sz_reg;

            n_compile_mult_cleanup i_in1 (i_in2 + 1) i_out (i_anc) n' (c - 1) sz_reg
                    
end.

Fixpoint n_compile'   (e : nexp) (i_out i_anc sz_reg: nat) : bccom :=
  match e with 
  | n_var_reg e1 => n_compile_var (e1 * sz_reg) i_out i_anc sz_reg sz_reg 

  | n_var_bit e1 => n_compile_var e1 i_out i_anc sz_reg sz_reg

  | n_plus e1 e2 => n_compile' e1 (i_anc + sz_reg) (i_anc + sz_reg *2) sz_reg;
                    n_compile' e2 (i_anc + sz_reg * 2) (i_anc + sz_reg *3) sz_reg;
                    n_compile_plus (i_anc + sz_reg * 2 -1) (i_anc + sz_reg * 3 - 1)
                                   (i_out + sz_reg - 1) (i_anc + sz_reg *3) sz_reg sz_reg;
                    n_compile' e2 (i_anc + sz_reg *2) (i_anc + sz_reg *3) sz_reg;
                    n_compile' e1 (i_anc + sz_reg) (i_anc + sz_reg *2) sz_reg

  | n_shiftr e1 c => n_compile' e1 i_out i_anc sz_reg;
                     n_compile_shiftr_c i_out i_anc c sz_reg sz_reg

      | n_mult e1 e2 =>  n_compile' e1 (i_anc) (i_anc + sz_reg) sz_reg;
                     
                     n_compile' e2 (i_anc  + sz_reg) (i_anc + sz_reg *2) sz_reg;
                     
                     n_compile_mult (i_anc + sz_reg - 1) (i_anc + sz_reg + sz_reg - 1)
                                     i_out (i_anc + sz_reg *2) sz_reg 0 sz_reg ;
                     
                     n_compile_mult_cleanup (i_anc + sz_reg - 1) (i_anc + sz_reg)
                                     i_out (i_anc + sz_reg *2) sz_reg sz_reg sz_reg ; 
                     
                     n_compile' e2 (i_anc  + sz_reg) (i_anc + sz_reg *2) sz_reg;
                     n_compile' e1 (i_anc) (i_anc + sz_reg) sz_reg


  end. 

(*compiles our number *)  
Definition n_compile n r_size : bccom :=
  n_compile' n (n_num_input_bits n r_size) ((n_num_input_bits n r_size) + r_size) r_size. 
(* Correctness of compile':
   1. The value at index i is xor-ed with the desired boolean expression.
   2. All other values remain unchanged.

   Notes:
   * The well-typedness constraint is used in the b_var case.
   * 'i < j' is used when applying f_to_vec_X, f_to_vec_bccnot, and f_to_vec_TOFF.
   * 'j + (num_ancillae b) < n + 1' and 'forall k ...' are used in the b_and 
     case -- note that this is the only case where the ancilla matter.
*)
Local Opaque CCX.

     
     (*
Lemma n_compile'_correct : forall (n : nexp) (f : nat -> bool) (dim i j d: nat), (* d for digit (even though it's bits *)
    nexp_well_typed i n -> (i < j)%nat -> (d < size n)%nat -> (j + (n_num_ancillae n) < dim + 1)%nat ->
    (forall k, (k > i)%nat -> f k = false) ->  
    (uc_eval (@n_compile' dim n i j 0)) × (f_to_vec dim f) =
    f_to_vec dim (update f (i- d)%nat ((f (i - d)%nat) ⊕ (interpret_nexp_at n f d))).
Proof.
  intros.
  generalize dependent f.
  generalize dependent j.
  generalize dependent i.
  induction n; intros. (* Inductive structure of nexp *)
  - inversion H; subst; clear H.
    unfold n_compile'. unfold n_compile_val.
    (* Induction on d *)
   (* induction d.
    + unfold interpret_nexp_at.
      assert (n/(2 ^ 0) = n)%nat. simpl. apply Nat.div_1_r. rewrite H.
      induction n0. unfold size. simpl in H1. autorewrite with eval_db. try lia. try lia.
      destruct (n mod 2 =? 1).
      2:{induction n. assert ((0 / 2) = 0 )%nat. apply Nat.div_small. lia. rewrite H4. rewrite IHn0. reflexivity. unfold size.  unfold size in H1. rewrite H1. }*)
(*Induction on n0?*)
    induction n. (* induction on value of the number *)
    + unfold interpret_nexp_at. unfold size. simpl in H1.
      rewrite Nat.div_0_l. rewrite Nat.mod_0_l.
      induction n0. (*induction on number of bits used *) 
      * simpl. autorewrite with eval_db; try lia.
      * simpl. simpl in IHn0. simpl in H2.  assert (n0 > 0 -> S n0 > 0)%nat by lia.
        rewrite IHn0. reflexivity.                    
      try lia.
      try lia.
    + destruct (n mod 2 =? 1).
      2:{unfold interpret_nexp_at. unfold interpret_nexp_at in IHn0. simpl in H1. rewrite IHn0. }
Abort.
*)
(** Examples **)


Infix "⊻" := b_xor (at level 40).
Infix "∧" := b_and (at level 40).

Local Close Scope R_scope.

Set Printing Depth 100.

(* Basic examples of compilation of plus and multiply without eval*)
Definition simple_add : nexp := (n_plus (n_var_reg 0) (n_var_reg 1)).
Redirect "out2" Eval compute in (n_compile simple_add 4).

Definition num_nexp : nexp := (n_mult (n_plus (n_var_reg 0) (n_var_reg 1)) (n_var_reg 2)).
Redirect "out2" Eval compute in (n_compile num_nexp 4).
Eval cbv in (n_compile num_nexp 4).

Definition multrec_nexp : nexp := (n_mult (n_plus (n_var_reg 0) (n_var_reg 1)) (n_var_reg 2)).
Redirect "out2" Eval compute in (n_compile multrec_nexp 4).
Eval cbv in (n_compile multrec_nexp 4).

(* Incorporating evaluation *)
Definition f_in2 : nat -> bool :=
  fun n => (match n with
            |0 => false
            |S 0  => false
            |S (S 0) => true
            |S (S (S 0)) => true

                    
            |4 => false
            |5 => false
            |6 => true
            |7 => true
            |_ => false end).
Eval compute in funbool_to_list 12 f_in2.
Definition add_nexp : nexp := (n_plus (n_var_reg 1) (n_var_reg 0)).
Definition add_nexp_compiled := (n_compile add_nexp 4).
Eval compute in funbool_to_list 12 (bcexec add_nexp_compiled f_in2).
Definition n_var_compiled : bccom := n_compile (n_var_reg 1 ) 4.
Eval compute in funbool_to_list 12 (bcexec n_var_compiled f_in2).
Eval compute in funbool_to_nat 4 (bcexec n_var_compiled f_in2).
(*  n_compile_var   (i_in i_out i_anc n sz_reg: nat) : bccom   *)



Definition simple_mult : nexp := (n_mult (n_var_reg 0) (n_var_reg 1)).
Eval compute in interpret_nexp (n_var_reg 0) f_in2 4.
Eval compute in interpret_nexp simple_mult f_in2 4.
Definition mult_nexp_compiled := (n_compile simple_mult 4).
Definition mult_nexp_interpreted := (bcexec mult_nexp_compiled f_in2).
Eval compute in funbool_to_nat 4 (shift_vec_l mult_nexp_interpreted 8).
Eval compute in funbool_to_nat 4 (nat_to_funbool 4 3).

(** Testing more generally with QuickChick **)

(*I want to, for now, use a list of nats to represent number stored in each register *)
Fixpoint listnat_to_binlist (size : nat) (lst : list nat ) : list bool :=
  match lst with

  |nil => []
  |h::t => (listnat_to_binlist size t)++(nat_to_binlist size h)
  end. 

Definition listnat_to_funbool (size : nat) (lst : list nat) : nat -> bool :=
  let bl := (listnat_to_binlist size lst) in
  list_to_funbool (List.length bl) (bl).

(* making sure that the listnat can fit within the desired expression and reg size *)

Fixpoint max_allowed_input_aux (size : nat) (ops : nexp) : nat :=
  match ops with
  |n_plus n1 n2 => min (max_allowed_input_aux (size - 1) n1) (max_allowed_input_aux (size - 1) n2)
  |n_mult n1 n2 => min (max_allowed_input_aux (size / 2) n1) (max_allowed_input_aux (size /2) n2)
  |_ => size
  end.

(*Note that this is too strict, there could be variations of numbers which would fit within
the registers but aren't allowed. This will just be used for generators.  *)  
Fixpoint max_allowed_input (size : nat) (ops : nexp) : nat :=
   Nat.pow 2 (max_allowed_input_aux size ops) - 1.

Eval compute in max_allowed_input 4 (n_mult (n_var_reg 0) (n_var_reg 1)).

(*I'll now do tests on simple_add which is a circuit which just adds two numbers *)

(*This generages lists of 2 nats, which we just need to transform into funbools. *)
Sample (vectorOf 2 (choose (0, (max_allowed_input 4 simple_add) ))).


Definition compile_matches (size : nat) (inputs : list nat) (e : nexp) :=
  let f := listnat_to_funbool size inputs in
  ((funbool_to_nat size (shift_vec_l (bcexec (n_compile e size) f) (size * (List.length inputs))))
  = interpret_nexp e f size) ?.
(*
 QuickChick
  (forAll
     (vectorOf 2 (choose (0, (max_allowed_input 4 simple_add) )))
     (fun i => compile_matches 4 i simple_add) 
    ).
Passes all tests.
Note that if we had changed max_allowed_input to use +1 rather than -1, it would fail
. One example being 9 + 7 which is 16, not expressible with 4 qubits*)
(*
QuickChick
  (forAll
     (choose (2, 10))
     (fun size => (forAll (vectorOf 2 (choose (0, (max_allowed_input size simple_add) )))
     (fun i =>
        compile_matches size i simple_add)) 
    )).
It passes for a variety of register sizes.*)

(*
 QuickChick
  (forAll
     (vectorOf 2 (choose (0, (max_allowed_input 4 simple_mult) )))
     (fun i => compile_matches 4 i simple_mult) 
    ).
I'm not going to vary the length of this much just because it takes an amount of time to compile
circuits with large register sizes. 
*)


(** Now for the much harder (and longer to compute part) of generating nexps *)
(* We want to generate expressions (and corresponding inputs) with the following characteristics:
1) We need input to fit within input list
2) The expression shouldn't be very deep (maybe 3 or 4 size max)
3) The expression should be well typed 

I suppose first we should generate random inputs, then random expressions from that?  

*)
Derive Show for nexp.

Fixpoint gen_nexp_reg ( num_inputs : nat) : G (nexp) :=
   bind (choose (0, num_inputs)) (fun x =>
         ret (n_var_reg x)) .
Sample (gen_nexp_reg 4).

(* Need to change notation because bccom uses semicolons and I can't seem to close that scope*)
Notation " 'freq' [ x ;;; y ] " := (freq_ (snd x) (cons x (cons y nil))) .
Notation " 'freq' [ x ;;; y ;;; .. ;;; z ] " := (freq_ (snd x) (cons x (cons y .. (cons z nil) ..))).

(*I am making n_plus twice as common as the two other possibilities because I don't want computation times to become too large *)
Fixpoint gen_nexp_sized (sz num_inputs: nat) : G (nexp) :=
  match sz with
  | 0 => gen_nexp_reg num_inputs
  | S sz' =>
    freq[(1, (gen_nexp_reg num_inputs) ) ;;;
         (2, (liftM2 n_plus (gen_nexp_sized sz' num_inputs) (gen_nexp_sized sz' num_inputs) )) ;;;
         (1, (liftM2 n_mult (gen_nexp_sized sz' num_inputs) (gen_nexp_sized sz' num_inputs) ))
        ]
  end.

Sample (gen_nexp_sized 2 4).

Fixpoint num_in_regs (n : nexp):=
  match n with
  |n_plus n1 n2 => max (num_in_regs n1) (num_in_regs n2)
  |n_mult n1 n2 => max (num_in_regs n1) (num_in_regs n2)
  |n_var_reg r => r
  |_ => 0
  end.
  

(* using size of 4 and also 4 inputs just because it's small enough but not too small *)

    

Definition test_mult_plus_4 :=
  forAll
      (gen_nexp_sized 3 4)
      (fun exp => let num_ins := ((num_in_regs exp)%nat + 1)%nat in
                 forAll( (vectorOf num_ins (choose (0, (max_allowed_input 4 exp)))))
                          (fun i => compile_matches 4 i exp)).
 (*QuickChick
   test_mult_plus_4.
This works for gen_nexp_sized 3 4! Now to test with more range *)

Definition test_mult_plus :=
  forAll
    (choose(1,6))
    (fun reg_size => forAll
      (gen_nexp_sized 3 reg_size)
      (fun exp => let num_ins := ((num_in_regs exp)%nat + 1)%nat in
                 forAll( (vectorOf num_ins (choose (0, (max_allowed_input reg_size exp)))))
                          (fun i => compile_matches reg_size i exp))).

(*QuickChick test_mult_plus.
test_mult_plus is a more generic test than any we have done before. I am reluctant to test register sizes larger than six because of the amount of time it would take to run all the tests. 
 
It is  also for this reason that I hesitate to increase the fuel parameter of gen_nexp_sized beyond 3
*)
