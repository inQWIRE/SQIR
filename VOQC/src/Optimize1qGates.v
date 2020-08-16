Require Import UnitarySem.
Require Export QiSGateSet.
Require Import List.
Open Scope ucom.

Local Close Scope C_scope.
Local Close Scope R_scope.
Local Close Scope Q_scope.

(**********************************************************************)
(** Optimization: simple combination w/ commutation **)
(**********************************************************************)

(* Combine several U gates on a qubit to one U gate. *)

(* equivalence rules for U1; U2 ; U3 *)

(* If both gates are U1, then sum them together. *)
Definition combine_U_equivalence1 {dim} q (l : QiS_ucom_l dim) := 
  match (next_single_qubit_gate l q) with
    | Some (l1, UQiS_U1 a, l2) =>
       match next_single_qubit_gate l2 q with 
            | Some (l3, UQiS_U1 a', l4) => Some (l1 ++ [U1 (a + a')%Q q] ++ l3 ++ l4)
            | _ => None end
    | _ => None end.

(* if u1 follows u2 then a + a, and b *)
Definition combine_U_equivalence2 {dim} q (l : QiS_ucom_l dim) := 
  match (next_single_qubit_gate l q) with
    | Some (l1, UQiS_U1 a, l2) =>
       match next_single_qubit_gate l2 q with 
            | Some (l3, UQiS_U2 a' b, l4) => Some (l1 ++ [U2 (a + a')%Q b q] ++ l3 ++ l4)
            | _ => None end
    | _ => None end.

(* the oppose of equiv2 *)
Definition combine_U_equivalence3 {dim} q (l : QiS_ucom_l dim) := 
  match (next_single_qubit_gate l q) with
    | Some (l1, UQiS_U2 a b, l2) =>
       match next_single_qubit_gate l2 q with 
            | Some (l3, UQiS_U1 a', l4) => Some (l1 ++ [U2 (a' + a)%Q b q] ++ l3 ++ l4)
            | _ => None end
    | _ => None end.


(* if u1 a follows U3 a b c then U3 a' (a + b) c *)
Definition combine_U_equivalence4 {dim} q (l : QiS_ucom_l dim) := 
  match (next_single_qubit_gate l q) with
    | Some (l1, UQiS_U1 a, l2) =>
       match next_single_qubit_gate l2 q with 
            | Some (l3, UQiS_U3 a' b c, l4) => Some (l1 ++ [U3 a' (a + b)%Q c q] ++ l3 ++ l4)
            | _ => None end
    | _ => None end.

(* the oppose of equiv4 *)
Definition combine_U_equivalence5 {dim} q (l : QiS_ucom_l dim) := 
  match (next_single_qubit_gate l q) with
    | Some (l1, UQiS_U3 a b c, l2) =>
       match next_single_qubit_gate l2 q with 
            | Some (l3, UQiS_U1 a', l4) => Some (l1 ++ [U3 a (b + a')%Q c q] ++ l3 ++ l4)
            | _ => None end
    | _ => None end.

(* if both are U2 (a b) (a' b'), then U3 (180 - b - a') (a + 90) (b' + 90)  *)
Definition combine_U_equivalence6 {dim} q (l : QiS_ucom_l dim) := 
  match (next_single_qubit_gate l q) with
    | Some (l1, UQiS_U2 a b, l2) =>
       match next_single_qubit_gate l2 q with 
            | Some (l3, UQiS_U2 a' b', l4)
               => Some (l1 ++ [U3 (180 - b - a')%Q (a + 90)%Q (b' + 90)%Q q] ++ l3 ++ l4)
            | _ => None end
    | _ => None end.

(* if both are U2 a b, or U3 a b c, and if a mod 360 = 0 then U1 0 0 ( b + c) *)
Definition combine_U_equivalence7 {dim} q (l : QiS_ucom_l dim) := 
  match (next_single_qubit_gate l q) with
    | Some (l1, UQiS_U2 a b, l2) =>
             if (Zmod (Qnum a) ((QDen a) * 360) =? 0)%Z then
                  Some (l1 ++ [U1 b q] ++ l2)
                else None
    | Some (l1, UQiS_U3 a b c, l2) =>
             if (Zmod (Qnum a) ((QDen a) * 360) =? 0)%Z then
                  Some (l1 ++ [U1 (b+c) q] ++ l2)
                else None
    | _ => None end.


(* if both are U3 a b c, if a mod 360 = 90 or 270 then U2 b/b+180 c/c-180. *)
Definition combine_U_equivalence8 {dim} q (l : QiS_ucom_l dim) := 
  match (next_single_qubit_gate l q) with
    | Some (l1, UQiS_U3 a b c, l2) =>
             if (Zmod (Qnum a) ((QDen a) * 360) =? 90)%Z then
                  Some (l1 ++ [U2 b c q] ++ l2)
                else if (Zmod (Qnum a) ((QDen a) * 360) =? 270)%Z then
                  Some (l1 ++ [U2 (b+180) (c - 180) q] ++ l2)
                else None
    | _ => None end.

(* if both are U1 a, if a mod 360 = 0 then the gate can be canceled. *)
Definition combine_U_equivalence9 {dim} q (l : QiS_ucom_l dim) := 
  match (next_single_qubit_gate l q) with
    | Some (l1, UQiS_U1 a, l2) =>
             if (Zmod (Qnum a) ((QDen a) * 360) =? 0)%Z then
                  Some (l1 ++ l2)
                else None
    | _ => None end.

Definition combine_U_equivalence {dim} (l : QiS_ucom_l dim) (q:nat) : option (QiS_ucom_l dim)  := 
   try_rewrites l (combine_U_equivalence1 q :: combine_U_equivalence2 q :: combine_U_equivalence3 q
            :: combine_U_equivalence4 q :: combine_U_equivalence5 q :: combine_U_equivalence6 q ::
           combine_U_equivalence7 q :: combine_U_equivalence8 q :: combine_U_equivalence9 q :: []).


Fixpoint combine_U_equivalences' {dim} (l : QiS_ucom_l dim) (n: nat) acc : QiS_ucom_l dim :=
  match n with
  | 0 => rev_append acc l
  | S n' => 
      match l with
      | [] => rev_append acc []
      | (App1 (UQiS_U1 a) q) :: t => 
          match combine_U_equivalence l q with
          | None => combine_U_equivalences' t n' (U1 a q :: acc)
          | Some l' => combine_U_equivalences' l' n' acc
          end
      | g :: t => combine_U_equivalences' t n' (g :: acc)
      end
  end.

Definition optimize1qgate {dim} (l : QiS_ucom_l dim) := 
  combine_U_equivalences' l (3 * (length l)) [].


