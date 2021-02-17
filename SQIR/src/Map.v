Require Export MapS.
Require Import Coq.FSets.FMapList.

Module Make (X : OrderedType) <: MapS.S X.
  Include FMapList.Make X.

  Section elt.
    Variable elt : Type.

    Lemma find_add : forall k v m,
        find (elt := elt) k (add k v m) = Some v.
    Proof.
      intros.
      apply find_1.
      apply add_1.
      apply E.eq_refl.
    Qed.

    Lemma mapsto_add1 : forall k v1 v2 s,
        MapsTo (elt := elt) k v1 (add k v2 s) -> v1 = v2.
    Proof.
      intros.
      apply find_1 in H.
      rewrite find_add in H.
      inversion H.
      reflexivity.
    Qed.

    Lemma mapsto_always_same : forall k v1 v2 s,
           MapsTo (elt := elt) k v1 s ->
            MapsTo (elt := elt) k v2 s -> 
                       v1 = v2.
    Proof.
     intros.
     apply find_1 in H.
     apply find_1 in H0.
     rewrite H in H0.
     injection H0.
     easy.
    Qed.

    Lemma mapsto_add2 : forall k1 k2 v1 v2 s,
        MapsTo (elt := elt) k1 v1 (add k2 v2 s) ->
        ~ E.eq k1 k2 ->
        MapsTo k1 v1 s.
    Proof.
      intros.
      apply add_3 with (x := k2) (e' := v2).
      unfold not.
      intros.
      apply H0.
      symmetry.
      assumption.
      assumption.
    Qed.

    Lemma mapsto_equal : forall k v s1 s2,
        MapsTo (elt := elt) k v s1 ->
        Equal s1 s2 ->
        MapsTo k v s2.
    Proof.
      intros.
      unfold Equal in H0.
      apply find_2. rewrite <- H0.
      apply find_1.
      assumption.
    Qed.

  End elt.
End Make.