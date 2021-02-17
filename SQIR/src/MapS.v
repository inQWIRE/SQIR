Require Export Coq.FSets.FMapInterface.

Module Type S (X : OrderedType).
  Include FMapInterface.Sfun X.

  Section elt.
    Variable elt : Type.

    Parameter find_add : forall k v m,
        find (elt := elt) k (add k v m) = Some v.

    Parameter mapsto_add1 : forall k v1 v2 s,
        MapsTo (elt := elt) k v1 (add k v2 s) -> v1 = v2.

    Parameter mapsto_add2 : forall k1 k2 v1 v2 s,
        MapsTo (elt := elt) k1 v1 (add k2 v2 s) ->
        ~X.eq k1 k2 ->
        MapsTo k1 v1 s.

    Parameter mapsto_equal : forall k v s1 s2,
        MapsTo (elt := elt) k v s1 ->
        Equal s1 s2 ->
        MapsTo k v s2.

  End elt.
End S.