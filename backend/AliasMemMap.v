Require Import AliasAbstract.
Require Export AliasPTMap.

Module MemMap <: PTMap.

  Definition k := aloc.

  Axiom t : Type.

  Axiom top : t.

  Axiom bot : t.

  Axiom get : aloc -> t -> PTSet.t.

  Axiom add : aloc -> PTSet.t -> t -> t.

  Definition ge m m' :=
    forall key, PTSet.ge (get key m) (get key m').

  Axiom ge_refl : forall m, ge m m.

  Axiom ge_trans : forall a b c, ge a b -> ge b c -> ge a c.

  Axiom ge_add: forall k v m, ge (add k v m) m.

  Axiom get_ge: forall m m',
    ge m m' ->
    (forall k, PTSet.ge (get k m) (get k m')).

  Axiom get_add_same: forall k v m, PTSet.ge (get k (add k v m)) v.

  Axiom get_top: forall k, PTSet.ge (get k top) PTSet.top.

  Axiom ge_top : forall m, ge top m.

  (* specific to MemMap *)
  Axiom get_add_lt : forall x y s m, aloc_lt x y -> PTSet.ge (get x (add y s m)) s.

End MemMap.