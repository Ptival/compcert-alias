Require Import AliasAbstract.

Module Type PTSetT.

  Definition elt := aloc.

  Parameter Inline t : Set.

  Parameter bot : t.

  Parameter top : t.

  Parameter add : elt -> t -> t.

  Parameter singleton : elt -> t.

  Parameter fold : forall {x}, (elt -> x -> x) -> t -> x -> x.

  Parameter join : t -> t -> t.

  Parameter In : elt -> t -> Prop.

  Axiom In_add : forall x s, In x s -> forall y, In x (add y s).

  Axiom In_add_same : forall x s, In x (add x s).

  Axiom In_add_lt : forall x y s, aloc_lt x y -> In x (add y s).

  Axiom fold_preserves_prop:
    forall S (P : S -> Prop) (f : _ -> S -> S) s x,
      P x ->
      (forall x y, P x -> P (f y x)) ->
      P (fold f s x).

  Axiom fold_adds_prop:
    forall S (P : S -> Prop) (f : _ -> S -> S) e s x,
      In e s ->
      (forall x, P (f e x)) ->
      (forall x y, P x -> P (f y x)) ->
      P (fold f s x).

  Axiom In_top : forall x, In x top.

  Axiom In_singleton : forall x, In x (singleton x).

  Definition ge s s' :=
    forall elt, In elt s' -> In elt s.

  Axiom ge_refl : forall s, ge s s.

  Axiom ge_trans : forall a b c, ge a b -> ge b c -> ge a c.

  Axiom ge_join_l : forall a b, ge (join a b) a.

  Axiom ge_join_r : forall a b, ge (join a b) b.

  Axiom loc_In_add_blk : forall b o s, In (Loc b o) (add (Blk b) s).

  Axiom for_all : (elt -> bool) -> t -> bool.

  Definition For_all (P : elt -> Prop) s :=
    forall x, In x s -> P x.

  Axiom for_all_iff : forall f s, For_all (fun x => f x = true) s <-> for_all f s = true.

End PTSetT.

Module PTSet <: PTSetT.

  Definition elt := aloc.

  Axiom t : Set.

  Axiom bot : t.

  Axiom top : t.

  Axiom add : aloc -> t -> t.

  Definition singleton x := add x bot.

  Axiom fold : forall {x}, (aloc -> x -> x) -> t -> x -> x.

  Axiom join : t -> t -> t.

  Axiom In : elt -> t -> Prop.

  Axiom In_add : forall x s, In x s -> forall y, In x (add y s).

  Axiom In_add_same : forall x s, In x (add x s).

  Axiom In_add_lt : forall x y s, aloc_lt x y -> In x (add y s).

  Axiom fold_preserves_prop:
    forall S (P : S -> Prop) (f : _ -> S -> S) s x,
      P x ->
      (forall x y, P x -> P (f y x)) ->
      P (fold f s x).

  Axiom fold_adds_prop:
    forall S (P : S -> Prop) (f : _ -> S -> S) e s x,
      In e s ->
      (forall x, P (f e x)) ->
      (forall x y, P x -> P (f y x)) ->
      P (fold f s x).

  Axiom In_top : forall x, In x top.

  Axiom In_singleton : forall x, In x (singleton x).

  Definition ge s s' :=
    forall elt, In elt s' -> In elt s.

  Axiom ge_refl : forall s, ge s s.

  Axiom ge_trans : forall a b c, ge a b -> ge b c -> ge a c.

  Axiom ge_join_l : forall a b, ge (join a b) a.

  Axiom ge_join_r : forall a b, ge (join a b) b.

  Axiom loc_In_add_blk : forall b o s, In (Loc b o) (add (Blk b) s).

  Axiom for_all : (elt -> bool) -> t -> bool.

  Definition For_all (P : elt -> Prop) s :=
    forall x, In x s -> P x.

  Axiom for_all_iff : forall f s, For_all (fun x => f x = true) s <-> for_all f s = true.

End PTSet.
