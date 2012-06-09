Require Import AliasHierarchy.

Module Type HSet (H: Hierarchy).
  Parameter t: Type.
  Parameter bot: t.
  Parameter top: t.
  Parameter add: H.t -> t -> t.
  Parameter In: H.t -> t -> Prop.
  Axiom In_add_spec: forall x y s,
    In x (add y s) <-> x = y \/ H.above y x \/ In x s.
  (*Parameter mem: forall x s, {In x s} + {~In x s}.*)
  Definition eq (s1 s2: t): Prop := forall x, In x s1 <-> In x s2.

(*
  Axiom In_add_same: forall x s, In x (add x s).
  Axiom In_add_hierarchy: forall x y,
    H.hierarchy x y -> (forall s, In y (add x s)).
  Axiom In_add_already: forall x y s, In x s -> In x (add y s).
*)
  Definition singleton x := add x bot.
(*
  Axiom In_singleton: forall x, In x (singleton x).
  Axiom In_singleton_hierarchy: forall x y,
    H.hierarchy x y -> In y (singleton x).
*)
End HSet.