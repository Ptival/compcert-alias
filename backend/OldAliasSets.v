Require Import AliasHierarchy.

Module Type HSet (H: Hierarchy).
  Parameter t: Type.
  Parameter bot: t.
  Parameter top: t.
  Parameter add: H.t -> t -> t.
  Parameter In: H.t -> t -> Prop.
  Axiom In_add_spec: forall x y s,
    In x (add y s) <-> x = y \/ H.above y x \/ In x s.
  Definition eq (s1 s2: t): Prop := forall x, In x s1 <-> In x s2.
  Definition singleton x := add x bot.
End HSet.