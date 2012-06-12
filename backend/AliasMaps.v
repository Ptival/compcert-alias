Require Import AliasHierarchy.
Require Import OrderedType.
Require Import Lattice.

Module Type RelMap (R: Relationship) (L: SEMILATTICE).
  Parameter t: Type.
  Parameter get: R.t -> t -> L.t.
  Parameter add: R.t -> L.t -> t -> t.
  (* set should only work for keys at the bottom of the hierarchy *)
  (* set still needs to propagate information upwards *)
  (*
    Parameter set: O.t -> L.t -> t -> t.
  *)
  Axiom get_add_same: forall k s m, L.ge (get k (add k s m)) s.
  Axiom get_add: forall x y s m, L.ge (get x (add y s m)) (get x m).
  Axiom get_add_related: forall x y s m,
    R.related x y ->
    L.ge (get x (add y s m)) s.
  (*
  Axiom get_set_same: forall k s m, L.ge (get k (set k s m)) s.
  Axiom get_set_other: forall x y s m, L.ge (get x (set y s m)) (get x m).
  *)
End RelMap.