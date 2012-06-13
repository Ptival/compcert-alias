Require Import AliasHierarchy.
Require Import OrderedType.
Require Import Lattice.

Module Type OverlapMap (O: Overlap) (L: SEMILATTICE).
  Parameter t: Type.
  Parameter get: O.t -> t -> L.t.
  Parameter add: O.t -> L.t -> t -> t.
  (* set should only work for keys at the bottom of the hierarchy *)
  (* set still needs to propagate information upwards *)
  (*
    Parameter set: O.t -> L.t -> t -> t.
  *)
  Axiom get_add_same: forall k s m, L.ge (get k (add k s m)) s.
  Axiom get_add: forall x y s m, L.ge (get x (add y s m)) (get x m).
  Axiom get_add_overlap: forall x y s m,
    O.overlap x y ->
    L.ge (get x (add y s m)) s.
  (*
  Axiom get_set_same: forall k s m, L.ge (get k (set k s m)) s.
  Axiom get_set_other: forall x y s m, L.ge (get x (set y s m)) (get x m).
  *)
End OverlapMap.