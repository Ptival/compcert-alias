Require Import BinPos.
Require Import EquivDec.
Require Import Omega.
Require Import OrderedType.

Require Import AST.
Require Import Integers.
Require Import RTL.

(* Abstract blocks:
                 All
           /       |     \
      Nonlocal   Stack   Allocs
     /      \            /  |  \
   Globs   Other
  /  |  \
*)

Inductive ablock :=
| All
| Nonlocal
| Globals
| Global: ident -> ablock
| Other
| Stack
| Allocs
| Alloc: node  -> ablock
.

Definition ablock_eqdec (x y : ablock) : { x = y } + { x <> y }.
Proof.
  destruct x, y; try solve [now left | now right].
  destruct (ident_eq i i0). left. now f_equal. right. intro. elim n. now inversion H.
  destruct (ident_eq n n0). left. now f_equal. right. intro. elim n1. now inversion H.
Defined.

Program Instance ablock_eqdec_instance : EqDec ablock eq := ablock_eqdec.

Definition ablock_parent (b : ablock) : option ablock :=
  match b with
  | All => None
  | (Nonlocal | Stack | Allocs) => Some All
  | (Globals | Other) => Some Nonlocal
  | Global _ => Some Globals
  | Alloc _ => Some Allocs
  end.

(* We need an OrderedType for using these with maps, however this is not the
 order we will otherwise consider, as this one needs to be total. *)

Module ablockOT <: OrderedType.

  Definition t := ablock.

  Definition eq := @eq t.

  Definition eq_refl := @refl_equal t.

  Definition eq_sym := @sym_eq t.

  Definition eq_trans := @trans_eq t.

  Definition eq_dec : forall x y, {eq x y} + {~ eq x y} := ablock_eqdec.

  (* some meaningless and arbitrary order... *)
  Definition lt (x y : t) : Prop :=
    match x with
    | All =>
      match y with All => False | _ => True end
    | Nonlocal =>
      match y with (All | Nonlocal) => False | _ => True end
    | Globals =>
      match y with (All | Nonlocal | Globals) => False | _ => True end
    | Global g0 =>
      match y with
      | (All | Nonlocal | Globals) => False
      | Global g1 => (g0 < g1)%positive
      | _ => True
      end
    | Other =>
      match y with (All | Nonlocal | Globals | Global _ | Other) => False | _ => True end
    | Stack =>
      match y with
      | (All | Nonlocal | Globals | Global _ | Other | Stack) => False
      | _ => True
      end
    | Allocs =>
      match y with
      | (All | Nonlocal | Globals | Global _ | Other | Stack | Allocs) => False
      | _ => True
      end
    | Alloc a0 =>
      match y with
      | (All | Nonlocal | Globals | Global _ | Other | Stack | Allocs) => False
      | Alloc a1 => (a0 < a1)%positive
      end
    end.

  Theorem lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    destruct x, y, z; intuition;
    repeat (
      match goal with
      | [ i : ident |- _ ] => destruct i
      | [ n : node |- _ ] => destruct n
      end
    ); simpl in *; zify; omega.
  Qed.

  Theorem lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    repeat intro. inversion H0. subst.
    destruct y; intuition (try congruence);
    repeat (
      match goal with
      | [ i : ident |- _ ] => destruct i
      | [ n : node |- _ ] => destruct n
      end
    ); simpl in *; zify; omega.
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    destruct x, y; try first [now apply EQ | now apply LT | now apply GT].
    destruct (Pcompare i i0 Eq) as []_eqn.
    apply EQ. apply Pcompare_eq_iff in Heqc. now subst.
    apply LT. auto.
    apply GT. unfold lt, BinPos.Plt.
    pose proof (Pcompare_antisym i i0 Eq). rewrite Heqc in H. now simpl.
    destruct (Pcompare n n0 Eq) as []_eqn.
    apply EQ. apply Pcompare_eq_iff in Heqc. now subst.
    apply LT. auto.
    apply GT. unfold lt, BinPos.Plt.
    pose proof (Pcompare_antisym n n0 Eq). rewrite Heqc in H. now simpl.
  Qed.

End ablockOT.

(* now defining the actual partial order of abstract blocks *)

Fixpoint lt (x y: ablock) : Prop :=
  match x with
  | All => False
  | (Nonlocal | Stack | Allocs) =>
    match y with All => True | _ => False end
  | (Globals | Other) =>
    match y with (All | Nonlocal) => True | _ => False end
  | Global _ =>
    match y with (All | Nonlocal | Globals) => True | _ => False end
  | Alloc _ =>
    match y with (All | Allocs) => True | _ => False end
  end.

Inductive aloc :=
| Blk : ablock -> aloc
| Loc : ablock -> Int.int -> aloc
.

Definition aloc_parent (l : aloc) : option aloc :=
  match l with
  | Loc b o => Some (Blk b)
  | Blk b =>
    match ablock_parent b with
    | None => None
    | Some b => Some (Blk b)
    end
  end.