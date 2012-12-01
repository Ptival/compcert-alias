Require Import List.

Require Import Kildall.
Require Import Lattice.
Require Import Maps.
Require Import RTL.

Require Import AliasAbstract.
Require Import AliasMemMap.
Require Import AliasRegMap.
Require Import AliasTransfer.

Module Result <: SEMILATTICE.

  Definition t := result.

  Variable eq: t -> t -> Prop.

  Hypothesis eq_refl: forall x, eq x x.

  Hypothesis eq_sym: forall x y, eq x y -> eq y x.

  Hypothesis eq_trans: forall x y z, eq x y -> eq y z -> eq x z.

  Variable beq: t -> t -> bool.

  Hypothesis beq_correct: forall x y, beq x y = true -> eq x y.

  Definition ge (x y : t) :=
    match x, y with
    | (rmap, mmap), (rmap', mmap') => RegMap.ge rmap rmap' /\ MemMap.ge mmap mmap'
    end.

  Hypothesis ge_refl: forall x y, eq x y -> ge x y.

  Hypothesis ge_trans: forall x y z, ge x y -> ge y z -> ge x z.

  Variable bot: t.

  Hypothesis ge_bot: forall x, ge x bot.

  Variable lub: t -> t -> t.

  Hypothesis ge_lub_left: forall x y, ge (lub x y) x.

  Hypothesis ge_lub_right: forall x y, ge (lub x y) y.

End Result.

Module Solver := Dataflow_Solver(Result)(NodeSetForward).

(* At function entry, be conservative about parameter registers *)
Definition entry_rmap reglist :=
  let add_reg_top rmap r := RegMap.add r PTSet.top rmap in
  fold_left add_reg_top reglist RegMap.bot.

(* At function entry, be conservative about non-local blocks *)
Definition entry_mmap :=
  MemMap.add (Blk Nonlocal) PTSet.top MemMap.bot.

Definition entry_result l := (entry_rmap l, entry_mmap).

Definition failure_prone_analysis f :=
  Solver.fixpoint (successors f) (transf (fn_code f))
  ((fn_entrypoint f, entry_result (fn_params f)) :: nil).

Definition analysis f :=
  match failure_prone_analysis f with
  | Some res => res
  | None     => PMap.init (RegMap.top, MemMap.top)
  end.
