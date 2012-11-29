Require Import AST.
Require Import Coqlib.
Require Import FMapAVL.
Require FMapFacts.
Require Import FMapInterface.
Require FSetFacts.
Require Import Globalenvs.
Require Import Integers.
Require Import Lattice.
Require Import List.
Require Import Maps.
Require Import Memory.
Require Import Op.
Require Import Kildall.
Require Import Registers.
Require Import Relations.
Require Import RTL.
Require Import Values.

Require Import AliasFMapAVLPlus.
Require Import AliasHierarchy.
Require Import AliasLattices.
Require Import AliasLib.
Require Import AliasMapLattice.
Require Import AliasMaps.
Require Import AliasSets.

Lemma fold_left_preserves_prop:
  forall S F (P: S -> Prop) (f: S -> F -> S) l s,
    P s ->
    (forall x y, P x -> P (f x y)) ->
    P (fold_left f l s).
Proof.
  induction l; simpl; auto.
Qed.

Lemma fold_left_adds_prop:
  forall E S (e: E) (P: S -> Prop) (f: S -> E -> S) l s0 eq',
    InA eq' e l ->
    (forall x y, eq' x y -> x = y) ->
    (forall x, P (f x e)) ->
    (forall x y, P x -> P (f x y)) ->
    P (fold_left f l s0).
Proof.
  induction l; intros.
  inversion H.
  inversion_clear H. apply H0 in H3. subst.
  simpl. apply fold_left_preserves_prop; auto.
  eapply IHl; eauto.
Qed.

(* Abstract blocks *)

Inductive absb' :=
| Allocs:  option node  -> absb'
| Globals: option ident -> absb'
| Other
| Stack
.

Definition absb := option absb'. (* None := All *)

Hint Unfold absb: unalias.
Notation All := None (only parsing).
Notation Just := Some (only parsing).

Module AbsBOT <: OrderedType.

  Definition t := absb.

  Definition eq := @eq t.

  Definition eq_refl := @refl_equal t.

  Definition eq_sym := @sym_eq t.

  Definition eq_trans := @trans_eq t.

  Definition eq_dec : forall x y, {eq x y}+{~eq x y}.
  Proof.
    unfold eq. destruct x, y; repeat decide equality. left. auto.
  Qed.

  Definition lt (x y: t) : Prop :=
    match x, y with
    | All,    All    => False
    | _,      All    => True
    | All,    _      => False
    | Just a, Just b =>
      match a, b with
      | Allocs (Just n1),  Allocs (Just n2)                         => (n1 < n2)%positive
      | Allocs (Just _),   (Allocs All | Globals _ | Other | Stack) => True
      | Allocs All,        (Globals _ | Other | Stack)              => True
      | Globals (Just g1), Globals (Just g2)                        => (g1 < g2)%positive
      | Globals (Just _),  (Globals _ | Other | Stack)              => True
      | Globals All,       (Other | Stack)                          => True
      | Other,             Stack                                    => True
      | _,                 _                                        => False
      end
    end.

  Theorem lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    intros.
    destruct x, y, z;
    try destruct a; try destruct a0; try destruct a1;
    try destruct o; try destruct o0; try destruct o1;
    auto; simpl in *; zify; omega.
  Qed.

  Theorem lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    repeat intro. inv H0. destruct y; simpl in H; auto.
    destruct a; auto; destruct o; auto;  zify; omega.
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros. unfold lt.
    destruct x, y;
    try destruct a, a0;
    try destruct o; try destruct o0;
    try solve [apply LT; auto|apply EQ; reflexivity|apply GT; auto].
    destruct (Pcompare n n0 Eq) as []_eqn.
    apply Pcompare_eq_iff in Heqc; subst; apply EQ; reflexivity.
    apply LT. auto.
    pose proof (Pcompare_antisym n n0 Eq). unfold CompOpp in *.
    apply GT; rewrite Heqc in H.
    unfold BinPos.Plt. auto.
    destruct (Pcompare i i0 Eq) as []_eqn.
    apply Pcompare_eq_iff in Heqc; subst; apply EQ; reflexivity.
    apply LT; auto.
    pose proof (Pcompare_antisym i i0 Eq). unfold CompOpp in *.
    apply GT; rewrite Heqc in H.
    unfold BinPos.Plt. auto.
  Qed.

End AbsBOT.

Module AbsBHFun <: HierarchyFun.
  Definition t := absb.

  Definition eq_dec: forall (x y: t), {eq x y} + {~ eq x y}.
  Proof.
    repeat decide equality.
  Qed.

  Definition top: t := None.

  Definition parent x :=
    match x with
    | All    => None
    | Just a => Some (
      match a with
      | Allocs (Just _)  => Just (Allocs All)
      | Globals (Just _) => Just (Globals All)
      | _                => All
      end
    )
    end.

  Definition measure x :=
    (
      match x with
      | All    => 0
      | Just a =>
        match a with
        | Allocs (Just _)  => 2
        | Globals (Just _) => 2
        | _                => 1
        end
      end
    )%nat.

  Ltac crunch_absb :=
    repeat (
      simpl in *; try easy;
      match goal with
      | H: Some _ = None |- _ => inv H
      | H: None = Some _ |- _ => inv H
      | H: Some _ = Some _ |- _ => inv H
      | x: option _ |- _ => destruct x
      | x: absb' |- _ => destruct x
      end
    ); intuition.

  Theorem parent_measure: forall x px,
    parent x = Some px -> (measure px < measure x)%nat.
  Proof.
    repeat crunch_absb.
  Qed.

  Theorem no_parent_is_top: forall x,
    parent x = None <-> x = top.
  Proof.
    repeat crunch_absb.
  Qed.

End AbsBHFun.

Inductive optint {t: Type}: Type :=
| Blk: t -> optint
| Loc: t -> Int.int -> optint
.
Definition absp := @optint absb.

Module OptIntHFun (H: HierarchyFun) <: HierarchyFun.

  Definition t:= @optint H.t.
  Hint Unfold t: unalias.

  Definition eq_dec: forall (x y: t), {eq x y} + {~ eq x y}.
  Proof.
    repeat decide equality; try apply H.eq_dec; apply Int.eq_dec.
  Qed.

  Definition top: t := Blk H.top.

  Definition parent x :=
    match x with
    | Loc b _ => Some (Blk b)
    | Blk b   =>
      match H.parent b with
      | Some pb => Some (Blk pb)
      | None    => None
      end
    end.

  Definition measure x :=
    (
    match x with
    | Loc b _ => 1 + H.measure b
    | Blk b   => H.measure b
    end
    )%nat.

  Theorem parent_measure: forall x px,
    parent x = Some px -> (measure px < measure x)%nat.
  Proof.
    intros. destruct x; simpl in *.
    destruct (H.parent t0) as []_eqn; inversion_clear H.
    now apply H.parent_measure.
    inversion_clear H. auto.
  Qed.

  Theorem no_parent_is_top: forall x, parent x = None <-> x = top.
  Proof.
    intros. destruct x; simpl in *.
    destruct (H.parent t0) as []_eqn.
    split. congruence. intros. inversion H. subst.
    pose proof (H.no_parent_is_top H.top). intuition. congruence.
    intuition. apply H.no_parent_is_top in Heqo. now inversion_clear Heqo.
    now intuition.
  Qed.

End OptIntHFun.

Module AbsPHFun := OptIntHFun(AbsBHFun).

Module AbsPH := MkHierarchy(AbsPHFun).

Theorem not_loc_above: forall b o x,
  ~ AbsPH.above (Loc b o) x.
Proof.
  repeat intro. apply clos_trans_t1n_iff in H.
  remember (Loc b o) as l. induction H.
  subst. compute in H.
  destruct y; try solve [inv H]. destruct t; try solve [inv H].
  subst. compute in H.
  destruct y; try solve [inv H]. destruct t; try solve [inv H].
Qed.

Module AbsPO <: Overlap.
  Include AbsPH.

  Module AbsBH := MkHierarchy(AbsBHFun).
  Module AbsBO := HtoO(AbsBH).

  Definition overlap (x y: t): Prop :=
    match x, y with
    | Blk blx,   Blk bly
    | Blk blx,   Loc bly _
    | Loc blx _, Blk bly
      => AbsBO.overlap blx bly
    | Loc blx ox, Loc bly oy
      => ox = oy /\ AbsBO.overlap blx bly
    end.

  Definition overlap_dec: forall x y, {overlap x y} + {~ overlap x y}.
  Proof.
    intros.
    destruct x, y; unfold overlap; try solve [apply AbsBO.overlap_dec].
    destruct (Int.eq_dec i i0); destruct (AbsBO.overlap_dec t0 t1); intuition.
  Qed.

  Instance overlap_refl: Reflexive overlap.
  Proof.
    intro. destruct x; unfold overlap; intuition.
  Qed.

  Instance overlap_sym: Symmetric overlap.
  Proof.
    repeat intro. destruct x, y; simpl in *; intuition.
  Qed.

  Lemma relate_above_overlap: forall a b,
    clos_trans t (fun y x : t => parent x = Some y) a b ->
    match a, b with
    | Blk ba,   Blk bb   => clos_trans _ AbsBH.is_parent ba bb
    | Blk ba,   Loc bb _ => clos_trans _ AbsBH.is_parent ba bb \/ ba = bb
    | Loc ba _, _        => False
    end.
  Proof.
    induction 1; intros. destruct y; simpl in H.
    destruct (AbsBHFun.parent t0) as []_eqn; inv H.
    constructor. auto.
    inv H. right. auto.
    destruct x, y, z; try contradiction.
    eapply t_trans; eauto.
    intuition.
    left. eapply t_trans; eauto.
    subst. auto.
  Qed.

  Theorem above_overlaps: forall x y,
    above x y -> overlap x y.
  Proof.
    intros.
    unfold above, is_parent, overlap, AbsBO.overlap, AbsBO.above in *.
    pose proof (relate_above_overlap _ _ H).
    destruct x, y; intuition.
  Qed.

  Lemma parent_overlaps_aux: forall x y px,
    AbsBO.overlap x y ->
    AbsBHFun.parent x = Some px ->
    AbsBO.overlap px y.
  Proof.
    intros. induction H.
    subst. right. left. constructor. auto.
    unfold AbsBO.overlap. intuition.
    right. left. eapply t_trans. constructor; eauto. auto.
    destruct (AbsBO.eq_dec px y).
    auto.
    right. right. eapply wf_tc_common_ancestor; eauto.
    intros. unfold AbsBH.is_parent in *. rewrite H2 in H. inv H. auto.
  Qed.

  Theorem parent_overlaps_too: forall x y px,
    parent x = Some px ->
    overlap x y ->
    overlap px y.
  Proof.
    intros ??? P O.
    destruct x, y; simpl in *; try solve [
      destruct (AbsBHFun.parent t0) as []_eqn; inv P; simpl;
        eapply parent_overlaps_aux; eauto
    ].
    destruct px; simpl in *; inv P; intuition.
    destruct px; simpl in *; inv P; intuition.
  Qed.

End AbsPO.

Ltac crunch_hierarchy :=
  unfold AbsPO.t, AbsPHFun.t, AbsBHFun.t, AbsPO.overlap in *;
  simpl in *;
  try discriminate; try tauto;
  match goal with
  | b: absb |- _ => destruct b; crunch_hierarchy
  | b: absb' |- _ => destruct b; crunch_hierarchy
  | o: option _ |- _ => destruct o; crunch_hierarchy
  | p: optint |- _ => destruct p; crunch_hierarchy
  | H: Some _ = Some _ |- _ => inv H; crunch_hierarchy
  | H: _ \/ _ |- _ => destruct H; crunch_hierarchy
  | |- _ => idtac
  end.

(*
Theorem absp_strong_ind: forall (P: absp -> Prop),
  P AbsPR.top ->
  (forall x, (forall y, AbsPR.above y x -> P y) -> P x) ->
  (forall x, P x).
Proof.
  intros. destruct x; repeat (crunch_hierarchy; apply H0; intros).
Qed.
*)

Module Type OrderedTypeLogicEq <: OrderedType.

  Parameter Inline t : Type.

  Definition eq := @eq t.
  Parameter Inline lt : t -> t -> Prop.

  Axiom eq_refl : forall x : t, eq x x.
  Axiom eq_sym : forall x y : t, eq x y -> eq y x.
  Axiom eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.

  Axiom lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Axiom lt_not_eq : forall x y : t, lt x y -> ~ eq x y.

  Parameter compare : forall x y : t, Compare lt eq x y.

  Hint Immediate eq_sym.
  Hint Resolve eq_refl eq_trans lt_not_eq lt_trans.

  Parameter eq_dec : forall x y, { eq x y } + { ~ eq x y }.

End OrderedTypeLogicEq.

Module OptIntOT (OT: OrderedTypeLogicEq) <: OrderedTypeLogicEq.

  Definition t := @optint OT.t.

  Definition eq := @eq t.

  Definition eq_refl: forall (x: t), eq x x := fun x => eq_refl x.

  Theorem eq_sym: forall x y, eq x y -> eq y x.
  Proof.
    apply eq_sym.
    (*intros. destruct x, y; simpl in *; intuition; auto.*)
  Qed.

  Theorem eq_trans: forall (x y z: t), eq x y -> eq y z -> eq x z.
  Proof.
    apply eq_trans.
  Qed.

  Definition eq_dec : forall (x y: t), {x = y} + {x <> y}.
  Proof.
    unfold eq.
    destruct x, y; repeat decide equality; auto;
      try solve [apply OT.eq_dec | apply Int.eq_dec].
  Qed.

  Definition lt (x y: t) : Prop :=
    match x, y with
    | Blk a,   Blk b   => OT.lt a b
    | Loc a x, Loc b y => OT.lt a b \/ (OT.eq a b /\ Int.lt x y = true)
    | Loc _ _, Blk _   => True
    | Blk _,   Loc _ _ => False
    end.

  Theorem lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    intros. destruct x, y, z; simpl in *; intuition; subst; auto.
    eapply OT.lt_trans; eauto.
    left. eapply OT.lt_trans; eauto.
    left. destruct (OT.compare t0 t2). auto.
    exfalso. eapply OT.lt_not_eq; eauto.
    exfalso. eapply OT.lt_not_eq. eapply OT.lt_trans; eauto. apply OT.eq_sym. auto.
    left. destruct (OT.compare t0 t2). auto.
    exfalso. eapply OT.lt_not_eq; eauto.
    exfalso. eapply OT.lt_not_eq. apply OT.lt_trans with (y:=t2); eauto. apply OT.eq_sym.
    auto.
    right. split. eapply OT.eq_trans; eauto. unfold Int.lt in *. repeat destruct zlt; auto.
    omegaContradiction.
  Qed.

  Theorem lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    destruct x, y; simpl in *; intuition;
      try solve [inv H0; eapply OT.lt_not_eq; eauto].
    inv H. inv H0. unfold Int.lt in *. destruct zlt. omega. congruence.
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros. unfold lt. destruct x, y.
    destruct (OT.compare t0 t1). apply LT. auto. inv e. apply EQ. reflexivity. apply GT. auto.
    apply GT. auto.
    apply LT. auto.
    destruct (OT.compare t0 t1). apply LT. auto.
    destruct (Int.lt i i0) as []_eqn.
    apply LT. right. split. apply e. auto.
    destruct (Int.eq_dec i i0).
    inv e. subst. apply EQ. simpl. reflexivity.
    apply GT. right. split. auto. unfold Int.lt in *. repeat (destruct zlt); auto.
    assert (SEQ: Int.signed i = Int.signed i0) by omega.
    apply (f_equal Int.repr) in SEQ. setoid_rewrite Int.repr_signed in SEQ. contradiction.
    apply GT. auto.
  Qed.

End OptIntOT.

Module AbsPOT := OptIntOT(AbsBOT).

Ltac merge_parents :=
  repeat (
    match goal with
      | H: AbsPH.parent ?x = _,
        G: AbsPH.parent ?x = _
        |- _ => rewrite G in H; inv H
    end
  ).

Module Type SEMILATTICE_EXTENDED.

  Include SEMILATTICE_WITH_TOP.

  Axiom lub_inc_l: forall a b, ge a b -> forall v, ge (lub v a) (lub v b).

  Axiom ge_lub: forall a b c d, ge a b -> ge c d -> ge (lub a c) (lub b d).

  Axiom lub_bot: forall a b, eq a bot -> eq b bot -> eq (lub a b) bot.

  Axiom bot_ge: forall x, ge bot x <-> eq bot x.

  Axiom ge_antisym: forall a b, ge a b -> ge b a -> eq a b.

End SEMILATTICE_EXTENDED.

Module PTSet
  <: HSet(AbsPH)
  <: SEMILATTICE_EXTENDED.

  Module AbsPSet := FSetAVL.Make AbsPOT.

  Module F := FSetFacts.WFacts_fun AbsPOT AbsPSet.

  Definition t := AbsPSet.t.

  Definition add := AbsPSet.add.

  Function In (x: AbsPH.t) (s: t) {measure AbsPH.measure x}: Prop :=
    match AbsPH.parent x with
    | Some px => AbsPSet.In x s \/ In px s
    | None    => AbsPSet.In x s
    end.
  Proof.
    intros ??? H. exact (AbsPH.parent_measure _ _ H).
  Qed.

  Lemma In_add_same: forall x s, In x (add x s).
  Proof.
    intros. remember (add x s) as s'. functional induction (In x s').
    left. apply F.add_iff. destruct x; auto.
    apply F.add_iff. destruct x; auto.
  Qed.

  Module HF := HierarchyFacts(AbsPH).

  Theorem In_add_spec: forall x y s,
    In x (add y s) <-> x = y \/ AbsPH.above y x \/ In x s.
  Proof.
    split; intros.
    Case "->".
    induction x using AbsPH.above_ind.
    remember (add y s) as s'.
    functional induction (In x s').
    SCase "1".
    intuition.
    apply F.add_iff in H1. destruct x, y; intuition.
    right. right. functional induction (In (Blk t0) s); auto.
    right. right. functional induction (In (Blk t0) s); auto.
    right. right. functional induction (In (Loc t0 i) s); auto.
    right. right. functional induction (In (Loc t0 i) s); auto.
    specialize (H0 px (AbsPH.parent_is_above _ _ e) H1).
    intuition; subst.
    right. left. exact (AbsPH.parent_is_above _ _ e).
    right. left. eapply transitivity. apply H0.
    exact (AbsPH.parent_is_above _ _ e).
    right. right.
    functional induction (In x s); merge_parents; auto.
    SCase "2".
    apply F.add_iff in H.
    destruct y, x; intuition; subst; auto;
      try solve [right; right;
        match goal with |- ?goal => functional induction goal end; auto].
    Case "<-".
    intuition.
    SCase "1".
    subst. apply In_add_same.
    SCase "2".
    remember (add y s) as s'. functional induction (In x s').
    right.
    destruct (AbsPH.eq_dec y px).
    subst. apply In_add_same.
    refine (IHP _ (eq_refl _)).
    exact (AbsPH.no_lozenge _ _ _ H e n).
    apply AbsPH.no_parent_is_top in e. subst.
    elim (HF.not_above_top _ H).
    SCase "3".
    remember (add y s) as s'.
    functional induction (In x s); functional induction (In x s');
      merge_parents; intuition.
    left. apply F.add_iff. right. auto.
    apply F.add_iff. right. auto.
  Qed.

  Theorem In_spec_aux:
    forall x s,
      In x s <->
      AbsPSet.In x s \/
      (exists px, AbsPH.parent x = Some px /\ In px s).
  Proof.
    split; intros.
    functional induction (In x s).
    destruct H; auto. right. exists px. auto.
    auto.
    functional induction (In x s).
    destruct H; auto. destruct H as [px' [A B]]. rewrite A in e; inv e. auto.
    destruct H; auto. destruct H as [px' [A B]]. rewrite A in e; inv e.
  Qed.

  Theorem In_spec:
    forall x s,
      In x s <->
      AbsPSet.In x s \/
      (exists ax, AbsPH.above ax x /\ AbsPSet.In ax s).
  Proof.
    split.
    Case "->".
    intros.
    apply In_spec_aux in H. intuition. destruct H0 as [px [P H]].
    right.
    apply In_spec_aux in H. intuition.
    exists px. split. apply AbsPH.parent_is_above. exact P. exact H0.
    destruct H0 as [ppx [PP H]].
    apply In_spec_aux in H. intuition.
    exists ppx. split.
    apply transitivity with (y := px).
    apply AbsPH.parent_is_above. exact PP.
    apply AbsPH.parent_is_above. exact P.
    exact H0.
    destruct H0 as [pppx [PPP H]].
    apply In_spec_aux in H. intuition.
    exists pppx. split.
    apply transitivity with (y := ppx).
    apply AbsPH.parent_is_above. exact PPP.
    apply transitivity with (y := px).
    apply AbsPH.parent_is_above. exact PP.
    apply AbsPH.parent_is_above. exact P.
    exact H0.
    destruct H0 as [ppppx [PPPP H]]. crunch_hierarchy.
    Case "<-".
    intros. intuition. functional induction (In x s); intuition.
    destruct H0 as [ax [ABOVE IN]].
    functional induction (In x s).
    right.
    destruct (AbsPH.eq_dec ax px).
    subst. functional induction (In px s); intuition.
    refine (IHP _ IN).
    eapply AbsPH.no_lozenge; eauto.
    apply AbsPH.no_parent_is_top in e. subst. elim (HF.not_above_top _ ABOVE).
  Qed.

  Definition mem x s : {In x s} + {~In x s}.
  Proof.
    functional induction (In x s).
    destruct IHP. auto.
    destruct (AbsPSet.mem x s) as []_eqn.
    apply F.mem_iff in Heqb. auto. apply F.not_mem_iff in Heqb. tauto.
    destruct (AbsPSet.mem x s) as []_eqn.
    apply F.mem_iff in Heqb. auto. apply F.not_mem_iff in Heqb. tauto.
  Qed.

  Definition bot := AbsPSet.empty.

  Definition eq (s1 s2: t): Prop :=
    forall x, In x s1 <-> In x s2.

  Theorem eq_refl: forall x, eq x x.
  Proof.
    split; auto.
  Qed.

  Theorem eq_sym: forall x y, eq x y -> eq y x.
  Proof.
    split; specialize (H x0); destruct H; auto.
  Qed.

  Theorem eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    split; specialize (H x0); destruct H; specialize (H0 x0); destruct H0; auto.
  Qed.

  Definition beq: t -> t -> bool := AbsPSet.equal.

  Definition beq_correct: forall x y, beq x y = true -> eq x y.
  Proof.
    intros.
    apply F.equal_iff in H. unfold AbsPSet.Equal in H.
    split; intros;
    functional induction (In x0 y); functional induction (In x0 x);
    merge_parents; intuition; try left; apply H; auto.
  Qed.

  Definition ge (s1 s2: t): Prop := forall x, In x s2 -> In x s1.

  Theorem ge_refl: forall x y, eq x y -> ge x y.
  Proof.
    repeat intro. specialize (H x0). tauto.
  Qed.

  Theorem ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof.
    repeat intro. specialize (H x0). specialize (H0 x0). tauto.
  Qed.

  Theorem ge_bot: forall x, ge x bot.
  Proof.
    repeat intro. remember bot. functional induction (In x0 t0).
    destruct H. inv H. apply In_spec_aux. right. exists px. auto.
    inv H.
  Qed.

  Definition is_not_above x y := negb (AbsPH.above_dec y x).

  Definition is_necessary s x := AbsPSet.for_all (is_not_above x) s.

  Definition normalize s := AbsPSet.filter (is_necessary s) s.

  Definition lub' a b := normalize (AbsPSet.union a b).

  Module HFacts := HierarchyFacts(AbsPH).

  Definition AbsPSet_In_dec: forall s x,
    { AbsPSet.In x s } + { ~ AbsPSet.In x s }.
  Proof.
    intros. destruct (AbsPSet.mem x s) as []_eqn.
    left. now apply F.mem_iff.
    right. now apply F.not_mem_iff.
  Qed.

  Theorem normalize_spec: forall s x,
    In x s <-> In x (normalize s).
  Proof.
    split.
    Case "->".
    revert x. refine (AbsPH.above_ind _ _); intros x IND IN.
    pose proof HFacts.exists_ancestor_dec as EA.
    specialize (EA (fun x => AbsPSet.In x s) (AbsPSet_In_dec s) x). simpl in EA.
    apply In_spec.
    destruct (AbsPSet.mem x (normalize s)) as []_eqn.
    apply F.mem_iff in Heqb. now left.
    apply F.not_mem_iff in Heqb. right.
    destruct EA as [EX | NEX].
    destruct EX as [ax [Aax INax]]. specialize (IND ax Aax).
    feed IND. apply In_spec. now left. apply In_spec in IND.
    destruct IND as [INax' | [ax' INax']].
    exists ax. auto.
    exists ax'. intuition. etransitivity; eauto.
    elim Heqb. unfold normalize. apply F.filter_iff.
    repeat intro. subst. auto.
    split.
    apply In_spec in IN. intuition. destruct H as [ax [Aax INax]].
    elim (NEX _ Aax INax).
    unfold is_necessary. apply F.for_all_iff.
    repeat intro. subst. auto.
    intros x0 INx0. unfold is_not_above.
    destruct (AbsPH.above_dec x0 x); simpl; auto.
    elim (NEX _ a INx0).
    Case "<-".
    revert x. refine (AbsPH.above_ind _ _); intros x IND IN.
    apply In_spec in IN. apply In_spec. intuition.
    apply F.filter_iff in H. intuition. repeat intro; subst; easy.
    destruct H as [ax [A IN]]. right. exists ax. apply F.filter_iff in IN.
    intuition. repeat intro; subst; easy.
  Qed.

  Theorem lub'_spec: forall a b x,
    (In x a \/ In x b) -> In x (lub' a b).
  Proof.
    intros. unfold lub'. apply -> normalize_spec. apply In_spec. intuition.
    apply In_spec in H0. intuition.
    left. apply F.union_iff. now left.
    right. destruct H as [ax [Aax Inax]].
    exists ax. split. easy. apply F.union_iff. left. easy.
    apply In_spec in H0. intuition.
    left. apply F.union_iff. now right.
    right. destruct H as [ax [Aax Inax]].
    exists ax. split. easy. apply F.union_iff. right. easy.
  Qed.

  (* [implies_widening b o l] is true if the value of l implies that (Loc b o)
     must or will be widened.
     This includes:
     - l = Loc b o', where o' <> O
     - L = blk b', where b' >= b
     *)
  Definition implies_widening b o l :=
    match l with
    | Loc b' o' => andb (AbsBOT.eq_dec b b') (negb (Int.eq o o'))
    (*
       was | Blk _ => false
       but this is problematic, as it does not ensure:
       ge A a -> ge B b -> ge (widen A B) (widen a b)
       counter-example:
       a = { Loc x o  }
       A = { Loc x o  }
       b = { Loc x o' }
       B = { Blk x    }
       widen A B = { Loc x o }
       widen a b = { Blk x   }
       *)
      | Blk b'    => if AbsBOT.eq_dec b' b || AbsPH.above_dec (Blk b') (Blk b) then true else false
    end.

  Definition widening widener x :=
    match x with
    | Blk b => Blk b
    | Loc b o =>
      if AbsPSet.exists_ (implies_widening b o) widener
      then Blk b (* widening *)
      else Loc b o
    end.

  Definition add_widened widener x res :=
    AbsPSet.add (widening widener x) res.

  Theorem add_widened_spec: forall widener x res,
    In x (add_widened widener x res).
  Proof.
    intros. apply In_spec. unfold add_widened.
    destruct x as [b|b o]; simpl.
    left. apply F.add_iff. now left.
    destruct (AbsPSet.exists_ (implies_widening b o) widener) as []_eqn.
    right. exists (Blk b). split.
    now apply AbsPH.parent_is_above.
    apply F.add_iff. now left.
    left.
    apply F.add_iff. now left.
  Qed.

  Theorem add_widened_spec_2: forall widener x res y,
    In x res ->
    In x (add_widened widener y res).
  Proof.
    intros ???? IN. apply In_spec in IN. apply In_spec.
    destruct IN as [IN|[ax [A IN]]].
    left. apply F.add_iff. now right.
    right. exists ax. split. easy. apply F.add_iff. now right.
  Qed.

  Definition widen (widened: t) (widener: t): t :=
    AbsPSet.fold (add_widened widener) widened AbsPSet.empty.

  Theorem widen_spec: forall widened widener x,
    In x widened -> In x (widen widened widener).
  Proof.
    intros. unfold widen. rewrite AbsPSet.fold_1. apply In_spec in H. intuition.

    eapply fold_left_adds_prop; eauto.
    apply PTSet.F.elements_iff. eauto.
    intros. apply add_widened_spec.
    intros. apply In_spec in H. apply In_spec. intuition.
    left. apply F.add_iff. now right.
    right. destruct H1 as [ax [Aax Inax]]. exists ax. split.
    easy.
    apply F.add_iff. now right.

    destruct H0 as [ax [Aax Inax]].
    eapply fold_left_adds_prop; eauto.
    apply PTSet.F.elements_iff. eauto.
    intros. apply In_spec. right. destruct ax as [b|bo].
    exists (Blk b). split. easy. apply F.add_iff. now left.
    elim (not_loc_above _ _ _ Aax).

    intros. apply In_spec in H. apply In_spec. intuition.
    left. apply F.add_iff. now right.
    right.
    destruct H0 as [aax [Aaax Inaax]].
    destruct aax as [b|b o].
    exists (Blk b). split. easy. apply F.add_iff. now right.
    elim (not_loc_above _ _ _ Aaax).
  Qed.

  (* lub takes into account its use in the Kildall algorithm. Therefore, it
     performs widening if its 2nd parameter grows in a possibly-infinite
     fashion, and thus it is not commutative. *)
  Definition lub (old: t) (new: t): t :=
    lub' old (widen new old).

  Theorem ge_lub_left: forall a b, ge (lub a b) a.
  Proof.
    repeat intro. apply lub'_spec. now left.
  Qed.

  Theorem ge_lub_right: forall a b, ge (lub a b) b.
  Proof.
    repeat intro. apply lub'_spec. right. now apply widen_spec.
  Qed.

  Definition top := add AbsPH.top AbsPSet.empty.

  Theorem In_top: forall x, In x top.
  Proof.
    intros. apply In_spec. destruct (AbsPH.eq_dec x AbsPH.top).
    left. subst. apply F.add_iff. now left.
    right. exists AbsPH.top. split.
    apply AbsPH.top_above; auto.
    apply F.add_iff. now left.
  Qed.

  Theorem ge_top: forall x, ge top x.
  Proof.
    repeat intro. apply In_spec.
    destruct (AbsPH.eq_dec x0 AbsPH.top).
    left. subst. apply F.add_iff. now left.
    right. exists AbsPH.top. split.
    apply AbsPH.top_above; auto.
    apply F.add_iff. now left.
  Qed.

  Definition singleton x := add x bot.

  Theorem In_singleton: forall x, In x (singleton x).
  Proof.
    intros. apply In_spec. left. apply F.add_iff. now left.
  Qed.

  Theorem above_In_singleton: forall x y,
    AbsPH.above x y -> In y (singleton x).
  Proof.
    intros. apply In_spec. right. exists x. split.
    easy.
    apply F.add_iff. now left.
  Qed.

  Theorem not_In_bot: forall x, ~ In x bot.
  Proof.
    repeat intro. apply In_spec in H. intuition. inversion H0.
    destruct H0 as [? [_ ?]]. inversion H.
  Qed.

  Theorem ge_top_eq_top: forall x, ge x top <-> eq x top.
  Proof.
    repeat (split; repeat intro); auto.
    apply In_top.
    now apply H.
  Qed.

  Theorem not_In_empty: forall x, ~ In x AbsPSet.empty.
  Proof.
    repeat intro. remember AbsPSet.empty as empty.
    functional induction (In x empty). intuition. inv H0. inv H.
  Qed.

  Lemma InA_elements_In: forall x s,
    InA Logic.eq x (AbsPSet.elements s) -> In x s.
  Proof.
    intros. apply In_spec. left. now apply F.elements_iff.
  Qed.

  Lemma ge_InA_elements_In:
    forall a b,
      ge a b ->
      forall x,
        InA Logic.eq x (AbsPSet.elements b) ->
        In x a.
  Proof.
    intros. apply H. now apply InA_elements_In.
  Qed.

  Module P := FSetProperties.Properties(AbsPSet).

  Lemma AbsPSet_fold_inv: forall x f sinit sfold,
    AbsPSet.In x (AbsPSet.fold (fun e s => AbsPSet.add (f e) s) sfold sinit) ->
    ~ AbsPSet.In x sinit ->
    exists ax, AbsPSet.In ax sfold /\ x = f ax.
  Proof.
    intros x f sinit sfold. apply P.fold_rec.
    intros. congruence.
    intros x0 a s' s'' Insfold NIns' ADD IND InADD NIninit.
    apply F.add_iff in InADD. destruct InADD as [fx0_eq_x | Inxa].
    exists x0. split; auto. apply ADD. now left.
    destruct (IND Inxa NIninit) as [ax [Insfold' x_fax]].
    exists ax. split; auto. apply ADD. now right.
  Qed.

  Lemma widen_inv: forall x s w,
    AbsPSet.In x (widen s w) ->
    exists dx, AbsPSet.In dx s /\ (x = widening w dx).
  Proof.
    intros x s w H. unfold widen in H.
    pose proof (AbsPSet_fold_inv _ _ _ _ H).
    destruct H0 as [ax [Inax xax]]. intro IN. inversion IN. subst. exists ax.
    split; easy.
  Qed.

  Lemma widen_inc_l_aux: forall b o s v,
    In (Loc b o) s ->
    AbsPSet.exists_ (implies_widening b o) v = true ->
    In (Blk b) (widen s v).
  Proof.
    intros ???? IN EX. unfold widen. rewrite AbsPSet.fold_1.
    apply In_spec in IN. destruct IN as [IN|[ax [A IN]]].
    eapply fold_left_adds_prop; eauto.
    apply F.elements_iff. apply IN.
    intros. unfold add_widened. unfold widening. rewrite EX. apply In_spec.
    left. apply F.add_iff. now left.
    intros. now apply add_widened_spec_2.
    eapply fold_left_adds_prop; eauto.
    apply F.elements_iff. apply IN.
    intros. unfold add_widened. unfold widening. destruct ax. apply In_spec.
    destruct (AbsBHFun.eq_dec b t0).
    subst. left. apply F.add_iff. now left.
    right. exists (Blk t0). split.
    eapply AbsPH.no_lozenge; eauto.
    unfold AbsPH.is_parent. simpl. reflexivity. congruence.
    apply F.add_iff. now left.
    elim (not_loc_above _ _ _ A).
    intros. now apply add_widened_spec_2.
  Qed.

  Lemma widen_inc_l: forall a b,
    ge a b ->
    forall v, ge (widen a v) (widen b v).
  Proof.
    intros a b GE v x INb. apply In_spec in INb.
    destruct INb as [INb | [ax [A IN]]].
    Case "direct".
    pose proof INb as INV. apply widen_inv in INV.
    destruct INV as [dx [dxInb xdx]]. subst.
    destruct dx; simpl in *.
    apply widen_spec. apply GE. apply In_spec. now left.
    destruct (AbsPSet.exists_ (implies_widening a0 i) v) as []_eqn.
    assert (In (Loc a0 i) a). apply GE. apply In_spec. now left.
    eapply widen_inc_l_aux; eauto.
    apply widen_spec. apply GE. apply In_spec. now left.
    Case "indirect".
    pose proof IN as INV. apply widen_inv in INV.
    destruct INV as [dx [dxInb xdx]]. subst.
    destruct dx; simpl in *.
    apply widen_spec. apply GE. apply In_spec. right.
    exists (Blk a0). split; easy.
    destruct (AbsPSet.exists_ (implies_widening a0 i) v) as []_eqn.
    assert (In (Loc a0 i) a). apply GE. apply In_spec. now left.
    assert (In (Blk a0) (widen a v)). eapply widen_inc_l_aux; eauto.
    apply In_spec in H0. apply In_spec. right. intuition.
    exists (Blk a0). split; easy.
    destruct H1 as [aax [Aaax INaax]]. exists aax. split.
    etransitivity; eauto. easy.
    elim (not_loc_above _ _ _ A).
  Qed.

  Lemma ge_union_l: forall a b s,
    ge a b ->
    ge (AbsPSet.union s a) (AbsPSet.union s b).
  Proof.
    intros ??? GE x IN. apply In_spec in IN. apply In_spec. intuition.
    apply F.union_iff in H. intuition.
    left. apply F.union_iff. intuition.
    assert (In x a). apply GE. apply In_spec. now left. apply In_spec in H.
    intuition.
    left. apply F.union_iff. intuition.
    destruct H1 as [ax [? ?]]. right. exists ax. intuition.
    apply F.union_iff. intuition.
    destruct H as [ax [? ?]].
    apply F.union_iff in H0. intuition.
    right. exists ax. intuition. apply F.union_iff. intuition.
    assert (In x a). apply GE. apply In_spec. right. exists ax; split; easy.
    apply In_spec in H0. intuition.
    left. apply F.union_iff. now right.
    destruct H2 as [aax [Aaax INaax]].
    right. exists aax. split. easy. apply F.union_iff. now right.
  Qed.

  Theorem lub_inc_l: forall a b, ge a b -> forall v, ge (lub v a) (lub v b).
  Proof with (try solve [repeat intro; subst; reflexivity]).
    unfold lub, lub'. intros a b GE v x IN. apply -> normalize_spec.
    apply normalize_spec in IN. eapply ge_union_l; eauto. now apply widen_inc_l.
  Qed.

  Theorem In_union: forall x a b,
    In x (AbsPSet.union a b) <-> In x a \/ In x b.
  Proof.
    split; intros.
    Case "->".
    apply In_spec in H. destruct H as [H|H].
    apply F.union_iff in H. intuition.
    left. apply In_spec. now left.
    right. apply  In_spec. now left.
    destruct H as [ax [A B]].
    apply F.union_iff in B. intuition.
    left. apply In_spec. right. exists ax. now split.
    right. apply In_spec. right. exists ax. now split.
    Case "<-".
    apply In_spec. destruct H as [H|H].
    apply In_spec in H. destruct H as [H|[ax [? ?]]].
    left. apply F.union_iff. now left.
    right. exists ax. split. easy. apply F.union_iff. now left.
    apply In_spec in H. destruct H as [H|[ax [? ?]]].
    left. apply F.union_iff. now right.
    right. exists ax. split. easy. apply F.union_iff. now right.
  Qed.

  Theorem widen_ge: forall a A b B,
    ge A a ->
    ge B b ->
    ge (widen A B) (widen a b).
  Proof.
    intros a A b B geAa geBb. intros x IN. unfold ge in *.
    apply In_spec in IN. destruct IN as [IN|[ax[Aax IN]]].
    Case "x is really in (widen a b) -> x is the widening of some dx".
    apply widen_inv in IN. destruct IN as [dx[IN ?]]. subst.
    unfold widening. destruct dx.
    SCase "dx was a Blk".
    apply widen_spec. apply geAa. apply In_spec. now left.
    SCase "dx was a Loc -> x is either the same Loc or the parent Blk".
    destruct (AbsPSet.exists_ (implies_widening a0 i) b) as []_eqn.
    SSCase "x is a Blk, there is a Loc for the same block in b".
    apply In_spec.
    (* DON'T DO 'left' HERE! IT CAN BE 'right'! *)
    unfold widen. rewrite AbsPSet.fold_1.
    assert (INA: In (Loc a0 i) A). apply geAa. apply In_spec. now left.
    apply In_spec in INA. destruct INA as [INA|[ax [Aax INA]]].
    SSSCase "(Loc a0 i) is in A".
    left.
    eapply fold_left_adds_prop; eauto.
    apply PTSet.F.elements_iff. eauto.
    SSSSCase "'add' case".
    intros. unfold add_widened. apply F.add_iff. unfold widening.
    destruct (AbsPSet.exists_ (implies_widening a0 i) B) as []_eqn.
    SSSSSCase "some element of B implies widening (a0, i)".
    now left.
    SSSSSCase "no element in B implies widening (a0, i)".
    exfalso. (* since there is one in b, there must be one in B >= b *)
    apply F.exists_iff in Heqb0. inv Heqb0. intuition.
    assert (INB: In x0 B). apply geBb. apply In_spec. now left.
    (* let's show it *)
    assert (AbsPSet.Exists (fun x => implies_widening a0 i x = true) B).
    apply In_spec in INB. destruct INB as [INB|[ax[Aax INB]]].
    SSSSSSCase "x0 is in B".
    exists x0. now split.
    SSSSSSCase "ax >= x0 is in B".
    exists ax. split. easy. unfold implies_widening. unfold implies_widening in H1.
    destruct ax.
    destruct (AbsBOT.eq_dec t0 a0); simpl. easy.
    destruct (AbsPH.above_dec (@Blk AbsBOT.t t0) (@Blk AbsBOT.t a0)); simpl. easy.
    destruct x0.
    destruct (AbsBOT.eq_dec a1 a0); simpl in H1. inv e. contradiction.
    destruct (AbsPH.above_dec (@Blk AbsBOT.t a1) (@Blk AbsBOT.t a0)); simpl in H1.
    elim n0. etransitivity. apply Aax. easy.
    inv H1.
    destruct (AbsBOT.eq_dec a0 a1); simpl in H1. inv e.
    destruct (Int.eq i i0); simpl in H1. inv H1.
    elim n0. eapply AbsPH.no_lozenge. apply Aax. now compute. congruence.
    congruence.
    elim (not_loc_above _ _ _ Aax).
    apply F.exists_iff in H.
    congruence.
    repeat intro; now subst.
    repeat intro; now subst.
    SSSSCase "'preserve' case".
    intros. apply F.add_iff. now right.
    SSSCase "ax >= (Loc a0 i) is in A".
    eapply fold_left_adds_prop; eauto.
    apply PTSet.F.elements_iff. eauto.
    SSSSCase "'add' case".
    destruct (AbsPH.eq_dec ax (Blk a0)).
    SSSSSCase "ax = Blk a0 -> left".
    subst. left. unfold add_widened. apply F.add_iff. unfold widening. now left.
    SSSSSCase "ax > Blk a0 -> right".
    right. exists ax. split.
    eapply AbsPH.no_lozenge; eauto. now compute.
    apply F.add_iff. unfold widening. destruct ax. now left. elim (not_loc_above _ _ _ Aax).
    SSSSCase "'preserve' case".
    intros. destruct H as [?|[aax [? ?]]].
    left. apply F.add_iff. now right.
    right. exists aax. split. easy. apply F.add_iff. now right.
    SSCase "x is a Loc, no widener in b".
    apply In_spec.
    unfold widen. rewrite AbsPSet.fold_1.
    assert (INA: In (Loc a0 i) A). apply geAa. apply In_spec. now left.
    apply In_spec in INA. destruct INA as [INA|[ax [Aax INA]]].
    SSSCase "really in A".
    destruct (AbsPSet.exists_ (implies_widening a0 i) B) as []_eqn.
    SSSSCase "widening -> right".
    right.
    eapply fold_left_adds_prop; eauto.
    apply PTSet.F.elements_iff. eauto.
    SSSSSCase "'add' case".
    intros. exists (Blk a0). split.
    apply AbsPH.parent_is_above. now compute.
    unfold add_widened. apply F.add_iff. unfold widening. rewrite Heqb1. now left.
    SSSSSCase "'preserve' case".
    intros. destruct H as [ax [? ?]].
    exists ax. split. easy. apply F.add_iff. now right.
    SSSSCase "no widening -> left".
    left.
    eapply fold_left_adds_prop; eauto.
    apply PTSet.F.elements_iff. eauto.
    SSSSSCase "'add' case".
    intros. apply F.add_iff. unfold widening. rewrite Heqb1. now left.
    SSSSSCase "'preserve' case".
    intros. apply F.add_iff. now right.
    SSSCase "parent in A".
    right. exists ax. split. easy.
    eapply fold_left_adds_prop; eauto.
    apply PTSet.F.elements_iff. eauto.
    intros. apply F.add_iff. destruct ax. now left. elim (not_loc_above _ _ _ Aax).
    intros. apply F.add_iff. now right.
    Case "x has a parent really in (widen a b)".
    apply In_spec. right. apply widen_inv in IN. destruct IN as [dx[IN ?]]. subst.
    assert (INA: In dx A). apply geAa. apply In_spec. now left.
    apply In_spec in INA. destruct INA as [?|[ax[? ?]]].
    SCase "dx in A".
    exists (widening B dx). split.
    unfold widening. destruct dx. easy. unfold widening in Aax. 
    destruct (AbsPSet.exists_ (implies_widening a0 i) b) as []_eqn;
    destruct (AbsPSet.exists_ (implies_widening a0 i) B) as []_eqn;
    try easy.
    exfalso.
    apply F.exists_iff in Heqb0. inv Heqb0. intuition.
    assert (In x0 B). apply geBb. apply In_spec. now left.
    assert (AbsPSet.Exists (fun x => implies_widening a0 i x = true) B).
    apply In_spec in H0. destruct H0 as [?|[ax[? ?]]].
    exists x0. now split.
    exists ax. split. easy. unfold implies_widening. unfold implies_widening in H2.
    destruct ax. destruct x0.
    Ltac finish_it :=
      repeat (
        try contradiction;
        match goal with
        | H: AbsPH.above (Loc _ _) _ |- _ => elim (not_loc_above _ _ _ H)
        | H: AbsBOT.eq _ _ |- _ => inv H
        | F: ~ AbsPH.above ?a ?b,
          A: AbsPH.above ?a ?x,
          B: AbsPH.above ?x ?b |- _ => elim F; etransitivity; eauto
        | A: AbsPH.above ?x (Loc ?b ?o),
          F: ~ AbsPH.above ?x (Blk ?b)
          |- _ =>
          elim F; eapply AbsPH.no_lozenge; [apply A | now compute | congruence]
        end
      ).
    destruct (AbsBOT.eq_dec a1 a0), (AbsPH.above_dec (@Blk AbsBOT.t a1) (@Blk AbsBOT.t a0)),
      (AbsBOT.eq_dec t0 a0), (AbsPH.above_dec (@Blk AbsBOT.t t0) (@Blk AbsBOT.t a0));
      simpl in *; try easy; finish_it.
    destruct (AbsBOT.eq_dec a0 a1), (Int.eq i i0),
      (AbsBOT.eq_dec t0 a0), (AbsPH.above_dec (@Blk AbsBOT.t t0) (@Blk AbsBOT.t a0));
      simpl in *; try easy; finish_it.
    destruct x0.
    destruct (AbsBOT.eq_dec a1 a0), (AbsPH.above_dec (@Blk AbsBOT.t a1) (@Blk AbsBOT.t a0)),
      (AbsBOT.eq_dec a0 t0), (Int.eq i i0);
      simpl in *; try easy; finish_it.
    destruct (AbsBOT.eq_dec a0 a1), (Int.eq i i1),
      (AbsBOT.eq_dec a0 t0), (Int.eq i i0);
      simpl in *; try easy; finish_it.
    apply F.exists_iff in H3. congruence.
    repeat intro; now subst.
    repeat intro; now subst.
    etransitivity; eauto. now apply AbsPH.parent_is_above.
    unfold widening. destruct dx.
    SSCase "dx was a Blk".
    unfold widen. rewrite AbsPSet.fold_1.
    eapply fold_left_adds_prop; eauto.
    apply PTSet.F.elements_iff. eauto.
    intros. apply F.add_iff. now left.
    intros. apply F.add_iff. now right.
    SSCase "dx was a Loc".
    unfold widen. rewrite AbsPSet.fold_1.
    eapply fold_left_adds_prop; eauto.
    apply PTSet.F.elements_iff. eauto.
    intros. apply F.add_iff. unfold widening. now left.
    intros. apply F.add_iff. now right.
    SCase "dx has ancestor in A".
    exists (widening B ax).
    split.
    unfold widening in *. destruct ax, dx.
    etransitivity; eauto.
    destruct (AbsPSet.exists_ (implies_widening a0 i) b) as []_eqn.
    destruct (AbsBOT.eq_dec a0 t0).
    now inv e.
    etransitivity. eapply AbsPH.no_lozenge. apply H. now compute. congruence. easy.
    elim (not_loc_above _ _ _ Aax).
    elim (not_loc_above _ _ _ H).
    elim (not_loc_above _ _ _ H).
    unfold widening. destruct ax.
    unfold widen. rewrite AbsPSet.fold_1.
    eapply fold_left_adds_prop; eauto.
    apply PTSet.F.elements_iff. eauto.
    intros. apply F.add_iff. now left.
    intros. apply F.add_iff. now right.
    unfold widen. rewrite AbsPSet.fold_1.
    eapply fold_left_adds_prop; eauto.
    apply PTSet.F.elements_iff. eauto.
    intros. apply F.add_iff. unfold widening. now left.
    intros. apply F.add_iff. now right.
  Qed.

  Theorem ge_lub: forall a b c d, ge a b -> ge c d -> ge (lub a c) (lub b d).
  Proof.
    unfold lub, lub'. intros a b c d GEab GEcd x IN. apply -> normalize_spec.
    apply normalize_spec in IN. unfold ge in *.
    apply In_union in IN. apply In_union. intuition.
    right. eapply widen_ge; eauto.
  Qed.

  Theorem lub_bot: forall a b, eq a bot -> eq b bot -> eq (lub a b) bot.
  Proof.
    intros a b abot bbot x. split; intros H.
    apply In_spec in H. destruct H as [H|[ax[A H]]].
    unfold lub in H. unfold lub' in H. unfold normalize in H.
    apply F.filter_iff in H. destruct H as [IN N].
    apply F.union_iff in IN. destruct IN as [IN|IN].
    assert (In x a). apply In_spec. now left. now apply abot in H.
    unfold widen in IN. apply AbsPSet_fold_inv in IN.
    destruct IN as [ax[IN ?]].
    assert (In ax b). apply In_spec. now left. apply bbot in H0. apply In_spec in H0. intuition.
    inv H1. destruct H1 as [?[? ?]]. inv H1.
    intro. inv H.
    repeat intro; now subst.
    unfold lub in H. unfold lub' in H. unfold normalize in H.
    apply F.filter_iff in H. destruct H as [IN N].
    apply F.union_iff in IN. destruct IN as [IN|IN].
    assert (In ax a). apply In_spec. now left. apply abot in H. apply In_spec in H. intuition.
    inv H0. destruct H0 as [?[? ?]]. inv H0.
    unfold widen in IN. apply AbsPSet_fold_inv in IN.
    destruct IN as [aax[IN ?]].
    assert (In aax b). apply In_spec. now left. apply bbot in H0. apply In_spec in H0. intuition.
    inv H1. destruct H1 as [?[? ?]]. inv H1.
    intro. inv H.
    repeat intro; now subst.
    apply In_spec in H. destruct H as [H|[?[H ?]]].
    inv H. inv H0.
  Qed.

  Theorem bot_ge: forall x, ge bot x <-> eq bot x.
  Proof.
    split; repeat intro.
    split; repeat intro.
    now apply ge_bot.
    now apply H.
    now apply H.
  Qed.

  Theorem ge_antisym: forall a b, ge a b -> ge b a -> eq a b.
  Proof.
    intros a b GEab GEba k. split; intros IN.
    now apply GEba. now apply GEab.
  Qed.

  Opaque mem In beq ge lub bot top.

  Hint Resolve In_add_spec In_spec eq_refl eq_sym eq_trans beq_correct
    ge_refl ge_trans ge_bot ge_lub_left ge_lub_right In_singleton
    above_In_singleton not_In_bot ge_top In_top ge_top_eq_top: ptset.

End PTSet.

Module RegOT <: OrderedType := OrderedTypeEx.Positive_as_OT.

(*
Module NaiveMergeStrategy (KEY: OrderedType) (VAL: SEMILATTICE)
  <: MergeStrategy(KEY)(VAL).
  Definition f (k: KEY.t) o1 o2 :=
    match o1, o2 with
    | None, None => None
    | Some s, None | None, Some s => Some s
    | Some s1, Some s2 => Some (VAL.lub s1 s2)
    end.
  Theorem f_compat:
    forall x x' o1 o2,
      KEY.eq x x' -> f x o1 o2 = f x' o1 o2.
  Proof.
    reflexivity.
  Qed.
End NaiveMergeStrategy.

Module RegMapMergeStrategy := NaiveMergeStrategy(RegOT)(PTSet).
*)

Module RegMapWithoutTop := MapSemiLattice(RegOT)(PTSet).

Module RegMap <: SEMILATTICE_WITH_TOP.
  Module L := SemiLatticeToLattice(RegMapWithoutTop).
  Include L.
  (* get should be like find, but wrapping the option type away *)
  Definition get (k: RegOT.t) (rmap: t): PTSet.t :=
    match rmap with
    | Top        => PTSet.top
    | Some rmap' =>
      match RegMapWithoutTop.M.find k rmap' with
      | None   => PTSet.bot
      | Some s => s
      end
    end.

  Definition add (r: RegOT.t) (s: PTSet.t) (rmap: t): t :=
    match rmap with
    | Top        => Top
    | Some rmap' =>
      Some (RegMapWithoutTop.M.add r (PTSet.lub s (get r rmap)) rmap')
    end.

  (*Parameter set: ROT.t -> PTSet.t -> t -> t.*)

  Theorem get_ge: forall rmap rmap',
    ge rmap rmap' ->
    (forall k, PTSet.ge (RegMap.get k rmap) (RegMap.get k rmap')).
  Proof.
    intros. unfold get. destruct rmap, rmap'; auto with ptset.
    specialize (H k). unalias.
    destruct (RegMapWithoutTop.M.find k t0);
    destruct (RegMapWithoutTop.M.find k t1);
    auto with ptset.
  Qed.

  Theorem get_add_same: forall k v m, PTSet.ge (get k (add k v m)) v.
  Proof.
    intros. destruct m; simpl.
    rewrite RegMapWithoutTop.FMF.add_eq_o.
    apply PTSet.ge_lub_left.
    reflexivity.
    apply PTSet.ge_top.
  Qed.

  Theorem get_add: forall x y s m, PTSet.ge (get x (add y s m)) (get x m).
  Proof.
    intros. destruct m; simpl.
    destruct (peq x y).
    subst. rewrite RegMapWithoutTop.FMF.add_eq_o.
    apply PTSet.ge_lub_right.
    reflexivity.
    rewrite RegMapWithoutTop.FMF.add_neq_o.
    apply PTSet.ge_refl. apply PTSet.eq_refl.
    auto.
    apply PTSet.ge_top.
  Qed.

  Theorem ge_add: forall k v m, ge (add k v m) m.
  Proof.
    intros. destruct m; simpl; intuition.
    unfold RegMapWithoutTop.ge. unalias. intros.
    destruct (peq k k0).
    subst. rewrite RegMapWithoutTop.FMF.add_eq_o; [|auto].
    generalize (RegMapWithoutTop.M.find k0 t0); intros s. destruct s; [|auto].
    apply PTSet.ge_lub_right.
    rewrite RegMapWithoutTop.FMF.add_neq_o; [|auto].
    generalize (RegMapWithoutTop.M.find k0 t0); intros s. destruct s; [|auto].
    apply PTSet.ge_refl. apply PTSet.eq_refl.
  Qed.

  Theorem get_top: forall k, PTSet.ge (get k top) PTSet.top.
  Proof.
    intros. simpl. apply PTSet.ge_top.
  Qed.

  Global Opaque eq ge bot get add (*set*).
End RegMap.

Module MkOverlapMapAux
  (O: Overlap)
  (OT: OrderedTypeLogicEq
    with Definition t := O.t
  )
  (L: SEMILATTICE_EXTENDED).

  (* We need a merge strategy to create a map semilattice from keys and image
     lattice. It defines what to put in the lub of two maps when keys are
     missing from either side. *)
  (* Module MergeStrategy := NaiveMergeStrategy(OT)(L). *)

  Module MSL := MapSemiLattice(OT)(L).

  (* The map semilattice does not have a Top. This adds it as an option on
     the underlying map semilattice type. *)
  Module LAT := SemiLatticeToLattice(MSL).

  Definition t := LAT.t.

(*
  Definition ge := LAT.ge.
  Definition ge_refl := LAT.ge_refl.
  Definition ge_trans := LAT.ge_trans.
*)

  Definition bot := LAT.bot.
(*  Definition ge_bot := LAT.ge_bot.*)
  Definition top := LAT.top.
(*  Definition ge_top := LAT.ge_top.*)

  Function get_rec (k: O.t) (m: MSL.t) {measure O.measure k}: L.t :=
    match MSL.M.find k m with
    | Some s => s
    | None   =>
      match O.parent k with
      | None   => L.bot
      | Some p => get_rec p m
      end
    end.
  Proof.
    intros ???? PARENT. exact (O.parent_measure _ _ PARENT).
  Qed.

  Definition get (k: O.t) (m: t): L.t :=
    match m with
    | LAT.Top => L.top
    | Some m  => get_rec k m
    end.

  Theorem get_equation: forall k m,
    get k m =
    match m with
    | None => L.top
    | Some m' =>
      match MSL.M.find k m' with
      | Some s => s
      | None =>
        match O.parent k with
        | Some p => get p m
        | None => L.bot
        end
      end
    end.
  Proof.
    intros k m. destruct m as [m|]. simpl. apply get_rec_equation. now simpl.
  Qed.

  Definition eq m n := forall k, L.eq (get k m) (get k n).

  Theorem eq_refl: forall m, eq m m.
  Proof.
    intros m k. apply L.eq_refl.
  Qed.

  Definition eq_sym: forall m n, eq m n -> eq n m.
  Proof.
    intros m n EQ k. now apply L.eq_sym.
  Qed.

  Definition eq_trans: forall m n o, eq m n -> eq n o -> eq m o.
  Proof.
    intros m n o EQmn EQno k. eapply L.eq_trans; eauto.
  Qed.

  Definition elements (m: t) :=
    match m with
    | LAT.Top => nil
    | Some m  => map (@fst O.t L.t) (MSL.M.elements m)
    end.

  Require Import ListSet.

  Definition union_elements m n :=
    set_union O.eq_dec (elements m) (elements n).

  Definition beq_always m n :=
    match m, n with
    | None,   None   => true
    | Some a, Some b => forallb (fun elt => L.beq (get_rec elt a) (get_rec elt b)) (union_elements m n)
    | Some x, None
    | None,   Some x =>
      negb (MSL.M.is_empty x) && forallb (fun elt => L.beq (get_rec elt x) L.top) (elements (Some x))
    end.

  Definition beq_has_top m n :=
    forallb (fun elt => L.beq (get elt m) (get elt n)) (union_elements m n).

  Theorem not_in_elements: forall k m,
    ~ In k (elements m) ->
    match m with
    | None   => True
    | Some m => ~ MSL.M.In k m
    end.
  Proof.
    intros k m NIN. destruct m as [m|]; auto. simpl in NIN. intro IN. elim NIN. clear NIN.
    apply MSL.M.FMF.elements_in_iff in IN. destruct IN as [e IN].
    generalize dependent (MSL.M.elements m). induction l.
    easy.
    intros. inv IN.
    left. inv H0. simpl in *. now subst.
    right. now apply IHl.
  Qed.

  Definition has_top (m: t): Prop :=
    match m with
    | None => True
    | Some m => MSL.M.In O.top m
    end.

  Definition beq_has_top_correct: forall m n, has_top m -> has_top n -> beq_has_top m n = true -> eq m n.
  Proof.
    intros m n HTm HTn BEQ. unfold eq. refine (O.above_ind _ _). intros k IND.
    unfold beq_has_top in BEQ.
    destruct (In_dec O.eq_dec k (union_elements m n)).
    apply forallb_forall with (x := k) in BEQ. now apply L.beq_correct. easy.

    assert (NINm: ~ In k (elements m)).
    intro. elim n0. now apply set_union_intro1.
    assert (NINn: ~ In k (elements n)).
    intro. elim n0. now apply set_union_intro2.
    pose proof (not_in_elements _ _ NINm) as M.
    pose proof (not_in_elements _ _ NINn) as N.

    setoid_rewrite get_equation.
    destruct m as [m|].
    destruct n as [n|].
    destruct (MSL.M.find k m) as [km|]_eqn, (MSL.M.find k n) as [kn|]_eqn; MSL.msimpl.
    destruct (O.parent k) as [pk|]_eqn.
    apply IND. now apply O.parent_is_above.
    apply L.eq_refl.
    destruct (MSL.M.find k m) as [km|]_eqn; MSL.msimpl.
    destruct (O.parent k) as [pk|]_eqn.
    apply IND. now apply O.parent_is_above.
    apply O.no_parent_is_top in Heqo0. subst. elim M. apply HTm.

    destruct n as [n|].
    destruct (MSL.M.find k n) as [kn|]_eqn; MSL.msimpl.
    destruct (O.parent k) as [pk|]_eqn.
    apply IND. now apply O.parent_is_above.
    apply O.no_parent_is_top in Heqo0. subst. elim N. apply HTn.

    apply L.eq_refl.
  Qed.

  Definition ge m n :=
    forall k, L.ge (get k m) (get k n).

  Theorem ge_refl: forall m n, eq m n -> ge m n.
  Proof.
    intros m n EQ k. destruct m as [m|], n as [n|]; simpl in *.
    revert k. refine (O.above_ind _ _). intros k IND.
    setoid_rewrite get_rec_equation. pose proof (EQ k) as EQk.
    simpl in EQk. setoid_rewrite get_rec_equation in EQk.
    destruct (MSL.M.find k m) as [km|]_eqn, (MSL.M.find k n) as [kn|]_eqn.
    now apply L.ge_refl. destruct (O.parent k) as [pk|]_eqn.
    now apply L.ge_refl. now apply L.ge_refl. now apply L.ge_refl.
    destruct (O.parent k) as [pk|]_eqn.
    apply IND. now apply O.parent_is_above. apply L.ge_bot.
    apply L.ge_refl. apply EQ.
    apply L.ge_refl. apply EQ.
    apply L.ge_top.
  Qed.

  Theorem ge_trans: forall m n o, ge m n -> ge n o -> ge m o.
  Proof.
    intros m n o GEmn GEno k.
    eapply L.ge_trans; eauto.
  Qed.

  Theorem ge_top: forall m, ge top m.
  Proof.
    intros m k. simpl. apply L.ge_top.
  Qed.

  Lemma get_rec_bot: forall k, get_rec k MSL.bot = L.bot.
  Proof.
    refine (O.above_ind _ _). intros k IND. rewrite get_rec_equation.
    destruct (MSL.M.find k MSL.bot) as []_eqn.
    inv Heqo.
    destruct (O.parent k) as [pk|]_eqn.
    apply IND. now apply O.parent_is_above.
    easy.
  Qed.

  Theorem ge_bot: forall m, ge m bot.
  Proof.
    intros m k. destruct m as [m|]; simpl. rewrite get_rec_bot.
    apply L.ge_bot.
    apply L.ge_top.
  Qed.

  Definition merge m n (k: OT.t) (a: option L.t) (b: option L.t): option L.t :=
    match a, b with
    | None,   None   => None
    | Some a, None   => Some (L.lub a (get_rec k n))
    | None,   Some b => Some (L.lub (get_rec k m) b)
    | Some a, Some b => Some (L.lub a b)
    end.

  Theorem merge_compat m n:
    forall x y a b, OT.eq x y -> merge m n x a b = merge m n y a b.
  Proof.
    intros. inv H. reflexivity.
  Qed.

  Definition hmap_lub (m n: MSL.t): MSL.t :=
    MSL.M.map2i (merge m n) (merge_compat m n) m n.
    
  Definition lub m n :=
    match m, n with
    | Some m, Some n => Some (hmap_lub m n)
    | _,      _      => None
    end.

  Lemma hmap_lub_preserves_ge_get_rec_right:
    forall m n a b x,
      L.ge a (get_rec x m) ->
      L.ge b (get_rec x n) ->
      L.ge (L.lub a b) (get_rec x (hmap_lub m n)).
  Proof.
    intros ????. refine (O.above_ind _ _); intros x IND GEa GEb.
    rewrite get_rec_equation. unfold hmap_lub at 1. rewrite MSL.M.map2i_4.
    rewrite get_rec_equation in GEa, GEb.
    destruct (MSL.M.find x m) as [xm|]_eqn; MSL.msimpl;
    destruct (MSL.M.find x n) as [xn|]_eqn; MSL.msimpl;
      simpl.
    now apply L.ge_lub.
    apply L.ge_lub. easy. destruct (O.parent x) as [px|]_eqn.
    rewrite get_rec_equation. destruct (MSL.M.find x n) as []_eqn; MSL.msimpl. now rewrite Heqo1.
    rewrite get_rec_equation. destruct (MSL.M.find x n) as []_eqn; MSL.msimpl. now rewrite Heqo1.
    apply L.ge_lub.
    rewrite get_rec_equation. destruct (MSL.M.find x m) as []_eqn; MSL.msimpl. easy. easy.
    destruct (O.parent x) as [px|]_eqn.
    apply IND; auto. now apply O.parent_is_above.
    apply L.ge_bot.
    simpl; auto.
  Qed.

  Lemma hmap_lub_preserves_ge_get_rec_left:
    forall m n a b x,
      L.ge (get_rec x m) a ->
      L.ge (get_rec x n) b ->
      L.ge (get_rec x (hmap_lub m n)) (L.lub a b).
  Proof with (try solve [now simpl]).
    intros ????. refine (O.above_ind _ _); intros x IND GEa GEb.
    rewrite get_rec_equation. unfold hmap_lub at 1. rewrite MSL.M.map2i_4...
    rewrite get_rec_equation in GEa, GEb. unfold merge.
    destruct (MSL.M.find x m) as [xm|]_eqn; MSL.msimpl;
    destruct (MSL.M.find x n) as [xn|]_eqn; MSL.msimpl;
      simpl.
    now apply L.ge_lub.
    destruct (O.parent x) as [px|]_eqn.
    apply L.ge_lub. easy.
    rewrite get_rec_equation. destruct (MSL.M.find x n) as []_eqn; MSL.msimpl. now rewrite Heqo1.
    apply L.ge_lub. easy.
    rewrite get_rec_equation. destruct (MSL.M.find x n) as []_eqn; MSL.msimpl. now rewrite Heqo1.
    apply L.ge_lub. rewrite get_rec_equation. destruct (MSL.M.find x m) as []_eqn; MSL.msimpl. easy. easy.
    destruct (O.parent x) as [px|]_eqn.
    apply IND; auto. now apply O.parent_is_above.
    apply L.ge_refl. apply L.eq_sym. apply L.lub_bot.
    apply L.eq_sym. now apply L.bot_ge.
    apply L.eq_sym. now apply L.bot_ge.
  Qed.

  Lemma mapsto_get_rec: forall k v m,
    MSL.M.MapsTo k v m ->
    get_rec k m = v.
  Proof.
    intros. rewrite get_rec_equation. destruct (MSL.M.find k m) as []_eqn; now MSL.msimpl.
  Qed.

  Theorem hmap_lub_preserves_ge_get_rec:
    (forall a b c d : L.t,
      L.ge a b -> L.ge c d -> L.ge (L.lub a c) (L.lub b d)) ->
    (forall a b : L.t,
      L.eq a L.bot -> L.eq b L.bot -> L.eq (L.lub a b) L.bot) ->
    (forall x : L.t, L.ge L.bot x <-> L.eq L.bot x) ->
    forall m n,
      (forall x ax, O.above ax x -> L.ge (get_rec ax m) (get_rec x m)) ->
      (forall x ax, O.above ax x -> L.ge (get_rec ax n) (get_rec x n)) ->
      forall x ax,
        O.above ax x ->
        L.ge (get_rec ax (hmap_lub m n)) (get_rec x (hmap_lub m n)).
  Proof with (try solve [now simpl]).
    intros C D E m n GEm GEn. refine (O.above_ind _ _); intros x INDx ax Aaxx.
    setoid_rewrite get_rec_equation at 2.
    unfold hmap_lub at 2. rewrite MSL.M.map2i_4...
    destruct (MSL.M.find x m) as [xm|]_eqn; MSL.msimpl;
    destruct (MSL.M.find x n) as [xn|]_eqn; MSL.msimpl;
      simpl.
    apply hmap_lub_preserves_ge_get_rec_left; auto. 
    setoid_rewrite <- (mapsto_get_rec _ _ _ Heqo); eauto.
    setoid_rewrite <- (mapsto_get_rec _ _ _ Heqo0); eauto.
    apply hmap_lub_preserves_ge_get_rec_left; auto.
    setoid_rewrite <- (mapsto_get_rec _ _ _ Heqo); eauto.
    apply hmap_lub_preserves_ge_get_rec_left; auto.
    setoid_rewrite <- (mapsto_get_rec _ _ _ Heqo0); eauto.
    destruct (O.parent x) as [px|]_eqn. destruct (O.eq_dec ax px).
    subst. apply L.ge_refl. apply L.eq_refl.
    apply INDx. now apply O.parent_is_above. eapply O.no_lozenge; eauto.
    apply L.ge_bot.
  Qed.

  Theorem lub_preserves_ge:
    (forall a b c d : L.t,
      L.ge a b -> L.ge c d -> L.ge (L.lub a c) (L.lub b d)) ->
    (forall a b : L.t,
      L.eq a L.bot -> L.eq b L.bot -> L.eq (L.lub a b) L.bot) ->
    (forall x : L.t, L.ge L.bot x <-> L.eq L.bot x) ->
    forall m n,
      (forall x ax, O.above ax x -> L.ge (get ax m) (get x m)) ->
      (forall x ax, O.above ax x -> L.ge (get ax n) (get x n)) ->
      forall x ax,
        L.ge (get ax m) (get x m) ->
        L.ge (get ax n) (get x n) ->
        O.above ax x ->
        L.ge (get ax (lub m n)) (get x (lub m n)).
  Proof.
    intros. destruct m as [m|], n as [n|]; simpl in *; try solve [apply L.ge_top].
    apply hmap_lub_preserves_ge_get_rec; auto.
  Qed.

  (* For now, I'll put negb (O.eq_dec key k) because I don't want to rewrite
     the proofs, but it doesn't really matter that key is lubbed. *)
  Definition lub_if_overlap (key: O.t) (val: L.t) (k: O.t) (v: L.t): L.t :=
    if O.overlap_dec key k && negb (O.eq_dec key k) then L.lub val v else v.

  Definition add_if_overlap key val m :=
    MSL.M.mapi (lub_if_overlap key val) m.

  Definition add (k: O.t) (v: L.t) (m: t): t :=
    match m with
    | LAT.Top    => LAT.Top
    | Some m =>
      Some (MSL.M.add k (L.lub v (get k (Some m))) (add_if_overlap k v m))
    end.

  Lemma get_rec_add_same: forall k s m, L.ge (get_rec k (MSL.M.add k s m)) s.
  Proof.
    intros.
    remember (MSL.M.add k s m) as m'.
    functional induction (get_rec k m'); rewrite MSL.FMF.add_eq_o in e; inv e;
      auto; try solve [destruct k; auto].
    apply L.ge_refl. apply L.eq_refl.
  Qed.

  Theorem get_add_same: forall k s m, L.ge (get k (add k s m)) s.
  Proof.
    intros. destruct m; simpl.
    eapply L.ge_trans. apply get_rec_add_same. apply L.ge_lub_left.
    apply L.ge_top.
  Qed.

  Theorem ge_add_if_overlap: forall x s m,
    ge (Some (add_if_overlap x s m)) (Some m).
  Proof.
    repeat intro. simpl. revert k. refine (O.above_ind _ _). intros k IND.
    unfold add_if_overlap. setoid_rewrite get_rec_equation.
    destruct (MSL.M.find k m) as [km|]_eqn.
    apply MSL.FMF.find_mapsto_iff in Heqo. eapply MSL.M.mapi_1 in Heqo.
    destruct Heqo as [y [_ MT]].
    apply MSL.FMF.find_mapsto_iff in MT. rewrite MT.
    unfold lub_if_overlap. destruct (O.overlap_dec x y), (O.eq_dec x y); simpl.
    apply L.ge_refl. apply L.eq_refl.
    apply L.ge_lub_right. apply L.ge_refl. apply L.eq_refl.
    apply L.ge_refl. apply L.eq_refl.
    destruct (MSL.M.find k (MSL.M.mapi (lub_if_overlap x s) m)) as [klub|]_eqn.
    exfalso.
    assert (MSL.M.In k (MSL.M.mapi (lub_if_overlap x s) m)).
    apply MSL.M.FMF.in_find_iff. congruence.
    apply MSL.M.FMF.mapi_in_iff in H. apply MSL.M.FMF.in_find_iff in H. congruence.
    destruct (O.parent k) as [pk|]_eqn.
    apply IND. now apply O.parent_is_above.
    apply L.ge_bot.
  Qed.

  Ltac MSL_simpl :=
    repeat (unfold not in *; try
      match goal with
        | H: MSL.M.find _ _ = Some _ |- _ =>
          apply MSL.M.FMF.find_mapsto_iff in H
        | H: MSL.M.find _ _ = None |- _ =>
          apply MSL.M.FMF.not_find_in_iff in H
        | H: MSL.M.MapsTo ?x ?s0 (MSL.M.add ?x ?s1 _) |- _ =>
          apply MSL.M.FMF.add_mapsto_iff in H; simpl in H; intuition; subst;
            auto
        | A: MSL.M.MapsTo ?x ?s0 ?m,
          B: MSL.M.MapsTo ?x ?s1 ?m |- _ =>
            assert (s0 = s1) by (
              apply MSL.M.FMF.find_mapsto_iff in A;
                apply MSL.M.FMF.find_mapsto_iff in B;
                  rewrite A in B; inversion_clear B; reflexivity
            ); subst; clear B
        | A: MSL.M.MapsTo ?x ?s ?m,
          B: MSL.M.In ?x (MSL.M.add _ _ ?m) -> False |- _ =>
            elim B; apply MSL.M.FMF.add_in_iff; right; exists s; exact A
        | A: MSL.M.MapsTo ?x ?s ?m,
          B: MSL.M.In ?x ?m -> False |- _ =>
            elim B; exists s; exact A
        | A: MSL.M.In ?x ?m -> False,
          B: MSL.M.MapsTo ?x ?s (MSL.M.add ?y _ ?m),
          C: ?x = ?y -> False |- _ =>
            apply MSL.M.FMF.add_neq_mapsto_iff in B;
              [elim A; exists s; exact B | ]
        | A: MSL.M.MapsTo ?x ?s ?m,
          B: MSL.M.In ?x (MSL.M.mapi _ ?m) -> False |- _ =>
            elim B; apply MSL.M.FMF.mapi_in_iff; exists s; exact A
        | A: MSL.M.In ?x ?m -> False,
          B: MSL.M.MapsTo ?x ?s (MSL.M.mapi _ ?m) |- _ =>
            elim A; rewrite <- MSL.M.FMF.mapi_in_iff; exists s; apply B
      end
    ).

  Ltac merge_parents :=
    repeat (
      match goal with
        | H: O.parent ?x = _,
          G: O.parent ?x = _
          |- _ => rewrite G in H; inv H
      end
    ).

  Lemma eq_get_add_same: forall k v mtop m,
    mtop = Some m ->
    get k (add k v mtop) = L.lub v (get_rec k m).
  Proof.
    intros. destruct mtop; inv H; simpl.
    remember (MSL.M.add k (L.lub v (get_rec k m)) (add_if_overlap k v m)) as m'.
    functional induction (get_rec k m'); MSL_simpl; elim e;
      apply MSL.M.FMF.add_in_iff; auto.
  Qed.

  Lemma eq_get_rec_parent: forall k p m,
    ~ MSL.M.In k m ->
    O.parent k = Some p ->
    get_rec k m = get_rec p m.
  Proof.
    intros ? ? ? NIN P.
    now functional induction (get_rec k m); MSL_simpl; merge_parents.
  Qed.

  Module OF := OverlapFacts(O).

  Definition get_add_above_increasing: forall x ax k v m,
    (* will need this axiom: *)
    (*LUB_INC_L: forall a b, L.ge a b -> L.ge (L.lub v a) (L.lub v b)*)
    (match m with None => True | Some m' => MSL.M.In O.top m' end) ->
    (forall x px, O.above px x -> L.ge (get px m) (get x m)) ->
    O.above ax x ->
    L.ge (get ax m) (get x m) ->
    L.ge (get ax (add k v m)) (get x (add k v m)).
  Proof.
    intros ????? HT WO A GE. destruct m as [m|]; [|apply L.ge_top].
    destruct (O.eq_dec x k) as [XK | NXK].
    Case "x = k".
    subst. erewrite eq_get_add_same; eauto.
    destruct (O.eq_dec ax k) as [AXK | NAXK].
    SCase "ax = k".
    subst. erewrite eq_get_add_same; eauto. now apply L.lub_inc_l.
    SCase "ax <> k".
    generalize dependent ax. refine (O.above_ind _ _); intros ax IND A GE NXK.
    simpl.
    remember (MSL.M.add k (L.lub v (get_rec k m)) (add_if_overlap k v m)) as m'.
    functional induction (get_rec ax m'); MSL_simpl.
    SSCase "1".
    apply MSL.M.FMF.add_mapsto_iff in e.
    destruct e as [? | [_ MT]]; intuition; subst.
    apply MSL.M.FMF.mapi_inv in MT.
    destruct MT as [x [? [? [? MT]]]]. subst.
    simpl in GE. erewrite mapsto_get_rec in GE; eauto.
    unfold lub_if_overlap.
    destruct (O.eq_dec k k0).
    congruence.
    destruct (O.overlap_dec k k0) as [O|NO]; simpl.
    apply L.lub_inc_l. auto.
    elim NO. symmetry. now apply O.above_overlaps.
    elim e. apply O.no_parent_is_top in e0. subst.
    apply MSL.M.FMF.add_in_iff. right.
    now apply MSL.M.FMF.mapi_in_iff.
    simpl in IND. apply IND.
    now apply O.parent_is_above.
    etransitivity; eauto. now apply O.parent_is_above.
    simpl in GE. erewrite eq_get_rec_parent in GE; eauto.
    intro. apply e. MSL.M.FMF.map_iff. right. now apply MSL.M.FMF.mapi_in_iff.
    intro. subst. eapply asymmetry. apply A. now apply O.parent_is_above.
    Case "x <> k".
    simpl.
    remember (MSL.M.add k (L.lub v (get_rec k m)) (add_if_overlap k v m)) as m'.
    functional induction (get_rec x m'); MSL_simpl.
    apply MSL.M.FMF.add_mapsto_iff in e.
    destruct e as [? | [_ MT]]; intuition; subst; try congruence.
    apply MSL.M.FMF.mapi_inv in MT.
    destruct MT as [x [? [? [? MT]]]]. subst.
    simpl in GE. setoid_rewrite mapsto_get_rec at 2 in GE; eauto.
    unfold lub_if_overlap. destruct (O.eq_dec k k0); try congruence. simpl.
    destruct (O.eq_dec ax k) as [AXK | NAXK].
    SCase "ax = k".
    subst. pose proof eq_get_add_same as EQ. specialize (EQ k v (Some m) m).
    simpl in EQ. rewrite EQ; auto. clear EQ.
    destruct (O.overlap_dec k k0); simpl. now apply L.lub_inc_l.
    eapply L.ge_trans. apply L.ge_lub_right. assumption.
    SCase "ax <> k".
    generalize dependent ax. refine (O.above_ind _ _); intros ax IND A GE NAXK.
    remember (MSL.M.add k (L.lub v (get_rec k m)) (add_if_overlap k v m)) as m'.
    functional induction (get_rec ax m'); MSL_simpl.
    apply MSL.M.FMF.add_mapsto_iff in e.
    destruct e as [? | [_ MT']]; intuition; subst; try congruence.
    apply MSL.M.FMF.mapi_inv in MT'.
    destruct MT' as [ax [? [? [? MT']]]]. subst.
    setoid_rewrite mapsto_get_rec in GE; eauto.
    unfold lub_if_overlap. destruct (O.eq_dec k k1); try congruence. simpl.
    destruct (O.overlap_dec k k0); destruct (O.overlap_dec k k1); simpl.
    now apply L.lub_inc_l.
    elim n1. symmetry. eapply OF.above_overlaps_too; eauto. now symmetry.
    eapply L.ge_trans. apply L.ge_lub_right. auto.
    auto.
    elim e. apply O.no_parent_is_top in e0. subst.
    apply MSL.M.FMF.add_in_iff. right.
    now apply MSL.M.FMF.mapi_in_iff.
    simpl in IND.
    destruct (O.eq_dec p k).
    subst. clear IHt0.
    pose proof eq_get_add_same as EQ. specialize (EQ k v (Some m) m).
    simpl in EQ. rewrite EQ; auto. clear EQ.
    erewrite eq_get_rec_parent in GE; eauto.
    destruct (O.overlap_dec k k0); simpl.
    now apply L.lub_inc_l.
    eapply L.ge_trans. apply L.ge_lub_right. assumption.
    intro. apply e. MSL.M.FMF.map_iff. right. now apply MSL.M.FMF.mapi_in_iff.
    apply IND.
    now apply O.parent_is_above.
    etransitivity; eauto. now apply O.parent_is_above.
    erewrite eq_get_rec_parent in GE; eauto.
    intro. apply e. MSL.M.FMF.map_iff. right. now apply MSL.M.FMF.mapi_in_iff.
    intro. subst. congruence.
    apply O.no_parent_is_top in e0. subst.
    elim e. MSL.M.FMF.map_iff. right. now apply MSL.M.FMF.mapi_in_iff.
    destruct (O.eq_dec ax p).
    subst. apply L.ge_refl. apply L.eq_refl.
    destruct (O.eq_dec k p).
    subst.
    pose proof eq_get_add_same as EQ. specialize (EQ p v (Some m) m).
    simpl in EQ. rewrite EQ; auto. clear EQ.
    remember (MSL.M.add p (L.lub v (get_rec p m)) (add_if_overlap p v m)) as m'.
    clear IHt0. (* ? *)
    functional induction (get_rec ax m'); MSL_simpl.
    apply MSL.M.FMF.add_mapsto_iff in e1.
    destruct e1 as [? | [_ MT']]; intuition; subst; try congruence.
    apply MSL.M.FMF.mapi_inv in MT'.
    destruct MT' as [v' [? [? [? MT']]]]. subst.
    simpl in *. setoid_rewrite mapsto_get_rec at 1 in GE; eauto.
    unfold lub_if_overlap. destruct (O.eq_dec p k); try congruence. simpl.
    destruct (O.overlap_dec p k); simpl.
    apply L.lub_inc_l. erewrite eq_get_rec_parent in GE; eauto.
    intro. apply e. MSL.M.FMF.map_iff. right. now apply MSL.M.FMF.mapi_in_iff.
    elim n1. symmetry. apply O.above_overlaps. eapply O.no_lozenge; eauto.
    elim e1. apply O.no_parent_is_top in e2. subst.
    apply MSL.M.FMF.add_in_iff. right.
    now apply MSL.M.FMF.mapi_in_iff.
    simpl in *. destruct (O.eq_dec p0 p).
    subst.
    pose proof eq_get_add_same as EQ. specialize (EQ p v (Some m) m).
    simpl in EQ. rewrite EQ; auto. apply L.ge_refl. apply L.eq_refl.
    apply IHt0; auto.
    etransitivity; eauto. now apply O.parent_is_above.
    eapply L.ge_trans; eauto. apply WO. now apply O.parent_is_above.
    apply IHt0.
    eapply O.no_lozenge; eauto.
    simpl in *. setoid_rewrite eq_get_rec_parent at 2 in GE; eauto.
    intro. apply e. MSL.M.FMF.map_iff. right. now apply MSL.M.FMF.mapi_in_iff.
    auto.
    reflexivity.
  Qed.

  Lemma ge_get_rec_add_1: forall x y s m,
    L.ge s (get_rec y m) ->
    L.ge (get_rec x (MSL.M.add y s m)) (get_rec x m).
  Proof.
    refine (O.above_ind _ _); intros.
    remember (MSL.M.add y s m) as m'.
    functional induction (get_rec x m);
      functional induction (get_rec k m');
        MSL_simpl; try solve [apply L.ge_bot]; merge_parents.
    Case "1".
    destruct (O.eq_dec k y).
    subst. MSL_simpl.
    functional induction (get_rec y m); MSL_simpl; auto.
    apply MSL.M.FMF.add_neq_mapsto_iff in e0; auto.
    MSL_simpl. apply L.ge_refl. apply L.eq_refl.
    Case "2".
    destruct (O.eq_dec k y).
    subst. MSL_simpl.
    functional induction (get_rec y m); MSL_simpl; merge_parents; auto.
    MSL_simpl. auto.
    Case "3".
    apply H. apply O.parent_is_above. exact e0. exact H0.
  Qed.

  Lemma ge_get_rec_add_2: forall x y s m,
    L.ge s (get_rec x m) ->
    L.ge (get_rec x (MSL.M.add y s m)) (get_rec x m).
  Proof.
    refine (O.above_ind _ _); intros.
    remember (MSL.M.add y s m) as m'.
    functional induction (get_rec x m);
      functional induction (get_rec k m');
        MSL_simpl; try solve [apply L.ge_bot]; merge_parents.
    Case "1".
    destruct (O.eq_dec k y).
    subst. MSL_simpl.
    apply MSL.M.FMF.add_neq_mapsto_iff in e0.
    MSL_simpl. apply L.ge_refl. apply L.eq_refl. auto.
    Case "2".
    destruct (O.eq_dec k y).
    subst. MSL_simpl.
    MSL_simpl. auto.
    Case "3".
    apply H. apply O.parent_is_above. exact e0. exact H0.
  Qed.

  Module HF := HierarchyFacts(O).

  Lemma eq_get_add_if_overlap: forall x s m,
    MSL.M.In x m ->
    L.eq (get_rec x m) (get_rec x (add_if_overlap x s m)).
  Proof.
    refine (O.above_ind _ _); intros.
    remember (add_if_overlap x s m) as m'. unfold add_if_overlap in Heqm'.
    functional induction (get_rec x m);
      functional induction (get_rec k m');
        MSL_simpl; merge_parents; try contradiction.
    pose proof MSL.M.FMF.mapi_inv as INV. simpl in INV.
    specialize (INV _ _ m k s1 (lub_if_overlap k s) e0).
    destruct INV as [a [y INV]]. intuition. subst. MSL_simpl.
    unfold lub_if_overlap in *.
    destruct (O.overlap_dec k k), (O.eq_dec k k); simpl.
    apply L.eq_refl.
    congruence.
    apply L.eq_refl.
    congruence.
  Qed.

  Theorem get_rec_mapi: forall x f m,
    (~ MSL.M.In x m
      /\ (forall y, O.above y x -> ~ MSL.M.In y m)
      /\ get_rec x m = L.bot
      /\ get_rec x (MSL.M.mapi f m) = L.bot
    ) \/
    exists y,
      (x = y \/ O.above y x) /\
      get_rec x (MSL.M.mapi f m) = f y (get_rec x m).
  Proof.
    refine (O.above_ind _ _); intros.
    remember (MSL.M.mapi f m) as m'.
    functional induction (get_rec x m);
      functional induction (get_rec k m');
        MSL_simpl; merge_parents; simpl in *; try discriminate.
    Case "1".
    right. exists k. intuition.
    apply MSL.M.FMF.mapi_inv in e0; destruct e0 as [v [k' INV]]; intuition;
      subst; simpl in *.
    now MSL_simpl.
    Case "2".
    left. intuition.
    apply O.no_parent_is_top in e0. subst.
    elim (HF.not_above_top _ H0).
    Case "1".
    clear IHt0 IHt1.
    specialize (H p0). feed H. auto using O.parent_is_above.
    specialize (H f m). intuition.
    SCase "1".
    left. intuition.
    destruct (O.eq_dec p0 y).
    SSCase "1".
    subst. contradiction.
    SSCase "2".
    apply H0 with (y := y). eauto using O.no_lozenge.
    exact H4.
    SCase "2".
    destruct H0 as [y ?]. intuition.
    SSCase "1".
    subst. right. exists y. intuition. right. auto using O.parent_is_above.
    SSCase "2".
    right. exists y. intuition. right.
    eapply transitivity; eauto using O.parent_is_above.
  Qed.

  Lemma ge_get_add_if_overlap: forall x s m,
    L.ge (L.lub s (get_rec x m)) (get_rec x (add_if_overlap x s m)).
  Proof.
    intros. destruct (MSL.M.FMF.In_dec m x).
    Case "In".
    eapply L.ge_trans. apply L.ge_lub_right.
    apply L.ge_refl. apply eq_get_add_if_overlap. exact i.
    Case "~In".
    unfold add_if_overlap, lub_if_overlap.
    pose proof get_rec_mapi.
    specialize (H x
      (fun (k0 : O.t) (v : L.t) =>
        if O.overlap_dec x k0 && negb (O.eq_dec x k0) then L.lub s v else v)
      m).
    intuition.
    rewrite H3. apply L.ge_bot.
    destruct H0. intuition. subst. rewrite H1.
    destruct (O.overlap_dec x0 x0), (O.eq_dec x0 x0); simpl.
    apply L.ge_lub_right.
    apply L.ge_refl. apply L.eq_refl.
    apply L.ge_lub_right.
    apply L.ge_lub_right.
    rewrite H1.
    destruct (O.overlap_dec x x0), (O.eq_dec x x0); simpl.
    apply L.ge_lub_right.
    apply L.ge_refl. apply L.eq_refl.
    apply L.ge_lub_right.
    apply L.ge_lub_right.
  Qed.

  Theorem get_add: forall x y s m,
    L.ge (get x (add y s m)) (get x m).
  Proof.
    intros. destruct m as [m|]; simpl.
    Case "m <> top".
    eapply L.ge_trans. apply ge_get_rec_add_1.
    destruct (MSL.M.FMF.In_dec m y).
    eapply L.ge_trans. apply L.ge_lub_right.
    apply L.ge_refl. apply eq_get_add_if_overlap. exact i.
    apply ge_get_add_if_overlap.
    unfold add_if_overlap.
    pose proof (get_rec_mapi x (lub_if_overlap y s) m). intuition.
    rewrite H1. apply L.ge_bot.
    destruct H0; intuition.
    subst. rewrite H1. unfold lub_if_overlap.
    destruct (O.overlap_dec y x0), (O.eq_dec y x0); simpl.
    apply L.ge_refl; apply L.eq_refl.
    apply L.ge_lub_right.
    apply L.ge_refl; apply L.eq_refl.
    apply L.ge_refl; apply L.eq_refl.
    rewrite H1. unfold lub_if_overlap.
    destruct (O.overlap_dec y x0), (O.eq_dec y x0); simpl.
    apply L.ge_refl; apply L.eq_refl.
    apply L.ge_lub_right.
    apply L.ge_refl; apply L.eq_refl.
    apply L.ge_refl; apply L.eq_refl.
    apply L.ge_top.
  Qed.

  Theorem get_add_overlap: forall x y s (m: t),
    (match m with None => True | Some m' => MSL.M.In O.top m' end) ->
    O.overlap x y ->
    L.ge (get x (add y s m)) s.
  Proof.
    intros ???? TOPIN REL. destruct m as [m|]; simpl.
    Case "m <> T".
    generalize dependent x; refine (O.above_ind _ _); intros.
    remember (MSL.M.add y (L.lub s (get_rec y m)) (add_if_overlap y s m))
    as m''.
    functional induction (get_rec x m''); MSL_simpl.
    SCase "1".
    destruct (O.eq_dec k y).
    SSCase "1".
    subst. apply MSL.M.FMF.add_mapsto_iff in e. intuition. subst.
    apply L.ge_lub_left.
    SSCase "2".
    apply MSL.M.FMF.add_neq_mapsto_iff in e; auto.
    apply MSL.M.FMF.mapi_inv in e. destruct e as [s' [k' e]]. intuition. subst.
    unfold lub_if_overlap.
    destruct (O.overlap_dec y k), (O.eq_dec y k); simpl; subst; intuition.
    apply L.ge_lub_left.
    SCase "2".
    apply O.no_parent_is_top in e0. subst. elim e.
    rewrite MSL.M.FMF.add_in_iff. right. apply MSL.M.FMF.mapi_in_iff.
    assumption.
    SCase "3".
    destruct (O.eq_dec y p).
    subst. intuition. eapply L.ge_trans.
    apply get_rec_add_same. apply L.ge_lub_left.
    apply IHt0; auto; intros. apply H; auto.
    eapply transitivity. apply H0. now apply O.parent_is_above.
    eapply O.parent_overlaps_too; eauto.
    apply L.ge_top.
  Qed.

  Theorem MSLge_lub_left: forall a b, MSL.ge (hmap_lub a b) a.
  Proof.
    intros a b k. unfold MSL.ge_m.
    destruct (MSL.M.find k (hmap_lub a b)) as [kab|]_eqn;
    destruct (MSL.M.find k a) as [ka|]_eqn;
    auto.

    pose proof hmap_lub_preserves_ge_get_rec_left as P.
    specialize (P a b ka L.bot k).
    setoid_rewrite get_rec_equation in P.
    rewrite Heqo in P. rewrite Heqo0 in P.
    eapply L.ge_trans. apply P. apply L.ge_refl. apply L.eq_refl. apply L.ge_bot.
    apply L.ge_lub_left.
    unfold hmap_lub in Heqo.
    rewrite MSL.M.map2i_1 in Heqo.
    rewrite Heqo0 in Heqo. now destruct (MSL.M.find k b).
    left. apply MSL.M.FMF.in_find_iff. congruence.
  Qed.

  Theorem ge_lub_left: forall a b, ge (lub a b) a.
  Proof.
    intros a b k. destruct a as [a|], b as [b|]; simpl.
    revert k. refine (O.above_ind _ _). intros k IND.
    setoid_rewrite get_rec_equation.
    pose proof (MSLge_lub_left a b k) as GE. unfold MSL.ge_m in GE.
    destruct
      (MSL.M.find (elt:=L.t) k (hmap_lub a b)) as [klub|]_eqn,
      (MSL.M.find (elt:=L.t) k a) as [ka|]_eqn.
    easy.
    unfold hmap_lub in Heqo. rewrite MSL.M.map2i_4 in Heqo. rewrite Heqo0 in Heqo. simpl in Heqo.
    destruct (MSL.M.find k b) as [kb|]_eqn; inv Heqo. rewrite get_rec_equation. rewrite Heqo0.
    destruct (O.parent k). apply L.ge_lub_left. apply L.ge_bot. now simpl.
    unfold hmap_lub in Heqo. rewrite MSL.M.map2i_4 in Heqo. rewrite Heqo0 in Heqo. simpl in Heqo.
    destruct (MSL.M.find k b) as [kb|]_eqn; inv Heqo. now simpl.
    destruct (O.parent k) as [pk|]_eqn.
    apply IND. now apply O.parent_is_above.
    apply L.ge_bot.
    apply L.ge_top.
    apply L.ge_top.
    apply L.ge_top.
  Qed.

  Theorem MSLge_lub_right: forall a b, MSL.ge (hmap_lub a b) b.
  Proof.
    intros a b k. unfold MSL.ge_m.
    destruct (MSL.M.find k (hmap_lub a b)) as [kab|]_eqn;
    destruct (MSL.M.find k b) as [kb|]_eqn;
    auto.

    pose proof hmap_lub_preserves_ge_get_rec_left as P.
    specialize (P a b L.bot kb k).
    setoid_rewrite get_rec_equation in P.
    rewrite Heqo in P. rewrite Heqo0 in P.
    eapply L.ge_trans. apply P. apply L.ge_bot. apply L.ge_refl. apply L.eq_refl.
    apply L.ge_lub_right.
    unfold hmap_lub in Heqo.
    rewrite MSL.M.map2i_1 in Heqo.
    rewrite Heqo0 in Heqo. now destruct (MSL.M.find k a).
    right. apply MSL.M.FMF.in_find_iff. congruence.
  Qed.

  Theorem ge_lub_right: forall a b, ge (lub a b) b.
  Proof.
    intros a b k. destruct a as [a|], b as [b|]; simpl.
    revert k. refine (O.above_ind _ _). intros k IND.
    setoid_rewrite get_rec_equation.
    pose proof (MSLge_lub_right a b k) as GE. unfold MSL.ge_m in GE.
    destruct
      (MSL.M.find (elt:=L.t) k (hmap_lub a b)) as [klub|]_eqn,
      (MSL.M.find (elt:=L.t) k b) as [kb|]_eqn.
    easy.
    unfold hmap_lub in Heqo. rewrite MSL.M.map2i_4 in Heqo. rewrite Heqo0 in Heqo. simpl in Heqo.
    destruct (MSL.M.find k a) as [ka|]_eqn; inv Heqo. rewrite get_rec_equation. rewrite Heqo0.
    destruct (O.parent k). apply L.ge_lub_right. apply L.ge_bot. now simpl.
    unfold hmap_lub in Heqo. rewrite MSL.M.map2i_4 in Heqo. rewrite Heqo0 in Heqo. simpl in Heqo.
    destruct (MSL.M.find k a) as [ka|]_eqn; inv Heqo. now simpl.
    destruct (O.parent k) as [pk|]_eqn.
    apply IND. now apply O.parent_is_above.
    apply L.ge_bot.
    apply L.ge_top.
    apply L.ge_top.
    apply L.ge_top.
  Qed.

End MkOverlapMapAux.

Module MkOverlapMap
  (O: Overlap)
  (OT: OrderedTypeLogicEq
    with Definition t := O.t
  )
  (L: SEMILATTICE_EXTENDED)
  <: OverlapMap(O)(L)
  <: SEMILATTICE_WITH_TOP.
  Module Raw := MkOverlapMapAux(O)(OT)(L).

  Definition has_top (m: Raw.t): Prop :=
    match m with
    | None => True
    | Some m => Raw.MSL.M.In O.top m
    end.

  Definition well_ordered (m: Raw.t): Prop :=
    forall x px, O.above px x -> L.ge (Raw.get px m) (Raw.get x m).

  Inductive well_formed (m: Raw.t): Prop :=
  | wf_intro: has_top m -> well_ordered m -> well_formed m.

  Definition t := { m : Raw.t | well_formed m }.

  Definition get (k: O.t) (m: t): L.t := Raw.get k (proj1_sig m).

  Program Definition add k v (m: t): t := exist _ (Raw.add k v (proj1_sig m)) _.
  Next Obligation.
    destruct m as [m [HT WO]].
    destruct m as [m|]; constructor; simpl; intuition.
    apply Raw.MSL.M.FMF.add_in_iff. right. now apply Raw.MSL.M.FMF.mapi_in_iff.
    unfold well_ordered in *. intros.
    pose proof Raw.get_add_above_increasing as GAAI.
    exact (GAAI x px k v (Some m) HT WO H (WO _ _ H)).
  Qed.

  Theorem get_add_same: forall k s m, L.ge (get k (add k s m)) s.
  Proof.
    intros. destruct m as [m OK].
    unfold get, add; simpl; apply Raw.get_add_same.
  Qed.

  Theorem get_add: forall x y s m, L.ge (get x (add y s m)) (get x m).
  Proof.
    intros. destruct m as [m OK].
    unfold get, add; simpl; apply Raw.get_add.
  Qed.

  Theorem get_add_overlap: forall x y s m,
    O.overlap x y ->
    L.ge (get x (add y s m)) s.
  Proof.
    intros. destruct m as [m OK].
    unfold get, add; simpl. inv OK. apply (Raw.get_add_overlap _ _ _ _ H0 H).
  Qed.

  (* Now let's make this a semi-lattice: *)

  Definition eq (m: t) (n: t): Prop := Raw.eq (proj1_sig m) (proj1_sig n).

  Theorem eq_refl: forall m, eq m m.
  Proof. intros. apply Raw.eq_refl. Qed.

  Theorem eq_sym: forall m n, eq m n -> eq n m.
  Proof. intros. apply Raw.eq_sym. exact H. Qed.

  Theorem eq_trans: forall m n o, eq m n -> eq n o -> eq m o.
  Proof. intros. eapply Raw.eq_trans; eauto. Qed.

  Definition beq (m: t) (n: t): bool := Raw.beq_has_top (proj1_sig m) (proj1_sig n).

  Theorem beq_correct: forall m n, beq m n = true -> eq m n.
  Proof.
    intros. apply Raw.beq_has_top_correct.
    destruct m as [m [HT WO]]. apply HT.
    destruct n as [n [HT WO]]. apply HT.
    exact H.
  Qed.

  Definition ge (m: t) (n: t): Prop := Raw.ge (proj1_sig m) (proj1_sig n).

  Theorem ge_refl: forall m n, eq m n -> ge m n.
  Proof.
    intros. now apply Raw.ge_refl.
  Qed.

  Theorem ge_trans: forall m n o, ge m n -> ge n o -> ge m o.
  Proof.
    intros. eapply Raw.ge_trans; eauto.
  Qed.

  Program Definition bot: t :=
    exist _ (Some (Raw.MSL.M.add O.top L.bot (Raw.MSL.M.empty _))) _.
  Next Obligation.
    constructor.
    apply Raw.MSL.M.FMF.add_in_iff. auto.
    refine (O.above_ind _ _); intros x IND px A. simpl.
    remember (Raw.MSL.M.add O.top L.bot (Raw.MSL.M.empty L.t)) as m;
    functional induction (Raw.get_rec x m);
    Raw.MSL.msimpl; try apply L.ge_bot.
    destruct (O.eq_dec px p).
    subst. apply L.ge_refl. apply L.eq_refl.
    apply IND. now apply O.parent_is_above.
    eapply O.no_lozenge; eauto.
  Qed.

  Theorem ge_bot: forall m, ge m bot.
  Proof.
    intros m k. destruct m as [[m|] [HT WO]]; simpl.
    replace (Raw.get_rec k (Raw.MSL.M.add O.top L.bot (Raw.MSL.M.empty L.t))) with L.bot.
    apply L.ge_bot. revert k. refine (O.above_ind _ _). intros k IND.
    setoid_rewrite Raw.get_rec_equation.
    destruct (Raw.MSL.M.find k
      (Raw.MSL.M.add O.top L.bot (Raw.MSL.M.empty L.t))) as [v|]_eqn.
    rewrite Raw.MSL.M.FMF.add_o in Heqo. destruct (OT.eq_dec O.top k).
    congruence. now compute in Heqo.
    destruct (O.parent k) as [pk|]_eqn.
    apply IND. now apply O.parent_is_above. easy.
    apply L.ge_top.
  Qed.

  Lemma wf_none: well_formed None.
  Proof.
    constructor. constructor. intros x px A. simpl. apply L.ge_top.
  Qed.

  Program Definition lub (m: t) (n: t): t := exist _ (Raw.lub m n) _.
  Next Obligation.
    repeat intro. destruct m as [m [HTm WOm]], n as [n [HTn WOn]]. simpl.
    destruct m as [m|], n as [n|]; simpl; auto using wf_none.
    remember (Raw.MSL.lub m n) as mn.
    constructor.
    Case "has_top".
    simpl. subst. unfold Raw.MSL.lub. apply Raw.MSL.M.map2i_5.
    intros. destruct a, b; simpl in *; try solve [congruence]; easy.
    left. apply HTm.
    Case "well_ordered".
    intros x px A. simpl. subst.
    unfold well_ordered in *. simpl in *.
    pose proof (WOm _ _ A) as GEm. pose proof (WOn _ _ A) as GEn.
    apply Raw.hmap_lub_preserves_ge_get_rec.
    apply L.ge_lub.
    apply L.lub_bot.
    apply L.bot_ge.
    apply WOm.
    apply WOn.
    easy.
  Qed.

  Theorem ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    destruct x as [x [HTx WOx]], y as [y [HTy WOy]]. unfold ge. simpl. apply Raw.ge_lub_left.
  Qed.

  Theorem ge_lub_right: forall x y, ge (lub x y) y.
  Proof.
    destruct x as [x [HTx WOx]], y as [y [HTy WOy]]. unfold ge. simpl. apply Raw.ge_lub_right.
  Qed.

  Program Definition top: t := exist _ Raw.top _.
  Next Obligation.
    constructor.
    now simpl.
    repeat intro. simpl. apply L.ge_top.
  Qed.

  Theorem ge_top: forall m, ge top m.
  Proof.
    intros. apply Raw.ge_top.
  Qed.

  Theorem get_top: forall k,
    get k top = L.top.
  Proof.
    auto.
  Qed.

  Theorem get_eq_top: forall mmap,
    eq mmap top ->
    (forall k, L.ge (get k mmap) L.top).
  Proof.
    intros mmap EQ k. destruct mmap as [m [HT WO]].
    unfold get; unfold eq in EQ; destruct m as [m|]; simpl in *.
    unfold Raw.eq in EQ. apply L.ge_refl. apply EQ.
    apply L.ge_top.
  Qed.

  Theorem ge_add: forall k v m,
    ge (add k v m) m.
  Proof.
    intros kadd v m k. simpl. apply Raw.get_add.
  Qed.

  Theorem ge_top_eq_top: forall m, ge m top -> eq top m.
  Proof.
    intros. unfold ge, eq in *. simpl in *. destruct m as [[m|][HT WO]]; simpl in *; auto.
    intros k. specialize (H k). simpl in *. apply L.ge_antisym. apply L.ge_top. easy.
    apply Raw.eq_refl.
  Qed.

End MkOverlapMap.

Module MemMap <: SEMILATTICE := MkOverlapMap(AbsPO)(AbsPOT)(PTSet).

Lemma MemMap_get_above:
  forall x ax,
    AbsPH.above ax x ->
    forall mmap e,
      PTSet.In e (MemMap.get x mmap) ->
      PTSet.In e (MemMap.get ax mmap).
Proof.
  intros x ax A mmap. destruct mmap as [m [HT WO]]. unfold MemMap.get; simpl.
  now apply WO.
Qed.

(* Result *)

Module Result <: SEMILATTICE.
  Module R := ProductSemiLattice(RegMap)(MemMap).
  Include R.
  Definition top := (RegMap.top, MemMap.top).
End Result.

Definition shift_offset (s: PTSet.t) (o: Int.int): PTSet.t :=
  PTSet.AbsPSet.fold
    (fun x saccu =>
      match x with
      | Blk _    => PTSet.AbsPSet.add x saccu
      | Loc b o' => PTSet.AbsPSet.add (Loc b (Int.add o o')) saccu
      end
    )
    s
    PTSet.AbsPSet.empty.

Definition unknown_offset (s: PTSet.t): PTSet.t :=
  PTSet.AbsPSet.fold
    (fun x saccu =>
      match x with
      | Blk _   => PTSet.AbsPSet.add x saccu
      | Loc b o => PTSet.AbsPSet.add (Blk b) saccu
      end
    )
    s
    PTSet.AbsPSet.empty.

Theorem In_unknown_offset_block_of_loc:
  forall b o s
    (IN: PTSet.AbsPSet.In (Loc b o) s),
    PTSet.In (Blk b) (unknown_offset s).
Proof.
  intros. unfold unknown_offset. rewrite PTSet.AbsPSet.fold_1.
  eapply fold_left_adds_prop.
  apply PTSet.F.elements_iff. eauto.
  intros. destruct x, y; subst; try (intuition; congruence).
  intros. simpl. apply PTSet.In_add_spec. auto.
  intros. destruct y; apply PTSet.In_add_spec; auto.
Qed.

Lemma In_unknown_offset_same_aux:
  forall p s
    (IN: PTSet.AbsPSet.In p s),
    PTSet.In p (unknown_offset s).
Proof.
  intros. destruct p. unfold unknown_offset. rewrite PTSet.AbsPSet.fold_1.
  eapply fold_left_adds_prop.
  apply PTSet.F.elements_iff. eauto.
  intros. destruct x, y; subst; try (intuition; congruence).
  simpl. intros. apply PTSet.In_add_spec. auto.
  intros. destruct y; apply PTSet.In_add_spec; auto.
  unfold unknown_offset. rewrite PTSet.AbsPSet.fold_1.
  eapply fold_left_adds_prop.
  apply PTSet.F.elements_iff. eauto.
  intros. destruct x, y; subst; try (intuition; congruence).
  simpl. intros. apply PTSet.In_add_spec. right. left. constructor. now compute.
  intros. destruct y; apply PTSet.In_add_spec; auto.
Qed.

Theorem In_unknown_offset_same:
  forall p s
    (IN: PTSet.In p s),
    PTSet.In p (unknown_offset s).
Proof.
  intros. apply PTSet.In_spec in IN. intuition.
  apply In_unknown_offset_same_aux. auto.
  destruct H as [ax [H IN]].
  unfold unknown_offset. rewrite PTSet.AbsPSet.fold_1.
  eapply fold_left_adds_prop.
  apply PTSet.F.elements_iff. eauto.
  intros. destruct x, y; subst; try (intuition; congruence).
  intros. destruct ax; apply PTSet.In_add_spec; auto.
  elim (not_loc_above _ _ _ H).
  intros. destruct y; apply PTSet.In_add_spec; auto.
Qed.

Definition image_of_ptset (s: PTSet.t) (m: MemMap.t): PTSet.t :=
  PTSet.AbsPSet.fold
    (fun p saccu => PTSet.lub (MemMap.get p m) saccu)
    s
    PTSet.bot.

Definition add_ptset_to_image (sadd: PTSet.t) (smod: PTSet.t) (m: MemMap.t)
  : MemMap.t :=
  PTSet.AbsPSet.fold (fun k maccu => MemMap.add k sadd maccu) smod m.

Definition addr_image addr args rmap :=
  match addr, args with
    | Aindexed o, r::nil             =>
      Some (shift_offset (RegMap.get r rmap) o)
    | Aindexed2 _, r1::r2::nil       =>
      Some (PTSet.lub
        (unknown_offset (RegMap.get r1 rmap))
        (unknown_offset (RegMap.get r2 rmap))
      )
    | Ascaled _ _, _::nil            => Some PTSet.bot
    | Aindexed2scaled _ _, r::_::nil =>
      Some (unknown_offset (RegMap.get r rmap))
    | Aglobal i o, nil               =>
      Some (PTSet.singleton (Loc (Just (Globals (Just i))) o))
    | Abased i _, _::nil
    | Abasedscaled _ i _, _::nil     =>
      Some (PTSet.singleton (Blk (Just (Globals (Just i)))))
    | Ainstack o, nil                =>
      Some (PTSet.singleton (Loc (Just Stack) o))
    | _, _                           => None
  end.

Definition transf_op op args dst rmap :=
  match op with
    | Oindirectsymbol i =>
      RegMap.add dst (PTSet.singleton (Loc (Just (Globals (Some i))) Int.zero)) rmap
    | Olea addr =>
      match addr_image addr args rmap with
        | None   => rmap (*!*)
        | Some s => RegMap.add dst s rmap
      end
    | Omove =>
      match args with
        | r::nil => RegMap.add dst (RegMap.get r rmap) rmap
        | _      => rmap (*!*)
      end
    | Osub =>
      match args with
        | r::_::nil => RegMap.add dst (unknown_offset (RegMap.get r rmap)) rmap
        | _         => rmap (*!*)
      end
    | _ => rmap
  end.

Definition transf_builtin ef args dst n (result: Result.t) :=
  let (rmap, mmap) := result in
  match ef with
  | EF_external _ _ =>
    (RegMap.add dst (PTSet.singleton (Blk (Just (Globals All)))) rmap, mmap)
  | EF_builtin _ _  =>
    (RegMap.add dst (PTSet.singleton (Blk (Just (Globals All)))) rmap, mmap)
    (*TODO: to do better things on vload/vstore global, we would first need
       to have strong updates, since Globals start at top anyway. *)
  | EF_vload _ | EF_vload_global _ _ _ => (RegMap.add dst PTSet.top rmap, mmap)
  | EF_vstore _ =>
    match args with
    | r1 :: r2 :: nil =>
      (rmap, add_ptset_to_image (RegMap.get r2 rmap) (RegMap.get r1 rmap) mmap)
    | _               => result
    end
  | EF_vstore_global _ i o =>
    match args with
    | r :: nil =>
      (rmap,
        MemMap.add (Loc (Just (Globals (Just i))) o) (RegMap.get r rmap) mmap)
    | _               => result
    end
  | EF_malloc        =>
    (RegMap.add dst
      (PTSet.singleton (Loc (Just (Allocs (Just n))) Int.zero)) rmap,
      mmap)
  | EF_free          => result
  | EF_memcpy _ _    =>
    match args with
    | rdst :: rsrc :: nil =>
      (rmap,
        add_ptset_to_image PTSet.top
        (unknown_offset (RegMap.get rdst rmap)) mmap
      )
    | _                   => result (*!*)
    end
  | EF_annot _ _     => result
  | EF_annot_val _ _ =>
    match args with
    | r1 :: nil => (RegMap.add dst (RegMap.get r1 rmap) rmap, mmap)
    | _       => result (*!*)
    end
  end.

Definition transf c n (result: Result.t) :=
  let (rmap, mmap) := result in
  match c!n with
  | Some instr =>
    match instr with
    | Inop _                         => result
    | Iop op args dst succ           => (transf_op op args dst rmap, mmap)
    | Iload chunk addr args dst succ =>
      match chunk with
      | Mint32 =>
        match addr_image addr args rmap with
        | None   => result (*!*)
        | Some s => (RegMap.add dst (image_of_ptset s mmap) rmap, mmap)
        end
      | _ => (RegMap.add dst PTSet.bot rmap, mmap)
      end
    | Istore chunk addr args src succ =>
      match chunk with
      | Mint32 =>
        match addr_image addr args rmap with
        | None      => result (*!*)
        | Some sdst =>
          (rmap, add_ptset_to_image (RegMap.get src rmap) sdst mmap)
        end
      | _ => result
      end
    | Icall sign fn args dst succ => (RegMap.add dst PTSet.top rmap, MemMap.top)
    | Itailcall sign fn args      => (rmap, MemMap.top)
    | Ibuiltin ef args dst succ   => transf_builtin ef args dst n result
    | Icond cond args ifso ifnot  => result
    | Ijumptable arg tbl          => result
    | Ireturn _                   => result
    end
  | None       => result
  end.

(* Kildall solver *)

Module Solver := Dataflow_Solver(Result)(NodeSetForward).

Definition coerce_solver (res: Solver.L.t): (RegMap.t * MemMap.t) := res.

Definition add_reg_top rmap r := RegMap.add r PTSet.top rmap.

Definition entry_rmap l := fold_left add_reg_top l RegMap.bot.

Definition entry_mmap :=
  MemMap.add (Blk (Just (Globals All))) PTSet.top (
  MemMap.add (Blk (Just Other)) PTSet.top (
  MemMap.bot)).

Definition entry_result l := (entry_rmap l, entry_mmap).

Definition funanalysis f :=
  Solver.fixpoint (successors f) (transf (fn_code f))
  ((fn_entrypoint f, entry_result (fn_params f)) :: nil).

Definition safe_funanalysis f :=
  match funanalysis f with
  | Some result => result
  | None        => PMap.init Result.top
  end.
Hint Unfold safe_funanalysis: unalias.

(* Proof invariant definitions *)

Definition abstracter := block -> option absb.

Definition valsat (v: val) (abs: abstracter) (s: PTSet.t) :=
  match v with
  | Vptr b o =>
    match abs b with
    | Some ab => PTSet.In (Loc ab o) s
    | None    => PTSet.ge s PTSet.top (* same as eq but easier in proofs *)
    end
  | _        => True
  end.
Hint Unfold valsat: unalias.

Definition regsat (r: reg) (rs: regset) (abs: abstracter) (rmap: RegMap.t) :=
  valsat rs#r abs (RegMap.get r rmap).
Hint Unfold regsat: unalias.

Definition memsat
  (b: block) (o: Int.int) (m: mem) (abs: abstracter) (mmap: MemMap.t)
  :=
  forall v
    (LOAD: Mem.loadv Mint32 m (Vptr b o) = Some v)
    ,
    (match abs b with
     | Some ab => valsat v abs (MemMap.get (Loc ab o) mmap)
     | None    => False
     end).
Hint Unfold memsat: unalias.

Definition ok_abs_mem (abs: abstracter) (m: mem) :=
  forall b, abs b <> None <-> Mem.valid_block m b.
Hint Unfold ok_abs_mem : unalias.

Definition ok_abs_genv (abs: abstracter) (ge: genv) :=
  forall i b
    (FIND: Genv.find_symbol ge i = Some b)
    ,
    abs b = Some (Just (Globals (Just i))).
Hint Unfold ok_abs_genv : unalias.

(* This is factored out to delay the instantiation of rmap, mmap in ok_stack *)
Inductive ok_abs_result_stack f pc rs rret abs: Prop :=
| ok_abs_result_stack_intro: forall rmap mmap
  (RPC:  (safe_funanalysis f)#pc = (rmap, mmap))
  (RSAT: forall r, regsat r rs abs rmap)
  (RET:  PTSet.ge (RegMap.get rret rmap) PTSet.top) (* same as eq, easier *)
  (MTOP: MemMap.eq mmap MemMap.top)
  ,
  ok_abs_result_stack f pc rs rret abs.

Inductive ok_stack (ge: genv) (b: block): list stackframe -> Prop :=
| ok_stack_nil:
  ok_stack ge b nil
| ok_stack_cons: forall r f bsp pc rs stk abs
  (STK:  ok_stack ge b stk)
  (MEM:  forall b', abs b' <> None -> b' < b)
  (GENV: ok_abs_genv abs ge)
  (SP:   abs bsp = Some (Just Stack))
  (RES:  ok_abs_result_stack f pc rs r abs)
  ,
  ok_stack ge b (Stackframe r f (Vptr bsp Int.zero) pc rs :: stk)
.

(* This is factored out to delay the instantiation of rmap, mmap in satisfy *)
Inductive ok_abs_result f pc rs m abs: Prop :=
| ok_abs_result_intro: forall rmap mmap
  (RPC:  (safe_funanalysis f)#pc = (rmap, mmap))
  (RSAT: forall r, regsat r rs abs rmap)
  (MSAT: forall b o, memsat b o m abs mmap)
  ,
  ok_abs_result f pc rs m abs.

Inductive satisfy (ge: genv) (abs: abstracter): state -> Prop :=
| satisfy_state: forall cs f bsp pc rs m
  (STK:  ok_stack ge (Mem.nextblock m) cs)
  (MEM:  ok_abs_mem abs m)
  (GENV: ok_abs_genv abs ge)
  (SP:   abs bsp = Some (Just Stack))
  (RES:  ok_abs_result f pc rs m abs)
  ,
  satisfy ge abs (State cs f (Vptr bsp Int.zero) pc rs m)
| satisfy_callstate: forall cs f args m
  (MEM:  ok_abs_mem abs m)
  (STK:  ok_stack ge (Mem.nextblock m) cs)
  (GENV: ok_abs_genv abs ge)
  ,
  satisfy ge abs (Callstate cs f args m)
| satisfy_returnstate: forall cs v m
  (MEM:  ok_abs_mem abs m)
  (STK:  ok_stack ge (Mem.nextblock m) cs)
  (GENV: ok_abs_genv abs ge)
  ,
  satisfy ge abs (Returnstate cs v m)
.

(* Lemmas *)

Ltac regsat_intro_unsafe rs r :=
  match goal with
  | H: Vptr _ _ = rs#r |- _ => apply symmetry in H; regsat_intro_unsafe rs r
  | R: (forall r, regsat r rs _ _),
    H: rs#r = Vptr _ _ |- _ =>
      let IN := fresh "IN" in
      pose proof (R r) as IN; unfold regsat, valsat in IN; rewrite H in IN
  end.
Tactic Notation "regsat_intro" constr(rs) constr(r) := regsat_intro_unsafe rs r.

Ltac crunch_eval :=
  match goal with
  | H: Val.add _ _ = _ |- _ => unfold Val.add in *; crunch_eval
  | H: Val.mul _ _ = _ |- _ => unfold Val.mul in *; crunch_eval
  | H: symbol_address _ _ _ = _ |- _ => unfold symbol_address in *; crunch_eval
  | H: Vptr _ _ = Vptr _ _ |- _ => inv H; crunch_eval
  | H: Some _ = None   |- _ => inv H
  | H: None   = Some _ |- _ => inv H
  | H: Some _ = Some _ |- _ => inv H; crunch_eval
  | H: (match _##?args with | nil => _ | _::_ => _ end) = _ |- _ =>
    destruct args; simpl in H; try solve [inv H]; crunch_eval
  | H: (match ?rs#?r with
        | Vundef => _ | Vint _ => _ | Vfloat _ => _ | Vptr _ _ => _
        end) = _ |- _ =>
    destruct rs#r as []_eqn; [ | | | regsat_intro rs r]; try solve [inv H]; crunch_eval
  | H: (if ?cond then _ else _) = _ |- _ =>
    destruct cond as []_eqn; try solve [inv H]; crunch_eval
  | H: (match ?opt with | Some _ => _ | None   => _ end) = _ |- _ =>
    destruct opt as []_eqn; try solve [inv H]; crunch_eval
  | H: (match ?opt with | Some _ => _ | None => _ end) |- _ =>
    destruct opt as []_eqn; try solve [congruence]; crunch_eval
  | H: (match ?val with
        | Vundef => _ | Vint _ => _ | Vfloat _ => _ | Vptr _ _ => _
        end) = _ |- _ =>
    destruct val as []_eqn; try solve [inv H]; crunch_eval
  | a: addressing |- _          => destruct a; simpl in *; crunch_eval
  (*| H: offset_sp ?sp _ = _ |- _ => unfold offset_sp in H; crunch_eval*)
  | H: option_map _ _ = _ |- _  => unfold option_map in H; crunch_eval
  | _ => idtac
  end.

Ltac merge :=
  match goal with
  | H: ?x = ?x |- _ => clear H; merge
  | H: (_, _) = (_, _) |- _ => inv H; merge
  | H1: ?a = None,
    H2: ?b = None |- _ => idtac (* prevents a loop *)
  | H1: ?x = ?a,
    H2: ?x = ?b |- _ =>
      rewrite H1 in H2; inv H2; merge
  | H1: ?a = ?x,
    H2: ?b = ?x |- _ =>
      rewrite <- H1 in H2; inv H2; merge
  | H1: ?x = ?a,
    H2: ?b = ?x |- _ =>
      rewrite H1 in H2; inv H2; merge
  | |- _ => idtac
  end.

Lemma above_same_loc: forall a b o o',
  AbsPH.above (Blk a) (Loc b o) ->
  AbsPH.above (Blk a) (Loc b o').
Proof.
  intros a b o o' A.
  unfold AbsPH.above in *.
  rewrite clos_trans_tn1_iff.
  rewrite clos_trans_tn1_iff in A. remember (Loc b o) as lbo. induction A.
  left. subst. inv H. now compute.
  right with (y:=y). subst. inv H. now compute.
  easy.
Qed.

Lemma In_unknown_offset:
  forall b o s
    (IN: PTSet.In (Loc b o) s)
    ,
    (forall o', PTSet.In (Loc b o') (unknown_offset s)).
Proof.
  intros. unfold unknown_offset. rewrite PTSet.AbsPSet.fold_1.
  apply PTSet.In_spec in IN. intuition.

  eapply fold_left_adds_prop.
  apply PTSet.F.elements_iff. eauto.
  intros. destruct x, y; subst; try (intuition; congruence).
  intros. simpl. apply PTSet.In_add_spec. right. left. left. now compute.
  intros. destruct y; apply PTSet.In_add_spec; auto.

  destruct H as [ax [H IN]].
  eapply fold_left_adds_prop.
  apply PTSet.F.elements_iff. eauto.
  intros. destruct x, y; subst; try (intuition; congruence).
  intros. destruct ax; apply PTSet.In_add_spec; simpl in *; intuition.

  right. left. eapply above_same_loc; eauto.
  elim (not_loc_above _ _ _ H).

  intros x y IN'. destruct y; apply PTSet.In_add_spec; intuition.
Qed.

Lemma above_loc_same_block: forall ba b o o',
  AbsPH.above (Blk ba) (Loc b o) ->
  AbsPH.above (Blk ba) (Loc b o').
Proof.
  intros. apply clos_trans_tn1_iff in H. apply clos_trans_tn1_iff.
  inv H.
  constructor. auto.
  right with (y := y); auto.
Qed.

Lemma In_shift_offset:
  forall b o s o' oshift
    (IN: PTSet.In (Loc b o) s)
    (SH: o' = Int.add o oshift)
    ,
    PTSet.In (Loc b o') (shift_offset s oshift).
Proof.
  intros. subst. rewrite Int.add_commut.
  unfold shift_offset. rewrite PTSet.AbsPSet.fold_1.
  apply PTSet.In_spec in IN. intuition.

  eapply fold_left_adds_prop.
  apply PTSet.F.elements_iff. eauto.
  intros. destruct x, y; subst; try (intuition; congruence).
  intros. simpl. apply PTSet.In_add_spec. auto.
  intros. destruct y; apply PTSet.In_add_spec; auto.

  destruct H as [ax [H IN]].
  eapply fold_left_adds_prop.
  apply PTSet.F.elements_iff. eauto.
  intros. destruct x, y; subst; try (intuition; congruence).
  intros. destruct ax; apply PTSet.In_add_spec; simpl; auto.
  right. left. eapply above_loc_same_block; eauto.
  elim (not_loc_above _ _ _ H).
  intros. destruct y; apply PTSet.In_add_spec; auto.
Qed.

Lemma unknown_offset_top:
  forall s
    (GETOP: PTSet.ge s PTSet.top)
    ,
    PTSet.ge (unknown_offset s) PTSet.top.
Proof.
  repeat intro. specialize (GETOP _ H). apply In_unknown_offset_same. auto.
Qed.

Lemma shift_offset_top:
  forall s
    (GETOP: PTSet.ge s PTSet.top)
    ,
    (forall oshift, PTSet.ge (shift_offset s oshift) PTSet.top).
Proof.
  repeat intro. clear H. unfold shift_offset. rewrite PTSet.AbsPSet.fold_1.
  pose proof (GETOP (Blk None)) as TOP.
  feed TOP. apply PTSet.In_top. apply PTSet.In_spec in TOP. intuition.

  eapply fold_left_adds_prop.
  apply PTSet.F.elements_iff. apply H.
  intros. destruct x0, y; subst; try (intuition; congruence).
  intros. simpl. apply PTSet.In_add_spec.
  destruct (AbsPH.eq_dec x (Blk None)); auto.
  right. left. apply AbsPH.top_above. reflexivity. auto.
  intros. destruct y; apply PTSet.In_add_spec; auto.

  destruct H as [ax [H IN]].
  elim (PTSet.HF.not_above_top _ H).
Qed.

Lemma In_image_of_ptset:
  forall x y mmap s,
    PTSet.In x s ->
    PTSet.In y (MemMap.get x mmap) ->
    PTSet.In y (image_of_ptset s mmap).
Proof.
  intros. unfold image_of_ptset. rewrite PTSet.AbsPSet.fold_1.
  apply PTSet.In_spec in H. intuition.

  eapply fold_left_adds_prop.
  apply PTSet.F.elements_iff. eauto.
  intros. destruct x0, y0; subst; try (intuition; congruence).
  intros. apply PTSet.ge_lub_left. auto.
  intros. apply PTSet.ge_lub_right. auto.

  destruct H1 as [ax [H IN]].
  eapply fold_left_adds_prop.
  apply PTSet.F.elements_iff. eauto.
  intros. destruct x0, y0; subst; try (intuition; congruence).
  intros. apply PTSet.ge_lub_left.
  pose proof MemMap.get_add_overlap.
  eapply MemMap_get_above; eauto.
  intros. apply PTSet.ge_lub_right. auto.
Qed.

Lemma In_add_ptset_to_image:
  forall x y sfrom sto mmap
    (FROM: PTSet.In x sfrom)
    (TO:   PTSet.In y sto)
    ,
    PTSet.In x (MemMap.get y (add_ptset_to_image sfrom sto mmap)).
Proof.
  intros. unfold add_ptset_to_image. rewrite PTSet.AbsPSet.fold_1.
  apply PTSet.In_spec in TO. intuition.

  eapply fold_left_adds_prop.
  apply PTSet.F.elements_iff. eauto.
  intros. destruct x0, y0; subst; try (intuition; congruence).
  intros. apply MemMap.get_add_same. auto.
  intros. apply MemMap.get_add. auto.

  destruct H as [ax [H IN]].
  eapply fold_left_adds_prop.
  apply PTSet.F.elements_iff. eauto.
  intros. destruct x0, y0; subst; try (intuition; congruence).
  intros. apply MemMap.get_add_overlap; auto.
  apply symmetry. now apply AbsPO.above_overlaps.
  intros. apply MemMap.get_add. auto.
Qed.

Lemma ge_add_ptset_to_image:
  forall mmap s s',
    MemMap.ge (add_ptset_to_image s s' mmap) mmap.
Proof.
  intros. unfold add_ptset_to_image. rewrite PTSet.AbsPSet.fold_1.

  eapply fold_left_preserves_prop.
  apply MemMap.ge_refl. apply MemMap.eq_refl.
  intros. eapply MemMap.ge_trans; eauto. apply MemMap.ge_add.
Qed.

Lemma addr_image_correct:
  forall ge rs rmap abs addr args b o ab s bsp
    (GENV: ok_abs_genv abs ge)
    (SP: abs bsp = Some (Just Stack))
    (RSAT: forall r, regsat r rs abs rmap)
    (EA: eval_addressing ge (Vptr bsp Int.zero) addr rs##args = Some (Vptr b o))
    (ABS: abs b = Some ab)
    (MPTA: addr_image addr args rmap = Some s)
    ,
    PTSet.In (Loc ab o) s.
Proof.
  intros.
  crunch_eval; merge.
  eapply In_shift_offset; eauto.
  apply PTSet.ge_lub_right. eapply In_unknown_offset; eauto.
  apply PTSet.ge_lub_left. eapply In_unknown_offset; eauto.
  eapply In_unknown_offset; eauto.
  specialize (GENV _ _ Heqo0). merge. apply PTSet.In_singleton.
  specialize (GENV _ _ Heqo). merge. apply PTSet.above_In_singleton.
  constructor. now compute.
  specialize (GENV _ _ Heqo0). merge. apply PTSet.above_In_singleton.
  constructor. now compute.
  rewrite Int.add_zero_l. apply PTSet.In_singleton.
Qed.

Lemma regsat_ge1:
  forall rs rmap abs rmap' r
    (RSAT: regsat r rs abs rmap)
    (GE:   RegMap.ge rmap' rmap)
    ,
    regsat r rs abs rmap'.
Proof.
  intros. unalias. destruct (rs#r); auto. destruct (abs b).
  destruct (abs b), rmap, rmap'; auto with ptset;
    try solve [eapply RegMap.get_ge; eauto].
  eapply PTSet.ge_trans; eauto. apply RegMap.get_ge. auto.
Qed.

Lemma regsat_ge:
  forall rs rmap abs rmap'
    (RSAT: forall r, regsat r rs abs rmap)
    (GE:   RegMap.ge rmap' rmap)
    ,
    (forall r, regsat r rs abs rmap').
Proof.
  intros. eapply regsat_ge1; eauto.
Qed.

Lemma regsat_assign_not_vptr:
  forall rs rmap abs v rdst
    (RSAT: forall r, regsat r rs abs rmap)
    (NPTR: match v with Vptr _ _ => False | _ => True end)
    ,
    (forall r, regsat r rs#rdst<-v abs rmap).
Proof.
  intros. specialize (RSAT r). unalias.
  destruct (peq r rdst).
  subst. rewrite Regmap.gss. destruct v; auto.
  contradiction.
  rewrite Regmap.gso; auto.
Qed.

Lemma regsat_assign_other:
  forall r res v rmap abs rs
    (RSAT:  forall r, regsat r rs abs rmap)
    (OTHER: res <> r)
    ,
    regsat r rs#res<-v abs rmap.
Proof.
  intros. specialize (RSAT r). unalias. rewrite Regmap.gso; auto.
Qed.

Lemma regsat_top:
  forall rs abs,
    (forall r, regsat r rs abs RegMap.top).
Proof.
  intros. unalias. destruct (rs#r) as []_eqn; auto. destruct (abs b) as []_eqn.
  apply RegMap.get_top. apply PTSet.In_top.
  apply RegMap.get_top.
Qed.

Lemma memsat_ge:
  forall m abs mmap mmap'
    (MSAT: forall b o, memsat b o m abs mmap)
    (GE:   MemMap.ge mmap' mmap)
    ,
    (forall b o, memsat b o m abs mmap').
Proof.
  repeat intro. unalias. specialize (MSAT _ _ _ LOAD).
  destruct (abs b), v; auto. destruct (abs b0).
  now apply GE.
  eapply PTSet.ge_trans; eauto. now apply GE.
Qed.

Lemma load_valid_block:
  forall chunk m b ofs v,
    Mem.load chunk m b ofs = Some v ->
    Mem.valid_block m b.
Proof.
  intros. eapply Mem.load_valid_access in H. eapply Mem.valid_access_implies in H.
  eapply Mem.valid_access_valid_block in H. auto. constructor.
Qed.

Lemma memsat_top:
  forall m abs
    (OKAM: ok_abs_mem abs m)
    ,
    (forall b o, memsat b o m abs MemMap.top).
Proof.
  unalias. intros. destruct (abs b) as []_eqn.
  destruct v; auto. destruct (abs b0) as []_eqn.
  rewrite MemMap.get_top. apply PTSet.In_top.
  rewrite MemMap.get_top. apply PTSet.ge_top.
  simpl in LOAD. apply load_valid_block in LOAD. now apply OKAM in LOAD.
Qed.

Lemma memsat_free:
  forall m abs ptm bf lo hi m'
    (MSAT: forall b o, memsat b o m abs ptm)
    (FREE: Mem.free m bf lo hi = Some m')
    ,
    (forall b o, memsat b o m' abs ptm).
Proof.
  intros. unfold memsat, valsat in *. intros. specialize (MSAT b o v).
  feed MSAT. simpl in *. erewrite Mem.load_free in LOAD. eauto. eauto.
  destruct (zeq b bf); auto. subst. apply Mem.load_valid_access in LOAD.
  eapply Mem.valid_access_free_inv_2 in LOAD; eauto.
  auto.
Qed.

Lemma ok_abs_mem_store:
  forall abs m chunk b o v m'
    (OKAM: ok_abs_mem abs m)
    (STOR: Mem.store chunk m b o v = Some m')
    ,
    ok_abs_mem abs m'.
Proof.
  unalias. split; intros.
  eapply Mem.store_valid_block_1; eauto. apply OKAM. auto.
  apply OKAM. eapply Mem.store_valid_block_2; eauto.
Qed.

Lemma ok_abs_mem_free:
  forall abs m b o s m'
    (OKAM: ok_abs_mem abs m)
    (FREE: Mem.free m b o s = Some m')
    ,
    ok_abs_mem abs m'.
Proof.
  unalias. split; intros.
  eapply Mem.valid_block_free_1; eauto. apply OKAM. auto.
  apply OKAM. eapply Mem.valid_block_free_2; eauto.
Qed.

Lemma ok_abs_mem_storebytes:
  forall abs m b o s m'
    (OK: ok_abs_mem abs m)
    (SB: Mem.storebytes m b o s = Some m')
    ,
    ok_abs_mem abs m'.
Proof.
  unalias; intros. specialize (OK b0). split; intros. apply OK in H.
  eapply Mem.storebytes_valid_block_1; eauto. apply OK.
  eapply Mem.storebytes_valid_block_2; eauto.
Qed.

Lemma ok_stack_incr:
  forall stk ge b, ok_stack ge b stk -> forall b', b <= b' -> ok_stack ge b' stk.
Proof.
  induction 1; intros; econstructor; eauto. intros. specialize (MEM b'0 H1). omega.
Qed.

Lemma ok_stack_alloc:
  forall stack ge m m' lo hi b,
    ok_stack ge (Mem.nextblock m) stack ->
    Mem.alloc m lo hi = (m', b) ->
    ok_stack ge (Mem.nextblock m') stack.
Proof.
  intros. eapply ok_stack_incr; eauto.
  setoid_rewrite Mem.nextblock_alloc at 2; eauto. omega.
Qed.

Lemma load_alloc_other':
  forall m1 lo hi m2 b,
    Mem.alloc m1 lo hi = (m2, b) ->
    forall b' ofs chunk,
    b <> b' ->
    Mem.load chunk m2 b' ofs = Mem.load chunk m1 b' ofs.
Proof.
  intros. destruct (Mem.load chunk m1 b' ofs) as []_eqn. pose proof Heqo as L.
  eapply Mem.load_valid_access in Heqo. eapply Mem.valid_access_implies in Heqo.
  eapply Mem.valid_access_valid_block in Heqo. erewrite Mem.load_alloc_unchanged; eauto.
  constructor. destruct (Mem.load chunk m2 b' ofs) as []_eqn; auto.
  eapply Mem.load_valid_access in Heqo0. eapply Mem.valid_access_implies in Heqo0.
  eapply Mem.valid_access_alloc_inv in Heqo0; eauto. destruct (eq_block b' b).
  congruence. eapply Mem.valid_access_load in Heqo0. destruct Heqo0. congruence.
  constructor.
Qed.

Lemma load_vptr_Mint32:
  forall chunk m a b o
    (LOAD: Mem.loadv chunk m a = Some (Vptr b o))
    ,
    chunk = Mint32.
Proof.
  intros. unfold Mem.loadv in LOAD. destruct a; try solve [inv LOAD].
  apply Mem.load_result in LOAD. symmetry in LOAD. apply decode_val_pointer_inv in LOAD.
  destruct LOAD. subst. auto.
Qed.

(* Theorems *)

Notation alias_interprets ge s := (exists abs, satisfy ge abs s).

Theorem alias_interprets_init:
  forall p st
    (IS:   initial_state p st),
    alias_interprets (Genv.globalenv p) st.
Proof.
  intros. inv IS.
  exists (fun b =>
    if zlt b (Mem.nextblock m0)
      then
        match Genv.invert_symbol ge b with
        | Some i => Some (Just (Globals (Just i)))
        | None   => Some (Just Other)
        end
      else None
  ).
  constructor.
  Case "ok_abs_mem".
  split; intros; destruct (zlt b0 (Mem.nextblock m0)); auto. elim H3. auto.
  destruct (Genv.invert_symbol); congruence.
  Case "ok_stack".
  constructor.
  Case "ok_abs_genv".
  unalias; intros. destruct (zlt b0 (Mem.nextblock m0)).
  eapply Genv.find_invert_symbol in FIND. unfold ge. rewrite FIND. auto.
  eapply Genv.find_symbol_not_fresh in FIND; eauto. contradiction.
Qed.

Theorem alias_interprets_step:
  forall ge st t st'
    (AI:   alias_interprets ge st)
    (STEP: step ge st t st')
    ,
    alias_interprets ge st'.
Proof.
  intros. destruct AI as [abs SAT].
  destruct st; destruct st'; try solve [inv STEP]; inv SAT; try inv RES.

  Case "state -> state".
  unfold safe_funanalysis in RPC. destruct (funanalysis f) as []_eqn.
  SCase "Kildall terminated".
  pose proof Heqo as FPS.
  eapply Solver.fixpoint_solution with (n:=pc)(s:=pc0) in FPS;
  [ |
  unfold successors; unfold successors_list; rewrite PTree.gmap1;
  inv STEP; rewrite H6; simpl; try destruct b; auto; eapply list_nth_z_in; eauto
  ].
  rewrite RPC in FPS. unfold Solver.L.ge in FPS.
  destruct (t0#pc0) as [rmap'' mmap'']_eqn.
  destruct (transf (fn_code f) pc (rmap, mmap)) as [rmap' mmap']_eqn.
  destruct FPS as [RGE MGE].
  inv STEP; unfold transf in Heqt0; rewrite H6 in Heqt0; inv Heqt0;
  try solve [exists abs; constructor; auto; econstructor;
    [unalias; rewrite Heqo; eauto | eapply regsat_ge; eauto | eapply memsat_ge; eauto]].
  SSCase "Iop".
  exists abs; constructor; auto.
  SSSCase "ok_abs_result".
  econstructor.
  SSSSCase "result".
  unfold safe_funanalysis. rewrite Heqo. eauto.
  SSSSCase "regsat".
  eapply regsat_ge; eauto.

  Ltac regsat_tac :=
    simpl in *;
    match goal with
    (* Easy case: same rs, higher rmap *)
    | H: forall r, regsat r ?rs ?abs ?rmap
      |- forall r, regsat r ?rs ?abs (RegMap.add _ _ ?rmap) =>
        eapply regsat_ge; [apply H | apply RegMap.ge_add]
    (* Simple cases: assigning something that is not a Vptr *)
    | |- forall r, regsat r _#_<-(Vundef) _ _ =>
      eapply regsat_assign_not_vptr; [ | auto]; regsat_tac
    | |- forall r, regsat r _#_<-(Vint _) _ _ =>
      eapply regsat_assign_not_vptr; [ | auto]; regsat_tac
    | |- forall r, regsat r _#_<-(Vfloat _) _ _ =>
      eapply regsat_assign_not_vptr; [ | auto]; regsat_tac

    | |- forall r, regsat r _#_<-(if ?cond then _ else _) _ _ =>
      destruct cond as []_eqn; regsat_tac
    | H: context [if ?cond then _ else _] |- _ =>
      destruct cond as []_eqn; try solve [inv H]; regsat_tac

    | |- match ?foo with
         | Vundef => _ | Vint _ => _ | Vfloat _ => _ | Vptr _ _ => _
         end =>
      destruct foo as []_eqn; regsat_tac

    | |- context [?rs#?r] =>
      destruct (rs#r) as []_eqn; simpl; try regsat_intro rs r; regsat_tac

    | H: context [?rs#?r] |- _ =>
      destruct (rs#r); simpl in H; inv H; try regsat_intro rs r; regsat_tac

    | H: context [match ?rs ## ?args with | nil => _ | _ :: _ => _ end] |- _ =>
      destruct args; simpl in H; try solve [inv H]; regsat_tac

    | v: val
      |- forall r, regsat r _#_<-?v _ _ =>
      destruct v; regsat_tac

    | |- match ?abs ?b with | Some _ => _ | None => _ end =>
      destruct (abs b) as []_eqn; regsat_tac

    | G: ok_abs_genv _ ?ge,
      H: Genv.find_symbol ?ge _ = _
      |- _ =>
      specialize (G _ _ H); merge; regsat_tac

    (* Almost done *)
    | |- PTSet.In _ (RegMap.get ?r (RegMap.add ?r _ _)) =>
      apply RegMap.get_add_same; regsat_tac
    | |- PTSet.ge (RegMap.get ?r (RegMap.add ?r _ _)) _ =>
      eapply PTSet.ge_trans; [apply RegMap.get_add_same | auto]; regsat_tac

    | |- forall r, regsat r _#?res<-_ _ _ =>
      let r := fresh "r" in intro r; destruct (peq res r);
        [ subst; unfold regsat, valsat; rewrite Regmap.gss
        | apply regsat_assign_other
        ];
        regsat_tac

    | c: condition |- _ => destruct c; regsat_tac
    | c: comparison |- _ => destruct c; regsat_tac

    (* Non-recursive cases *)
    | H: _ = Vptr _ _ |- _ => try solve [inv H]
    | H: Vptr _ _ = _ |- _ => try solve [inv H]

    | |- _ => auto
    end.

  destruct op; simpl in *; repeat (crunch_eval; regsat_tac).
  SSSSSCase "Oindirectsymbol".
  apply PTSet.In_singleton.
  SSSSSCase "Osub".
  eapply In_unknown_offset; eauto.
  apply unknown_offset_top; auto.
  SSSSSCase "Olea Aindexed".
  eapply In_shift_offset; eauto.
  apply shift_offset_top; auto.
  SSSSSCase "Olea Aindexed2".
  apply PTSet.ge_lub_right. eapply In_unknown_offset; eauto.
  eapply PTSet.ge_trans. apply PTSet.ge_lub_right. apply unknown_offset_top; auto.
  apply PTSet.ge_lub_left. eapply In_unknown_offset; eauto.
  eapply PTSet.ge_trans. apply PTSet.ge_lub_left. apply unknown_offset_top; auto.
  SSSSSCase "Olea Aindexed2scaled".
  eapply In_unknown_offset; eauto.
  apply unknown_offset_top; auto.
  SSSSSCase "Olea Aglobal".
  apply PTSet.In_singleton.
  SSSSSCase "Olea Abased".
  apply PTSet.above_In_singleton. constructor. now compute.
  SSSSSCase "Olea Abasedscaled".
  apply PTSet.above_In_singleton. constructor. now compute.
  SSSSSCase "Olea Ainstack".
  rewrite Int.add_zero_l. apply PTSet.In_singleton.
  SSSSCase "memsat".
  eapply memsat_ge; eauto.
  SSCase "Iload".
  exists abs; constructor; auto.
  SSSCase "ok_abs_result".
  econstructor.
  SSSSCase "result".
  unfold safe_funanalysis. rewrite Heqo. eauto.
  SSSSCase "regsat".
  eapply regsat_ge; eauto.
  destruct chunk; try solve [inv H0;
    eapply regsat_assign_not_vptr;
      [ eapply regsat_ge; [auto | apply RegMap.ge_add]
      | destruct v; auto; apply load_vptr_Mint32 in H14; congruence
      ]
  ].
  intros. destruct (peq dst r).
  SSSSSCase "r = dst".
  subst. unfold regsat, valsat. rewrite Regmap.gss. destruct v; auto.
  destruct a as [ | | |ba oa]; try solve [inv H14].
  specialize (MSAT _ _ _ H14).
  destruct (abs ba) as []_eqn; [|contradiction].
  destruct (abs b) as []_eqn.
  SSSSSSCase "abs b = Some".
  crunch_eval; inv H0; apply RegMap.get_add_same; eapply In_image_of_ptset;
    eauto; merge.
  eapply In_shift_offset; eauto.
  apply PTSet.ge_lub_right. eapply In_unknown_offset; eauto.
  apply PTSet.ge_lub_left. eapply In_unknown_offset; eauto.
  eapply In_unknown_offset; eauto.
  specialize (GENV _ _ Heqo2). merge. apply PTSet.In_singleton.
  specialize (GENV _ _ Heqo1). merge. apply PTSet.above_In_singleton.
  constructor. now compute.
  specialize (GENV _ _ Heqo1). merge. apply PTSet.above_In_singleton.
  constructor. now compute.
  rewrite Int.add_zero_l. apply PTSet.In_singleton.
  SSSSSSCase "abs b = None".
  crunch_eval; inv H0; (
  eapply PTSet.ge_trans;
    [ apply RegMap.get_add_same
    | repeat intro; eapply In_image_of_ptset; [ | apply MSAT; apply PTSet.In_top]
    ]); merge.
  eapply In_shift_offset; eauto.
  apply PTSet.ge_lub_right. eapply In_unknown_offset; eauto.
  apply PTSet.ge_lub_left. eapply In_unknown_offset; eauto.
  eapply In_unknown_offset; eauto.
  apply unknown_offset_top; auto. apply PTSet.In_top.
  specialize (GENV _ _ Heqo2). merge. apply PTSet.In_singleton.
  specialize (GENV _ _ Heqo3). merge. apply PTSet.above_In_singleton.
  constructor. now compute.
  specialize (GENV _ _ Heqo3). merge. apply PTSet.above_In_singleton.
  constructor. now compute.
  merge. rewrite Int.add_zero_l. apply PTSet.In_singleton.
  SSSSSCase "r <> dst".
  eapply regsat_assign_other; eauto. destruct addr_image; inv H0; auto.
  eapply regsat_ge; eauto. apply RegMap.ge_add.
  SSSSCase "memsat".
  eapply memsat_ge; eauto. eapply MemMap.ge_trans; eauto.
  destruct chunk; try solve [inv H0; apply MemMap.ge_refl; apply MemMap.eq_refl].
  destruct addr_image; inv H0; apply MemMap.ge_refl; apply MemMap.eq_refl.
  SSCase "Istore".
  assert (MGE': MemMap.ge mmap' mmap) by (
  destruct chunk; try solve [inv H0; apply MemMap.ge_refl; apply MemMap.eq_refl];
  destruct addr_image; inv H0;
    [ apply ge_add_ptset_to_image
    | apply MemMap.ge_refl; apply MemMap.eq_refl
    ]).
  exists abs. destruct a; try solve [inv H14]. constructor; auto.
  SSSCase "ok_stack".
  erewrite Mem.nextblock_store; eauto.
  SSSCase "ok_abs_mem".
  eapply ok_abs_mem_store; eauto.
  SSSCase "ok_abs_result".
  econstructor.
  SSSSCase "result".
  unfold safe_funanalysis. rewrite Heqo. eauto.
  SSSSCase "regsat".
  eapply regsat_ge; eauto. eapply RegMap.ge_trans; eauto. eapply RegMap.ge_refl.
  destruct chunk; try solve [inv H0; apply RegMap.eq_refl].
  destruct addr_image; inv H0; apply RegMap.eq_refl.
  SSSSCase "memsat".
  eapply memsat_ge; eauto.
  intros. specialize (MSAT b0 o). unfold memsat, valsat in *. intros.
  pose proof (Mem.valid_access_load m Mint32 b0 (Int.unsigned o)) as LOAD'.
  feed LOAD'. eapply Mem.store_valid_access_2; eauto. eapply Mem.load_valid_access; eauto.
  destruct LOAD' as [v' LOAD']. specialize (MSAT _ LOAD').
  destruct (zeq b b0).
  SSSSSCase "Stored in b".
  subst.
  destruct (zlt (Int.unsigned i) (Int.unsigned o + size_chunk Mint32)).
  destruct (zlt (Int.unsigned o) (Int.unsigned i + size_chunk chunk)).
  SSSSSSCase "Overlapped offset o".
  destruct (abs b0) as []_eqn; [|contradiction].
  destruct v; auto. pose proof LOAD as LOAD''.
  eapply Mem.load_pointer_store in LOAD; eauto.
  intuition; try solve [omegaContradiction]. subst. simpl in *.
  assert (i = o)
    by (apply f_equal with (f:=Int.repr) in H5; rewrite Int.repr_unsigned in H5;
      rewrite Int.repr_unsigned in H5; auto). subst. clear z z0 H5.
  regsat_intro rs0 src.
  destruct (addr_image addr args rmap) as []_eqn; [|crunch_eval]. inv H0.
  eapply addr_image_correct in Heqo1; eauto.
  destruct (abs b) as []_eqn.
  SSSSSSSSCase "abs b = Some".
  apply In_add_ptset_to_image; auto.
  SSSSSSSSCase "abs b = None".
  repeat intro. apply In_add_ptset_to_image; auto.
  SSSSSSCase "Didn't overlap offset o".
  simpl in LOAD.
  erewrite Mem.load_store_other in LOAD; eauto; [|right; right; omega]. merge.
  destruct (abs b0) as []_eqn; [|contradiction].
  destruct v; auto.
  destruct (abs b) as []_eqn.
  SSSSSSSCase "abs b = Some".
  now apply MGE'.
  SSSSSSSCase "abs b = None".
  eapply PTSet.ge_trans; eauto. now apply MGE'.
  SSSSSSCase "Didn't overlap offset o, for another reason".
  simpl in LOAD.
  erewrite Mem.load_store_other in LOAD; eauto; [|right; left; omega]. merge.
  destruct (abs b0) as []_eqn; [|contradiction].
  destruct v; auto.
  destruct (abs b) as []_eqn.
  SSSSSSSCase "abs b = Some".
  now apply MGE'.
  SSSSSSSCase "abs b = None".
  eapply PTSet.ge_trans; eauto. now apply MGE'.
  SSSSSCase "Didn't store in b0".
  simpl in LOAD. erewrite Mem.load_store_other in LOAD; eauto. merge.
  destruct (abs b0) as []_eqn; [|contradiction].
  destruct v; auto.
  destruct (abs b1) as []_eqn.
  SSSSSSCase "abs b1 = Some".
  now apply MGE'.
  SSSSSSCase "abs b1 = None".
  eapply PTSet.ge_trans; eauto. now apply MGE'.
  SSCase "Ibuiltin".
  assert (RGE': RegMap.ge rmap' rmap) by (
  destruct ef; repeat (
    try solve [inv H0; apply RegMap.ge_add];
    try solve [inv H0; apply RegMap.ge_refl; apply RegMap.eq_refl];
    destruct args)).
  assert (MGE': MemMap.ge mmap' mmap).
  destruct ef; repeat (
    try solve [inv H0; apply ge_add_ptset_to_image];
    try solve [inv H0; apply MemMap.ge_refl; apply MemMap.eq_refl];
    try solve [inv H0; apply MemMap.ge_add];
    destruct args).
  destruct ef; inv H13; merge.
  SSSCase "EF_external".
  exists abs. constructor; auto.
  SSSSCase "ok_abs_result".
  econstructor.
  SSSSSCase "result".
  unfold safe_funanalysis. rewrite Heqo. eauto.
  SSSSSCase "regsat".
  intros; destruct (peq res r); [subst | eapply regsat_assign_other; eauto;
    eapply regsat_ge; [eauto | eapply RegMap.ge_trans; eauto]].
  unfold regsat, valsat. rewrite Regmap.gss. destruct v; auto.
  inv H1. specialize (GENV _ _ H4). rewrite GENV.
  eapply PTSet.ge_trans. apply RegMap.get_ge; apply RGE. apply RegMap.get_add_same.
  apply PTSet.above_In_singleton.
  right with (y := Blk (Some (Globals (Some id))));
    constructor; compute; try reflexivity.
  SSSSSCase "memsat".
  eapply memsat_ge; eauto.
  SSSCase "EF_builtin".
  exists abs. constructor; auto.
  SSSSCase "ok_abs_result".
  econstructor.
  SSSSSCase "result".
  unfold safe_funanalysis. rewrite Heqo. eauto.
  SSSSSCase "regsat".
  intros; destruct (peq res r); [subst | eapply regsat_assign_other; eauto;
    eapply regsat_ge; [eauto | eapply RegMap.ge_trans; eauto]].
  unfold regsat, valsat. rewrite Regmap.gss. destruct v; auto.
  inv H1. specialize (GENV _ _ H4). rewrite GENV.
  eapply PTSet.ge_trans. apply RegMap.get_ge; apply RGE. apply RegMap.get_add_same.
  apply PTSet.above_In_singleton.
  right with (y := Blk (Some (Globals (Some id))));
    constructor; compute; try reflexivity.
  SSSSSCase "memsat".
  eapply memsat_ge; eauto.
  SSSCase "EF_vload".
  exists abs. constructor; auto.
  SSSSCase "ok_abs_result".
  econstructor.
  SSSSSCase "result".
  unfold safe_funanalysis. rewrite Heqo. eauto.
  SSSSSCase "regsat".
  intros; destruct (peq res r); [subst | eapply regsat_assign_other; eauto;
    eapply regsat_ge; [eauto | eapply RegMap.ge_trans; eauto]].
  unfold regsat, valsat. rewrite Regmap.gss. destruct v; simpl; auto.
  regsat_tac.
  eapply RegMap.get_ge. eauto. apply RegMap.get_add_same. apply PTSet.In_top.
  eapply PTSet.ge_trans. apply RegMap.get_ge. eauto. apply RegMap.get_add_same.
  SSSSSCase "memsat".
  eapply memsat_ge; eauto.
  inv H1. (* Check whether the store is volatile *)
  SSSCase "EF_vstore (volatile)".
  exists abs. constructor; auto.
  SSSSCase "ok_abs_result".
  econstructor.
  SSSSSCase "result".
  unfold safe_funanalysis. rewrite Heqo. eauto.
  SSSSSCase "regsat".
  intros; destruct (peq res r); [subst | eapply regsat_assign_other; eauto;
    eapply regsat_ge; [eauto | eapply RegMap.ge_trans; eauto]].
  unfold regsat, valsat. rewrite Regmap.gss. auto.
  SSSSSCase "memsat".
  eapply memsat_ge; eauto. eapply MemMap.ge_trans; eauto.
  SSSCase "EF_vstore (not volatile)".
  exists abs. constructor; auto.
  SSSSCase "ok_stack".
  erewrite Mem.nextblock_store; eauto.
  SSSSCase "ok_abs_mem".
  eapply ok_abs_mem_store; eauto.
  SSSSCase "ok_abs_result".
  econstructor.
  SSSSSCase "result".
  unfold safe_funanalysis. rewrite Heqo. eauto.
  SSSSSCase "regsat".
  intros; destruct (peq res r); [subst | eapply regsat_assign_other; eauto;
    eapply regsat_ge; [eauto | eapply RegMap.ge_trans; eauto]].
  unfold regsat, valsat. rewrite Regmap.gss. auto.
  SSSSSCase "memsat".
  eapply memsat_ge; eauto.
  repeat (destruct args; try solve [inv H]). inv H. inv H0.
  intros. specialize (MSAT b0 o). unfold memsat, valsat in *. intros.
  pose proof (Mem.valid_access_load m Mint32 b0 (Int.unsigned o)) as LOAD'.
  feed LOAD'. eapply Mem.store_valid_access_2; eauto. eapply Mem.load_valid_access; eauto.
  destruct LOAD' as [v' LOAD']. specialize (MSAT _ LOAD').
  destruct (zeq b b0).
  SSSSSSCase "Stored in b".
  subst.
  destruct (zlt (Int.unsigned ofs) (Int.unsigned o + size_chunk Mint32)).
  destruct (zlt (Int.unsigned o) (Int.unsigned ofs + size_chunk chunk)).
  SSSSSSSCase "Overlapped offset o".
  destruct (abs b0) as []_eqn; [|contradiction].
  destruct v; auto. pose proof LOAD as LOAD''.
  eapply Mem.load_pointer_store in LOAD; eauto.
  intuition; try solve [omegaContradiction]. merge. subst. simpl in *.
  assert (o = ofs)
    by (apply f_equal with (f:=Int.repr) in H8; rewrite Int.repr_unsigned in H8;
      rewrite Int.repr_unsigned in H8; auto). subst. clear z z0 H8.
  regsat_intro rs r0. regsat_intro rs r. rewrite Heqo0 in IN0.
  destruct (abs b) as []_eqn.
  SSSSSSSSCase "abs b = Some".
  apply In_add_ptset_to_image; auto.
  SSSSSSSSCase "abs b = None".
  eapply PTSet.ge_trans; eauto. repeat intro. apply In_add_ptset_to_image; auto.
  SSSSSSSCase "Didn't overlap offset o".
  simpl in LOAD.
  erewrite Mem.load_store_other in LOAD; eauto; [|right; right; omega]. merge.
  destruct (abs b0) as []_eqn; [|contradiction].
  destruct v; auto.
  destruct (abs b) as []_eqn.
  SSSSSSSSCase "abs b = Some".
  now apply MGE'.
  SSSSSSSSCase "abs b = None".
  eapply PTSet.ge_trans; eauto. now apply MGE'.
  SSSSSSSCase "Didn't overlap offset o, for another reason".
  simpl in LOAD.
  erewrite Mem.load_store_other in LOAD; eauto; [|right; left; omega]. merge.
  destruct (abs b0) as []_eqn; [|contradiction].
  destruct v; auto.
  destruct (abs b) as []_eqn.
  SSSSSSSSCase "abs b = Some".
  now apply MGE'.
  SSSSSSSSCase "abs b = None".
  eapply PTSet.ge_trans; eauto. now apply MGE'.
  SSSSSSCase "Didn't store in b0".
  simpl in LOAD. erewrite Mem.load_store_other in LOAD; eauto. merge.
  destruct (abs b0) as []_eqn; [|contradiction].
  destruct v; auto.
  destruct (abs b1) as []_eqn.
  SSSSSSSCase "abs b1 = Some".
  now apply MGE'.
  SSSSSSSCase "abs b1 = None".
  eapply PTSet.ge_trans; eauto. now apply MGE'.
  SSSCase "EF_vload_global".
  exists abs. constructor; auto.
  SSSSCase "ok_abs_result".
  econstructor.
  SSSSSCase "result".
  unfold safe_funanalysis. rewrite Heqo. eauto.
  SSSSSCase "regsat".
  intros; destruct (peq res r); [subst | eapply regsat_assign_other; eauto;
    eapply regsat_ge; [eauto | eapply RegMap.ge_trans; eauto]].
  unfold regsat, valsat. rewrite Regmap.gss. destruct v; auto.
  regsat_tac.
  eapply RegMap.get_ge. eauto. apply RegMap.get_add_same. apply PTSet.In_top.
  eapply PTSet.ge_trans. apply RegMap.get_ge. eauto. apply RegMap.get_add_same.
  SSSSSCase "memsat".
  eapply memsat_ge; eauto.
  inv H2. (* Check whether the store is volatile *)
  SSSCase "EF_vstore_global (volatile)".
  exists abs. constructor; auto.
  SSSSCase "ok_abs_result".
  econstructor.
  SSSSSCase "result".
  unfold safe_funanalysis. rewrite Heqo. eauto.
  SSSSSCase "regsat".
  intros; destruct (peq res r); [subst | eapply regsat_assign_other; eauto;
    eapply regsat_ge; [eauto | eapply RegMap.ge_trans; eauto]].
  unfold regsat, valsat. rewrite Regmap.gss. auto.
  SSSSSCase "memsat".
  eapply memsat_ge; eauto. eapply MemMap.ge_trans; eauto.
  SSSCase "EF_vstore (not volatile)".
  exists abs. constructor; auto.
  SSSSCase "ok_stack".
  erewrite Mem.nextblock_store; eauto.
  SSSSCase "ok_abs_mem".
  eapply ok_abs_mem_store; eauto.
  SSSSCase "ok_abs_result".
  econstructor.
  SSSSSCase "result".
  unfold safe_funanalysis. rewrite Heqo. eauto.
  SSSSSCase "regsat".
  intros; destruct (peq res r); [subst | eapply regsat_assign_other; eauto;
    eapply regsat_ge; [eauto | eapply RegMap.ge_trans; eauto]].
  unfold regsat, valsat. rewrite Regmap.gss. auto.
  SSSSSCase "memsat".
  specialize (GENV _ _ H1).
  eapply memsat_ge; eauto.
  repeat (destruct args; try solve [inv H]). inv H. inv H0.
  intros b0 o. specialize (MSAT b0 o). unfold memsat, valsat in *.
  intros v LOAD.
  pose proof (Mem.valid_access_load m Mint32 b0 (Int.unsigned o)) as LOAD'.
  feed LOAD'.
  eapply Mem.store_valid_access_2; eauto.
  eapply Mem.load_valid_access; eauto.
  destruct LOAD' as [v' LOAD']. specialize (MSAT _ LOAD').
  destruct (zeq b b0).
  SSSSSSCase "Stored in b".
  subst. rewrite GENV. rewrite GENV in MSAT. destruct v; auto.
  destruct (zlt (Int.unsigned ofs) (Int.unsigned o + size_chunk Mint32)).
  destruct (zlt (Int.unsigned o) (Int.unsigned ofs + size_chunk chunk)).
  SSSSSSSCase "Overlapped offset o".
  pose proof LOAD as LOAD''.
  eapply Mem.load_pointer_store in LOAD; eauto.
  intuition; try solve [omegaContradiction]. merge. subst. simpl in *.
  assert (o = ofs)
    by (apply f_equal with (f:=Int.repr) in H8; rewrite Int.repr_unsigned in H8;
      rewrite Int.repr_unsigned in H8; auto). subst. clear z z0 H8.
  regsat_intro rs r. rewrite H in H4.
  destruct (abs b) as []_eqn.
  SSSSSSSSCase "abs b = Some".
  apply MemMap.get_add_same. exact IN.
  SSSSSSSSCase "abs b = None".
  eapply PTSet.ge_trans; eauto. apply MemMap.get_add_same.
  SSSSSSSCase "Didn't overlap offset o".
  simpl in LOAD.
  erewrite Mem.load_store_other in LOAD; eauto; [|right; right; omega]. merge.
  destruct (abs b) as []_eqn.
  SSSSSSSSCase "abs b = Some".
  now apply MGE'.
  SSSSSSSSCase "abs b = None".
  eapply PTSet.ge_trans; eauto. now apply MGE'.
  SSSSSSSCase "Didn't overlap offset o, for another reason".
  simpl in LOAD.
  erewrite Mem.load_store_other in LOAD; eauto; [|right; left; omega]. merge.
  destruct (abs b) as []_eqn.
  SSSSSSSSCase "abs b = Some".
  now apply MGE'.
  SSSSSSSSCase "abs b = None".
  eapply PTSet.ge_trans; eauto. now apply MGE'.
  SSSSSSCase "Didn't store in b0".
  simpl in LOAD. erewrite Mem.load_store_other in LOAD; eauto. merge.
  destruct (abs b0) as []_eqn; [|contradiction].
  destruct v; auto.
  destruct (abs b1) as []_eqn.
  SSSSSSSCase "abs b1 = Some".
  now apply MGE'.
  SSSSSSSCase "abs b1 = None".
  eapply PTSet.ge_trans; eauto. now apply MGE'.
  SSSCase "EF_malloc".
  exists (fun x =>
    if zeq x b
      then Some (Just (Allocs (Just pc)))
      else abs x).
  constructor; auto.
  SSSSCase "ok_stack".
  erewrite Mem.nextblock_store; [|eauto]. eapply ok_stack_alloc; eauto.
  SSSSCase "ok_abs_mem".
  unalias. split; intros.
  destruct (zeq b0 b); [subst|].
  eapply Mem.store_valid_block_1; eauto. eapply Mem.valid_new_block; eauto.
  eapply Mem.store_valid_block_1; eauto. eapply Mem.valid_block_alloc; eauto.
  apply MEM. auto.
  destruct (zeq b0 b); [subst|].
  congruence.
  apply MEM.
  eapply Mem.store_valid_block_2 in H2; [|eauto].
  eapply Mem.valid_block_alloc_inv in H2; [|eauto].
  inv H2. congruence. auto.
  SSSSCase "ok_abs_genv".
  unalias; intros. destruct (zeq b0 b); auto.
  exfalso. subst. eapply Mem.fresh_block_alloc; eauto. apply MEM.
  erewrite GENV; [congruence|eauto].
  SSSSCase "sp".
  destruct (zeq bsp b); auto.
  subst. exfalso. eapply Mem.fresh_block_alloc; eauto. apply MEM. congruence.
  SSSSCase "ok_abs_result".
  econstructor.
  SSSSSCase "result".
  unfold safe_funanalysis. rewrite Heqo. eauto.
  SSSSSCase "regsat".
  intros; destruct (peq res r); [subst | ].
  SSSSSSCase "res = r".
  unfold regsat, valsat. rewrite Regmap.gss.
  destruct (zeq b b); [merge|congruence].
  eapply RegMap.get_ge. eauto. apply RegMap.get_add_same. apply PTSet.In_singleton.
  SSSSSSCase "res <> r".
  unfold regsat, valsat. rewrite Regmap.gso; [|auto]. destruct (rs#r) as []_eqn; auto.
  regsat_intro rs r. destruct (zeq b0 b).
  SSSSSSSCase "b0 = b".
  subst. eapply RegMap.get_ge. eauto. destruct (abs b) as []_eqn.
  SSSSSSSSCase "abs b = Some".
  exfalso. eapply Mem.fresh_block_alloc; eauto. apply MEM. congruence.
  SSSSSSSSCase "abs b = None".
  eapply RegMap.get_ge. apply RegMap.ge_add. apply IN. apply PTSet.In_top.
  SSSSSSSCase "b0 <> b".
  destruct (abs b0) as []_eqn.
  SSSSSSSSCase "abs b0 = Some".
  eapply RegMap.get_ge. eauto. eapply RegMap.get_ge. apply RegMap.ge_add. auto.
  SSSSSSSSCase "abs b0 = None".
  eapply PTSet.ge_trans. apply RegMap.get_ge. eauto.
  eapply PTSet.ge_trans. apply RegMap.get_ge. apply RegMap.ge_add. auto.
  SSSSSCase "memsat".
  eapply memsat_ge; eauto.
  unfold memsat, valsat in *. intros.
  destruct (zeq b0 b).
  SSSSSSCase "b0 = b".
  subst. destruct v; auto. simpl in LOAD. pose proof LOAD as LOAD'.
  eapply Mem.load_pointer_store in LOAD; eauto. intuition; try solve [congruence]; merge.
  simpl in H0. pose proof (Int.unsigned_range o). omegaContradiction.
  erewrite Mem.load_store_other in LOAD'; eauto.
  eapply Mem.load_alloc_same in LOAD'; eauto. inv LOAD'.
  SSSSSSCase "b0 <> b".
  simpl in *.
  erewrite Mem.load_store_other in LOAD; eauto.
  erewrite Mem.load_alloc_unchanged in LOAD; eauto.
  specialize (MSAT _ _ _ LOAD). destruct (abs b0) as []_eqn; auto.
  destruct v; auto. destruct (zeq b1 b); auto.
  subst. destruct (abs b) as []_eqn.
  SSSSSSSSCase "abs b = Some".
  exfalso. eapply Mem.fresh_block_alloc; eauto. apply MEM. congruence.
  SSSSSSSSCase "abs b = None".
  apply MSAT. apply PTSet.In_top.
  SSSSSSCase "b0 <> b".
  apply MEM. erewrite load_alloc_other' in LOAD; eauto.
  specialize (MSAT _ _ _ LOAD). destruct (abs b0); auto; congruence.
  SSSCase "EF_free".
  exists abs. constructor; auto.
  SSSSCase "ok_stack".
  erewrite Mem.nextblock_free; eauto.
  SSSSCase "ok_abs_mem".
  eapply ok_abs_mem_free; eauto.
  SSSSCase "ok_abs_result".
  econstructor.
  SSSSSCase "result".
  unfold safe_funanalysis. rewrite Heqo. eauto.
  SSSSSCase "regsat".
  intros; destruct (peq res r); [subst | eapply regsat_assign_other; eauto;
    eapply regsat_ge; [eauto | eapply RegMap.ge_trans; eauto]].
  unfold regsat, valsat. rewrite Regmap.gss. auto.
  SSSSSCase "memsat".
  eapply memsat_ge; eauto. eapply memsat_free; eauto.
  SSSCase "EF_memcpy".
  exists abs. constructor; auto.
  SSSSCase "ok_stack".
  erewrite Mem.nextblock_storebytes; eauto.
  SSSSCase "ok_abs_mem".
  eapply ok_abs_mem_storebytes; eauto.
  SSSSCase "ok_abs_result".
  econstructor.
  SSSSSCase "result".
  unfold safe_funanalysis. rewrite Heqo. eauto.
  SSSSSCase "regsat".
  intros; destruct (peq res r); [subst | eapply regsat_assign_other; eauto;
    eapply regsat_ge; [eauto | eapply RegMap.ge_trans; eauto]].
  unfold regsat, valsat. rewrite Regmap.gss. auto.
  SSSSSCase "memsat".
  eapply memsat_ge; eauto.
  unfold memsat, valsat in *. intros.
  repeat (destruct args; try solve [inv H]). inv H. inv H0.
  destruct (zeq b bdst).
  SSSSSSCase "b = bdst".
  subst. regsat_intro rs r. destruct (abs bdst) as []_eqn.
  SSSSSSSCase "abs bdst = Some".
  destruct v; auto. destruct (abs b) as []_eqn.
  SSSSSSSSCase "abs b = Some".
  apply In_add_ptset_to_image. apply PTSet.In_top. eapply In_unknown_offset; eauto.
  SSSSSSSSCase "abs b = None".
  eapply PTSet.ge_trans. repeat intro. apply In_add_ptset_to_image. apply H.
  eapply In_unknown_offset; eauto. apply PTSet.ge_refl. apply PTSet.eq_refl.
  SSSSSSSCase "abs bdst = None".
  eapply Mem.load_valid_access in LOAD. eapply Mem.valid_access_implies in LOAD.
  eapply Mem.valid_access_valid_block in LOAD.
  eapply Mem.storebytes_valid_block_2 in LOAD; eauto.
  apply MEM in LOAD. congruence. constructor.
  SSSSSSCase "b <> bdst".
  specialize (MSAT b o v). feed MSAT. simpl. erewrite <- Mem.load_storebytes_other; eauto.
  destruct (abs b); [|contradiction]. destruct v; auto. destruct (abs b0).
  SSSSSSSCase "abs b0 = Some".
  now apply MGE'.
  SSSSSSSCase "abs b0 = None".
  eapply PTSet.ge_trans. apply ge_add_ptset_to_image. auto.
  SSSCase "EF_annot".
  exists abs. constructor; auto.
  SSSSCase "ok_abs_result".
  econstructor.
  SSSSSCase "result".
  unfold safe_funanalysis. rewrite Heqo. eauto.
  SSSSSCase "regsat".
  intros; destruct (peq res r); [subst | eapply regsat_assign_other; eauto;
    eapply regsat_ge; [eauto | eapply RegMap.ge_trans; eauto]].
  unfold regsat, valsat. rewrite Regmap.gss. auto.
  SSSSSCase "memsat".
  eapply memsat_ge; eauto.
  SSSCase "EF_annot_val".
  exists abs. constructor; auto.
  SSSSCase "ok_abs_result".
  econstructor.
  SSSSSCase "result".
  unfold safe_funanalysis. rewrite Heqo. eauto.
  SSSSSCase "regsat".
  intros; destruct (peq res r); [subst | eapply regsat_assign_other; eauto;
    eapply regsat_ge; [eauto | eapply RegMap.ge_trans; eauto]].
  unfold regsat, valsat. rewrite Regmap.gss. destruct v; auto.
  inv H1. specialize (GENV _ _ H5). rewrite GENV.
  destruct args. inv H. destruct args; inv H. inv H0.
  regsat_intro rs r0. rewrite GENV in IN.
  eapply RegMap.get_ge. eauto. apply RegMap.get_add_same. auto.
  SSSSSCase "memsat".
  eapply memsat_ge; eauto. eapply MemMap.ge_trans; eauto.
  SCase "Kildall failed".
  rewrite PMap.gi in RPC. inv RPC.
  inv STEP; try solve [
    exists abs; constructor; auto; econstructor; eauto;
      unfold safe_funanalysis; rewrite Heqo; rewrite PMap.gi; reflexivity
  ].
  SSCase "Iop".
  exists abs; constructor; auto.
  SSSCase "ok_abs_result".
  econstructor.
  SSSSCase "result".
  unfold safe_funanalysis. rewrite Heqo. rewrite PMap.gi. reflexivity.
  SSSSCase "regsat".
  apply regsat_top.
  SSSSCase "memsat".
  apply memsat_top. auto.
  SSCase "Iload".
  exists abs; constructor; auto.
  SSSCase "ok_abs_result".
  econstructor.
  SSSSCase "result".
  unfold safe_funanalysis. rewrite Heqo. rewrite PMap.gi. reflexivity.
  SSSSCase "regsat".
  apply regsat_top.
  SSSSCase "memsat".
  apply memsat_top. auto.
  SSCase "Istore".
  destruct a; try solve [inv H14].
  exists abs; constructor; auto.
  SSSCase "ok_stack".
  erewrite Mem.nextblock_store; eauto.
  SSSCase "ok_abs_mem".
  eapply ok_abs_mem_store; eauto.
  SSSCase "ok_abs_result".
  econstructor.
  SSSSCase "result".
  unfold safe_funanalysis. rewrite Heqo. rewrite PMap.gi. reflexivity.
  SSSSCase "regsat".
  apply regsat_top.
  SSSSCase "memsat".
  apply memsat_top. eapply ok_abs_mem_store; eauto.
  SSCase "Ibuiltin".
  destruct ef; inv H13; merge; try solve [
    exists abs; constructor; auto; econstructor;
    [ unfold safe_funanalysis; rewrite Heqo; rewrite PMap.gi; reflexivity
    | apply regsat_top
    | apply memsat_top; auto
    ]
  ].
  inv H0.
  SSSCase "EF_vstore (volatile)".
  exists abs. constructor; auto.
  SSSSCase "ok_abs_result".
  econstructor.
  SSSSSCase "result".
  unfold safe_funanalysis. rewrite Heqo. rewrite Regmap.gi. reflexivity.
  SSSSSCase "regsat".
  apply regsat_top.
  SSSSSCase "memsat".
  apply memsat_top. auto.
  SSSCase "EF_vstore (not volatile)".
  exists abs. constructor; auto.
  SSSSCase "ok_stack".
  erewrite Mem.nextblock_store; eauto.
  SSSSCase "ok_abs_mem".
  eapply ok_abs_mem_store; eauto.
  SSSSCase "ok_abs_result".
  econstructor.
  SSSSSCase "result".
  unfold safe_funanalysis. rewrite Heqo. rewrite Regmap.gi. reflexivity.
  SSSSSCase "regsat".
  apply regsat_top.
  SSSSSCase "memsat".
  apply memsat_top. eapply ok_abs_mem_store; eauto.
  SSSCase "EF_vstore_global".
  exists abs. inv H1; constructor; auto.
  econstructor.
  unfold safe_funanalysis. rewrite Heqo. rewrite Regmap.gi. reflexivity.
  apply regsat_top.
  apply memsat_top. auto.
  erewrite Mem.nextblock_store; eauto.
  eapply ok_abs_mem_store; eauto.
  econstructor.
  unfold safe_funanalysis. rewrite Heqo. rewrite Regmap.gi. reflexivity.
  apply regsat_top.
  apply memsat_top. eapply ok_abs_mem_store; eauto.
  SSSCase "EF_malloc".
  exists (fun x =>
    if zeq x b
      then Some (Just (Allocs (Just pc)))
      else abs x).
  (* We will need this twice, so let's prove it upfront... *)
  assert (OKAM:
    ok_abs_mem
    (fun x : Z => if zeq x b then Some (Some (Allocs (Some pc))) else abs x)
    m0).
  unalias. split; intros.
  destruct (zeq b0 b); [subst|].
  eapply Mem.store_valid_block_1; eauto. eapply Mem.valid_new_block; eauto.
  eapply Mem.store_valid_block_1; eauto. eapply Mem.valid_block_alloc; eauto.
  apply MEM. auto.
  destruct (zeq b0 b); [subst|].
  congruence.
  apply MEM.
  eapply Mem.store_valid_block_2 in H2; [|eauto].
  eapply Mem.valid_block_alloc_inv in H2; [|eauto].
  inv H2. congruence. auto.
  constructor; auto.
  SSSSCase "ok_stack".
  erewrite Mem.nextblock_store; [|eauto]. eapply ok_stack_alloc; eauto.
  SSSSCase "ok_abs_genv".
  unalias; intros. destruct (zeq b0 b); auto.
  exfalso. subst. eapply Mem.fresh_block_alloc; eauto. apply MEM.
  erewrite GENV; [congruence|eauto].
  SSSSCase "sp".
  destruct (zeq bsp b); auto.
  subst. exfalso. eapply Mem.fresh_block_alloc; eauto. apply MEM. congruence.
  SSSSCase "ok_abs_result".
  econstructor.
  SSSSSCase "result".
  unfold safe_funanalysis. rewrite Heqo. rewrite PMap.gi. reflexivity.
  SSSSSCase "regsat".
  apply regsat_top.
  SSSSSCase "memsat".
  apply memsat_top. auto.
  SSSCase "EF_free".
  exists abs. constructor; auto.
  SSSSCase "ok_stack".
  erewrite Mem.nextblock_free; eauto.
  SSSSCase "ok_abs_mem".
  eapply ok_abs_mem_free; eauto.
  SSSSCase "ok_abs_result".
  econstructor.
  SSSSSCase "result".
  unfold safe_funanalysis. rewrite Heqo. rewrite PMap.gi. reflexivity.
  SSSSSCase "regsat".
  apply regsat_top.
  SSSSSCase "memsat".
  apply memsat_top. eapply ok_abs_mem_free; eauto.
  SSSCase "EF_memcpy".
  exists abs. constructor; auto.
  SSSSCase "ok_stack".
  erewrite Mem.nextblock_storebytes; eauto.
  SSSSCase "ok_abs_mem".
  eapply ok_abs_mem_storebytes; eauto.
  SSSSCase "ok_abs_result".
  econstructor.
  SSSSSCase "result".
  unfold safe_funanalysis. rewrite Heqo. rewrite PMap.gi. reflexivity.
  SSSSSCase "regsat".
  apply regsat_top.
  SSSSSCase "memsat".
  apply memsat_top.
  eapply ok_abs_mem_storebytes; eauto.

  Case "state -> callstate".
  exists abs. inv STEP.
  SCase "Icall".
  constructor; auto.
  SSCase "ok_stack".
  econstructor; eauto.
  SSSCase "MEM".
  apply MEM.
  SSSCase "ok_abs_result_stack".
  unfold safe_funanalysis in RPC. destruct (funanalysis f) as []_eqn.
  SSSSCase "Kildall terminated".
  pose proof Heqo as FPS.
  eapply Solver.fixpoint_solution with (n:=pc)(s:=pc') in FPS; [|
    unfold successors; unfold successors_list; rewrite PTree.gmap1;
      rewrite H6; simpl; auto; eapply list_nth_z_in; eauto].
  unfold transf in FPS. rewrite H6 in FPS. unfold Solver.L.ge in FPS.
  destruct (t#pc') as [rmap' mmap']_eqn. rewrite RPC in FPS. destruct FPS as [RGE MGE].
  econstructor.
  SSSSSCase "result".
  unfold safe_funanalysis. rewrite Heqo. eauto.
  SSSSSCase "regsat".
  eapply regsat_ge; eauto. eapply RegMap.ge_trans; eauto. apply RegMap.ge_add.
  SSSSSCase "ret".
  eapply PTSet.ge_trans. apply RegMap.get_ge; eauto.
  eapply PTSet.ge_trans. apply RegMap.get_add_same. auto with ptset.
  SSSSSCase "mem".
  pose proof MemMap.ge_top_eq_top. apply MemMap.eq_sym. now apply H.
  SSSSCase "Kildall failed".
  econstructor.
  SSSSSCase "result".
  unfold safe_funanalysis. rewrite Heqo. rewrite PMap.gi. unfold Result.top. eauto.
  SSSSSCase "regsat".
  eapply regsat_ge; eauto. apply RegMap.ge_top.
  SSSSSCase "ret".
  apply RegMap.get_top.
  SSSSSCase "mem".
  apply MemMap.eq_refl.
  SCase "Itailcall".
  constructor; auto.
  SSCase "ok_abs_mem".
  eapply ok_abs_mem_free; eauto.
  SSCase "ok_stack".
  erewrite Mem.nextblock_free; eauto.

  Case "state -> returnstate".
  exists abs. inv STEP.
  constructor; auto.
  SCase "ok_abs_mem".
  eapply ok_abs_mem_free; eauto.
  SCase "ok_stack".
  erewrite Mem.nextblock_free; eauto.

  Case "callstate -> state".
  inv STEP.
  exists (fun b =>
    if zeq b stk then Some (Just Stack) else
      match abs b with
      | Some ab => Some (Just
        (
          match ab with
          | Just (Globals (Some i)) => Globals (Some i)
          | Just (Globals None)     => Globals None
          | _                       => Other
          end
        ))
      | None    => None
      end
  ).
  constructor; auto.
  SCase "ok_stack".
  eapply ok_stack_alloc; eauto.
  SCase "ok_abs_mem".
  unalias; split; intros.
  SSCase "->".
  destruct (zeq b stk).
  SSSCase "b = stk".
  subst. eapply Mem.valid_new_block; eauto.
  SSSCase "b <> stk".
  destruct (abs b) as []_eqn; [|congruence].
  eapply Mem.valid_block_alloc; eauto. apply MEM. congruence.
  SSCase "<-".
  destruct (zeq b stk).
  SSSCase "b = stk".
  congruence.
  SSSCase "b <> stk".
  destruct (abs b) as []_eqn. destruct a; congruence.
  eapply Mem.valid_block_alloc_inv in H; eauto. intuition. apply MEM in H1; auto.
  SCase "ok_abs_genv".
  unalias; intros. specialize (GENV _ _ FIND). rewrite GENV.
  destruct (zeq b stk); [|auto]. subst.
  exfalso. eapply Mem.fresh_block_alloc; eauto. apply MEM. congruence.
  SCase "sp".
  destruct (zeq stk stk); [auto|congruence].
  SCase "ok_abs_result".
  destruct (funanalysis f0) as []_eqn.
  SSCase "Kildall will terminate".
  destruct t. destruct t. pose proof Heqo as FA.
  eapply Solver.fixpoint_entry in Heqo; [|constructor; eauto].
  destruct ((t, t1, t0) # (fn_entrypoint f0)) as [rmap mmap]_eqn.
  setoid_rewrite Heqp in Heqo. unfold entry_result in Heqo.
  destruct Heqo as [RGE MGE].
  econstructor.
  SSSCase "result".
  unfold safe_funanalysis. rewrite FA. eauto.
  SSSCase "regsat".
  eapply regsat_ge; eauto.
  generalize (fn_params f0). intros. unalias.
  destruct ((init_regs args l)#r) as []_eqn; auto.
  assert (InA eq r l).
  SSSSCase "assert".
  revert Heqv. revert args. induction l; intros.
  simpl in Heqv. rewrite Regmap.gi in Heqv. congruence.
  simpl in Heqv. destruct args.
  rewrite Regmap.gi in Heqv. congruence.
  destruct (peq r a).
  subst. constructor. auto.
  rewrite Regmap.gso in Heqv; [|auto]. right. eapply IHl; eauto.
  SSSSCase "end of assert".
  unfold entry_rmap. destruct (zeq b stk).
  subst.
  eapply fold_left_adds_prop; eauto; intros.
  apply RegMap.get_add_same. apply PTSet.In_top.
  apply RegMap.get_add. auto.
  destruct (abs b).
  eapply fold_left_adds_prop; eauto; intros.
  apply RegMap.get_add_same. apply PTSet.In_top.
  apply RegMap.get_add. auto.
  eapply fold_left_adds_prop; eauto; intros.
  apply RegMap.get_add_same.
  eapply PTSet.ge_trans. apply RegMap.get_add. auto.
  SSSCase "memsat".
  eapply memsat_ge; eauto. unalias. intros. destruct (zeq b stk).
  SSSSCase "b = stk".
  subst. simpl in LOAD. eapply Mem.load_alloc_same in LOAD; eauto. subst. auto.
  SSSSCase "b <> stk".
  destruct (abs b) as []_eqn.
  SSSSSCase "abs b = Some".
  destruct v; auto.
  destruct (zeq b0 stk).
  SSSSSSCase "b0 = stk".
  subst. unfold entry_mmap.
  destruct a; try destruct a; try destruct o0; try
  first
    [ solve [apply MemMap.get_add_overlap; [compute; auto | apply PTSet.In_top]]
    | solve [apply MemMap.get_add; apply MemMap.get_add_overlap;
      [compute; auto | apply PTSet.In_top]]
    ].
  apply MemMap.get_add_overlap. apply AbsPO.overlap_sym.
  apply AbsPO.above_overlaps. eright; [|left; compute; reflexivity].
  left; compute; reflexivity.
  apply PTSet.In_top.

  SSSSSSCase "b0 <> stk".
  destruct (abs b0) as []_eqn.
  SSSSSSSCase "abs b0 = Some".
  unfold entry_mmap.
  destruct a; try destruct a; try destruct o0; try first
    [ solve [apply MemMap.get_add_overlap; [compute; auto | apply PTSet.In_top]]
    | solve [apply MemMap.get_add; apply MemMap.get_add_overlap;
      [compute; auto | apply PTSet.In_top]]
    ].
  apply MemMap.get_add_overlap. apply AbsPO.overlap_sym.
  apply AbsPO.above_overlaps. eright; [|left; compute; reflexivity].
  left; compute; reflexivity.
  apply PTSet.In_top.
  SSSSSSSCase "abs b0 = None".
  unfold entry_mmap.
  destruct a; try destruct a; try destruct o0; try first
    [ solve [apply MemMap.get_add_overlap; compute; auto]
    | solve [eapply PTSet.ge_trans;
      [apply MemMap.get_add | apply MemMap.get_add_overlap; compute; auto]]
    ].
  apply MemMap.get_add_overlap. apply AbsPO.overlap_sym.
  apply AbsPO.above_overlaps.
  eright; [|left; compute; reflexivity].
  left; compute; reflexivity.
  SSSSSCase "abs b = None".
  eapply load_valid_block in LOAD. eapply Mem.valid_block_alloc_inv in LOAD; eauto.
  intuition. apply MEM in H; auto.
  SSCase "Kildall won't terminate".
  econstructor; intros.
  SSSCase "result".
  unfold safe_funanalysis. rewrite Heqo. rewrite PMap.gi. unfold Result.top. auto.
  SSSCase "regsat".
  unalias.
  destruct ((init_regs args (fn_params f0))#r); auto.
  destruct (zeq b stk).
  subst. apply RegMap.get_top. apply PTSet.In_top.
  destruct (abs b); apply RegMap.get_top; apply PTSet.In_top.
  SSSCase "memsat".
  unalias. intros. destruct (zeq b stk).
  SSSSCase "b = stk".
  subst. destruct v; auto. simpl in LOAD. eapply Mem.load_alloc_same in LOAD; eauto.
  congruence.
  SSSSCase "b <> stk".
  destruct (abs b) as []_eqn.
  SSSSSCase "abs b = Some".
  destruct v; auto.
  destruct (zeq b0 stk).
  SSSSSSCase "b0 = stk".
  subst. rewrite MemMap.get_top. apply PTSet.In_top.
  SSSSSSCase "b0 <> stk".
  destruct (abs b0) as []_eqn.
  rewrite MemMap.get_top. apply PTSet.In_top.
  apply MemMap.get_eq_top. apply MemMap.eq_refl.
  SSSSSCase "abs b = None".
  eapply load_valid_block in LOAD. eapply Mem.valid_block_alloc_inv in LOAD; eauto.
  intuition. apply MEM in H; auto.

  Case "callstate -> returnstate (un-inlined external calls)".
  inv STEP. destruct ef; inv H4; try solve [exists abs; constructor; auto].
  SCase "volatile store".
  exists abs; constructor; auto.
  inv H. auto. eapply ok_abs_mem_store; eauto.
  inv H. auto. erewrite Mem.nextblock_store; eauto.
  SCase "global volatile store".
  exists abs; constructor; auto.
  inv H0. auto. eapply ok_abs_mem_store; eauto.
  inv H0. auto. erewrite Mem.nextblock_store; eauto.
  SCase "malloc".
  exists (fun x =>
    if zeq x b
      then Some (Just Other)
      else abs x).
  constructor; auto.
  SSCase "ok_abs_mem".
  constructor; intros.
  destruct (zeq b0 b).
  subst. eapply Mem.store_valid_block_1; eauto. eapply Mem.valid_new_block; eauto.
  eapply Mem.store_valid_block_1; eauto. eapply Mem.valid_block_alloc; eauto. apply MEM.
  auto.
  destruct (zeq b0 b).
  congruence.
  apply MEM. eapply Mem.store_valid_block_2 in H1; [|eauto].
  eapply Mem.valid_block_alloc_inv in H1; eauto.
  intuition.
  SSCase "ok_stack".
  erewrite Mem.nextblock_store; [|eauto]. eapply ok_stack_alloc; eauto.
  SSCase "ok_abs_genv".
  unalias; intros. specialize (GENV _ _ FIND). destruct (zeq b0 b); [|auto].
  subst. exfalso. eapply Mem.fresh_block_alloc; eauto. apply MEM. congruence.
  SCase "free".
  exists abs; constructor; auto.
  SSCase "ok_abs_mem".
  eapply ok_abs_mem_free; eauto.
  SSCase "ok_stack".
  erewrite Mem.nextblock_free; eauto.
  SCase "memcpy".
  exists abs; constructor; auto.
  SSCase "ok_abs_mem".
  constructor; intros.
  eapply Mem.storebytes_valid_block_1; eauto. apply MEM. auto.
  apply MEM. eapply Mem.storebytes_valid_block_2; eauto.
  erewrite Mem.nextblock_storebytes; eauto.

  Case "returnstate -> state".
  inv STEP.
  clear MEM GENV abs. (* don't even think about using this abs! *)
  inv STK. (* use this good old abs instead! *)
  exists (fun b =>
    match abs b with
    | Some _ => abs b
    | None   => if (zlt b (Mem.nextblock m0)) then Some (Just Other) else None
    end).
  econstructor; eauto; intros.
  SCase "ok_abs_mem".
  constructor; intros.
  specialize (MEM b). destruct (abs b). red. apply MEM. auto.
  destruct (zlt b (Mem.nextblock m0)). auto. congruence.
  destruct (abs b) as []_eqn. congruence.
  destruct (zlt b (Mem.nextblock m0)); congruence.
  SCase "ok_abs_genv".
  unalias; intros. specialize (GENV _ _ FIND). rewrite GENV. auto.
  SCase "sp".
  rewrite SP. auto.
  SCase "ok_abs_result".
  inv RES.
  econstructor; eauto; intros.
  SSCase "regsat".
  unalias. destruct (peq res r); [subst|].
  SSSCase "res = r".
  rewrite Regmap.gss. destruct v; auto.
  destruct (abs b). apply RET. auto with ptset.
  destruct (zlt b (Mem.nextblock m0)); [|auto].
  apply RET. auto with ptset.
  SSSCase "res <> r".
  specialize (RSAT r). rewrite Regmap.gso; [|auto]. destruct (rs0#r); auto.
  destruct (abs b). auto.
  destruct (zlt b (Mem.nextblock m0)); [|auto].
  apply RSAT. auto with ptset.
  SSCase "memsat".
  unalias. intros. destruct (abs b). destruct v0; auto.
  destruct (abs b0); destruct (zlt b0 (Mem.nextblock m0));
  apply MemMap.get_eq_top; auto with ptset.
  destruct (zlt b (Mem.nextblock m0)). destruct v0; auto.
  destruct (abs b0).
  apply MemMap.get_eq_top; auto with ptset.
  destruct (zlt b0 (Mem.nextblock m0));
  apply MemMap.get_eq_top; auto with ptset.
  apply load_valid_block in LOAD. congruence.
Qed.