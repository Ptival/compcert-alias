Require Import Omega.
Require Import RelationClasses.
Require Import Relations.
Require Import Transitive_Closure.

Section Relation.

  Variable A: Type.
  Variable R: relation A.

  Theorem wf_irrefl: well_founded R -> Irreflexive R.
  Proof.
    intros WF x. induction (WF x) as [? _ IH].
    intros ?. now apply (IH x).
  Qed.

  Theorem wf_asymm: well_founded R -> Asymmetric R.
  Proof.
    intros WF x. induction (WF x) as [? _ IH].
    intros y Rxy Ryx. now apply (IH y Ryx x).
  Qed.

End Relation.

Section MeasuredRelation.

  Variable A: Type.
  Variable R: relation A.
  Variable measure: A -> nat.
  Variable ok_measure: forall x y, R x y -> measure x < measure y.

  Theorem wf_measure: well_founded R.
  Proof.
    intros x.
    assert (IND: forall n, forall z, measure z < n -> Acc R z).
    induction n; intros z Hz.
    exfalso. omega.
    constructor. intros y Ryz. apply IHn.
    specialize (ok_measure  _ _ Ryz). omega.
    apply IND with (n := S (measure x)). omega.
  Qed.

End MeasuredRelation.

Section WellFoundedRelation.

  Variable A: Type.
  Variable R: relation A.
  Variable WF: well_founded R.
  Notation tc_R := (clos_trans _ R).

  Instance wf_tc_so: StrictOrder tc_R.
  Proof.
    constructor.
    now apply wf_irrefl, wf_clos_trans.
    red. apply t_trans.
  Qed.

  Section UniqueAntecedent.

    Variable uniq_ante: forall x y z, R y x -> R z x -> y = z.

    Lemma wf_tc_common_ancestor: forall x a b,
      tc_R a x ->
      R b x ->
      a <> b ->
      tc_R a b.
    Proof.
      intros ??? tcRax Rbx NEQ.
      apply clos_trans_tn1_iff in tcRax.
      inversion_clear tcRax.
      contradict NEQ. now apply (uniq_ante x).
      apply clos_trans_tn1_iff.
      now rewrite (uniq_ante x b y).
   Qed.

  End UniqueAntecedent.

End WellFoundedRelation.

Module Type HierarchyFun.

  Parameter t: Type.

  Parameter eq_dec: forall (x y: t), {eq x y} + {~eq x y}.

  Parameter top: t.

  Parameter parent: t -> option t.

  Parameter measure: t -> nat.

  Axiom parent_measure: forall x px,
    parent x = Some px -> measure px < measure x.

  Axiom no_parent_is_top: forall x, parent x = None <-> x = top.

End HierarchyFun.

Module Type Hierarchy.

  Include HierarchyFun.

  Parameter above: @relation t.

  Declare Instance above_so: StrictOrder above.

  Parameter above_dec: forall x y, {above x y} + {~ above x y}.

  Axiom parent_is_above: forall x px,
    parent x = Some px -> above px x.

  Axiom above_ind: forall (P: t -> Prop),
    (forall x, (forall y, above y x -> P y) -> P x) ->
    (forall x, P x).

  Axiom top_above: forall t,
    t = top <-> (forall x, x <> top -> above t x).

  Axiom no_lozenge: forall x px ax,
    above ax x -> parent x = Some px -> ax <> px -> above ax px.

End Hierarchy.

Module MkHierarchy(H: HierarchyFun) <: Hierarchy.

  Include H.

  Definition is_parent y x := parent x = Some y.
  Lemma wf_is_parent: well_founded is_parent.
  Proof.
    apply wf_measure with (measure := measure).
    intros. apply parent_measure in H. omega.
  Qed.

  Definition above := clos_trans _ is_parent.
  Lemma wf_above: well_founded above.
  Proof.
    exact (wf_clos_trans _ _ wf_is_parent).
  Qed.

  Definition above_so := wf_tc_so _ _ wf_is_parent.
  Instance above_so_instance: StrictOrder above := above_so.

  Lemma above_implies: forall x ax,
    above ax x ->
    match parent x with
    | None => False
    | Some px => ax = px \/ above ax px
    end.
  Proof.
    intros. apply clos_trans_t1n_iff in H. induction H.
    rewrite H. now left.
    destruct (parent z); intuition; subst.
    right. apply clos_trans_t1n_iff. now left.
    right. right with (y := y). now left. exact H1.
  Qed.

  Definition above_dec: forall x y, {above x y} + {~ above x y}.
  Proof.
    assert (forall n,
      forall x y, measure y < n ->
        {above x y} + {~ above x y}
    ).
    induction n; intros.
    exfalso. omega.
    destruct (parent y) as [py|]_eqn.
    destruct (eq_dec x py).
    left. subst. constructor. easy.
    assert (My: measure py < measure y). apply parent_measure. exact Heqo.
    specialize (IHn x py). destruct IHn. omega.
    left. eright; eauto. now left.
    right. intro A. apply above_implies in A. rewrite Heqo in A. intuition.
    right. intro A. apply above_implies in A. rewrite Heqo in A. intuition.
    intros x y. apply X with (n := S (measure y)). omega.
  Defined.

  Theorem parent_is_above: forall x px,
    is_parent px x -> above px x.
  Proof.
    intros. constructor. exact H.
  Qed.

  Theorem above_ind: forall (P: t -> Prop),
    (forall x, (forall y, above y x -> P y) -> P x) ->
    (forall x, P x).
  Proof.
    apply well_founded_ind, wf_above.
  Qed.

  Theorem top_above: forall t,
    t = top <-> (forall x, x <> top -> above t x).
  Proof.
    split.
    (* -> *)
    intros EQ. subst. refine (above_ind _ _); intros.
    destruct (parent x) as [px|]_eqn.
    destruct (eq_dec px top).
    subst. exact (parent_is_above _ _ Heqo).
    apply transitivity with (y := px).
    exact (H _ (parent_is_above _ _ Heqo) n).
    exact (parent_is_above _ _ Heqo).
    apply no_parent_is_top in Heqo. contradiction.
    (* <- *)
    revert t0. refine (above_ind _ _); intros.
    destruct (eq_dec x top).
    auto.
    specialize (H0 _ n). now destruct irreflexivity with (x := x).
  Qed.

  Theorem no_lozenge: forall x px ax,
    above ax x ->
    is_parent px x ->
    ax <> px ->
    above ax px.
  Proof.
    intros. eapply wf_tc_common_ancestor; eauto.
    intros. unfold is_parent in *. rewrite H2 in H3. congruence.
  Qed.

(*
  Theorem above_ind: forall (P: t -> Prop),
    (forall x, (forall y, above y x -> P y) -> P x) ->
    (forall x, P x).
  Proof.
    apply well_founded_ind, wf_above.
  Qed.

  Lemma parent_top_is_none: parent top = None.
  Proof.
    pose proof (no_parent_is_top top) as [_ ?]. exact (H (eq_refl top)).
  Qed.

  Theorem not_above_top: forall x, ~ above x top.
  Proof.
    intros x H. apply clos_trans_t1n_iff in H. remember top as top.
    induction H.
    subst. unfold is_parent in H. rewrite parent_top_is_none in H. easy.
    now apply IHclos_trans_1n.
  Qed.

*)

End MkHierarchy.

Module HierarchyFacts(H: Hierarchy).

  Include H.

  Theorem parent_top_is_none: parent top = None.
  Proof.
    now apply (no_parent_is_top top).
  Qed.

  Instance above_so_instance: StrictOrder above := above_so.

  Theorem not_above_top: forall x, ~ above x top.
  Proof.
    intros x H.
    destruct (eq_dec x top).
    subst. now destruct irreflexivity with (x := top).
    destruct (top_above top) as [H' _].
    specialize (H' (eq_refl _) _ n).
    assert (above x x) by (eapply transitivity; eauto).
    now destruct irreflexivity with (x := x).
  Qed.

  Theorem above_measure: forall x ax,
    above ax x -> measure ax < measure x.
  Proof.
    refine (above_ind _ _). intros x IH ax ABOVE.
    destruct (parent x) as [px|]_eqn.
    destruct (eq_dec ax px).
    subst. now apply parent_measure.
    apply transitivity with (y := measure px).
    apply IH. now apply parent_is_above.
    exact (no_lozenge _ _ _ ABOVE Heqo n).
    now apply parent_measure.
    apply no_parent_is_top in Heqo. subst. elim (not_above_top _ ABOVE).
  Qed.

End HierarchyFacts.

Module Type Relationship.
  Include Hierarchy.
  Axiom overlap x y: t -> t -> Prop.
  Axiom overlap_dec: forall x y, {overlap x y} + {~ overlap x y}.
  (*Declare Instance overlap_irrefl: Irreflexive overlap.*)
  Declare Instance overlap_sym: Symmetric overlap.
  Axiom above_overlap: forall x y,
    above x y -> overlap x y.
  Axiom parent_overlap: forall x y px,
    overlap x y ->
    parent x = Some px ->
    overlap px y.
End Relationship.

(*
Module HtoR (H: Hierarchy) <: Relationship.

  Include H.

  Definition related x y := above x y \/ above y x.

  Definition related_dec: forall x y, {related x y} + {~ related x y}.
  Proof.
    intros.
    destruct (above_dec x y).
    now left; left.
    destruct (above_dec y x).
    now left; right.
    right. intro. now inversion H.
  Defined.

  Instance related_irrefl: Irreflexive related.
  Proof.
    intuition. repeat intro. destruct H; eapply irreflexivity; eauto.
  Qed.

  Instance related_sym: Symmetric related.
  Proof.
    repeat intro. unfold related in *. intuition.
  Qed.

End HtoR.
*)