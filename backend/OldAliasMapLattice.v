Require Import Coqlib.
Require Import Lattice.
Require Import OrderedType.

Require Import AliasFMapAVLPlus.
Require Import AliasLib.

Module MapSemiLattice
  (KEY: OrderedType)
  (VAL: SEMILATTICE)
  <: SEMILATTICE.

  Module M := FMapAVLPlus(KEY).

  Module FMF := FMapFacts.WFacts_fun KEY M.

  Definition t := M.t VAL.t.

  Definition eq (x y: t): Prop :=
    forall k,
      match M.find k x, M.find k y with
      | None, None     => True
      | Some a, Some b => VAL.eq a b
      | _, _           => False
      end.

  Theorem eq_refl: forall x, eq x x.
  Proof.
    repeat intro. destruct M.find. apply VAL.eq_refl. auto.
  Qed.

  Theorem eq_sym: forall x y, eq x y -> eq y x.
  Proof.
    repeat intro. unalias. specialize (H k).
    destruct M.find; destruct M.find; auto. apply VAL.eq_sym. auto.
  Qed.

  Theorem eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    repeat intro. unalias. specialize (H k). specialize (H0 k).
    destruct M.find; destruct M.find; destruct M.find; auto.
    eapply VAL.eq_trans; eauto. contradiction.
  Qed.

  Definition beq: t -> t -> bool := M.equal VAL.beq.

  Theorem beq_correct: forall x y, beq x y = true -> eq x y.
  Proof.
    repeat intro. apply M.equal_2 in H. inv H.
    destruct (M.find k x) as []_eqn; destruct (M.find k y) as []_eqn; auto.
    apply VAL.beq_correct. eapply H1; apply FMF.find_mapsto_iff; eauto.
    apply FMF.not_find_in_iff in Heqo0. elim Heqo0. apply H0.
    apply FMF.in_find_iff. congruence.
    apply FMF.not_find_in_iff in Heqo. elim Heqo. apply H0.
    apply FMF.in_find_iff. congruence.
  Qed.

  (* Assuming None is the same as bot *)
  Definition ge_m k x y :=
    match M.find k x, M.find k y with
    | None,   None   => True
    | Some a, Some b => VAL.ge a b
    | Some _, None   => True
    | None,   Some b => VAL.ge VAL.bot b
    end.
  Definition ge x y := forall k, ge_m k x y.
  Hint Unfold ge ge_m: unalias.

  Theorem ge_refl: forall x y, eq x y -> ge x y.
  Proof.
    repeat intro. unalias. specialize (H k).
    destruct (M.find k x) as []_eqn; destruct (M.find k y) as []_eqn; auto.
    apply VAL.ge_refl. auto. contradiction.
  Qed.

  Theorem ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof.
    repeat intro. unalias. specialize (H k). specialize (H0 k).
    destruct (M.find k x) as []_eqn; destruct (M.find k y) as []_eqn;
    destruct (M.find k z) as []_eqn; auto.
    eapply VAL.ge_trans; eauto.
    eapply VAL.ge_trans. apply VAL.ge_bot. auto.
    eapply VAL.ge_trans. eauto. auto.
  Qed.

  Definition bot: t := M.empty VAL.t.

  Theorem ge_bot: forall x, ge x bot.
  Proof.
    repeat intro. unalias.
    destruct (M.find k x) as []_eqn; rewrite FMF.empty_o; auto.
  Qed.

  Definition merge (k: KEY.t) o1 o2 :=
    match o1, o2 with
    | None,   None   => None
    | Some s, None   => Some (VAL.lub s VAL.bot)
    | None,   Some s => Some (VAL.lub VAL.bot s)
    | Some x, Some y => Some (VAL.lub x y)
    end.

  Theorem merge_compat:
    forall x y o1 o2,
      KEY.eq x y -> merge x o1 o2 = merge y o1 o2.
  Proof.
    reflexivity.
  Qed.

  Definition lub (m: t) (n: t): t :=
    M.map2i merge merge_compat m n.

  Ltac msimpl :=
    repeat (
      unfold not in *; try
        match goal with
        | H: M.find _ _ = Some _ |- _ =>
          apply FMF.find_mapsto_iff in H
        | H: M.find _ _ = None |- _ =>
         apply FMF.not_find_in_iff in H
        | H: M.MapsTo _ _ (M.empty _) |- _ => inversion H
        | H: M.MapsTo _ _ (M.add _ _ _) |- _ =>
         apply FMF.add_mapsto_iff in H; simpl in H; intuition; subst; auto
        | A: M.MapsTo ?x ?s0 ?m,
          B: M.MapsTo ?x ?s1 ?m |- _ =>
            assert (s0 = s1) by (
              apply FMF.find_mapsto_iff in A;
                apply FMF.find_mapsto_iff in B;
                  rewrite A in B; inversion_clear B; reflexivity
            ); subst; clear B
        | A: M.MapsTo ?x ?s ?m,
          B: M.In ?x (M.add _ _ ?m) -> False |- _ =>
            elim B; apply FMF.add_in_iff; right; exists s; exact A
        | A: M.MapsTo ?x ?s ?m,
          B: M.In ?x ?m -> False |- _ =>
            elim B; exists s; exact A
        | A: M.In ?x ?m -> False,
          B: M.MapsTo ?x ?s (M.add ?y _ ?m),
          C: ?x = ?y -> False |- _ =>
            apply FMF.add_neq_mapsto_iff in B;
              [elim A; exists s; exact B | ]
        | A: M.MapsTo ?x ?s ?m,
          B: M.In ?x (M.mapi _ ?m) -> False |- _ =>
            elim B; apply FMF.mapi_in_iff; exists s; exact A
        | A: M.In ?x ?m -> False,
          B: M.MapsTo ?x ?s (M.mapi _ ?m) |- _ =>
            elim A; rewrite <- FMF.mapi_in_iff; exists s; apply B
        end
    ).

  Theorem ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    repeat intro. unalias.
    destruct (M.find k (lub x y)) as []_eqn, (M.find k x) as []_eqn; msimpl; auto.
    unfold lub in Heqo.
    pose proof M.map2i_1. specialize (H _ _ _ merge merge_compat x y k).
    feed H. left. now exists t1.
    setoid_rewrite (proj1 (M.FMF.find_mapsto_iff _ _ _)) in H at 2; [|eauto]. simpl in H.
    destruct (M.find k y) as []_eqn; msimpl.
    apply VAL.ge_lub_left. apply VAL.ge_lub_left.
    elim Heqo. unfold lub.
    pose proof M.map2i_1. specialize (H _ _ _ merge merge_compat x y k).
    feed H. left. now exists t0.
    replace (M.find k x) with (Some t0) in H. simpl in H.
    destruct (M.find k y) as []_eqn; msimpl.
    destruct (M.find k x) as []_eqn; msimpl; reflexivity.
  Qed.

(*
  Lemma find_merge_some_left:
    forall k x y s,
    M.find k (M.map2i merge merge_compat x y) = merge k (Some s) (M.find k y) ->
    exists s', M.MapsTo k s' (M.map2i merge merge_compat x y) /\ VAL.ge s' s.
  Proof.
    intros. edestruct (merge_some_left _ _ _) as [s' M]. rewrite M in H. exists s'.
    split. now msimpl. pose proof ge_merge_left as GE. TODO. apply ge_merge_left.

    pose proof merge_some_left.
    edestruct H0 as [s' M]. rewrite M in H. pose proof ge_merge_left as ML. setoid_rewrite M in ML. apply ge_merge_left in M.
    setoid_rewrite (merge_some_left _ _ _) in H.

    erewrite merge_some_left in H.
*)

  Theorem ge_lub_right: forall x y, ge (lub x y) y.
  Proof.
    repeat intro. unalias.
    destruct (M.find k (lub x y)) as []_eqn, (M.find k y) as []_eqn; msimpl;
      auto.
    unfold lub in Heqo.
    pose proof M.map2i_1. specialize (H _ _ _ merge merge_compat x y k).
    feed H. right. now exists t1.
    replace (M.find k y) with (Some t1) in H.
    destruct (M.find k x) as []_eqn; simpl in H; msimpl; auto.
    apply VAL.ge_lub_right. apply VAL.ge_lub_right.
    destruct (M.find k y) as []_eqn; msimpl; reflexivity.
    elim Heqo. unfold lub.
    pose proof M.map2i_1. specialize (H _ _ _ merge merge_compat x y k).
    feed H. right. now exists t0.
    replace (M.find k y) with (Some t0) in H.
    destruct (M.find k x) as []_eqn; simpl in H; msimpl.
    destruct (M.find k y) as []_eqn; simpl in H; msimpl; reflexivity.
  Qed.

  Definition ge_k m j k :=
    match M.find j m, M.find k m with
    | None,   None   => True
    | Some a, Some b => VAL.ge a b
    | Some _, None   => True
    | None,   Some b => VAL.ge VAL.bot b
    end.
  Hint Unfold ge_k: unalias.

  Theorem lub_preserves_ge_k: forall m n x px
    (* TODO: possibly move these axioms in SEMILATTICE signature *)
    (LUB_INC_L: forall a b, VAL.ge a b ->
      forall c, VAL.ge (VAL.lub c a) (VAL.lub c b))
    (LUB_GE: forall a b c d,
      VAL.ge a b -> VAL.ge c d -> VAL.ge (VAL.lub a c) (VAL.lub b d))
    (LUB_BOT: forall a b,
      VAL.eq a VAL.bot -> VAL.eq b VAL.bot -> VAL.eq (VAL.lub a b) VAL.bot)
    (GE_BOT_EQ: forall x,
      VAL.ge VAL.bot x <-> VAL.eq VAL.bot x)
    ,
    ge_k m px x ->
    ge_k n px x ->
    ge_k (lub m n) px x.
  Proof.
    intros. unalias.

    pose proof M.map2i_1 as M2Ix.
    specialize (M2Ix _ _ _ merge merge_compat m n x).
    pose proof M.map2i_1 as M2Ipx.
    specialize (M2Ipx _ _ _ merge merge_compat m n px).

    destruct (M.find x (lub m n)) as []_eqn,
      (M.find px (lub m n)) as []_eqn,
      (M.find x m) as []_eqn, (M.find px m) as []_eqn,
      (M.find x n) as []_eqn, (M.find px n) as []_eqn;
      msimpl; auto; unfold lub in *;
    repeat (
      match goal with
      | I: M.In ?x ?m \/ _ -> _,
        M: M.MapsTo ?x ?v ?m |- _ =>
          feed I; [left; exists v; apply M|]; simpl in I; msimpl
      | I: _ \/ M.In ?x ?m -> _,
        M: M.MapsTo ?x ?v ?m |- _ =>
          feed I; [right; exists v; apply M|]; simpl in I; msimpl
      | Hm: M.In ?x ?m -> False,
        Hn: M.In ?x ?n -> False,
        MT: M.MapsTo ?x _ (M.map2i _ _ ?m ?n)
        |- _ =>
        apply M.FMF.find_mapsto_iff in MT; rewrite M.map2i_3 in MT;
          [ congruence|now simpl|now apply M.FMF.not_find_in_iff|now apply M.FMF.not_find_in_iff]
      end
    ); try solve
    [ now apply LUB_GE
    | apply LUB_GE; [easy | apply VAL.ge_bot]
    ].
    apply LUB_GE. apply VAL.ge_bot. easy.
    eapply VAL.ge_trans. apply VAL.ge_bot. apply VAL.ge_refl. apply VAL.eq_sym.
    apply LUB_BOT. apply VAL.eq_refl. apply VAL.eq_sym; now apply GE_BOT_EQ.
    now apply LUB_INC_L.
    apply GE_BOT_EQ. apply VAL.eq_sym. apply LUB_BOT; apply VAL.eq_sym; now apply GE_BOT_EQ.
    apply GE_BOT_EQ. apply VAL.eq_sym. apply LUB_BOT. apply VAL.eq_sym; now apply GE_BOT_EQ. apply VAL.eq_refl.
    apply GE_BOT_EQ. apply VAL.eq_sym. apply LUB_BOT. apply VAL.eq_refl. apply VAL.eq_sym; now apply GE_BOT_EQ.
  Qed.

  Theorem not_in_lub: forall m n x,
    ~ M.In x (lub m n) ->
    ~ M.In x m /\ ~ M.In x n.
  Proof.
    intros. unfold lub in H. pose proof M.map2i_1 as M2I.
    specialize (M2I _ _ _ merge merge_compat m n x). split; intro IN; apply H.
    apply M.FMF.in_find_iff. rewrite M2I; [|now left]. apply M.FMF.in_find_iff in IN.
    destruct (M.find x m), (M.find x n); simpl; congruence.
    apply M.FMF.in_find_iff. rewrite M2I; [|now right]. apply M.FMF.in_find_iff in IN.
    destruct (M.find x m), (M.find x n); simpl; congruence.
  Qed.

End MapSemiLattice.