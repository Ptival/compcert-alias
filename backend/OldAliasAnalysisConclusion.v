Require Import Relations.

Require Import AST.
Require Import Coqlib.
Require Import Integers.
Require Import Memory.
Require Import Registers.
Require Import RTL.
Require Import Values.

Require Import AliasAnalysis.
Require Import AliasHierarchy.
Require Import AliasLib.

Definition disjoint (x y: PTSet.t) :=
  forall a b, PTSet.In a x -> PTSet.In b y -> ~ AbsPO.overlap a b.

Theorem disjoint_implies: forall
  ge cs f sp pc rs m
  (AI: alias_interprets ge (State cs f sp pc rs m))
  rmap mmap (RES: (safe_funanalysis f)#pc = (rmap, mmap))
  r1 r2 (DISJ: disjoint (RegMap.get r1 rmap) (RegMap.get r2 rmap))
  b1 o1 (R1: rs # r1 = Vptr b1 o1)
  b2 o2 (R2: rs # r2 = Vptr b2 o2)
  ,
  Vptr b1 o1 <> Vptr b2 o2.
Proof.
  repeat intro. inv H. destruct AI as [abs SAT]. inv SAT. inv RES0. rewrite RPC in RES. inv RES.
  pose proof (RSAT r1) as Sr1. pose proof (RSAT r2) as Sr2.
  unfold regsat, valsat in Sr1, Sr2.
  rewrite R1 in Sr1. rewrite R2 in Sr2.
  destruct (abs b2).
  elim (DISJ (Loc a o2) (Loc a o2)); auto. apply reflexivity.
  elim (DISJ AbsPH.top AbsPH.top); auto using PTSet.In_top. apply reflexivity.
Qed.

Definition disjoint_dec_bool (a b: PTSet.t): bool :=
  PTSet.AbsPSet.for_all
  (fun x =>
    PTSet.AbsPSet.for_all
    (fun y =>
      negb (AbsPO.overlap_dec x y)
    )
    b
  )
  a.

Module Facts := OverlapFacts(AbsPO).

Theorem disjoint_dec_bool_spec: forall a b,
  disjoint_dec_bool a b = true -> disjoint a b.
Proof.
  intros a b DISJ x y INx INy OVER.
  apply PTSet.F.for_all_iff in DISJ.
  apply PTSet.In_spec in INx; destruct INx as [INx | [ax [Ax INax]]].
  Case "x is really in a".
  specialize (DISJ x INx). simpl in DISJ.
  apply PTSet.In_spec in INy; destruct INy as [INy | [ay [Ay INay]]].
  SCase "y is really in b".
  apply PTSet.F.for_all_iff in DISJ; auto.
  specialize (DISJ y INy). simpl in DISJ.
  destruct (AbsPO.overlap_dec x y). inv DISJ. contradiction.
  repeat intro. subst. reflexivity.
  SCase "y has an ancestor in b".
  apply PTSet.F.for_all_iff in DISJ; auto.
  specialize (DISJ ay INay). simpl in DISJ.
  destruct (AbsPO.overlap_dec x ay). inv DISJ. elim n.
  symmetry. eapply Facts.above_overlaps_too; eauto. now symmetry.
  repeat intro. subst. reflexivity.
  Case "x has an ancestor in a".
  specialize (DISJ ax INax). simpl in DISJ.
  apply PTSet.In_spec in INy; destruct INy as [INy | [ay [Ay INay]]].
  SCase "y is really in b".
  apply PTSet.F.for_all_iff in DISJ; auto.
  specialize (DISJ y INy). simpl in DISJ.
  destruct (AbsPO.overlap_dec ax y). inv DISJ.
  elim n. eapply Facts.above_overlaps_too; eauto.
  repeat intro. subst. reflexivity.
  SCase "y has an ancestor in b".
  apply PTSet.F.for_all_iff in DISJ; auto.
  specialize (DISJ ay INay). simpl in DISJ.
  destruct (AbsPO.overlap_dec ax ay). inv DISJ. elim n.
  eapply Facts.above_overlaps_too; eauto. symmetry.
  eapply Facts.above_overlaps_too; eauto. now symmetry.
  repeat intro. subst. reflexivity.
  repeat intro. subst. reflexivity.
Qed.

Definition disjoint_chunks (chunk1 chunk2: memory_chunk) (s1 s2: PTSet.t) :=
  forall (p1 p2: AbsPO.t),
    PTSet.In p1 s1 -> PTSet.In p2 s2 ->
    match p1, p2 with
    | Loc b1 o1, Loc b2 o2 =>
      (b1 <> b2 /\ ~ AbsPO.AbsBO.overlap b1 b2)
      \/ (Int.unsigned o1 + size_chunk chunk1 <= Int.unsigned o2)
      \/ (Int.unsigned o2 + size_chunk chunk2 <= Int.unsigned o1)
    | Loc b1 _, Blk b2 | Blk b1, Loc b2 _ | Blk b1, Blk b2 =>
      b1 <> b2
      \/ ~ AbsPO.AbsBO.overlap b1 b2
    end.

Theorem disjoint_chunks_implies: forall
  ge cs f sp pc rs m
  (AI: alias_interprets ge (State cs f sp pc rs m))
  rmap mmap (RES: (safe_funanalysis f)#pc = (rmap, mmap))
  chunk1 chunk2 r1 r2 (DISJ: disjoint_chunks chunk1 chunk2 (RegMap.get r1 rmap) (RegMap.get r2 rmap))
  b1 o1 (R1: rs # r1 = Vptr b1 o1)
  b2 o2 (R2: rs # r2 = Vptr b2 o2)
  ,
  b1 <> b2
  \/ (Int.unsigned o1 + size_chunk chunk1 <= Int.unsigned o2)
  \/ (Int.unsigned o2 + size_chunk chunk2 <= Int.unsigned o1).
Proof.
  intros. destruct AI as [abs SAT]. inv SAT. inv RES0. rewrite RPC in RES. inv RES.
  pose proof (RSAT r1) as Sr1. pose proof (RSAT r2) as Sr2.
  unfold regsat, valsat in Sr1, Sr2.
  rewrite R1 in Sr1. rewrite R2 in Sr2.
  destruct (abs b2) as [ab2|]_eqn, (abs b1) as [ab1|]_eqn.
  specialize (DISJ _ _ Sr1 Sr2). simpl in DISJ. intuition.
  left. intro. subst. rewrite Heqo in Heqo0. inv Heqo0. now apply H0.
  simpl in DISJ. left. intro. subst. rewrite Heqo in Heqo0. congruence.
  simpl in DISJ. left. intro. subst. rewrite Heqo in Heqo0. congruence.
  unfold disjoint_chunks in DISJ.
  specialize (DISJ (Loc AbsPO.AbsBO.top o1) (Loc AbsPO.AbsBO.top o2)). simpl in DISJ.
  feed_all DISJ.
  apply Sr1. apply PTSet.In_top.
  apply Sr2. apply PTSet.In_top.
  intuition.
Qed.

Theorem disjoint_chunks_implies2: forall
  ge cs f sp pc rs m
  abs (SAT: satisfy ge abs (State cs f sp pc rs m))
  rmap mmap (RES: (safe_funanalysis f)#pc = (rmap, mmap))
  chunk1 chunk2 set1 set2 (DISJ: disjoint_chunks chunk1 chunk2 set1 set2)
  b1 o1 b2 o2
  (In1:
    match abs b1 with
    | Some ab1 => PTSet.In (Loc ab1 o1) set1
    | None     => PTSet.ge set1 PTSet.top
    end
  )
  (In2:
    match abs b2 with
    | Some ab2 => PTSet.In (Loc ab2 o2) set2
    | None     => PTSet.ge set2 PTSet.top
    end
  )
  ,
  b1 <> b2
  \/ (Int.unsigned o2 + size_chunk chunk2 <= Int.unsigned o1)
  \/ (Int.unsigned o1 + size_chunk chunk1 <= Int.unsigned o2).
Proof.
  intros. inv SAT. inv RES0. rewrite RPC in RES. inv RES.
  (*
  pose proof (RSAT r1) as Sr1. pose proof (RSAT r2) as Sr2.
  unfold regsat, valsat in Sr1, Sr2.
  rewrite R1 in Sr1. rewrite R2 in Sr2.
  *)
  destruct (abs b2) as [ab2|]_eqn, (abs b1) as [ab1|]_eqn.
  specialize (DISJ _ _ In1 In2). simpl in DISJ. intuition.
  left. intro. subst. rewrite Heqo in Heqo0. inv Heqo0. now apply H0.
  simpl in DISJ. left. intro. subst. rewrite Heqo in Heqo0. congruence.
  simpl in DISJ. left. intro. subst. rewrite Heqo in Heqo0. congruence.
  unfold disjoint_chunks in DISJ.
  specialize (DISJ (Loc AbsPO.AbsBO.top o1) (Loc AbsPO.AbsBO.top o2)). simpl in DISJ.
  feed_all DISJ.
  apply In1. apply PTSet.In_top.
  apply In2. apply PTSet.In_top.
  intuition.
Qed.

Theorem disjoint_chunks_implies3: forall
  ge cs f sp pc rs m
  abs (SAT: satisfy ge abs (State cs f sp pc rs m))
  rmap mmap (RES: (safe_funanalysis f)#pc = (rmap, mmap))
  chunk1 chunk2 set1 set2 (DISJ: disjoint_chunks chunk1 chunk2 set1 set2)
  b o1 o2
  (In1:
    match abs b with
    | Some ab => PTSet.In (Loc ab o1) set1 /\ PTSet.In (Loc ab o2) set2
    | None    => PTSet.ge set1 PTSet.top /\ PTSet.ge set2 PTSet.top
    end
  )
  ,
  (Int.unsigned o2 + size_chunk chunk2 <= Int.unsigned o1)
  \/ (Int.unsigned o1 + size_chunk chunk1 <= Int.unsigned o2).
Proof.
  intros.
  pose proof (disjoint_chunks_implies2 _ _ _ _ _ _ _ _ SAT _ _ RES _ _ _ _ DISJ b o1 b o2).
  feed_all H; destruct (abs b); intuition.
Qed.

(* Should be moved in Integers.v *)
Theorem int_add_sub: forall a b,
  Int.add (Int.sub a b) b = a.
Proof.
  intros. rewrite Int.sub_add_opp. rewrite Int.add_assoc.
  setoid_rewrite Int.add_commut at 2. rewrite Int.add_neg_zero. now rewrite Int.add_zero.
Qed.

Theorem disjoint_chunks_shift_implies: forall
  ge cs f sp pc rs m
  (AI: alias_interprets ge (State cs f sp pc rs m))
  rmap mmap (RES: (safe_funanalysis f)#pc = (rmap, mmap))
  chunk1 chunk2 r1 r2 s1 s2
  (DISJ: disjoint_chunks chunk1 chunk2
    (shift_offset (RegMap.get r1 rmap) s1)
    (shift_offset (RegMap.get r2 rmap) s2)
  )
  b1 o1 (R1: rs # r1 = Vptr b1 o1)
  b2 o2 (R2: rs # r2 = Vptr b2 o2)
  ,
  (
    b1 <> b2
    \/ (Int.unsigned (Int.add o1 s1) + size_chunk chunk1 <= Int.unsigned (Int.add o2 s2))
    \/ (Int.unsigned (Int.add o2 s2) + size_chunk chunk2 <= Int.unsigned (Int.add o1 s1))
  )
  \/
  (
    b1 <> b2
    \/ (Int.unsigned o1 + size_chunk chunk1 <= Int.unsigned o2)
    \/ (Int.unsigned o2 + size_chunk chunk2 <= Int.unsigned o1)
  ).

Proof.
  intros. destruct AI as [abs SAT]. inv SAT. inv RES0. rewrite RPC in RES. inv RES.
  pose proof (RSAT r1) as Sr1. pose proof (RSAT r2) as Sr2.
  unfold regsat, valsat in Sr1, Sr2.
  rewrite R1 in Sr1. rewrite R2 in Sr2.
  destruct (abs b2) as [ab2|]_eqn, (abs b1) as [ab1|]_eqn.
  eapply In_shift_offset with (o' := Int.add o1 s1) in Sr1; [|reflexivity].
  eapply In_shift_offset with (o' := Int.add o2 s2) in Sr2; [|reflexivity].
  specialize (DISJ _ _ Sr1 Sr2). simpl in DISJ. intuition.
  left. left. intro. subst. rewrite Heqo in Heqo0. inv Heqo0. now apply H0.
  left. simpl in DISJ. left. intro. subst. rewrite Heqo in Heqo0. congruence.
  left. simpl in DISJ. left. intro. subst. rewrite Heqo in Heqo0. congruence.
  right. unfold disjoint_chunks in DISJ.
  specialize (DISJ (Loc AbsPO.AbsBO.top o1) (Loc AbsPO.AbsBO.top o2)). simpl in DISJ.
  feed_all DISJ.
  apply In_shift_offset with (o := Int.sub o1 s1). apply Sr1. apply PTSet.In_top.
  auto using int_add_sub.
  apply In_shift_offset with (o := Int.sub o2 s2). apply Sr2. apply PTSet.In_top.
  auto using int_add_sub.
  intuition.
Qed.

Definition disjoint_chunks_dec_bool chunk1 chunk2 (s1 s2: PTSet.t): bool :=
  PTSet.AbsPSet.for_all
  (fun p1 =>
    PTSet.AbsPSet.for_all
    (fun p2 =>
      match p1, p2 with
      | Loc b1 o1, Loc b2 o2 =>
        ((negb (AbsPO.AbsBO.eq_dec b1 b2)) && (negb (AbsPO.AbsBO.overlap_dec b1 b2)))
        || Int.no_overlap o1 (size_chunk chunk1) o2 (size_chunk chunk2)
      | Loc b1 _, Blk b2 | Blk b1, Loc b2 _ | Blk b1, Blk b2 =>
        ((negb (AbsPO.AbsBO.eq_dec b1 b2)) && (negb (AbsPO.AbsBO.overlap_dec b1 b2)))
      end
    )
    s2
  )
  s1.

Module AbsPHFacts := HierarchyFacts(AbsPH).

Lemma above_blk: forall x z,
  AbsPH.above (Blk x) (Blk z) ->
  AbsPO.AbsBO.above x z.
Proof.
  unfold AbsPH.above, AbsPO.AbsBO.above. intros x.
  setoid_rewrite clos_trans_tn1_iff.
  refine (AbsPO.AbsBO.above_ind _ _); intros z IND H.
  inv H.
  left.
  destruct x, z; try destruct a0; try destruct o; compute in *; congruence.
  destruct y.
  right with (y := t).
  destruct t, z; try destruct a0; try destruct o; compute in *; try congruence.
  apply IND; auto. apply AbsPO.AbsBO.parent_is_above.
  destruct t, z; try destruct a0; try destruct o; compute in *; try congruence.
  destruct t, z; try destruct a0; try destruct o; compute in *; try congruence.
Qed.

Lemma above_blk_loc: forall x z o,
  AbsPH.above (Blk x) (Loc z o) ->
  x = z \/ AbsPO.AbsBO.above x z.
Proof.
  unfold AbsPH.above, AbsPO.AbsBO.above. intros x.
  setoid_rewrite clos_trans_tn1_iff.
  refine (AbsPO.AbsBO.above_ind _ _); intros z o IND H.
  inv H.
  left.
  destruct x, z; try destruct a0; try destruct o; compute in *; congruence.
  destruct y.
  assert (t = z).
  destruct t, z; try destruct a0; try destruct o; compute in *; congruence.
  subst.
  assert (AbsPH.above (Blk x) (Blk z)).
  unfold AbsPH.above. now setoid_rewrite clos_trans_tn1_iff.
  apply above_blk in H. right.
  unfold AbsPO.AbsBO.above in H. now setoid_rewrite clos_trans_tn1_iff in H.
  exfalso.
  destruct t, z; try destruct a0; try destruct o; compute in *; try congruence.
Qed.

Module AbsBOFacts := OverlapFacts(AbsPO.AbsBO).

Ltac solver :=
  repeat (intuition (idtac;
    match goal with
    | |- _ \/ _ => left
    | |- _ \/ _ => right
    | |- _ <> _ => intro

    | H: AbsPH.above (Loc _ _) _ |- _ => apply not_loc_above in H
    | H: AbsPH.above (Blk ?b) (Blk ?c) |- _ => apply above_blk in H
    | H: AbsPH.above (Blk ?b) (Loc ?c ?o) |- _ => apply above_blk_loc in H

    | _: _ = _ |- _ => progress subst
    | _: _ = _ |- _ => discriminate
    | H: ?x = ?x |- _ => clear H
    | |- _ => AbsBOFacts.solver
    | |- _ => fail
    end
  )).

Theorem disjoint_chunks_dec_bool_spec: forall chunk1 chunk2 s1 s2,
  disjoint_chunks_dec_bool chunk1 chunk2 s1 s2 = true -> disjoint_chunks chunk1 chunk2 s1 s2.
Proof.
  intros ???? DISJ x y INx INy.
  apply PTSet.F.for_all_iff in DISJ; [|repeat intro; now subst].
  apply PTSet.In_spec in INx; destruct INx as [INx | [ax [Ax INax]]].
  Case "x is really in a".
  specialize (DISJ x INx). simpl in DISJ.
  apply PTSet.In_spec in INy; destruct INy as [INy | [ay [Ay INay]]].
  SCase "y is really in b".
  apply PTSet.F.for_all_iff in DISJ; [|repeat intro; now subst].
  specialize (DISJ y INy). simpl in DISJ.
  destruct x, y;
  destruct (AbsPO.AbsBO.eq_dec t t0), (AbsPO.AbsBO.overlap_dec t t0);
  simpl in DISJ; try solve [solver];
  right;
  apply Int.no_overlap_sound with (base := Int.zero) in DISJ; auto using size_chunk_pos;
  simpl in DISJ;
  setoid_rewrite Zmod_small in DISJ; auto using Int.unsigned_range.
  SCase "y has an ancestor in b".
  apply PTSet.F.for_all_iff in DISJ; [|repeat intro; now subst].
  specialize (DISJ ay INay). simpl in DISJ.
  destruct ay as [bay|? ?]; [|elim (not_loc_above _ _ _ Ay)].
  destruct x as [bx|bx ox], y as [byy|byy oy];
  destruct (AbsPO.AbsBO.eq_dec bx bay), (AbsPO.AbsBO.overlap_dec bx bay);
  simpl in DISJ; solve [solver].
  Case "x has an ancestor in a".
  specialize (DISJ ax INax). simpl in DISJ.
  apply PTSet.In_spec in INy; destruct INy as [INy | [ay [Ay INay]]].
  SCase "y is really in b".
  apply PTSet.F.for_all_iff in DISJ; [|repeat intro; now subst].
  specialize (DISJ y INy). simpl in DISJ.
  destruct ax as [bax|? ?]; [|elim (not_loc_above _ _ _ Ax)].
  destruct x as [bx|bx ox], y as [byy|byy oy];
  destruct (AbsPO.AbsBO.eq_dec bax byy), (AbsPO.AbsBO.overlap_dec bax byy);
  simpl in DISJ; solve [solver].
  SCase "y has an ancestor in b".
  apply PTSet.F.for_all_iff in DISJ; [|repeat intro; now subst].
  specialize (DISJ ay INay). simpl in DISJ.
  destruct ax as [bax|? ?]; [|elim (not_loc_above _ _ _ Ax)].
  destruct ay as [bay|bay oay];
  destruct (AbsPO.AbsBO.eq_dec bax bay), (AbsPO.AbsBO.overlap_dec bax bay);
  simpl in DISJ; try solve [solver];
  destruct x as [bx|bx ox], y as [byy|byy oy];
  solve [solver].
Qed.