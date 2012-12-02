Require Import AST.
Require Import Coqlib.
Require Import Integers.
Require Import Memory.
Require Import Registers.
Require Import RTL.
Require Import Values.

Require Import AliasAbstract.
Require Import AliasPTSet.
Require Import AliasRegMap.
Require Import AliasSolver.
Require Import AliasSoundness.
Require Import AliasTransfer.

Definition ablock_overlap x y :=
  x = y \/ ablock_lt x y \/ ablock_lt y x.

Definition ablock_overlap_dec :
  forall x y, { ablock_overlap x y } + { ~ ablock_overlap x y }.
Proof.
  intros. unfold ablock_overlap. destruct (ablock_eq_dec x y).
  tauto.
  destruct x, y; simpl; tauto.
Defined.

Definition aloc_overlap x y :=
  x = y \/ aloc_lt x y \/ aloc_lt y x.

Definition overlap_dec :
  forall x y, { aloc_overlap x y } + { ~ aloc_overlap x y }.
Proof.
  intros. unfold aloc_overlap. destruct (aloc_eq_dec x y).
  tauto.
  destruct x as [b|b o], y as [b'|b' o']; simpl.
  destruct b, b'; simpl; try tauto; solve [right; intuition congruence].
  destruct b, b'; simpl; try tauto; try solve [right; intuition congruence].
  destruct (positive_eq_dec i i0); first [ subst; tauto | right; intuition congruence ].
  destruct (positive_eq_dec n0 n1); first [ subst; tauto | right; intuition congruence ].
  destruct b, b'; simpl; try tauto; try solve [right; intuition congruence].
  destruct (positive_eq_dec i i0); first [ subst; tauto | right; intuition congruence ].
  destruct (positive_eq_dec n0 n1); first [ subst; tauto | right; intuition congruence ].
  right. intuition congruence.
Defined.

Definition disjoint (x y: PTSet.t) :=
  forall a b, PTSet.In a x -> PTSet.In b y -> ~ aloc_overlap a b.

Theorem disjoint_implies: forall
  ge cs f sp pc rs m
  (AI: alias_interprets ge (State cs f sp pc rs m))
  rmap mmap (RES: (analysis f)#pc = (rmap, mmap))
  r1 r2 (DISJ: disjoint (RegMap.get r1 rmap) (RegMap.get r2 rmap))
  b1 o1 (R1: rs # r1 = Vptr b1 o1)
  b2 o2 (R2: rs # r2 = Vptr b2 o2)
  ,
  Vptr b1 o1 <> Vptr b2 o2.
Proof.
  repeat intro. inv H. destruct AI as [abs SAT]. inv SAT. inv RES0.
  rewrite RPC in RES. inv RES.
  pose proof (RSAT r1) as Sr1. pose proof (RSAT r2) as Sr2.
  unfold regsat, valsat in Sr1, Sr2.
  rewrite R1 in Sr1. rewrite R2 in Sr2.
  destruct (abs b2).
  elim (DISJ (Loc a o2) (Loc a o2)); auto. now left.
  elim (DISJ (Blk All) (Blk All)); auto using PTSet.In_top. now left.
Qed.

Definition disjoint_dec_bool (a b: PTSet.t): bool :=
  PTSet.for_all (fun x =>
  PTSet.for_all (fun y =>
    negb (overlap_dec x y)
  ) b) a.

Theorem disjoint_dec_bool_spec: forall a b,
  disjoint_dec_bool a b = true -> disjoint a b.
Proof.
  intros a b DISJ x y INx INy OVER.
  apply PTSet.for_all_iff in DISJ. specialize (DISJ _ INx). simpl in DISJ.
  apply PTSet.for_all_iff in DISJ. specialize (DISJ _ INy). simpl in DISJ.
  destruct (overlap_dec x y); now simpl in DISJ.
Qed.

Definition disjoint_chunks (chunk1 chunk2: memory_chunk) (s1 s2: PTSet.t) :=
  forall p1 p2,
    PTSet.In p1 s1 -> PTSet.In p2 s2 ->
    match p1, p2 with
    | Loc b1 o1, Loc b2 o2 =>
      (b1 <> b2 /\ ~ ablock_overlap b1 b2)
      \/ (Int.unsigned o1 + size_chunk chunk1 <= Int.unsigned o2)
      \/ (Int.unsigned o2 + size_chunk chunk2 <= Int.unsigned o1)
    | Loc b1 _, Blk b2 | Blk b1, Loc b2 _ | Blk b1, Blk b2 =>
      b1 <> b2
      \/ ~ ablock_overlap b1 b2
    end.

Theorem disjoint_chunks_implies: forall
  ge cs f sp pc rs m
  (AI: alias_interprets ge (State cs f sp pc rs m))
  rmap mmap (RES: (analysis f)#pc = (rmap, mmap))
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
  specialize (DISJ (Loc All o1) (Loc All o2)). simpl in DISJ.
  exploit DISJ.
  apply Sr1. apply PTSet.In_top.
  apply Sr2. apply PTSet.In_top.
  tauto.
Qed.

Theorem disjoint_chunks_implies2: forall
  ge cs f sp pc rs m
  abs (SAT: satisfy ge abs (State cs f sp pc rs m))
  rmap mmap (RES: (analysis f)#pc = (rmap, mmap))
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
  destruct (abs b2) as [ab2|]_eqn, (abs b1) as [ab1|]_eqn.
  specialize (DISJ _ _ In1 In2). simpl in DISJ. intuition.
  left. intro. subst. rewrite Heqo in Heqo0. inv Heqo0. now apply H0.
  simpl in DISJ. left. intro. subst. rewrite Heqo in Heqo0. congruence.
  simpl in DISJ. left. intro. subst. rewrite Heqo in Heqo0. congruence.
  unfold disjoint_chunks in DISJ.
  specialize (DISJ (Loc All o1) (Loc All o2)). simpl in DISJ.
  exploit DISJ.
  apply In1. apply PTSet.In_top.
  apply In2. apply PTSet.In_top.
  tauto.
Qed.

Theorem disjoint_chunks_implies3: forall
  ge cs f sp pc rs m
  abs (SAT: satisfy ge abs (State cs f sp pc rs m))
  rmap mmap (RES: (analysis f)#pc = (rmap, mmap))
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
  exploit H; destruct (abs b); tauto.
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
  rmap mmap (RES: (analysis f)#pc = (rmap, mmap))
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
  specialize (DISJ (Loc All o1) (Loc All o2)). simpl in DISJ.
  exploit DISJ.
  apply In_shift_offset with (o := Int.sub o1 s1). apply Sr1. apply PTSet.In_top.
  auto using int_add_sub.
  apply In_shift_offset with (o := Int.sub o2 s2). apply Sr2. apply PTSet.In_top.
  auto using int_add_sub.
  tauto.
Qed.

Definition disjoint_chunks_dec_bool chunk1 chunk2 (s1 s2: PTSet.t): bool :=
  PTSet.for_all (fun p1 =>
  PTSet.for_all (fun p2 =>
    match p1, p2 with
    | Loc b1 o1, Loc b2 o2 =>
      ((negb (ablock_eq_dec b1 b2)) && (negb (ablock_overlap_dec b1 b2)))
        || Int.no_overlap o1 (size_chunk chunk1) o2 (size_chunk chunk2)
    | Loc b1 _, Blk b2 | Blk b1, Loc b2 _ | Blk b1, Blk b2 =>
      ((negb (ablock_eq_dec b1 b2)) && (negb (ablock_overlap_dec b1 b2)))
    end
  ) s2) s1.

Theorem disjoint_chunks_dec_bool_spec: forall chunk1 chunk2 s1 s2,
  disjoint_chunks_dec_bool chunk1 chunk2 s1 s2 = true ->
  disjoint_chunks chunk1 chunk2 s1 s2.
Proof.
  intros ???? DISJ x y INx INy.
  apply PTSet.for_all_iff in DISJ. specialize (DISJ x INx). simpl in DISJ.
  apply PTSet.for_all_iff in DISJ. specialize (DISJ y INy). simpl in DISJ.
  destruct x as [b|b o], y as [b'|b' o'].
  destruct (ablock_eq_dec b b'), (ablock_overlap_dec b b');
  simpl in DISJ; intuition congruence.
  destruct (ablock_eq_dec b b'), (ablock_overlap_dec b b');
  simpl in DISJ; intuition congruence.
  destruct (ablock_eq_dec b b'), (ablock_overlap_dec b b');
  simpl in DISJ; intuition congruence.
  destruct (ablock_eq_dec b b'), (ablock_overlap_dec b b'); try tauto;
  simpl in DISJ;
  apply Int.no_overlap_sound with (base := Int.zero) in DISJ; auto using size_chunk_pos;
  simpl in DISJ;
  setoid_rewrite Zmod_small in DISJ; auto using Int.unsigned_range.
Qed.
