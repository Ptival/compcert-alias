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
Require Import RTL.
Require Import Values.

(* Library *)

Require String. Open Scope string_scope.
Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.
Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.
Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].
Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.
Tactic Notation "SSSSSSSSCase" constr(name) := Case_aux SSSSSSSSCase name.
Tactic Notation "SSSSSSSSSCase" constr(name) := Case_aux SSSSSSSSSCase name.

Ltac unalias := repeat (autounfold with unalias in *).

Ltac feed H :=
  match type of H with
  | ?foo -> _ =>
    let FOO := fresh in
    assert foo as FOO; [|specialize (H FOO); clear FOO]
  end.

Ltac feed_all H := feed H; [|try feed_all H].

Ltac feed_n n H :=
  match constr:n with
  | O => idtac
  | (S ?m) => feed H ; [| feed_n m H]
  end.

(* Interfaces *)

Module Type Hierarchy.
  Parameter t: Type.
  Parameter top: t.
  Parameter parent: t -> option t.
  Parameter measure: t -> nat.
  Axiom eq_dec: forall (x y: t), {eq x y} + {~eq x y}. (* useful for optint *)
  Axiom hierarchy: t -> t -> Prop.
  Axiom hierarchy_dec: forall x y, {hierarchy x y} + {~ hierarchy x y}.
  Axiom top_spec: forall x, x <> top -> hierarchy top x.
  Axiom parent_measure: forall x px,
    parent x = Some px -> measure x = S (measure px).
End Hierarchy.

Module Type Overlap.
  Include Hierarchy.
  Axiom overlap: t -> t -> Prop.
  Axiom overlap_dec: forall x y, {overlap x y} + {~ overlap x y}.
End Overlap.

(* A hierarchical set is a set over hierarchical elements, such that an element
   up in the hierarchy embodies all of its ancestors. *)

Module Type HSet (H: Hierarchy).
  Parameter t: Type.
  Parameter bot: t.
  Parameter top: t.
  Parameter add: H.t -> t -> t.
  Parameter In: H.t -> t -> Prop.
  Parameter mem: forall x s, {In x s} + {~In x s}.
  Definition eq (s1 s2: t): Prop := forall x, In x s1 <-> In x s2.
  Axiom In_add_same: forall x s, In x (add x s).
  Axiom In_add_hierarchy: forall x y,
    H.hierarchy x y -> (forall s, In y (add x s)).
  Axiom In_add_already: forall x y s, In x s -> In x (add y s).
  Definition singleton x := add x bot.
  Axiom In_singleton: forall x, In x (singleton x).
  Axiom In_singleton_hierarchy: forall x y,
    H.hierarchy x y -> In y (singleton x).
End HSet.

Module Type OMap (O: Overlap) (L: SEMILATTICE).
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
End OMap.

(* Useful functors *)

Module HtoO (H: Hierarchy) <: Overlap.
  Include H.
  Definition overlap x y := hierarchy x y \/ hierarchy y x.
  Definition overlap_dec: forall x y, {overlap x y} + {~ overlap x y}.
  Proof.
    intros. destruct (hierarchy_dec x y).
    left. left. auto. destruct (hierarchy_dec y x).
    left. right. auto.
    right. intro. inv H; contradiction.
  Defined.
End HtoO.

Module ProductSemiLattice (A: SEMILATTICE) (B: SEMILATTICE) <: SEMILATTICE.
  Definition t := (A.t * B.t)%type.
  Definition eq (x y: t) :=
    let (a, b) := x in let (c, d) := y in
    A.eq a c /\ B.eq b d.
  Theorem eq_refl: forall x, eq x x.
  Proof.
    destruct x. split. apply A.eq_refl. apply B.eq_refl.
  Qed.
  Theorem eq_sym: forall x y, eq x y -> eq y x.
  Proof.
    intros. destruct x, y. inv H. constructor.
    apply A.eq_sym. auto.
    apply B.eq_sym. auto.
  Qed.
  Theorem eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    intros. destruct x, y, z. inv H. inv H0. constructor.
    eapply A.eq_trans; eauto.
    eapply B.eq_trans; eauto.
  Qed.
  Definition beq (x y: t) :=
    let (a, b) := x in let (c, d) := y in
    (A.beq a c) && (B.beq b d).
  Theorem beq_correct: forall x y, beq x y = true -> eq x y.
  Proof.
    intros. destruct x, y. apply andb_prop in H. destruct H as [? ?]. constructor.
    apply A.beq_correct. auto.
    apply B.beq_correct. auto.
  Qed.
  Definition ge (x y: t) :=
    let (a, b) := x in let (c, d) := y in
    A.ge a c /\ B.ge b d.
  Theorem ge_refl: forall x y, eq x y -> ge x y.
  Proof.
    intros. destruct x, y. inv H. constructor.
    apply A.ge_refl. auto.
    apply B.ge_refl. auto.
  Qed.
  Theorem ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof.
    intros. destruct x, y, z. inv H. inv H0. constructor.
    eapply A.ge_trans; eauto.
    eapply B.ge_trans; eauto.
  Qed.
  Definition bot := (A.bot, B.bot).
  Theorem ge_bot: forall x, ge x bot.
  Proof.
    destruct x. constructor. apply A.ge_bot. apply B.ge_bot.
  Qed.
  Definition lub (x y: t) :=
    let (a, b) := x in let (c, d) := y in
    (A.lub a c, B.lub b d).
  Theorem ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    destruct x, y. constructor. apply A.ge_lub_left. apply B.ge_lub_left.
  Qed.
  Theorem ge_lub_right: forall x y, ge (lub x y) y.
  Proof.
    destruct x, y. constructor. apply A.ge_lub_right. apply B.ge_lub_right.
  Qed.
End ProductSemiLattice.

Module FMapAVLPlus(X: OrderedType).

Module M := FMapAVL.Make(X).

Include M.

Module FMF := FMapFacts.WFacts_fun X M.

Section MAP2.

Variable elt elt' elt'' : Type.
Variable f : key -> option elt -> option elt' -> option elt''.
Hypothesis f_compat: forall x x' o1 o2, X.eq x x' -> f x o1 o2 = f x' o1 o2.

Definition raw_map2i : Raw.t elt -> Raw.t elt' -> Raw.t elt'' :=
  Raw.map2_opt
    (fun k d o => f k (Some d) o)
    (Raw.map_option (fun k d => f k (Some d) None))
    (Raw.map_option (fun k d' => f k None (Some d'))).

Lemma map2i_bst:
  forall m1 m2, Raw.bst m1 -> Raw.bst m2 -> Raw.bst (raw_map2i m1 m2).
Proof.
  intros. unfold raw_map2i.
  apply Raw.Proofs.map2_opt_bst with (f0 := f); auto; intros.
  apply Raw.Proofs.map_option_bst; auto.
  apply Raw.Proofs.map_option_bst; auto.
  apply Raw.Proofs.map_option_find; auto.
  apply Raw.Proofs.map_option_find; auto.
Qed.

Definition map2i (m1: t elt) (m2: t elt') : t elt'' :=
  Bst (map2i_bst m1 m2 m1.(is_bst) m2.(is_bst)).

Lemma map2i_1: forall (m: t elt)(m': t elt') (x:key),
  In x m \/ In x m' ->
  find x (map2i m m') = f x (find x m) (find x m').
Proof.
  unfold find, map2i, In; intros until x. simpl.
  do 2 rewrite Raw.Proofs.In_alt. unfold raw_map2i. intros.
  rewrite Raw.Proofs.map2_opt_1 with (f0 := f); auto; intros.
  apply Raw.Proofs.map_option_bst; auto.
  apply Raw.Proofs.map_option_bst; auto.
  apply Raw.Proofs.map_option_find; auto.
  apply Raw.Proofs.map_option_find; auto.
  apply is_bst. apply is_bst.
Qed.

Lemma map2i_2: forall (m: t elt)(m': t elt') (x:key),
  In x (map2i m m') -> In x m \/ In x m'.
Proof.
  unfold In, map2i; intros until x.
  do 3 rewrite Raw.Proofs.In_alt. simpl. unfold raw_map2i; intros.
  eapply Raw.Proofs.map2_opt_2 with (f0 := f); eauto; intros.
  apply Raw.Proofs.map_option_bst; auto.
  apply Raw.Proofs.map_option_bst; auto.
  apply Raw.Proofs.map_option_find; auto.
  apply Raw.Proofs.map_option_find; auto.
  apply is_bst. apply is_bst.
Qed.

Lemma map2i_3: forall x m1 m2,
  (forall k, f k None None = None) ->
  find x m1 = None ->
  find x m2 = None ->
  find x (map2i m1 m2) = None.
Proof.
  intros. destruct (find x (map2i m1 m2)) as []_eqn; [|auto].
  assert (find x (map2i m1 m2) <> None). congruence.
  apply FMF.in_find_iff in H2. apply map2i_2 in H2. inv H2.
  apply FMF.in_find_iff in H3. congruence.
  apply FMF.in_find_iff in H3. congruence.
Qed.

Lemma map2i_4: forall m m' (H: forall k, f k None None = None) x,
  find x (map2i m m') = f x (find x m) (find x m').
Proof.
  intros. destruct (find x m) as []_eqn.
  rewrite <- Heqo. apply map2i_1. left. apply FMF.in_find_iff. congruence.
  destruct (find x m') as []_eqn.
  rewrite <- Heqo. rewrite <- Heqo0. apply map2i_1.
  right. apply FMF.in_find_iff. congruence.
  rewrite H. apply map2i_3; auto.
Qed.

End MAP2.

End FMapAVLPlus.

Module Type MergeStrategy (KEY: OrderedType) (VAL: SEMILATTICE).
  Variable f: KEY.t -> option VAL.t -> option VAL.t -> option VAL.t.
  Axiom f_compat:
    forall (x x': KEY.t) (o1: option VAL.t) (o2: option VAL.t),
      KEY.eq x x' -> f x o1 o2 = f x' o1 o2.
End MergeStrategy.

Module MapSemiLattice
  (KEY: OrderedType)
  (VAL: SEMILATTICE)
  (MGS: MergeStrategy(KEY)(VAL))
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
  (* Assuming None is the same as B.bot *)
  Definition ge x y :=
    forall k,
      match M.find k x, M.find k y with
      | None,   None   => True
      | Some a, Some b => VAL.ge a b
      | Some _, None   => True
      | None,   Some b => VAL.ge VAL.bot b
      end.
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
    repeat intro.
    destruct (M.find k x) as []_eqn; rewrite FMF.empty_o; auto.
  Qed.
  Definition lub (m: t) (n: t): t :=
    M.map2i VAL.t VAL.t VAL.t MGS.f MGS.f_compat m n.
  Axiom ge_lub_left: forall x y, ge (lub x y) x.
  Axiom ge_lub_right: forall x y, ge (lub x y) y.
End MapSemiLattice.

Module SemiLatticeToLattice (S: SEMILATTICE) <: SEMILATTICE_WITH_TOP.
  Definition t := option S.t.
  Notation Top := None (only parsing).
  Definition eq (x y: t) :=
    match x, y with
    | Top,    Top    => True
    | Some a, Some b => S.eq a b
    | _,      _      => False
    end.
  Theorem eq_refl: forall x, eq x x.
  Proof.
    destruct x; intuition. apply S.eq_refl.
  Qed.
  Theorem eq_sym: forall x y, eq x y -> eq y x.
  Proof.
    intros. destruct x, y; simpl in *; intuition. apply S.eq_sym. auto.
  Qed.
  Theorem eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    intros. destruct x, y, z; simpl in *; intuition. eapply S.eq_trans; eauto.
  Qed.
  Definition beq (x y: t) :=
    match x, y with
    | Top,    Top => true
    | Some a, Some b => S.beq a b
    | _,      _ => false
    end.
  Theorem beq_correct: forall x y, beq x y = true -> eq x y.
  Proof.
    intros. destruct x, y; simpl in *; intuition. apply S.beq_correct. auto.
  Qed.
  Definition ge (x y: t) :=
    match x, y with
    | Top,    _      => True
    | _,      Top    => False
    | Some a, Some b => S.ge a b
    end.
  Theorem ge_refl: forall x y, eq x y -> ge x y.
  Proof.
    intros. destruct x, y; simpl in *; intuition. apply S.ge_refl. auto.
  Qed.
  Theorem ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof.
    intros. destruct x, y, z; simpl in *; intuition. eapply S.ge_trans; eauto.
  Qed.
  Definition bot := Some S.bot.
  Theorem ge_bot: forall x, ge x bot.
  Proof.
    destruct x; simpl in *; intuition. apply S.ge_bot.
  Qed.
  Definition lub (x y: t) :=
    match x, y with
    | Top,    _      => Top
    | _,      Top    => Top
    | Some a, Some b => Some (S.lub a b)
    end.
  Theorem ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    destruct x, y; simpl in *; intuition. apply S.ge_lub_left.
  Qed.
  Theorem ge_lub_right: forall x y, ge (lub x y) y.
  Proof.
    destruct x, y; simpl in *; intuition. apply S.ge_lub_right.
  Qed.
  (* New: *)
  Definition top := @Top S.t.
  Theorem ge_top: forall x, ge top x.
  Proof.
    destruct x; simpl in *; intuition.
  Qed.
End SemiLatticeToLattice.

(* Abstract blocks *)

Inductive absb' :=
| Allocs:  option node  -> absb'
| Globals: option ident -> absb'
| Other
| Stack
.
Definition absb := option absb'. (* None := All *)
Hint Unfold absb: unalias.
(* Better use this *)
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
  Defined.
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
  Defined.
End AbsBOT.

Module AbsBH <: Hierarchy.
  Definition t := absb.
  Definition top: t := None.
  Definition hierarchy x y :=
    match x, y with
    | _,      All    => False
    | All,    _      => True
    | Just a, Just b =>
      match a, b with
      | Allocs All,  Allocs (Just _)  => True
      | Globals All, Globals (Just _) => True
      | _,           _                => False
      end
    end.
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
  Definition eq_dec: forall (x y: t), {eq x y} + {~ eq x y}.
  Proof.
    repeat decide equality.
  Defined.
  Definition hierarchy_dec: forall x y, {hierarchy x y} + {~ hierarchy x y}.
  Proof.
    intros.
    destruct x, y; try destruct a, a0; try destruct o; try destruct o0;
      simpl; auto.
  Defined.
  Theorem top_spec: forall x, x <> top -> hierarchy top x.
  Proof.
    destruct x; simpl; intuition.
  Qed.
  Theorem parent_measure: forall x px,
    parent x = Some px -> measure x = S (measure px).
  Proof.
    intros. destruct x; try destruct a; try destruct o; inv H; auto.
  Qed.
End AbsBH.

(* With offsets *)

Inductive optint {t: Type}: Type :=
| Blk: t -> optint
| Loc: t -> Int.int -> optint
.
Definition absp := @optint absb.

Module OptIntH (H: Hierarchy) <: Hierarchy.
  Definition t:= @optint H.t.
  Hint Unfold t: unalias.
  Definition top: t := Blk H.top.
  Definition hierarchy x y :=
    match x, y with
    | Blk a, Blk b   => H.hierarchy a b
    | Blk a, Loc b _ => a = b \/ H.hierarchy a b
    | _, _ => False
    end.
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
  Definition eq_dec: forall (x y: t), {eq x y} + {~ eq x y}.
  Proof.
    repeat decide equality; try apply H.eq_dec; apply Int.eq_dec.
  Defined.
  Definition hierarchy_dec: forall x y, {hierarchy x y} + {~ hierarchy x y}.
  Proof.
    intros. destruct x, y; auto. apply H.hierarchy_dec. destruct (H.eq_dec t0 t1).
    subst. left. simpl. auto.
    simpl. destruct (H.hierarchy_dec t0 t1); intuition.
  Defined.
  Theorem top_spec: forall x, x <> top -> hierarchy top x.
  Proof.
    intros. simpl in *. destruct x. unfold top in H.
    apply H.top_spec. congruence.
    destruct (H.eq_dec H.top t0). auto. right. apply H.top_spec. auto.
  Qed.
  Theorem parent_measure: forall x px, parent x = Some px -> measure x = S (measure px).
  Proof.
    intros. destruct x; simpl in *. destruct (H.parent t0) as []_eqn; inv H.
    apply H.parent_measure. auto.
    inv H. auto.
  Qed.
End OptIntH.

Module AbsPH := OptIntH(AbsBH).
Module AbsPO := HtoO(AbsPH).

Module OptIntOT (OT: OrderedType) <: OrderedType.
  Definition t := @optint OT.t.
  Definition eq (x y: t): Prop :=
    match x, y with
    | Blk a,   Blk b   => OT.eq a b
    | Loc a x, Loc b y => OT.eq a b /\ x = y
    | _,       _       => False
    end.
  Definition eq_equiv := @eq_equivalence.
  Definition eq_refl: forall (x: t), eq x x.
  Proof.
    intros. destruct x. apply OT.eq_refl. split; auto.
  Defined.
  Theorem eq_sym: forall x y, eq x y -> eq y x.
  Proof.
    intros. destruct x, y; simpl in *; intuition; auto.
  Qed.
  Theorem eq_trans: forall (x y z: t), eq x y -> eq y z -> eq x z.
  Proof.
    destruct x, y, z; simpl in *; intuition; subst; auto; eapply OT.eq_trans; eauto.
  Qed.
  Definition eq_dec : forall x y, {eq x y}+{~eq x y}.
  Proof.
    unfold eq. destruct x, y; repeat decide equality; auto. apply OT.eq_dec.
    pose proof (OT.eq_dec t0 t1). pose proof (Int.eq_dec i i0). intuition.
  Defined.
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
    destruct x, y; simpl in *; intuition; try solve [eapply OT.lt_not_eq; eauto].
    subst. unfold Int.lt in *. destruct zlt. omega. congruence.
  Qed.
  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros. unfold lt. destruct x, y.
    destruct (OT.compare t0 t1). apply LT. auto. apply EQ. auto. apply GT. auto.
    apply GT. auto.
    apply LT. auto.
    destruct (OT.compare t0 t1). apply LT. auto.
    destruct (Int.lt i i0) as []_eqn.
    apply LT. right. split. apply e. auto.
    destruct (Int.eq_dec i i0).
    subst. apply EQ. simpl. auto.
    apply GT. right. split. auto. unfold Int.lt in *. repeat (destruct zlt); auto.
    assert (SEQ: Int.signed i = Int.signed i0) by omega.
    apply (f_equal Int.repr) in SEQ. setoid_rewrite Int.repr_signed in SEQ. contradiction.
    apply GT. auto.
  Defined.
End OptIntOT.

Module AbsPOT := OptIntOT(AbsBOT).

Ltac crunch_hierarchy :=
  unfold AbsPH.t, AbsBH.t in *;
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

Module PTSet
  <: HSet(AbsPH)
  <: SEMILATTICE_WITH_TOP.
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
    intros. setoid_rewrite AbsPH.parent_measure at 2; eauto.
  Qed.
  Definition mem x s : {In x s} + {~In x s}.
  Proof.
    functional induction (In x s).
    destruct IHP. auto.
    destruct (AbsPSet.mem x s) as []_eqn.
    apply F.mem_iff in Heqb. auto. apply F.not_mem_iff in Heqb. tauto.
    destruct (AbsPSet.mem x s) as []_eqn.
    apply F.mem_iff in Heqb. auto. apply F.not_mem_iff in Heqb. tauto.
  Defined.
  Definition bot := AbsPSet.empty.
  Theorem In_add_same: forall x s, In x (add x s).
  Proof.
    intros. remember (add x s). functional induction (In x t0).
    left. apply F.add_iff. destruct x; auto.
    apply F.add_iff. destruct x; auto.
  Qed.
  Theorem In_add_hierarchy: forall x y,
    AbsPH.hierarchy x y -> forall s, In y (add x s).
  Proof.
    intros. remember (add x s). functional induction (In y t0).
    crunch_hierarchy; right; apply In_add_same.
    crunch_hierarchy.
  Qed.
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
  Lemma In_equiv:
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
  Theorem In_add_already: forall x y s, In x s -> In x (add y s).
  Proof.
    intros.
    apply In_equiv in H. apply In_equiv. intuition.
    left. apply F.add_iff. auto.
    right. destruct H0 as [px]. exists px. intuition.
    apply In_equiv in H1. apply In_equiv. intuition.
    left. apply F.add_iff. auto.
    right. destruct H as [ppx]. exists ppx. intuition.
    apply In_equiv in H2. apply In_equiv. intuition.
    left. apply F.add_iff. auto.
    right. destruct H as [pppx]. exists pppx. intuition.
    apply In_equiv in H3. apply In_equiv. intuition.
    left. apply F.add_iff. auto.
    right. destruct H as [ppppx]. exfalso. intuition. crunch_hierarchy.
  Qed.
  Definition beq_correct: forall x y, beq x y = true -> eq x y.
  Proof.
    split; intros.
    apply F.equal_iff in H. unfold AbsPSet.Equal in H.
    functional induction (In x0 y).
    apply In_equiv in H0.
    destruct H0. left. apply H. apply H0.
    destruct H0 as [px' [A B]]. rewrite A in e; inv e. right. auto.
    apply In_equiv in H0. destruct H0.
    apply H. apply H0.
    destruct H0 as [px' [A B]]. rewrite A in e; inv e.
    apply F.equal_iff in H. unfold AbsPSet.Equal in H.
    functional induction (In x0 x).
    apply In_equiv in H0.
    destruct H0. left. apply H. apply H0.
    destruct H0 as [px' [A B]]. rewrite A in e; inv e. right. auto.
    apply In_equiv in H0. destruct H0.
    apply H. apply H0.
    destruct H0 as [px' [A B]]. rewrite A in e; inv e.
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
    destruct H. inv H. apply In_equiv. right. exists px. auto.
    inv H.
  Qed.
  Definition lub' (old: t) (new: t): t :=
    let out := AbsPSet.union old new in
      AbsPSet.filter
      (fun x =>
        AbsPSet.for_all
        (fun y => negb (AbsPH.hierarchy_dec y x))
        out
      )
      out.
  (* [widen s t] widens s according to t, that is, it returns a set greater
     than s, according to some criterion on [s] and [t]. *)
  Definition widen (widened: t) (widener: t): t :=
    AbsPSet.fold
      (fun x res =>
        AbsPSet.add
        (
          match x with
            | Blk b => Blk b
            | Loc b o =>
              if AbsPSet.exists_
                (fun y =>
                  match y with
                    | Loc b' o' =>
                      andb (AbsBOT.eq_dec b b') (negb (Int.eq o o'))
                    | _ => false
                  end
                )
                widener
                then Blk b (* widening *)
                else Loc b o
          end
        )
        res
      )
      widened
      AbsPSet.empty.
  (* lub takes into account its use in the Kildall algorithm. Therefore, it
     performs widening if its 2nd parameter grows in a possibly-infinite
     fashion, and thus it is not commutative. *)
  Definition lub (old: t) (new: t): t :=
    lub' old (widen new old).
  Hypothesis ge_lub_left: forall x y, ge (lub x y) x.
  Hypothesis ge_lub_right: forall x y, ge (lub x y) y.
  Definition top := add AbsPH.top AbsPSet.empty.
  Axiom ge_top: forall x, ge top x.
  Definition singleton x := add x bot.
  Axiom In_singleton: forall x, In x (singleton x).
  Axiom In_singleton_hierarchy: forall x y,
    AbsPH.hierarchy x y -> In y (singleton x).
  Axiom not_In_bot: forall x, ~ In x bot.
  Axiom In_top: forall x, In x top.
  Axiom ge_top_eq_top: forall x, ge x top <-> eq x top.
  Axiom top_ge: forall x, ge top x.
  Opaque mem In beq ge lub bot top.
  Hint Resolve In_add_same In_add_hierarchy eq_refl eq_sym eq_trans beq_correct
    ge_refl ge_trans ge_bot ge_lub_left ge_lub_right In_singleton
    In_singleton_hierarchy not_In_bot ge_top In_top ge_top_eq_top top_ge: ptset.
End PTSet.

(* Registers *)

Module ROT <: OrderedType := OrderedTypeEx.Positive_as_OT.

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
    auto.
  Qed.
End NaiveMergeStrategy.

Module RMapMergeStrategy := NaiveMergeStrategy(ROT)(PTSet).
Module RMapWithoutTop := MapSemiLattice(ROT)(PTSet)(RMapMergeStrategy).

Module RMap <: SEMILATTICE_WITH_TOP.
  Module L := SemiLatticeToLattice(RMapWithoutTop).
  Include L.
  (* get should be like find, but wrapping the option type away *)
  Definition get (k: ROT.t) (rmap: t): PTSet.t :=
    match rmap with
    | Top        => PTSet.top
    | Some rmap' =>
      match RMapWithoutTop.M.find k rmap' with
      | None   => PTSet.bot
      | Some s => s
      end
    end.

  Definition add (r: ROT.t) (s: PTSet.t) (rmap: t): t :=
    match rmap with
    | Top        => Top
    | Some rmap' =>
      Some (RMapWithoutTop.M.add r (PTSet.lub s (get r rmap)) rmap')
    end.

  (*Parameter set: ROT.t -> PTSet.t -> t -> t.*)

  Theorem get_ge: forall rmap rmap',
    ge rmap rmap' ->
    (forall k, PTSet.ge (RMap.get k rmap) (RMap.get k rmap')).
  Proof.
    intros. unfold get. destruct rmap, rmap'; auto with ptset.
    specialize (H k).
    destruct (RMapWithoutTop.M.find k t0);
    destruct (RMapWithoutTop.M.find k t1);
    auto with ptset.
  Qed.

  Theorem get_add_same: forall k v m, PTSet.ge (get k (add k v m)) v.
  Proof.
    intros. destruct m; simpl.
    rewrite RMapWithoutTop.FMF.add_eq_o.
    apply PTSet.ge_lub_left.
    reflexivity.
    apply PTSet.ge_top.
  Qed.

  Theorem get_add: forall x y s m, PTSet.ge (get x (add y s m)) (get x m).
  Proof.
    intros. destruct m; simpl.
    destruct (peq x y).
    subst. rewrite RMapWithoutTop.FMF.add_eq_o.
    apply PTSet.ge_lub_right.
    reflexivity.
    rewrite RMapWithoutTop.FMF.add_neq_o.
    apply PTSet.ge_refl. apply PTSet.eq_refl.
    auto.
    apply PTSet.ge_top.
  Qed.

  Theorem ge_add: forall k v m, ge (add k v m) m.
  Proof.
    intros. destruct m; simpl; intuition.
    unfold RMapWithoutTop.ge. intros.
    destruct (peq k k0).
    subst. rewrite RMapWithoutTop.FMF.add_eq_o; [|auto].
    generalize (RMapWithoutTop.M.find k0 t0); intros s. destruct s; [|auto].
    apply PTSet.ge_lub_right.
    rewrite RMapWithoutTop.FMF.add_neq_o; [|auto].
    generalize (RMapWithoutTop.M.find k0 t0); intros s. destruct s; [|auto].
    apply PTSet.ge_refl. apply PTSet.eq_refl.
  Qed.

  Theorem get_top: forall k, PTSet.ge (get k top) PTSet.top.
  Proof.
    intros. simpl. apply PTSet.ge_top.
  Qed.

  Global Opaque eq ge bot get add (*set*).
End RMap.

(* Memory *)

Module AbsPOMap (L: SEMILATTICE_WITH_TOP)
  <: OMap(AbsPO)(L)
  <: SEMILATTICE_WITH_TOP.
  Module AbsPOMapMergeStrategy :=
    NaiveMergeStrategy(AbsPOT)(L). (* won't use it anyway *)
  Module MSL := MapSemiLattice(AbsPOT)(L)(AbsPOMapMergeStrategy).
  Module LAT := SemiLatticeToLattice(MSL).
  Include LAT.

  Function get_rec (k: AbsPO.t) (m: MSL.t) {measure AbsPO.measure k}: L.t :=
    match MSL.M.find k m with
    | Some s => s
    | None   =>
      match AbsPO.parent k with
      | None   => L.bot
      | Some p => get_rec p m
      end
    end.
  Proof.
    intros. rewrite (AbsPH.parent_measure k p teq0). auto.
  Qed.

  Definition get (k: AbsPO.t) (m: t): L.t :=
    match m with
    | Top    => L.top
    | Some m => get_rec k m
    end.

  Definition lub_on_overlap (key: AbsPO.t) (val: L.t) (k: AbsPO.t) (v: L.t)
    : L.t :=
    if AbsPO.overlap_dec key k then L.lub v val else v.

  Definition add_overlap key val m :=
    MSL.M.mapi (lub_on_overlap key val) m.

  Definition add (k: AbsPO.t) (v: L.t) (m: t): t :=
    match m with
    | Top    => Top
    | Some m =>
      Some (MSL.M.add k (L.lub v (get k (Some m))) (add_overlap k v m))
    end.

  (*Parameter set: AbsPO.t -> L.t -> t -> t.*)
  Theorem get_add_same: forall k s m, L.ge (get k (add k s m)) s.
  Proof.
    intros. destruct m; simpl.
    generalize (get_rec k t0). generalize (add_overlap k s t0). intros m' s'.
    remember (MSL.M.add k (L.lub s s') m').
    functional induction (get_rec k t1); rewrite MSL.FMF.add_eq_o in e; inv e;
      try solve [destruct k; auto].
    apply L.ge_lub_left.
    apply L.ge_top.
  Qed.

  Theorem get_add: forall x y s m, L.ge (get x (add y s m)) (get x m).
  Proof.
    intros. destruct m; simpl.
    destruct (AbsPO.eq_dec x y).

    subst.
    generalize (add_overlap y s t0). intros m'.
    remember (MSL.M.add y (L.lub s (get_rec y t0)) m').
    functional induction (get_rec y t1); rewrite MSL.FMF.add_eq_o in e; inv e;
      try solve [destruct k; auto].
    apply L.ge_lub_right.

    remember (MSL.M.add y (L.lub s (get_rec y t0)) (add_overlap y s t0)).
    functional induction (get_rec x t1).
    rewrite MSL.FMF.add_neq_o in e.
    admit.
    destruct k, y; repeat (subst; intuition).
    destruct k; destruct t1; inv e0. rewrite MSL.FMF.add_neq_o in e.
    admit.
    destruct y; repeat (subst; intuition).
    admit.

    apply L.ge_refl. apply L.eq_refl.
  Qed.

  Theorem get_add_overlap: forall x y s m,
    AbsPO.overlap x y ->
    L.ge (get x (add y s m)) s.
  Proof.
    intros.
    admit.
  Qed.

  (*
  Axiom get_set_same: forall k s m, L.ge (get k (set k s m)) s.
  Axiom get_set_other: forall x y s m, L.ge (get x (set y s m)) (get x m).
  *)

  (* Additional lemmas *)
  (*
  Theorem get_eq: forall mmap mmap'
    (EQ: eq mmap mmap')
    ,
    (forall k, L.eq (get k mmap) (get k mmap')).
  Proof.
    intros.
    destruct mmap, mmap'; try solve [inv EQ | apply L.eq_refl]; simpl.
    pose proof (EQ k) as EQk.
    functional induction (get_rec k t0); rewrite e in EQk.
    functional induction (get_rec k t1); rewrite e0 in EQk; intuition.
    functional induction (get_rec k t1); rewrite e1 in EQk.
    elim EQk. apply L.eq_refl. rewrite e2 in e0; inv e0.
    pose proof (EQ p) as EQp.
    functional induction (get_rec k t1); rewrite e1 in EQk.
    elim EQk. rewrite e2 in e0; inv e0. rewrite e2 in e0; inv e0.
    functional induction (get_rec p m); rewrite e0 in *;
    functional induction (get_rec k0 m0); rewrite e3 in *; intuition.
  Qed.
  *)

  Theorem get_ge: forall mmap mmap',
    ge mmap mmap' ->
    (forall k, L.ge (get k mmap) (get k mmap')).
  Proof.
  Admitted.

  Theorem ge_get_top: forall k, L.ge (get k top) L.top.
  Proof.
    intros. simpl. apply L.ge_top.
  Admitted.

  Theorem get_top: forall k,
    get k top = L.top.
  Proof.
    auto.
  Qed.

  Theorem get_eq_top: forall mmap,
    eq mmap top ->
    (forall k, L.ge (get k mmap) L.top).
  Proof.
  Admitted.

  Theorem ge_add: forall k v m,
    ge (add k v m) m.
  Proof.
  Admitted.

  Theorem get_bot: forall k,
    get k bot = L.bot.
  Proof.
    intros. simpl. remember MSL.bot.
    functional induction (get_rec k t0); inv e; auto.
  Qed.
End AbsPOMap.

Module WFAbsPOMap (L: SEMILATTICE_WITH_TOP)
  <: OMap(AbsPO)(L)
  <: SEMILATTICE_WITH_TOP.
  Module Raw := AbsPOMap(L).
  Definition well_formed (m: Raw.t) :=
    forall x y, AbsPO.hierarchy y x -> L.ge (Raw.get y m) (Raw.get x m).
  Definition t := { m: Raw.t | well_formed m }.

  Definition eq (m: t) (n: t): Prop := Raw.eq (proj1_sig m) (proj1_sig n).
  Theorem eq_refl: forall m, eq m m.
  Proof. intros. apply Raw.eq_refl. Qed.
  Theorem eq_sym: forall m n, eq m n -> eq n m.
  Proof. intros. apply Raw.eq_sym. exact H. Qed.
  Theorem eq_trans: forall m n o, eq m n -> eq n o -> eq m o.
  Proof. intros. eapply Raw.eq_trans; eauto. Qed.
  Definition beq (m: t) (n: t): bool := Raw.beq (proj1_sig m) (proj1_sig n).
  Theorem beq_correct: forall m n, beq m n = true -> eq m n.
  Proof. intros. apply Raw.beq_correct. exact H. Qed.
  Definition ge (m: t) (n: t): Prop := Raw.ge (proj1_sig m) (proj1_sig n).
  Theorem ge_refl: forall m n, eq m n -> ge m n.
  Proof. intros. apply Raw.ge_refl. exact H. Qed.
  Theorem ge_trans: forall m n o, ge m n -> ge n o -> ge m o.
  Proof. intros. eapply Raw.ge_trans; eauto. Qed.
  Program Definition bot: t := exist _ Raw.bot _.
  Next Obligation.
    repeat intro. setoid_rewrite Raw.get_bot. apply L.ge_bot.
  Qed.
  Theorem ge_bot: forall x, ge x bot.
  Proof. intros. apply Raw.ge_bot. Qed.
  Program Definition lub (m: t) (n: t): t := exist _ (Raw.lub m n) _.
  Next Obligation.
    repeat intro. destruct m as [m WFm], n as [n WFn]. simpl.
    destruct m as [m|], n as [n|]; try solve [apply L.ge_top]; simpl.
    remember (Raw.MSL.lub m n) as mn.
    admit.
  Qed.
  Theorem ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    admit.
  Qed.
  Theorem ge_lub_right: forall x y, ge (lub x y) y.
  Proof.
    admit.
  Qed.
  Program Definition top: t := exist _ Raw.top _.
  Next Obligation.
    repeat intro. setoid_rewrite Raw.get_top. apply L.ge_top.
  Qed.
  Theorem ge_top: forall m, ge top m.
  Proof. intros. apply Raw.ge_top. Qed.
  Definition get k (m: t): L.t := Raw.get k (proj1_sig m).
  Program Definition add k v (m: t): t := exist _ (Raw.add k v (proj1_sig m)) _.
  Next Obligation.
    repeat intro. admit.
  Qed.
  Theorem get_add_same: forall k s m, L.ge (get k (add k s m)) s.
  Proof.
    admit.
  Qed.
  Theorem get_add: forall x y s m, L.ge (get x (add y s m)) (get x m).
  Proof.
    admit.
  Qed.
  Theorem get_add_overlap: forall x y s m,
    AbsPO.overlap x y ->
    L.ge (get x (add y s m)) s.
  Proof.
    admit.
  Qed.
  Theorem get_top: forall k, L.ge (get k top) L.top.
  Proof.
    admit.
  Qed.
  Theorem get_eq_top: forall mmap,
    eq mmap top ->
    (forall k, L.ge (get k mmap) L.top).
  Proof.
    admit.
  Qed.
  Theorem get_ge: forall mmap mmap',
    ge mmap mmap' ->
    (forall k, L.ge (get k mmap) (get k mmap')).
  Proof.
  Admitted.
  Theorem ge_add: forall k v m,
    ge (add k v m) m.
  Proof.
  Admitted.
  Theorem ge_get_hierarchy: forall x y m,
    AbsPO.hierarchy x y ->
    L.ge (get x m) (get y m).
  Proof.
    intros. unfold get. destruct m. simpl. apply w. exact H.
  Qed.

  Global Opaque eq ge bot get add (*set*) top.
End WFAbsPOMap.

Module MMap <: SEMILATTICE.
  Module WFAPOM := WFAbsPOMap(PTSet).
  Include WFAPOM.
  Hint Resolve get_add_same get_add get_add_overlap
  (*get_set_same get_set_other*)
    (*get_ge*) get_top get_eq_top: mmap.
End MMap.

(* Result *)

Module Result <: SEMILATTICE.
  Module R := ProductSemiLattice(RMap)(MMap).
  Include R.
  Definition top := (RMap.top, MMap.top).
End Result.

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
  inv H.
  inv H. apply H0 in H4. subst.
  simpl. apply fold_left_preserves_prop; auto.
  eapply IHl; eauto.
Qed.

(* Transfer function *)
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
  simpl. apply PTSet.In_add_same.
  intros.
  apply PTSet.In_equiv in H. intuition; apply PTSet.In_equiv.
  left; destruct y; apply PTSet.F.add_iff; right; auto.
  right. destruct H0 as [px]. exists px. intuition.
  apply PTSet.In_equiv in H1. intuition; apply PTSet.In_equiv.
  left; destruct y; apply PTSet.F.add_iff; right; auto.
  right. destruct H as [px']. exists px'. intuition.
  apply PTSet.In_equiv in H2. intuition; apply PTSet.In_equiv.
  left; destruct y; apply PTSet.F.add_iff; right; auto.
  exfalso.
  destruct H as [px'']. intuition. crunch_hierarchy.
Qed.

Lemma In_unknown_offset_same_aux:
  forall p s
    (IN: PTSet.AbsPSet.In p s),
    PTSet.In p (unknown_offset s).
Proof.
  intros. apply PTSet.In_equiv. destruct p.
  left. unfold unknown_offset. rewrite PTSet.AbsPSet.fold_1.
  eapply fold_left_adds_prop.
  apply PTSet.F.elements_iff. eauto.
  intros. destruct x, y; subst; try (intuition; congruence).
  simpl. intros. apply PTSet.F.add_iff. auto.
  intros. destruct y; apply PTSet.F.add_iff; right; auto.
  right. exists (Blk a). intuition. apply PTSet.In_equiv. left.
  unfold unknown_offset. rewrite PTSet.AbsPSet.fold_1.
  eapply fold_left_adds_prop.
  apply PTSet.F.elements_iff. eauto.
  intros. destruct x, y; subst; try (intuition; congruence).
  simpl. intros. apply PTSet.F.add_iff. auto.
  intros. destruct y; apply PTSet.F.add_iff; right; auto.
Qed.

Theorem In_unknown_offset_same:
  forall p s
    (IN: PTSet.In p s),
    PTSet.In p (unknown_offset s).
Proof.
  intros.
  apply PTSet.In_equiv in IN. intuition.
  apply In_unknown_offset_same_aux. auto.
  destruct H as [pp]. intuition. apply PTSet.In_equiv. right. exists pp.
  intuition.
  apply PTSet.In_equiv in H1. intuition.
  apply In_unknown_offset_same_aux. auto.
  destruct H as [ppp]. intuition. apply PTSet.In_equiv. right. exists ppp.
  intuition.
  apply PTSet.In_equiv in H2. intuition.
  apply In_unknown_offset_same_aux. auto.
  destruct H as [pppp]. intuition. apply PTSet.In_equiv. right. exists pppp.
  intuition.
  apply PTSet.In_equiv in H3. intuition.
  apply In_unknown_offset_same_aux. auto.
  destruct H as [ppppp]. intuition.
  crunch_hierarchy.
Qed.

(*
Check MMap.MSL.M.fold.
=>
Anomaly: uncaught exception Failure "Cannot print a global reference".
Please report.
*)

Definition image_of_ptset (s: PTSet.t) (m: MMap.t): PTSet.t :=
  PTSet.AbsPSet.fold
    (fun p saccu => PTSet.lub (MMap.get p m) saccu)
    s
    PTSet.bot.

Definition add_ptset_to_image (sadd: PTSet.t) (smod: PTSet.t) (m: MMap.t)
  : MMap.t :=
  PTSet.AbsPSet.fold (fun k maccu => MMap.add k sadd maccu) smod m.

Definition addr_image addr args rmap :=
  match addr, args with
    | Aindexed o, r::nil             =>
      Some (shift_offset (RMap.get r rmap) o)
    | Aindexed2 _, r1::r2::nil       =>
      Some (PTSet.lub
        (unknown_offset (RMap.get r1 rmap))
        (unknown_offset (RMap.get r2 rmap))
      )
    | Ascaled _ _, _::nil            => Some PTSet.bot
    | Aindexed2scaled _ _, r::_::nil =>
      Some (unknown_offset (RMap.get r rmap))
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
    | Olea addr =>
      match addr_image addr args rmap with
        | None   => rmap (*!*)
        | Some s => RMap.add dst s rmap
      end
    | Omove     =>
      match args with
        | r::nil => RMap.add dst (RMap.get r rmap) rmap
        | _      => rmap (*!*)
      end
    | Osub      =>
      match args with
        | r::_::nil => RMap.add dst (unknown_offset (RMap.get r rmap)) rmap
        | _         => rmap (*!*)
      end
    | _         => rmap
  end.

Definition transf_builtin ef args dst n (result: Result.t) :=
  let (rmap, mmap) := result in
  match ef with
  | EF_external _ _ =>
    (RMap.add dst (PTSet.singleton (Blk (Just (Globals All)))) rmap, mmap)
  | EF_builtin _ _  =>
    (RMap.add dst (PTSet.singleton (Blk (Just (Globals All)))) rmap, mmap)
    (*TODO: to do better things on vload/vstore global, we would first need
       to have strong updates, since Globals start at top anyway. *)
  | EF_vload _ | EF_vload_global _ _ _ => (RMap.add dst PTSet.top rmap, mmap)
  | EF_vstore _ =>
    match args with
    | r1 :: r2 :: nil =>
      (rmap, add_ptset_to_image (RMap.get r2 rmap) (RMap.get r1 rmap) mmap)
    | _               => result
    end
  | EF_vstore_global _ i o =>
    match args with
    | r :: nil =>
      (rmap, MMap.add (Loc (Just (Globals (Just i))) o) (RMap.get r rmap) mmap)
    | _               => result
    end
  | EF_malloc        =>
    (RMap.add dst
      (PTSet.singleton (Loc (Just (Allocs (Just n))) Int.zero)) rmap,
      mmap)
  | EF_free          => result
  | EF_memcpy _ _    =>
    match args with
    | rdst :: rsrc :: nil =>
      (rmap,
        add_ptset_to_image PTSet.top (unknown_offset (RMap.get rdst rmap)) mmap)
    | _                   => result (*!*)
    end
  | EF_annot _ _     => result
  | EF_annot_val _ _ =>
    match args with
    | r1 :: nil => (RMap.add dst (RMap.get r1 rmap) rmap, mmap)
    | _       => result (*!*)
    end
  end.

Definition transf c n (result: Result.t) :=
  let (rmap, mmap) := result in
  match c!n with
  | Some instr =>
    match instr with
    | Inop _                          => result
    | Iop op args dst succ            => (transf_op op args dst rmap, mmap)
    | Iload chunk addr args dst succ  =>
      match chunk with
      | Mint32 =>
        match addr_image addr args rmap with
        | None   => result (*!*)
        | Some s => (RMap.add dst (image_of_ptset s mmap) rmap, mmap)
        end
      | _ => (RMap.add dst PTSet.bot rmap, mmap)
      end
    | Istore chunk addr args src succ =>
      match chunk with
      | Mint32 =>
        match addr_image addr args rmap with
        | None      => result (*!*)
        | Some sdst => (rmap, add_ptset_to_image (RMap.get src rmap) sdst mmap)
        end
      | _ => result
      end
    | Icall sign fn args dst succ     => (RMap.add dst PTSet.top rmap, MMap.top)
    | Itailcall sign fn args          => (rmap, MMap.top)
    | Ibuiltin ef args dst succ       => transf_builtin ef args dst n result
    | Icond cond args ifso ifnot      => result
    | Ijumptable arg tbl              => result
    | Ireturn _                       => result
    end
  | None       => result
  end.

(* Kildall solver *)

Module Solver := Dataflow_Solver(Result)(NodeSetForward).

Definition coerce_solver (res: Solver.L.t): (RMap.t * MMap.t) := res.

Definition add_reg_top rmap r := RMap.add r PTSet.top rmap.

Definition entry_rmap l := fold_left add_reg_top l RMap.bot.

Definition entry_mmap :=
  MMap.add (Blk (Just (Globals All))) PTSet.top (
  MMap.add (Blk (Just Other)) PTSet.top (
  MMap.bot)).

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
    | None    => PTSet.ge s PTSet.top (* equivalent to eq but easier in proofs *)
    end
  | _        => True
  end.
Hint Unfold valsat: unalias.

Definition regsat (r: reg) (rs: regset) (abs: abstracter) (rmap: RMap.t) :=
  valsat rs#r abs (RMap.get r rmap).
Hint Unfold regsat: unalias.

Definition memsat
  (b: block) (o: Int.int) (m: mem) (abs: abstracter) (mmap: MMap.t)
  :=
  forall v
    (LOAD: Mem.loadv Mint32 m (Vptr b o) = Some v)
    ,
    (match abs b with
     | Some ab => valsat v abs (MMap.get (Loc ab o) mmap)
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
  (RET:  PTSet.ge (RMap.get rret rmap) PTSet.top) (* same as eq, easier *)
  (MTOP: MMap.eq mmap MMap.top)
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

Lemma In_unknown_offset:
  forall b o s
    (IN: PTSet.In (Loc b o) s)
    ,
    (forall o', PTSet.In (Loc b o') (unknown_offset s)).
Proof.
  intros. remember (Loc b o) as lb. remember (Loc b o') as lb'.
  remember (unknown_offset s) as uos.
  functional induction (PTSet.In lb s); [ | crunch_hierarchy].
  clear IHP. destruct IN.
  functional induction (PTSet.In lb' uos); [ | crunch_hierarchy].
  clear IHP.
  assert (px = px0) by (crunch_hierarchy; auto); subst.
  right. destruct px0; inv e. eapply In_unknown_offset_block_of_loc; eauto.
  functional induction (PTSet.In lb' uos); [ | crunch_hierarchy].
  clear IHP.
  assert (px = px0) by (crunch_hierarchy; auto); subst.
  right. eauto using In_unknown_offset_same.
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
  apply PTSet.In_equiv in IN. intuition.
  eapply fold_left_adds_prop.
  apply PTSet.F.elements_iff. eauto.
  intros. destruct x, y; subst; try (intuition; congruence).
  simpl. apply PTSet.In_add_same.
  intros. destruct y; apply PTSet.In_add_already; auto.

  destruct H as [px]. simpl in *. intuition. inv H0.
  apply PTSet.In_equiv in H1. intuition.
  eapply fold_left_adds_prop.
  apply PTSet.F.elements_iff. eauto.
  intros. destruct x, y; subst; try (intuition; congruence).
  simpl. apply PTSet.In_add_hierarchy. simpl. auto.
  intros. destruct y; apply PTSet.In_add_already; auto.

  destruct H as [px]. intuition.
  apply PTSet.In_equiv in H1. intuition.
  eapply fold_left_adds_prop.
  apply PTSet.F.elements_iff. eauto.
  intros. destruct x, y; subst; try (intuition; congruence).
  intros. destruct px, b; inv H0. apply PTSet.In_add_hierarchy.
  destruct a; simpl; auto; destruct o0; simpl; auto.
  intros. destruct y; apply PTSet.In_add_already; auto.

  destruct H as [ppx]. intuition.
  apply PTSet.In_equiv in H2. intuition.
  eapply fold_left_adds_prop.
  apply PTSet.F.elements_iff. eauto.
  intros. destruct x, y; subst; try (intuition; congruence).
  intros. crunch_hierarchy; apply PTSet.In_add_hierarchy; simpl; auto.
  intros. destruct y; apply PTSet.In_add_already; auto.

  destruct H as [pppx]. intuition. exfalso. crunch_hierarchy.
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
  repeat intro. pose proof (GETOP _ H) as xIns. clear H.
  remember (shift_offset s oshift).
  functional induction (PTSet.In x t);
    functional induction (PTSet.In x s);
      merge; intuition.
  unfold shift_offset. rewrite PTSet.AbsPSet.fold_1.
  destruct x; inv e. destruct t; inv H0.
  eapply fold_left_adds_prop.
  apply PTSet.F.elements_iff. eauto.
  intros. destruct x, y; subst; try (intuition; congruence).
  intros. simpl. apply PTSet.F.add_iff. left; auto.
  intros. simpl. destruct y; apply PTSet.F.add_iff; right; auto.
Qed.

Lemma In_image_of_ptset:
  forall x y mmap s,
    PTSet.In x s ->
    PTSet.In y (MMap.get x mmap) ->
    PTSet.In y (image_of_ptset s mmap).
Proof.
  intros. unfold image_of_ptset. rewrite PTSet.AbsPSet.fold_1.

  functional induction (PTSet.In x s); intuition. clear IHP.

  eapply fold_left_adds_prop.
  apply PTSet.F.elements_iff. eauto.
  intros. destruct x0, y0; subst; try (intuition; congruence).
  intros. apply PTSet.ge_lub_left. auto.
  intros. apply PTSet.ge_lub_right. auto.

  functional induction (PTSet.In px s); intuition; try clear IHP.

  eapply fold_left_adds_prop.
  apply PTSet.F.elements_iff. eauto.
  intros. destruct x1, y0; subst; try (intuition; congruence).
  intros. apply PTSet.ge_lub_left. eapply MMap.ge_get_hierarchy; eauto.
  crunch_hierarchy.
  intros. apply PTSet.ge_lub_right. auto.

  functional induction (PTSet.In px s); intuition; try clear IHP.

  eapply fold_left_adds_prop.
  apply PTSet.F.elements_iff. eauto.
  intros. destruct x2, y0; subst; try (intuition; congruence).
  intros. apply PTSet.ge_lub_left. eapply MMap.ge_get_hierarchy; eauto.
  crunch_hierarchy.
  intros. apply PTSet.ge_lub_right. auto.

  functional induction (PTSet.In px s); intuition; try clear IHP.

  eapply fold_left_adds_prop.
  apply PTSet.F.elements_iff. eauto.
  intros. destruct x3, y0; subst; try (intuition; congruence).
  intros. apply PTSet.ge_lub_left. eapply MMap.ge_get_hierarchy; eauto.
  crunch_hierarchy.

  crunch_hierarchy.
  crunch_hierarchy.

  eapply fold_left_adds_prop.
  apply PTSet.F.elements_iff. eauto.
  intros. destruct x3, y0; subst; try (intuition; congruence).
  intros. apply PTSet.ge_lub_left. eapply MMap.ge_get_hierarchy; eauto.
  crunch_hierarchy.
  intros. apply PTSet.ge_lub_right. auto.

  eapply fold_left_adds_prop.
  apply PTSet.F.elements_iff. eauto.
  intros. destruct x2, y0; subst; try (intuition; congruence).
  intros. apply PTSet.ge_lub_left. eapply MMap.ge_get_hierarchy; eauto.
  crunch_hierarchy.
  intros. apply PTSet.ge_lub_right. auto.

  eapply fold_left_adds_prop.
  apply PTSet.F.elements_iff. eauto.
  intros. destruct x1, y0; subst; try (intuition; congruence).
  intros. apply PTSet.ge_lub_left. eapply MMap.ge_get_hierarchy; eauto.
  crunch_hierarchy.
  intros. apply PTSet.ge_lub_right. auto.

  eapply fold_left_adds_prop.
  apply PTSet.F.elements_iff. eauto.
  intros. destruct x0, y0; subst; try (intuition; congruence).
  intros. apply PTSet.ge_lub_left. auto.
  intros. apply PTSet.ge_lub_right. auto.
Qed.

Lemma In_add_ptset_to_image:
  forall x y sfrom sto mmap
    (FROM: PTSet.In x sfrom)
    (TO:   PTSet.In y sto)
    ,
    PTSet.In x (MMap.get y (add_ptset_to_image sfrom sto mmap)).
Proof.
Admitted.

Lemma ge_add_ptset_to_image:
  forall mmap s s',
    MMap.ge (add_ptset_to_image s s' mmap) mmap.
Proof.
Admitted.

Lemma addr_image_correct:
  forall ge rs rmap abs addr args b o ab s bsp
    (GENV: ok_abs_genv abs ge)
    (SP:   abs bsp = Some (Just Stack))
    (RSAT: forall r, regsat r rs abs rmap)
    (EA:   eval_addressing ge (Vptr bsp Int.zero) addr rs##args = Some (Vptr b o))
    (ABS:  abs b = Some ab)
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
  specialize (GENV _ _ Heqo). merge. apply PTSet.In_singleton_hierarchy. compute; auto.
  specialize (GENV _ _ Heqo0). merge. apply PTSet.In_singleton_hierarchy. compute; auto.
  rewrite Int.add_zero_l. apply PTSet.In_singleton.
Qed.

Lemma regsat_ge1:
  forall rs rmap abs rmap' r
    (RSAT: regsat r rs abs rmap)
    (GE:   RMap.ge rmap' rmap)
    ,
    regsat r rs abs rmap'.
Proof.
  intros. unalias. destruct (rs#r); auto. destruct (abs b).
  destruct (abs b), rmap, rmap'; auto with ptset; try solve [eapply RMap.get_ge; eauto].
  eapply PTSet.ge_trans; eauto. apply RMap.get_ge. auto.
Qed.

Lemma regsat_ge:
  forall rs rmap abs rmap'
    (RSAT: forall r, regsat r rs abs rmap)
    (GE:   RMap.ge rmap' rmap)
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
    (forall r, regsat r rs abs RMap.top).
Proof.
  intros. unalias. destruct (rs#r) as []_eqn; auto. destruct (abs b) as []_eqn.
  apply RMap.get_top. apply PTSet.In_top.
  apply RMap.get_top.
Qed.

Lemma memsat_ge:
  forall m abs mmap mmap'
    (MSAT: forall b o, memsat b o m abs mmap)
    (GE:   MMap.ge mmap' mmap)
    ,
    (forall b o, memsat b o m abs mmap').
Proof.
  repeat intro. unalias. specialize (MSAT _ _ _ LOAD).
  destruct (abs b), v; auto. destruct (abs b0).
  eapply MMap.get_ge; eauto.
  eapply PTSet.ge_trans; eauto. apply MMap.get_ge. auto.
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
    (forall b o, memsat b o m abs MMap.top).
Proof.
  unalias. intros. destruct (abs b) as []_eqn.
  destruct v; auto. destruct (abs b0) as []_eqn.
  apply MMap.get_top. apply PTSet.In_top.
  apply MMap.get_top.
  simpl in LOAD. apply load_valid_block in LOAD. apply OKAM in LOAD. contradiction.
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

Theorem satisfy_init:
  forall p st
    (IS:   initial_state p st),
    exists abs, satisfy (Genv.globalenv p) abs st.
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
Set Undo 9000.
Theorem satisfy_step:
  forall ge st t st' abs
    (SAT:  satisfy ge abs st)
    (STEP: step ge st t st')
    ,
    exists abs', satisfy ge abs' st'.
Proof.
  intros.
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
      |- forall r, regsat r ?rs ?abs (RMap.add _ _ ?rmap) =>
        eapply regsat_ge; [apply H | apply RMap.ge_add]
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
    | |- PTSet.In _ (RMap.get ?r (RMap.add ?r _ _)) =>
      apply RMap.get_add_same; regsat_tac
    | |- PTSet.ge (RMap.get ?r (RMap.add ?r _ _)) _ =>
      eapply PTSet.ge_trans; [apply RMap.get_add_same | auto]; regsat_tac

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
  apply PTSet.In_singleton_hierarchy. compute; auto.
  SSSSSCase "Olea Abasedscaled".
  apply PTSet.In_singleton_hierarchy. compute; auto.
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
      [ eapply regsat_ge; [auto | apply RMap.ge_add]
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
  crunch_eval; inv H0; apply RMap.get_add_same; eapply In_image_of_ptset;
    eauto; merge.
  eapply In_shift_offset; eauto.
  apply PTSet.ge_lub_right. eapply In_unknown_offset; eauto.
  apply PTSet.ge_lub_left. eapply In_unknown_offset; eauto.
  eapply In_unknown_offset; eauto.
  specialize (GENV _ _ Heqo2). merge. apply PTSet.In_singleton.
  specialize (GENV _ _ Heqo1). merge. apply PTSet.In_singleton_hierarchy. compute; auto.
  specialize (GENV _ _ Heqo1). merge. apply PTSet.In_singleton_hierarchy. compute; auto.
  rewrite Int.add_zero_l. apply PTSet.In_singleton.
  SSSSSSCase "abs b = None".
  crunch_eval; inv H0; (
  eapply PTSet.ge_trans;
    [ apply RMap.get_add_same
    | repeat intro; eapply In_image_of_ptset; [ | apply MSAT; apply PTSet.In_top]
    ]); merge.
  eapply In_shift_offset; eauto.
  apply PTSet.ge_lub_right. eapply In_unknown_offset; eauto.
  apply PTSet.ge_lub_left. eapply In_unknown_offset; eauto.
  eapply In_unknown_offset; eauto.
  apply unknown_offset_top; auto. apply PTSet.In_top.
  specialize (GENV _ _ Heqo2). merge. apply PTSet.In_singleton.
  specialize (GENV _ _ Heqo3). merge. apply PTSet.In_singleton_hierarchy. compute; auto.
  specialize (GENV _ _ Heqo3). merge. apply PTSet.In_singleton_hierarchy. compute; auto.
  merge. rewrite Int.add_zero_l. apply PTSet.In_singleton.
  SSSSSCase "r <> dst".
  eapply regsat_assign_other; eauto. destruct addr_image; inv H0; auto.
  eapply regsat_ge; eauto. apply RMap.ge_add.
  SSSSCase "memsat".
  eapply memsat_ge; eauto. eapply MMap.ge_trans; eauto.
  destruct chunk; try solve [inv H0; apply MMap.ge_refl; apply MMap.eq_refl].
  destruct addr_image; inv H0; apply MMap.ge_refl; apply MMap.eq_refl.
  SSCase "Istore".
  assert (MGE': MMap.ge mmap' mmap) by (
  destruct chunk; try solve [inv H0; apply MMap.ge_refl; apply MMap.eq_refl];
  destruct addr_image; inv H0;
    [ apply ge_add_ptset_to_image
    | apply MMap.ge_refl; apply MMap.eq_refl
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
  eapply regsat_ge; eauto. eapply RMap.ge_trans; eauto. eapply RMap.ge_refl.
  destruct chunk; try solve [inv H0; apply RMap.eq_refl].
  destruct addr_image; inv H0; apply RMap.eq_refl.
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
  eapply MMap.get_ge; eauto.
  SSSSSSSCase "abs b = None".
  eapply PTSet.ge_trans; eauto. apply MMap.get_ge; auto.
  SSSSSSCase "Didn't overlap offset o, for another reason".
  simpl in LOAD.
  erewrite Mem.load_store_other in LOAD; eauto; [|right; left; omega]. merge.
  destruct (abs b0) as []_eqn; [|contradiction].
  destruct v; auto.
  destruct (abs b) as []_eqn.
  SSSSSSSCase "abs b = Some".
  eapply MMap.get_ge; eauto.
  SSSSSSSCase "abs b = None".
  eapply PTSet.ge_trans; eauto. apply MMap.get_ge; auto.
  SSSSSCase "Didn't store in b0".
  simpl in LOAD. erewrite Mem.load_store_other in LOAD; eauto. merge.
  destruct (abs b0) as []_eqn; [|contradiction].
  destruct v; auto.
  destruct (abs b1) as []_eqn.
  SSSSSSCase "abs b1 = Some".
  eapply MMap.get_ge; eauto.
  SSSSSSCase "abs b1 = None".
  eapply PTSet.ge_trans; eauto. apply MMap.get_ge; auto.
  SSCase "Ibuiltin".
  assert (RGE': RMap.ge rmap' rmap) by (
  destruct ef; repeat (
    try solve [inv H0; apply RMap.ge_add];
    try solve [inv H0; apply RMap.ge_refl; apply RMap.eq_refl];
    destruct args)).
  assert (MGE': MMap.ge mmap' mmap).
  destruct ef; repeat (
    try solve [inv H0; apply ge_add_ptset_to_image];
    try solve [inv H0; apply MMap.ge_refl; apply MMap.eq_refl];
    try solve [inv H0; apply MMap.ge_add];
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
    eapply regsat_ge; [eauto | eapply RMap.ge_trans; eauto]].
  unfold regsat, valsat. rewrite Regmap.gss. destruct v; auto.
  inv H1. specialize (GENV _ _ H4). rewrite GENV.
  eapply PTSet.ge_trans. apply RMap.get_ge; apply RGE. apply RMap.get_add_same.
  apply PTSet.In_singleton_hierarchy. compute; auto.
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
    eapply regsat_ge; [eauto | eapply RMap.ge_trans; eauto]].
  unfold regsat, valsat. rewrite Regmap.gss. destruct v; auto.
  inv H1. specialize (GENV _ _ H4). rewrite GENV.
  eapply PTSet.ge_trans. apply RMap.get_ge; apply RGE. apply RMap.get_add_same.
  apply PTSet.In_singleton_hierarchy. compute; auto.
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
    eapply regsat_ge; [eauto | eapply RMap.ge_trans; eauto]].
  unfold regsat, valsat. rewrite Regmap.gss. destruct v; simpl; auto.
  regsat_tac.
  eapply RMap.get_ge. eauto. apply RMap.get_add_same. apply PTSet.In_top.
  eapply PTSet.ge_trans. apply RMap.get_ge. eauto. apply RMap.get_add_same.
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
    eapply regsat_ge; [eauto | eapply RMap.ge_trans; eauto]].
  unfold regsat, valsat. rewrite Regmap.gss. auto.
  SSSSSCase "memsat".
  eapply memsat_ge; eauto. eapply MMap.ge_trans; eauto.
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
    eapply regsat_ge; [eauto | eapply RMap.ge_trans; eauto]].
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
  eapply MMap.get_ge; eauto.
  SSSSSSSSCase "abs b = None".
  eapply PTSet.ge_trans; eauto. apply MMap.get_ge; auto.
  SSSSSSSCase "Didn't overlap offset o, for another reason".
  simpl in LOAD.
  erewrite Mem.load_store_other in LOAD; eauto; [|right; left; omega]. merge.
  destruct (abs b0) as []_eqn; [|contradiction].
  destruct v; auto.
  destruct (abs b) as []_eqn.
  SSSSSSSSCase "abs b = Some".
  eapply MMap.get_ge; eauto.
  SSSSSSSSCase "abs b = None".
  eapply PTSet.ge_trans; eauto. apply MMap.get_ge; auto.
  SSSSSSCase "Didn't store in b0".
  simpl in LOAD. erewrite Mem.load_store_other in LOAD; eauto. merge.
  destruct (abs b0) as []_eqn; [|contradiction].
  destruct v; auto.
  destruct (abs b1) as []_eqn.
  SSSSSSSCase "abs b1 = Some".
  eapply MMap.get_ge; eauto.
  SSSSSSSCase "abs b1 = None".
  eapply PTSet.ge_trans; eauto. apply MMap.get_ge; auto.
  SSSCase "EF_vload_global".
  exists abs. constructor; auto.
  SSSSCase "ok_abs_result".
  econstructor.
  SSSSSCase "result".
  unfold safe_funanalysis. rewrite Heqo. eauto.
  SSSSSCase "regsat".
  intros; destruct (peq res r); [subst | eapply regsat_assign_other; eauto;
    eapply regsat_ge; [eauto | eapply RMap.ge_trans; eauto]].
  unfold regsat, valsat. rewrite Regmap.gss. destruct v; auto.
  regsat_tac.
  eapply RMap.get_ge. eauto. apply RMap.get_add_same. apply PTSet.In_top.
  eapply PTSet.ge_trans. apply RMap.get_ge. eauto. apply RMap.get_add_same.
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
    eapply regsat_ge; [eauto | eapply RMap.ge_trans; eauto]].
  unfold regsat, valsat. rewrite Regmap.gss. auto.
  SSSSSCase "memsat".
  eapply memsat_ge; eauto. eapply MMap.ge_trans; eauto.
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
    eapply regsat_ge; [eauto | eapply RMap.ge_trans; eauto]].
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
  apply MMap.get_add_same. exact IN.
  SSSSSSSSCase "abs b = None".
  eapply PTSet.ge_trans; eauto. apply MMap.get_add_same.
  SSSSSSSCase "Didn't overlap offset o".
  simpl in LOAD.
  erewrite Mem.load_store_other in LOAD; eauto; [|right; right; omega]. merge.
  destruct (abs b) as []_eqn.
  SSSSSSSSCase "abs b = Some".
  eapply MMap.get_ge; eauto.
  SSSSSSSSCase "abs b = None".
  eapply PTSet.ge_trans; eauto. apply MMap.get_ge; auto.
  SSSSSSSCase "Didn't overlap offset o, for another reason".
  simpl in LOAD.
  erewrite Mem.load_store_other in LOAD; eauto; [|right; left; omega]. merge.
  destruct (abs b) as []_eqn.
  SSSSSSSSCase "abs b = Some".
  eapply MMap.get_ge; eauto.
  SSSSSSSSCase "abs b = None".
  eapply PTSet.ge_trans; eauto. apply MMap.get_ge; auto.
  SSSSSSCase "Didn't store in b0".
  simpl in LOAD. erewrite Mem.load_store_other in LOAD; eauto. merge.
  destruct (abs b0) as []_eqn; [|contradiction].
  destruct v; auto.
  destruct (abs b1) as []_eqn.
  SSSSSSSCase "abs b1 = Some".
  eapply MMap.get_ge; eauto.
  SSSSSSSCase "abs b1 = None".
  eapply PTSet.ge_trans; eauto. apply MMap.get_ge; auto.
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
  eapply RMap.get_ge. eauto. apply RMap.get_add_same. apply PTSet.In_singleton.
  SSSSSSCase "res <> r".
  unfold regsat, valsat. rewrite Regmap.gso; [|auto]. destruct (rs#r) as []_eqn; auto.
  regsat_intro rs r. destruct (zeq b0 b).
  SSSSSSSCase "b0 = b".
  subst. eapply RMap.get_ge. eauto. destruct (abs b) as []_eqn.
  SSSSSSSSCase "abs b = Some".
  exfalso. eapply Mem.fresh_block_alloc; eauto. apply MEM. congruence.
  SSSSSSSSCase "abs b = None".
  eapply RMap.get_ge. apply RMap.ge_add. apply IN. apply PTSet.In_top.
  SSSSSSSCase "b0 <> b".
  destruct (abs b0) as []_eqn.
  SSSSSSSSCase "abs b0 = Some".
  eapply RMap.get_ge. eauto. eapply RMap.get_ge. apply RMap.ge_add. auto.
  SSSSSSSSCase "abs b0 = None".
  eapply PTSet.ge_trans. apply RMap.get_ge. eauto.
  eapply PTSet.ge_trans. apply RMap.get_ge. apply RMap.ge_add. auto.
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
    eapply regsat_ge; [eauto | eapply RMap.ge_trans; eauto]].
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
    eapply regsat_ge; [eauto | eapply RMap.ge_trans; eauto]].
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
  eapply MMap.get_ge. apply ge_add_ptset_to_image. auto.
  SSSSSSSCase "abs b0 = None".
  eapply PTSet.ge_trans. eapply MMap.get_ge. eapply ge_add_ptset_to_image. auto.
  SSSCase "EF_annot".
  exists abs. constructor; auto.
  SSSSCase "ok_abs_result".
  econstructor.
  SSSSSCase "result".
  unfold safe_funanalysis. rewrite Heqo. eauto.
  SSSSSCase "regsat".
  intros; destruct (peq res r); [subst | eapply regsat_assign_other; eauto;
    eapply regsat_ge; [eauto | eapply RMap.ge_trans; eauto]].
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
    eapply regsat_ge; [eauto | eapply RMap.ge_trans; eauto]].
  unfold regsat, valsat. rewrite Regmap.gss. destruct v; auto.
  inv H1. specialize (GENV _ _ H5). rewrite GENV.
  destruct args. inv H. destruct args; inv H. inv H0.
  regsat_intro rs r0. rewrite GENV in IN.
  eapply RMap.get_ge. eauto. apply RMap.get_add_same. auto.
  SSSSSCase "memsat".
  eapply memsat_ge; eauto. eapply MMap.ge_trans; eauto.
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
  eapply regsat_ge; eauto. eapply RMap.ge_trans; eauto. apply RMap.ge_add.
  SSSSSCase "ret".
  eapply PTSet.ge_trans. apply RMap.get_ge; eauto.
  eapply PTSet.ge_trans. apply RMap.get_add_same. auto with ptset.
  SSSSSCase "mem".
  auto. (*?*)
  SSSSCase "Kildall failed".
  econstructor.
  SSSSSCase "result".
  unfold safe_funanalysis. rewrite Heqo. rewrite PMap.gi. unfold Result.top. eauto.
  SSSSSCase "regsat".
  eapply regsat_ge; eauto. apply RMap.ge_top.
  SSSSSCase "ret".
  apply RMap.get_top.
  SSSSSCase "mem".
  apply MMap.eq_refl.
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
  apply RMap.get_add_same. apply PTSet.In_top.
  apply RMap.get_add. auto.
  destruct (abs b).
  eapply fold_left_adds_prop; eauto; intros.
  apply RMap.get_add_same. apply PTSet.In_top.
  apply RMap.get_add. auto.
  eapply fold_left_adds_prop; eauto; intros.
  apply RMap.get_add_same.
  eapply PTSet.ge_trans. apply RMap.get_add. auto.
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
  destruct a; try destruct a; try destruct o0; first
    [ solve [apply MMap.get_add_overlap; [compute; auto | apply PTSet.In_top]]
    | solve [apply MMap.get_add; apply MMap.get_add_overlap;
      [compute; auto | apply PTSet.In_top]]
    ].
  SSSSSSCase "b0 <> stk".
  destruct (abs b0) as []_eqn.
  SSSSSSSCase "abs b0 = Some".
  unfold entry_mmap.
  destruct a; try destruct a; try destruct o0; first
    [ solve [apply MMap.get_add_overlap; [compute; auto | apply PTSet.In_top]]
    | solve [apply MMap.get_add; apply MMap.get_add_overlap;
      [compute; auto | apply PTSet.In_top]]
    ].
  SSSSSSSCase "abs b0 = None".
  unfold entry_mmap.
  destruct a; try destruct a; try destruct o0; first
    [ solve [apply MMap.get_add_overlap; compute; auto]
    | solve [eapply PTSet.ge_trans;
      [apply MMap.get_add | apply MMap.get_add_overlap; compute; auto]]
    ].
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
  subst. apply RMap.get_top. apply PTSet.In_top.
  destruct (abs b); apply RMap.get_top; apply PTSet.In_top.
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
  subst. apply MMap.get_top. apply PTSet.In_top.
  SSSSSSCase "b0 <> stk".
  destruct (abs b0) as []_eqn.
  apply MMap.get_top. apply PTSet.In_top.
  apply MMap.get_eq_top. apply MMap.eq_refl.
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
  apply MMap.get_eq_top; auto with ptset.
  destruct (zlt b (Mem.nextblock m0)). destruct v0; auto.
  destruct (abs b0).
  apply MMap.get_eq_top; auto with ptset.
  destruct (zlt b0 (Mem.nextblock m0));
  apply MMap.get_eq_top; auto with ptset.
  apply load_valid_block in LOAD. congruence.
Qed.