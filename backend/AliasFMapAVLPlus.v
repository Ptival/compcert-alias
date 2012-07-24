Require Import FMapAVL.
Require Import FMapFacts.
Require Import OrderedType.

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
      apply FMF.in_find_iff in H2. apply map2i_2 in H2. inversion H2.
      apply FMF.in_find_iff in H3. congruence.
      apply FMF.in_find_iff in H3. congruence.
    Qed.

    Lemma map2i_4: forall m m',
      (forall k, f k None None = None) ->
      forall x,
        find x (map2i m m') = f x (find x m) (find x m').
    Proof.
      intros ?? H ?. destruct (find x m) as []_eqn.
      rewrite <- Heqo. apply map2i_1. left. apply FMF.in_find_iff. congruence.
      destruct (find x m') as []_eqn.
      rewrite <- Heqo. rewrite <- Heqo0. apply map2i_1.
      right. apply FMF.in_find_iff. congruence.
      rewrite H. apply map2i_3; auto.
    Qed.

    Lemma map2i_5:
      (forall k a b, f k a b = None -> a = None /\ b = None) ->
      forall (m: t elt) (n: t elt') x,
        In x m \/ In x n ->
        In x (map2i m n).
    Proof.
      unfold map2i, In. intros Hf ?? (*Rm Rn*) ? H.
      setoid_rewrite Raw.Proofs.In_alt in H. rewrite Raw.Proofs.In_alt. simpl.
      unfold raw_map2i. apply Raw.Proofs.find_in. intro Hfind.
      rewrite Raw.Proofs.map2_opt_1 with (f0 := f) in Hfind; auto; intros.
      apply Hf in Hfind. destruct Hfind as [? ?].
      destruct H as [H|H]; apply Raw.Proofs.in_find in H; try congruence; intros.
      apply is_bst. apply is_bst.
      apply Raw.Proofs.map_option_bst; auto.
      apply Raw.Proofs.map_option_bst; auto.
      apply Raw.Proofs.map_option_find; auto.
      apply Raw.Proofs.map_option_find; auto.
      apply is_bst. apply is_bst.
    Qed.

  End MAP2.
  
  Implicit Arguments map2i [elt elt' elt''].

End FMapAVLPlus.