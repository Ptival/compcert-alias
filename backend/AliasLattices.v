Require Import Lattice.

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
    intros. destruct x, y. inversion_clear H. constructor.
    apply A.eq_sym. auto.
    apply B.eq_sym. auto.
  Qed.

  Theorem eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    intros. destruct x, y, z. inversion_clear H. inversion_clear H0.
    constructor.
    eapply A.eq_trans; eauto.
    eapply B.eq_trans; eauto.
  Qed.

  Definition beq (x y: t) :=
    let (a, b) := x in let (c, d) := y in
    ((A.beq a c) && (B.beq b d))%bool.

  Theorem beq_correct: forall x y, beq x y = true -> eq x y.
  Proof.
    intros. destruct x, y. apply andb_prop in H. destruct H as [? ?].
    constructor.
    apply A.beq_correct. auto.
    apply B.beq_correct. auto.
  Qed.

  Definition ge (x y: t) :=
    let (a, b) := x in let (c, d) := y in
    A.ge a c /\ B.ge b d.

  Theorem ge_refl: forall x y, eq x y -> ge x y.
  Proof.
    intros. destruct x, y. inversion_clear H. constructor.
    apply A.ge_refl. auto.
    apply B.ge_refl. auto.
  Qed.

  Theorem ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof.
    intros. destruct x, y, z. inversion_clear H. inversion_clear H0.
    constructor.
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