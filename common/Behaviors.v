(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Whole-program behaviors *)

Require Import Classical.
Require Import ClassicalEpsilon.
Require Import Coqlib.
Require Import AST.
Require Import Events.
Require Import Globalenvs.
Require Import Integers.
Require Import Smallstep.

Set Implicit Arguments.

(** * Behaviors for program executions *)

(** The four possible outcomes for the execution of a program:
- Termination, with a finite trace of observable events
  and an integer value that stands for the process exit code
  (the return value of the main function).
- Divergence with a finite trace of observable events.
  (At some point, the program runs forever without doing any I/O.)
- Reactive divergence with an infinite trace of observable events.
  (The program performs infinitely many I/O operations separated
   by finite amounts of internal computations.)
- Going wrong, with a finite trace of observable events
  performed before the program gets stuck.
*)

Inductive program_behavior: Type :=
  | Terminates: trace -> int -> program_behavior
  | Diverges: trace -> program_behavior
  | Reacts: traceinf -> program_behavior
  | Goes_wrong: trace -> program_behavior.

(** Operations and relations on behaviors *)

Definition not_wrong (beh: program_behavior) : Prop :=
  match beh with
  | Terminates _ _ => True
  | Diverges _ => True
  | Reacts _ => True
  | Goes_wrong _ => False
  end.

Definition behavior_app (t: trace) (beh: program_behavior): program_behavior :=
  match beh with
  | Terminates t1 r => Terminates (t ** t1) r
  | Diverges t1 => Diverges (t ** t1)
  | Reacts T => Reacts (t *** T)
  | Goes_wrong t1 => Goes_wrong (t ** t1)
  end.

Lemma behavior_app_assoc:
  forall t1 t2 beh,
  behavior_app (t1 ** t2) beh = behavior_app t1 (behavior_app t2 beh).
Proof.
  intros. destruct beh; simpl; f_equal; traceEq. 
Qed.

Lemma behavior_app_E0:
  forall beh, behavior_app E0 beh = beh.
Proof.
  destruct beh; auto.
Qed.

Definition behavior_prefix (t: trace) (beh: program_behavior) : Prop :=
  exists beh', beh = behavior_app t beh'.

Definition behavior_improves (beh1 beh2: program_behavior) : Prop :=
  beh1 = beh2 \/ exists t, beh1 = Goes_wrong t /\ behavior_prefix t beh2.

Lemma behavior_improves_refl:
  forall beh, behavior_improves beh beh.
Proof.
  intros; red; auto.
Qed.

Lemma behavior_improves_trans:
  forall beh1 beh2 beh3, 
  behavior_improves beh1 beh2 -> behavior_improves beh2 beh3 ->
  behavior_improves beh1 beh3.
Proof.
  intros. red. destruct H; destruct H0; subst; auto. 
  destruct H as [t1 [EQ1 [beh2' EQ1']]].
  destruct H0 as [t2 [EQ2 [beh3' EQ2']]].
  subst. destruct beh2'; simpl in EQ2; try discriminate. inv EQ2. 
  right. exists t1; split; auto. exists (behavior_app t beh3'). apply behavior_app_assoc.
Qed.

Lemma behavior_improves_bot:
  forall beh, behavior_improves (Goes_wrong E0) beh.
Proof.
  intros. right. exists E0; split; auto. exists beh. rewrite behavior_app_E0; auto.
Qed.

Lemma behavior_improves_app:
  forall t beh1 beh2,
  behavior_improves beh1 beh2 ->
  behavior_improves (behavior_app t beh1) (behavior_app t beh2).
Proof.
  intros. red; destruct H. left; congruence. 
  destruct H as [t' [A [beh' B]]]. subst.
  right; exists (t ** t'); split; auto. exists beh'. rewrite behavior_app_assoc; auto.
Qed.

(** Associating behaviors to programs. *)

Section PROGRAM_BEHAVIORS.

Variable L: semantics.
Variable ge: globalenv L.  

Inductive state_behaves (s: state L): program_behavior -> Prop :=
  | state_terminates: forall t s' r,
      star L ge s t s' ->
      final_state L s' r ->
      state_behaves s (Terminates t r)
  | state_diverges: forall t s',
      star L ge s t s' -> forever_silent L ge s' ->
      state_behaves s (Diverges t)
  | state_reacts: forall T,
      forever_reactive L ge s T ->
      state_behaves s (Reacts T)
  | state_goes_wrong: forall t s',
      star L ge s t s' ->
      nostep L ge s' ->
      (forall r, ~final_state L s' r) ->
      state_behaves s (Goes_wrong t).

Inductive program_behaves: program_behavior -> Prop :=
  | program_runs: forall s beh,
      initial_state L s -> state_behaves s beh ->
      program_behaves beh
  | program_goes_initially_wrong:
      (forall s, ~initial_state L s) ->
      program_behaves (Goes_wrong E0).

Lemma state_behaves_app:
  forall s1 t s2 beh,
  star L ge s1 t s2 -> state_behaves s2 beh -> state_behaves s1 (behavior_app t beh).
Proof.
  intros. inv H0; simpl; econstructor; eauto; try (eapply star_trans; eauto). 
  eapply star_forever_reactive; eauto.
Qed.

(** * Existence of behaviors *)

(** We now show that any program admits at least one behavior.
  The proof requires classical logic: the axiom of excluded middle
  and an axiom of description. *)

(** The most difficult part of the proof is to show the existence
  of an infinite trace in the case of reactive divergence. *)

Section TRACEINF_REACTS.

Variable s0: state L.

Hypothesis reacts:
  forall s1 t1, star L ge s0 t1 s1 ->
  exists s2, exists t2, star L ge s1 t2 s2 /\ t2 <> E0.

Lemma reacts':
  forall s1 t1, star L ge s0 t1 s1 ->
  { s2 : state L & { t2 : trace | star L ge s1 t2 s2 /\ t2 <> E0 } }.
Proof.
  intros. 
  destruct (constructive_indefinite_description _ (reacts H)) as [s2 A].
  destruct (constructive_indefinite_description _ A) as [t2 [B C]].
  exists s2; exists t2; auto.
Qed.

CoFixpoint build_traceinf' (s1: state L) (t1: trace) (ST: star L ge s0 t1 s1) : traceinf' :=
  match reacts' ST with
  | existT s2 (exist t2 (conj A B)) =>
      Econsinf' t2 
                (build_traceinf' (star_trans ST A (refl_equal _)))
                B
  end.

Lemma reacts_forever_reactive_rec:
  forall s1 t1 (ST: star L ge s0 t1 s1),
  forever_reactive L ge s1 (traceinf_of_traceinf' (build_traceinf' ST)).
Proof.
  cofix COINDHYP; intros.
  rewrite (unroll_traceinf' (build_traceinf' ST)). simpl. 
  destruct (reacts' ST) as [s2 [t2 [A B]]]. 
  rewrite traceinf_traceinf'_app. 
  econstructor. eexact A. auto. apply COINDHYP. 
Qed.

Lemma reacts_forever_reactive:
  exists T, forever_reactive L ge s0 T.
Proof.
  exists (traceinf_of_traceinf' (build_traceinf' (star_refl L ge s0))).
  apply reacts_forever_reactive_rec.
Qed.

End TRACEINF_REACTS.

Lemma diverges_forever_silent:
  forall s0,
  (forall s1 t1, star L ge s0 t1 s1 -> exists s2, L ge s1 E0 s2) ->
  forever_silent L ge s0.
Proof.
  cofix COINDHYP; intros. 
  destruct (H s0 E0) as [s1 ST]. constructor. 
  econstructor. eexact ST. apply COINDHYP. 
  intros. eapply H. eapply star_left; eauto.
Qed.

Lemma state_behaves_exists:
  forall s, exists beh, state_behaves s beh.
Proof.
  intros s0.
  destruct (classic (forall s1 t1, star L ge s0 t1 s1 -> exists s2, exists t2, L ge s1 t2 s2)).
(* 1 Divergence (silent or reactive) *)
  destruct (classic (exists s1, exists t1, star L ge s0 t1 s1 /\
                       (forall s2 t2, star L ge s1 t2 s2 ->
                        exists s3, L ge s2 E0 s3))).
(* 1.1 Silent divergence *)
  destruct H0 as [s1 [t1 [A B]]].
  exists (Diverges t1); econstructor; eauto. 
  apply diverges_forever_silent; auto.
(* 1.2 Reactive divergence *)
  destruct (@reacts_forever_reactive s0) as [T FR].
  intros.
  generalize (not_ex_all_not _ _ H0 s1). intro A; clear H0.
  generalize (not_ex_all_not _ _ A t1). intro B; clear A.
  destruct (not_and_or _ _ B). contradiction. 
  destruct (not_all_ex_not _ _ H0) as [s2 C]; clear H0. 
  destruct (not_all_ex_not _ _ C) as [t2 D]; clear C.
  destruct (imply_to_and _ _ D) as [E F]; clear D.
  destruct (H s2 (t1 ** t2)) as [s3 [t3 G]]. eapply star_trans; eauto. 
  exists s3; exists (t2 ** t3); split.
  eapply star_right; eauto. 
  red; intros. destruct (app_eq_nil t2 t3 H0). subst. elim F. exists s3; auto.
  exists (Reacts T); econstructor; eauto.
(* 2 Termination (normal or by going wrong) *)
  destruct (not_all_ex_not _ _ H) as [s1 A]; clear H.
  destruct (not_all_ex_not _ _ A) as [t1 B]; clear A.
  destruct (imply_to_and _ _ B) as [C D]; clear B.
  destruct (classic (exists r, final_state L s1 r)) as [[r FINAL] | NOTFINAL].
(* 2.1 Normal termination *)
  exists (Terminates t1 r); econstructor; eauto.
(* 2.2 Going wrong *)
  exists (Goes_wrong t1); econstructor; eauto. red. intros. 
  generalize (not_ex_all_not _ _ D s'); intros. 
  generalize (not_ex_all_not _ _ H t); intros. 
  auto.
Qed.

Theorem program_behaves_exists:
  exists beh, program_behaves beh.
Proof.
  destruct (classic (exists s, initial_state L s)) as [[s0 INIT] | NOTINIT].
(* 1. Initial state is defined. *)
  destruct (state_behaves_exists s0) as [beh SB].
  exists beh; econstructor; eauto. 
(* 2. Initial state is undefined *)
  exists (Goes_wrong E0). apply program_goes_initially_wrong. 
  intros. eapply not_ex_all_not; eauto. 
Qed.

End PROGRAM_BEHAVIORS.

Implicit Arguments state_behaves [].
Implicit Arguments program_behaves [].

(** * Forward simulations and program behaviors *)

Section FORWARD_SIMULATIONS.

Variable L1: semantics.
Variable L2: semantics.
Variable ge1: globalenv L1.
Variable ge2: globalenv L2.
Variable S: forward_simulation L1 L2 ge1 ge2.

Lemma forward_simulation_state_behaves:
  forall i s1 s2 beh1,
  S i s1 s2 -> state_behaves L1 ge1 s1 beh1 ->
  exists beh2, state_behaves L2 ge2 s2 beh2 /\ behavior_improves beh1 beh2.
Proof.
  intros. inv H0. 
(* termination *)
  exploit simulation_star; eauto. intros [i' [s2' [A B]]].
  exists (Terminates t r); split.
  econstructor; eauto. eapply fsim_match_final_states; eauto.
  apply behavior_improves_refl.
(* silent divergence *)
  exploit simulation_star; eauto. intros [i' [s2' [A B]]].
  exists (Diverges t); split.
  econstructor; eauto. eapply simulation_forever_silent; eauto.
  apply behavior_improves_refl.
(* reactive divergence *)
  exists (Reacts T); split.
  econstructor. eapply simulation_forever_reactive; eauto.
  apply behavior_improves_refl.
(* going wrong *)
  exploit simulation_star; eauto. intros [i' [s2' [A B]]].
  destruct (state_behaves_exists ge2 s2') as [beh' SB].
  exists (behavior_app t beh'); split. 
  eapply state_behaves_app; eauto. 
  replace (Goes_wrong t) with (behavior_app t (Goes_wrong E0)).
  apply behavior_improves_app. apply behavior_improves_bot. 
  simpl. decEq. traceEq.
Qed.

Theorem forward_simulation_behavior_improves:
  forall beh1, program_behaves L1 ge1 beh1 ->
  exists beh2, program_behaves L2 ge2 beh2 /\ behavior_improves beh1 beh2.
Proof.
  intros. inv H.
(* initial state defined *)
  exploit (fsim_match_initial_states S); eauto. intros [i [s' [INIT MATCH]]].
  exploit forward_simulation_state_behaves; eauto. intros [beh2 [A B]].
  exists beh2; split; auto. econstructor; eauto.
(* initial state undefined *)
  destruct (classic (exists s', initial_state L2 s')).
  destruct H as [s' INIT]. 
  destruct (state_behaves_exists ge2 s') as [beh' SB].
  exists beh'; split. econstructor; eauto. apply behavior_improves_bot.
  exists (Goes_wrong E0); split.
  apply program_goes_initially_wrong. 
  intros; red; intros. elim H; exists s; auto.
  apply behavior_improves_refl.
Qed.

Corollary forward_simulation_same_safe_behavior:
  forall beh,
  program_behaves L1 ge1 beh -> not_wrong beh ->
  program_behaves L2 ge2 beh.
Proof.
  intros. exploit forward_simulation_behavior_improves; eauto. 
  intros [beh' [A B]]. destruct B. 
  congruence.
  destruct H1 as [t [C D]]. subst. contradiction.
Qed.

End FORWARD_SIMULATIONS.

(** * Backward simulations and program behaviors *)

Section BACKWARD_SIMULATIONS.

Variable L1: semantics.
Variable L2: semantics.
Variable ge1: globalenv L1.
Variable ge2: globalenv L2.
Variable S: backward_simulation L1 L2 ge1 ge2.

Definition safe_along_behavior (s: state L1) (b: program_behavior) : Prop :=
  forall t1 s' b2, star L1 ge1 s t1 s' -> b = behavior_app t1 b2 ->
     (exists r, final_state L1 s' r)
  \/ (exists t2, exists s'', L1 ge1 s' t2 s'').

Remark safe_along_safe:
  forall s b, safe_along_behavior s b -> safe L1 ge1 s.
Proof.
  intros; red; intros. eapply H; eauto. symmetry; apply behavior_app_E0. 
Qed.

Remark star_safe_along:
  forall s b t1 s' b2,
  safe_along_behavior s b ->
  star L1 ge1 s t1 s' -> b = behavior_app t1 b2 ->
  safe_along_behavior s' b2.
Proof.
  intros; red; intros. eapply H. eapply star_trans; eauto.
  subst. rewrite behavior_app_assoc. eauto.
Qed.

Remark not_safe_along_behavior:
  forall s b,
  ~ safe_along_behavior s b ->
  exists t, exists s',
    behavior_prefix t b /\ star L1 ge1 s t s' /\ nostep L1 ge1 s' /\ (forall r, ~(final_state L1 s' r)).
Proof.
  intros. 
  destruct (not_all_ex_not _ _ H) as [t1 A]; clear H.
  destruct (not_all_ex_not _ _ A) as [s' B]; clear A.
  destruct (not_all_ex_not _ _ B) as [b2 C]; clear B.
  destruct (imply_to_and _ _ C) as [D E]; clear C.
  destruct (imply_to_and _ _ E) as [F G]; clear E.
  destruct (not_or_and _ _ G) as [P Q]; clear G.
  exists t1; exists s'. 
  split. exists b2; auto. 
  split. auto. 
  split. red; intros; red; intros. elim Q. exists t; exists s'0; auto.
  intros; red; intros. elim P. exists r; auto.
Qed.

Lemma backward_simulation_star:
  forall s2 t s2', star L2 ge2 s2 t s2' ->
  forall i s1 b, S i s1 s2 -> safe_along_behavior s1 (behavior_app t b) ->
  exists i', exists s1', star L1 ge1 s1 t s1' /\ S i' s1' s2'.
Proof.
  induction 1; intros.
  exists i; exists s1; split; auto. apply star_refl.
  exploit (bsim_simulation S); eauto. eapply safe_along_safe; eauto. 
  intros [i' [s1' [A B]]].
  assert (star L1 ge1 s0 t1 s1'). intuition. apply plus_star; auto.
  exploit IHstar; eauto. eapply star_safe_along; eauto.
  subst t; apply behavior_app_assoc.
  intros [i'' [s2'' [C D]]].
  exists i''; exists s2''; split; auto. eapply star_trans; eauto.
Qed.

Lemma backward_simulation_forever_silent:
  forall i s1 s2,
  forever_silent L2 ge2 s2 -> S i s1 s2 -> safe L1 ge1 s1 ->
  forever_silent L1 ge1 s1.
Proof.
  assert (forall i s1 s2,
         forever_silent L2 ge2 s2 -> S i s1 s2 -> safe L1 ge1 s1 ->
         forever_silent_N L1 (bsim_order S) ge1 i s1).
    cofix COINDHYP; intros.
    inv H.  destruct (bsim_simulation S _ _ _ H2 _ H0 H1) as [i' [s2' [A B]]].
    destruct A as [C | [C D]].
    eapply forever_silent_N_plus; eauto. eapply COINDHYP; eauto.
      eapply star_safe; eauto. apply plus_star; auto.
    eapply forever_silent_N_star; eauto. eapply COINDHYP; eauto.
      eapply star_safe; eauto.
  intros. eapply forever_silent_N_forever; eauto. apply bsim_order_wf.
Qed.

Lemma backward_simulation_forever_reactive:
  forall i s1 s2 T,
  forever_reactive L2 ge2 s2 T -> S i s1 s2 -> safe_along_behavior s1 (Reacts T) ->
  forever_reactive L1 ge1 s1 T.
Proof.
  cofix COINDHYP; intros. inv H. 
  destruct (backward_simulation_star H2 _ (Reacts T0) H0) as [i' [s1' [A B]]]; eauto.
  econstructor; eauto. eapply COINDHYP; eauto. eapply star_safe_along; eauto. 
Qed.

Lemma backward_simulation_state_behaves:
  forall i s1 s2 beh2,
  S i s1 s2 -> state_behaves L2 ge2 s2 beh2 ->
  exists beh1, state_behaves L1 ge1 s1 beh1 /\ behavior_improves beh1 beh2.
Proof.
  intros. destruct (classic (safe_along_behavior s1 beh2)).
(* 1. Safe along *)
  exists beh2; split; [idtac|apply behavior_improves_refl].
  inv H0. 
(* termination *)
  assert (Terminates t r = behavior_app t (Terminates E0 r)).
    simpl. rewrite E0_right; auto.
  rewrite H0 in H1. 
  exploit backward_simulation_star; eauto.
  intros [i' [s1' [A B]]].
  exploit (bsim_match_final_states S); eauto.
    eapply safe_along_safe. eapply star_safe_along; eauto. 
  intros [s1'' [C D]].
  econstructor. eapply star_trans; eauto. traceEq. auto.
(* silent divergence *)
  assert (Diverges t = behavior_app t (Diverges E0)).
    simpl. rewrite E0_right; auto.
  rewrite H0 in H1. 
  exploit backward_simulation_star; eauto.
  intros [i' [s1' [A B]]].
  econstructor. eauto. eapply backward_simulation_forever_silent; eauto. 
  eapply safe_along_safe. eapply star_safe_along; eauto. 
(* reactive divergence *)
  econstructor. eapply backward_simulation_forever_reactive; eauto. 
(* goes wrong *)
  assert (Goes_wrong t = behavior_app t (Goes_wrong E0)).
    simpl. rewrite E0_right; auto.
  rewrite H0 in H1. 
  exploit backward_simulation_star; eauto.
  intros [i' [s1' [A B]]].
  exploit (bsim_progress S); eauto. eapply safe_along_safe. eapply star_safe_along; eauto. 
  intros [[r FIN] | [t' [s2' STEP2]]]. 
  elim (H4 _ FIN).
  elim (H3 _ _ STEP2).

(* 2. Not safe along *)
  exploit not_safe_along_behavior; eauto. 
  intros [t [s1' [PREF [STEPS [NOSTEP NOFIN]]]]].
  exists (Goes_wrong t); split.
  econstructor; eauto. 
  right. exists t; auto.
Qed.

Theorem backward_simulation_behavior_improves:
  forall beh2, program_behaves L2 ge2 beh2 ->
  exists beh1, program_behaves L1 ge1 beh1 /\ behavior_improves beh1 beh2.
Proof.
  intros. inv H.
(* L2's initial state is defined. *)
  destruct (classic (exists s1, initial_state L1 s1)) as [[s1 INIT] | NOINIT].
(* L1's initial state is defined too. *)
  exploit (bsim_match_initial_states S); eauto. intros [i [s1' [INIT1' MATCH]]].
  exploit backward_simulation_state_behaves; eauto. intros [beh1 [A B]].
  exists beh1; split; auto. econstructor; eauto.
(* L1 has no initial state *)
  exists (Goes_wrong E0); split.
  apply program_goes_initially_wrong. 
  intros; red; intros. elim NOINIT; exists s0; auto.
  apply behavior_improves_bot.
(* L2 has no initial state *)
  exists (Goes_wrong E0); split.
  apply program_goes_initially_wrong. 
  intros; red; intros.
  exploit (bsim_initial_states_exist S); eauto. intros [s2 INIT2]. 
  elim (H0 s2); auto.
  apply behavior_improves_refl.
Qed.

Corollary backward_simulation_same_safe_behavior:
  (forall beh, program_behaves L1 ge1 beh -> not_wrong beh) ->
  (forall beh, program_behaves L2 ge2 beh -> program_behaves L1 ge1 beh).
Proof.
  intros. exploit backward_simulation_behavior_improves; eauto. 
  intros [beh' [A B]]. destruct B. 
  congruence.
  destruct H1 as [t [C D]]. subst. elim (H (Goes_wrong t)). auto.
Qed.

End BACKWARD_SIMULATIONS.

(** * Additional results about infinite reduction sequences *)

(** We now show that any infinite sequence of reductions is either of
  the "reactive" kind or of the "silent" kind (after a finite number
  of non-silent transitions).  The proof necessitates the axiom of
  excluded middle.  This result is used in [Csem] and [Cminor] to
  relate the coinductive big-step semantics for divergence with the
  small-step notions of divergence. *)

Unset Implicit Arguments.

Section INF_SEQ_DECOMP.

Variable genv: Type.
Variable state: Type.
Variable step: genv -> state -> trace -> state -> Prop.

Variable ge: genv.

Inductive State: Type :=
  ST: forall (s: state) (T: traceinf), forever step ge s T -> State.

Definition state_of_State (S: State): state :=
  match S with ST s T F => s end.
Definition traceinf_of_State (S: State) : traceinf :=
  match S with ST s T F => T end.

Inductive Step: trace -> State -> State -> Prop :=
  | Step_intro: forall s1 t T s2 S F,
      Step t (ST s1 (t *** T) (@forever_intro genv state step ge s1 t s2 T S F))
             (ST s2 T F).

Inductive Steps: State -> State -> Prop :=
  | Steps_refl: forall S, Steps S S
  | Steps_left: forall t S1 S2 S3, Step t S1 S2 -> Steps S2 S3 -> Steps S1 S3.

Remark Steps_trans:
  forall S1 S2, Steps S1 S2 -> forall S3, Steps S2 S3 -> Steps S1 S3.
Proof.
  induction 1; intros. auto. econstructor; eauto.
Qed.

Let Reactive (S: State) : Prop :=
  forall S1, 
  Steps S S1 ->
  exists S2, exists S3, exists t, Steps S1 S2 /\ Step t S2 S3 /\ t <> E0.

Let Silent (S: State) : Prop :=
  forall S1 t S2, Steps S S1 -> Step t S1 S2 -> t = E0.

Lemma Reactive_or_Silent:
  forall S, Reactive S \/ (exists S', Steps S S' /\ Silent S').
Proof.
  intros. destruct (classic (exists S', Steps S S' /\ Silent S')).
  auto.
  left. red; intros. 
  generalize (not_ex_all_not _ _ H S1). intros.
  destruct (not_and_or _ _ H1). contradiction. 
  unfold Silent in H2. 
  generalize (not_all_ex_not _ _ H2). intros [S2 A].
  generalize (not_all_ex_not _ _ A). intros [t B].
  generalize (not_all_ex_not _ _ B). intros [S3 C].
  generalize (imply_to_and _ _ C). intros [D F].
  generalize (imply_to_and _ _ F). intros [G J].
  exists S2; exists S3; exists t. auto.  
Qed.

Lemma Steps_star:
  forall S1 S2, Steps S1 S2 ->
  exists t, star step ge (state_of_State S1) t (state_of_State S2)
         /\ traceinf_of_State S1 = t *** traceinf_of_State S2.
Proof.
  induction 1.
  exists E0; split. apply star_refl. auto.
  inv H. destruct IHSteps as [t' [A B]].
  exists (t ** t'); split.
  simpl; eapply star_left; eauto.
  simpl in *. subst T. traceEq.
Qed.

Lemma Silent_forever_silent:
  forall S,
  Silent S -> forever_silent step ge (state_of_State S).
Proof.
  cofix COINDHYP; intro S. case S. intros until f. simpl. case f. intros.
  assert (Step t (ST s1 (t *** T0) (forever_intro s1 t s0 f0))
                 (ST s2 T0 f0)). 
    constructor.
  assert (t = E0). 
    red in H. eapply H; eauto. apply Steps_refl.
  apply forever_silent_intro with (state_of_State (ST s2 T0 f0)).
  rewrite <- H1. assumption. 
  apply COINDHYP. 
  red; intros. eapply H. eapply Steps_left; eauto. eauto. 
Qed.

Lemma Reactive_forever_reactive:
  forall S,
  Reactive S -> forever_reactive step ge (state_of_State S) (traceinf_of_State S).
Proof.
  cofix COINDHYP; intros.
  destruct (H S) as [S1 [S2 [t [A [B C]]]]]. apply Steps_refl. 
  destruct (Steps_star _ _ A) as [t' [P Q]].
  inv B. simpl in *. rewrite Q. rewrite <- Eappinf_assoc. 
  apply forever_reactive_intro with s2. 
  eapply star_right; eauto. 
  red; intros. destruct (Eapp_E0_inv _ _ H0). contradiction.
  change (forever_reactive step ge (state_of_State (ST s2 T F)) (traceinf_of_State (ST s2 T F))).
  apply COINDHYP. 
  red; intros. apply H.
  eapply Steps_trans. eauto.
  eapply Steps_left. constructor. eauto.
Qed.

Theorem forever_silent_or_reactive:
  forall s T,
  forever step ge s T ->
  forever_reactive step ge s T \/
  exists t, exists s', exists T',
  star step ge s t s' /\ forever_silent step ge s' /\ T = t *** T'.
Proof.
  intros. 
  destruct (Reactive_or_Silent (ST s T H)).
  left. 
  change (forever_reactive step ge (state_of_State (ST s T H)) (traceinf_of_State (ST s T H))).
  apply Reactive_forever_reactive. auto.
  destruct H0 as [S' [A B]].
  exploit Steps_star; eauto. intros [t [C D]]. simpl in *.
  right. exists t; exists (state_of_State S'); exists (traceinf_of_State S').
  split. auto. 
  split. apply Silent_forever_silent. auto.
  auto.
Qed.

End INF_SEQ_DECOMP.

