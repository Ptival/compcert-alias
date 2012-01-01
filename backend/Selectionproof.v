(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness of instruction selection *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Cminor.
Require Import Op.
Require Import CminorSel.
Require Import SelectOp.
Require Import Selection.
Require Import SelectOpproof.

Open Local Scope cminorsel_scope.

(** * Correctness of the instruction selection functions for expressions *)

Section CMCONSTR.

Variable ge: genv.
Variable sp: val.
Variable e: env.
Variable m: mem.

(** Conversion of condition expressions. *)

Lemma negate_condexpr_correct:
  forall le a b,
  eval_condexpr ge sp e m le a b ->
  eval_condexpr ge sp e m le (negate_condexpr a) (negb b).
Proof.
  induction 1; simpl.
  constructor.
  constructor.
  econstructor. eauto. apply eval_negate_condition. auto.
  econstructor. eauto. destruct vb1; auto.
Qed. 

Scheme expr_ind2 := Induction for expr Sort Prop
  with exprlist_ind2 := Induction for exprlist Sort Prop.

Fixpoint forall_exprlist (P: expr -> Prop) (el: exprlist) {struct el}: Prop :=
  match el with
  | Enil => True
  | Econs e el' => P e /\ forall_exprlist P el'
  end.

Lemma expr_induction_principle:
  forall (P: expr -> Prop),
  (forall i : ident, P (Evar i)) ->
  (forall (o : operation) (e : exprlist),
     forall_exprlist P e -> P (Eop o e)) ->
  (forall (m : memory_chunk) (a : Op.addressing) (e : exprlist),
     forall_exprlist P e -> P (Eload m a e)) ->
  (forall (c : condexpr) (e : expr),
     P e -> forall e0 : expr, P e0 -> P (Econdition c e e0)) ->
  (forall e : expr, P e -> forall e0 : expr, P e0 -> P (Elet e e0)) ->
  (forall n : nat, P (Eletvar n)) ->
  forall e : expr, P e.
Proof.
  intros. apply expr_ind2 with (P := P) (P0 := forall_exprlist P); auto.
  simpl. auto.
  intros. simpl. auto.
Qed.

Lemma eval_base_condition_of_expr:
  forall le a v b,
  eval_expr ge sp e m le a v ->
  Val.bool_of_val v b ->
  eval_condexpr ge sp e m le 
                (CEcond (Ccompuimm Cne Int.zero) (a ::: Enil))
                b.
Proof.
  intros. 
  eapply eval_CEcond. eauto with evalexpr. 
  inversion H0; simpl. rewrite Int.eq_false; auto. auto. auto.
Qed.

Lemma is_compare_neq_zero_correct:
  forall c v b,
  is_compare_neq_zero c = true ->
  eval_condition c (v :: nil) m = Some b ->
  Val.bool_of_val v b.
Proof.
  intros.
  destruct c; simpl in H; try discriminate;
  destruct c; simpl in H; try discriminate;
  generalize (Int.eq_spec i Int.zero); rewrite H; intro; subst i.

  simpl in H0. destruct v; inv H0. 
  generalize (Int.eq_spec i Int.zero). destruct (Int.eq i Int.zero); intros; simpl.
  subst i; constructor. constructor; auto.

  simpl in H0. destruct v; inv H0. 
  generalize (Int.eq_spec i Int.zero). destruct (Int.eq i Int.zero); intros; simpl.
  subst i; constructor. constructor; auto.
  constructor.
Qed.

Lemma is_compare_eq_zero_correct:
  forall c v b,
  is_compare_eq_zero c = true ->
  eval_condition c (v :: nil) m = Some b ->
  Val.bool_of_val v (negb b).
Proof.
  intros. apply is_compare_neq_zero_correct with (negate_condition c).
  destruct c; simpl in H; simpl; try discriminate;
  destruct c; simpl; try discriminate; auto.
  apply eval_negate_condition; auto.
Qed.

Lemma eval_condition_of_expr:
  forall a le v b,
  eval_expr ge sp e m le a v ->
  Val.bool_of_val v b ->
  eval_condexpr ge sp e m le (condexpr_of_expr a) b.
Proof.
  intro a0; pattern a0.
  apply expr_induction_principle; simpl; intros;
    try (eapply eval_base_condition_of_expr; eauto; fail).
  
  destruct o; try (eapply eval_base_condition_of_expr; eauto; fail).

  destruct e0. inv H0. inv H5. simpl in H7. inv H7.  
  inversion H1. 
  rewrite Int.eq_false; auto. constructor.
  subst i; rewrite Int.eq_true. constructor.
  eapply eval_base_condition_of_expr; eauto.

  inv H0. simpl in H7.
  assert (eval_condition c vl m = Some b).
    destruct (eval_condition c vl m).
    destruct b0; inv H7; inversion H1; congruence.
    inv H7. inv H1.
  assert (eval_condexpr ge sp e m le (CEcond c e0) b).
    eapply eval_CEcond; eauto.
  destruct e0; auto. destruct e1; auto.
  simpl in H. destruct H.
  inv H5. inv H11.

  case_eq (is_compare_neq_zero c); intros.
  eapply H; eauto.
  apply is_compare_neq_zero_correct with c; auto.

  case_eq (is_compare_eq_zero c); intros.
  replace b with (negb (negb b)). apply negate_condexpr_correct.
  eapply H; eauto.
  apply is_compare_eq_zero_correct with c; auto.
  apply negb_involutive.

  auto.

  inv H1. destruct v1; eauto with evalexpr.
Qed.

Lemma eval_load:
  forall le a v chunk v',
  eval_expr ge sp e m le a v ->
  Mem.loadv chunk m v = Some v' ->
  eval_expr ge sp e m le (load chunk a) v'.
Proof.
  intros. generalize H0; destruct v; simpl; intro; try discriminate.
  unfold load. 
  generalize (eval_addressing _ _ _ _ _ chunk _ _ _ _ H (refl_equal _)).
  destruct (addressing chunk a). intros [vl [EV EQ]]. 
  eapply eval_Eload; eauto. 
Qed.

Lemma eval_store:
  forall chunk a1 a2 v1 v2 f k m',
  eval_expr ge sp e m nil a1 v1 ->
  eval_expr ge sp e m nil a2 v2 ->
  Mem.storev chunk m v1 v2 = Some m' ->
  step ge (State f (store chunk a1 a2) k sp e m)
       E0 (State f Sskip k sp e m').
Proof.
  intros. generalize H1; destruct v1; simpl; intro; try discriminate.
  unfold store.
  generalize (eval_addressing _ _ _ _ _ chunk _ _ _ _ H (refl_equal _)).
  destruct (addressing chunk a1). intros [vl [EV EQ]]. 
  eapply step_store; eauto. 
Qed.

(** Correctness of instruction selection for operators *)

Lemma eval_sel_unop:
  forall le op a1 v1 v,
  eval_expr ge sp e m le a1 v1 ->
  eval_unop op v1 = Some v ->
  exists v', eval_expr ge sp e m le (sel_unop op a1) v' /\ Val.lessdef v v'.
Proof.
  destruct op; simpl; intros; FuncInv; try subst v.
  apply eval_cast8unsigned; auto.
  apply eval_cast8signed; auto.
  apply eval_cast16unsigned; auto.
  apply eval_cast16signed; auto.
  apply eval_negint; auto.
  apply eval_notbool; auto.
  apply eval_notint; auto.
  apply eval_negf; auto.
  apply eval_absf; auto.
  apply eval_singleoffloat; auto.
  eapply eval_intoffloat; eauto.
  eapply eval_intuoffloat; eauto.
  eapply eval_floatofint; eauto.
  eapply eval_floatofintu; eauto.
Qed.

Lemma eval_sel_binop:
  forall le op a1 a2 v1 v2 v,
  eval_expr ge sp e m le a1 v1 ->
  eval_expr ge sp e m le a2 v2 ->
  eval_binop op v1 v2 m = Some v ->
  exists v', eval_expr ge sp e m le (sel_binop op a1 a2) v' /\ Val.lessdef v v'.
Proof.
  destruct op; simpl; intros; FuncInv; try subst v.
  apply eval_add; auto.
  apply eval_sub; auto.
  apply eval_mul; auto.
  eapply eval_divs; eauto.
  eapply eval_divu; eauto.
  eapply eval_mods; eauto.
  eapply eval_modu; eauto.
  apply eval_and; auto.
  apply eval_or; auto.
  apply eval_xor; auto.
  apply eval_shl; auto.
  apply eval_shr; auto.
  apply eval_shru; auto.
  apply eval_addf; auto.
  apply eval_subf; auto.
  apply eval_mulf; auto.
  apply eval_divf; auto.
  apply eval_comp; auto.
  apply eval_compu; auto.
  apply eval_compf; auto.
Qed.

End CMCONSTR.

(** Recognition of calls to built-in functions *)

Lemma expr_is_addrof_ident_correct:
  forall e id,
  expr_is_addrof_ident e = Some id ->
  e = Cminor.Econst (Cminor.Oaddrsymbol id Int.zero).
Proof.
  intros e id. unfold expr_is_addrof_ident. 
  destruct e; try congruence.
  destruct c; try congruence.
  predSpec Int.eq Int.eq_spec i0 Int.zero; congruence.
Qed.

Lemma expr_is_addrof_builtin_correct:
  forall ge sp e m a v ef fd,
  expr_is_addrof_builtin ge a = Some ef ->
  Cminor.eval_expr ge sp e m a v ->
  Genv.find_funct ge v = Some fd ->
  fd = External ef.
Proof.
  intros until fd; unfold expr_is_addrof_builtin.
  case_eq (expr_is_addrof_ident a); intros; try congruence.
  exploit expr_is_addrof_ident_correct; eauto. intro EQ; subst a.
  inv H1. inv H4. 
  destruct (Genv.find_symbol ge i); try congruence.
  rewrite Genv.find_funct_find_funct_ptr in H2. rewrite H2 in H0. 
  destruct fd; try congruence. 
  destruct (ef_inline e0); congruence.
Qed.

(** Compatibility of evaluation functions with the "less defined than" relation. *)

Ltac TrivialExists :=
  match goal with
  | [ |- exists v, Some ?x = Some v /\ _ ] => exists x; split; auto
  | _ => idtac
  end.

Lemma eval_unop_lessdef:
  forall op v1 v1' v,
  eval_unop op v1 = Some v -> Val.lessdef v1 v1' ->
  exists v', eval_unop op v1' = Some v' /\ Val.lessdef v v'.
Proof.
  intros until v; intros EV LD. inv LD. 
  exists v; auto.
  destruct op; simpl in *; inv EV; TrivialExists.
Qed.

Lemma eval_binop_lessdef:
  forall op v1 v1' v2 v2' v m m',
  eval_binop op v1 v2 m = Some v -> 
  Val.lessdef v1 v1' -> Val.lessdef v2 v2' -> Mem.extends m m' ->
  exists v', eval_binop op v1' v2' m' = Some v' /\ Val.lessdef v v'.
Proof.
  intros until m'; intros EV LD1 LD2 ME.
  assert (exists v', eval_binop op v1' v2' m = Some v' /\ Val.lessdef v v').
  inv LD1. inv LD2. exists v; auto. 
  destruct op; destruct v1'; simpl in *; inv EV; TrivialExists.
  destruct op; simpl in *; inv EV; TrivialExists.
  destruct op; try (exact H). 
  simpl in *. TrivialExists. inv EV. apply Val.of_optbool_lessdef. 
  intros. apply Val.cmpu_bool_lessdef with (Mem.valid_pointer m) v1 v2; auto.
  intros; eapply Mem.valid_pointer_extends; eauto.
Qed.

(** * Semantic preservation for instruction selection. *)

Section PRESERVATION.

Variable prog: Cminor.program.
Let tprog := sel_program prog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

(** Relationship between the global environments for the original
  Cminor program and the generated CminorSel program. *)

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  intros; unfold ge, tge, tprog, sel_program. 
  apply Genv.find_symbol_transf.
Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: Cminor.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  Genv.find_funct_ptr tge b = Some (sel_fundef ge f).
Proof.  
  intros. 
  exact (Genv.find_funct_ptr_transf (sel_fundef ge) _ _ H).
Qed.

Lemma functions_translated:
  forall (v v': val) (f: Cminor.fundef),
  Genv.find_funct ge v = Some f ->
  Val.lessdef v v' ->
  Genv.find_funct tge v' = Some (sel_fundef ge f).
Proof.  
  intros. inv H0.
  exact (Genv.find_funct_transf (sel_fundef ge) _ _ H).
  simpl in H. discriminate.
Qed.

Lemma sig_function_translated:
  forall f,
  funsig (sel_fundef ge f) = Cminor.funsig f.
Proof.
  intros. destruct f; reflexivity.
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros; unfold ge, tge, tprog, sel_program. 
  apply Genv.find_var_info_transf.
Qed.

(** Relationship between the local environments. *)

Definition env_lessdef (e1 e2: env) : Prop :=
  forall id v1, e1!id = Some v1 -> exists v2, e2!id = Some v2 /\ Val.lessdef v1 v2.

Lemma set_var_lessdef:
  forall e1 e2 id v1 v2,
  env_lessdef e1 e2 -> Val.lessdef v1 v2 ->
  env_lessdef (PTree.set id v1 e1) (PTree.set id v2 e2).
Proof.
  intros; red; intros. rewrite PTree.gsspec in *. destruct (peq id0 id).
  exists v2; split; congruence.
  auto.
Qed.

Lemma set_params_lessdef:
  forall il vl1 vl2, 
  Val.lessdef_list vl1 vl2 ->
  env_lessdef (set_params vl1 il) (set_params vl2 il).
Proof.
  induction il; simpl; intros.
  red; intros. rewrite PTree.gempty in H0; congruence.
  inv H; apply set_var_lessdef; auto.
Qed.

Lemma set_locals_lessdef:
  forall e1 e2, env_lessdef e1 e2 ->
  forall il, env_lessdef (set_locals il e1) (set_locals il e2).
Proof.
  induction il; simpl. auto. apply set_var_lessdef; auto.
Qed.

(** Semantic preservation for expressions. *)

Lemma sel_expr_correct:
  forall sp e m a v,
  Cminor.eval_expr ge sp e m a v ->
  forall e' le m',
  env_lessdef e e' -> Mem.extends m m' ->
  exists v', eval_expr tge sp e' m' le (sel_expr a) v' /\ Val.lessdef v v'.
Proof.
  induction 1; intros; simpl.
  (* Evar *)
  exploit H0; eauto. intros [v' [A B]]. exists v'; split; auto. constructor; auto.
  (* Econst *)
  destruct cst; simpl in *; inv H. 
  exists (Vint i); split; auto. econstructor. constructor. auto. 
  exists (Vfloat f); split; auto. econstructor. constructor. auto.
  rewrite <- symbols_preserved. fold (symbol_address tge i i0). apply eval_addrsymbol.
  apply eval_addrstack.
  (* Eunop *)
  exploit IHeval_expr; eauto. intros [v1' [A B]].
  exploit eval_unop_lessdef; eauto. intros [v' [C D]].
  exploit eval_sel_unop; eauto. intros [v'' [E F]].
  exists v''; split; eauto. eapply Val.lessdef_trans; eauto. 
  (* Ebinop *)
  exploit IHeval_expr1; eauto. intros [v1' [A B]].
  exploit IHeval_expr2; eauto. intros [v2' [C D]].
  exploit eval_binop_lessdef; eauto. intros [v' [E F]].
  exploit eval_sel_binop. eexact A. eexact C. eauto. intros [v'' [P Q]].
  exists v''; split; eauto. eapply Val.lessdef_trans; eauto. 
  (* Eload *)
  exploit IHeval_expr; eauto. intros [vaddr' [A B]].
  exploit Mem.loadv_extends; eauto. intros [v' [C D]].
  exists v'; split; auto. eapply eval_load; eauto.
  (* Econdition *)
  exploit IHeval_expr1; eauto. intros [v1' [A B]].
  exploit IHeval_expr2; eauto. intros [v2' [C D]].
  replace (sel_expr (if b1 then a2 else a3)) with (if b1 then sel_expr a2 else sel_expr a3) in C.
  assert (Val.bool_of_val v1' b1). inv B. auto. inv H0.
  exists v2'; split; auto. 
  econstructor; eauto. eapply eval_condition_of_expr; eauto. 
  destruct b1; auto.
Qed.

Lemma sel_exprlist_correct:
  forall sp e m a v,
  Cminor.eval_exprlist ge sp e m a v ->
  forall e' le m',
  env_lessdef e e' -> Mem.extends m m' ->
  exists v', eval_exprlist tge sp e' m' le (sel_exprlist a) v' /\ Val.lessdef_list v v'.
Proof.
  induction 1; intros; simpl. 
  exists (@nil val); split; auto. constructor.
  exploit sel_expr_correct; eauto. intros [v1' [A B]].
  exploit IHeval_exprlist; eauto. intros [vl' [C D]].
  exists (v1' :: vl'); split; auto. constructor; eauto.
Qed.

(** Semantic preservation for functions and statements. *)

Inductive match_cont: Cminor.cont -> CminorSel.cont -> Prop :=
  | match_cont_stop:
      match_cont Cminor.Kstop Kstop
  | match_cont_seq: forall s k k',
      match_cont k k' ->
      match_cont (Cminor.Kseq s k) (Kseq (sel_stmt ge s) k')
  | match_cont_block: forall k k',
      match_cont k k' ->
      match_cont (Cminor.Kblock k) (Kblock k')
  | match_cont_call: forall id f sp e k e' k',
      match_cont k k' -> env_lessdef e e' ->
      match_cont (Cminor.Kcall id f sp e k) (Kcall id (sel_function ge f) sp e' k').

Inductive match_states: Cminor.state -> CminorSel.state -> Prop :=
  | match_state: forall f s k s' k' sp e m e' m',
      s' = sel_stmt ge s ->
      match_cont k k' ->
      env_lessdef e e' ->
      Mem.extends m m' ->
      match_states
        (Cminor.State f s k sp e m)
        (State (sel_function ge f) s' k' sp e' m')
  | match_callstate: forall f args args' k k' m m',
      match_cont k k' ->
      Val.lessdef_list args args' ->
      Mem.extends m m' ->
      match_states
        (Cminor.Callstate f args k m)
        (Callstate (sel_fundef ge f) args' k' m')
  | match_returnstate: forall v v' k k' m m',
      match_cont k k' ->
      Val.lessdef v v' ->
      Mem.extends m m' ->
      match_states
        (Cminor.Returnstate v k m)
        (Returnstate v' k' m')
  | match_builtin_1: forall ef args args' optid f sp e k m al e' k' m',
      match_cont k k' ->
      Val.lessdef_list args args' ->
      env_lessdef e e' ->
      Mem.extends m m' ->
      eval_exprlist tge sp e' m' nil al args' ->
      match_states
        (Cminor.Callstate (External ef) args (Cminor.Kcall optid f sp e k) m)
        (State (sel_function ge f) (Sbuiltin optid ef al) k' sp e' m')
  | match_builtin_2: forall v v' optid f sp e k m e' m' k',
      match_cont k k' ->
      Val.lessdef v v' ->
      env_lessdef e e' ->
      Mem.extends m m' ->
      match_states
        (Cminor.Returnstate v (Cminor.Kcall optid f sp e k) m)
        (State (sel_function ge f) Sskip k' sp (set_optvar optid v' e') m').

Remark call_cont_commut:
  forall k k', match_cont k k' -> match_cont (Cminor.call_cont k) (call_cont k').
Proof.
  induction 1; simpl; auto. constructor. constructor; auto.
Qed.

Remark find_label_commut:
  forall lbl s k k',
  match_cont k k' ->
  match Cminor.find_label lbl s k, find_label lbl (sel_stmt ge s) k' with
  | None, None => True
  | Some(s1, k1), Some(s1', k1') => s1' = sel_stmt ge s1 /\ match_cont k1 k1'
  | _, _ => False
  end.
Proof.
  induction s; intros; simpl; auto.
(* store *)
  unfold store. destruct (addressing m (sel_expr e)); simpl; auto.
(* call *)
  destruct (expr_is_addrof_builtin ge e); simpl; auto.
(* seq *)
  exploit (IHs1 (Cminor.Kseq s2 k)). constructor; eauto. 
  destruct (Cminor.find_label lbl s1 (Cminor.Kseq s2 k)) as [[sx kx] | ];
  destruct (find_label lbl (sel_stmt ge s1) (Kseq (sel_stmt ge s2) k')) as [[sy ky] | ];
  intuition. apply IHs2; auto.
(* ifthenelse *)
  exploit (IHs1 k); eauto. 
  destruct (Cminor.find_label lbl s1 k) as [[sx kx] | ];
  destruct (find_label lbl (sel_stmt ge s1) k') as [[sy ky] | ];
  intuition. apply IHs2; auto.
(* loop *)
  apply IHs. constructor; auto.
(* block *)
  apply IHs. constructor; auto.
(* return *)
  destruct o; simpl; auto. 
(* label *)
  destruct (ident_eq lbl l). auto. apply IHs; auto.
Qed.

Definition measure (s: Cminor.state) : nat :=
  match s with
  | Cminor.Callstate _ _ _ _ => 0%nat
  | Cminor.State _ _ _ _ _ _ => 1%nat
  | Cminor.Returnstate _ _ _ => 2%nat
  end.

Lemma sel_step_correct:
  forall S1 t S2, Cminor.step ge S1 t S2 ->
  forall T1, match_states S1 T1 ->
  (exists T2, step tge T1 t T2 /\ match_states S2 T2)
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 T1)%nat.
Proof.
  induction 1; intros T1 ME; inv ME; simpl.
  (* skip seq *)
  inv H7. left; econstructor; split. econstructor. constructor; auto.
  (* skip block *)
  inv H7. left; econstructor; split. econstructor. constructor; auto.
  (* skip call *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].
  left; econstructor; split. 
  econstructor. inv H10; simpl in H; simpl; auto. 
  rewrite <- H0; reflexivity.
  eauto. 
  constructor; auto.
  (* assign *)
  exploit sel_expr_correct; eauto. intros [v' [A B]].
  left; econstructor; split.
  econstructor; eauto.
  constructor; auto. apply set_var_lessdef; auto.
  (* store *)
  exploit sel_expr_correct. eexact H. eauto. eauto. intros [vaddr' [A B]].
  exploit sel_expr_correct. eexact H0. eauto. eauto. intros [v' [C D]].
  exploit Mem.storev_extends; eauto. intros [m2' [P Q]].
  left; econstructor; split.
  eapply eval_store; eauto.
  constructor; auto.
  (* Scall *)
  exploit sel_expr_correct; eauto. intros [vf' [A B]].
  exploit sel_exprlist_correct; eauto. intros [vargs' [C D]].
  destruct (expr_is_addrof_builtin ge a) as [ef|]_eqn.
  (* Scall turned into Sbuiltin *)
  exploit expr_is_addrof_builtin_correct; eauto. intro EQ1. subst fd.
  right; split. omega. split. auto. 
  econstructor; eauto.
  (* Scall preserved *)
  left; econstructor; split.
  econstructor; eauto.
  eapply functions_translated; eauto. 
  apply sig_function_translated.
  constructor; auto. constructor; auto.
  (* Stailcall *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [P Q]].
  exploit sel_expr_correct; eauto. intros [vf' [A B]].
  exploit sel_exprlist_correct; eauto. intros [vargs' [C D]].
  left; econstructor; split.
  econstructor; eauto.
  eapply functions_translated; eauto. 
  apply sig_function_translated.
  constructor; auto. apply call_cont_commut; auto.
  (* Seq *)
  left; econstructor; split. constructor. constructor; auto. constructor; auto.
  (* Sifthenelse *)
  exploit sel_expr_correct; eauto. intros [v' [A B]].
  assert (Val.bool_of_val v' b). inv B. auto. inv H0.
  left; exists (State (sel_function ge f) (if b then sel_stmt ge s1 else sel_stmt ge s2) k' sp e' m'); split.
  constructor. eapply eval_condition_of_expr; eauto.
  constructor; auto. destruct b; auto.
  (* Sloop *)
  left; econstructor; split. constructor. constructor; auto. constructor; auto.
  (* Sblock *)
  left; econstructor; split. constructor. constructor; auto. constructor; auto.
  (* Sexit seq *)
  inv H7. left; econstructor; split. constructor. constructor; auto.
  (* Sexit0 block *)
  inv H7. left; econstructor; split. constructor. constructor; auto.
  (* SexitS block *)
  inv H7. left; econstructor; split. constructor. constructor; auto.
  (* Sswitch *)
  exploit sel_expr_correct; eauto. intros [v' [A B]]. inv B.
  left; econstructor; split. econstructor; eauto. constructor; auto.
  (* Sreturn None *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [P Q]].
  left; econstructor; split. 
  econstructor. simpl; eauto. 
  constructor; auto. apply call_cont_commut; auto.
  (* Sreturn Some *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [P Q]].
  exploit sel_expr_correct; eauto. intros [v' [A B]].
  left; econstructor; split. 
  econstructor; eauto.
  constructor; auto. apply call_cont_commut; auto.
  (* Slabel *)
  left; econstructor; split. constructor. constructor; auto.
  (* Sgoto *)
  exploit (find_label_commut lbl (Cminor.fn_body f) (Cminor.call_cont k)).
    apply call_cont_commut; eauto.
  rewrite H. 
  destruct (find_label lbl (sel_stmt ge (Cminor.fn_body f)) (call_cont k'0))
  as [[s'' k'']|]_eqn; intros; try contradiction.
  destruct H0. 
  left; econstructor; split.
  econstructor; eauto. 
  constructor; auto.
  (* internal function *)
  exploit Mem.alloc_extends. eauto. eauto. apply Zle_refl. apply Zle_refl. 
  intros [m2' [A B]].
  left; econstructor; split.
  econstructor; eauto.
  constructor; auto. apply set_locals_lessdef. apply set_params_lessdef; auto.
  (* external call *)
  exploit external_call_mem_extends; eauto. 
  intros [vres' [m2 [A [B [C D]]]]].
  left; econstructor; split.
  econstructor. eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  constructor; auto.
  (* external call turned into a Sbuiltin *)
  exploit external_call_mem_extends; eauto. 
  intros [vres' [m2 [A [B [C D]]]]].
  left; econstructor; split.
  econstructor. eauto. eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  constructor; auto.
  (* return *)
  inv H2. 
  left; econstructor; split. 
  econstructor. 
  constructor; auto. destruct optid; simpl; auto. apply set_var_lessdef; auto.
  (* return of an external call turned into a Sbuiltin *)
  right; split. omega. split. auto. constructor; auto. 
  destruct optid; simpl; auto. apply set_var_lessdef; auto.
Qed.

Lemma sel_initial_states:
  forall S, Cminor.initial_state prog S ->
  exists R, initial_state tprog R /\ match_states S R.
Proof.
  induction 1.
  econstructor; split.
  econstructor.
  apply Genv.init_mem_transf; eauto.
  simpl. fold tge. rewrite symbols_preserved. eexact H0.
  apply function_ptr_translated. eauto. 
  rewrite <- H2. apply sig_function_translated; auto.
  constructor; auto. constructor. apply Mem.extends_refl.
Qed.

Lemma sel_final_states:
  forall S R r,
  match_states S R -> Cminor.final_state S r -> final_state R r.
Proof.
  intros. inv H0. inv H. inv H3. inv H5. constructor.
Qed.

Theorem transf_program_correct:
  forward_simulation (Cminor.semantics prog) (CminorSel.semantics tprog).
Proof.
  eapply forward_simulation_opt.
  eexact symbols_preserved.
  eexact sel_initial_states.
  eexact sel_final_states.
  eexact sel_step_correct. 
Qed.

End PRESERVATION.
