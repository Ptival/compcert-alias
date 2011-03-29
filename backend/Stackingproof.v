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

(** Correctness proof for the translation from Linear to Mach. *)

(** This file proves semantic preservation for the [Stacking] pass. *)

Require Import Coqlib.
Require Import Maps.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Op.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Locations.
Require LTL.
Require Import Linear.
Require Import Lineartyping.
Require Import Mach.
Require Import Machconcr.
Require Import Bounds.
Require Import Conventions.
Require Import Stacklayout.
Require Import Stacking.

(** * Properties of frame offsets *)

(** ``Good variable'' properties for frame accesses. *)

Lemma typesize_typesize:
  forall ty, AST.typesize ty = 4 * Locations.typesize ty.
Proof.
  destruct ty; auto.
Qed.

Remark size_type_chunk:
  forall ty, size_chunk (chunk_of_type ty) = AST.typesize ty.
Proof.
  destruct ty; reflexivity.
Qed.

Section PRESERVATION.

Variable prog: Linear.program.
Variable tprog: Mach.program.
Hypothesis TRANSF: transf_program prog = OK tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.


Section FRAME_PROPERTIES.

Variable f: Linear.function.
Let b := function_bounds f.
Let fe := make_env b.
Variable tf: Mach.function.
Hypothesis TRANSF_F: transf_function f = OK tf.

Lemma unfold_transf_function:
  tf = Mach.mkfunction
         f.(Linear.fn_sig)
         (transl_body f fe)
         (fe.(fe_size) + f.(Linear.fn_stacksize))
         (Int.repr fe.(fe_ofs_link))
         (Int.repr fe.(fe_ofs_retaddr)).
Proof.
  generalize TRANSF_F. unfold transf_function.
  destruct (zlt (Linear.fn_stacksize f) 0). intros; discriminate.
  destruct (zlt Int.max_signed (fe_size (make_env (function_bounds f)) + Linear.fn_stacksize f)).
  intros; discriminate.
  intros. unfold fe. unfold b. congruence.
Qed.

Lemma stacksize_pos: f.(Linear.fn_stacksize) >= 0.
Proof.
  generalize TRANSF_F. unfold transf_function.
  destruct (zlt (Linear.fn_stacksize f) 0). intros; discriminate.
  auto.
Qed.

Lemma size_no_overflow: fe.(fe_size) + f.(Linear.fn_stacksize) <= Int.max_signed.
Proof.
  generalize TRANSF_F. unfold transf_function.
  destruct (zlt (Linear.fn_stacksize f) 0). intros; discriminate.
  destruct (zlt Int.max_signed (fe_size (make_env (function_bounds f)) + Linear.fn_stacksize f)).
  intros; discriminate.
  intros. unfold fe,b. omega.
Qed.

(** A frame index is valid if it lies within the resource bounds
  of the current function. *)

Definition index_valid (idx: frame_index) :=
  match idx with
  | FI_link => True
  | FI_retaddr => True
  | FI_local x Tint => 0 <= x < b.(bound_int_local)
  | FI_local x Tfloat => 0 <= x < b.(bound_float_local)
  | FI_arg x ty => 0 <= x /\ x + typesize ty <= b.(bound_outgoing)
  | FI_saved_int x => 0 <= x < b.(bound_int_callee_save)
  | FI_saved_float x => 0 <= x < b.(bound_float_callee_save)
  end.

Definition type_of_index (idx: frame_index) :=
  match idx with
  | FI_link => Tint
  | FI_retaddr => Tint
  | FI_local x ty => ty
  | FI_arg x ty => ty
  | FI_saved_int x => Tint
  | FI_saved_float x => Tfloat
  end.

(** Non-overlap between the memory areas corresponding to two
  frame indices. *)

Definition index_diff (idx1 idx2: frame_index) : Prop :=
  match idx1, idx2 with
  | FI_link, FI_link => False
  | FI_retaddr, FI_retaddr => False
  | FI_local x1 ty1, FI_local x2 ty2 =>
      x1 <> x2 \/ ty1 <> ty2
  | FI_arg x1 ty1, FI_arg x2 ty2 =>
      x1 + typesize ty1 <= x2 \/ x2 + typesize ty2 <= x1
  | FI_saved_int x1, FI_saved_int x2 => x1 <> x2
  | FI_saved_float x1, FI_saved_float x2 => x1 <> x2
  | _, _ => True
  end.

Lemma index_diff_sym:
  forall idx1 idx2, index_diff idx1 idx2 -> index_diff idx2 idx1.
Proof.
  unfold index_diff; intros. 
  destruct idx1; destruct idx2; intuition.
Qed.

Ltac AddPosProps :=
  generalize (bound_int_local_pos b); intro;
  generalize (bound_float_local_pos b); intro;
  generalize (bound_int_callee_save_pos b); intro;
  generalize (bound_float_callee_save_pos b); intro;
  generalize (bound_outgoing_pos b); intro;
  generalize (align_float_part b); intro.

Lemma size_pos: fe.(fe_size) >= 0.
Proof.
  AddPosProps.
  unfold fe, make_env, fe_size. omega.
Qed.

Opaque function_bounds.

Lemma offset_of_index_disj:
  forall idx1 idx2,
  index_valid idx1 -> index_valid idx2 ->
  index_diff idx1 idx2 ->
  offset_of_index fe idx1 + AST.typesize (type_of_index idx1) <= offset_of_index fe idx2 \/
  offset_of_index fe idx2 + AST.typesize (type_of_index idx2) <= offset_of_index fe idx1.
Proof.
  AddPosProps.
  intros.
  destruct idx1; destruct idx2;
  try (destruct t); try (destruct t0);
  unfold offset_of_index, fe, make_env,
    fe_size, fe_ofs_int_local, fe_ofs_int_callee_save,
    fe_ofs_float_local, fe_ofs_float_callee_save,
    fe_ofs_link, fe_ofs_retaddr, fe_ofs_arg,
    type_of_index, AST.typesize;
  simpl in H5; simpl in H6; simpl in H7;
  try omega.
  assert (z <> z0). intuition auto. omega.
  assert (z <> z0). intuition auto. omega.
Qed.

Remark aligned_4_4x: forall x, (4 | 4 * x).
Proof. intro. exists x; ring. Qed.

Remark aligned_4_8x: forall x, (4 | 8 * x).
Proof. intro. exists (x * 2); ring. Qed.

Remark aligned_4_align8: forall x, (4 | align x 8).
Proof. 
  intro. apply Zdivides_trans with 8. exists 2; auto. apply align_divides. omega.
Qed.

Hint Resolve Zdivide_0 Zdivide_refl Zdivide_plus_r
             aligned_4_4x aligned_4_8x aligned_4_align8: align_4.

Hint Extern 4 (?X | ?Y) => (exists (Y/X); reflexivity) : align_4.

Lemma offset_of_index_aligned:
  forall idx, (4 | offset_of_index fe idx).
Proof.
  intros.
  destruct idx;
  unfold offset_of_index, fe, make_env,
    fe_size, fe_ofs_int_local, fe_ofs_int_callee_save,
    fe_ofs_float_local, fe_ofs_float_callee_save,
    fe_ofs_link, fe_ofs_retaddr, fe_ofs_arg;
  auto with align_4.
  destruct t; auto with align_4.
Qed.

Lemma frame_size_aligned:
  (4 | fe_size fe).
Proof.
  unfold offset_of_index, fe, make_env,
    fe_size, fe_ofs_int_local, fe_ofs_int_callee_save,
    fe_ofs_float_local, fe_ofs_float_callee_save,
    fe_ofs_link, fe_ofs_retaddr, fe_ofs_arg;
  auto with align_4.
Qed.

(** The following lemmas give sufficient conditions for indices
  of various kinds to be valid. *)

Lemma index_local_valid:
  forall ofs ty,
  slot_within_bounds f b (Local ofs ty) ->
  index_valid (FI_local ofs ty).
Proof.
  unfold slot_within_bounds, index_valid. auto.
Qed.

Lemma index_arg_valid:
  forall ofs ty,
  slot_within_bounds f b (Outgoing ofs ty) ->
  index_valid (FI_arg ofs ty).
Proof.
  unfold slot_within_bounds, index_valid. auto.
Qed.

Lemma index_saved_int_valid:
  forall r,
  In r int_callee_save_regs ->
  index_int_callee_save r < b.(bound_int_callee_save) ->
  index_valid (FI_saved_int (index_int_callee_save r)).
Proof.
  intros. red. split. 
  apply Zge_le. apply index_int_callee_save_pos; auto. 
  auto.
Qed.

Lemma index_saved_float_valid:
  forall r,
  In r float_callee_save_regs ->
  index_float_callee_save r < b.(bound_float_callee_save) ->
  index_valid (FI_saved_float (index_float_callee_save r)).
Proof.
  intros. red. split. 
  apply Zge_le. apply index_float_callee_save_pos; auto. 
  auto.
Qed.

Hint Resolve index_local_valid index_arg_valid
             index_saved_int_valid index_saved_float_valid: stacking.

(** The offset of a valid index lies within the bounds of the frame. *)

Lemma offset_of_index_valid:
  forall idx,
  index_valid idx ->
  0 <= offset_of_index fe idx /\
  offset_of_index fe idx + AST.typesize (type_of_index idx) <= fe.(fe_size).
Proof.
  AddPosProps.
  intros.
  destruct idx; try destruct t;
  unfold offset_of_index, fe, make_env,
    fe_size, fe_ofs_int_local, fe_ofs_int_callee_save,
    fe_ofs_float_local, fe_ofs_float_callee_save,
    fe_ofs_link, fe_ofs_retaddr, fe_ofs_arg,
    type_of_index, AST.typesize;
  unfold index_valid in H5; simpl typesize in H5;
  omega.
Qed. 

(** Offsets for valid index are representable as signed machine integers
  without loss of precision. *)

Lemma offset_of_index_no_overflow:
  forall idx,
  index_valid idx ->
  Int.signed (Int.repr (offset_of_index fe idx)) = offset_of_index fe idx.
Proof.
  intros.
  generalize (offset_of_index_valid idx H). intros [A B].
  apply Int.signed_repr.
  split. apply Zle_trans with 0; auto. compute; intro; discriminate.
  assert (offset_of_index fe idx < fe_size fe).
    generalize (AST.typesize_pos (type_of_index idx)); intro. omega.
  generalize size_no_overflow. generalize stacksize_pos. omega.
Qed.

(** * Contents of frame slots *)

Inductive index_contains (m: mem) (sp: block) (idx: frame_index) (v: val) : Prop :=
  | index_contains_intro:
      index_valid idx ->
      Mem.load (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) = Some v ->
      index_contains m sp idx v.

(*
Lemma index_contains_undef:
  forall j m sp idx,
  index_valid idx ->
  Mem.range_perm m sp 0 fe.(fe_size) Freeable ->
  index_contains j m sp idx Vundef.
Proof.
  intros.
  exploit offset_of_index_valid; eauto. intros [A B].
  exploit (Mem.valid_access_load m (chunk_of_type (type_of_index idx)) sp (offset_of_index fe idx)).
  constructor. 
  rewrite size_type_chunk. red; intros. 
  apply Mem.perm_implies with Freeable; auto with mem.
  apply H0. omega. 
  replace (align_chunk (chunk_of_type (type_of_index idx))) with 4. 
  apply offset_of_index_aligned. destruct (type_of_index idx); auto.
  intros [v C]. 
  exists v; auto. 
Qed.
*)

Lemma index_contains_load_stack:
  forall m sp idx v,
  index_contains m sp idx v ->
  load_stack m (Vptr sp Int.zero) (type_of_index idx)
              (Int.repr (offset_of_index fe idx)) = Some v.
Proof.
  intros. inv H. 
  unfold load_stack. simpl. rewrite Int.add_commut. rewrite Int.add_zero.
  rewrite offset_of_index_no_overflow; auto.
Qed.

(** Good variable properties for [index_contains] *)

Lemma gss_index_contains_base:
  forall idx m m' sp v,
  Mem.store (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) v = Some m' ->
  index_valid idx ->
  exists v',
     index_contains m' sp idx v'
  /\ decode_encode_val v (chunk_of_type (type_of_index idx)) (chunk_of_type (type_of_index idx)) v'.
Proof.
  intros. 
  exploit Mem.load_store_similar. eauto. reflexivity. 
  intros [v' [A B]].
  exists v'; split; auto. constructor; auto.
Qed.

Lemma gss_index_contains:
  forall idx m m' sp v,
  Mem.store (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) v = Some m' ->
  index_valid idx ->
  Val.has_type v (type_of_index idx) ->
  index_contains m' sp idx v.
Proof.
  intros. exploit gss_index_contains_base; eauto. intros [v' [A B]].
  assert (v' = v).
    destruct v; destruct (type_of_index idx); simpl in *; intuition congruence.
  subst v'. auto.
Qed.

Lemma gso_index_contains:
  forall idx m m' sp v idx' v',
  Mem.store (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) v = Some m' ->
  index_valid idx ->
  index_contains m sp idx' v' ->
  index_diff idx idx' ->
  index_contains m' sp idx' v'.
Proof.
  intros. inv H1. constructor; auto. 
  rewrite <- H4. eapply Mem.load_store_other; eauto.
  right. repeat rewrite size_type_chunk. 
  apply offset_of_index_disj; auto. apply index_diff_sym; auto.
Qed.

Lemma store_other_index_contains:
  forall chunk m b ofs v' m' sp idx v,
  Mem.store chunk m b ofs v' = Some m' ->
  b <> sp \/ ofs >= fe.(fe_size) ->
  index_contains m sp idx v ->
  index_contains m' sp idx v.
Proof.
  intros. inv H1. constructor; auto. rewrite <- H3. 
  eapply Mem.load_store_other; eauto. 
  destruct H0. auto. right. 
  exploit offset_of_index_valid; eauto. intros [A B]. 
  rewrite size_type_chunk. left. omega. 
Qed.

Lemma store_index_succeeds:
  forall m sp idx v,
  index_valid idx ->
  Mem.range_perm m sp 0 fe.(fe_size) Freeable ->
  exists m',
  Mem.store (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) v = Some m'.
Proof.
  intros.
  destruct (Mem.valid_access_store m (chunk_of_type (type_of_index idx)) sp (offset_of_index fe idx) v) as [m' ST].
  constructor.
  exploit offset_of_index_valid; eauto. intros [A B].
  rewrite size_type_chunk. 
  red; intros. apply Mem.perm_implies with Freeable; auto with mem. 
  apply H0. omega.
  replace (align_chunk (chunk_of_type (type_of_index idx))) with 4.
  apply offset_of_index_aligned; auto.
  destruct (type_of_index idx); auto.
  exists m'; auto.
Qed.

Lemma store_stack_succeeds:
  forall m sp idx v m',
  index_valid idx ->
  Mem.store (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) v = Some m' ->
  store_stack m (Vptr sp Int.zero) (type_of_index idx) (Int.repr (offset_of_index fe idx)) v = Some m'.
Proof.
  intros. unfold store_stack. simpl. rewrite Int.add_commut. rewrite Int.add_zero.
  rewrite offset_of_index_no_overflow; auto.
Qed.

(** A variant of [index_contains], modulo a memory injection. *)

Definition index_contains_inj (j: meminj) (m: mem) (sp: block) (idx: frame_index) (v: val) : Prop :=
  exists v', index_contains m sp idx v' /\ val_inject j v v'.

Lemma gss_index_contains_inj:
  forall j idx m m' sp v v',
  Mem.store (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) v' = Some m' ->
  index_valid idx ->
  Val.has_type v (type_of_index idx) ->
  val_inject j v v' ->
  index_contains_inj j m' sp idx v.
Proof.
  intros. exploit gss_index_contains_base; eauto. intros [v'' [A B]].
  exists v''; split; auto.
  inv H2; destruct (type_of_index idx); simpl in *; try contradiction; subst; auto.
  econstructor; eauto.
Qed.

Lemma gso_index_contains_inj:
  forall j idx m m' sp v idx' v',
  Mem.store (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) v = Some m' ->
  index_valid idx ->
  index_contains_inj j m sp idx' v' ->
  index_diff idx idx' ->
  index_contains_inj j m' sp idx' v'.
Proof.
  intros. destruct H1 as [v'' [A B]]. exists v''; split; auto.
  eapply gso_index_contains; eauto.
Qed.

Lemma store_other_index_contains_inj:
  forall j chunk m b ofs v' m' sp idx v,
  Mem.store chunk m b ofs v' = Some m' ->
  b <> sp \/ ofs >= fe.(fe_size) ->
  index_contains_inj j m sp idx v ->
  index_contains_inj j m' sp idx v.
Proof.
  intros. destruct H1 as [v'' [A B]]. exists v''; split; auto.
  eapply store_other_index_contains; eauto.
Qed.

Lemma index_contains_inj_incr:
  forall j m sp idx v j',
  index_contains_inj j m sp idx v ->
  inject_incr j j' ->
  index_contains_inj j' m sp idx v.
Proof.
  intros. destruct H as [v'' [A B]]. exists v''; split; auto. eauto. 
Qed.

Lemma index_contains_inj_undef:
  forall j m sp idx,
  index_valid idx ->
  Mem.range_perm m sp 0 fe.(fe_size) Freeable ->
  index_contains_inj j m sp idx Vundef.
Proof.
  intros. 
  exploit offset_of_index_valid; eauto. intros [A B].
  exploit (Mem.valid_access_load m (chunk_of_type (type_of_index idx)) sp (offset_of_index fe idx)).
  constructor. 
  rewrite size_type_chunk. red; intros. 
  apply Mem.perm_implies with Freeable; auto with mem.
  apply H0. omega. 
  replace (align_chunk (chunk_of_type (type_of_index idx))) with 4. 
  apply offset_of_index_aligned. destruct (type_of_index idx); auto.
  intros [v C]. 
  exists v; split; auto. constructor; auto. 
Qed.

Hint Resolve store_other_index_contains_inj index_contains_inj_incr: stacking.

(** * Agreement between location sets and Mach states *)

(** Agreement with Mach register states *)

Definition agree_regs (j: meminj) (ls: locset) (rs: regset) : Prop :=
  forall r, val_inject j (ls (R r)) (rs r).

Record agree_locsets (ls ls0: locset) : Prop :=
  mk_agree_locs {
    agree_unused_reg:
       forall r, ~(mreg_within_bounds b r) -> ls (R r) = ls0 (R r);
    agree_incoming:
       forall ofs ty, 
       In (S (Incoming ofs ty)) (loc_parameters f.(Linear.fn_sig)) ->
       ls (S (Incoming ofs ty)) = ls0 (S (Outgoing ofs ty))
  }.

Hint Resolve agree_unused_reg agree_incoming: stacking.

(* A variant used at call points *)

Definition agree_callee_save (ls ls0: locset) : Prop :=
  forall l,
  match l with
  | R r => In r int_callee_save_regs \/ In r float_callee_save_regs
  | S s => True
  end ->
  ls l = ls0 l.

(** Agreement over the data stored in the Mach frame *)

Record agree_frame (j: meminj) (ls ls0: locset) (m: mem) (sp: block) (parent retaddr: val) : Prop :=
  mk_agree_frame {
    (** Local and outgoing stack slots (on the Linear side) have
        the same values as the one loaded from the current Mach frame 
        at the corresponding offsets. *)
    agree_locals:
      forall ofs ty, 
      slot_within_bounds f b (Local ofs ty) ->
      index_contains_inj j m sp (FI_local ofs ty) (ls (S (Local ofs ty)));
    agree_outgoing:
      forall ofs ty, 
      slot_within_bounds f b (Outgoing ofs ty) ->
      index_contains_inj j m sp (FI_arg ofs ty) (ls (S (Outgoing ofs ty)));

    (** The back link and return address slots of the Mach frame contain
        the [parent] and [retaddr] values, respectively. *)
    agree_link:
      index_contains m sp FI_link parent;
    agree_retaddr:
      index_contains m sp FI_retaddr retaddr;

    (** The areas of the frame reserved for saving used callee-save
        registers always contain the values that those registers had
        on function entry. *)
    agree_saved_int:
      forall r,
      In r int_callee_save_regs ->
      index_int_callee_save r < b.(bound_int_callee_save) ->
      index_contains_inj j m sp (FI_saved_int (index_int_callee_save r)) (ls0 (R r));
    agree_saved_float:
      forall r,
      In r float_callee_save_regs ->
      index_float_callee_save r < b.(bound_float_callee_save) ->
      index_contains_inj j m sp (FI_saved_float (index_float_callee_save r)) (ls0 (R r));

    (** Validity of [sp] *)
    agree_valid_mach:
      Mem.valid_block m sp;
    (** Permissions *)
    agree_perm:
      Mem.range_perm m sp 0 fe.(fe_size) Freeable
  }.

Hint Resolve agree_locals agree_outgoing agree_link agree_retaddr
             agree_saved_int agree_saved_float agree_valid_mach agree_perm: stacking.

(** Properties of the Linear stack data block *)

Record agree_stackdata (m: mem) (sp: block) := mk_agree_stackdata {
    agree_valid_linear:
      Mem.valid_block m sp;
    agree_bounds:
      Mem.bounds m sp = (0, f.(Linear.fn_stacksize))
  }.

(** Mapping between the Linear stack pointer [sp] and the Mach stack pointer [sp']. *)

Record agree_stackptrs (j: meminj) (sp sp': block) := mk_agree_stackptrs {
    agree_inj:
      j sp = Some(sp', fe.(fe_size));
    agree_inj_unique:
      forall b delta, j b = Some(sp', delta) -> b = sp /\ delta = fe.(fe_size)
  }.

(** ** Properties of [agree_regs]. *)

(** Values of registers *)

Lemma agree_reg:
  forall j ls rs r,
  agree_regs j ls rs -> val_inject j (ls (R r)) (rs r).
Proof.
  intros. auto. 
Qed.

Lemma agree_reglist:
  forall j ls rs rl,
  agree_regs j ls rs -> val_list_inject j (reglist ls rl) (rs##rl).
Proof.
  induction rl; simpl; intros.
  auto. constructor. eauto with stacking. auto. 
Qed.

Hint Resolve agree_reg agree_reglist: stacking.

(** Preservation under assignment of machine register. *)

Lemma agree_regs_set_reg:
  forall j ls rs r v v',
  agree_regs j ls rs ->
  val_inject j v v' ->
  agree_regs j (Locmap.set (R r) v ls) (Regmap.set r v' rs).
Proof.
  intros; red; intros. 
  unfold Regmap.set. destruct (RegEq.eq r0 r). subst r0. 
  rewrite Locmap.gss; auto.
  rewrite Locmap.gso; auto. red. auto.
Qed.

Lemma agree_regs_undef_temps:
  forall j ls rs,
  agree_regs j ls rs ->
  agree_regs j (LTL.undef_temps ls) (undef_temps rs).
Proof.
  unfold LTL.undef_temps, undef_temps.
  change temporaries with (List.map R (int_temporaries ++ float_temporaries)).
  generalize (int_temporaries ++ float_temporaries).
  induction l; simpl; intros.
  auto. 
  apply IHl. apply agree_regs_set_reg; auto. 
Qed.

Lemma agree_regs_undef_op:
  forall op j ls rs,
  agree_regs j ls rs ->
  agree_regs j (Linear.undef_op op ls) (undef_op (transl_op fe op) rs).
Proof.
  intros.
  generalize (agree_regs_undef_temps _ _ _ H). 
  destruct op; simpl; auto.
Qed.

(** Preservation under assignment of stack slot *)

Lemma agree_regs_set_slot:
  forall j ls rs ss v,
  agree_regs j ls rs ->
  agree_regs j (Locmap.set (S ss) v ls) rs.
Proof.
  intros; red; intros. rewrite Locmap.gso; auto. red. destruct ss; auto.
Qed.

(** Preservation by increasing memory injections *)

Lemma agree_regs_inject_incr:
  forall j ls rs j',
  agree_regs j ls rs -> inject_incr j j' -> agree_regs j' ls rs.
Proof.
  intros; red; intros; eauto with stacking.
Qed.

(** ** Properties of [agree_locsets] *)

(** Preservation under assignment of machine register. *)

Lemma agree_locsets_set_reg:
  forall ls ls0 r v,
  agree_locsets ls ls0 ->
  mreg_within_bounds b r ->
  agree_locsets (Locmap.set (R r) v ls) ls0.
Proof.
  intros. constructor; intros.
  rewrite Locmap.gso. eauto with stacking. red. intuition congruence.
  rewrite Locmap.gso; eauto with stacking. red; auto.
Qed.

Remark temporary_within_bounds:
  forall r, In (R r) temporaries -> mreg_within_bounds b r.
Proof.
  intros; red. destruct (mreg_type r). 
  destruct (zlt (index_int_callee_save r) 0). 
  generalize (bound_int_callee_save_pos b). omega.
  exploit int_callee_save_not_destroyed. 
  left. eauto with coqlib. apply index_int_callee_save_pos2; auto.
  contradiction.
  destruct (zlt (index_float_callee_save r) 0). 
  generalize (bound_float_callee_save_pos b). omega.
  exploit float_callee_save_not_destroyed. 
  left. eauto with coqlib. apply index_float_callee_save_pos2; auto.
  contradiction.
Qed.

Lemma agree_locsets_undef_temps:
  forall ls0 ls,
  agree_locsets ls ls0 ->
  agree_locsets (LTL.undef_temps ls) ls0.
Proof.
  intros ls0. unfold LTL.undef_temps. 
  assert (forall regs ls,
         incl (List.map R regs) temporaries ->
         agree_locsets ls ls0 ->
         agree_locsets (Locmap.undef (List.map R regs) ls) ls0).
  induction regs; simpl; intros.
  auto.
  apply IHregs; eauto with coqlib.
  apply agree_locsets_set_reg; auto. 
  apply temporary_within_bounds; eauto with coqlib.
  intros. unfold LTL.undef_temps.
  change temporaries with (List.map R (int_temporaries ++ float_temporaries)).
  apply H; auto. apply incl_refl. 
Qed.

Lemma agree_locsets_undef_op:
  forall op ls ls0,
  agree_locsets ls ls0 ->
  agree_locsets (Linear.undef_op op ls) ls0.
Proof.
  intros.
  generalize (agree_locsets_undef_temps _ _ H). 
  destruct op; simpl; auto.
Qed.

(** Preservation under assignment of stack slot *)

Lemma agree_locsets_set_slot:
  forall ls ls0 ss v,
  agree_locsets ls ls0 ->
  slot_writable ss ->
  agree_locsets (Locmap.set (S ss) v ls) ls0.
Proof.
  unfold slot_writable. intros; constructor; intros.
  rewrite Locmap.gso; eauto with stacking. red. destruct ss; auto.
  rewrite Locmap.gso; eauto with stacking. red. destruct ss; tauto.
Qed.

(** Preservation at tail calls (when parent locset is changed). *)

Remark mreg_not_within_bounds:
  forall r,
  ~mreg_within_bounds b r -> In r int_callee_save_regs \/ In r float_callee_save_regs.
Proof.
  intro r; unfold mreg_within_bounds.
  destruct (mreg_type r); intro.
  left. apply index_int_callee_save_pos2. 
  generalize (bound_int_callee_save_pos b). omega.
  right. apply index_float_callee_save_pos2. 
  generalize (bound_float_callee_save_pos b). omega.
Qed.

Lemma agree_callee_save_agree_locsets:
  forall ls ls1 ls2,
  agree_locsets ls ls1 ->
  agree_callee_save ls1 ls2 ->
  agree_locsets ls ls2.
Proof.
  intros. inv H. constructor; intros.
  rewrite agree_unused_reg0; auto.
  apply H0. apply mreg_not_within_bounds; auto.
  rewrite agree_incoming0; auto.
Qed.

(** Preservation at return points (when locset is changed) *)

Lemma agree_callee_save_agree_locsets_2:
  forall ls0 ls1 ls2,
  agree_locsets ls1 ls0 ->
  agree_callee_save ls2 ls1 ->
  agree_locsets ls2 ls0.
Proof.
  intros. inv H. constructor; intros.
  red in H0. rewrite H0. apply agree_unused_reg0. auto.
  apply mreg_not_within_bounds; auto.
  red in H0. rewrite H0. auto. auto.
Qed.

(** Properties of [agree_callee_save]. *)

Lemma agree_callee_save_return_regs:
  forall ls1 ls2,
  agree_callee_save (return_regs ls1 ls2) ls1.
Proof.
  intros; red; intros.
  unfold return_regs. destruct l; auto.
  generalize (int_callee_save_not_destroyed m); intro.
  generalize (float_callee_save_not_destroyed m); intro.
  destruct (In_dec Loc.eq (R m) temporaries). tauto.
  destruct (In_dec Loc.eq (R m) destroyed_at_call). tauto.
  auto.
Qed.

Lemma agree_callee_save_set_result:
  forall ls1 ls2 v sg,
  agree_callee_save ls1 ls2 ->
  agree_callee_save (Locmap.set (R (loc_result sg)) v ls1) ls2.
Proof.
  intros; red; intros. rewrite <- H; auto. 
  apply Locmap.gso. destruct l; simpl; auto.
  red; intro. subst m. elim (loc_result_not_callee_save _ H0).
Qed.

(** ** Properties of [agree_frame] *)

(** General invariance property *)

Lemma agree_frame_invariant:
  forall j ls ls0 m sp parent retaddr ls' ls0' m',
  agree_frame j ls ls0 m sp parent retaddr ->
  (forall l,
      match l with
      | S(Local ofs ty) => slot_within_bounds f b (Local ofs ty)
      | S(Outgoing ofs ty) => slot_within_bounds f b (Outgoing ofs ty)
      | _ => False
      end ->
      ls' l = ls l) ->
  (forall r,
      In r int_callee_save_regs \/ In r float_callee_save_regs ->
      ls0' (R r) = ls0 (R r)) ->
  (forall chunk ofs v,
      0 <= ofs -> ofs + size_chunk chunk <= fe.(fe_size) ->
      Mem.load chunk m sp ofs = Some v ->
      Mem.load chunk m' sp ofs = Some v) ->
  (Mem.valid_block m sp -> Mem.valid_block m' sp) ->
  (forall ofs p,
      0 <= ofs < fe.(fe_size) -> Mem.perm m sp ofs p -> Mem.perm m' sp ofs p) ->
  agree_frame j ls' ls0' m' sp parent retaddr.
Proof.
  intros.
  assert (IC: forall idx v,
              index_contains m sp idx v -> index_contains m' sp idx v).
    intros. inv H5.
    exploit offset_of_index_valid; eauto. intros [A B].
    constructor; auto. apply H2. auto. rewrite size_type_chunk; auto. auto.
  assert (ICI: forall idx v,
              index_contains_inj j m sp idx v -> index_contains_inj j m' sp idx v).
    intros. destruct H5 as [v' [A B]]. exists v'; split; auto. 
  inv H; constructor; intros.
  rewrite H0; eauto. 
  rewrite H0; eauto.
  auto.
  auto.
  rewrite H1; eauto.
  rewrite H1; eauto.
  eauto.
  red; intros. apply H4; auto. 
Qed.

(** Preservation by assignment to register *)

Lemma agree_frame_set_reg:
  forall j ls ls0 m sp parent retaddr r v,
  agree_frame j ls ls0 m sp parent retaddr ->
  agree_frame j (Locmap.set (R r) v ls) ls0 m sp parent retaddr.
Proof.
  intros. eapply agree_frame_invariant; eauto. 
  intros. apply Locmap.gso. red. destruct l; tauto.
Qed.

(** Preservation by assignment to local slot *)

Lemma agree_frame_set_local:
  forall j ls ls0 m sp parent retaddr ofs ty v v' m',
  agree_frame j ls ls0 m sp parent retaddr ->
  slot_within_bounds f b (Local ofs ty) ->
  val_inject j v v' ->
  Val.has_type v ty ->
  Mem.store (chunk_of_type ty) m sp (offset_of_index fe (FI_local ofs ty)) v' = Some m' ->
  agree_frame j (Locmap.set (S (Local ofs ty)) v ls) ls0 m' sp parent retaddr.
Proof.
  intros. 
  change (chunk_of_type ty) with (chunk_of_type (type_of_index (FI_local ofs ty))) in H3.
  constructor; intros.
(* local *)
  unfold Locmap.set. simpl. destruct (Loc.eq (S (Local ofs ty)) (S (Local ofs0 ty0))).
  inv e. eapply gss_index_contains_inj; eauto. 
  eapply gso_index_contains_inj. eauto. simpl; auto. eauto with stacking.
  simpl. destruct (zeq ofs ofs0); auto. destruct (typ_eq ty ty0); auto. congruence.
(* outgoing *)
  rewrite Locmap.gso. eapply gso_index_contains_inj; eauto with stacking.
  simpl; auto. red; auto.
(* parent *)
  eapply gso_index_contains; eauto with stacking. red; auto.
(* retaddr *)
  eapply gso_index_contains; eauto with stacking. red; auto.
(* int callee save *)
  eapply gso_index_contains_inj; eauto with stacking. simpl; auto. 
(* float callee save *)
  eapply gso_index_contains_inj; eauto with stacking. simpl; auto.
(* valid *)
  eauto with mem stacking.
(* perm *)
  red; intros. eapply Mem.perm_store_1; eauto. eapply agree_perm; eauto. 
Qed.

(** Preservation by assignment to outgoing slot *)

Lemma agree_frame_set_outgoing:
  forall j ls ls0 m sp parent retaddr ofs ty v v' m',
  agree_frame j ls ls0 m sp parent retaddr ->
  slot_within_bounds f b (Outgoing ofs ty) ->
  val_inject j v v' ->
  Val.has_type v ty ->
  Mem.store (chunk_of_type ty) m sp (offset_of_index fe (FI_arg ofs ty)) v' = Some m' ->
  agree_frame j (Locmap.set (S (Outgoing ofs ty)) v ls) ls0 m' sp parent retaddr.
Proof.
  intros. 
  change (chunk_of_type ty) with (chunk_of_type (type_of_index (FI_arg ofs ty))) in H3.
  constructor; intros.
(* local *)
  rewrite Locmap.gso. eapply gso_index_contains_inj; eauto with stacking. simpl; auto. red; auto.
(* outgoing *)
  unfold Locmap.set. simpl. destruct (Loc.eq (S (Outgoing ofs ty)) (S (Outgoing ofs0 ty0))).
  inv e. eapply gss_index_contains_inj; eauto.
  case_eq (Loc.overlap_aux ty ofs ofs0 || Loc.overlap_aux ty0 ofs0 ofs); intros.
  apply index_contains_inj_undef. auto.
  red; intros. eapply Mem.perm_store_1; eauto. eapply agree_perm; eauto.
  eapply gso_index_contains_inj; eauto with stacking.
  red. eapply Loc.overlap_aux_false_1; eauto.
(* parent *)
  eapply gso_index_contains; eauto with stacking. red; auto.
(* retaddr *)
  eapply gso_index_contains; eauto with stacking. red; auto.
(* int callee save *)
  eapply gso_index_contains_inj; eauto with stacking. simpl; auto. 
(* float callee save *)
  eapply gso_index_contains_inj; eauto with stacking. simpl; auto.
(* valid *)
  eauto with mem stacking.
(* perm *)
  red; intros. eapply Mem.perm_store_1; eauto. eapply agree_perm; eauto.
Qed.

(** Preservation by increasing memory injections *)

Lemma agree_frame_inject_incr:
  forall j ls ls0 m sp parent retaddr j',
  agree_frame j ls ls0 m sp parent retaddr ->
  inject_incr j j' ->
  agree_frame j' ls ls0 m sp parent retaddr.
Proof.
  intros. constructor; intros; eauto with stacking.
Qed.

(** ** Properties of the [agree_stackdata] predicate. *)

(** General invariance property *)
  
Lemma agree_stackdata_invariant:
  forall m sp m',
  agree_stackdata m sp ->
  (Mem.valid_block m sp -> Mem.valid_block m' sp) ->
  Mem.bounds m' sp = Mem.bounds m sp ->
  agree_stackdata m' sp.
Proof.
  intros. inv H. constructor; auto. congruence.
Qed.

(** ** Properties of the [agree_stackptrs] predicate. *)

(** Preservation by increasing injections (external calls. allocations) *)

Lemma agree_stackptrs_inject_incr:
  forall j sp1 sp2 m1 m2 j',
  agree_stackptrs j sp1 sp2 ->
  inject_incr j j' -> inject_separated j j' m1 m2 ->
  Mem.valid_block m1 sp1 -> Mem.valid_block m2 sp2 ->
  agree_stackptrs j' sp1 sp2.
Proof.
  intros. inv H. constructor. 
  auto. 
  intros. caseEq (j b0); intros. 
  destruct p as [b' delta']. apply agree_inj_unique0. 
  exploit H0. eexact H4. congruence.
  exploit H1; eauto. intros [A B]. contradiction.
Qed.

Remark inject_alloc_separated:
  forall j m1 m2 j' b1 b2 delta,
  inject_incr j j' ->
  j' b1 = Some(b2, delta) ->
  (forall b, b <> b1 -> j' b = j b) ->
  ~Mem.valid_block m1 b1 -> ~Mem.valid_block m2 b2 ->
  inject_separated j j' m1 m2.
Proof.
  intros. red. intros.
  destruct (eq_block b0 b1). subst b0. rewrite H0 in H5; inv H5. tauto.
  rewrite H1 in H5. congruence. auto.
Qed.

(** * Correctness of saving and restoring of callee-save registers *)

(** The following lemmas show the correctness of the register saving
  code generated by [save_callee_save]: after this code has executed,
  the register save areas of the current frame do contain the
  values of the callee-save registers used by the function. *)

Section SAVE_CALLEE_SAVE.

Variable bound: frame_env -> Z.
Variable number: mreg -> Z.
Variable mkindex: Z -> frame_index.
Variable ty: typ.
Variable j: meminj.
Variable cs: list stackframe.
Variable fb: block.
Variable sp: block.
Variable csregs: list mreg.
Variable ls: locset.
Variable rs: regset.

Inductive stores_in_frame: mem -> mem -> Prop :=
  | stores_in_frame_refl: forall m,
      stores_in_frame m m
  | stores_in_frame_step: forall m1 chunk ofs v m2 m3,
       ofs + size_chunk chunk <= fe.(fe_size) ->
       Mem.store chunk m1 sp ofs v = Some m2 ->
       stores_in_frame m2 m3 ->
       stores_in_frame m1 m3.

Remark stores_in_frame_trans:
  forall m1 m2, stores_in_frame m1 m2 ->
  forall m3, stores_in_frame m2 m3 -> stores_in_frame m1 m3.
Proof.
  induction 1; intros. auto. econstructor; eauto.
Qed.

Hypothesis number_inj: 
  forall r1 r2, In r1 csregs -> In r2 csregs -> r1 <> r2 -> number r1 <> number r2.
Hypothesis mkindex_valid:
  forall r, In r csregs -> number r < bound fe -> index_valid (mkindex (number r)).
Hypothesis mkindex_typ:
  forall z, type_of_index (mkindex z) = ty.
Hypothesis mkindex_inj:
  forall z1 z2, z1 <> z2 -> mkindex z1 <> mkindex z2.
Hypothesis mkindex_diff:
  forall r idx,
  idx <> mkindex (number r) -> index_diff (mkindex (number r)) idx.
Hypothesis csregs_typ:
  forall r, In r csregs -> mreg_type r = ty.

Hypothesis agree: agree_regs j ls rs.
Hypothesis wt_ls: wt_locset ls.

Lemma save_callee_save_regs_correct:
  forall l k m,
  incl l csregs ->
  list_norepet l ->
  Mem.range_perm m sp 0 fe.(fe_size) Freeable ->
  exists m',
    star step tge 
       (State cs fb (Vptr sp Int.zero)
         (save_callee_save_regs bound number mkindex ty fe l k) rs m)
    E0 (State cs fb (Vptr sp Int.zero) k rs m')
  /\ (forall r,
       In r l -> number r < bound fe ->
       index_contains_inj j m' sp (mkindex (number r)) (ls (R r)))
  /\ (forall idx v,
       index_valid idx ->
       (forall r,
         In r l -> number r < bound fe -> idx <> mkindex (number r)) ->
       index_contains m sp idx v ->
       index_contains m' sp idx v)
  /\ stores_in_frame m m'
  /\ Mem.range_perm m' sp 0 fe.(fe_size) Freeable.
Proof.
  induction l; intros; simpl save_callee_save_regs.
  (* base case *)
  exists m. split. apply star_refl. 
  split. intros. elim H2.
  split. auto.
  split. constructor.
  auto.
  (* inductive case *)
  assert (R1: incl l csregs). eauto with coqlib.
  assert (R2: list_norepet l). inversion H0; auto.
  unfold save_callee_save_reg.
  destruct (zlt (number a) (bound fe)).
  (* a store takes place *)
  exploit store_index_succeeds. apply (mkindex_valid a); auto with coqlib. 
  eauto. instantiate (1 := rs a). intros [m1 ST].
  exploit (IHl k m1).  auto with coqlib. auto. 
  red; eauto with mem.
  intros [m' [A [B [C [D E]]]]].
  exists m'. 
  split. eapply star_left; eauto. constructor. 
  rewrite <- (mkindex_typ (number a)). 
  apply store_stack_succeeds; auto with coqlib.
  traceEq.
  split; intros.
  simpl in H2. destruct (mreg_eq a r). subst r.
  assert (index_contains_inj j m1 sp (mkindex (number a)) (ls (R a))).
    eapply gss_index_contains_inj; eauto.
    rewrite mkindex_typ. rewrite <- (csregs_typ a). apply wt_ls. auto with coqlib.
  destruct H4 as [v' [P Q]].
  exists v'; split; auto. apply C; auto. 
  intros. apply mkindex_inj. apply number_inj; auto with coqlib. 
  inv H0. intuition congruence.
  apply B; auto with coqlib. 
  intuition congruence.
  split. intros.
  apply C; auto with coqlib.
  eapply gso_index_contains; eauto with coqlib. 
  split. econstructor; eauto.
  rewrite size_type_chunk. 
  exploit offset_of_index_valid; eauto with coqlib.
  intros [P Q]. omega.
  auto.
  (* no store takes place *)
  exploit (IHl k m); auto with coqlib. 
  intros [m' [A [B [C [D E]]]]].
  exists m'; intuition. 
  simpl in H2. destruct H2. subst r. omegaContradiction. apply B; auto.
  apply C; auto with coqlib.
  intros. eapply H3; eauto. auto with coqlib.
Qed.

End SAVE_CALLEE_SAVE.

Lemma save_callee_save_correct:
  forall j ls rs sp cs fb k m,
  agree_regs j ls rs ->
  (forall l, Val.has_type (ls l) (Loc.type l)) ->
  Mem.range_perm m sp 0 fe.(fe_size) Freeable ->
  exists m',
    star step tge 
       (State cs fb (Vptr sp Int.zero) (save_callee_save fe k) rs m)
    E0 (State cs fb (Vptr sp Int.zero) k rs m')
  /\ (forall r,
       In r int_callee_save_regs -> index_int_callee_save r < b.(bound_int_callee_save) ->
       index_contains_inj j m' sp (FI_saved_int (index_int_callee_save r)) (ls (R r)))
  /\ (forall r,
       In r float_callee_save_regs -> index_float_callee_save r < b.(bound_float_callee_save) ->
       index_contains_inj j m' sp (FI_saved_float (index_float_callee_save r)) (ls (R r)))
  /\ (forall idx v,
       index_valid idx ->
       match idx with FI_saved_int _ => False | FI_saved_float _ => False | _ => True end ->
       index_contains m sp idx v ->
       index_contains m' sp idx v)
  /\ stores_in_frame sp m m'
  /\ Mem.range_perm m' sp 0 fe.(fe_size) Freeable.
Proof.
  intros.
  exploit (save_callee_save_regs_correct 
             fe_num_int_callee_save
             index_int_callee_save
             FI_saved_int Tint
             j cs fb sp int_callee_save_regs ls rs).
  intros. apply index_int_callee_save_inj; auto. 
  intros. simpl. split. apply Zge_le. apply index_int_callee_save_pos; auto. assumption.
  auto.
  intros; congruence.
  intros; simpl. destruct idx; auto. congruence.
  intros. apply int_callee_save_type. auto.
  auto.
  auto.
  apply incl_refl. 
  apply int_callee_save_norepet.
  eauto.
  intros [m1 [A [B [C [D E]]]]].
  exploit (save_callee_save_regs_correct 
             fe_num_float_callee_save
             index_float_callee_save
             FI_saved_float Tfloat
             j cs fb sp float_callee_save_regs ls rs).
  intros. apply index_float_callee_save_inj; auto. 
  intros. simpl. split. apply Zge_le. apply index_float_callee_save_pos; auto. assumption.
  simpl; auto.
  intros; congruence.
  intros; simpl. destruct idx; auto. congruence.
  intros. apply float_callee_save_type. auto.
  auto. 
  auto.
  apply incl_refl. 
  apply float_callee_save_norepet.
  eexact E.
  intros [m2 [P [Q [R [S T]]]]].
  exists m2.
  split. unfold save_callee_save, save_callee_save_int, save_callee_save_float.
  eapply star_trans; eauto. 
  split; intros.
  destruct (B r H2 H3) as [v [X Y]]. exists v; split; auto. apply R.
  apply index_saved_int_valid; auto. 
  intros. congruence.
  auto.
  split. intros. apply Q; auto.
  split. intros. apply R. auto.
  intros. destruct idx; contradiction||congruence.
  apply C. auto. 
  intros. destruct idx; contradiction||congruence.
  auto.
  split. eapply stores_in_frame_trans; eauto.
  auto.
Qed.

Lemma stores_in_frame_inject:
  forall j sp sp' m,
  agree_stackptrs j sp sp' ->
  Mem.bounds m sp = (0, f.(Linear.fn_stacksize)) ->
  forall m1 m2, stores_in_frame sp' m1 m2 -> Mem.inject j m m1 -> Mem.inject j m m2.
Proof.
  induction 3; intros.
  auto.
  apply IHstores_in_frame.
  intros. eapply Mem.store_outside_inject; eauto.
  intros. exploit agree_inj_unique; eauto. intros [A B]; subst.
  right. rewrite H0; unfold fst. omega.
Qed.

Lemma stores_in_frame_valid:
  forall b sp m m', stores_in_frame sp m m' -> Mem.valid_block m b -> Mem.valid_block m' b.
Proof.
  induction 1; intros. auto. apply IHstores_in_frame. eauto with mem.
Qed.

Lemma stores_in_frame_perm:
  forall b ofs p sp m m', stores_in_frame sp m m' -> Mem.perm m b ofs p -> Mem.perm m' b ofs p.
Proof.
  induction 1; intros. auto. apply IHstores_in_frame. eauto with mem.
Qed.

Lemma stores_in_frame_contents:
  forall chunk b ofs sp, b < sp ->
  forall m m', stores_in_frame sp m m' -> 
  Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
Proof.
  induction 2. auto. 
  rewrite IHstores_in_frame. eapply Mem.load_store_other; eauto.
  left; unfold block; omega.
Qed.

(** Function prologue *)

Lemma function_prologue_correct:
  forall j ls rs m1 m1' m2 sp parent ra cs fb k,
  agree_regs j ls rs ->
  wt_locset ls ->
  Mem.inject j m1 m1' ->
  Mem.alloc m1 0 f.(Linear.fn_stacksize) = (m2, sp) ->
  Val.has_type parent Tint -> Val.has_type ra Tint ->
  exists j', exists m2', exists sp', exists m3', exists m4', exists m5',
     Mem.alloc m1' 0 tf.(fn_stacksize) = (m2', sp')
  /\ store_stack m2' (Vptr sp' Int.zero) Tint tf.(fn_link_ofs) parent = Some m3'
  /\ store_stack m3' (Vptr sp' Int.zero) Tint tf.(fn_retaddr_ofs) ra = Some m4'
  /\ star step tge 
         (State cs fb (Vptr sp' Int.zero) (save_callee_save fe k) rs m4')
      E0 (State cs fb (Vptr sp' Int.zero) k rs m5')
  /\ agree_regs j' (call_regs ls) rs
  /\ agree_locsets (call_regs ls) ls
  /\ agree_frame j' (call_regs ls) ls m5' sp' parent ra
  /\ agree_stackdata m2 sp
  /\ agree_stackptrs j' sp sp'
  /\ inject_incr j j'
  /\ inject_separated j j' m1 m1'
  /\ Mem.inject j' m2 m5'
  /\ stores_in_frame sp' m2' m5'.
Proof.
  intros until k; intros AGREGS WTREGS INJ1 ALLOC TYPAR TYRA.
  rewrite unfold_transf_function.
  unfold fn_stacksize, fn_link_ofs, fn_retaddr_ofs.
  (* Allocation step *)
  caseEq (Mem.alloc m1' 0 (fe_size fe + Linear.fn_stacksize f)). intros m2' sp' ALLOC'.
  exploit Mem.alloc_left_mapped_inject.
    eapply Mem.alloc_right_inject; eauto.
    eauto.
    instantiate (1 := sp'). eauto with mem.
    instantiate (1 := fe_size fe). 
      split. apply Zle_trans with 0. compute; congruence. apply Zge_le. apply size_pos.
      generalize stacksize_pos, size_no_overflow; omega.
    right. rewrite (Mem.bounds_alloc _ _ _ _ _ ALLOC'). rewrite dec_eq_true. unfold fst, snd.
      split. compute; congruence. apply size_no_overflow.
    intros. apply Mem.perm_implies with Freeable; auto with mem. 
    eapply Mem.perm_alloc_2; eauto. generalize size_pos; omega.
    red. intros. apply Zdivides_trans with 4. 
    destruct chunk; simpl; auto with align_4.
    apply frame_size_aligned.
    intros.
      assert (Mem.valid_block m1' sp'). eapply Mem.valid_block_inject_2; eauto.
      assert (~Mem.valid_block m1' sp') by eauto with mem.
      contradiction.
  intros [j' [INJ2 [INCR [MAP1 MAP2]]]].
  assert (PERM: Mem.range_perm m2' sp' 0 fe.(fe_size) Freeable).
    red; intros. eapply Mem.perm_alloc_2; eauto. generalize stacksize_pos; omega. 
  (* Agree stackptrs *)
  assert (STACKPTRS: agree_stackptrs j' sp sp').
    constructor. auto.
    intros. destruct (eq_block b0 sp). 
    subst b0. rewrite MAP1 in H; inv H; auto.
    rewrite MAP2 in H; auto. 
    assert (Mem.valid_block m1' sp'). eapply Mem.valid_block_inject_2; eauto.
    assert (~Mem.valid_block m1' sp') by eauto with mem.
    contradiction.
  assert (STORE_IN_FRAME_INJ: forall m m' chunk ofs v,
           Mem.store chunk m sp' ofs v = Some m' ->
           Mem.inject j' m2 m ->
           ofs + size_chunk chunk <= fe.(fe_size) ->
           Mem.inject j' m2 m').
    intros. eapply Mem.store_outside_inject. eexact H0. 2: eexact H. 
    intros. exploit agree_inj_unique; eauto. intros [A B]; subst. 
    rewrite (Mem.bounds_alloc _ _ _ _ _ ALLOC). rewrite dec_eq_true. unfold fst, snd.
    right; omega.
  (* Store of parent *)
  exploit (store_index_succeeds m2' sp' FI_link parent). red; auto. auto. 
  intros [m3' STORE2].
  (* Store of retaddr *)
  exploit (store_index_succeeds m3' sp' FI_retaddr ra). red; auto. red; eauto with mem.
  intros [m4' STORE3].
  (* Saving callee-save registers *)
  assert (PERM4: Mem.range_perm m4' sp' 0 (fe_size fe) Freeable).
    red; intros. eauto with mem. 
  exploit save_callee_save_correct. 
    eapply agree_regs_inject_incr; eauto.
    auto.
    eexact PERM4.
  intros [m5' [STEPS [ICS [FCS [OTHERS [STORES PERM5]]]]]].
  (* stores in frames *)
  assert (SIF: stores_in_frame sp' m2' m5').
    econstructor; eauto. 
    rewrite size_type_chunk. apply offset_of_index_valid. red; auto.
    econstructor; eauto. 
    rewrite size_type_chunk. apply offset_of_index_valid. red; auto.
  (* Agree frame *)
  assert (FRAME: agree_frame j' (call_regs ls) ls m5' sp' parent ra).
    constructor; intros.
    simpl. apply index_contains_inj_undef; auto. 
    simpl. apply index_contains_inj_undef; auto.
    apply OTHERS; auto. red; auto.
    eapply gso_index_contains; eauto. red; auto.
    eapply gss_index_contains; eauto. red; auto.
    red; auto.
    apply OTHERS; auto. red; auto.
    eapply gss_index_contains; eauto. red; auto.
    apply ICS; auto.
    apply FCS; auto.
    eapply stores_in_frame_valid with (m := m2'); eauto with mem.
    auto.
  (* Conclusions *)
  exists j'; exists m2'; exists sp'; exists m3'; exists m4'; exists m5'; intuition.
  change Tint with (type_of_index FI_link). 
  change (fe_ofs_link fe) with (offset_of_index fe FI_link).
  apply store_stack_succeeds; auto. red; auto.
  change Tint with (type_of_index FI_retaddr). 
  change (fe_ofs_retaddr fe) with (offset_of_index fe FI_retaddr).
  apply store_stack_succeeds; auto. red; auto.
  eexact STEPS.
  red; simpl; eauto.
  eauto with mem.
  rewrite (Mem.bounds_alloc _ _ _ _ _ ALLOC). rewrite dec_eq_true; auto.
  eapply inject_alloc_separated; eauto with mem.
  eapply stores_in_frame_inject; eauto. 
  rewrite (Mem.bounds_alloc _ _ _ _ _ ALLOC). rewrite dec_eq_true; auto.
Qed.

(** The following lemmas show the correctness of the register reloading
  code generated by [reload_callee_save]: after this code has executed,
  all callee-save registers contain the same values they had at
  function entry. *)

Section RESTORE_CALLEE_SAVE.

Variable bound: frame_env -> Z.
Variable number: mreg -> Z.
Variable mkindex: Z -> frame_index.
Variable ty: typ.
Variable csregs: list mreg.
Variable j: meminj.
Variable cs: list stackframe.
Variable fb: block.
Variable sp: block.
Variable ls0: locset.
Variable m: mem.

Hypothesis mkindex_valid:
  forall r, In r csregs -> number r < bound fe -> index_valid (mkindex (number r)).
Hypothesis mkindex_typ:
  forall z, type_of_index (mkindex z) = ty.
Hypothesis number_within_bounds:
  forall r, In r csregs ->
  (number r < bound fe <-> mreg_within_bounds b r).
Hypothesis mkindex_val:
  forall r,
  In r csregs -> number r < bound fe ->
  index_contains_inj j m sp (mkindex (number r)) (ls0 (R r)).

Lemma restore_callee_save_regs_correct:
  forall l ls rs k,
  incl l csregs ->
  list_norepet l -> 
  agree_regs j ls rs ->
  agree_locsets ls ls0 ->
  wt_locset ls -> wt_locset ls0 ->
  exists ls', exists rs',
    star step tge
      (State cs fb (Vptr sp Int.zero)
        (restore_callee_save_regs bound number mkindex ty fe l k) rs m)
   E0 (State cs fb (Vptr sp Int.zero) k rs' m)
  /\ (forall r, In r l -> val_inject j (ls0 (R r)) (rs' r))
  /\ (forall r, ~(In r l) -> rs' r = rs r)
  /\ agree_regs j ls' rs'
  /\ agree_locsets ls' ls0
  /\ wt_locset ls'.
Proof.
  induction l; intros; simpl restore_callee_save_regs.
  (* base case *)
  exists ls. exists rs. intuition. apply star_refl. elim H2. 
  (* inductive case *)
  assert (R0: In a csregs). apply H; auto with coqlib.
  assert (R1: incl l csregs). eauto with coqlib.
  assert (R2: list_norepet l). inversion H0; auto.
  unfold restore_callee_save_reg.
  destruct (zlt (number a) (bound fe)).
  exploit (mkindex_val a); auto. intros [v [X Y]].
  set (ls1 := Locmap.set (R a) (ls0 (R a)) ls).
  set (rs1 := Regmap.set a v rs).
  exploit (IHl ls1 rs1 k); eauto. 
    unfold ls1, rs1. apply agree_regs_set_reg; auto. 
    unfold ls1. apply agree_locsets_set_reg; auto. rewrite <- number_within_bounds; auto.
    unfold ls1. apply wt_setloc; auto. 
  intros [ls' [rs' [A [B [C D]]]]].
  exists ls'; exists rs'. split. 
  eapply star_left. 
  constructor. rewrite <- (mkindex_typ (number a)). apply index_contains_load_stack. eauto.   
  eauto. traceEq.
  split. intros. destruct H5.
  subst r. rewrite C. unfold rs1. rewrite Regmap.gss. auto. inv H0; auto.
  auto.
  split. intros. simpl in H5. rewrite C. unfold rs1. apply Regmap.gso.
  apply sym_not_eq; tauto. tauto.
  auto.
  (* no load takes place *)
  exploit (IHl ls rs k); auto.
  intros [ls' [rs' [A [B [C [D [E F]]]]]]].
  exists ls'; exists rs'. split. assumption.
  split. intros. destruct H5.
  subst r. rewrite <- (agree_unused_reg _ _ E). apply D. 
  rewrite <- number_within_bounds. auto. auto. auto.
  split. intros. simpl in H5. apply C. tauto.
  auto.
Qed.

End RESTORE_CALLEE_SAVE.

Lemma restore_callee_save_correct:
  forall j cs fb sp k rs m ls ls0 pa ra,
  agree_regs j ls rs -> agree_locsets ls ls0 -> 
  agree_frame j ls ls0 m sp pa ra ->
  wt_locset ls -> wt_locset ls0 ->
  exists rs',
    star step tge
       (State cs fb (Vptr sp Int.zero) (restore_callee_save fe k) rs m)
    E0 (State cs fb (Vptr sp Int.zero) k rs' m)
  /\ (forall r, 
        In r int_callee_save_regs \/ In r float_callee_save_regs -> 
        val_inject j (ls0 (R r)) (rs' r))
  /\ (forall r, 
        ~(In r int_callee_save_regs) ->
        ~(In r float_callee_save_regs) ->
        rs' r = rs r).
Proof.
  intros. 
    exploit (restore_callee_save_regs_correct 
             fe_num_int_callee_save
             index_int_callee_save
             FI_saved_int
             Tint
             int_callee_save_regs
             j cs fb sp ls0 m); auto.
  intros. unfold mreg_within_bounds. rewrite (int_callee_save_type r H4). tauto.
  eapply agree_saved_int; eauto. 
  apply incl_refl.
  apply int_callee_save_norepet.
  eauto. auto. auto.
  intros [ls1 [rs1 [A [B [C [D [E F]]]]]]].
    exploit (restore_callee_save_regs_correct 
             fe_num_float_callee_save
             index_float_callee_save
             FI_saved_float
             Tfloat
             float_callee_save_regs
             j cs fb sp ls0 m); auto.
  intros. unfold mreg_within_bounds. rewrite (float_callee_save_type r H4). tauto.
  eapply agree_saved_float; eauto. 
  apply incl_refl.
  apply float_callee_save_norepet.
  eexact D. eexact E. exact F.
  intros [ls2 [rs2 [P [Q [R [S [T U]]]]]]].
  exists rs2.
  split. unfold restore_callee_save. eapply star_trans; eauto.
  split. intros. destruct H4.
    rewrite R. apply B; auto. red; intros. exploit int_float_callee_save_disjoint; eauto.
   apply Q; auto.
  intros. rewrite R; auto.
Qed.


Lemma function_epilogue_correct:
  forall j cs fb k ls rs ls0 m' sp' pa ra m sp m1,
  agree_regs j ls rs ->
  agree_locsets ls ls0 ->
  agree_frame j ls ls0 m' sp' pa ra ->
  agree_stackdata m sp ->
  agree_stackptrs j sp sp' ->
  wt_locset ls ->
  wt_locset ls0 ->
  Mem.inject j m m' ->
  Mem.free m sp 0 f.(Linear.fn_stacksize) = Some m1 ->
  exists rs1, exists m1',
     load_stack m' (Vptr sp' Int.zero) Tint tf.(fn_link_ofs) = Some pa
  /\ load_stack m' (Vptr sp' Int.zero) Tint tf.(fn_retaddr_ofs) = Some ra
  /\ Mem.free m' sp' 0 tf.(fn_stacksize) = Some m1'
  /\ star step tge
       (State cs fb (Vptr sp' Int.zero) (restore_callee_save fe k) rs m')
    E0 (State cs fb (Vptr sp' Int.zero) k rs1 m')
  /\ agree_regs j (return_regs ls0 ls) rs1
  /\ agree_callee_save (return_regs ls0 ls) ls0
  /\ rs1 IT1 = rs IT1
  /\ Mem.inject j m1 m1'.
Proof.
  intros.
  (* can free *)
  destruct (Mem.range_perm_free m' sp' 0 (fn_stacksize tf)) as [m1' FREE].
  rewrite unfold_transf_function; unfold fn_stacksize. red; intros.
  destruct (zlt ofs (fe_size fe)).
  eapply agree_perm; eauto. omega. 
  replace ofs with ((ofs - fe_size fe) + fe_size fe) by omega.
  eapply Mem.perm_inject with (f := j). eapply agree_inj; eauto. eauto. 
  eapply Mem.free_range_perm; eauto. omega.
  (* inject after free *)
  assert (INJ1: Mem.inject j m1 m1').
  eapply Mem.free_inject with (l := (sp, 0, f.(Linear.fn_stacksize)) :: nil); eauto.
  simpl. rewrite H7. auto.
  intros. exploit agree_inj_unique; eauto. intros [P Q]; subst b1 delta.
  exists 0; exists (Linear.fn_stacksize f); split. auto with coqlib.
  exploit Mem.perm_in_bounds; eauto. 
  rewrite (agree_bounds _ _ H2). auto.
  (* can execute epilogue *)
  exploit restore_callee_save_correct; eauto. intros [rs1 [A [B C]]].
  (* conclusions *)
  exists rs1; exists m1'.
  split. rewrite unfold_transf_function; unfold fn_link_ofs. 
    eapply index_contains_load_stack with (idx := FI_link); eauto with stacking.
  split. rewrite unfold_transf_function; unfold fn_retaddr_ofs. 
    eapply index_contains_load_stack with (idx := FI_retaddr); eauto with stacking.
  split. auto.
  split. eexact A.
  split. red;intros. unfold return_regs. 
    generalize (register_classification r) (int_callee_save_not_destroyed r) (float_callee_save_not_destroyed r); intros.
    destruct (in_dec Loc.eq (R r) temporaries).
    rewrite C; auto. 
    destruct (in_dec Loc.eq (R r) destroyed_at_call).
    rewrite C; auto.
    intuition.
  split. apply agree_callee_save_return_regs.
  split. apply C. apply int_callee_save_not_destroyed. left; simpl; auto. 
  apply float_callee_save_not_destroyed. left; simpl; auto.
  auto.
Qed.

End FRAME_PROPERTIES.

(** * Call stack invariant *)

Inductive match_globalenvs (j: meminj) (bound: Z) : Prop :=
  | match_globalenvs_intro
      (POS: bound > 0)
      (DOMAIN: forall b, b < bound -> j b = Some(b, 0))
      (IMAGE: forall b1 b2 delta, j b1 = Some(b2, delta) -> b2 < bound -> b1 = b2)
      (SYMBOLS: forall id b, Genv.find_symbol ge id = Some b -> b < bound)
      (INFOS: forall b gv, Genv.find_var_info ge b = Some gv -> b < bound).

Inductive match_stacks (j: meminj) (m m': mem): 
       list Linear.stackframe -> list stackframe -> signature -> Z -> Z -> Prop :=
  | match_callstack_empty: forall sg hi bound bound',
      hi <= bound -> hi <= bound' -> match_globalenvs j hi ->
      tailcall_possible sg ->
      match_stacks j m m' nil nil sg bound bound'
  | match_callstack_cons: forall f sp ls c cs fb sp' ra c' cs' sg bound bound' trf
        (INCL: incl c (Linear.fn_code f))
        (WTF: wt_function f)
        (FINDF: Genv.find_funct_ptr tge fb = Some (Internal trf))
        (TRF: transf_function f = OK trf)
        (TRC: transl_code (make_env (function_bounds f)) c = c')
        (WTLS: wt_locset ls)
        (TY_RA: Val.has_type ra Tint)
        (LOC: agree_locsets f ls (parent_locset cs))
        (FRM: agree_frame f j ls (parent_locset cs) m' sp' (parent_sp cs') (parent_ra cs'))
        (SDATA: agree_stackdata f m sp)
        (SPTRS: agree_stackptrs f j sp sp')
        (ARGS: forall ofs ty, In (S (Outgoing ofs ty)) (loc_arguments sg) ->
                             slot_within_bounds f (function_bounds f) (Outgoing ofs ty))
        (STK: match_stacks j m m' cs cs' (Linear.fn_sig f) sp sp')
        (BELOW: sp < bound)
        (BELOW': sp' < bound'),
      match_stacks j m m'
                   (Linear.Stackframe f (Vptr sp Int.zero) ls c :: cs)
                   (Stackframe fb (Vptr sp' Int.zero) ra c' :: cs')
                   sg bound bound'.

(** Invariance with respect to change of bounds. *)

Lemma match_stack_change_bounds:
  forall j m1 m' cs cs' sg bound bound',
  match_stacks j m1 m' cs cs' sg bound bound' ->
  forall xbound xbound',
  bound <= xbound -> bound' <= xbound' ->
  match_stacks j m1 m' cs cs' sg xbound xbound'.
Proof.
  induction 1; intros. 
  apply match_callstack_empty with hi; auto. omega. omega.
  econstructor; eauto. omega. omega.
Qed.

(** Invariance with respect to change of [m]. *)

Lemma match_stack_change_linear_mem:
  forall j m1 m2 m' cs cs' sg bound bound',
  match_stacks j m1 m' cs cs' sg bound bound' ->
  (forall b, b < bound -> Mem.valid_block m1 b -> Mem.valid_block m2 b) ->
  (forall b, b < bound -> Mem.bounds m2 b = Mem.bounds m1 b) ->
  match_stacks j m2 m' cs cs' sg bound bound'.
Proof.
  induction 1; intros.
  econstructor; eauto.
  econstructor; eauto.
  eapply agree_stackdata_invariant; eauto. 
  apply IHmatch_stacks.
  intros. apply H0; auto. omega.
  intros. apply H1. omega.
Qed.

(** Invariance with respect to change of [m']. *)

Lemma match_stack_change_mach_mem:
  forall j m m1' m2' cs cs' sg bound bound',
  match_stacks j m m1' cs cs' sg bound bound' ->
  (forall b, b < bound' -> Mem.valid_block m1' b -> Mem.valid_block m2' b) ->
  (forall b ofs p, b < bound' -> Mem.perm m1' b ofs p -> Mem.perm m2' b ofs p) ->
  (forall chunk b ofs, b < bound' -> Mem.load chunk m2' b ofs = Mem.load chunk m1' b ofs) ->
  match_stacks j m m2' cs cs' sg bound bound'.
Proof.
  induction 1; intros.
  econstructor; eauto.
  econstructor; eauto.
  eapply agree_frame_invariant; eauto. 
  intros. rewrite <- H5. auto.
  apply IHmatch_stacks. 
  intros; apply H0; auto; omega.
  intros; apply H1; auto; omega.
  intros; apply H2; omega.
Qed.

(** Invariance with respect to change of [j]. *)

Lemma match_stacks_change_meminj:
  forall j j' m m',
  inject_incr j j' ->
  inject_separated j j' m m' ->
  forall cs cs' sg bound bound',
  match_stacks j m m' cs cs' sg bound bound' ->
  bound <= Mem.nextblock m -> bound' <= Mem.nextblock m' ->
  match_stacks j' m m' cs cs' sg bound bound'.
Proof.
  induction 3; intros.
  apply match_callstack_empty with hi; auto.
  inv H3. constructor; auto.
  intros. red in H0. case_eq (j b1).
  intros [b' delta'] EQ. rewrite (H _ _ _ EQ) in H3. inv H3. eauto.
  intros EQ. exploit H0; eauto. intros [A B]. elim B. red. omega. 
  econstructor; eauto. 
  eapply agree_frame_inject_incr; eauto.
  eapply agree_stackptrs_inject_incr; eauto. red; omega. red; omega. 
  apply IHmatch_stacks. omega. omega.
Qed.

(** Invariance by external calls. *)

Lemma match_stack_change_extcall:
  forall ec args m1 res t m2 args' m1' res' t' m2' j j',
  external_call ec ge args m1 t res m2 ->
  external_call ec ge args' m1' t' res' m2' ->
  inject_incr j j' ->
  inject_separated j j' m1 m1' ->
  mem_unchanged_on (loc_out_of_reach j m1) m1' m2' ->
  forall cs cs' sg bound bound',
  match_stacks j m1 m1' cs cs' sg bound bound' ->
  bound <= Mem.nextblock m1 -> bound' <= Mem.nextblock m1' ->
  match_stacks j' m2 m2' cs cs' sg bound bound'.
Proof.
  intros until cs. induction 1; intros.
  apply match_callstack_empty with hi; auto.
  inv H6. constructor; auto.
  intros. red in H2. case_eq (j b1).
  intros [b' delta'] EQ. rewrite (H1 _ _ _ EQ) in H6. inv H6. eauto.
  intros EQ. exploit H2; eauto. intros [A B]. elim B. red. omega. 
  assert (REACH: forall ofs,
    0 <= ofs < fe_size (make_env (function_bounds f)) ->
    loc_out_of_reach j m1 sp' ofs).
  intros; red; intros. exploit agree_inj_unique; eauto. intros [EQ1 EQ2]; subst.
  rewrite (agree_bounds _ _ _ SDATA). unfold fst. left. omega. 
  econstructor; eauto.
  apply agree_frame_inject_incr with j; auto.
  apply agree_frame_invariant with ls (parent_locset cs) m1'; auto.
  red in H3. intros. apply H3. intros. apply REACH. omega. auto. 
  intros. eapply external_call_valid_block; eauto.
  intros. apply H3. apply REACH. omega. auto.
  apply agree_stackdata_invariant with m1; auto. 
  intros. eapply external_call_valid_block; eauto.
  eapply external_call_bounds; eauto. eapply agree_valid_linear; eauto. 
  eapply agree_stackptrs_inject_incr; eauto.  eapply agree_valid_linear; eauto. eapply agree_valid_mach; eauto.
  apply IHmatch_stacks. omega. omega. 
Qed.

(** Invariance with respect to change of signature *)

Lemma match_stacks_change_sig:
  forall sg1 j m m' cs cs' sg bound bound',
  match_stacks j m m' cs cs' sg bound bound' ->
  tailcall_possible sg1 ->
  match_stacks j m m' cs cs' sg1 bound bound'.
Proof.
  induction 1; intros. econstructor; eauto. econstructor; eauto. 
  intros. elim (H0 _ H1). 
Qed.

(** [match_stacks] implies [match_globalenvs], which implies [meminj_preserves_globals]. *)

Lemma match_stacks_globalenvs:
  forall j m m' cs cs' sg bound bound',
  match_stacks j m m' cs cs' sg bound bound' ->
  exists hi, match_globalenvs j hi.
Proof.
  induction 1. exists hi; auto. auto.
Qed.

Lemma match_globalenvs_preserves_globals:
  forall j hi,
  match_globalenvs j hi ->
  meminj_preserves_globals ge j.
Proof.
  intros. inv H. split. eauto. split. eauto. intros. symmetry. eauto. 
Qed.

(** Typing properties of [match_stacks]. *)

Lemma match_stacks_wt_locset:
  forall j m m' cs cs' sg bound bound',
  match_stacks j m m' cs cs' sg bound bound' ->
  wt_locset (parent_locset cs).
Proof.
  induction 1; simpl.
  unfold Locmap.init; red; intros; red; auto.
  auto.
Qed.

Lemma match_stacks_type_sp:
  forall j m m' cs cs' sg bound bound',
  match_stacks j m m' cs cs' sg bound bound' ->
  Val.has_type (parent_sp cs') Tint.
Proof.
  induction 1; simpl; auto.
Qed.

Lemma match_stacks_type_retaddr:
  forall j m m' cs cs' sg bound bound',
  match_stacks j m m' cs cs' sg bound bound' ->
  Val.has_type (parent_ra cs') Tint.
Proof.
  induction 1; simpl; auto.
Qed.

(** * Semantic preservation *)

(** Preservation of code labels through the translation. *)

Section LABELS.

Remark find_label_fold_right:
  forall (A: Type) (fn: A -> Mach.code -> Mach.code) lbl,
  (forall x k, Mach.find_label lbl (fn x k) = Mach.find_label lbl k) ->  forall (args: list A) k,
  Mach.find_label lbl (List.fold_right fn k args) = Mach.find_label lbl k.
Proof.
  induction args; simpl. auto. 
  intros. rewrite H. auto.
Qed.

Remark find_label_save_callee_save:
  forall fe lbl k,
  Mach.find_label lbl (save_callee_save fe k) = Mach.find_label lbl k.
Proof.
  intros. unfold save_callee_save, save_callee_save_int, save_callee_save_float, save_callee_save_regs.
  repeat rewrite find_label_fold_right. reflexivity.
  intros. unfold save_callee_save_reg. 
  case (zlt (index_float_callee_save x) (fe_num_float_callee_save fe));
  intro; reflexivity.
  intros. unfold save_callee_save_reg.  
  case (zlt (index_int_callee_save x) (fe_num_int_callee_save fe));
  intro; reflexivity.
Qed.

Remark find_label_restore_callee_save:
  forall fe lbl k,
  Mach.find_label lbl (restore_callee_save fe k) = Mach.find_label lbl k.
Proof.
  intros. unfold restore_callee_save, restore_callee_save_int, restore_callee_save_float, restore_callee_save_regs.
  repeat rewrite find_label_fold_right. reflexivity.
  intros. unfold restore_callee_save_reg. 
  case (zlt (index_float_callee_save x) (fe_num_float_callee_save fe));
  intro; reflexivity.
  intros. unfold restore_callee_save_reg. 
  case (zlt (index_int_callee_save x) (fe_num_int_callee_save fe));
  intro; reflexivity.
Qed.

Lemma find_label_transl_code:
  forall fe lbl c,
  Mach.find_label lbl (transl_code fe c) =
    option_map (transl_code fe) (Linear.find_label lbl c).
Proof.
  induction c; simpl; intros.
  auto.
  destruct a; unfold transl_instr; auto.
  destruct s; simpl; auto.
  destruct s; simpl; auto.
  rewrite find_label_restore_callee_save. auto.
  simpl. case (peq lbl l); intro. reflexivity. auto.
  rewrite find_label_restore_callee_save. auto.
Qed.

Lemma transl_find_label:
  forall f tf lbl c,
  transf_function f = OK tf ->
  Linear.find_label lbl f.(Linear.fn_code) = Some c ->
  Mach.find_label lbl tf.(Mach.fn_code) = 
    Some (transl_code (make_env (function_bounds f)) c).
Proof.
  intros. rewrite (unfold_transf_function _ _ H).  simpl. 
  unfold transl_body. rewrite find_label_save_callee_save.
  rewrite find_label_transl_code. rewrite H0. reflexivity.
Qed.

End LABELS.

(** Code inclusion property for Linear executions. *)

Lemma find_label_incl:
  forall lbl c c', 
  Linear.find_label lbl c = Some c' -> incl c' c.
Proof.
  induction c; simpl.
  intros; discriminate.
  intro c'. case (Linear.is_label lbl a); intros.
  injection H; intro; subst c'. red; intros; auto with coqlib. 
  apply incl_tl. auto.
Qed.

(** Preservation / translation of global symbols and functions. *)

Lemma symbols_preserved:
  forall id, Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof.
  intros. unfold ge, tge. 
  apply Genv.find_symbol_transf_partial with transf_fundef.
  exact TRANSF. 
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros. unfold ge, tge. 
  apply Genv.find_var_info_transf_partial with transf_fundef.
  exact TRANSF. 
Qed.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
Proof
  (Genv.find_funct_transf_partial transf_fundef _ TRANSF).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  exists tf,
  Genv.find_funct_ptr tge v = Some tf /\ transf_fundef f = OK tf.
Proof
  (Genv.find_funct_ptr_transf_partial transf_fundef _ TRANSF).

Lemma sig_preserved:
  forall f tf, transf_fundef f = OK tf -> Mach.funsig tf = Linear.funsig f.
Proof.
  intros until tf; unfold transf_fundef, transf_partial_fundef.
  destruct f; intros; monadInv H.
  rewrite (unfold_transf_function _ _ EQ). auto. 
  auto.
Qed.

Lemma find_function_translated:
  forall j ls rs m m' cs cs' sg bound bound' ros f,
  agree_regs j ls rs ->
  match_stacks j m m' cs cs' sg bound bound' ->
  Linear.find_function ge ros ls = Some f ->
  exists bf, exists tf,
     find_function_ptr tge ros rs = Some bf
  /\ Genv.find_funct_ptr tge bf = Some tf
  /\ transf_fundef f = OK tf.
Proof.
  intros until f; intros AG MS FF.
  exploit match_stacks_globalenvs; eauto. intros [hi MG]. 
  destruct ros; simpl in FF.
  exploit Genv.find_funct_inv; eauto. intros [b EQ]. rewrite EQ in FF. 
  rewrite Genv.find_funct_find_funct_ptr in FF. 
  exploit function_ptr_translated; eauto. intros [tf [A B]].
  exists b; exists tf; split; auto. simpl.
  generalize (AG m0). rewrite EQ. intro INJ. inv INJ.
  exploit Genv.find_funct_ptr_negative. unfold ge in FF; eexact FF. intros. 
  inv MG. rewrite (DOMAIN b) in H2. inv H2. auto. omega. 
  revert FF. case_eq (Genv.find_symbol ge i); intros; try discriminate. 
  exploit function_ptr_translated; eauto. intros [tf [A B]].
  exists b; exists tf; split; auto. simpl. 
  rewrite symbols_preserved. auto.
Qed.

Hypothesis wt_prog: wt_program prog.

Lemma find_function_well_typed:
  forall ros ls f,
  Linear.find_function ge ros ls = Some f -> wt_fundef f.
Proof.
  intros until f; destruct ros; simpl; unfold ge.
  intro. eapply Genv.find_funct_prop; eauto.
  destruct (Genv.find_symbol (Genv.globalenv prog) i); try congruence.
  intro. eapply Genv.find_funct_ptr_prop; eauto. 
Qed.

(** Preservation of the arguments to an external call. *)

Section EXTERNAL_ARGUMENTS.

Variable j: meminj.
Variables m m': mem.
Variable cs: list Linear.stackframe.
Variable cs': list stackframe.
Variable sg: signature.
Variables bound bound': Z.
Hypothesis MS: match_stacks j m m' cs cs' sg bound bound'.
Variable ls: locset.
Variable rs: regset.
Hypothesis AGR: agree_regs j ls rs.
Hypothesis AGCS: agree_callee_save ls (parent_locset cs).

Lemma transl_external_argument:
  forall l,
  In l (loc_arguments sg) ->
  exists v, extcall_arg rs m' (parent_sp cs') l v /\ val_inject j (ls l) v.
Proof.
  intros.
  assert (loc_argument_acceptable l). apply loc_arguments_acceptable with sg; auto.
  destruct l; red in H0.
  exists (rs m0); split. constructor. auto. 
  destruct s; try contradiction.
  inv MS. 
  elim (H4 _ H).
  unfold parent_sp. 
  exploit agree_outgoing; eauto. intros [v [A B]].
  exists v; split.
  constructor. 
  eapply index_contains_load_stack with (idx := FI_arg z t); eauto. 
  red in AGCS. rewrite AGCS; auto.
Qed.

Lemma transl_external_arguments_rec:
  forall locs,
  incl locs (loc_arguments sg) ->
  exists vl,
  extcall_args rs m' (parent_sp cs') locs vl /\ val_list_inject j ls##locs vl.
Proof.
  induction locs; simpl; intros.
  exists (@nil val); split. constructor. constructor.
  exploit transl_external_argument; eauto with coqlib. intros [v [A B]].
  exploit IHlocs; eauto with coqlib. intros [vl [C D]].
  exists (v :: vl); split; constructor; auto.
Qed.

Lemma transl_external_arguments:
  exists vl,
  extcall_arguments rs m' (parent_sp cs') sg vl /\
  val_list_inject j (ls ## (loc_arguments sg)) vl.
Proof.
  unfold extcall_arguments. 
  apply transl_external_arguments_rec.
  auto with coqlib.
Qed.

End EXTERNAL_ARGUMENTS.

(** The proof of semantic preservation relies on simulation diagrams
  of the following form:
<<
           st1 --------------- st2
            |                   |
           t|                  +|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  Matching between source and target states is defined by [match_states]
  below.  It implies:
- Agreement between, on the Linear side, the location sets [ls]
  and [parent_locset s] of the current function and its caller,
  and on the Mach side the register set [rs], the frame [fr]
  and the caller's frame [parent_frame ts].
- Inclusion between the Linear code [c] and the code of the
  function [f] being executed.
- Well-typedness of [f].
*)

Inductive match_states: Linear.state -> Machconcr.state -> Prop :=
  | match_states_intro:
      forall cs f sp c ls m cs' fb sp' rs m' j tf
        (MINJ: Mem.inject j m m')
        (STACKS: match_stacks j m m' cs cs' f.(Linear.fn_sig) sp sp')
        (TRANSL: transf_function f = OK tf)
        (FIND: Genv.find_funct_ptr tge fb = Some (Internal tf))
        (WTF: wt_function f)
        (WTLS: wt_locset ls)
        (AGREGS: agree_regs j ls rs)
        (AGLOCS: agree_locsets f ls (parent_locset cs))
        (AGFRAME: agree_frame f j ls (parent_locset cs) m' sp' (parent_sp cs') (parent_ra cs'))
        (AGSTKD: agree_stackdata f m sp)
        (AGPTRS: agree_stackptrs f j sp sp')
        (INCL: incl c (Linear.fn_code f)),
      match_states (Linear.State cs f (Vptr sp Int.zero) c ls m)
                  (Machconcr.State cs' fb (Vptr sp' Int.zero) (transl_code (make_env (function_bounds f)) c) rs m')
  | match_states_call:
      forall cs f ls m cs' fb rs m' j tf
        (MINJ: Mem.inject j m m')
        (STACKS: match_stacks j m m' cs cs' (Linear.funsig f) (Mem.nextblock m) (Mem.nextblock m'))
        (TRANSL: transf_fundef f = OK tf)
        (FIND: Genv.find_funct_ptr tge fb = Some tf)
        (WTF: wt_fundef f)
        (WTLS: wt_locset ls)
        (AGREGS: agree_regs j ls rs)
        (AGLOCS: agree_callee_save ls (parent_locset cs)),
      match_states (Linear.Callstate cs f ls m)
                  (Machconcr.Callstate cs' fb rs m')
  | match_states_return:
      forall cs ls m cs' rs m' j sg 
        (MINJ: Mem.inject j m m')
        (STACKS: match_stacks j m m' cs cs' sg (Mem.nextblock m) (Mem.nextblock m'))
        (WTLS: wt_locset ls)
        (AGREGS: agree_regs j ls rs)
        (AGLOCS: agree_callee_save ls (parent_locset cs)),
      match_states (Linear.Returnstate cs ls m)
                  (Machconcr.Returnstate cs' rs m').

Remark incoming_slot_in_parameters:
  forall ofs ty sg,
  In (S (Incoming ofs ty)) (loc_parameters sg) ->
  In (S (Outgoing ofs ty)) (loc_arguments sg).
Proof.
  intros.
  unfold loc_parameters in H. 
  change (S (Incoming ofs ty)) with (parameter_of_argument (S (Outgoing ofs ty))) in H.
  exploit list_in_map_inv. eexact H. intros [x [A B]]. simpl in A.
  exploit loc_arguments_acceptable; eauto. unfold loc_argument_acceptable; intros.
  destruct x; simpl in A; try discriminate.
  destruct s; try contradiction. 
  inv A. auto.
Qed. 

Theorem transf_step_correct:
  forall s1 t s2, Linear.step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  exists s2', plus Machconcr.step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  assert (RED: forall f i c,
          transl_code (make_env (function_bounds f)) (i :: c) = 
          transl_instr (make_env (function_bounds f)) i
                       (transl_code (make_env (function_bounds f)) c)).
    intros. reflexivity.
  induction 1; intros;
  try inv MS;
  try rewrite RED;
  try (generalize (WTF _ (INCL _ (in_eq _ _))); intro WTI);
  try (generalize (function_is_within_bounds f WTF _ (INCL _ (in_eq _ _)));
       intro BOUND; simpl in BOUND);
  unfold transl_instr.

  (* Lgetstack *)
  inv WTI. destruct BOUND. unfold undef_getstack; destruct sl.
  (* Lgetstack, local *)
  exploit agree_locals; eauto. intros [v [A B]].
  econstructor; split.
  apply plus_one. apply exec_Mgetstack. 
  eapply index_contains_load_stack; eauto.
  econstructor; eauto with coqlib.
  eapply wt_setloc; eauto. simpl. rewrite <- H1. apply WTLS. 
  apply agree_regs_set_reg; auto.
  apply agree_locsets_set_reg; auto. 
  apply agree_frame_set_reg; auto.
  (* Lgetstack, incoming *)
  red in H2. exploit incoming_slot_in_parameters; eauto. intros IN_ARGS.
  inv STACKS. elim (H6 _ IN_ARGS). 
  exploit agree_outgoing. eexact FRM. eapply ARGS; eauto.
  intros [v [A B]].
  econstructor; split.
  apply plus_one. eapply exec_Mgetparam; eauto. 
  rewrite (unfold_transf_function _ _ TRANSL). unfold fn_link_ofs. 
  eapply index_contains_load_stack with (idx := FI_link). eauto. eapply agree_link; eauto. 
  simpl parent_sp.
  change (offset_of_index (make_env (function_bounds f)) (FI_arg z t))
    with (offset_of_index (make_env (function_bounds f0)) (FI_arg z t)).
  eapply index_contains_load_stack with (idx := FI_arg z t). eauto. eauto.
  exploit agree_incoming; eauto. intros EQ; simpl in EQ.
  econstructor; eauto with coqlib. econstructor; eauto.
  eapply wt_setloc; eauto. simpl. rewrite <- H1. apply WTLS. 
  apply wt_setloc; auto. simpl; auto. 
  apply agree_regs_set_reg. apply agree_regs_set_reg. auto. auto. congruence. 
  apply agree_locsets_set_reg; auto. apply agree_locsets_set_reg; auto.
  apply temporary_within_bounds. unfold temporaries; auto with coqlib.
  apply agree_frame_set_reg; auto. apply agree_frame_set_reg; auto.
  (* Lgetstack, outgoing *)
  exploit agree_outgoing; eauto. intros [v [A B]].
  econstructor; split.
  apply plus_one. apply exec_Mgetstack. 
  eapply index_contains_load_stack; eauto.
  econstructor; eauto with coqlib.
  eapply wt_setloc; eauto. simpl. rewrite <- H1. apply WTLS. 
  apply agree_regs_set_reg; auto.
  apply agree_locsets_set_reg; auto. 
  apply agree_frame_set_reg; auto.

  (* Lsetstack *)
  inv WTI.
  set (idx := match sl with
              | Local ofs ty => FI_local ofs ty
              | Incoming ofs ty => FI_link (*dummy*)
              | Outgoing ofs ty => FI_arg ofs ty
              end).
  assert (index_valid f idx).
    unfold idx; destruct sl.
    apply index_local_valid; auto.
    red; auto.
    apply index_arg_valid; auto.
  exploit store_index_succeeds; eauto. eapply agree_perm; eauto.
  instantiate (1 := rs0 r). intros [m1' STORE].
  econstructor; split.
  apply plus_one. destruct sl; simpl in H3.
    econstructor. eapply store_stack_succeeds with (idx := idx); eauto. 
    contradiction.
    econstructor. eapply store_stack_succeeds with (idx := idx); eauto. 
  econstructor; eauto with coqlib.
  eapply Mem.store_outside_inject; eauto. 
    intros. exploit agree_inj_unique; eauto. intros [EQ1 EQ2]; subst b' delta.
    right. rewrite (agree_bounds _ _ _ AGSTKD). simpl fst. rewrite Zplus_0_l. 
    rewrite size_type_chunk. apply offset_of_index_valid; auto.
  apply match_stack_change_mach_mem with m'; auto.
  eauto with mem. eauto with mem. intros. eapply Mem.load_store_other; eauto. left; unfold block; omega.
  eapply wt_setloc; eauto. simpl. rewrite H1. apply WTLS. 
  apply agree_regs_set_slot; auto.
  apply agree_locsets_set_slot; auto.
  destruct sl.
    eapply agree_frame_set_local; eauto. simpl in H1; rewrite H1; apply WTLS.
    simpl in H3; contradiction.
    eapply agree_frame_set_outgoing; eauto. simpl in H1; rewrite H1; apply WTLS.

  (* Lop *)
  assert (meminj_preserves_globals ge j).
    exploit match_stacks_globalenvs; eauto. intros [hi MG].
    eapply match_globalenvs_preserves_globals; eauto.
  assert (Val.has_type v (mreg_type res)).
    inv WTI. simpl in H. inv H. rewrite <- H2. apply WTLS. 
    replace (mreg_type res) with (snd (type_of_operation op)).
    eapply type_of_operation_sound; eauto. 
    rewrite <- H5; auto.
  assert (exists v',
          eval_operation ge (Vptr sp' Int.zero) (transl_op (make_env (function_bounds f)) op) rs0##args = Some v'
       /\ val_inject j v v').
  eapply eval_operation_inject; eauto. eapply agree_inj; eauto. eapply agree_reglist; eauto.
  destruct H2 as [v' [A B]].
  econstructor; split. 
  apply plus_one. constructor. 
  instantiate (1 := v'). rewrite <- A. apply eval_operation_preserved. 
  exact symbols_preserved.
  econstructor; eauto.
  apply wt_setloc. assumption. apply wt_undef_op; auto. 
  apply agree_regs_set_reg; auto. apply agree_regs_undef_op; auto. 
  apply agree_locsets_set_reg; auto. apply agree_locsets_undef_op; auto.
  
inv WTI.
  apply eval_oeexact A. 
  
    

  inv WTI.
  
  admit.

  (* Lload *)
  admit.

  (* Lstore *)
  admit.

  (* Lcall *)
  exploit find_function_translated; eauto. intros [bf [tf' [A [B C]]]].
  exploit Asmgenretaddr.return_address_exists.
    instantiate (2 := transl_code (make_env (function_bounds f)) b). 
    instantiate (1 := tf).
    admit.
  intros [ra D].
  econstructor; split.
  apply plus_one. econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto with coqlib.
  simpl; auto.
  intros; red. split.
    generalize (loc_arguments_acceptable _ _ H0). simpl. omega.
    apply Zle_trans with (size_arguments (Linear.funsig f')); auto.
    apply loc_arguments_bounded; auto.
  eapply agree_valid_linear; eauto.
  eapply agree_valid_mach; eauto.
  eapply find_function_well_typed; eauto.
  simpl; red; auto.

  (* Ltailcall *)
  exploit find_function_translated; eauto. intros [bf [tf' [A [B C]]]].
  exploit function_epilogue_correct; eauto. eapply match_stacks_wt_locset; eauto.
  intros [rs1 [m1' [P [Q [R [S [T [U [V W]]]]]]]]].
  econstructor; split.
  eapply plus_right. eexact S. econstructor; eauto.
  replace (find_function_ptr tge ros rs1)
     with (find_function_ptr tge ros rs0). eauto.
  destruct ros; simpl; auto. inv WTI. rewrite V; auto. 
  traceEq.
  econstructor; eauto.
  inv WTI. apply match_stacks_change_sig with (Linear.fn_sig f); auto.
  apply match_stack_change_bounds with stk sp'.
  apply match_stack_change_linear_mem with m. 
  apply match_stack_change_mach_mem with m'0.
  auto. 
  eauto with mem. intros. eapply Mem.perm_free_1; eauto. left; unfold block; omega. 
  intros. eapply Mem.load_free; eauto. left; unfold block; omega.
  eauto with mem. intros. eapply Mem.bounds_free; eauto.
  apply Zlt_le_weak. change (Mem.valid_block m' stk). eapply Mem.valid_block_free_1; eauto. eapply agree_valid_linear; eauto. 
  apply Zlt_le_weak. change (Mem.valid_block m1' sp'). eapply Mem.valid_block_free_1; eauto. eapply agree_valid_mach; eauto. 
  eapply find_function_well_typed; eauto.
  apply wt_return_regs; auto. eapply match_stacks_wt_locset; eauto.

  (* Lbuiltin *)
  admit.

  (* Llabel *)
  econstructor; split.
  apply plus_one; apply exec_Mlabel.
  econstructor; eauto with coqlib.

  (* Lgoto *)
  econstructor; split.
  apply plus_one; eapply exec_Mgoto; eauto.
  apply transl_find_label; eauto.
  econstructor; eauto. 
  eapply find_label_incl; eauto.

  (* Lcond, true *)
  admit.

  (* Lcond, false *)
  admit.

  (* Ljumptable *)
  assert (rs0 arg = Vint n).
    generalize (AGREGS arg). rewrite H. intro IJ; inv IJ; auto.
  econstructor; split.
  apply plus_one; eapply exec_Mjumptable; eauto. 
  apply transl_find_label; eauto.
  econstructor; eauto.
  apply wt_undef_temps; auto.
  apply agree_regs_undef_temps; auto.
  apply agree_locsets_undef_temps; auto.
  admit.
  eapply find_label_incl; eauto.

  (* Lreturn *)
  exploit function_epilogue_correct; eauto. eapply match_stacks_wt_locset; eauto.
  intros [rs1 [m1' [P [Q [R [S [T [U [V W]]]]]]]]].
  econstructor; split.
  eapply plus_right. eexact S. econstructor; eauto.
  traceEq.
  econstructor; eauto.
  apply match_stack_change_bounds with stk sp'.
  apply match_stack_change_linear_mem with m. 
  apply match_stack_change_mach_mem with m'0.
  eauto. 
  eauto with mem. intros. eapply Mem.perm_free_1; eauto. left; unfold block; omega. 
  intros. eapply Mem.load_free; eauto. left; unfold block; omega.
  eauto with mem. intros. eapply Mem.bounds_free; eauto.
  apply Zlt_le_weak. change (Mem.valid_block m' stk). eapply Mem.valid_block_free_1; eauto. eapply agree_valid_linear; eauto. 
  apply Zlt_le_weak. change (Mem.valid_block m1' sp'). eapply Mem.valid_block_free_1; eauto. eapply agree_valid_mach; eauto. 
  apply wt_return_regs; auto. eapply match_stacks_wt_locset; eauto.

  (* internal function *)
  revert TRANSL. unfold transf_fundef, transf_partial_fundef.
  caseEq (transf_function f); simpl; try congruence.
  intros tfn TRANSL EQ. inversion EQ; clear EQ; subst tf.
  inversion WTF as [|f' WTFN]. subst f'.
  exploit function_prologue_correct; eauto.
  eapply match_stacks_type_sp; eauto. 
  eapply match_stacks_type_retaddr; eauto.
  intros [j' [m2' [sp' [m3' [m4' [m5' [A [B [C [D [E [F [G [J [K [L [M [N P]]]]]]]]]]]]]]]]]].
  econstructor; split.
  eapply plus_left. econstructor; eauto. 
  rewrite (unfold_transf_function _ _ TRANSL). unfold fn_code. unfold transl_body. 
  eexact D. traceEq.
  generalize (Mem.alloc_result _ _ _ _ _ H). intro SP_EQ. 
  generalize (Mem.alloc_result _ _ _ _ _ A). intro SP'_EQ.
  econstructor; eauto. 
  apply match_stack_change_mach_mem with m'0.
  apply match_stack_change_linear_mem with m.
  rewrite SP_EQ; rewrite SP'_EQ.
  apply match_stacks_change_meminj with j; auto. omega. omega.
  eauto with mem. intros. eapply Mem.bounds_alloc_other; eauto. unfold block; omega. 
  intros. eapply stores_in_frame_valid; eauto with mem. 
  intros. eapply stores_in_frame_perm; eauto with mem.
  intros. transitivity (Mem.load chunk m2' b ofs). eapply stores_in_frame_contents; eauto.
  eapply Mem.load_alloc_unchanged; eauto. red. congruence.
  apply wt_call_regs; auto.
  eapply agree_callee_save_agree_locsets; eauto.
  apply agree_frame_invariant with (call_regs rs) rs m5'; auto.
  intros. symmetry. apply AGLOCS. auto.
  apply incl_refl.

  (* external function *)
  simpl in TRANSL. inversion TRANSL; subst tf.
  inversion WTF. subst ef0.
  exploit transl_external_arguments; eauto. intros [vl [ARGS VINJ]].
  exploit external_call_mem_inject; eauto. 
  exploit match_stacks_globalenvs; eauto. intros [hi MG]. eapply match_globalenvs_preserves_globals; eauto.
  intros [j' [res' [m1' [A [B [C [D [E [F G]]]]]]]]].
  econstructor; split.
  apply plus_one. eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto.
  apply match_stack_change_bounds with (Mem.nextblock m) (Mem.nextblock m'0).
  eapply match_stack_change_extcall; eauto. omega. omega.
  exploit external_call_valid_block. eexact H. 
    instantiate (1 := (Mem.nextblock m - 1)). red; omega. unfold Mem.valid_block; omega.
  exploit external_call_valid_block. eexact A. 
    instantiate (1 := (Mem.nextblock m'0 - 1)). red; omega. unfold Mem.valid_block; omega.
  apply wt_setloc; auto. simpl. rewrite loc_result_type.
  change (Val.has_type res (proj_sig_res (ef_sig ef))). 
  eapply external_call_well_typed; eauto. 
  apply agree_regs_set_reg; auto. apply agree_regs_inject_incr with j; auto. 
  apply agree_callee_save_set_result; auto. 

  (* return *)
  inv STACKS. simpl in AGLOCS.  
  econstructor; split.
  apply plus_one. apply exec_return. 
  econstructor; eauto.
  apply agree_callee_save_agree_locsets_2 with rs0; auto.
  apply agree_frame_invariant with rs0 (parent_locset s) m'; auto.
  intros. apply AGLOCS. destruct l; tauto.
Qed.

Lemma transf_initial_states:
  forall st1, Linear.initial_state prog st1 ->
  exists st2, Machabstr.initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated; eauto. intros [tf [FIND TR]].
  econstructor; split.
  econstructor. 
  eapply Genv.init_mem_transf_partial; eauto.
  rewrite (transform_partial_program_main _ _ TRANSF). 
  rewrite symbols_preserved. eauto.
  eauto. 
  econstructor; eauto. constructor. 
  eapply Genv.find_funct_ptr_prop; eauto.
  intros. rewrite H3 in H5. simpl in H5. contradiction.
  simpl; red; auto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r, 
  match_states st1 st2 -> Linear.final_state st1 r -> Machabstr.final_state st2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. econstructor. rewrite AG1; auto.
Qed.

Theorem transf_program_correct:
  forall (beh: program_behavior), not_wrong beh ->
  Linear.exec_program prog beh -> Machabstr.exec_program tprog beh.
Proof.
  unfold Linear.exec_program, Machabstr.exec_program; intros.
  eapply simulation_plus_preservation; eauto.
  eexact transf_initial_states.
  eexact transf_final_states.
  eexact transf_step_correct. 
Qed.

End PRESERVATION.
