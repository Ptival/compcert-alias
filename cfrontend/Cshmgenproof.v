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

(** * Correctness of the translation from Clight to C#minor. *)

Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import AST.
Require Import Values.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Csyntax.
Require Import Csem.
Require Import Clight.
Require Import Cminor.
Require Import Csharpminor.
Require Import Cshmgen.

(** * Properties of operations over types *)

Remark type_of_kind_of_type:
  forall t k,
  var_kind_of_type t = OK k -> type_of_kind k = typ_of_type t.
Proof.
  intros. destruct t; try (monadInv H); auto. 
  destruct i; destruct s; monadInv H; auto.
  destruct f; monadInv H; auto.
Qed.

Remark transl_params_types:
  forall p tp,
  transl_vars p = OK tp ->
  map type_of_kind (map variable_kind tp) = typlist_of_typelist (type_of_params p).
Proof.
  induction p; simpl; intros. 
  inv H. auto.
  destruct a as [id ty]. destruct (var_kind_of_type ty) as []_eqn; monadInv H.
  simpl. f_equal; auto. apply type_of_kind_of_type; auto.
Qed.

Lemma transl_fundef_sig1:
  forall f tf args res,
  transl_fundef f = OK tf ->
  classify_fun (type_of_fundef f) = fun_case_f args res ->
  funsig tf = signature_of_type args res.
Proof.
  intros. destruct f; simpl in *. 
  monadInv H. monadInv EQ. simpl. inversion H0.    
  unfold fn_sig; simpl. unfold signature_of_type. f_equal. 
  apply transl_params_types; auto.
  destruct (list_typ_eq (sig_args (ef_sig e)) (typlist_of_typelist t)); simpl in H.
  destruct (opt_typ_eq (sig_res (ef_sig e)) (opttyp_of_type t0)); simpl in H.
  inv H. simpl. destruct (ef_sig e); simpl in *. inv H0.
  unfold signature_of_type. auto.
  congruence.
  congruence.
Qed.

Lemma transl_fundef_sig2:
  forall f tf args res,
  transl_fundef f = OK tf ->
  type_of_fundef f = Tfunction args res ->
  funsig tf = signature_of_type args res.
Proof.
  intros. eapply transl_fundef_sig1; eauto.
  rewrite H0; reflexivity.
Qed.

Lemma var_kind_by_value:
  forall ty chunk,
  access_mode ty = By_value chunk ->
  var_kind_of_type ty = OK(Vscalar chunk).
Proof.
  intros ty chunk; destruct ty; simpl; try congruence.
  destruct i; try congruence; destruct s; congruence.
  destruct f; congruence.
Qed.

Lemma var_kind_by_reference:
  forall ty vk,
  access_mode ty = By_reference \/ access_mode ty = By_copy ->
  var_kind_of_type ty = OK vk ->
  vk = Varray (Csyntax.sizeof ty) (Csyntax.alignof ty).
Proof.
  intros ty vk; destruct ty; simpl; try intuition congruence.
  destruct i; try congruence; destruct s; intuition congruence.
  destruct f; intuition congruence.
Qed.

Lemma sizeof_var_kind_of_type:
  forall ty vk,
  var_kind_of_type ty = OK vk ->
  Csharpminor.sizeof vk = Csyntax.sizeof ty.
Proof.
  intros ty vk.
  assert (sizeof (Varray (Csyntax.sizeof ty) (Csyntax.alignof ty)) = Csyntax.sizeof ty).
    simpl. rewrite Zmax_spec. apply zlt_false. 
    generalize (Csyntax.sizeof_pos ty). omega.
  destruct ty; try (destruct i; try destruct s); try (destruct f); 
  simpl; intro EQ; inversion EQ; subst vk; auto.
Qed.

Remark cast_int_int_normalized:
  forall sz si a chunk n,
  access_mode (Tint sz si a) = By_value chunk ->
  val_normalized (Vint (cast_int_int sz si n)) chunk.
Proof.
  unfold access_mode, cast_int_int, val_normalized; intros. destruct sz.
  destruct si; inv H; simpl.
  rewrite Int.sign_ext_idem; auto. compute; auto.
  rewrite Int.zero_ext_idem; auto. compute; auto.
  destruct si; inv H; simpl.
  rewrite Int.sign_ext_idem; auto. compute; auto.
  rewrite Int.zero_ext_idem; auto. compute; auto.
  inv H. auto.
  inv H. destruct (Int.eq n Int.zero); auto.
Qed.

Remark cast_float_float_normalized:
  forall sz a chunk n,
  access_mode (Tfloat sz a) = By_value chunk ->
  val_normalized (Vfloat (cast_float_float sz n)) chunk.
Proof.
  unfold access_mode, cast_float_float, val_normalized; intros. 
  destruct sz; inv H; simpl.
  rewrite Float.singleoffloat_idem. auto.
  auto.
Qed.

Remark cast_neutral_normalized:
  forall ty1 ty2 chunk,
  classify_cast ty1 ty2 = cast_case_neutral ->
  access_mode ty2 = By_value chunk ->
  chunk = Mint32.
Proof.
  intros. functional inversion H; subst; simpl in H0; congruence.
Qed.

Lemma cast_result_normalized:
  forall chunk v1 ty1 ty2 v2,
  sem_cast v1 ty1 ty2 = Some v2 ->
  access_mode ty2 = By_value chunk ->
  val_normalized v2 chunk.
Proof.
  intros. functional inversion H; subst.
  rewrite (cast_neutral_normalized ty1 ty2 chunk); auto. red; auto.
  rewrite (cast_neutral_normalized ty1 ty2 chunk); auto. red; auto.
  functional inversion H2; subst. eapply cast_int_int_normalized; eauto.
  functional inversion H2; subst. eapply cast_float_float_normalized; eauto.
  functional inversion H2; subst. eapply cast_float_float_normalized; eauto.
  functional inversion H2; subst. eapply cast_int_int_normalized; eauto.
  assert (chunk = Mint8unsigned). 
    functional inversion H2; subst; simpl in H0; try congruence.
  subst chunk. destruct (Int.eq i Int.zero); red; auto.
  assert (chunk = Mint8unsigned). 
    functional inversion H2; subst; simpl in H0; try congruence.
  subst chunk. red; auto.
  functional inversion H2; subst. simpl in H0. inv H0. red; auto.
  functional inversion H2; subst. simpl in H0. inv H0. red; auto.
  functional inversion H2; subst. simpl in H0. congruence.
  functional inversion H2; subst. simpl in H0. congruence.
  functional inversion H5; subst. simpl in H0. congruence.
Qed.

Definition val_casted (v: val) (ty: type) : Prop :=
  exists v0, exists ty0, sem_cast v0 ty0 ty = Some v.

Lemma val_casted_normalized:
  forall v ty chunk,
  val_casted v ty -> access_mode ty = By_value chunk -> val_normalized v chunk.
Proof.
  intros. destruct H as [v0 [ty0 CAST]]. eapply cast_result_normalized; eauto.
Qed.

Fixpoint val_casted_list (vl: list val) (tyl: typelist) {struct vl}: Prop :=
  match vl, tyl with
  | nil, Tnil => True
  | v1 :: vl', Tcons ty1 tyl' => val_casted v1 ty1 /\ val_casted_list vl' tyl'
  | _, _ => False
  end.

Lemma eval_exprlist_casted:
  forall ge e le m al tyl vl,
  Clight.eval_exprlist ge e le m al tyl vl ->
  val_casted_list vl tyl.
Proof.
  induction 1; simpl.
  auto.
  split. exists v1; exists (typeof a); auto. eauto.
Qed.

(** * Properties of the translation functions *)

Lemma map_partial_names:
  forall (A B: Type) (f: A -> res B)
         (l: list (ident * A)) (tl: list (ident * B)),
  map_partial prefix_var_name f l = OK tl ->
  List.map (@fst ident B) tl = List.map (@fst ident A) l.
Proof.
  induction l; simpl.
  intros. inversion H. reflexivity.
  intro tl. destruct a as [id x]. destruct (f x); try congruence.
  caseEq (map_partial prefix_var_name f l); simpl; intros; try congruence.
  inv H0. simpl. decEq. auto.
Qed.
   
Lemma map_partial_append:
  forall (A B: Type) (f: A -> res B)
         (l1 l2: list (ident * A)) (tl1 tl2: list (ident * B)),
  map_partial prefix_var_name f l1 = OK tl1 ->
  map_partial prefix_var_name f l2 = OK tl2 ->
  map_partial prefix_var_name f (l1 ++ l2) = OK (tl1 ++ tl2).
Proof.
  induction l1; intros until tl2; simpl.
  intros. inversion H. simpl; auto.
  destruct a as [id x]. destruct (f x); try congruence.
  caseEq (map_partial prefix_var_name f l1); simpl; intros; try congruence.
  inv H0. rewrite (IHl1 _ _ _ H H1). auto.
Qed.
 
Lemma transl_vars_names:
  forall vars tvars,
  transl_vars vars = OK tvars ->
  List.map variable_name tvars = var_names vars.
Proof.
  exact (map_partial_names _ _ var_kind_of_type).
Qed.

Lemma transl_names_norepet:
  forall params vars sg tparams tvars temps body,
  list_norepet (var_names params ++ var_names vars) ->
  transl_vars params = OK tparams ->
  transl_vars vars = OK tvars ->
  let f := Csharpminor.mkfunction sg tparams tvars temps body in
  list_norepet (fn_params_names f ++ fn_vars_names f).
Proof.
  intros. unfold fn_params_names, fn_vars_names; simpl. 
  rewrite (transl_vars_names _ _ H0).
  rewrite (transl_vars_names _ _ H1).
  auto.
Qed.

Lemma transl_vars_append:
  forall l1 l2 tl1 tl2,
  transl_vars l1 = OK tl1 -> transl_vars l2 = OK tl2 ->
  transl_vars (l1 ++ l2) = OK (tl1 ++ tl2).
Proof.
  exact (map_partial_append _ _ var_kind_of_type).
Qed.

Lemma transl_fn_variables:
  forall params vars sg tparams tvars temps body,
  transl_vars params = OK tparams ->
  transl_vars vars = OK tvars ->
  let f := Csharpminor.mkfunction sg tparams tvars temps body in
  transl_vars (params ++ vars) = OK (fn_variables f).
Proof.
  intros. 
  rewrite (transl_vars_append _ _ _ _ H H0).
  reflexivity.
Qed.

(** Transformation of expressions and statements. *)

Lemma is_variable_correct:
  forall a id,
  is_variable a = Some id ->
  a = Clight.Evar id (typeof a).
Proof.
  intros until id. unfold is_variable; destruct a; intros; try discriminate.
  simpl. congruence.
Qed.

Lemma transl_expr_lvalue:
  forall ge e le m a loc ofs ta,
  Clight.eval_lvalue ge e le m a loc ofs ->
  transl_expr a = OK ta ->
  (exists id, exists ty, a = Clight.Evar id ty /\ var_get id ty = OK ta) \/
  (exists tb, transl_lvalue a = OK tb /\
              make_load tb (typeof a) = OK ta).
Proof.
  intros until ta; intros EVAL TR. inv EVAL.
  (* var local *)
  left; exists id; exists ty; auto.
  (* var global *)
  left; exists id; exists ty; auto.
  (* deref *)
  monadInv TR. right. exists x; split; auto.
  (* field struct *)
  simpl in TR. rewrite H0 in TR. monadInv TR.
  right. econstructor; split. simpl. rewrite H0.
  rewrite EQ; rewrite EQ1; simpl; eauto. auto.
  (* field union *)
  simpl in TR. rewrite H0 in TR. monadInv TR.
  right. econstructor; split. simpl. rewrite H0. rewrite EQ; simpl; eauto. auto.
Qed.

(** Properties of labeled statements *)

Lemma transl_lbl_stmt_1:
  forall tyret nbrk ncnt n sl tsl,
  transl_lbl_stmt tyret nbrk ncnt sl = OK tsl ->
  transl_lbl_stmt tyret nbrk ncnt (Clight.select_switch n sl) = OK (select_switch n tsl).
Proof.
  induction sl; intros.
  monadInv H. simpl. rewrite EQ. auto.
  generalize H; intro TR. monadInv TR. simpl. 
  destruct (Int.eq i n). auto. auto. 
Qed.

Lemma transl_lbl_stmt_2:
  forall tyret nbrk ncnt sl tsl,
  transl_lbl_stmt tyret nbrk ncnt sl = OK tsl ->
  transl_statement tyret nbrk ncnt (seq_of_labeled_statement sl) = OK (seq_of_lbl_stmt tsl).
Proof.
  induction sl; intros.
  monadInv H. simpl. auto.
  monadInv H. simpl. rewrite EQ; simpl. rewrite (IHsl _ EQ1). simpl. auto.
Qed.

(** * Correctness of Csharpminor construction functions *)

Section CONSTRUCTORS.

Variable ge: genv.

Lemma make_intconst_correct:
  forall n e le m,
  eval_expr ge e le m (make_intconst n) (Vint n).
Proof.
  intros. unfold make_intconst. econstructor. reflexivity. 
Qed.

Lemma make_floatconst_correct:
  forall n e le m,
  eval_expr ge e le m (make_floatconst n) (Vfloat n).
Proof.
  intros. unfold make_floatconst. econstructor. reflexivity. 
Qed.

Lemma make_floatofint_correct:
  forall a n sg e le m,
  eval_expr ge e le m a (Vint n) ->
  eval_expr ge e le m (make_floatofint a sg) (Vfloat(cast_int_float sg n)).
Proof.
  intros. unfold make_floatofint, cast_int_float. 
  destruct sg; econstructor; eauto. 
Qed.

Lemma make_intoffloat_correct:
  forall e le m a sg f i,
  eval_expr ge e le m a (Vfloat f) ->
  cast_float_int sg f = Some i ->
  eval_expr ge e le m (make_intoffloat a sg) (Vint i).
Proof.
  unfold cast_float_int, make_intoffloat; intros.
  destruct sg; econstructor; eauto; simpl; rewrite H0; auto.
Qed.

Hint Resolve make_intconst_correct make_floatconst_correct
             make_floatofint_correct make_intoffloat_correct
             eval_Eunop eval_Ebinop: cshm.
Hint Extern 2 (@eq trace _ _) => traceEq: cshm.

Lemma make_cast_int_correct:
  forall e le m a n sz si,
  eval_expr ge e le m a (Vint n) ->
  eval_expr ge e le m (make_cast_int a sz si) (Vint (cast_int_int sz si n)).
Proof.
  intros. unfold make_cast_int, cast_int_int. 
  destruct sz.
  destruct si; eauto with cshm.
  destruct si; eauto with cshm.
  auto.
  econstructor. eauto. simpl. destruct (Int.eq n Int.zero); auto.
Qed.

Lemma make_cast_float_correct:
  forall e le m a n sz,
  eval_expr ge e le m a (Vfloat n) ->
  eval_expr ge e le m (make_cast_float a sz) (Vfloat (cast_float_float sz n)).
Proof.
  intros. unfold make_cast_float, cast_float_float. 
  destruct sz. eauto with cshm. auto.
Qed.

Hint Resolve make_cast_int_correct make_cast_float_correct: cshm.

Lemma make_cast_correct:
  forall e le m a v ty1 ty2 v',
  eval_expr ge e le m a v ->
  sem_cast v ty1 ty2 = Some v' ->
  eval_expr ge e le m (make_cast ty1 ty2 a) v'.
Proof.
  intros. unfold make_cast. functional inversion H0; subst.
  (* neutral *)
  rewrite H2; auto.
  rewrite H2; auto.
  (* int -> int *)
  rewrite H2. auto with cshm. 
  (* float -> float *)
  rewrite H2. auto with cshm.
  (* int -> float *)
  rewrite H2. auto with cshm. 
  (* float -> int *)
  rewrite H2. eauto with cshm.
  (* int/pointer -> bool *)
  rewrite H2. econstructor; eauto. simpl. destruct (Int.eq i Int.zero); auto.
  rewrite H2. econstructor; eauto. 
  (* float -> bool *)
  rewrite H2. econstructor; eauto with cshm.
  simpl. unfold Val.cmpf, Val.cmpf_bool. rewrite Float.cmp_ne_eq. rewrite H7; auto.
  rewrite H2. econstructor; eauto with cshm.
  simpl. unfold Val.cmpf, Val.cmpf_bool. rewrite Float.cmp_ne_eq. rewrite H7; auto.
  (* struct -> struct *)
  rewrite H2. auto.
  (* union -> union *)
  rewrite H2. auto.
  (* any -> void *)
  rewrite H5. auto.
Qed.

Lemma make_boolean_correct:
 forall e le m a v ty b,
  eval_expr ge e le m a v ->
  bool_val v ty = Some b ->
  exists vb,
    eval_expr ge e le m (make_boolean a ty) vb
    /\ Val.bool_of_val vb b.
Proof.
  assert (VBI: forall n, Val.bool_of_val (Vint n) (negb (Int.eq n Int.zero))).
    intros. predSpec Int.eq Int.eq_spec n Int.zero; simpl.
    subst. constructor.
    constructor. auto.
  intros. functional inversion H0; subst; simpl.
  exists (Vint n); split; auto.
  exists (Vint n); split; auto.
  exists (Vint n); split; auto.
  exists (Vint n); split; auto.
  exists (Vptr b0 ofs); split; auto. constructor.
  exists (Vptr b0 ofs); split; auto. constructor.
  exists (Vptr b0 ofs); split; auto. constructor.
  exists (Vptr b0 ofs); split; auto. constructor.
  rewrite <- Float.cmp_ne_eq.
  exists (Val.of_bool (Float.cmp Cne f Float.zero)); split.
  econstructor; eauto with cshm. 
  destruct (Float.cmp Cne f Float.zero); simpl; constructor. apply Int.one_not_zero.
Qed.

Lemma make_neg_correct:
  forall a tya c va v e le m,
  sem_neg va tya = Some v ->
  make_neg a tya = OK c ->  
  eval_expr ge e le m a va ->
  eval_expr ge e le m c v.
Proof.
  intros until m; intro SEM. unfold make_neg. 
  functional inversion SEM; intros.
  rewrite H0 in H4. inv H4. eapply eval_Eunop; eauto with cshm.
  rewrite H0 in H4. inv H4. eauto with cshm.
Qed.

Lemma make_notbool_correct:
  forall a tya c va v e le m,
  sem_notbool va tya = Some v ->
  make_notbool a tya = OK c ->  
  eval_expr ge e le m a va ->
  eval_expr ge e le m c v.
Proof.
  intros until m; intro SEM. unfold make_notbool. 
  functional inversion SEM; intros; rewrite H0 in H4; inversion H4; simpl;
  eauto with cshm.
Qed.

Lemma make_notint_correct:
  forall a tya c va v e le m,
  sem_notint va tya = Some v ->
  make_notint a tya = c ->  
  eval_expr ge e le m a va ->
  eval_expr ge e le m c v.
Proof.
  intros until m; intro SEM. unfold make_notint. 
  functional inversion SEM; intros. subst. eauto with cshm. 
Qed.

Definition binary_constructor_correct
    (make: expr -> type -> expr -> type -> res expr)
    (sem: val -> type -> val -> type -> option val): Prop :=
  forall a tya b tyb c va vb v e le m,
  sem va tya vb tyb = Some v ->
  make a tya b tyb = OK c ->  
  eval_expr ge e le m a va ->
  eval_expr ge e le m b vb ->
  eval_expr ge e le m c v.

Lemma make_add_correct: binary_constructor_correct make_add sem_add.
Proof.
  red; intros until m. intro SEM. unfold make_add. 
  functional inversion SEM; rewrite H0; intros;
  inversion H7; eauto with cshm. 
  eapply eval_Ebinop. eauto. 
  eapply eval_Ebinop. eauto with cshm. eauto.
  simpl. reflexivity. reflexivity. 
  eapply eval_Ebinop. eauto. 
  eapply eval_Ebinop. eauto with cshm. eauto. 
  simpl. reflexivity. simpl. reflexivity.
Qed.

Lemma make_sub_correct: binary_constructor_correct make_sub sem_sub.
Proof.
  red; intros until m. intro SEM. unfold make_sub. 
  functional inversion SEM; rewrite H0; intros;
  inversion H7; eauto with cshm. 
  eapply eval_Ebinop. eauto. 
  eapply eval_Ebinop. eauto with cshm. eauto.
  simpl. reflexivity. reflexivity. 
  inversion H9. eapply eval_Ebinop. 
  eapply eval_Ebinop; eauto. 
  simpl. unfold eq_block; rewrite H3. reflexivity.
  eauto with cshm. simpl. rewrite H8. reflexivity.
Qed.

Lemma make_mul_correct: binary_constructor_correct make_mul sem_mul.
Proof.
  red; intros until m. intro SEM. unfold make_mul. 
  functional inversion SEM; rewrite H0; intros;
  inversion H7; eauto with cshm. 
Qed.

Lemma make_div_correct: binary_constructor_correct make_div sem_div.
Proof.
  red; intros until m. intro SEM. unfold make_div. 
  functional inversion SEM; rewrite H0; intros.
  inversion H8. eapply eval_Ebinop; eauto with cshm. 
  simpl. rewrite H7; auto.
  inversion H8. eapply eval_Ebinop; eauto with cshm. 
  simpl. rewrite H7; auto.
  inversion H7; eauto with cshm. 
  inversion H7; eauto with cshm. 
  inversion H7; eauto with cshm. 
Qed.

Lemma make_mod_correct: binary_constructor_correct make_mod sem_mod.
  red; intros until m. intro SEM. unfold make_mod. 
  functional inversion SEM; rewrite H0; intros.
  inversion H8. eapply eval_Ebinop; eauto with cshm. 
  simpl. rewrite H7; auto.
  inversion H8. eapply eval_Ebinop; eauto with cshm. 
  simpl. rewrite H7; auto.
Qed.

Lemma make_and_correct: binary_constructor_correct make_and sem_and.
Proof.
  red; intros until m. intro SEM. unfold make_and. 
  functional inversion SEM. intros. inversion H7. 
  eauto with cshm. 
Qed.

Lemma make_or_correct: binary_constructor_correct make_or sem_or.
Proof.
  red; intros until m. intro SEM. unfold make_or. 
  functional inversion SEM. intros. inversion H7. 
  eauto with cshm. 
Qed.

Lemma make_xor_correct: binary_constructor_correct make_xor sem_xor.
Proof.
  red; intros until m. intro SEM. unfold make_xor. 
  functional inversion SEM. intros. inversion H7. 
  eauto with cshm. 
Qed.

Lemma make_shl_correct: binary_constructor_correct make_shl sem_shl.
Proof.
  red; intros until m. intro SEM. unfold make_shl. 
  functional inversion SEM. intros. inversion H8. 
  eapply eval_Ebinop; eauto with cshm. 
  simpl. rewrite H7. auto.
Qed.

Lemma make_shr_correct: binary_constructor_correct make_shr sem_shr.
Proof.
  red; intros until m. intro SEM. unfold make_shr. 
  functional inversion SEM; intros; rewrite H0 in H8; inversion H8.
  eapply eval_Ebinop; eauto with cshm.
  simpl; rewrite H7; auto.
  eapply eval_Ebinop; eauto with cshm.
  simpl; rewrite H7; auto.
Qed.

Lemma make_cmp_correct:
  forall cmp a tya b tyb c va vb v e le m,
  sem_cmp cmp va tya vb tyb m = Some v ->
  make_cmp cmp a tya b tyb = OK c ->  
  eval_expr ge e le m a va ->
  eval_expr ge e le m b vb ->
  eval_expr ge e le m c v.
Proof.
  intros until m. intro SEM. unfold make_cmp.
  functional inversion SEM; rewrite H0; intros.
  (** ii Signed *)
  inversion H8; eauto with cshm.
  (* ii Unsigned *) 
  inversion H8. eauto with cshm.
  (* pp int int *)
  inversion H8. eauto with cshm.
  (* pp ptr ptr *)
  inversion H10. eapply eval_Ebinop; eauto with cshm.
  simpl. unfold Val.cmpu. simpl. rewrite H3. rewrite H9. auto.
  inversion H10. eapply eval_Ebinop; eauto with cshm.
  simpl. unfold Val.cmpu. simpl. rewrite H3. rewrite H9.
  destruct cmp; simpl in *; inv H; auto.
  (* pp ptr int *)
  inversion H9. eapply eval_Ebinop; eauto with cshm.
  simpl. unfold Val.cmpu. simpl. rewrite H8.
  destruct cmp; simpl in *; inv H; auto.
  (* pp int ptr *)
  inversion H9. eapply eval_Ebinop; eauto with cshm.
  simpl. unfold Val.cmpu. simpl. rewrite H8.
  destruct cmp; simpl in *; inv H; auto.
  (* ff *)
  inversion H8. eauto with cshm.
  (* if *)
  inversion H8. eauto with cshm.
  (* fi *)
  inversion H8. eauto with cshm.
Qed.

Lemma transl_unop_correct:
  forall op a tya c va v e le m, 
  transl_unop op a tya = OK c ->
  sem_unary_operation op va tya = Some v ->
  eval_expr ge e le m a va ->
  eval_expr ge e le m c v.
Proof.
  intros. destruct op; simpl in *.
  eapply make_notbool_correct; eauto. 
  eapply make_notint_correct with (tya := tya); eauto. congruence.
  eapply make_neg_correct; eauto.
Qed.

Lemma transl_binop_correct:
  forall op a tya b tyb c va vb v e le m,
  transl_binop op a tya b tyb = OK c ->  
  sem_binary_operation op va tya vb tyb m = Some v ->
  eval_expr ge e le m a va ->
  eval_expr ge e le m b vb ->
  eval_expr ge e le m c v.
Proof.
  intros. destruct op; simpl in *.
  eapply make_add_correct; eauto.
  eapply make_sub_correct; eauto.
  eapply make_mul_correct; eauto.
  eapply make_div_correct; eauto.
  eapply make_mod_correct; eauto.
  eapply make_and_correct; eauto.
  eapply make_or_correct; eauto.
  eapply make_xor_correct; eauto.
  eapply make_shl_correct; eauto.
  eapply make_shr_correct; eauto.
  eapply make_cmp_correct; eauto.
  eapply make_cmp_correct; eauto.
  eapply make_cmp_correct; eauto.
  eapply make_cmp_correct; eauto.
  eapply make_cmp_correct; eauto.
  eapply make_cmp_correct; eauto.
Qed. 

Lemma make_load_correct:
  forall addr ty code b ofs v e le m,
  make_load addr ty = OK code ->
  eval_expr ge e le m addr (Vptr b ofs) ->
  deref_loc ge ty m b ofs E0 v ->
  type_is_volatile ty = false ->
  eval_expr ge e le m code v.
Proof.
  unfold make_load; intros until m; intros MKLOAD EVEXP DEREF NONVOL.
  inv DEREF. 
  (* nonvolatile scalar *)
  rewrite H in MKLOAD. inv MKLOAD. apply eval_Eload with (Vptr b ofs); auto.
  (* volatile scalar *)
  congruence.
  (* by reference *)
  rewrite H in MKLOAD. inv MKLOAD. auto.
  (* by copy *)
  rewrite H in MKLOAD. inv MKLOAD. auto.
Qed.

Lemma make_vol_load_correct:
  forall id addr ty code b ofs t v e le m f k,
  make_vol_load id addr ty = OK code ->
  eval_expr ge e le m addr (Vptr b ofs) ->
  deref_loc ge ty m b ofs t v ->
  type_is_volatile ty = true ->
  step ge (State f code k e le m) t (State f Sskip k e (PTree.set id v le) m).
Proof.
  unfold make_vol_load; intros until k; intros MKLOAD EVEXP DEREF VOL.
  inv DEREF.
  (* nonvolatile scalar *)
  congruence.
(**
  rewrite H in MKLOAD. inv MKLOAD.
  change (PTree.set id v le) with (Cminor.set_optvar (Some id) v le).
  econstructor. constructor. eauto. constructor. constructor; auto. constructor; auto. 
*)
  (* volatile scalar *)
  rewrite H in MKLOAD. inv MKLOAD.
  change (PTree.set id v le) with (Cminor.set_optvar (Some id) v le).
  econstructor. constructor. eauto. constructor. constructor; auto.
  (* by reference *)
  rewrite H in MKLOAD. inv MKLOAD. constructor; auto. 
  (* by copy *)
  rewrite H in MKLOAD. inv MKLOAD. constructor; auto. 
Qed.

(*
Remark capped_alignof_divides:
  forall ty n, 
  (alignof ty | n) -> (Zmin (alignof ty) 4 | n).
Proof.
  intros. generalize (alignof_1248 ty). 
  intros [A|[A|[A|A]]]; rewrite A in *; auto. 
  apply Zdivides_trans with 8; auto. exists 2; auto.
Qed.

Remark capped_alignof_124:
  forall ty,
  Zmin (alignof ty) 4 = 1 \/ Zmin (alignof ty) 4 = 2 \/ Zmin (alignof ty) 4 = 4.
Proof.
  intros. generalize (alignof_1248 ty). 
  intros [A|[A|[A|A]]]; rewrite A; auto.
Qed.
*)

Lemma make_memcpy_correct:
  forall f dst src ty k e le m b ofs v t m',
  eval_expr ge e le m dst (Vptr b ofs) ->
  eval_expr ge e le m src v ->
  assign_loc ge ty m b ofs v t m' ->
  access_mode ty = By_copy ->
  step ge (State f (make_memcpy dst src ty) k e le m) t (State f Sskip k e le m').
Proof.
  intros. inv H1; try congruence. 
  unfold make_memcpy. change le with (set_optvar None Vundef le) at 2. 
  econstructor.
  econstructor. eauto. econstructor. eauto. constructor. 
  econstructor; eauto. 
  apply alignof_1248.
  apply sizeof_pos. 
  apply sizeof_alignof_compat.
Qed.
 
Lemma make_store_correct:
  forall addr ty rhs code e le m b ofs v t m' f k,
  make_store addr ty rhs = OK code ->
  eval_expr ge e le m addr (Vptr b ofs) ->
  eval_expr ge e le m rhs v ->
  assign_loc ge ty m b ofs v t m' ->
  type_is_volatile ty = false ->
  step ge (State f code k e le m) t (State f Sskip k e le m').
Proof.
  unfold make_store. intros until k; intros MKSTORE EV1 EV2 ASSIGN NONVOL.
  inversion ASSIGN; subst.
  (* nonvolatile scalar *)
  rewrite H in MKSTORE; inv MKSTORE.
  econstructor; eauto. 
  (* volatile scalar *)
  congruence.
  (* by copy *)
  rewrite H in MKSTORE; inv MKSTORE. 
  eapply make_memcpy_correct; eauto. 
Qed.

Lemma make_vol_store_correct:
  forall addr ty rhs code e le m b ofs v t m' f k,
  make_vol_store addr ty rhs = OK code ->
  eval_expr ge e le m addr (Vptr b ofs) ->
  eval_expr ge e le m rhs v ->
  assign_loc ge ty m b ofs v t m' ->
  type_is_volatile ty = true ->
  step ge (State f code k e le m) t (State f Sskip k e le m').
Proof.
  unfold make_vol_store. intros until k; intros MKSTORE EV1 EV2 ASSIGN VOL.
  inversion ASSIGN; subst.
  (* nonvolatile scalar *)
  congruence.
  (* volatile scalar *)
  rewrite H in MKSTORE; inv MKSTORE. 
  change le with (Cminor.set_optvar None Vundef le) at 2.
  econstructor. constructor. eauto. constructor. eauto. constructor.
  constructor. auto.
  (* by copy *)
  rewrite H in MKSTORE; inv MKSTORE. 
  eapply make_memcpy_correct; eauto. 
Qed.

End CONSTRUCTORS.

(** * Basic preservation invariants *)

Section CORRECTNESS.

Variable prog: Clight.program.
Variable tprog: Csharpminor.program.
Hypothesis TRANSL: transl_program prog = OK tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall s, Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_transf_partial2 transl_fundef transl_globvar _ TRANSL).

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  exists tf, Genv.find_funct tge v = Some tf /\ transl_fundef f = OK tf.
Proof (Genv.find_funct_transf_partial2 transl_fundef transl_globvar _ TRANSL).

Lemma function_ptr_translated:
  forall b f,
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial2 transl_fundef transl_globvar _ TRANSL).

Lemma var_info_translated:
  forall b v,
  Genv.find_var_info ge b = Some v ->
  exists tv, Genv.find_var_info tge b = Some tv /\ transf_globvar transl_globvar v = OK tv.
Proof (Genv.find_var_info_transf_partial2 transl_fundef transl_globvar _ TRANSL).

Lemma var_info_rev_translated:
  forall b tv,
  Genv.find_var_info tge b = Some tv ->
  exists v, Genv.find_var_info ge b = Some v /\ transf_globvar transl_globvar v = OK tv.
Proof (Genv.find_var_info_rev_transf_partial2 transl_fundef transl_globvar _ TRANSL).

Lemma block_is_volatile_preserved:
  forall b, block_is_volatile tge b = block_is_volatile ge b.
Proof.
  intros. unfold block_is_volatile.
  destruct (Genv.find_var_info ge b) as []_eqn.
  exploit var_info_translated; eauto. intros [tv [A B]]. rewrite A. 
  unfold transf_globvar in B. monadInv B. auto.
  destruct (Genv.find_var_info tge b) as []_eqn.
  exploit var_info_rev_translated; eauto. intros [tv [A B]]. congruence.
  auto.
Qed.

Lemma deref_loc_preserved:
  forall ty m b ofs t v,
  deref_loc ge ty m b ofs t v -> deref_loc tge ty m b ofs t v.
Proof.
  intros. inv H. 
  eapply deref_loc_value; eauto.
  eapply deref_loc_volatile; eauto.
  eapply volatile_load_preserved with (ge1 := ge); auto.
  exact symbols_preserved. exact block_is_volatile_preserved.
  eapply deref_loc_reference; eauto.
  eapply deref_loc_copy; eauto.
Qed.

Lemma assign_loc_preserved:
  forall ty m b ofs v t m',
  assign_loc ge ty m b ofs v t m' -> assign_loc tge ty m b ofs v t m'.
Proof.
  intros. inv H. 
  eapply assign_loc_value; eauto.
  eapply assign_loc_volatile; eauto.
  eapply volatile_store_preserved with (ge1 := ge); auto.
  exact symbols_preserved. exact block_is_volatile_preserved.
  eapply assign_loc_copy; eauto.
Qed.

(** * Matching between environments *)

(** In this section, we define a matching relation between
  a Clight local environment and a Csharpminor local environment. *)

Record match_env (e: Clight.env) (te: Csharpminor.env) : Prop :=
  mk_match_env {
    me_local:
      forall id b ty,
      e!id = Some (b, ty) ->
      exists vk, var_kind_of_type ty = OK vk /\ te!id = Some (b, vk);
    me_local_inv:
      forall id b vk,
      te!id = Some (b, vk) -> exists ty, e!id = Some(b, ty)
  }.

Lemma match_env_globals:
  forall e te id l ty,
  match_env e te ->
  e!id = None ->
  Genv.find_symbol ge id = Some l ->
  type_of_global ge l = Some ty ->
  te!id = None /\
  (forall chunk, access_mode ty = By_value chunk ->
   exists gv, Genv.find_var_info tge l = Some gv /\ gvar_info gv = Vscalar chunk).
Proof.
  intros.
  case_eq (te!id). intros [b' vk] EQ. 
  exploit me_local_inv; eauto. intros [ty' EQ']. congruence.
  intros. split; auto; intros.
  revert H2; unfold type_of_global. 
  case_eq (Genv.find_var_info ge l). intros. inv H5. 
  exploit var_info_translated; eauto. intros [gv [A B]]. monadInv B. unfold transl_globvar in EQ. 
  econstructor; split. eauto. simpl. 
  exploit var_kind_by_value; eauto. congruence.
  intros. destruct (Genv.find_funct_ptr ge l); intros; inv H5. 
  destruct f; simpl in H4; discriminate.
Qed.

Lemma match_env_same_blocks:
  forall e te,
  match_env e te ->
  blocks_of_env te = Csem.blocks_of_env e.
Proof.
  intros.
  set (R := fun (x: (block * type)) (y: (block * var_kind)) =>
         match x, y with
         | (b1, ty), (b2, vk) => b2 = b1 /\ var_kind_of_type ty = OK vk
         end).
  assert (list_forall2 
            (fun i_x i_y => fst i_x = fst i_y /\ R (snd i_x) (snd i_y))
            (PTree.elements e) (PTree.elements te)).
  apply PTree.elements_canonical_order.
  intros id [b ty] GET. exploit me_local; eauto. intros [vk [A B]].
  exists (b, vk); split; auto. red. auto.
  intros id [b vk] GET. 
  exploit me_local_inv; eauto. intros [ty A]. 
  exploit me_local; eauto. intros [vk' [B C]]. 
  assert (vk' = vk) by congruence. subst vk'.
  exists (b, ty); split; auto. red. auto.

  unfold blocks_of_env, Csem.blocks_of_env.
  generalize H0. induction 1. auto. 
  simpl. f_equal; auto.
  unfold block_of_binding, Csem.block_of_binding. 
  destruct a1 as [id1 [blk1 ty1]]. destruct b1 as [id2 [blk2 vk2]].
  simpl in *. destruct H1 as [A [B C]]. subst blk2 id2. f_equal.
  apply sizeof_var_kind_of_type. auto. 
Qed.

Lemma match_env_free_blocks:
  forall e te m m',
  match_env e te ->
  Mem.free_list m (Csem.blocks_of_env e) = Some m' ->
  Mem.free_list m (blocks_of_env te) = Some m'.
Proof.
  intros. rewrite (match_env_same_blocks _ _ H). auto.
Qed.

Lemma match_env_empty:
  match_env Clight.empty_env Csharpminor.empty_env.
Proof.
  unfold Clight.empty_env, Csharpminor.empty_env.
  constructor.
  intros until b. repeat rewrite PTree.gempty. congruence.
  intros until vk. rewrite PTree.gempty. congruence.
Qed.

(** The following lemmas establish the [match_env] invariant at
  the beginning of a function invocation, after allocation of
  local variables and initialization of the parameters. *)

Lemma match_env_alloc_variables:
  forall e1 m1 vars e2 m2,
  Csem.alloc_variables e1 m1 vars e2 m2 ->
  forall te1 tvars,
  match_env e1 te1 ->
  transl_vars vars = OK tvars ->
  exists te2,
  Csharpminor.alloc_variables te1 m1 tvars te2 m2
  /\ match_env e2 te2.
Proof.
  induction 1; intros.
  monadInv H0. 
  exists te1; split. constructor. auto.
  generalize H2. simpl. 
  caseEq (var_kind_of_type ty); simpl; [intros vk VK | congruence].
  caseEq (transl_vars vars); simpl; [intros tvrs TVARS | congruence].
  intro EQ; inversion EQ; subst tvars; clear EQ.
  set (te2 := PTree.set id (b1, vk) te1).
  assert (match_env (PTree.set id (b1, ty) e) te2).
    inversion H1. unfold te2. constructor.
    (* me_local *)
    intros until ty0. simpl. repeat rewrite PTree.gsspec.
    destruct (peq id0 id); intros.
    inv H3. exists vk; intuition.
    auto.
    (* me_local_inv *)
    intros until vk0. repeat rewrite PTree.gsspec. 
    destruct (peq id0 id); intros. exists ty; congruence. eauto. 
  destruct (IHalloc_variables _ _ H3 TVARS) as [te3 [ALLOC MENV]]. 
  exists te3; split.
  econstructor; eauto.
  rewrite (sizeof_var_kind_of_type _ _ VK). eauto. 
  auto. 
Qed. 

Lemma bind_parameters_match:
  forall e m1 vars vals m2,
  Csem.bind_parameters ge e m1 vars vals m2 ->
  forall te tvars,
  val_casted_list vals (type_of_params vars) ->
  match_env e te ->
  transl_vars vars = OK tvars ->
  Csharpminor.bind_parameters tge te m1 tvars vals m2.
Proof.
  induction 1; intros.
(* base case *)
  monadInv H1. constructor.
(* inductive case *)
  simpl in H2. destruct H2.
  simpl in H4. destruct (var_kind_of_type ty) as [vk|]_eqn; monadInv H4.
  assert (A: (exists chunk, access_mode ty = By_value chunk /\ Mem.store chunk m b 0 v1 = Some m1)
             \/ access_mode ty = By_copy).
    inv H0; auto; left; econstructor; split; eauto. inv H7. auto. 
  destruct A as [[chunk [MODE STORE]] | MODE].
  (* scalar case *)
  assert (vk = Vscalar chunk). exploit var_kind_by_value; eauto. congruence. 
  subst vk.
  apply bind_parameters_scalar with b m1. 
  exploit me_local; eauto. intros [vk [A B]]. congruence. 
  eapply val_casted_normalized; eauto.
  assumption.
  apply IHbind_parameters; auto.
  (* array case *)
  inv H0; try congruence.
  exploit var_kind_by_reference; eauto. intros; subst vk.
  apply bind_parameters_array with b m1. 
  exploit me_local; eauto. intros [vk [A B]]. congruence. 
  econstructor; eauto. 
  apply alignof_1248.
  apply sizeof_pos. 
  apply sizeof_alignof_compat. 
  apply IHbind_parameters; auto.
Qed.

(* ** Correctness of variable accessors *)

(** Correctness of the code generated by [var_get]. *)

Lemma var_get_correct:
  forall e le m id ty loc ofs v code te,
  Clight.eval_lvalue ge e le m (Clight.Evar id ty) loc ofs ->
  deref_loc ge ty m loc ofs E0 v ->
  var_get id ty = OK code ->
  match_env e te ->
  eval_expr tge te le m code v.
Proof.
  unfold var_get; intros. 
  destruct (access_mode ty) as [chunk| | | ]_eqn.
  (* access mode By_value *)
  assert (Mem.loadv chunk m (Vptr loc ofs) = Some v).
    inv H0.
    congruence.
    inv H5. simpl. congruence.
    congruence.
    congruence.
  inv H1. inv H.
    (* local variable *)
    exploit me_local; eauto. intros [vk [A B]].
    assert (vk = Vscalar chunk).
    exploit var_kind_by_value; eauto. congruence.
    subst vk.
    eapply eval_Evar. 
    eapply eval_var_ref_local. eauto. assumption. 
    (* global variable *)
    exploit match_env_globals; eauto. intros [A B].
    exploit B; eauto. intros [gv [C D]].
    eapply eval_Evar. 
    eapply eval_var_ref_global. auto.
    rewrite symbols_preserved. eauto.
    eauto. eauto. 
    assumption. 
  (* access mode By_reference *)
  assert (v = Vptr loc ofs). inv H0; congruence.
  inv H1. inv H.
    (* local variable *)
    exploit me_local; eauto. intros [vk [A B]].
    eapply eval_Eaddrof.
    eapply eval_var_addr_local. eauto. 
    (* global variable *)
    exploit match_env_globals; eauto. intros [A B].
    eapply eval_Eaddrof.
    eapply eval_var_addr_global. auto. 
    rewrite symbols_preserved. eauto.
  (* access mode By_copy *)
  assert (v = Vptr loc ofs). inv H0; congruence.
  inv H1. inv H.
    (* local variable *)
    exploit me_local; eauto. intros [vk [A B]].
    eapply eval_Eaddrof.
    eapply eval_var_addr_local. eauto. 
    (* global variable *)
    exploit match_env_globals; eauto. intros [A B].
    eapply eval_Eaddrof.
    eapply eval_var_addr_global. auto. 
    rewrite symbols_preserved. eauto.
  (* access mode By_nothing *)
  congruence.
Qed.

(** Correctness of the code generated by [var_set]. *)

Lemma var_set_correct:
  forall e le m id ty loc ofs v t m' code te rhs f k, 
  Clight.eval_lvalue ge e le m (Clight.Evar id ty) loc ofs ->
  val_casted v ty ->
  assign_loc ge ty m loc ofs v t m' ->
  type_is_volatile ty = false ->
  var_set id ty rhs = OK code ->
  match_env e te ->
  eval_expr tge te le m rhs v ->
  step tge (State f code k te le m) t (State f Sskip k te le m').
Proof.
  intros. unfold var_set in H3.
  inversion H1; subst; rewrite H6 in H3; inv H3.
  (* scalar, non volatile *)
  inv H.
    (* local variable *)
    exploit me_local; eauto. intros [vk [A B]].
    assert (vk = Vscalar chunk).
      exploit var_kind_by_value; eauto. congruence.
    subst vk.
    eapply step_assign. eauto.
    econstructor. eapply eval_var_ref_local. eauto.
    eapply val_casted_normalized; eauto. assumption. 
    (* global variable *)
    exploit match_env_globals; eauto. intros [A B].
    exploit B; eauto. intros [gv [C D]].
    eapply step_assign. eauto.
    econstructor. eapply eval_var_ref_global. auto.
    rewrite symbols_preserved. eauto.
    eauto. eauto.
    eapply val_casted_normalized; eauto. assumption.
  (* scalar, volatile *)
  congruence.
  (* array *)
  assert (eval_expr tge te le m (Eaddrof id) (Vptr loc ofs)).
    inv H. 
    exploit me_local; eauto. intros [vk [A B]].
    constructor. eapply eval_var_addr_local; eauto. 
    exploit match_env_globals; eauto. intros [A B].
    constructor. eapply eval_var_addr_global; eauto. 
    rewrite symbols_preserved. eauto.
  eapply make_memcpy_correct; eauto. eapply assign_loc_preserved; eauto. 
Qed.

(** * Proof of semantic preservation *)

(** ** Semantic preservation for expressions *)

(** The proof of semantic preservation for the translation of expressions
  relies on simulation diagrams of the following form:
<<
         e, le, m, a ------------------- te, le, m, ta
            |                                |
            |                                |
            |                                |
            v                                v
         e, le, m, v ------------------- te, le, m, v
>>
  Left: evaluation of r-value expression [a] in Clight.
  Right: evaluation of its translation [ta] in Csharpminor.
  Top (precondition): matching between environments [e], [te], 
    plus well-typedness of expression [a].
  Bottom (postcondition): the result values [v] 
    are identical in both evaluations.

  We state these diagrams as the following properties, parameterized
  by the Clight evaluation. *)

Section EXPR.

Variable e: Clight.env.
Variable le: temp_env.
Variable m: mem.
Variable te: Csharpminor.env.
Hypothesis MENV: match_env e te.

Lemma transl_expr_lvalue_correct:
  (forall a v,
   Clight.eval_expr ge e le m a v ->
   forall ta (TR: transl_expr a = OK ta) ,
   Csharpminor.eval_expr tge te le m ta v)
/\(forall a b ofs,
   Clight.eval_lvalue ge e le m a b ofs ->
   forall ta (TR: transl_lvalue a = OK ta),
   Csharpminor.eval_expr tge te le m ta (Vptr b ofs)).
Proof.
  apply eval_expr_lvalue_ind; intros; try (monadInv TR).
(* const int *)
  apply make_intconst_correct.
(* const float *)
  apply make_floatconst_correct.
(* temp var *)
  constructor; auto.
(* addrof *)
  simpl in TR. auto. 
(* unop *)
  eapply transl_unop_correct; eauto.
(* binop *)
  eapply transl_binop_correct; eauto.
(* condition *)
  exploit make_boolean_correct. eapply H0; eauto. eauto.
  intros [vb [EVAL BVAL]].
  eapply eval_Econdition; eauto.
  destruct b; eapply make_cast_correct; eauto. 
(* cast *)
  eapply make_cast_correct; eauto.
(* rvalue out of lvalue *)
  exploit transl_expr_lvalue; eauto. 
  intros [[id [ty [EQ VARGET]]] | [tb [TRLVAL MKLOAD]]].
  (* Case a is a variable *)
  subst a. eapply var_get_correct; eauto.
  (* Case a is another lvalue *)
  eapply make_load_correct; eauto. eapply deref_loc_preserved; eauto. 
(* var local *)
  exploit (me_local _ _ MENV); eauto.
  intros [vk [A B]].
  econstructor. eapply eval_var_addr_local. eauto.
(* var global *)
  exploit match_env_globals; eauto. intros [A B].
  econstructor. eapply eval_var_addr_global. eauto. 
  rewrite symbols_preserved. auto.
(* deref *)
  simpl in TR. eauto. 
(* field struct *)
  simpl in TR. rewrite H1 in TR. monadInv TR.
  eapply eval_Ebinop; eauto.
  apply make_intconst_correct. 
  simpl. congruence.
(* field union *)
  simpl in TR. rewrite H1 in TR. eauto.
Qed.

Lemma transl_expr_correct:
   forall a v,
   Clight.eval_expr ge e le m a v ->
   forall ta, transl_expr a = OK ta ->
   Csharpminor.eval_expr tge te le m ta v.
Proof (proj1 transl_expr_lvalue_correct).

Lemma transl_lvalue_correct:
   forall a b ofs,
   Clight.eval_lvalue ge e le m a b ofs ->
   forall ta, transl_lvalue a = OK ta ->
   Csharpminor.eval_expr tge te le m ta (Vptr b ofs).
Proof (proj2 transl_expr_lvalue_correct).

Lemma transl_exprlist_correct:
  forall al tyl vl,
  Clight.eval_exprlist ge e le m al tyl vl ->
  forall tal, transl_exprlist al tyl = OK tal ->
  Csharpminor.eval_exprlist tge te le m tal vl.
Proof.
  induction 1; intros.
  monadInv H. constructor.
  monadInv H2. constructor. 
  eapply make_cast_correct. eapply transl_expr_correct; eauto. auto. 
  eauto.
Qed.

End EXPR.

Lemma is_constant_bool_sound:
  forall te le m a v ty b,
  Csharpminor.eval_expr tge te le m a v ->
  bool_val v ty = Some b ->
  is_constant_bool a = Some b \/ is_constant_bool a = None.
Proof.
  intros. unfold is_constant_bool. destruct a; auto. destruct c; auto. 
  left. decEq. inv H. simpl in H2. inv H2. functional inversion H0; auto.
Qed.

Lemma exit_if_false_true:
  forall a ts e le m v te f tk,
  exit_if_false a = OK ts ->
  Clight.eval_expr ge e le m a v ->
  bool_val v (typeof a) = Some true ->
  match_env e te ->
  star step tge (State f ts tk te le m) E0 (State f Sskip tk te le m).
Proof.
  intros. monadInv H.
  exploit transl_expr_correct; eauto. intros EV.
  exploit is_constant_bool_sound; eauto. intros [P | P]; rewrite P in EQ0; inv EQ0.
  constructor.
  exploit make_boolean_correct; eauto. intros [vb [EV' VB]].
  apply star_one. apply step_ifthenelse with (v := vb) (b := true); auto. 
Qed.
 
Lemma exit_if_false_false:
  forall a ts e le m v te f tk,
  exit_if_false a = OK ts ->
  Clight.eval_expr ge e le m a v ->
  bool_val v (typeof a) = Some false ->
  match_env e te ->
  star step tge (State f ts tk te le m) E0 (State f (Sexit 0) tk te le m).
Proof.
  intros. monadInv H.
  exploit transl_expr_correct; eauto. intros EV.
  exploit is_constant_bool_sound; eauto. intros [P | P]; rewrite P in EQ0; inv EQ0.
  constructor.
  exploit make_boolean_correct; eauto. intros [vb [EV' VB]].
  apply star_one. apply step_ifthenelse with (v := vb) (b := false); auto. 
Qed.

(** ** Semantic preservation for statements *)

(** The simulation diagram for the translation of statements and functions
  is a "plus" diagram of the form
<<
           I
     S1 ------- R1
     |          | 
   t |        + | t
     v          v  
     S2 ------- R2
           I                         I
>>

The invariant [I] is the [match_states] predicate that we now define.
*)

Inductive match_transl: stmt -> cont -> stmt -> cont -> Prop :=
  | match_transl_0: forall ts tk,
      match_transl ts tk ts tk
  | match_transl_1: forall ts tk,
      match_transl (Sblock ts) tk ts (Kblock tk).

Lemma match_transl_step:
  forall ts tk ts' tk' f te le m,
  match_transl (Sblock ts) tk ts' tk' ->
  star step tge (State f ts' tk' te le m) E0 (State f ts (Kblock tk) te le m).
Proof.
  intros. inv H. 
  apply star_one. constructor. 
  apply star_refl.
Qed.

Inductive match_cont: type -> nat -> nat -> Clight.cont -> Csharpminor.cont -> Prop :=
  | match_Kstop: forall tyret nbrk ncnt,
      match_cont tyret nbrk ncnt Clight.Kstop Kstop
  | match_Kseq: forall tyret nbrk ncnt s k ts tk,
      transl_statement tyret nbrk ncnt s = OK ts ->
      match_cont tyret nbrk ncnt k tk ->
      match_cont tyret nbrk ncnt
                 (Clight.Kseq s k)
                 (Kseq ts tk)
  | match_Kwhile: forall tyret nbrk ncnt a s k ta ts tk,
      exit_if_false a = OK ta ->
      transl_statement tyret 1%nat 0%nat s = OK ts ->
      match_cont tyret nbrk ncnt k tk ->
      match_cont tyret 1%nat 0%nat
                 (Clight.Kwhile a s k) 
                 (Kblock (Kseq (Sloop (Sseq ta (Sblock ts))) (Kblock tk)))
  | match_Kdowhile: forall tyret nbrk ncnt a s k ta ts tk,
      exit_if_false a = OK ta ->
      transl_statement tyret 1%nat 0%nat s = OK ts ->
      match_cont tyret nbrk ncnt k tk ->
      match_cont tyret 1%nat 0%nat
                 (Clight.Kdowhile a s k) 
                 (Kblock (Kseq ta (Kseq (Sloop (Sseq (Sblock ts) ta)) (Kblock tk))))
  | match_Kfor2: forall tyret nbrk ncnt a2 a3 s k ta2 ta3 ts tk,
      exit_if_false a2 = OK ta2 ->
      transl_statement tyret 0%nat (S ncnt) a3 = OK ta3 ->
      transl_statement tyret 1%nat 0%nat s = OK ts ->
      match_cont tyret nbrk ncnt k tk ->
      match_cont tyret 1%nat 0%nat
                 (Clight.Kfor2 a2 a3 s k)
                 (Kblock (Kseq ta3 (Kseq (Sloop (Sseq ta2 (Sseq (Sblock ts) ta3))) (Kblock tk))))
  | match_Kfor3: forall tyret nbrk ncnt a2 a3 s k ta2 ta3 ts tk,
      exit_if_false a2 = OK ta2 ->
      transl_statement tyret 0%nat (S ncnt) a3 = OK ta3 ->
      transl_statement tyret 1%nat 0%nat s = OK ts ->
      match_cont tyret nbrk ncnt k tk ->
      match_cont tyret 0%nat (S ncnt)
                 (Clight.Kfor3 a2 a3 s k)
                 (Kseq (Sloop (Sseq ta2 (Sseq (Sblock ts) ta3))) (Kblock tk))
  | match_Kswitch: forall tyret nbrk ncnt k tk,
      match_cont tyret nbrk ncnt k tk ->
      match_cont tyret 0%nat (S ncnt)
                 (Clight.Kswitch k)
                 (Kblock tk)
  | match_Kcall_some: forall tyret nbrk ncnt nbrk' ncnt' f e k id tf te le tk,
      transl_function f = OK tf ->
      match_env e te ->
      match_cont (Clight.fn_return f) nbrk' ncnt' k tk ->
      match_cont tyret nbrk ncnt 
                 (Clight.Kcall id f e le k)
                 (Kcall id tf te le tk).

Inductive match_states: Clight.state -> Csharpminor.state -> Prop :=
  | match_state:
      forall f nbrk ncnt s k e le m tf ts tk te ts' tk'
          (TRF: transl_function f = OK tf)
          (TR: transl_statement (Clight.fn_return f) nbrk ncnt s = OK ts)
          (MTR: match_transl ts tk ts' tk')
          (MENV: match_env e te)
          (MK: match_cont (Clight.fn_return f) nbrk ncnt k tk),
      match_states (Clight.State f s k e le m)
                   (State tf ts' tk' te le m)
  | match_callstate:
      forall fd args k m tfd tk targs tres
          (TR: transl_fundef fd = OK tfd)
          (MK: match_cont Tvoid 0%nat 0%nat k tk)
          (ISCC: Clight.is_call_cont k)
          (TY: type_of_fundef fd = Tfunction targs tres)
          (VCAST: val_casted_list args targs),
      match_states (Clight.Callstate fd args k m)
                   (Callstate tfd args tk m)
  | match_returnstate:
      forall res k m tk 
          (MK: match_cont Tvoid 0%nat 0%nat k tk),
      match_states (Clight.Returnstate res k m)
                   (Returnstate res tk m).

Remark match_states_skip:
  forall f e le te nbrk ncnt k tf tk m,
  transl_function f = OK tf ->
  match_env e te ->
  match_cont (Clight.fn_return f) nbrk ncnt k tk ->
  match_states (Clight.State f Clight.Sskip k e le m) (State tf Sskip tk te le m).
Proof.
  intros. econstructor; eauto. simpl; reflexivity. constructor. 
Qed.

(** Commutation between label resolution and compilation *)

Section FIND_LABEL.
Variable lbl: label.
Variable tyret: type.

Remark exit_if_false_no_label:
  forall a s, exit_if_false a = OK s -> forall k, find_label lbl s k = None.
Proof.
  intros. unfold exit_if_false in H. monadInv H.
  destruct (is_constant_bool x). destruct b; inv EQ0; auto. inv EQ0; auto.
Qed.
  
Lemma transl_find_label:
  forall s nbrk ncnt k ts tk
  (TR: transl_statement tyret nbrk ncnt s = OK ts)
  (MC: match_cont tyret nbrk ncnt k tk),
  match Clight.find_label lbl s k with
  | None => find_label lbl ts tk = None
  | Some (s', k') =>
      exists ts', exists tk', exists nbrk', exists ncnt',
      find_label lbl ts tk = Some (ts', tk')
      /\ transl_statement tyret nbrk' ncnt' s' = OK ts'
      /\ match_cont tyret nbrk' ncnt' k' tk'
  end

with transl_find_label_ls:
  forall ls nbrk ncnt k tls tk
  (TR: transl_lbl_stmt tyret nbrk ncnt ls = OK tls)
  (MC: match_cont tyret nbrk ncnt k tk),
  match Clight.find_label_ls lbl ls k with
  | None => find_label_ls lbl tls tk = None
  | Some (s', k') =>
      exists ts', exists tk', exists nbrk', exists ncnt',
      find_label_ls lbl tls tk = Some (ts', tk')
      /\ transl_statement tyret nbrk' ncnt' s' = OK ts'
      /\ match_cont tyret nbrk' ncnt' k' tk'
  end.

Proof.
  intro s; case s; intros; try (monadInv TR); simpl.
(* skip *)
  auto.
(* assign *)
  simpl in TR. destruct (type_is_volatile (typeof e)) as []_eqn.
  monadInv TR. unfold make_vol_store, make_memcpy in EQ2.
  destruct (access_mode (typeof e)); inv EQ2; auto.
  destruct (is_variable e); monadInv TR.
  unfold var_set, make_memcpy in EQ0.
  destruct (access_mode (typeof e)); inv EQ0; auto.
  unfold make_store, make_memcpy in EQ2. destruct (access_mode (typeof e)); inv EQ2; auto.
(* set *)
  auto.
(* vol load *)
  unfold make_vol_load in EQ0. destruct (access_mode (typeof e)); inv EQ0; auto.
(* call *)
  simpl in TR. destruct (classify_fun (typeof e)); monadInv TR. auto.
(* seq *)
  exploit (transl_find_label s0 nbrk ncnt (Clight.Kseq s1 k)); eauto. constructor; eauto. 
  destruct (Clight.find_label lbl s0 (Clight.Kseq s1 k)) as [[s' k'] | ].
  intros [ts' [tk' [nbrk' [ncnt' [A [B C]]]]]].
  rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. rewrite H. eapply transl_find_label; eauto.
(* ifthenelse *)
  exploit (transl_find_label s0); eauto. 
  destruct (Clight.find_label lbl s0 k) as [[s' k'] | ].
  intros [ts' [tk' [nbrk' [ncnt' [A [B C]]]]]].
  rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. rewrite H. eapply transl_find_label; eauto.
(* while *)
  rewrite (exit_if_false_no_label _ _ EQ).
  eapply transl_find_label; eauto. econstructor; eauto.
(* dowhile *)
  exploit (transl_find_label s0 1%nat 0%nat (Clight.Kdowhile e s0 k)); eauto. econstructor; eauto.
  destruct (Clight.find_label lbl s0 (Kdowhile e s0 k)) as [[s' k'] | ].
  intros [ts' [tk' [nbrk' [ncnt' [A [B C]]]]]].
  rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. rewrite H. eapply exit_if_false_no_label; eauto.
(* for *)
  rewrite (exit_if_false_no_label _ _ EQ). 
  exploit (transl_find_label s1 1%nat 0%nat (Kfor2 e s0 s1 k)); eauto. econstructor; eauto.
  destruct (Clight.find_label lbl s1 (Kfor2 e s0 s1 k)) as [[s' k'] | ].
  intros [ts' [tk' [nbrk' [ncnt' [A [B C]]]]]].
  rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. rewrite H.
  eapply transl_find_label; eauto. econstructor; eauto.
(* break *)
  auto.
(* continue *)
  auto.
(* return *)
  simpl in TR. destruct o; monadInv TR. auto. auto. 
(* switch *)
  eapply transl_find_label_ls with (k := Clight.Kswitch k); eauto. econstructor; eauto. 
(* label *)
  destruct (ident_eq lbl l). 
  exists x; exists tk; exists nbrk; exists ncnt; auto.
  eapply transl_find_label; eauto.
(* goto *)
  auto.

  intro ls; case ls; intros; monadInv TR; simpl.
(* default *)
  eapply transl_find_label; eauto.
(* case *)
  exploit (transl_find_label s nbrk ncnt (Clight.Kseq (seq_of_labeled_statement l) k)); eauto. 
  econstructor; eauto. apply transl_lbl_stmt_2; eauto.
  destruct (Clight.find_label lbl s (Clight.Kseq (seq_of_labeled_statement l) k)) as [[s' k'] | ].
  intros [ts' [tk' [nbrk' [ncnt' [A [B C]]]]]].
  rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. rewrite H.
  eapply transl_find_label_ls; eauto.
Qed.

End FIND_LABEL.

(** Properties of call continuations *)

Lemma match_cont_call_cont:
  forall tyret' nbrk' ncnt' tyret nbrk ncnt k tk,
  match_cont tyret nbrk ncnt k tk ->
  match_cont tyret' nbrk' ncnt' (Clight.call_cont k) (call_cont tk).
Proof.
  induction 1; simpl; auto.
  constructor.
  econstructor; eauto. 
Qed.

Lemma match_cont_is_call_cont:
  forall tyret nbrk ncnt k tk tyret' nbrk' ncnt',
  match_cont tyret nbrk ncnt k tk ->
  Clight.is_call_cont k ->
  match_cont tyret' nbrk' ncnt' k tk /\ is_call_cont tk.
Proof.
  intros. inv H; simpl in H0; try contradiction; simpl.
  split; auto; constructor.
  split; auto; econstructor; eauto.
Qed.

(** The simulation proof *)

Lemma transl_step:
  forall S1 t S2, Clight.step ge S1 t S2 ->
  forall T1, match_states S1 T1 ->
  exists T2, plus step tge T1 t T2 /\ match_states S2 T2.
Proof.
  induction 1; intros T1 MST; inv MST.

(* assign *)
  simpl in TR. destruct (type_is_volatile (typeof a1)) as []_eqn. 
  (* Case 1: volatile *)
  monadInv TR. 
  assert (SAME: ts' = ts /\ tk' = tk).
    inversion MTR. auto. 
    subst ts. unfold make_vol_store, make_memcpy in EQ2.
    destruct (access_mode (typeof a1)); congruence.
  destruct SAME; subst ts' tk'.
  econstructor; split.
  apply plus_one. eapply make_vol_store_correct; eauto.
  eapply transl_lvalue_correct; eauto. eapply make_cast_correct; eauto.
  eapply transl_expr_correct; eauto. eapply assign_loc_preserved; eauto. 
  eapply match_states_skip; eauto.
  (* Case 2: variable *)
  destruct (is_variable a1) as []_eqn; monadInv TR.
  assert (SAME: ts' = ts /\ tk' = tk).
    inversion MTR. auto. 
    subst ts. unfold var_set, make_memcpy in EQ0. destruct (access_mode (typeof a1)); congruence.
  destruct SAME; subst ts' tk'.
  exploit is_variable_correct; eauto. intro EQ1. rewrite EQ1 in H.
  econstructor; split.
  apply plus_one. eapply var_set_correct; eauto. exists v2; exists (typeof a2); auto.
  eapply make_cast_correct; eauto. eapply transl_expr_correct; eauto.
  eapply match_states_skip; eauto.
  (* Case 3: everything else *)
  assert (SAME: ts' = ts /\ tk' = tk).
    inversion MTR. auto. 
    subst ts. unfold make_store, make_memcpy in EQ2. destruct (access_mode (typeof a1)); congruence.
  destruct SAME; subst ts' tk'.
  econstructor; split.
  apply plus_one. eapply make_store_correct; eauto.
  eapply transl_lvalue_correct; eauto. eapply make_cast_correct; eauto.
  eapply transl_expr_correct; eauto. eapply assign_loc_preserved; eauto. 
  eapply match_states_skip; eauto.

(* set *)
  monadInv TR. inv MTR. econstructor; split.
  apply plus_one. econstructor. eapply transl_expr_correct; eauto. 
  eapply match_states_skip; eauto.

(* vol read *)
  monadInv TR. 
  assert (SAME: ts' = ts /\ tk' = tk).
    inversion MTR. auto. 
    subst ts. unfold make_vol_load in EQ0. destruct (access_mode (typeof a)); congruence.
  destruct SAME; subst ts' tk'.
  econstructor; split.
  apply plus_one. eapply make_vol_load_correct; eauto. eapply transl_lvalue_correct; eauto.
  eapply deref_loc_preserved; eauto.
  eapply match_states_skip; eauto.

(* call *)
  revert TR. simpl. case_eq (classify_fun (typeof a)); try congruence.
  intros targs tres CF TR. monadInv TR. inv MTR. 
  exploit functions_translated; eauto. intros [tfd [FIND TFD]].
  rewrite H in CF. simpl in CF. inv CF.
  econstructor; split.
  apply plus_one. econstructor; eauto. 
  exploit transl_expr_correct; eauto.
  exploit transl_exprlist_correct; eauto.
  eapply transl_fundef_sig1; eauto.
  rewrite H3. auto.
  econstructor; eauto.  
  econstructor; eauto.
  simpl. auto.
  eapply eval_exprlist_casted; eauto. 

(* seq *)
  monadInv TR. inv MTR.
  econstructor; split.
  apply plus_one. constructor. 
  econstructor; eauto. constructor. 
  econstructor; eauto.

(* skip seq *)
  monadInv TR. inv MTR. inv MK.
  econstructor; split.
  apply plus_one. apply step_skip_seq. 
  econstructor; eauto. constructor.

(* continue seq *)
  monadInv TR. inv MTR. inv MK.
  econstructor; split.
  apply plus_one. constructor. 
  econstructor; eauto. simpl. reflexivity. constructor.

(* break seq *)
  monadInv TR. inv MTR. inv MK.
  econstructor; split.
  apply plus_one. constructor. 
  econstructor; eauto. simpl. reflexivity. constructor.

(* ifthenelse *)
  monadInv TR. inv MTR.
  exploit make_boolean_correct; eauto. 
  exploit transl_expr_correct; eauto.
  intros [v [A B]].
  econstructor; split.
  apply plus_one. apply step_ifthenelse with (v := v) (b := b); auto.
  destruct b; econstructor; eauto; constructor.

(* while false *)
  monadInv TR.
  econstructor; split.
  eapply star_plus_trans. eapply match_transl_step; eauto. 
  eapply plus_left. constructor. 
  eapply star_left. constructor.
  eapply star_trans. eapply exit_if_false_false; eauto.
  eapply star_left. constructor. 
  eapply star_left. constructor.
  apply star_one. constructor.
  reflexivity. reflexivity. reflexivity. reflexivity. reflexivity. traceEq.
  eapply match_states_skip; eauto.

(* while true *)
  monadInv TR.
  econstructor; split.
  eapply star_plus_trans. eapply match_transl_step; eauto. 
  eapply plus_left. constructor.
  eapply star_left. constructor.
  eapply star_trans. eapply exit_if_false_true; eauto.
  eapply star_left. constructor.
  apply star_one. constructor.
  reflexivity. reflexivity. reflexivity. reflexivity. traceEq.
  econstructor; eauto. constructor. 
  econstructor; eauto.

(* skip or continue while *)
  assert ((ts' = Sskip \/ ts' = Sexit ncnt) /\ tk' = tk).
    destruct H; subst x; monadInv TR; inv MTR; auto.
  destruct H0. inv MK.
  econstructor; split.
  eapply plus_left.
  destruct H0; subst ts'; constructor. 
  apply star_one. constructor. traceEq.
  econstructor; eauto.
  simpl. rewrite H8; simpl. rewrite H10; simpl. reflexivity.
  constructor.

(* break while *)
  monadInv TR. inv MTR. inv MK.
  econstructor; split.
  eapply plus_left. constructor.
  eapply star_left. constructor.
  apply star_one. constructor.
  reflexivity. traceEq.
  eapply match_states_skip; eauto.

(* dowhile *)
  monadInv TR.
  econstructor; split.
  eapply star_plus_trans. eapply match_transl_step; eauto. 
  eapply plus_left. constructor.
  eapply star_left. constructor.
  apply star_one. constructor.
  reflexivity. reflexivity. traceEq.
  econstructor; eauto. constructor.
  econstructor; eauto.

(* skip or continue dowhile false *)
  assert ((ts' = Sskip \/ ts' = Sexit ncnt) /\ tk' = tk).
    destruct H; subst x; monadInv TR; inv MTR; auto.
  destruct H2. inv MK.
  econstructor; split.
  eapply plus_left. destruct H2; subst ts'; constructor.
  eapply star_left. constructor.
  eapply star_trans. eapply exit_if_false_false; eauto.
  eapply star_left. constructor.
  apply star_one. constructor.
  reflexivity. reflexivity. reflexivity. traceEq.
  eapply match_states_skip; eauto.

(* skip or continue dowhile true *)
  assert ((ts' = Sskip \/ ts' = Sexit ncnt) /\ tk' = tk).
    destruct H; subst x; monadInv TR; inv MTR; auto.
  destruct H2. inv MK.
  econstructor; split.
  eapply plus_left. destruct H2; subst ts'; constructor.
  eapply star_left. constructor.
  eapply star_trans. eapply exit_if_false_true; eauto.
  apply star_one. constructor.
  reflexivity. reflexivity. traceEq.
  econstructor; eauto.
  simpl. rewrite H10; simpl. rewrite H12; simpl. reflexivity. constructor.

(* break dowhile *)
  monadInv TR. inv MTR. inv MK.
  econstructor; split.
  eapply plus_left. constructor.
  eapply star_left. constructor.
  eapply star_left. constructor.
  apply star_one. constructor.
  reflexivity. reflexivity. traceEq.
  eapply match_states_skip; eauto.

(* for false *)
  monadInv TR.
  econstructor; split.
  eapply star_plus_trans. eapply match_transl_step; eauto.
  eapply plus_left. constructor.
  eapply star_left. constructor.
  eapply star_trans. eapply exit_if_false_false; eauto.
  eapply star_left. constructor. 
  eapply star_left. constructor.
  apply star_one. constructor.
  reflexivity. reflexivity. reflexivity. reflexivity. reflexivity. reflexivity.
  eapply match_states_skip; eauto.

(* for true *)
   monadInv TR.
  econstructor; split.
  eapply star_plus_trans. eapply match_transl_step; eauto.
  eapply plus_left. constructor.
  eapply star_left. constructor.
  eapply star_trans. eapply exit_if_false_true; eauto.
  eapply star_left. constructor. 
  eapply star_left. constructor.
  apply star_one. constructor.
  reflexivity. reflexivity. reflexivity. reflexivity. reflexivity. reflexivity.
  econstructor; eauto. constructor.
  econstructor; eauto. 

(* skip or continue for2 *)
  assert ((ts' = Sskip \/ ts' = Sexit ncnt) /\ tk' = tk).
    destruct H; subst x; monadInv TR; inv MTR; auto.
  destruct H0. inv MK.
  econstructor; split.
  eapply plus_left. destruct H0; subst ts'; constructor.
  apply star_one. constructor. reflexivity. 
  econstructor; eauto. constructor. 
  econstructor; eauto.

(* break for2 *) 
  monadInv TR. inv MTR. inv MK.
  econstructor; split.
  eapply plus_left. constructor.
  eapply star_left. constructor.
  eapply star_left. constructor.
  apply star_one. constructor.
  reflexivity. reflexivity. traceEq.
  eapply match_states_skip; eauto.

(* skip for3 *)
  monadInv TR. inv MTR. inv MK.
  econstructor; split.
  apply plus_one. constructor.
  econstructor; eauto.
  simpl. rewrite H6; simpl. rewrite H8; simpl. rewrite H9; simpl. reflexivity.
  constructor.

(* break for3 *)
  monadInv TR. inv MTR. inv MK.
  econstructor; split.
  eapply plus_left. constructor. apply star_one. constructor. 
  econstructor; eauto.
  eapply match_states_skip; eauto.

(* return none *)
  monadInv TR. inv MTR. 
  econstructor; split.
  apply plus_one. constructor.
  eapply match_env_free_blocks; eauto. 
  econstructor; eauto.
  eapply match_cont_call_cont. eauto. 

(* return some *)
  monadInv TR. inv MTR. 
  econstructor; split.
  apply plus_one. constructor.
(* monadInv TRF. simpl.
  unfold opttyp_of_type. destruct (Clight.fn_return f); try congruence.
  inv H0. inv H3. inv H3. 
*)
  eapply make_cast_correct. eapply transl_expr_correct; eauto. eauto.
  eapply match_env_free_blocks; eauto.
  econstructor; eauto.
  eapply match_cont_call_cont. eauto. 

(* skip call *)
  monadInv TR. inv MTR.
  exploit match_cont_is_call_cont; eauto. intros [A B].
  econstructor; split.
  apply plus_one. apply step_skip_call. auto.
  monadInv TRF. simpl. rewrite H0. auto.
  eapply match_env_free_blocks; eauto.
  constructor. eauto.

(* switch *)
  monadInv TR.
  exploit transl_expr_correct; eauto. intro EV.
  econstructor; split.
  eapply star_plus_trans. eapply match_transl_step; eauto.
  apply plus_one. econstructor. eauto. traceEq. 
  econstructor; eauto.
  apply transl_lbl_stmt_2. apply transl_lbl_stmt_1. eauto. 
  constructor.
  econstructor. eauto.

(* skip or break switch *)
  assert ((ts' = Sskip \/ ts' = Sexit nbrk) /\ tk' = tk).
    destruct H; subst x; monadInv TR; inv MTR; auto.
  destruct H0. inv MK.
  econstructor; split.
  apply plus_one. destruct H0; subst ts'; constructor.
  eapply match_states_skip; eauto.


(* continue switch *)
  monadInv TR. inv MTR. inv MK.
  econstructor; split.
  apply plus_one. constructor. 
  econstructor; eauto. simpl. reflexivity. constructor.

(* label *)
  monadInv TR. inv MTR. 
  econstructor; split.
  apply plus_one. constructor. 
  econstructor; eauto. constructor.

(* goto *)
  monadInv TR. inv MTR.
  generalize TRF. unfold transl_function. intro TRF'. monadInv TRF'.
  exploit (transl_find_label lbl). eexact EQ0. eapply match_cont_call_cont. eauto.
  rewrite H. 
  intros [ts' [tk'' [nbrk' [ncnt' [A [B C]]]]]].
  econstructor; split.
  apply plus_one. constructor. simpl. eexact A. 
  econstructor; eauto. constructor.

(* internal function *)
  monadInv TR. monadInv EQ.
  exploit match_cont_is_call_cont; eauto. intros [A B].
  exploit match_env_alloc_variables; eauto. 
  apply match_env_empty.
  eapply transl_fn_variables; eauto.
  intros [te1 [C D]].
  econstructor; split.
  apply plus_one. econstructor.
  eapply transl_names_norepet; eauto. 
  eexact C. eapply bind_parameters_match; eauto.
  simpl in TY. unfold type_of_function in TY. congruence.
  econstructor; eauto.
  unfold transl_function. rewrite EQ0; simpl. rewrite EQ; simpl. rewrite EQ1; auto. 
  constructor.

(* external function *)
  simpl in TR. 
  destruct (list_typ_eq (sig_args (ef_sig ef)) (typlist_of_typelist targs) &&
            opt_typ_eq (sig_res (ef_sig ef)) (opttyp_of_type tres));
  monadInv TR. 
  exploit match_cont_is_call_cont; eauto. intros [A B].
  econstructor; split.
  apply plus_one. constructor. eauto. 
  eapply external_call_symbols_preserved_2; eauto.
  exact symbols_preserved.
  eexact (Genv.find_var_info_transf_partial2 transl_fundef transl_globvar _ TRANSL).
  eexact (Genv.find_var_info_rev_transf_partial2 transl_fundef transl_globvar _ TRANSL).
  econstructor; eauto.

(* returnstate *)
  inv MK. 
  econstructor; split.
  apply plus_one. constructor.
  econstructor; eauto. simpl; reflexivity. constructor.
  inv MK. 
  econstructor; split.
  apply plus_one. constructor.
  econstructor; eauto. simpl; reflexivity. constructor.
Qed.

Lemma transl_initial_states:
  forall S, Clight.initial_state prog S ->
  exists R, initial_state tprog R /\ match_states S R.
Proof.
  intros. inv H.
  exploit function_ptr_translated; eauto. intros [tf [A B]].
  assert (C: Genv.find_symbol tge (prog_main tprog) = Some b).
    rewrite symbols_preserved. replace (prog_main tprog) with (prog_main prog).
    auto. symmetry. unfold transl_program in TRANSL. 
    eapply transform_partial_program2_main; eauto.
  assert (funsig tf = signature_of_type Tnil type_int32s).
    eapply transl_fundef_sig2; eauto. 
  econstructor; split.
  econstructor; eauto. eapply Genv.init_mem_transf_partial2; eauto. 
  econstructor; eauto. constructor; auto. exact I. red; auto.
Qed.

Lemma transl_final_states:
  forall S R r,
  match_states S R -> Clight.final_state S r -> final_state R r.
Proof.
  intros. inv H0. inv H. inv MK. constructor.
Qed.

Theorem transl_program_correct:
  forward_simulation (Clight.semantics prog) (Csharpminor.semantics tprog).
Proof.
  eapply forward_simulation_plus.
  eexact symbols_preserved.
  eexact transl_initial_states.
  eexact transl_final_states.
  eexact transl_step.
Qed.

End CORRECTNESS.
