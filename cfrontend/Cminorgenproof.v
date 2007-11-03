(** Correctness proof for Cminor generation. *)

Require Import FSets.
Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Csharpminor.
Require Import Op.
Require Import Cminor.
Require Import Cminorgen.

Open Local Scope error_monad_scope.

Section TRANSLATION.

Variable prog: Csharpminor.program.
Variable tprog: program.
Hypothesis TRANSL: transl_program prog = OK tprog.
Let ge : Csharpminor.genv := Genv.globalenv prog.
Let tge: genv := Genv.globalenv tprog.
Let gce : compilenv := build_global_compilenv prog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_transf_partial2 (transl_fundef gce) transl_globvar _ TRANSL).

Lemma function_ptr_translated:
  forall (b: block) (f: Csharpminor.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transl_fundef gce f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial2 (transl_fundef gce) transl_globvar TRANSL).


Lemma functions_translated:
  forall (v: val) (f: Csharpminor.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transl_fundef gce f = OK tf.
Proof (Genv.find_funct_transf_partial2 (transl_fundef gce) transl_globvar TRANSL).

Lemma sig_preserved:
  forall f tf,
  transl_fundef gce f = OK tf -> 
  Cminor.funsig tf = Csharpminor.funsig f.
Proof.
  intros until tf; destruct f; simpl.
  unfold transl_function. destruct (build_compilenv gce f).
  case (zle z Int.max_signed); simpl; try congruence.
  intros. monadInv H. monadInv EQ. reflexivity.
  intro. inv H. reflexivity.
Qed.

Definition global_compilenv_match (ce: compilenv) (gv: gvarenv) : Prop :=
  forall id,
  match ce!!id with
  | Var_global_scalar chunk => gv!id = Some (Vscalar chunk)
  | Var_global_array => True
  | _ => False
  end.

Lemma global_compilenv_charact:
  global_compilenv_match gce (global_var_env prog).
Proof.
  set (mkgve := fun gv (vars: list (ident * list init_data * var_kind)) =>
         List.fold_left
          (fun gve x => match x with (id, init, k) => PTree.set id k gve end)
          vars gv).
  assert (forall vars gv ce,
            global_compilenv_match ce gv ->
            global_compilenv_match (List.fold_left assign_global_variable vars ce)
                                   (mkgve gv vars)).
  induction vars; simpl; intros.
  auto.
  apply IHvars. intro id1. unfold assign_global_variable.
  destruct a as [[id2 init2] lv2]. destruct lv2; simpl; rewrite PMap.gsspec; rewrite PTree.gsspec.
  case (peq id1 id2); intro. auto. apply H. 
  case (peq id1 id2); intro. auto. apply H.

  change (global_var_env prog) with (mkgve (PTree.empty var_kind) prog.(prog_vars)).
  unfold gce, build_global_compilenv. apply H. 
  intro. rewrite PMap.gi. auto.
Qed.

(** * Correspondence between Csharpminor's and Cminor's environments and memory states *)

(** In Csharpminor, every variable is stored in a separate memory block.
  In the corresponding Cminor code, some of these variables reside in
  the local variable environment; others are sub-blocks of the stack data 
  block.  We capture these changes in memory via a memory injection [f]:
- [f b = None] means that the Csharpminor block [b] no longer exist
  in the execution of the generated Cminor code.  This corresponds to
  a Csharpminor local variable translated to a Cminor local variable.
- [f b = Some(b', ofs)] means that Csharpminor block [b] corresponds
  to a sub-block of Cminor block [b] at offset [ofs].

  A memory injection [f] defines a relation [val_inject f] between
  values and a relation [mem_inject f] between memory states.
  These relations, defined in file [Memory], will be used intensively
  in our proof of simulation between Csharpminor and Cminor executions.

  In the remainder of this section, we define relations between
  Csharpminor and Cminor environments and call stacks. *)

(** Matching for a Csharpminor variable [id].
- If this variable is mapped to a Cminor local variable, the
  corresponding Csharpminor memory block [b] must no longer exist in
  Cminor ([f b = None]).  Moreover, the content of block [b] must
  match the value of [id] found in the Cminor local environment [te].
- If this variable is mapped to a sub-block of the Cminor stack data
  at offset [ofs], the address of this variable in Csharpminor [Vptr b
  Int.zero] must match the address of the sub-block [Vptr sp (Int.repr
  ofs)].
*)

Inductive match_var (f: meminj) (id: ident)
                    (e: Csharpminor.env) (m: mem) (te: env) (sp: block) : 
                    var_info -> Prop :=
  | match_var_local:
      forall chunk b v v',
      PTree.get id e = Some (b, Vscalar chunk) ->
      Mem.load chunk m b 0 = Some v ->
      f b = None ->
      PTree.get id te = Some v' ->
      val_inject f v v' ->
      match_var f id e m te sp (Var_local chunk)
  | match_var_stack_scalar:
      forall chunk ofs b,
      PTree.get id e = Some (b, Vscalar chunk) ->
      val_inject f (Vptr b Int.zero) (Vptr sp (Int.repr ofs)) ->
      match_var f id e m te sp (Var_stack_scalar chunk ofs)
  | match_var_stack_array:
      forall ofs sz b,
      PTree.get id e = Some (b, Varray sz) ->
      val_inject f (Vptr b Int.zero) (Vptr sp (Int.repr ofs)) ->
      match_var f id e m te sp (Var_stack_array ofs)
  | match_var_global_scalar:
      forall chunk,
      PTree.get id e = None ->
      PTree.get id (global_var_env prog) = Some (Vscalar chunk) ->
      match_var f id e m te sp (Var_global_scalar chunk)
  | match_var_global_array:
      PTree.get id e = None ->
      match_var f id e m te sp (Var_global_array).

(** Matching between a Csharpminor environment [e] and a Cminor
  environment [te].  The [lo] and [hi] parameters delimit the range
  of addresses for the blocks referenced from [te]. *)

Record match_env (f: meminj) (cenv: compilenv)
                 (e: Csharpminor.env) (m: mem) (te: env) (sp: block)
                 (lo hi: Z) : Prop :=
  mk_match_env {

(** Each variable mentioned in the compilation environment must match
  as defined above. *)
    me_vars:
      forall id, match_var f id e m te sp (PMap.get id cenv);

(** The range [lo, hi] must not be empty. *)
    me_low_high:
      lo <= hi;

(** Every block appearing in the Csharpminor environment [e] must be
  in the range [lo, hi]. *)
    me_bounded:
      forall id b lv, PTree.get id e = Some(b, lv) -> lo <= b < hi;

(** Distinct Csharpminor local variables must be mapped to distinct blocks. *)
    me_inj:
      forall id1 b1 lv1 id2 b2 lv2,
      PTree.get id1 e = Some(b1, lv1) ->
      PTree.get id2 e = Some(b2, lv2) ->
      id1 <> id2 -> b1 <> b2;

(** All blocks mapped to sub-blocks of the Cminor stack data must be in
  the range [lo, hi]. *)
    me_inv:
      forall b delta,
      f b = Some(sp, delta) -> lo <= b < hi;

(** All Csharpminor blocks below [lo] (i.e. allocated before the blocks
  referenced from [e]) must map to blocks that are below [sp]
  (i.e. allocated before the stack data for the current Cminor function). *)
    me_incr:
      forall b tb delta,
      f b = Some(tb, delta) -> b < lo -> tb < sp
  }.

(** Global environments match if the memory injection [f] leaves unchanged
  the references to global symbols and functions. *)

Record match_globalenvs (f: meminj) : Prop := 
  mk_match_globalenvs {
    mg_symbols:
      forall id b,
      Genv.find_symbol ge id = Some b ->
      f b = Some (b, 0) /\ Genv.find_symbol tge id = Some b;
    mg_functions:
      forall b, b < 0 -> f b = Some(b, 0)
  }.

(** Call stacks represent abstractly the execution state of the current
  Csharpminor and Cminor functions, as well as the states of the
  calling functions.  A call stack is a list of frames, each frame
  collecting information on the current execution state of a Csharpminor
  function and its Cminor translation. *)

Record frame : Set :=
  mkframe {
    fr_cenv: compilenv;
    fr_e: Csharpminor.env;
    fr_te: env;
    fr_sp: block;
    fr_low: Z;
    fr_high: Z
  }.

Definition callstack : Set := list frame.

(** Matching of call stacks imply matching of environments for each of
  the frames, plus matching of the global environments, plus disjointness
  conditions over the memory blocks allocated for local variables
  and Cminor stack data. *)

Inductive match_callstack: meminj -> callstack -> Z -> Z -> mem -> Prop :=
  | mcs_nil:
      forall f bound tbound m,
      match_globalenvs f ->
      match_callstack f nil bound tbound m
  | mcs_cons:
      forall f cenv e te sp lo hi cs bound tbound m,
      hi <= bound ->
      sp < tbound ->
      match_env f cenv e m te sp lo hi ->
      match_callstack f cs lo sp m ->
      match_callstack f (mkframe cenv e te sp lo hi :: cs) bound tbound m.

(** The remainder of this section is devoted to showing preservation
  of the [match_callstack] invariant under various assignments and memory
  stores.  First: preservation by memory stores to ``mapped'' blocks
  (block that have a counterpart in the Cminor execution). *)

Lemma match_env_store_mapped:
  forall f cenv e m1 m2 te sp lo hi chunk b ofs v,
  f b <> None ->
  store chunk m1 b ofs v = Some m2 ->
  match_env f cenv e m1 te sp lo hi ->
  match_env f cenv e m2 te sp lo hi.
Proof.
  intros. inversion H1. constructor; auto.
  (* vars *)
  intros. generalize (me_vars0 id); intro. 
  inversion H2; econstructor; eauto.
  rewrite <- H5. eapply load_store_other; eauto. 
  left. congruence.
Qed.

Lemma match_callstack_mapped:
  forall f cs bound tbound m1,
  match_callstack f cs bound tbound m1 ->
  forall chunk b ofs v m2,
  f b <> None ->
  store chunk m1 b ofs v = Some m2 ->
  match_callstack f cs bound tbound m2.
Proof.
  induction 1; intros; econstructor; eauto.
  eapply match_env_store_mapped; eauto.
Qed.

(** Preservation by assignment to a Csharpminor variable that is 
  translated to a Cminor local variable.  The value being assigned
  must be normalized with respect to the memory chunk of the variable,
  in the following sense. *)

Lemma match_env_store_local:
  forall f cenv e m1 m2 te sp lo hi id b chunk v tv,
  e!id = Some(b, Vscalar chunk) ->
  val_inject f (Val.load_result chunk v) tv ->
  store chunk m1 b 0 v = Some m2 ->
  match_env f cenv e m1 te sp lo hi ->
  match_env f cenv e m2 (PTree.set id tv te) sp lo hi.
Proof.
  intros. inversion H2. constructor; auto.
  intros. generalize (me_vars0 id0); intro.
  inversion H3; subst.
  (* var_local *)
  case (peq id id0); intro.
    (* the stored variable *)
    subst id0. 
    change Csharpminor.var_kind with var_kind in H4. 
    rewrite H in H5. injection H5; clear H5; intros; subst b0 chunk0.
    econstructor. eauto. 
    eapply load_store_same; eauto. auto. 
    rewrite PTree.gss. reflexivity.
    auto.
    (* a different variable *)
    econstructor; eauto.
    rewrite <- H6. eapply load_store_other; eauto. 
    rewrite PTree.gso; auto.
  (* var_stack_scalar *)
  econstructor; eauto.
  (* var_stack_array *)
  econstructor; eauto.
  (* var_global_scalar *)
  econstructor; eauto.
  (* var_global_array *)
  econstructor; eauto.
Qed.

Lemma match_env_store_above:
  forall f cenv e m1 m2 te sp lo hi chunk b v,
  store chunk m1 b 0 v = Some m2 ->
  hi <= b ->
  match_env f cenv e m1 te sp lo hi ->
  match_env f cenv e m2 te sp lo hi.
Proof.
  intros. inversion H1; constructor; auto.
  intros. generalize (me_vars0 id); intro.
  inversion H2; econstructor; eauto.
  rewrite <- H5. eapply load_store_other; eauto.
  left. generalize (me_bounded0 _ _ _ H4). unfold block in *. omega.
Qed.

Lemma match_callstack_store_above:
  forall f cs bound tbound m1,
  match_callstack f cs bound tbound m1 ->
  forall chunk b v m2,
  store chunk m1 b 0 v = Some m2 ->
  bound <= b ->
  match_callstack f cs bound tbound m2.
Proof.
  induction 1; intros; econstructor; eauto.
  eapply match_env_store_above with (b := b); eauto. omega.
  eapply IHmatch_callstack; eauto. 
  inversion H1. omega.
Qed.

Lemma match_callstack_store_local:
  forall f cenv e te sp lo hi cs bound tbound m1 m2 id b chunk v tv,
  e!id = Some(b, Vscalar chunk) ->
  val_inject f (Val.load_result chunk v) tv ->
  store chunk m1 b 0 v = Some m2 ->
  match_callstack f (mkframe cenv e te sp lo hi :: cs) bound tbound m1 ->
  match_callstack f (mkframe cenv e (PTree.set id tv te) sp lo hi :: cs) bound tbound m2.
Proof.
  intros. inversion H2. constructor; auto.
  eapply match_env_store_local; eauto.
  eapply match_callstack_store_above; eauto.
  inversion H16. 
  generalize (me_bounded0 _ _ _ H). omega.
Qed.

(** A variant of [match_callstack_store_local] where the Cminor environment
  [te] already associates to [id] a value that matches the assigned value.
  In this case, [match_callstack] is preserved even if no assignment
  takes place on the Cminor side. *)

Lemma match_env_extensional:
  forall f cenv e m te1 sp lo hi,
  match_env f cenv e m te1 sp lo hi ->
  forall te2,
  (forall id, te2!id = te1!id) ->
  match_env f cenv e m te2 sp lo hi.
Proof.
  induction 1; intros; econstructor; eauto.
  intros. generalize (me_vars0 id); intro. 
  inversion H0; econstructor; eauto.
  rewrite H. auto.
Qed.

Lemma match_callstack_store_local_unchanged:
  forall f cenv e te sp lo hi cs bound tbound m1 m2 id b chunk v tv,
  e!id = Some(b, Vscalar chunk) ->
  val_inject f (Val.load_result chunk v) tv ->
  store chunk m1 b 0 v = Some m2 ->
  te!id = Some tv ->
  match_callstack f (mkframe cenv e te sp lo hi :: cs) bound tbound m1 ->
  match_callstack f (mkframe cenv e te sp lo hi :: cs) bound tbound m2.
Proof.
  intros. inversion H3. constructor; auto.
  apply match_env_extensional with (PTree.set id tv te).
  eapply match_env_store_local; eauto.
  intros. rewrite PTree.gsspec. 
  case (peq id0 id); intros. congruence. auto.
  eapply match_callstack_store_above; eauto.
  inversion H17. 
  generalize (me_bounded0 _ _ _ H). omega.
Qed.

(** Preservation of [match_callstack] by freeing all blocks allocated
  for local variables at function entry (on the Csharpminor side). *)

Lemma match_callstack_incr_bound:
  forall f cs bound tbound m,
  match_callstack f cs bound tbound m ->
  forall bound' tbound',
  bound <= bound' -> tbound <= tbound' ->
  match_callstack f cs bound' tbound' m.
Proof.
  intros. inversion H; constructor; auto. omega. omega.
Qed.

Lemma load_freelist:
  forall fbl chunk m b ofs,
  (forall b', In b' fbl -> b' <> b) -> 
  load chunk (free_list m fbl) b ofs = load chunk m b ofs.
Proof.
  induction fbl; simpl; intros.
  auto.
  rewrite load_free. apply IHfbl. 
  intros. apply H. tauto.
  apply sym_not_equal. apply H. tauto.
Qed.

Lemma match_env_freelist:
  forall f cenv e m te sp lo hi fbl,
  match_env f cenv e m te sp lo hi ->
  (forall b, In b fbl -> hi <= b) ->
  match_env f cenv e (free_list m fbl) te sp lo hi.
Proof.
  intros. inversion H. econstructor; eauto.
  intros. generalize (me_vars0 id); intro. 
  inversion H1; econstructor; eauto.
  rewrite <- H4. apply load_freelist. 
  intros. generalize (H0 _ H8); intro. 
  generalize (me_bounded0 _ _ _ H3). unfold block; omega.
Qed.  

Lemma match_callstack_freelist_rec:
  forall f cs bound tbound m,
  match_callstack f cs bound tbound m ->
  forall fbl,
  (forall b, In b fbl -> bound <= b) ->
  match_callstack f cs bound tbound (free_list m fbl).
Proof.
  induction 1; intros; constructor; auto.
  eapply match_env_freelist; eauto. 
  intros. generalize (H3 _ H4). omega.
  apply IHmatch_callstack. intros. 
  generalize (H3 _ H4). inversion H1. omega. 
Qed.

Lemma match_callstack_freelist:
  forall f cenv e te sp lo hi cs bound tbound m fbl,
  (forall b, In b fbl -> lo <= b) ->
  match_callstack f (mkframe cenv e te sp lo hi :: cs) bound tbound m ->
  match_callstack f cs bound tbound (free_list m fbl).
Proof.
  intros. inversion H0. inversion H14.
  apply match_callstack_incr_bound with lo sp.
  apply match_callstack_freelist_rec. auto. 
  assumption.
  omega. omega.
Qed.

(** Preservation of [match_callstack] when allocating a block for
  a local variable on the Csharpminor side.  *)

Lemma load_from_alloc_is_undef:
  forall m1 chunk m2 b,
  alloc m1 0 (size_chunk chunk) = (m2, b) ->
  load chunk m2 b 0 = Some Vundef.
Proof.
  intros.
  assert (exists v, load chunk m2 b 0 = Some v).
    apply valid_access_load.
    eapply valid_access_alloc_same; eauto; omega.
  destruct H0 as [v LOAD]. rewrite LOAD. decEq. 
  eapply load_alloc_same; eauto.
Qed.

Lemma match_env_alloc_same:
  forall m1 lv m2 b info f1 cenv1 e1 te sp lo id data tv,
  alloc m1 0 (sizeof lv) = (m2, b) ->
  match info with
    | Var_local chunk => data = None /\ lv = Vscalar chunk
    | Var_stack_scalar chunk pos => data = Some(sp, pos) /\ lv = Vscalar chunk
    | Var_stack_array pos => data = Some(sp, pos) /\ exists sz, lv = Varray sz
    | Var_global_scalar chunk => False
    | Var_global_array => False
  end ->
  match_env f1 cenv1 e1 m1 te sp lo m1.(nextblock) ->
  te!id = Some tv ->
  let f2 := extend_inject b data f1 in
  let cenv2 := PMap.set id info cenv1 in
  let e2 := PTree.set id (b, lv) e1 in
  inject_incr f1 f2 ->
  match_env f2 cenv2 e2 m2 te sp lo m2.(nextblock).
Proof.
  intros. 
  assert (b = m1.(nextblock)).
    injection H; intros. auto.
  assert (m2.(nextblock) = Zsucc m1.(nextblock)).
    injection H; intros. rewrite <- H6; reflexivity.
  inversion H1. constructor.
  (* me_vars *)
  intros id0. unfold cenv2. rewrite PMap.gsspec. case (peq id0 id); intros.
    (* same var *)
    subst id0. destruct info.
      (* info = Var_local chunk *)
      elim H0; intros.
      apply match_var_local with b Vundef tv.
      unfold e2; rewrite PTree.gss. congruence.
      eapply load_from_alloc_is_undef; eauto. 
      rewrite H7 in H. unfold sizeof in H. eauto.
      unfold f2, extend_inject, eq_block. rewrite zeq_true. auto.
      auto.
      constructor.
      (* info = Var_stack_scalar chunk ofs *)
      elim H0; intros.
      apply match_var_stack_scalar with b. 
      unfold e2; rewrite PTree.gss. congruence.
      eapply val_inject_ptr. 
      unfold f2, extend_inject, eq_block. rewrite zeq_true. eauto.
      rewrite Int.add_commut. rewrite Int.add_zero. auto.
      (* info = Var_stack_array z *)
      elim H0; intros A [sz B].
      apply match_var_stack_array with sz b.
      unfold e2; rewrite PTree.gss. congruence.
      eapply val_inject_ptr. 
      unfold f2, extend_inject, eq_block. rewrite zeq_true. eauto.
      rewrite Int.add_commut. rewrite Int.add_zero. auto.
      (* info = Var_global *)
      contradiction.
      contradiction.
    (* other vars *)
    generalize (me_vars0 id0); intros.
    inversion H6.
    eapply match_var_local with (v := v); eauto.
      unfold e2; rewrite PTree.gso; eauto.
      eapply load_alloc_other; eauto. 
      unfold f2, extend_inject, eq_block; rewrite zeq_false; auto.
      generalize (me_bounded0 _ _ _ H8). unfold block in *; omega.
    econstructor; eauto.
      unfold e2; rewrite PTree.gso; eauto.
    econstructor; eauto. 
      unfold e2; rewrite PTree.gso; eauto. 
    econstructor; eauto.
      unfold e2; rewrite PTree.gso; eauto.
    econstructor; eauto. 
      unfold e2; rewrite PTree.gso; eauto. 
  (* lo <= hi *)
  unfold block in *; omega.
  (* me_bounded *)
  intros until lv0. unfold e2; rewrite PTree.gsspec. 
  case (peq id0 id); intros.
  subst id0. inversion H6. subst b0. unfold block in *; omega. 
  generalize (me_bounded0 _ _ _ H6). rewrite H5. omega.
  (* me_inj *)
  intros until lv2. unfold e2; repeat rewrite PTree.gsspec.
  case (peq id1 id); case (peq id2 id); intros.
  congruence.
  inversion H6. subst b1. rewrite H4. 
    generalize (me_bounded0 _ _ _ H7). unfold block; omega.
  inversion H7. subst b2. rewrite H4.
    generalize (me_bounded0 _ _ _ H6). unfold block; omega.
  eauto.
  (* me_inv *)
  intros until delta. unfold f2, extend_inject, eq_block.
  case (zeq b0 b); intros.
  subst b0. rewrite H4; rewrite H5. omega. 
  generalize (me_inv0 _ _ H6). rewrite H5. omega.
  (* me_incr *)
  intros until delta. unfold f2, extend_inject, eq_block.
  case (zeq b0 b); intros.
  subst b0. unfold block in *; omegaContradiction.
  eauto.
Qed.

Lemma match_env_alloc_other:
  forall f1 cenv e m1 m2 te sp lo hi chunk b data,
  alloc m1 0 (sizeof chunk) = (m2, b) ->
  match data with None => True | Some (b', delta') => sp < b' end ->
  hi <= m1.(nextblock) ->
  match_env f1 cenv e m1 te sp lo hi ->
  let f2 := extend_inject b data f1 in
  inject_incr f1 f2 ->
  match_env f2 cenv e m2 te sp lo hi.
Proof.
  intros. 
  assert (b = m1.(nextblock)). injection H; auto.
  rewrite <- H4 in H1.
  inversion H2. constructor; auto.
  (* me_vars *)
  intros. generalize (me_vars0 id); intro. 
  inversion H5.
  eapply match_var_local with (v := v); eauto.
    eapply load_alloc_other; eauto.
    unfold f2, extend_inject, eq_block. rewrite zeq_false. auto.
    generalize (me_bounded0 _ _ _ H7). unfold block in *; omega.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  (* me_bounded *)
  intros until delta. unfold f2, extend_inject, eq_block.
  case (zeq b0 b); intros. rewrite H5 in H0. omegaContradiction.
  eauto.
  (* me_incr *)
  intros until delta. unfold f2, extend_inject, eq_block.
  case (zeq b0 b); intros. subst b0. omegaContradiction.
  eauto.
Qed.

Lemma match_callstack_alloc_other:
  forall f1 cs bound tbound m1,
  match_callstack f1 cs bound tbound m1 ->
  forall lv m2 b data,
  alloc m1 0 (sizeof lv) = (m2, b) ->
  match data with None => True | Some (b', delta') => tbound <= b' end ->
  bound <= m1.(nextblock) ->
  let f2 := extend_inject b data f1 in
  inject_incr f1 f2 ->
  match_callstack f2 cs bound tbound m2.
Proof.
  induction 1; intros.
  constructor. 
    inversion H. constructor. 
    intros. auto.
    intros. elim (mg_symbols0 _ _ H4); intros.
    split; auto. elim (H3 b0); intros; congruence.
    intros. generalize (mg_functions0 _ H4). elim (H3 b0); congruence.
  constructor. auto. auto. 
  unfold f2; eapply match_env_alloc_other; eauto. 
  destruct data; auto. destruct p. omega. omega. 
  unfold f2; eapply IHmatch_callstack; eauto. 
  destruct data; auto. destruct p. omega. 
  inversion H1; omega.
Qed.

Lemma match_callstack_alloc_left:
  forall m1 lv m2 b info f1 cenv1 e1 te sp lo id data cs tv tbound,
  alloc m1 0 (sizeof lv) = (m2, b) ->
  match info with
    | Var_local chunk => data = None /\ lv = Vscalar chunk
    | Var_stack_scalar chunk pos => data = Some(sp, pos) /\ lv = Vscalar chunk
    | Var_stack_array pos => data = Some(sp, pos) /\ exists sz, lv = Varray sz
    | Var_global_scalar chunk => False
    | Var_global_array => False
  end ->
  match_callstack f1 (mkframe cenv1 e1 te sp lo m1.(nextblock) :: cs) m1.(nextblock) tbound m1 ->
  te!id = Some tv ->
  let f2 := extend_inject b data f1 in
  let cenv2 := PMap.set id info cenv1 in
  let e2 := PTree.set id (b, lv) e1 in
  inject_incr f1 f2 ->
  match_callstack f2 (mkframe cenv2 e2 te sp lo m2.(nextblock) :: cs) m2.(nextblock) tbound m2.
Proof.
  intros. inversion H1. constructor. omega. auto.
  unfold f2, cenv2, e2. eapply match_env_alloc_same; eauto.
  unfold f2; eapply match_callstack_alloc_other; eauto. 
  destruct info.
  elim H0; intros. rewrite H19. auto.
  elim H0; intros. rewrite H19. omega.
  elim H0; intros. rewrite H19. omega.
  contradiction.
  contradiction.
  inversion H17; omega. 
Qed.

Lemma match_callstack_alloc_right:
  forall f cs bound tm1 m tm2 lo hi b,
  alloc tm1 lo hi = (tm2, b) ->
  match_callstack f cs bound tm1.(nextblock) m ->
  match_callstack f cs bound tm2.(nextblock) m.
Proof.
  intros. eapply match_callstack_incr_bound; eauto. omega.
  injection H; intros. rewrite <- H2; simpl. omega.
Qed.

Lemma match_env_alloc:
  forall m1 l h m2 b tm1 tm2 tb f1 ce e te sp lo hi,
  alloc m1 l h = (m2, b) ->
  alloc tm1 l h = (tm2, tb) ->
  match_env f1 ce e m1 te sp lo hi ->
  hi <= m1.(nextblock) ->
  sp < tm1.(nextblock) ->
  let f2 := extend_inject b (Some(tb, 0)) f1 in
  inject_incr f1 f2 ->
  match_env f2 ce e m2 te sp lo hi.
Proof.
  intros. 
  assert (BEQ: b = m1.(nextblock)). injection H; auto.
  assert (TBEQ: tb = tm1.(nextblock)). injection H0; auto.
  inversion H1. constructor; auto.
  (* me_vars *)
  intros. generalize (me_vars0 id); intro. inversion H5.
    (* var_local *)
    eapply match_var_local with (v := v); eauto.
    eapply load_alloc_other; eauto. 
    generalize (me_bounded0 _ _ _ H7). intro. 
    unfold f2, extend_inject. case (zeq b0 b); intro. 
    subst b0. rewrite BEQ in H12. omegaContradiction. 
    auto.
    (* var_stack_scalar *)
    econstructor; eauto.
    (* var_stack_array *)
    econstructor; eauto.
    (* var_global_scalar *)
    econstructor; eauto.
    (* var_global_array *)
    econstructor; eauto.
  (* me_bounded *)
  intros until delta. unfold f2, extend_inject. case (zeq b0 b); intro.
  intro. injection H5; clear H5; intros. 
  rewrite H6 in TBEQ. rewrite TBEQ in H3. omegaContradiction.
  eauto.
  (* me_inj *)
  intros until delta. unfold f2, extend_inject. case (zeq b0 b); intros.
  injection H5; clear H5; intros; subst b0 tb0 delta.
  rewrite BEQ in H6. omegaContradiction. 
  eauto.
Qed.

Lemma match_callstack_alloc_rec:
  forall f1 cs bound tbound m1,
  match_callstack f1 cs bound tbound m1 ->
  forall l h m2 b tm1 tm2 tb,
  alloc m1 l h = (m2, b) ->
  alloc tm1 l h = (tm2, tb) ->
  bound <= m1.(nextblock) ->
  tbound <= tm1.(nextblock) ->
  let f2 := extend_inject b (Some(tb, 0)) f1 in
  inject_incr f1 f2 ->
  match_callstack f2 cs bound tbound m2.
Proof.
  induction 1; intros.
  constructor. 
    inversion H. constructor.
    intros. elim (mg_symbols0 _ _ H5); intros.
    split; auto. elim (H4 b0); intros; congruence.
    intros. generalize (mg_functions0 _ H5). elim (H4 b0); congruence.
  constructor. auto. auto. 
  unfold f2. eapply match_env_alloc; eauto. omega. omega. 
  unfold f2; eapply IHmatch_callstack; eauto.
  inversion H1; omega.
  omega.
Qed.

Lemma match_callstack_alloc:
  forall f1 cs m1 tm1 l h m2 b tm2 tb,
  match_callstack f1 cs m1.(nextblock) tm1.(nextblock) m1 ->
  alloc m1 l h = (m2, b) ->
  alloc tm1 l h = (tm2, tb) ->
  let f2 := extend_inject b (Some(tb, 0)) f1 in
  inject_incr f1 f2 ->
  match_callstack f2 cs m2.(nextblock) tm2.(nextblock) m2.
Proof.
  intros. unfold f2 in *. 
  apply match_callstack_incr_bound with m1.(nextblock) tm1.(nextblock).
  eapply match_callstack_alloc_rec; eauto. omega. omega. 
  injection H0; intros; subst m2; simpl; omega. 
  injection H1; intros; subst tm2; simpl; omega. 
Qed.

(** [match_callstack] implies [match_globalenvs]. *)

Lemma match_callstack_match_globalenvs:
  forall f cs bound tbound m,
  match_callstack f cs bound tbound m ->
  match_globalenvs f.
Proof.
  induction 1; eauto.
Qed.

(** * Correctness of Cminor construction functions *)

Remark val_inject_val_of_bool:
  forall f b, val_inject f (Val.of_bool b) (Val.of_bool b).
Proof.
  intros; destruct b; unfold Val.of_bool, Vtrue, Vfalse; constructor.
Qed.

Remark val_inject_eval_compare_null:
  forall f c i v,  
  eval_compare_null c i = Some v ->
  val_inject f v v.
Proof.
  unfold eval_compare_null; intros.
  destruct (Int.eq i Int.zero). 
  destruct c; inv H; unfold Vfalse, Vtrue; constructor.
  discriminate.
Qed.

Hint Resolve eval_Econst eval_Eunop eval_Ebinop eval_Eload: evalexpr.

Ltac TrivialOp :=
  match goal with
  | [ |- exists y, _ /\ val_inject _ (Vint ?x) _ ] =>
      exists (Vint x); split;
      [eauto with evalexpr | constructor]
  | [ |- exists y, _ /\ val_inject _ (Vfloat ?x) _ ] =>
      exists (Vfloat x); split;
      [eauto with evalexpr | constructor]
  | [ |- exists y, _ /\ val_inject _ (Val.of_bool ?x) _ ] =>
      exists (Val.of_bool x); split;
      [eauto with evalexpr | apply val_inject_val_of_bool]
  | [ |- exists y, Some ?x = Some y /\ val_inject _ _ _ ] =>
      exists x; split; [auto | econstructor; eauto]
  | _ => idtac
  end.

Remark eval_compare_null_inv:
  forall c i v,
  eval_compare_null c i = Some v ->
  i = Int.zero /\ (c = Ceq /\ v = Vfalse \/ c = Cne /\ v = Vtrue).
Proof.
  intros until v. unfold eval_compare_null.
  predSpec Int.eq Int.eq_spec i Int.zero.
  case c; intro EQ; simplify_eq EQ; intro; subst v; tauto.
  congruence.
Qed.

(** Correctness of [transl_constant]. *)

Lemma transl_constant_correct:
  forall f sp cst v,
  Csharpminor.eval_constant cst = Some v ->
  exists tv,
     eval_constant tge sp (transl_constant cst) = Some tv
  /\ val_inject f v tv.
Proof.
  destruct cst; simpl; intros; inv H; TrivialOp.
Qed.

(** Compatibility of [eval_unop] with respect to [val_inject]. *)

Lemma eval_unop_compat:
  forall f op v1 tv1 v,
  eval_unop op v1 = Some v ->
  val_inject f v1 tv1 ->
  exists tv,
     eval_unop op tv1 = Some tv
  /\ val_inject f v tv.
Proof.
  destruct op; simpl; intros.
  inv H; inv H0; simpl; TrivialOp.
  inv H; inv H0; simpl; TrivialOp.
  inv H; inv H0; simpl; TrivialOp.
  inv H; inv H0; simpl; TrivialOp.
  inv H0; inv H. TrivialOp. unfold Vfalse; TrivialOp.
  inv H0; inv H. TrivialOp. unfold Vfalse; TrivialOp.
  inv H0; inv H; TrivialOp.
  inv H0; inv H; TrivialOp.
  inv H0; inv H; TrivialOp.
  inv H0; inv H; TrivialOp.
  inv H0; inv H; TrivialOp.
  inv H0; inv H; TrivialOp.
  inv H0; inv H; TrivialOp.
Qed.

(** Compatibility of [eval_binop] with respect to [val_inject]. *)

Lemma eval_binop_compat:
  forall f op v1 tv1 v2 tv2 v m tm,
  eval_binop op v1 v2 m = Some v ->
  val_inject f v1 tv1 ->
  val_inject f v2 tv2 ->
  mem_inject f m tm ->
  exists tv,
     eval_binop op tv1 tv2 tm = Some tv
  /\ val_inject f v tv.
Proof.
  destruct op; simpl; intros.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
    repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
    repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
    apply Int.sub_add_l.
    destruct (eq_block b1 b0); inv H4. 
    assert (b3 = b2) by congruence. subst b3. 
    unfold eq_block; rewrite zeq_true. TrivialOp.
    replace x0 with x by congruence. decEq. decEq. 
    apply Int.sub_shifted.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
    destruct (Int.eq i0 Int.zero); inv H1. TrivialOp.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
    destruct (Int.eq i0 Int.zero); inv H1. TrivialOp.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
    destruct (Int.eq i0 Int.zero); inv H1. TrivialOp.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
    destruct (Int.eq i0 Int.zero); inv H1. TrivialOp.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
    destruct (Int.ltu i0 (Int.repr 32)); inv H1. TrivialOp.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
    destruct (Int.ltu i0 (Int.repr 32)); inv H1. TrivialOp.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
    destruct (Int.ltu i0 (Int.repr 32)); inv H1. TrivialOp.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
    exists v; split; auto. eapply val_inject_eval_compare_null; eauto.
    exists v; split; auto. eapply val_inject_eval_compare_null; eauto.
  (* cmp ptr ptr *)
  caseEq (valid_pointer m b1 (Int.signed ofs1) && valid_pointer m b0 (Int.signed ofs0)); 
  intro EQ; rewrite EQ in H4; try discriminate.
  destruct (eq_block b1 b0); inv H4.
  assert (b3 = b2) by congruence. subst b3.
  assert (x0 = x) by congruence. subst x0.
  elim (andb_prop _ _ EQ); intros.
  exists (Val.of_bool (Int.cmp c ofs1 ofs0)); split.
  exploit (Mem.valid_pointer_inject f m tm b0 ofs0); eauto. 
  intro VP; rewrite VP; clear VP.
  exploit (Mem.valid_pointer_inject f m tm b0 ofs1); eauto. 
  intro VP; rewrite VP; clear VP.
  unfold eq_block; rewrite zeq_true; simpl.
  decEq. decEq. rewrite Int.translate_cmp. auto. 
  eapply valid_pointer_inject_no_overflow; eauto.
  eapply valid_pointer_inject_no_overflow; eauto.
  apply val_inject_val_of_bool. 
  (* *)
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
Qed.

(** Correctness of [make_cast].  Note that the resulting Cminor value is
  normalized according to the given memory chunk. *)

Lemma make_cast_correct:
  forall f sp te tm a v tv chunk,
  eval_expr tge sp te tm a tv ->
  val_inject f v tv ->
  exists tv',
     eval_expr tge sp te tm (make_cast chunk a) tv'
  /\ val_inject f (Val.load_result chunk v) tv'.
Proof.
  intros. destruct chunk; simpl make_cast.

  exists (Val.cast8signed tv). 
  split. eauto with evalexpr. inversion H0; simpl; constructor.

  exists (Val.cast8unsigned tv). 
  split. eauto with evalexpr. inversion H0; simpl; constructor.

  exists (Val.cast16signed tv). 
  split. eauto with evalexpr. inversion H0; simpl; constructor.

  exists (Val.cast16unsigned tv). 
  split. eauto with evalexpr. inversion H0; simpl; constructor.

  exists tv.
  split. auto. inversion H0; simpl; econstructor; eauto.

  exists (Val.singleoffloat tv). 
  split. eauto with evalexpr. inversion H0; simpl; constructor.

  exists tv.
  split. auto. inversion H0; simpl; econstructor; eauto.
Qed.

Lemma make_stackaddr_correct:
  forall sp te tm ofs,
  eval_expr tge (Vptr sp Int.zero) te tm
            (make_stackaddr ofs) (Vptr sp (Int.repr ofs)).
Proof.
  intros; unfold make_stackaddr.
  eapply eval_Econst. simpl. decEq. decEq.
  rewrite Int.add_commut. apply Int.add_zero.
Qed.

Lemma make_globaladdr_correct:
  forall sp te tm id b,
  Genv.find_symbol tge id = Some b ->
  eval_expr tge (Vptr sp Int.zero) te tm
            (make_globaladdr id) (Vptr b Int.zero).
Proof.
  intros; unfold make_globaladdr.
  eapply eval_Econst. simpl. rewrite H. auto.
Qed.

(** Correctness of [make_store]. *)

Lemma store_arg_content_inject:
  forall f sp te tm a v va chunk,
  eval_expr tge sp te tm a va ->
  val_inject f v va ->
  exists vb,
     eval_expr tge sp te tm (store_arg chunk a) vb
  /\ val_content_inject f chunk v vb.
Proof.
  intros. 
  assert (exists vb,
       eval_expr tge sp te tm a vb  
    /\ val_content_inject f chunk v vb).
  exists va; split. assumption. constructor. assumption.
  destruct a; simpl store_arg; trivial;
  destruct u; trivial;
  destruct chunk; trivial;
  inv H; simpl in H6; inv H6;
  econstructor; (split; [eauto|idtac]);
  destruct v1; simpl in H0; inv H0; try (constructor; constructor).
  apply val_content_inject_8. auto. apply Int.cast8_unsigned_idem.
  apply val_content_inject_8; auto. apply Int.cast8_unsigned_signed. 
  apply val_content_inject_16; auto. apply Int.cast16_unsigned_idem. 
  apply val_content_inject_16; auto. apply Int.cast16_unsigned_signed. 
  apply val_content_inject_32. apply Float.singleoffloat_idem. 
Qed.

Lemma make_store_correct:
  forall f sp te tm addr tvaddr rhs tvrhs chunk m vaddr vrhs m',
  eval_expr tge sp te tm addr tvaddr ->
  eval_expr tge sp te tm rhs tvrhs ->
  Mem.storev chunk m vaddr vrhs = Some m' ->
  mem_inject f m tm ->
  val_inject f vaddr tvaddr ->
  val_inject f vrhs tvrhs ->
  exists tm',
  exec_stmt tge sp te tm (make_store chunk addr rhs)
                E0 te tm' Out_normal
  /\ mem_inject f m' tm'
  /\ nextblock tm' = nextblock tm.
Proof.
  intros. unfold make_store.
  exploit store_arg_content_inject. eexact H0. eauto. 
  intros [tv [EVAL VCINJ]].
  exploit storev_mapped_inject_1; eauto.
  intros [tm' [STORE MEMINJ]].
  exists tm'.
  split. eapply exec_Sstore; eauto. 
  split. auto.
  unfold storev in STORE; destruct tvaddr; try discriminate.
  eapply nextblock_store; eauto.
Qed.

(** Correctness of the variable accessors [var_get], [var_addr],
  and [var_set]. *)

Lemma var_get_correct:
  forall cenv id a f e te sp lo hi m cs tm b chunk v,
  var_get cenv id = OK a ->
  match_callstack f (mkframe cenv e te sp lo hi :: cs) m.(nextblock) tm.(nextblock) m ->
  mem_inject f m tm ->
  eval_var_ref prog e id b chunk ->
  load chunk m b 0 = Some v ->
  exists tv,
    eval_expr tge (Vptr sp Int.zero) te tm a tv /\
    val_inject f v tv.
Proof.
  unfold var_get; intros.
  assert (match_var f id e m te sp cenv!!id).
    inversion H0. inversion H17. auto.
  inversion H4; subst; rewrite <- H5 in H; inversion H; subst.
  (* var_local *)
  inversion H2; [subst|congruence].
  exists v'; split.
  apply eval_Evar. auto. 
  replace v with v0. auto. congruence.
  (* var_stack_scalar *)
  inversion H2; [subst|congruence].
  assert (b0 = b). congruence. subst b0.
  assert (chunk0 = chunk). congruence. subst chunk0.
  exploit loadv_inject; eauto.
    unfold loadv. eexact H3. 
  intros [tv [LOAD INJ]].
  exists tv; split. 
  eapply eval_Eload; eauto. eapply make_stackaddr_correct; eauto.
  auto.
  (* var_global_scalar *)
  inversion H2; [congruence|subst]. 
  assert (match_globalenvs f). eapply match_callstack_match_globalenvs; eauto.
  inversion H11. destruct (mg_symbols0 _ _ H9) as [A B].
  assert (chunk0 = chunk). congruence. subst chunk0.
  assert (loadv chunk m (Vptr b Int.zero) = Some v). assumption.
  assert (val_inject f (Vptr b Int.zero) (Vptr b Int.zero)).
    econstructor; eauto. 
  generalize (loadv_inject _ _ _ _ _ _ _ H1 H12 H13).
  intros [tv [LOAD INJ]].
  exists tv; split. 
  eapply eval_Eload; eauto. eapply make_globaladdr_correct; eauto.
  auto.
Qed.

Lemma var_addr_correct:
  forall cenv id a f e te sp lo hi m cs tm b,
  match_callstack f (mkframe cenv e te sp lo hi :: cs) m.(nextblock) tm.(nextblock) m ->
  var_addr cenv id = OK a ->
  eval_var_addr prog e id b ->
  exists tv,
    eval_expr tge (Vptr sp Int.zero) te tm a tv /\
    val_inject f (Vptr b Int.zero) tv.
Proof.
  unfold var_addr; intros.
  assert (match_var f id e m te sp cenv!!id).
    inversion H. inversion H15. auto.
  inversion H2; subst; rewrite <- H3 in H0; inversion H0; subst; clear H0.
  (* var_stack_scalar *)
  inversion H1; [subst|congruence]. 
  exists (Vptr sp (Int.repr ofs)); split.
  eapply make_stackaddr_correct.
  replace b with b0. auto. congruence.
  (* var_stack_array *)
  inversion H1; [subst|congruence]. 
  exists (Vptr sp (Int.repr ofs)); split.
  eapply make_stackaddr_correct.
  replace b with b0. auto. congruence.
  (* var_global_scalar *)
  inversion H1; [congruence|subst].
  assert (match_globalenvs f). eapply match_callstack_match_globalenvs; eauto.
  inversion H7. destruct (mg_symbols0 _ _ H6) as [A B].
  exists (Vptr b Int.zero); split.
  eapply make_globaladdr_correct. eauto.
  econstructor; eauto. 
  (* var_global_array *)
  inversion H1; [congruence|subst].
  assert (match_globalenvs f). eapply match_callstack_match_globalenvs; eauto.
  inversion H6. destruct (mg_symbols0 _ _ H5) as [A B].
  exists (Vptr b Int.zero); split.
  eapply make_globaladdr_correct. eauto.
  econstructor; eauto. 
Qed.

Lemma var_set_correct:
  forall cenv id rhs a f e te sp lo hi m cs tm tv v m',
  var_set cenv id rhs = OK a ->
  match_callstack f (mkframe cenv e te sp lo hi :: cs) m.(nextblock) tm.(nextblock) m ->
  eval_expr tge (Vptr sp Int.zero) te tm rhs tv ->
  val_inject f v tv ->
  mem_inject f m tm ->
  exec_assign prog e m id v m' ->
  exists te', exists tm',
    exec_stmt tge (Vptr sp Int.zero) te tm a E0 te' tm' Out_normal /\
    mem_inject f m' tm' /\
    match_callstack f (mkframe cenv e te' sp lo hi :: cs) m'.(nextblock) tm'.(nextblock) m' /\
    (forall id', id' <> id -> te'!id' = te!id').
Proof.
  unfold var_set; intros.
  inv H4. 
  assert (NEXTBLOCK: nextblock m' = nextblock m).
    eapply nextblock_store; eauto.
  inversion H0; subst.
  assert (match_var f id e m te sp cenv!!id). inversion H19; auto.
  inv H4; rewrite <- H7 in H; inv H.
  (* var_local *)
  inversion H5; [subst|congruence]. 
  assert (b0 = b) by congruence. subst b0.
  assert (chunk0 = chunk) by congruence. subst chunk0.
  exploit make_cast_correct; eauto.  
  intros [tv' [EVAL INJ]].
  exists (PTree.set id tv' te); exists tm.
  split. eapply exec_Sassign. eauto. 
  split. eapply store_unmapped_inject; eauto. 
  split. rewrite NEXTBLOCK. eapply match_callstack_store_local; eauto.
  intros. apply PTree.gso; auto.
  (* var_stack_scalar *)
  inversion H5; [subst|congruence].
  assert (b0 = b) by congruence. subst b0.
  assert (chunk0 = chunk) by congruence. subst chunk0.
  assert (storev chunk m (Vptr b Int.zero) v = Some m'). assumption.
  exploit make_store_correct.
    eapply make_stackaddr_correct.
    eauto. eauto. eauto. eauto. eauto. 
  intros [tm' [EVAL [MEMINJ TNEXTBLOCK]]].
  exists te; exists tm'.
  split. auto. split. auto.  
  split. rewrite NEXTBLOCK; rewrite TNEXTBLOCK.
  eapply match_callstack_mapped; eauto. 
  inversion H9; congruence.
  auto.
  (* var_global_scalar *)
  inversion H5; [congruence|subst]. 
  assert (chunk0 = chunk) by congruence. subst chunk0.  
  assert (storev chunk m (Vptr b Int.zero) v = Some m'). assumption.
  assert (match_globalenvs f). eapply match_callstack_match_globalenvs; eauto.
  inversion H12. destruct (mg_symbols0 _ _ H4) as [A B].
  exploit make_store_correct.
    eapply make_globaladdr_correct; eauto.
    eauto. eauto. eauto. eauto. eauto. 
  intros [tm' [EVAL [MEMINJ TNEXTBLOCK]]].
  exists te; exists tm'.
  split. auto. split. auto. 
  split. rewrite NEXTBLOCK; rewrite TNEXTBLOCK.
  eapply match_callstack_mapped; eauto. congruence.
  auto.
Qed.

Lemma match_env_extensional':
  forall f cenv e m te1 sp lo hi,
  match_env f cenv e m te1 sp lo hi ->
  forall te2,
  (forall id, 
     match cenv!!id with
     | Var_local _ => te2!id = te1!id
     | _ => True
     end) ->
  match_env f cenv e m te2 sp lo hi.
Proof.
  induction 1; intros; econstructor; eauto.
  intros. generalize (me_vars0 id); intro. 
  inversion H0; econstructor; eauto.
  generalize (H id). rewrite <- H1. congruence. 
Qed.


Lemma match_callstack_extensional:
  forall f cenv e te1 te2 sp lo hi cs bound tbound m,
  (forall id, 
     match cenv!!id with
     | Var_local _ => te2!id = te1!id
     | _ => True
     end) ->
  match_callstack f (mkframe cenv e te1 sp lo hi :: cs) bound tbound m ->
  match_callstack f (mkframe cenv e te2 sp lo hi :: cs) bound tbound m.
Proof.
  intros. inv H0. constructor; auto. 
  apply match_env_extensional' with te1; auto.
Qed.

Lemma var_set_self_correct:
  forall cenv id a f e te sp lo hi m cs tm tv v m',
  var_set cenv id (Evar id) = OK a ->
  match_callstack f (mkframe cenv e te sp lo hi :: cs) m.(nextblock) tm.(nextblock) m ->
  val_inject f v tv ->
  mem_inject f m tm ->
  exec_assign prog e m id v m' ->
  exists te', exists tm',
    exec_stmt tge (Vptr sp Int.zero) (PTree.set id tv te) tm a E0 te' tm' Out_normal /\
    mem_inject f m' tm' /\
    match_callstack f (mkframe cenv e te' sp lo hi :: cs) m'.(nextblock) tm'.(nextblock) m'.
Proof.
  unfold var_set; intros.
  inv H3. 
  assert (NEXTBLOCK: nextblock m' = nextblock m).
    eapply nextblock_store; eauto.
  inversion H0; subst.
  assert (EVAR: eval_expr tge (Vptr sp Int.zero) (PTree.set id tv te) tm (Evar id) tv).
    constructor. apply PTree.gss.
  assert (match_var f id e m te sp cenv!!id). inversion H18; auto.
  inv H3; rewrite <- H6 in H; inv H.
  (* var_local *)
  inversion H4; [subst|congruence]. 
  assert (b0 = b) by congruence. subst b0.
  assert (chunk0 = chunk) by congruence. subst chunk0.
  exploit make_cast_correct; eauto. 
  intros [tv' [EVAL INJ]].
  exists (PTree.set id tv' (PTree.set id tv te)); exists tm.
  split. eapply exec_Sassign. eauto. 
  split. eapply store_unmapped_inject; eauto. 
  rewrite NEXTBLOCK.
  apply match_callstack_extensional with (PTree.set id tv' te).
  intros. destruct (cenv!!id0); auto. 
  repeat rewrite PTree.gsspec. destruct (peq id0 id); auto. 
  eapply match_callstack_store_local; eauto.
  (* var_stack_scalar *)
  inversion H4; [subst|congruence].
  assert (b0 = b) by congruence. subst b0.
  assert (chunk0 = chunk) by congruence. subst chunk0.
  assert (storev chunk m (Vptr b Int.zero) v = Some m'). assumption.
  exploit make_store_correct.
    eapply make_stackaddr_correct.
    eauto. eauto. eauto. eauto. eauto. 
  intros [tm' [EVAL [MEMINJ TNEXTBLOCK]]].
  exists (PTree.set id tv te); exists tm'.
  split. auto. split. auto.  
  rewrite NEXTBLOCK; rewrite TNEXTBLOCK.
  apply match_callstack_extensional with te.
  intros. caseEq (cenv!!id0); intros; auto.
  rewrite PTree.gsspec. destruct (peq id0 id). congruence. auto.
  eapply match_callstack_mapped; eauto. 
  inversion H8; congruence.
  (* var_global_scalar *)
  inversion H4; [congruence|subst]. 
  assert (chunk0 = chunk) by congruence. subst chunk0.  
  assert (storev chunk m (Vptr b Int.zero) v = Some m'). assumption.
  assert (match_globalenvs f). eapply match_callstack_match_globalenvs; eauto.
  inversion H11. destruct (mg_symbols0 _ _ H3) as [A B].
  exploit make_store_correct.
    eapply make_globaladdr_correct; eauto.
    eauto. eauto. eauto. eauto. eauto. 
  intros [tm' [EVAL [MEMINJ TNEXTBLOCK]]].
  exists (PTree.set id tv te); exists tm'.
  split. auto. split. auto. 
  rewrite NEXTBLOCK; rewrite TNEXTBLOCK.
  apply match_callstack_extensional with te.
  intros. caseEq (cenv!!id0); intros; auto.
  rewrite PTree.gsspec. destruct (peq id0 id). congruence. auto.
  eapply match_callstack_mapped; eauto. congruence.
Qed.

(** * Correctness of stack allocation of local variables *)

(** This section shows the correctness of the translation of Csharpminor
  local variables, either as Cminor local variables or as sub-blocks
  of the Cminor stack data.  This is the most difficult part of the proof. *)

Remark assign_variables_incr:
  forall atk vars cenv sz cenv' sz',
  assign_variables atk vars (cenv, sz) = (cenv', sz') -> sz <= sz'.
Proof.
  induction vars; intros until sz'; simpl.
  intro. replace sz' with sz. omega. congruence.
  destruct a. destruct v. case (Identset.mem i atk); intros.
  generalize (IHvars _ _ _ _ H). 
  generalize (size_chunk_pos m). intro.
  generalize (align_le sz (size_chunk m) H0). omega.
  eauto.
  intro. generalize (IHvars _ _ _ _ H). 
  assert (8 > 0). omega. generalize (align_le sz 8 H0).
  assert (0 <= Zmax 0 z). apply Zmax_bound_l. omega.
  omega.
Qed.

Lemma match_callstack_alloc_variables_rec:
  forall tm sp cenv' sz' te lo cs atk,
  valid_block tm sp ->
  low_bound tm sp = 0 ->
  high_bound tm sp = sz' ->
  sz' <= Int.max_signed ->
  forall e m vars e' m' lb,
  alloc_variables e m vars e' m' lb ->
  forall f cenv sz,
  assign_variables atk vars (cenv, sz) = (cenv', sz') ->
  match_callstack f (mkframe cenv e te sp lo m.(nextblock) :: cs)
                    m.(nextblock) tm.(nextblock) m ->
  mem_inject f m tm ->
  0 <= sz ->
  (forall b delta, f b = Some(sp, delta) -> high_bound m b + delta <= sz) ->
  (forall id lv, In (id, lv) vars -> te!id <> None) ->
  exists f',
     inject_incr f f'
  /\ mem_inject f' m' tm
  /\ match_callstack f' (mkframe cenv' e' te sp lo m'.(nextblock) :: cs)
                        m'.(nextblock) tm.(nextblock) m'.
Proof.
  intros until atk. intros VB LB HB NOOV.
  induction 1.
  (* base case *)
  intros. simpl in H. inversion H; subst cenv sz.
  exists f. split. apply inject_incr_refl. split. auto. auto.
  (* inductive case *)
  intros until sz.
  change (assign_variables atk ((id, lv) :: vars) (cenv, sz))
  with (assign_variables atk vars (assign_variable atk (id, lv) (cenv, sz))).
  caseEq (assign_variable atk (id, lv) (cenv, sz)).
  intros cenv1 sz1 ASV1 ASVS MATCH MINJ SZPOS BOUND DEFINED.
  assert (DEFINED1: forall id0 lv0, In (id0, lv0) vars -> te!id0 <> None).
    intros. eapply DEFINED. simpl. right. eauto.
  assert (exists tv, te!id = Some tv).
    assert (te!id <> None). eapply DEFINED. simpl; left; auto.
    destruct (te!id). exists v; auto. congruence.
  elim H1; intros tv TEID; clear H1.
  generalize ASV1. unfold assign_variable.
  caseEq lv.
  (* 1. lv = LVscalar chunk *)
  intros chunk LV. case (Identset.mem id atk).
  (* 1.1 info = Var_stack_scalar chunk ... *)
    set (ofs := align sz (size_chunk chunk)).
    intro EQ; injection EQ; intros; clear EQ.
    set (f1 := extend_inject b1 (Some (sp, ofs)) f).
    generalize (size_chunk_pos chunk); intro SIZEPOS.
    generalize (align_le sz (size_chunk chunk) SIZEPOS). fold ofs. intro SZOFS.
    assert (mem_inject f1 m1 tm /\ inject_incr f f1).
      assert (Int.min_signed < 0). compute; auto.
      generalize (assign_variables_incr _ _ _ _ _ _ ASVS). intro.
      unfold f1; eapply alloc_mapped_inject; eauto.
      omega. omega. omega. omega. unfold sizeof; rewrite LV. omega. 
      intros. left. generalize (BOUND _ _ H5). omega. 
    elim H3; intros MINJ1 INCR1; clear H3.
    exploit IHalloc_variables; eauto.
      unfold f1; rewrite <- H2; eapply match_callstack_alloc_left; eauto.
      rewrite <- H1. omega.
      intros until delta; unfold f1, extend_inject, eq_block.
      rewrite (high_bound_alloc _ _ _ _ _ H b).
      case (zeq b b1); intros. 
      inversion H3. unfold sizeof; rewrite LV. omega.
      generalize (BOUND _ _ H3). omega. 
    intros [f' [INCR2 [MINJ2 MATCH2]]].
    exists f'; intuition. eapply inject_incr_trans; eauto. 
  (* 1.2 info = Var_local chunk *)
    intro EQ; injection EQ; intros; clear EQ. subst sz1.
    exploit alloc_unmapped_inject; eauto.
    set (f1 := extend_inject b1 None f). intros [MINJ1 INCR1].
    exploit IHalloc_variables; eauto.
      unfold f1; rewrite <- H2; eapply match_callstack_alloc_left; eauto.
      intros until delta; unfold f1, extend_inject, eq_block.
      rewrite (high_bound_alloc _ _ _ _ _ H b).
      case (zeq b b1); intros. discriminate.
      eapply BOUND; eauto.
    intros [f' [INCR2 [MINJ2 MATCH2]]].
    exists f'; intuition. eapply inject_incr_trans; eauto. 
  (* 2. lv = LVarray dim, info = Var_stack_array *)
  intros dim LV EQ. injection EQ; clear EQ; intros.
  assert (0 <= Zmax 0 dim). apply Zmax1. 
  assert (8 > 0). omega.
  generalize (align_le sz 8 H4). intro.
  set (ofs := align sz 8) in *.
  set (f1 := extend_inject b1 (Some (sp, ofs)) f).
  assert (mem_inject f1 m1 tm /\ inject_incr f f1).
    assert (Int.min_signed < 0). compute; auto.
    generalize (assign_variables_incr _ _ _ _ _ _ ASVS). intro.
    unfold f1; eapply alloc_mapped_inject; eauto.
    omega. omega. omega. omega. unfold sizeof; rewrite LV. omega. 
    intros. left. generalize (BOUND _ _ H8). omega. 
  destruct H6 as [MINJ1 INCR1].
  exploit IHalloc_variables; eauto.  
    unfold f1; rewrite <- H2; eapply match_callstack_alloc_left; eauto.
    rewrite <- H1. omega.
    intros until delta; unfold f1, extend_inject, eq_block.
    rewrite (high_bound_alloc _ _ _ _ _ H b).
    case (zeq b b1); intros. 
    inversion H6. unfold sizeof; rewrite LV. omega.
    generalize (BOUND _ _ H6). omega. 
    intros [f' [INCR2 [MINJ2 MATCH2]]].
    exists f'; intuition. eapply inject_incr_trans; eauto. 
Qed.

Lemma set_params_defined:
  forall params args id,
  In id params -> (set_params args params)!id <> None.
Proof.
  induction params; simpl; intros.
  elim H.
  destruct args.
  rewrite PTree.gsspec. case (peq id a); intro.
  congruence. eapply IHparams. elim H; intro. congruence. auto.
  rewrite PTree.gsspec. case (peq id a); intro.
  congruence. eapply IHparams. elim H; intro. congruence. auto.
Qed.

Lemma set_locals_defined:
  forall e vars id,
  In id vars \/ e!id <> None -> (set_locals vars e)!id <> None.
Proof.
  induction vars; simpl; intros.
  tauto.
  rewrite PTree.gsspec. case (peq id a); intro.
  congruence.
  apply IHvars. assert (a <> id). congruence. tauto.
Qed.

Lemma set_locals_params_defined:
  forall args params vars id,
  In id (params ++ vars) ->
  (set_locals vars (set_params args params))!id <> None.
Proof.
  intros. apply set_locals_defined. 
  elim (in_app_or _ _ _ H); intro. 
  right. apply set_params_defined; auto.
  left; auto.
Qed.

(** Preservation of [match_callstack] by simultaneous allocation
  of Csharpminor local variables and of the Cminor stack data block. *)

Lemma match_callstack_alloc_variables:
  forall fn cenv sz m e m' lb tm tm' sp f cs targs,
  build_compilenv gce fn = (cenv, sz) ->
  sz <= Int.max_signed ->
  alloc_variables Csharpminor.empty_env m (fn_variables fn) e m' lb ->
  Mem.alloc tm 0 sz = (tm', sp) ->
  match_callstack f cs m.(nextblock) tm.(nextblock) m ->
  mem_inject f m tm ->
  let tparams := List.map (@fst ident memory_chunk) fn.(Csharpminor.fn_params) in
  let tvars := List.map (@fst ident var_kind) fn.(Csharpminor.fn_vars) in
  let te := set_locals tvars (set_params targs tparams) in
  exists f',
     inject_incr f f'
  /\ mem_inject f' m' tm'
  /\ match_callstack f' (mkframe cenv e te sp m.(nextblock) m'.(nextblock) :: cs)
                        m'.(nextblock) tm'.(nextblock) m'.
Proof.
  intros. 
  assert (SP: sp = nextblock tm). injection H2; auto.
  unfold build_compilenv in H. 
  eapply match_callstack_alloc_variables_rec with (sz' := sz); eauto with mem.
  eapply low_bound_alloc_same; eauto.
  eapply high_bound_alloc_same; eauto.
  (* match_callstack *)
  constructor. omega. change (valid_block tm' sp). eapply valid_new_block; eauto.
  constructor. 
    (* me_vars *)
    intros. generalize (global_compilenv_charact id).
    destruct (gce!!id); intro; try contradiction.
    constructor.
      unfold Csharpminor.empty_env. apply PTree.gempty. auto.
    constructor.
      unfold Csharpminor.empty_env. apply PTree.gempty. 
    (* me_low_high *)
    omega.
    (* me_bounded *)
    intros until lv. unfold Csharpminor.empty_env. rewrite PTree.gempty. congruence.
    (* me_inj *)
    intros until lv2. unfold Csharpminor.empty_env; rewrite PTree.gempty; congruence.
    (* me_inv *)
    intros. exploit mi_mappedblocks; eauto. intro A.
    elim (fresh_block_alloc _ _ _ _ _ H2 A).
    (* me_incr *)
    intros. exploit mi_mappedblocks; eauto. intro A.
    rewrite SP; auto.
  rewrite SP; auto.
  eapply alloc_right_inject; eauto.
  omega.
  intros. exploit mi_mappedblocks; eauto. unfold valid_block; intro.
  unfold block in SP; omegaContradiction.
  (* defined *)
  intros. unfold te. apply set_locals_params_defined. 
  unfold tparams, tvars. unfold fn_variables in H5.
  change Csharpminor.fn_params with Csharpminor.fn_params in H5. 
  change Csharpminor.fn_vars with Csharpminor.fn_vars in H5. 
  elim (in_app_or _ _ _ H5); intros.
  elim (list_in_map_inv _ _ _ H6). intros x [A B].
  apply in_or_app; left. inversion A. apply List.in_map. auto.
  apply in_or_app; right. 
  change id with (fst (id, lv)). apply List.in_map; auto.
Qed.

(** Characterization of the range of addresses for the blocks allocated
  to hold Csharpminor local variables. *)

Lemma alloc_variables_nextblock_incr:
  forall e1 m1 vars e2 m2 lb,
  alloc_variables e1 m1 vars e2 m2 lb ->
  nextblock m1 <= nextblock m2.
Proof.
  induction 1; intros.
  omega.
  inversion H; subst m1; simpl in IHalloc_variables. omega.
Qed.

Lemma alloc_variables_list_block:
  forall e1 m1 vars e2 m2 lb,
  alloc_variables e1 m1 vars e2 m2 lb ->
  forall b, m1.(nextblock) <= b < m2.(nextblock) <-> In b lb.
Proof.
  induction 1; intros.
  simpl; split; intro. omega. contradiction.
  elim (IHalloc_variables b); intros A B.
  assert (nextblock m = b1). injection H; intros. auto.
  assert (nextblock m1 = Zsucc (nextblock m)).
    injection H; intros; subst m1; reflexivity.
  simpl; split; intro. 
  assert (nextblock m = b \/ nextblock m1 <= b < nextblock m2).
    unfold block; rewrite H2; omega.
  elim H4; intro. left; congruence. right; auto.
  elim H3; intro. subst b b1. 
  generalize (alloc_variables_nextblock_incr _ _ _ _ _ _ H0).
  rewrite H2. omega.
  generalize (B H4). rewrite H2. omega.
Qed.

(** Correctness of the code generated by [store_parameters]
  to store in memory the values of parameters that are stack-allocated. *)

Inductive vars_vals_match:
    meminj -> list (ident * memory_chunk) -> list val -> env -> Prop :=
  | vars_vals_nil:
      forall f te,
      vars_vals_match f nil nil te
  | vars_vals_cons:
      forall f te id chunk vars v vals tv,
      te!id = Some tv ->
      val_inject f v tv ->
      vars_vals_match f vars vals te ->
      vars_vals_match f ((id, chunk) :: vars) (v :: vals) te.

Lemma vars_vals_match_extensional:
  forall f vars vals te,
  vars_vals_match f vars vals te ->
  forall te',
  (forall id lv, In (id, lv) vars -> te'!id = te!id) ->
  vars_vals_match f vars vals te'.
Proof.
  induction 1; intros.
  constructor.
  econstructor; eauto. rewrite <- H. eapply H2. left. reflexivity.
  apply IHvars_vals_match. intros. eapply H2; eauto. right. eauto.
Qed.

Lemma store_parameters_correct:
  forall e m1 params vl m2,
  bind_parameters e m1 params vl m2 ->
  forall s f te1 cenv sp lo hi cs tm1,
  vars_vals_match f params vl te1 ->
  list_norepet (List.map (@fst ident memory_chunk) params) ->
  mem_inject f m1 tm1 ->
  match_callstack f (mkframe cenv e te1 sp lo hi :: cs) m1.(nextblock) tm1.(nextblock) m1 ->
  store_parameters cenv params = OK s ->
  exists te2, exists tm2,
     exec_stmt tge (Vptr sp Int.zero)
                   te1 tm1 s
                E0 te2 tm2 Out_normal
  /\ mem_inject f m2 tm2
  /\ match_callstack f (mkframe cenv e te2 sp lo hi :: cs) m2.(nextblock) tm2.(nextblock) m2.
Proof.
  induction 1.
  (* base case *)
  intros; simpl. monadInv H3.
  exists te1; exists tm1. split. constructor. tauto.
  (* inductive case *)
  intros until tm1.  intros VVM NOREPET MINJ MATCH STOREP.
  monadInv STOREP.
  inversion VVM. subst f0 id0 chunk0 vars v vals te.
  inversion NOREPET. subst hd tl.
  exploit var_set_correct; eauto.
    constructor; auto.
    econstructor; eauto.
    econstructor; eauto.
  intros [te2 [tm2 [EXEC1 [MINJ1 [MATCH1 UNCHANGED1]]]]].
  assert (vars_vals_match f params vl te2).
    apply vars_vals_match_extensional with te1; auto.
    intros. apply UNCHANGED1. red; intro; subst id0.
    elim H4. change id with (fst (id, lv)). apply List.in_map. auto.
  exploit IHbind_parameters; eauto.
  intros [te3 [tm3 [EXEC2 [MINJ2 MATCH2]]]].
  exists te3; exists tm3.
  split. econstructor; eauto.
  auto.
Qed.

Lemma vars_vals_match_holds_1:
  forall f params args targs,
  list_norepet (List.map (@fst ident memory_chunk) params) ->
  List.length params = List.length args ->
  val_list_inject f args targs ->
  vars_vals_match f params args
    (set_params targs (List.map (@fst ident memory_chunk) params)).
Proof.
  induction params; destruct args; simpl; intros; try discriminate.
  constructor.
  inversion H1. subst v0 vl targs. 
  inversion H. subst hd tl.
  destruct a as [id chunk]. econstructor. 
  simpl. rewrite PTree.gss. reflexivity.
  auto. 
  apply vars_vals_match_extensional
  with (set_params vl' (map (@fst ident memory_chunk) params)).
  eapply IHparams; eauto. 
  intros. simpl. apply PTree.gso. red; intro; subst id0.
  elim H5. change (fst (id, chunk)) with (fst (id, lv)). 
  apply List.in_map; auto.
Qed.

Lemma vars_vals_match_holds:
  forall f params args targs,
  List.length params = List.length args ->
  val_list_inject f args targs ->
  forall vars,
  list_norepet (List.map (@fst ident var_kind) vars
             ++ List.map (@fst ident memory_chunk) params) ->
  vars_vals_match f params args
    (set_locals (List.map (@fst ident var_kind) vars)
      (set_params targs (List.map (@fst ident memory_chunk) params))).
Proof.
  induction vars; simpl; intros.
  eapply vars_vals_match_holds_1; eauto.
  inversion H1. subst hd tl.
  eapply vars_vals_match_extensional; eauto.
  intros. apply PTree.gso. red; intro; subst id; elim H4.
  apply in_or_app. right. change (fst a) with (fst (fst a, lv)).
  apply List.in_map; auto.
Qed.

Lemma bind_parameters_length:
  forall e m1 params args m2,
  bind_parameters e m1 params args m2 ->
  List.length params = List.length args.
Proof.
  induction 1; simpl; eauto.
Qed.

(** The final result in this section: the behaviour of function entry
  in the generated Cminor code (allocate stack data block and store
  parameters whose address is taken) simulates what happens at function
  entry in the original Csharpminor (allocate one block per local variable
  and initialize the blocks corresponding to function parameters). *)

Lemma function_entry_ok:
  forall fn m e m1 lb vargs m2 f cs tm cenv sz tm1 sp tvargs s,
  alloc_variables empty_env m (fn_variables fn) e m1 lb ->
  bind_parameters e m1 fn.(Csharpminor.fn_params) vargs m2 ->
  match_callstack f cs m.(nextblock) tm.(nextblock) m ->
  build_compilenv gce fn = (cenv, sz) ->
  sz <= Int.max_signed ->
  Mem.alloc tm 0 sz = (tm1, sp) ->
  let te :=
    set_locals (fn_vars_names fn) (set_params tvargs (fn_params_names fn)) in
  val_list_inject f vargs tvargs ->
  mem_inject f m tm ->
  list_norepet (fn_params_names fn ++ fn_vars_names fn) ->
  store_parameters cenv fn.(Csharpminor.fn_params) = OK s ->
  exists f2, exists te2, exists tm2,
     exec_stmt tge (Vptr sp Int.zero)
               te tm1 s
            E0 te2 tm2 Out_normal
  /\ mem_inject f2 m2 tm2
  /\ inject_incr f f2
  /\ match_callstack f2
       (mkframe cenv e te2 sp m.(nextblock) m1.(nextblock) :: cs)
       m2.(nextblock) tm2.(nextblock) m2
  /\ (forall b, m.(nextblock) <= b < m1.(nextblock) <-> In b lb).
Proof.
  intros. 
  exploit bind_parameters_length; eauto. intro LEN1.
  exploit match_callstack_alloc_variables; eauto.
  intros [f1 [INCR1 [MINJ1 MATCH1]]].
  exploit vars_vals_match_holds.
    eauto. apply val_list_inject_incr with f. eauto. eauto. 
    apply list_norepet_append_commut. 
    unfold fn_vars_names in H7. eexact H7.
  intro VVM.
  exploit store_parameters_correct.
    eauto. eauto. 
    unfold fn_params_names in H7. eapply list_norepet_append_left; eauto.
    eexact MINJ1. eauto. eauto. 
  intros [te2 [tm2 [EXEC [MINJ2 MATCH2]]]].
  exists f1; exists te2; exists tm2.
  split; auto. split; auto. split; auto. split; auto.
  intros; eapply alloc_variables_list_block; eauto. 
Qed.

(** * Semantic preservation for the translation *)

(** The proof of semantic preservation uses simulation diagrams of the
  following form:
<<
       e, m1, s ----------------- sp, te1, tm1, ts
          |                                |
         t|                                |t
          v                                v
       e, m2, out --------------- sp, te2, tm2, tout
>>
  where [ts] is the Cminor statement obtained by translating the
  Csharpminor statement [s].  The left vertical arrow is an execution
  of a Csharpminor statement.  The right vertical arrow is an execution
  of a Cminor statement.  The precondition (top vertical bar)
  includes a [mem_inject] relation between the memory states [m1] and [tm1],
  and a [match_callstack] relation for any callstack having
  [e], [te1], [sp] as top frame.  The postcondition (bottom vertical bar)
  is the existence of a memory injection [f2] that extends the injection
  [f1] we started with, preserves the [match_callstack] relation for
  the transformed callstack at the final state, and validates a
  [outcome_inject] relation between the outcomes [out] and [tout].
*)

(** ** Semantic preservation for expressions *)

Remark bool_of_val_inject:
  forall f v tv b,
  Val.bool_of_val v b -> val_inject f v tv -> Val.bool_of_val tv b.
Proof.
  intros. inv H0; inv H; constructor; auto.
Qed.

Lemma transl_expr_correct:
  forall f m tm cenv e te sp lo hi cs
    (MINJ: mem_inject f m tm)
    (MATCH: match_callstack f
             (mkframe cenv e te sp lo hi :: cs)
             m.(nextblock) tm.(nextblock) m),
  forall a v,
  Csharpminor.eval_expr prog e m a v ->
  forall ta
    (TR: transl_expr cenv a = OK ta),
  exists tv,
     eval_expr tge (Vptr sp Int.zero) te tm ta tv
  /\ val_inject f v tv.
Proof.
  induction 3; intros; simpl in TR; try (monadInv TR).
  (* Evar *)
  eapply var_get_correct; eauto.
  (* Eaddrof *)
  eapply var_addr_correct; eauto.
  (* Econst *)
  exploit transl_constant_correct; eauto. intros [tv [A B]].
  exists tv; split. constructor; eauto. eauto.
  (* Eunop *)
  exploit IHeval_expr; eauto. intros [tv1 [EVAL1 INJ1]].
  exploit eval_unop_compat; eauto. intros [tv [EVAL INJ]].
  exists tv; split. econstructor; eauto. auto.
  (* Ebinop *)
  exploit IHeval_expr1; eauto. intros [tv1 [EVAL1 INJ1]].
  exploit IHeval_expr2; eauto. intros [tv2 [EVAL2 INJ2]].
  exploit eval_binop_compat; eauto. intros [tv [EVAL INJ]].
  exists tv; split. econstructor; eauto. auto.
  (* Eload *)
  exploit IHeval_expr; eauto. intros [tv1 [EVAL1 INJ1]].
  exploit loadv_inject; eauto. intros [tv [LOAD INJ]].
  exists tv; split. econstructor; eauto. auto.
  (* Econdition *)
  exploit IHeval_expr1; eauto. intros [tv1 [EVAL1 INJ1]].
  assert (transl_expr cenv (if vb1 then b else c) =
          OK (if vb1 then x0 else x1)).
    destruct vb1; auto.
  exploit IHeval_expr2; eauto. intros [tv2 [EVAL2 INJ2]].
  exists tv2; split. eapply eval_Econdition; eauto.
  eapply bool_of_val_inject; eauto. auto.
Qed.

Lemma transl_exprlist_correct:
  forall f m tm cenv e te sp lo hi cs
    (MINJ: mem_inject f m tm)
    (MATCH: match_callstack f
             (mkframe cenv e te sp lo hi :: cs)
             m.(nextblock) tm.(nextblock) m),
  forall a v,
  Csharpminor.eval_exprlist prog e m a v ->
  forall ta
    (TR: transl_exprlist cenv a = OK ta),
  exists tv,
     eval_exprlist tge (Vptr sp Int.zero) te tm ta tv
  /\ val_list_inject f v tv.
Proof.
  induction 3; intros; monadInv TR.
  exists (@nil val); split. constructor. constructor.
  exploit transl_expr_correct; eauto. intros [tv1 [EVAL1 VINJ1]].
  exploit IHeval_exprlist; eauto. intros [tv2 [EVAL2 VINJ2]].
  exists (tv1 :: tv2); split. constructor; auto. constructor; auto.
Qed.

(** ** Semantic preservation for statements and functions *)

Definition eval_funcall_prop
    (m1: mem) (fn: Csharpminor.fundef) (args: list val) (t: trace) (m2: mem) (res: val) : Prop :=
  forall tfn f1 tm1 cs targs
  (TR: transl_fundef gce fn = OK tfn)
  (MINJ: mem_inject f1 m1 tm1)
  (MATCH: match_callstack f1 cs m1.(nextblock) tm1.(nextblock) m1)
  (ARGSINJ: val_list_inject f1 args targs),
  exists f2, exists tm2, exists tres,
     eval_funcall tge tm1 tfn targs t tm2 tres
  /\ val_inject f2 res tres
  /\ mem_inject f2 m2 tm2
  /\ inject_incr f1 f2
  /\ match_callstack f2 cs m2.(nextblock) tm2.(nextblock) m2.

Inductive outcome_inject (f: meminj) : Csharpminor.outcome -> outcome -> Prop :=
  | outcome_inject_normal:
      outcome_inject f Csharpminor.Out_normal Out_normal
  | outcome_inject_exit:
      forall n, outcome_inject f (Csharpminor.Out_exit n) (Out_exit n)
  | outcome_inject_return_none:
      outcome_inject f (Csharpminor.Out_return None) (Out_return None)
  | outcome_inject_return_some:
      forall v1 v2,
      val_inject f v1 v2 ->
      outcome_inject f (Csharpminor.Out_return (Some v1)) (Out_return (Some v2)).

Definition exec_stmt_prop
    (e: Csharpminor.env) (m1: mem) (s: Csharpminor.stmt) (t: trace) (m2: mem) (out: Csharpminor.outcome): Prop :=
  forall cenv ts f1 te1 tm1 sp lo hi cs
  (TR: transl_stmt cenv s = OK ts)
  (MINJ: mem_inject f1 m1 tm1)
  (MATCH: match_callstack f1
           (mkframe cenv e te1 sp lo hi :: cs)
           m1.(nextblock) tm1.(nextblock) m1),
  exists f2, exists te2, exists tm2, exists tout,
     exec_stmt tge (Vptr sp Int.zero) te1 tm1 ts t te2 tm2 tout
  /\ outcome_inject f2 out tout
  /\ mem_inject f2 m2 tm2
  /\ inject_incr f1 f2
  /\ match_callstack f2
        (mkframe cenv e te2 sp lo hi :: cs)
        m2.(nextblock) tm2.(nextblock) m2.

(* Check (Csharpminor.eval_funcall_ind2 prog eval_funcall_prop exec_stmt_prop). *)

(** There are as many cases in the inductive proof as there are evaluation
  rules in the Csharpminor semantics.  We treat each case as a separate
  lemma. *)

Lemma transl_funcall_internal_correct:
   forall (m : mem) (f : Csharpminor.function) (vargs : list val)
     (e : Csharpminor.env) (m1 : mem) (lb : list block) (m2: mem)
     (t: trace) (m3 : mem) (out : Csharpminor.outcome) (vres : val),
   list_norepet (fn_params_names f ++ fn_vars_names f) ->
   alloc_variables empty_env m (fn_variables f) e m1 lb ->
   bind_parameters e m1 (Csharpminor.fn_params f) vargs m2 ->
   Csharpminor.exec_stmt prog e m2 (Csharpminor.fn_body f) t m3 out ->
   exec_stmt_prop e m2 (Csharpminor.fn_body f) t m3 out ->
   Csharpminor.outcome_result_value out (sig_res (Csharpminor.fn_sig f)) vres ->
   eval_funcall_prop m (Internal f) vargs t (free_list m3 lb) vres.
Proof.
  intros; red. intros tfn f1 tm; intros.
  monadInv TR. generalize EQ.
  unfold transl_function.
  caseEq (build_compilenv gce f); intros cenv stacksize CENV.
  destruct (zle stacksize Int.max_signed); try congruence.
  intro TR. monadInv TR.
  caseEq (alloc tm 0 stacksize). intros tm1 sp ALLOC.
  exploit function_entry_ok; eauto. 
  intros [f2 [te2 [tm2 [STOREPARAM [MINJ2 [INCR12 [MATCH2 BLOCKS]]]]]]].
  red in H3; exploit H3; eauto. 
  intros [f3 [te3 [tm3 [tout [EXECBODY [OUTINJ [MINJ3 [INCR23 MATCH3]]]]]]]].
  assert (exists tvres, 
           outcome_result_value tout f.(Csharpminor.fn_sig).(sig_res) tvres /\
           val_inject f3 vres tvres).
    generalize H4. unfold Csharpminor.outcome_result_value, outcome_result_value.
    inversion OUTINJ. 
    destruct (sig_res (Csharpminor.fn_sig f)); intro. contradiction.
      exists Vundef; split. auto. subst vres; constructor.
    tauto.
    destruct (sig_res (Csharpminor.fn_sig f)); intro. contradiction.
      exists Vundef; split. auto. subst vres; constructor.
    destruct (sig_res (Csharpminor.fn_sig f)); intro. 
      exists v2; split. auto. subst vres; auto.
      contradiction.
  destruct H5 as [tvres [TOUT VINJRES]].
  assert (outcome_free_mem tout tm3 sp = Mem.free tm3 sp).
    inversion OUTINJ; auto.
  exists f3; exists (Mem.free tm3 sp); exists tvres.
  (* execution *)
  split. rewrite <- H5. econstructor; simpl; eauto.
  apply exec_Sseq_continue with E0 te2 tm2 t.
  exact STOREPARAM.
  eexact EXECBODY.
  traceEq.
  (* val_inject *)
  split. assumption.
  (* mem_inject *)
  split. apply free_inject; auto. 
  intros. elim (BLOCKS b1); intros B1 B2. apply B1. inversion MATCH3. inversion H20.
  eapply me_inv0. eauto. 
  (* inject_incr *)
  split. eapply inject_incr_trans; eauto.
  (* match_callstack *)
  assert (forall bl mm, nextblock (free_list mm bl) = nextblock mm).
    induction bl; intros. reflexivity. simpl. auto.
  unfold free; simpl nextblock. rewrite H6. 
  eapply match_callstack_freelist; eauto. 
  intros. elim (BLOCKS b); intros B1 B2. generalize (B2 H7). omega.
Qed.

Lemma transl_funcall_external_correct:
  forall (m : mem) (ef : external_function) (vargs : list val)
         (t : trace) (vres : val),
  event_match ef vargs t vres ->
  eval_funcall_prop m (External ef) vargs t m vres.
Proof.
  intros; red; intros. monadInv TR. 
  exploit event_match_inject; eauto. intros [A B].
  exists f1; exists tm1; exists vres; intuition.
  constructor; auto. 
Qed.

Lemma transl_stmt_Sskip_correct:
  forall (e : Csharpminor.env) (m : mem),
  exec_stmt_prop e m Csharpminor.Sskip E0 m Csharpminor.Out_normal.
Proof.
  intros; red; intros. monadInv TR. 
  exists f1; exists te1; exists tm1; exists Out_normal.
  intuition. constructor. constructor.
Qed.

Lemma transl_stmt_Sassign_correct:
  forall (e : Csharpminor.env) (m : mem) (id : ident)
         (a : Csharpminor.expr) (v : val) (m' : mem),
  Csharpminor.eval_expr prog e m a v ->
  exec_assign prog e m id v m' ->
  exec_stmt_prop e m (Csharpminor.Sassign id a) E0 m' Csharpminor.Out_normal.
Proof.
  intros; red; intros. monadInv TR.
  exploit transl_expr_correct; eauto. intros [tv1 [EVAL1 VINJ1]].
  exploit var_set_correct; eauto. 
  intros [te2 [tm2 [EVAL2 [MINJ2 MATCH2]]]].
  exists f1; exists te2; exists tm2; exists Out_normal.
  intuition. constructor.
Qed.

Lemma transl_stmt_Sstore_correct:
  forall (e : Csharpminor.env) (m : mem) (chunk : memory_chunk)
         (a b : Csharpminor.expr) (v1 v2 : val) (m' : mem),
  Csharpminor.eval_expr prog e m a v1 ->
  Csharpminor.eval_expr prog e m b v2 ->
  storev chunk m v1 v2 = Some m' ->
  exec_stmt_prop e m (Csharpminor.Sstore chunk a b) E0 m' Csharpminor.Out_normal.
Proof.
  intros; red; intros. monadInv TR.
  exploit transl_expr_correct.
    eauto. eauto. eexact H. eauto. 
  intros [tv1 [EVAL1 INJ1]].
  exploit transl_expr_correct.
    eauto. eauto. eexact H0. eauto. 
  intros [tv2 [EVAL2 INJ2]].
  exploit make_store_correct.
    eexact EVAL1. eexact EVAL2. eauto. eauto. eauto. eauto.
  intros [tm2 [EXEC [MINJ2 NEXTBLOCK]]].
  exists f1; exists te1; exists tm2; exists Out_normal.
  intuition. 
  constructor.
  unfold storev in H1; destruct v1; try discriminate.
  inv INJ1.
  rewrite NEXTBLOCK. replace (nextblock m') with (nextblock m).
  eapply match_callstack_mapped; eauto. congruence.
  symmetry. eapply nextblock_store; eauto. 
Qed.

Lemma transl_stmt_Scall_correct:
  forall (e : Csharpminor.env) (m : mem) (optid : option ident)
         (sig : signature) (a : Csharpminor.expr)
         (bl : list Csharpminor.expr) (vf : val) (vargs : list val)
         (f : Csharpminor.fundef) (t : trace) (m1 : mem) (vres : val)
         (m2 : mem),
  Csharpminor.eval_expr prog e m a vf ->
  Csharpminor.eval_exprlist prog e m bl vargs ->
  Genv.find_funct (Genv.globalenv prog) vf = Some f ->
  Csharpminor.funsig f = sig ->
  Csharpminor.eval_funcall prog m f vargs t m1 vres ->
  eval_funcall_prop m f vargs t m1 vres ->
  exec_opt_assign prog e m1 optid vres m2 ->
  exec_stmt_prop e m (Csharpminor.Scall optid sig a bl) t m2 Csharpminor.Out_normal.
Proof.
  intros;red;intros.
  assert (forall tv, val_inject f1 vf tv -> tv = vf).
    intros.
    elim (Genv.find_funct_inv H1). intros bf VF. rewrite VF in H1.
    rewrite Genv.find_funct_find_funct_ptr in H1. 
    generalize (Genv.find_funct_ptr_negative H1). intro.
    assert (match_globalenvs f1). eapply match_callstack_match_globalenvs; eauto.
    generalize (mg_functions _ H8 _ H7). intro.
    rewrite VF in H6. inv H6.  
    decEq. congruence. 
    replace x with 0. reflexivity. congruence.
  inv H5; monadInv TR.
  (* optid = None *)
  exploit transl_expr_correct; eauto. intros [tv1 [EVAL1 VINJ1]].
  exploit transl_exprlist_correct; eauto. intros [tv2 [EVAL2 VINJ2]].
  rewrite <- (H6 _ VINJ1) in H1. 
  elim (functions_translated _ _ H1). intros tf [FIND TRF].
  exploit H4; eauto.
  intros [f2 [tm2 [tres [EVAL3 [VINJ3 [MINJ3 [INCR3 MATCH3]]]]]]].
  exists f2; exists te1; exists tm2; exists Out_normal.
  intuition. eapply exec_Scall; eauto. 
  apply sig_preserved; auto.
  constructor.
  (* optid = Some id *)
  exploit transl_expr_correct; eauto. intros [tv1 [EVAL1 VINJ1]].
  exploit transl_exprlist_correct; eauto. intros [tv2 [EVAL2 VINJ2]].
  rewrite <- (H6 _ VINJ1) in H1. 
  elim (functions_translated _ _ H1). intros tf [FIND TRF].
  exploit H4; eauto.
  intros [f2 [tm2 [tres [EVAL3 [VINJ3 [MINJ3 [INCR3 MATCH3]]]]]]].
  exploit var_set_self_correct.
    eauto. eexact MATCH3. eauto. eauto. eauto. 
  intros [te3 [tm3 [EVAL4 [MINJ4 MATCH4]]]].  
  exists f2; exists te3; exists tm3; exists Out_normal. intuition.
  eapply exec_Sseq_continue. eapply exec_Scall; eauto. 
  apply sig_preserved; auto.
  simpl. eexact EVAL4. traceEq.
  constructor.
Qed.

Lemma transl_stmt_Sseq_continue_correct:
  forall (e : Csharpminor.env) (m : mem) (s1 s2 : Csharpminor.stmt)
         (t1 t2: trace) (m1 m2 : mem) (t: trace) (out : Csharpminor.outcome),
  Csharpminor.exec_stmt prog e m s1 t1 m1 Csharpminor.Out_normal ->
  exec_stmt_prop e m s1 t1 m1 Csharpminor.Out_normal ->
  Csharpminor.exec_stmt prog e m1 s2 t2 m2 out ->
  exec_stmt_prop e m1 s2 t2 m2 out ->
  t = t1 ** t2 ->
  exec_stmt_prop e m (Csharpminor.Sseq s1 s2) t m2 out.
Proof.
  intros; red; intros; monadInv TR.
  exploit H0; eauto.
  intros [f2 [te2 [tm2 [tout1 [EXEC1 [OINJ1 [MINJ2 [INCR2 MATCH2]]]]]]]].
  exploit H2; eauto.
  intros [f3 [te3 [tm3 [tout2 [EXEC2 [OINJ2 [MINJ3 [INCR3 MATCH3]]]]]]]].
  exists f3; exists te3; exists tm3; exists tout2.
  intuition. eapply exec_Sseq_continue; eauto.
  inversion OINJ1. subst tout1. auto.
  eapply inject_incr_trans; eauto.
Qed.

Lemma transl_stmt_Sseq_stop_correct:
  forall (e : Csharpminor.env) (m : mem) (s1 s2 : Csharpminor.stmt)
         (t1: trace) (m1 : mem) (out : Csharpminor.outcome),
  Csharpminor.exec_stmt prog e m s1 t1 m1 out ->
  exec_stmt_prop e m s1 t1 m1 out ->
  out <> Csharpminor.Out_normal ->
  exec_stmt_prop e m (Csharpminor.Sseq s1 s2) t1 m1 out.
Proof.
  intros; red; intros; monadInv TR.
  exploit H0; eauto.
  intros [f2 [te2 [tm2 [tout1 [EXEC1 [OINJ1 [MINJ2 [INCR2 MATCH2]]]]]]]].
  exists f2; exists te2; exists tm2; exists tout1.
  intuition. eapply exec_Sseq_stop; eauto.
  inversion OINJ1; subst out tout1; congruence.
Qed.

Lemma transl_stmt_Sifthenelse_correct:
  forall (e : Csharpminor.env) (m : mem) (a : Csharpminor.expr)
         (sl1 sl2 : Csharpminor.stmt) (v : val) (vb : bool) (t : trace)
         (m' : mem) (out : Csharpminor.outcome),
  Csharpminor.eval_expr prog e m a v ->
  Val.bool_of_val v vb ->
  Csharpminor.exec_stmt prog e m (if vb then sl1 else sl2) t m' out ->
  exec_stmt_prop e m (if vb then sl1 else sl2) t m' out ->
  exec_stmt_prop e m (Csharpminor.Sifthenelse a sl1 sl2) t m' out.
Proof.
  intros; red; intros. monadInv TR.
  exploit transl_expr_correct; eauto.
  intros [tv1 [EVAL1 VINJ1]].
  assert (transl_stmt cenv (if vb then sl1 else sl2) =
          OK (if vb then x0 else x1)). destruct vb; auto.
  exploit H2; eauto.
  intros [f2 [te2 [tm2 [tout [EVAL2 [OINJ [MINJ2 [INCR2 MATCH2]]]]]]]].
  exists f2; exists te2; exists tm2; exists tout.
  intuition. 
  eapply exec_Sifthenelse; eauto.
  eapply bool_of_val_inject; eauto.
Qed.

Lemma transl_stmt_Sloop_loop_correct:
   forall (e : Csharpminor.env) (m : mem) (sl : Csharpminor.stmt)
     (t1: trace) (m1: mem) (t2: trace) (m2 : mem)
     (out : Csharpminor.outcome) (t: trace),
   Csharpminor.exec_stmt prog e m sl t1 m1 Csharpminor.Out_normal ->
   exec_stmt_prop e m sl t1 m1 Csharpminor.Out_normal ->
   Csharpminor.exec_stmt prog e m1 (Csharpminor.Sloop sl) t2 m2 out ->
   exec_stmt_prop e m1 (Csharpminor.Sloop sl) t2 m2 out ->
   t = t1 ** t2 ->
   exec_stmt_prop e m (Csharpminor.Sloop sl) t m2 out.
Proof.
  intros; red; intros. generalize TR; intro TR'; monadInv TR'.
  exploit H0; eauto.
  intros [f2 [te2 [tm2 [tout1 [EVAL1 [OINJ1 [MINJ2 [INCR2 MATCH2]]]]]]]].
  exploit H2; eauto.
  intros [f3 [te3 [tm3 [tout2 [EVAL2 [OINJ2 [MINJ3 [INCR3 MATCH3]]]]]]]].
  exists f3; exists te3; exists tm3; exists tout2.
  intuition. 
  eapply exec_Sloop_loop; eauto.
  inversion OINJ1; subst tout1; eauto.
  eapply inject_incr_trans; eauto.
Qed.

Lemma transl_stmt_Sloop_exit_correct:
   forall (e : Csharpminor.env) (m : mem) (sl : Csharpminor.stmt)
     (t1: trace) (m1 : mem) (out : Csharpminor.outcome),
   Csharpminor.exec_stmt prog e m sl t1 m1 out ->
   exec_stmt_prop e m sl t1 m1 out ->
   out <> Csharpminor.Out_normal ->
   exec_stmt_prop e m (Csharpminor.Sloop sl) t1 m1 out.
Proof.
  intros; red; intros. monadInv TR.
  exploit H0; eauto.
  intros [f2 [te2 [tm2 [tout1 [EVAL1 [OINJ1 [MINJ2 [INCR2 MATCH2]]]]]]]].
  exists f2; exists te2; exists tm2; exists tout1.
  intuition. eapply exec_Sloop_stop; eauto.
  inversion OINJ1; subst out tout1; congruence.
Qed.

Remark outcome_block_inject:
  forall f out tout,
  outcome_inject f out tout ->
  outcome_inject f (Csharpminor.outcome_block out) (outcome_block tout).
Proof.
  induction 1; simpl.
  constructor.
  destruct n; constructor.
  constructor.
  constructor; auto.
Qed.

Lemma transl_stmt_Sblock_correct:
   forall (e : Csharpminor.env) (m : mem) (sl : Csharpminor.stmt)
     (t1: trace) (m1 : mem) (out : Csharpminor.outcome),
   Csharpminor.exec_stmt prog e m sl t1 m1 out ->
   exec_stmt_prop e m sl t1 m1 out ->
   exec_stmt_prop e m (Csharpminor.Sblock sl) t1 m1
     (Csharpminor.outcome_block out).
Proof.
  intros; red; intros. monadInv TR.
  exploit H0; eauto.
  intros [f2 [te2 [tm2 [tout1 [EVAL1 [OINJ1 [MINJ2 [INCR2 MATCH2]]]]]]]].
  exists f2; exists te2; exists tm2; exists (outcome_block tout1).
  intuition. eapply exec_Sblock; eauto.
  apply outcome_block_inject; auto.
Qed.

Lemma transl_stmt_Sexit_correct:
   forall (e : Csharpminor.env) (m : mem) (n : nat),
   exec_stmt_prop e m (Csharpminor.Sexit n) E0 m (Csharpminor.Out_exit n).
Proof.
  intros; red; intros. monadInv TR.
  exists f1; exists te1; exists tm1; exists (Out_exit n).
  intuition. constructor. constructor.
Qed.

Lemma transl_stmt_Sswitch_correct:
  forall (e : Csharpminor.env) (m : mem) (a : Csharpminor.expr)
         (cases : list (int * nat)) (default : nat) (n : int),
  Csharpminor.eval_expr prog e m a (Vint n) ->
  exec_stmt_prop e m (Csharpminor.Sswitch a cases default) E0 m
                     (Csharpminor.Out_exit (switch_target n default cases)).
Proof.
  intros; red; intros. monadInv TR.
  exploit transl_expr_correct; eauto.
  intros [tv1 [EVAL VINJ1]].
  inv VINJ1.
  exists f1; exists te1; exists tm1; exists (Out_exit (switch_target n default cases)).
  split. constructor. auto.
  split. constructor.
  split. auto.
  split. apply inject_incr_refl.
  auto.
Qed.

Lemma transl_stmt_Sreturn_none_correct:
   forall (e : Csharpminor.env) (m : mem),
   exec_stmt_prop e m (Csharpminor.Sreturn None) E0 m
     (Csharpminor.Out_return None).
Proof.
  intros; red; intros. monadInv TR.
  exists f1; exists te1; exists tm1; exists (Out_return None).
  intuition. constructor. constructor.
Qed.

Lemma transl_stmt_Sreturn_some_correct:
  forall (e : Csharpminor.env) (m : mem) (a : Csharpminor.expr)
         (v : val),
  Csharpminor.eval_expr prog e m a v ->
  exec_stmt_prop e m (Csharpminor.Sreturn (Some a)) E0 m
                     (Csharpminor.Out_return (Some v)).
Proof.
  intros; red; intros; monadInv TR.
  exploit transl_expr_correct; eauto.
  intros [tv1 [EVAL VINJ1]].
  exists f1; exists te1; exists tm1; exists (Out_return (Some tv1)).
  intuition. econstructor; eauto. constructor; auto.
Qed.

(** We conclude by an induction over the structure of the Csharpminor
  evaluation derivation, using the lemmas above for each case. *)

Lemma transl_function_correct:
   forall m1 f vargs t m2 vres,
   Csharpminor.eval_funcall prog m1 f vargs t m2 vres ->
   eval_funcall_prop m1 f vargs t m2 vres.
Proof
  (Csharpminor.eval_funcall_ind2 prog
     eval_funcall_prop
     exec_stmt_prop

     transl_funcall_internal_correct
     transl_funcall_external_correct
     transl_stmt_Sskip_correct
     transl_stmt_Sassign_correct
     transl_stmt_Sstore_correct
     transl_stmt_Scall_correct
     transl_stmt_Sseq_continue_correct
     transl_stmt_Sseq_stop_correct
     transl_stmt_Sifthenelse_correct
     transl_stmt_Sloop_loop_correct
     transl_stmt_Sloop_exit_correct
     transl_stmt_Sblock_correct
     transl_stmt_Sexit_correct
     transl_stmt_Sswitch_correct
     transl_stmt_Sreturn_none_correct
     transl_stmt_Sreturn_some_correct).

Lemma transl_stmt_correct:
   forall e m1 s t m2 out,
   Csharpminor.exec_stmt prog e m1 s t m2 out ->
   exec_stmt_prop e m1 s t m2 out.
Proof
  (Csharpminor.exec_stmt_ind2 prog
     eval_funcall_prop
     exec_stmt_prop

     transl_funcall_internal_correct
     transl_funcall_external_correct
     transl_stmt_Sskip_correct
     transl_stmt_Sassign_correct
     transl_stmt_Sstore_correct
     transl_stmt_Scall_correct
     transl_stmt_Sseq_continue_correct
     transl_stmt_Sseq_stop_correct
     transl_stmt_Sifthenelse_correct
     transl_stmt_Sloop_loop_correct
     transl_stmt_Sloop_exit_correct
     transl_stmt_Sblock_correct
     transl_stmt_Sexit_correct
     transl_stmt_Sswitch_correct
     transl_stmt_Sreturn_none_correct
     transl_stmt_Sreturn_some_correct).

(** ** Semantic preservation for divergence *)

Definition evalinf_funcall_prop
    (m1: mem) (fn: Csharpminor.fundef) (args: list val) (t: traceinf) : Prop :=
  forall tfn f1 tm1 cs targs
  (TR: transl_fundef gce fn = OK tfn)
  (MINJ: mem_inject f1 m1 tm1)
  (MATCH: match_callstack f1 cs m1.(nextblock) tm1.(nextblock) m1)
  (ARGSINJ: val_list_inject f1 args targs),
  evalinf_funcall tge tm1 tfn targs t.

Definition execinf_stmt_prop
    (e: Csharpminor.env) (m1: mem) (s: Csharpminor.stmt) (t: traceinf): Prop :=
  forall cenv ts f1 te1 tm1 sp lo hi cs
  (TR: transl_stmt cenv s = OK ts)
  (MINJ: mem_inject f1 m1 tm1)
  (MATCH: match_callstack f1
           (mkframe cenv e te1 sp lo hi :: cs)
           m1.(nextblock) tm1.(nextblock) m1),
  execinf_stmt tge (Vptr sp Int.zero) te1 tm1 ts t.

Theorem transl_function_divergence_correct:
  forall m1 fn args t,
  Csharpminor.evalinf_funcall prog m1 fn args t ->
  evalinf_funcall_prop m1 fn args t.
Proof.
  unfold evalinf_funcall_prop; cofix FUNCALL.
  assert (STMT: forall e m1 s t,
          Csharpminor.execinf_stmt prog e m1 s t ->
          execinf_stmt_prop e m1 s t).
  unfold execinf_stmt_prop; cofix STMT.
  intros. inv H; simpl in TR; try (monadInv TR).
  (* Scall *)
  assert (forall tv, val_inject f1 vf tv -> tv = vf).
    intros.
    elim (Genv.find_funct_inv H2). intros bf VF. rewrite VF in H2.
    rewrite Genv.find_funct_find_funct_ptr in H2. 
    generalize (Genv.find_funct_ptr_negative H2). intro.
    assert (match_globalenvs f1). eapply match_callstack_match_globalenvs; eauto.
    generalize (mg_functions _ H5 _ H3). intro.
    rewrite VF in H. inv H.  
    decEq. congruence. 
    replace x with 0. reflexivity. congruence.
  destruct optid; monadInv TR.
  (* optid = Some i *)
  destruct (transl_expr_correct _ _ _ _ _ _ _ _ _ _ MINJ MATCH _ _ H0 _ EQ)
  as [tv1 [EVAL1 VINJ1]].
  destruct (transl_exprlist_correct _ _ _ _ _ _ _ _ _ _ MINJ MATCH _ _ H1 _ EQ1)
  as [tv2 [EVAL2 VINJ2]].
  rewrite <- (H _ VINJ1) in H2. 
  elim (functions_translated _ _ H2). intros tf [FIND TRF].
  apply execinf_Sseq_1. eapply execinf_Scall.
  eauto. eauto. eauto. apply sig_preserved; auto. 
  eapply FUNCALL; eauto.
  (* optid = None *)
  destruct (transl_expr_correct _ _ _ _ _ _ _ _ _ _ MINJ MATCH _ _ H0 _ EQ)
  as [tv1 [EVAL1 VINJ1]].
  destruct (transl_exprlist_correct _ _ _ _ _ _ _ _ _ _ MINJ MATCH _ _ H1 _ EQ1)
  as [tv2 [EVAL2 VINJ2]].
  rewrite <- (H _ VINJ1) in H2. 
  elim (functions_translated _ _ H2). intros tf [FIND TRF].
  eapply execinf_Scall.
  eauto. eauto. eauto. apply sig_preserved; auto. 
  eapply FUNCALL; eauto.
  (* Sseq, 1 *)
  apply execinf_Sseq_1. eapply STMT; eauto. 
  (* Sseq, 2 *)
  destruct (transl_stmt_correct _ _ _ _ _ _ H0
            _ _ _ _ _ _ _ _ _ EQ MINJ MATCH)
  as [f2 [te2 [tm2 [tout [EXEC1 [OUT [MINJ2 [INCR12 MATCH2]]]]]]]].
  inv OUT.
  eapply execinf_Sseq_2. eexact EXEC1.
  eapply STMT; eauto. 
  auto.
  (* Sifthenelse, true *)
  destruct (transl_expr_correct _ _ _ _ _ _ _ _ _ _ MINJ MATCH _ _ H0 _ EQ)
  as [tv1 [EVAL1 VINJ1]].
  assert (transl_stmt cenv (if vb then sl1 else sl2) =
          OK (if vb then x0 else x1)). destruct vb; auto.
  eapply execinf_Sifthenelse. eexact EVAL1. 
  eapply bool_of_val_inject; eauto.
  eapply STMT; eauto.
  (* Sloop, body *)
  eapply execinf_Sloop_body. eapply STMT; eauto.
  (* Sloop, loop *)
  destruct (transl_stmt_correct _ _ _ _ _ _ H0
            _ _ _ _ _ _ _ _ _ EQ MINJ MATCH)
  as [f2 [te2 [tm2 [tout [EXEC1 [OUT [MINJ2 [INCR12 MATCH2]]]]]]]].
  inv OUT.
  eapply execinf_Sloop_loop. eexact EXEC1. 
  eapply STMT; eauto. 
  simpl. rewrite EQ. auto. auto.
  (* Sblock *)
  apply execinf_Sblock. eapply STMT; eauto.
  (* stutter *)
  generalize (execinf_stmt_N_inv _ _ _ _ _ _ H0); intro.
  destruct s; try contradiction; monadInv TR.
  apply execinf_Sseq_1. eapply STMT; eauto. 
  apply execinf_Sblock. eapply STMT; eauto.
  (* Sloop_block *)
  destruct (transl_stmt_correct _ _ _ _ _ _ H0
            _ _ _ _ _ _ _ _ _ EQ MINJ MATCH)
  as [f2 [te2 [tm2 [tout [EXEC1 [OUT [MINJ2 [INCR12 MATCH2]]]]]]]].
  inv OUT. 
  eapply execinf_Sloop_loop. eexact EXEC1. 
  eapply STMT with (s := Csharpminor.Sloop sl); eauto.
  apply execinf_Sblock_inv; eauto.
  simpl. rewrite EQ; auto. auto.   
  (* Function *)
  intros. inv H.
  monadInv TR. generalize EQ.
  unfold transl_function.
  caseEq (build_compilenv gce f); intros cenv stacksize CENV.
  destruct (zle stacksize Int.max_signed); try congruence.
  intro TR. monadInv TR.
  caseEq (alloc tm1 0 stacksize). intros tm2 sp ALLOC.
  destruct (function_entry_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            H1 H2 MATCH CENV z ALLOC ARGSINJ MINJ H0 EQ2)
  as [f2 [te2 [tm3 [STOREPARAM [MINJ2 [INCR12 [MATCH2 BLOCKS]]]]]]].
  eapply evalinf_funcall_internal; simpl.
  eauto. reflexivity. eapply execinf_Sseq_2. eexact STOREPARAM. 
  unfold execinf_stmt_prop in STMT. eapply STMT; eauto.
  traceEq.
Qed.

(** ** Semantic preservation for whole programs *)  

(** The [match_globalenvs] relation holds for the global environments
  of the source program and the transformed program. *)

Lemma match_globalenvs_init:
  let m := Genv.init_mem prog in
  let tm := Genv.init_mem tprog in
  let f := fun b => if zlt b m.(nextblock) then Some(b, 0) else None in
  match_globalenvs f.
Proof.
  intros. constructor.
  intros. split.
  unfold f. rewrite zlt_true. auto. unfold m. 
  eapply Genv.find_symbol_not_fresh; eauto.
  rewrite <- H. apply symbols_preserved.
  intros. unfold f. rewrite zlt_true. auto.
  generalize (nextblock_pos m). omega.
Qed.

(** The correctness of the translation of a whole Csharpminor program
  follows. *)

Theorem transl_program_correct:
  forall beh,
  Csharpminor.exec_program prog beh ->
  exec_program tprog beh.
Proof.
  intros.
  set (m0 := Genv.init_mem prog) in *.
  set (f := meminj_init m0).
  assert (MINJ0: mem_inject f m0 m0).
    unfold f; apply init_inject. 
    unfold m0; apply Genv.initmem_inject_neutral.
  assert (MATCH0: match_callstack f nil m0.(nextblock) m0.(nextblock) m0).
    constructor. unfold f; apply match_globalenvs_init.
  inv H.
  (* Terminating case *)
  subst ge0 m1. 
  elim (function_ptr_translated _ _ H1). intros tfn [TFIND TR].
  fold ge in H3.
  exploit transl_function_correct; eauto.
  intros [f1 [tm1 [tres [TEVAL [VINJ [MINJ1 [INCR MATCH1]]]]]]].
  econstructor; eauto. 
  fold tge. rewrite <- H0. fold ge. 
  replace (prog_main prog) with (AST.prog_main tprog). apply symbols_preserved.
  apply transform_partial_program2_main with (transl_fundef gce) transl_globvar. assumption.
  rewrite <- H2. apply sig_preserved; auto.
  rewrite (Genv.init_mem_transf_partial2 (transl_fundef gce) transl_globvar _ TRANSL).
  inv VINJ. fold tge; fold m0. eexact TEVAL.
  (* Diverging case *)
  subst ge0 m1. 
  elim (function_ptr_translated _ _ H1). intros tfn [TFIND TR].
  econstructor; eauto.
  fold tge. rewrite <- H0. fold ge. 
  replace (prog_main prog) with (AST.prog_main tprog). apply symbols_preserved.
  apply transform_partial_program2_main with (transl_fundef gce) transl_globvar. assumption.
  rewrite <- H2. apply sig_preserved; auto.
  rewrite (Genv.init_mem_transf_partial2 (transl_fundef gce) transl_globvar _ TRANSL).
  fold tge; fold m0.
  eapply (transl_function_divergence_correct _ _ _ _ H3); eauto.
Qed.

End TRANSLATION.