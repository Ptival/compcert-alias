Require Import BinInt.

Require Import AST.
Require Import Coqlib.
Require Import Globalenvs.
Require Import Integers.
Require Import Kildall.
Require Import Maps.
Require Import Memory.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Values.

Require Import AliasAbstract.
Require Import AliasLib.
Require Import AliasMemMap.
Require Import AliasPTSet.
Require Import AliasRegMap.
Require Import AliasSolver.
Require Import AliasTransfer.

Definition abstracter := block -> option ablock.

Definition valsat (v: val) (abs: abstracter) (s: PTSet.t) :=
  match v with
  | Vptr b o =>
    match abs b with
    | Some ab => PTSet.In (Loc ab o) s
    | None    => PTSet.ge s PTSet.top
    end
  | _        => True
  end.
Hint Unfold valsat: unalias.

Definition regsat (r: reg) (rs: regset) (abs: abstracter) (rmap: RegMap.t) :=
  valsat rs#r abs (RegMap.get r rmap).
Hint Unfold regsat: unalias.

Definition memsat
  (b: block) (o: Int.int) (m: mem) (abs: abstracter) (mmap: MemMap.t)
  :=
  forall v
    (LOAD: Mem.loadv Mint32 m (Vptr b o) = Some v)
    ,
    (match abs b with
     | Some ab => valsat v abs (MemMap.get (Loc ab o) mmap)
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
    abs b = Some (Global i).
Hint Unfold ok_abs_genv : unalias.

(* This is factored out to delay the instantiation of rmap, mmap in ok_stack *)
Inductive ok_abs_result_stack f pc rs rret abs: Prop :=
| ok_abs_result_stack_intro: forall rmap mmap
  (RPC:  (analysis f)#pc = (rmap, mmap))
  (RSAT: forall r, regsat r rs abs rmap)
  (RET:  PTSet.ge (RegMap.get rret rmap) PTSet.top) (* same as eq, easier *)
  (MTOP: MemMap.ge mmap MemMap.top)
  ,
  ok_abs_result_stack f pc rs rret abs.

Inductive ok_stack (ge: genv) (b: block): list stackframe -> Prop :=
| ok_stack_nil:
  ok_stack ge b nil
| ok_stack_cons: forall r f bsp pc rs stk abs
  (STK:  ok_stack ge b stk)
  (MEM:  forall b', abs b' <> None -> (b' < b)%Z)
  (GENV: ok_abs_genv abs ge)
  (SP:   abs bsp = Some Stack)
  (RES:  ok_abs_result_stack f pc rs r abs)
  ,
  ok_stack ge b (Stackframe r f (Vptr bsp Int.zero) pc rs :: stk)
.

(* This is factored out to delay the instantiation of rmap, mmap in satisfy *)
Inductive ok_abs_result f pc rs m abs: Prop :=
| ok_abs_result_intro: forall rmap mmap
  (RPC:  (analysis f)#pc = (rmap, mmap))
  (RSAT: forall r, regsat r rs abs rmap)
  (MSAT: forall b o, memsat b o m abs mmap)
  ,
  ok_abs_result f pc rs m abs.

Inductive satisfy (ge: genv) (abs: abstracter): state -> Prop :=
| satisfy_state: forall cs f bsp pc rs m
  (STK:  ok_stack ge (Mem.nextblock m) cs)
  (MEM:  ok_abs_mem abs m)
  (GENV: ok_abs_genv abs ge)
  (SP:   abs bsp = Some Stack)
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

Lemma regsat_ge1:
  forall rs rmap abs rmap' r
    (RSAT: regsat r rs abs rmap)
    (GE:   RegMap.ge rmap' rmap)
    ,
    regsat r rs abs rmap'.
Proof.
  intros. unalias. destruct (rs#r); auto. destruct (abs b).
  now apply GE. eapply PTSet.ge_trans; eauto.
Qed.

Lemma regsat_ge:
  forall rs rmap abs rmap'
    (RSAT: forall r, regsat r rs abs rmap)
    (GE:   RegMap.ge rmap' rmap)
    ,
    (forall r, regsat r rs abs rmap').
Proof.
  intros. eapply regsat_ge1; eauto.
Qed.

Lemma memsat_ge:
  forall m abs mmap mmap'
    (MSAT: forall b o, memsat b o m abs mmap)
    (GE:   MemMap.ge mmap' mmap)
    ,
    (forall b o, memsat b o m abs mmap').
Proof.
  repeat intro. unalias. specialize (MSAT _ _ _ LOAD).
  destruct (abs b), v as [ | | | bv ov]; auto. destruct (abs bv).
  now apply GE.
  eapply PTSet.ge_trans; eauto.
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
    (forall r, regsat r rs abs RegMap.top).
Proof.
  intros. unalias. destruct (rs#r) as []_eqn; auto. destruct (abs b) as []_eqn.
  apply RegMap.get_top. apply PTSet.In_top.
  apply RegMap.get_top.
Qed.

Notation alias_interprets ge s := (exists abs, satisfy ge abs s).

Theorem alias_interprets_init:
  forall p st
    (IS:   initial_state p st),
    alias_interprets (Genv.globalenv p) st.
Proof.
  intros. inv IS.
  exists (fun b =>
    if zlt b (Mem.nextblock m0)
      then
        match Genv.invert_symbol ge b with
        | Some i => Some (Global i)
        | None   => Some Other
        end
      else None
  ).
  constructor.
  Case "ok_abs_mem".
  split; intros; destruct (zlt b0 (Mem.nextblock m0)); auto. congruence.
  destruct (Genv.invert_symbol); congruence.
  Case "ok_stack".
  constructor.
  Case "ok_abs_genv".
  unalias; intros. destruct (zlt b0 (Mem.nextblock m0)).
  eapply Genv.find_invert_symbol in FIND. unfold ge. now rewrite FIND.
  eapply Genv.find_symbol_not_fresh in FIND; eauto. contradiction.
Qed.

Ltac regsat_intro_unsafe rs r :=
  match goal with
  | H: Vptr _ _ = rs#r |- _ => apply symmetry in H; regsat_intro_unsafe rs r
  | R: (forall r, regsat r rs _ _),
    H: rs#r = Vptr _ _ |- _ =>
      let IN := fresh "IN" in
      pose proof (R r) as IN; unfold regsat, valsat in IN; rewrite H in IN
  end.
Tactic Notation "regsat_intro" constr(rs) constr(r) := regsat_intro_unsafe rs r.

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

Ltac regsat_tac :=
  simpl in *;
  match goal with
  (* Easy case: same rs, higher rmap *)
  | H: forall r, regsat r ?rs ?abs ?rmap
    |- forall r, regsat r ?rs ?abs (RegMap.add _ _ ?rmap) =>
    eapply regsat_ge; [apply H | apply RegMap.ge_add]
  (* Simple cases: assigning something that is not a Vptr *)
  | |- forall r, regsat r _#_<-?v _ _ =>
    let ok := constr : (
      match v with (Vundef | Vint _ | Vfloat _) => true | _ => false end
    ) in
    match v with
    | true  => eapply regsat_assign_not_vptr; [ | auto]; regsat_tac
    | false => fail
    end
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
  | |- PTSet.In _ (RegMap.get ?r (RegMap.add ?r _ _)) =>
    apply RegMap.get_add_same; regsat_tac
  | |- PTSet.ge (RegMap.get ?r (RegMap.add ?r _ _)) _ =>
    eapply PTSet.ge_trans; [apply RegMap.get_add_same | auto]; regsat_tac

  | |- forall r, regsat r _#?res<-_ _ _ =>
    let r := fresh "r" in intro r; destruct (peq res r);
    [ subst; unfold regsat, valsat; rewrite Regmap.gss
    | apply regsat_assign_other
    ];
    regsat_tac
(*
  | c: condition |- _ => destruct c; regsat_tac
  | c: comparison |- _ => destruct c; regsat_tac
*)
  (* Non-recursive cases *)
  | H: _ = Vptr _ _ |- _ => try solve [inv H]
  | H: Vptr _ _ = _ |- _ => try solve [inv H]

  | |- _ => auto
  end.

Ltac crunch_eval :=
  match goal with
  | H: Val.of_optbool _ = _ |- _ => unfold Val.of_optbool in H; crunch_eval
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

Lemma In_unknown_offset:
  forall b o s
    (IN: PTSet.In (Loc b o) s)
    ,
    (forall o', PTSet.In (Loc b o') (unknown_offset s)).
Proof.
  intros. unfold unknown_offset. eapply PTSet.fold_adds_prop; intros; eauto.
  simpl. apply PTSet.loc_In_add_blk.
  destruct y; now apply PTSet.In_add.
Qed.

Theorem In_unknown_offset_same:
  forall p s
    (IN: PTSet.In p s),
    PTSet.In p (unknown_offset s).
Proof.
  intros. unfold unknown_offset. eapply PTSet.fold_adds_prop; intros; eauto.
  destruct p. apply PTSet.In_add_same. apply PTSet.loc_In_add_blk.
  destruct y; now apply PTSet.In_add.
Qed.

Lemma unknown_offset_top:
  forall s
    (GETOP: PTSet.ge s PTSet.top)
    ,
    PTSet.ge (unknown_offset s) PTSet.top.
Proof.
  repeat intro. specialize (GETOP _ H). apply In_unknown_offset_same. auto.
Qed.

Lemma In_shift_offset:
  forall b o s o' oshift
    (IN: PTSet.In (Loc b o) s)
    (SH: o' = Int.add o oshift)
    ,
    PTSet.In (Loc b o') (shift_offset s oshift).
Proof.
  intros. subst. rewrite Int.add_commut.
  unfold shift_offset. eapply PTSet.fold_adds_prop; intros; eauto; simpl.
  apply PTSet.In_add_same.
  destruct y; now apply PTSet.In_add.
Qed.

Lemma shift_offset_top:
  forall s
    (GETOP: PTSet.ge s PTSet.top)
    ,
    (forall oshift, PTSet.ge (shift_offset s oshift) PTSet.top).
Proof.
  repeat intro. clear H. unfold shift_offset.
  apply PTSet.fold_adds_prop with (e := Blk All); intros.
  apply (GETOP (Blk All)). apply PTSet.In_top.
  destruct elt; destruct a; try solve
  [ apply PTSet.In_add_lt; simpl; now intuition
  | apply PTSet.In_add_same
  ].
  destruct y; now apply PTSet.In_add.
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
    (forall b o, memsat b o m abs MemMap.top).
Proof.
  unalias. intros. destruct (abs b) as []_eqn.
  destruct v; auto. destruct (abs b0) as []_eqn.
  apply MemMap.get_top. apply PTSet.In_top.
  apply MemMap.get_top.
  simpl in LOAD. apply load_valid_block in LOAD. now apply OKAM in LOAD.
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

Lemma In_image_of_ptset:
  forall x y mmap s,
    PTSet.In x s ->
    PTSet.In y (MemMap.get x mmap) ->
    PTSet.In y (image_of_ptset s mmap).
Proof.
  intros. unfold image_of_ptset. eapply PTSet.fold_adds_prop; eauto; intros.
  now apply PTSet.ge_join_l.
  now apply PTSet.ge_join_r.
Qed.

Lemma In_add_ptset_to_image:
  forall x y sfrom sto mmap
    (FROM: PTSet.In x sfrom)
    (TO:   PTSet.In y sto)
    ,
    PTSet.In x (MemMap.get y (add_ptset_to_image sfrom sto mmap)).
Proof.
  intros. unfold add_ptset_to_image. eapply PTSet.fold_adds_prop; eauto; intros.
  now apply MemMap.get_add_same.
  now apply MemMap.ge_add.
Qed.

Lemma ge_add_ptset_to_image:
  forall mmap s s',
    MemMap.ge (add_ptset_to_image s s' mmap) mmap.
Proof.
  intros. unfold add_ptset_to_image. apply PTSet.fold_preserves_prop; intros.
  apply MemMap.ge_refl.
  eapply MemMap.ge_trans; eauto. apply MemMap.ge_add.
Qed.

Lemma addr_image_correct:
  forall ge rs rmap abs addr args b o ab s bsp
    (GENV: ok_abs_genv abs ge)
    (SP: abs bsp = Some Stack)
    (RSAT: forall r, regsat r rs abs rmap)
    (EA: eval_addressing ge (Vptr bsp Int.zero) addr rs##args = Some (Vptr b o))
    (ABS: abs b = Some ab)
    (MPTA: addr_image addr args rmap = Some s)
    ,
    PTSet.In (Loc ab o) s.
Proof.
  intros.
  crunch_eval; merge.
  eapply In_shift_offset; eauto.
  apply PTSet.ge_join_r. eapply In_unknown_offset; eauto.
  apply PTSet.ge_join_l. eapply In_unknown_offset; eauto.
  eapply In_unknown_offset; eauto.
  specialize (GENV _ _ Heqo0). merge. apply PTSet.In_singleton.
  specialize (GENV _ _ Heqo). merge. apply PTSet.loc_In_add_blk.
  specialize (GENV _ _ Heqo0). merge. apply PTSet.loc_In_add_blk.
  rewrite Int.add_zero_l. apply PTSet.In_singleton.
Qed.

Lemma fold_left_preserves_prop:
  forall S F (P: S -> Prop) (f: S -> F -> S) l s,
    P s ->
    (forall x y, P x -> P (f x y)) ->
    P (fold_left f l s).
Proof.
  induction l; simpl; auto.
Qed.

Lemma fold_left_adds_prop:
  forall E S (e: E) (P: S -> Prop) (f: S -> E -> S) l s0,
    In e l ->
    (forall x, P (f x e)) ->
    (forall x y, P x -> P (f x y)) ->
    P (fold_left f l s0).
Proof.
  induction l; intros.
  inversion H.
  inversion_clear H. subst.
  simpl. apply fold_left_preserves_prop; auto.
  eapply IHl; eauto.
Qed.

Theorem alias_interprets_step:
  forall ge st t st'
    (AI:   alias_interprets ge st)
    (STEP: step ge st t st')
    ,
    alias_interprets ge st'.
Proof.
  intros. destruct AI as [abs SAT].
  destruct st; destruct st'; try solve [inv STEP]; inv SAT; try inv RES.

  Case "State -> State".
  unfold analysis in RPC. destruct (failure_prone_analysis f) as [res|]_eqn.
  SCase "Kildall terminated".
  pose proof Heqo as FPS.
  eapply Solver.fixpoint_solution with (n:=pc)(s:=pc0) in FPS;
  [ |
  unfold successors; unfold successors_list; rewrite PTree.gmap1;
  inv STEP; rewrite H6; simpl; try destruct b; auto; eapply list_nth_z_in; eauto
  ].
  rewrite RPC in FPS. unfold Solver.L.ge in FPS.
  destruct (res#pc0) as [rmap'' mmap'']_eqn.
  destruct (transf (fn_code f) pc (rmap, mmap)) as [rmap' mmap']_eqn.
  destruct FPS as [RGE MGE].
  inv STEP;
  match goal with A : ?f ! ?pc = _, B : transf ?f ?pc _ = _ |- _ =>
    unfold transf in B; rewrite A in B; inv B
  end;
  try solve [
    exists abs; constructor; auto; econstructor;
    [ unfold analysis; rewrite Heqo; apply Heqt0
    | eapply regsat_ge; eauto | eapply memsat_ge; eauto]
  ].

  SSCase "Iop".
  exists abs; constructor; auto.
  SSSCase "ok_abs_result".
  econstructor.
  SSSSCase "result".
  unfold analysis. rewrite Heqo. eauto.
  SSSSCase "regsat".
  eapply regsat_ge; eauto.

  destruct op; simpl in *; repeat (crunch_eval; regsat_tac).
  SSSSSCase "Oindirectsymbol".
  apply PTSet.In_singleton.
  SSSSSCase "Osub".
  eapply In_unknown_offset; eauto.
  apply unknown_offset_top; auto.
  SSSSSCase "Olea Aindexed".
  eapply In_shift_offset; eauto.
  apply shift_offset_top; auto.
  SSSSSCase "Olea Aindexed2".
  apply PTSet.ge_join_r. eapply In_unknown_offset; eauto.
  eapply PTSet.ge_trans. apply PTSet.ge_join_r. apply unknown_offset_top; auto.
  apply PTSet.ge_join_l. eapply In_unknown_offset; eauto.
  eapply PTSet.ge_trans. apply PTSet.ge_join_l. apply unknown_offset_top; auto.
  SSSSSCase "Olea Aindexed2scaled".
  eapply In_unknown_offset; eauto.
  apply unknown_offset_top; auto.
  SSSSSCase "Olea Aglobal".
  apply PTSet.In_singleton.
  SSSSSCase "Olea Abased".
  apply PTSet.loc_In_add_blk.
  SSSSSCase "Olea Abasedscaled".
  apply PTSet.loc_In_add_blk.
  SSSSSCase "Olea Ainstack".
  rewrite Int.add_zero_l. apply PTSet.In_singleton.
  SSSSCase "memsat".
  eapply memsat_ge; eauto.
  SSCase "Iload".
  exists abs; constructor; auto.
  SSSCase "ok_abs_result".
  econstructor.
  SSSSCase "result".
  unfold analysis. rewrite Heqo. eauto.
  SSSSCase "regsat".
  eapply regsat_ge; eauto.
  destruct chunk; try solve [inv H0;
    eapply regsat_assign_not_vptr;
      [ eapply regsat_ge; [auto | apply RegMap.ge_add]
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
  crunch_eval; inv H0; apply RegMap.get_add_same; eapply In_image_of_ptset;
    eauto; merge.
  eapply In_shift_offset; eauto.
  apply PTSet.ge_join_r. eapply In_unknown_offset; eauto.
  apply PTSet.ge_join_l. eapply In_unknown_offset; eauto.
  eapply In_unknown_offset; eauto.
  specialize (GENV _ _ Heqo2). merge. apply PTSet.In_singleton.
  specialize (GENV _ _ Heqo1). merge. apply PTSet.loc_In_add_blk.
  specialize (GENV _ _ Heqo1). merge. apply PTSet.loc_In_add_blk.
  rewrite Int.add_zero_l. apply PTSet.In_singleton.
  SSSSSSCase "abs b = None".
  crunch_eval; inv H0; (
  eapply PTSet.ge_trans;
    [ apply RegMap.get_add_same
    | repeat intro; eapply In_image_of_ptset; [ | apply MSAT; apply PTSet.In_top]
    ]); merge.
  eapply In_shift_offset; eauto.
  apply PTSet.ge_join_r. eapply In_unknown_offset; eauto.
  apply PTSet.ge_join_l. eapply In_unknown_offset; eauto.
  eapply In_unknown_offset; eauto.
  apply unknown_offset_top; auto. apply PTSet.In_top.
  specialize (GENV _ _ Heqo2). merge. apply PTSet.In_singleton.
  specialize (GENV _ _ Heqo3). merge. apply PTSet.loc_In_add_blk.
  specialize (GENV _ _ Heqo3). merge. apply PTSet.loc_In_add_blk.
  merge. rewrite Int.add_zero_l. apply PTSet.In_singleton.
  SSSSSCase "r <> dst".
  eapply regsat_assign_other; eauto. destruct addr_image; inv H0; auto.
  eapply regsat_ge; eauto. apply RegMap.ge_add.
  SSSSCase "memsat".
  eapply memsat_ge; eauto. eapply MemMap.ge_trans; eauto.
  destruct chunk; try solve [inv H0; apply MemMap.ge_refl].
  destruct addr_image; inv H0; apply MemMap.ge_refl.
  SSCase "Istore".
  assert (MGE': MemMap.ge mmap' mmap) by (
  destruct chunk; try solve [inv H0; apply MemMap.ge_refl];
  destruct addr_image; inv H0;
    [ apply ge_add_ptset_to_image
    | apply MemMap.ge_refl
    ]).
  exists abs. destruct a; try solve [inv H14]. constructor; auto.
  SSSCase "ok_stack".
  erewrite Mem.nextblock_store; eauto.
  SSSCase "ok_abs_mem".
  eapply ok_abs_mem_store; eauto.
  SSSCase "ok_abs_result".
  econstructor.
  SSSSCase "result".
  unfold analysis. rewrite Heqo. eauto.
  SSSSCase "regsat".
  eapply regsat_ge; eauto. eapply RegMap.ge_trans; eauto.
  destruct chunk; try solve [inv H0; apply RegMap.ge_refl].
  destruct addr_image; inv H0; apply RegMap.ge_refl.
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
  now apply MGE'.
  SSSSSSSCase "abs b = None".
  eapply PTSet.ge_trans; eauto.
  SSSSSSCase "Didn't overlap offset o, for another reason".
  simpl in LOAD.
  erewrite Mem.load_store_other in LOAD; eauto; [|right; left; omega]. merge.
  destruct (abs b0) as []_eqn; [|contradiction].
  destruct v; auto.
  destruct (abs b) as []_eqn.
  SSSSSSSCase "abs b = Some".
  now apply MGE'.
  SSSSSSSCase "abs b = None".
  eapply PTSet.ge_trans; eauto.
  SSSSSCase "Didn't store in b0".
  simpl in LOAD. erewrite Mem.load_store_other in LOAD; eauto. merge.
  destruct (abs b0) as []_eqn; [|contradiction].
  destruct v; auto.
  destruct (abs b1) as []_eqn.
  SSSSSSCase "abs b1 = Some".
  now apply MGE'.
  SSSSSSCase "abs b1 = None".
  eapply PTSet.ge_trans; eauto.
  SSCase "Ibuiltin".
  assert (RGE': RegMap.ge rmap' rmap) by (
  destruct ef; repeat (
    try solve [inv H0; apply RegMap.ge_add];
    try solve [inv H0; apply RegMap.ge_refl];
    destruct args)).
  assert (MGE': MemMap.ge mmap' mmap).
  destruct ef; repeat (
    try solve [inv H0; apply ge_add_ptset_to_image];
    try solve [inv H0; apply MemMap.ge_refl];
    try solve [inv H0; apply MemMap.ge_add];
    destruct args).
  destruct ef; inv H13; merge.
  SSSCase "EF_external".
  exists abs. constructor; auto.
  SSSSCase "ok_abs_result".
  econstructor.
  SSSSSCase "result".
  unfold analysis. rewrite Heqo. eauto.
  SSSSSCase "regsat".
  intros; destruct (peq res0 r); [subst | eapply regsat_assign_other; eauto;
    eapply regsat_ge; [eauto | eapply RegMap.ge_trans; eauto]].
  unfold regsat, valsat. rewrite Regmap.gss. destruct v; auto.
  inv H1. specialize (GENV _ _ H4). rewrite GENV.
  eapply PTSet.ge_trans. apply RegMap.get_ge; apply RGE. apply RegMap.get_add_same.
  apply PTSet.In_add_lt. simpl. tauto.
  SSSSSCase "memsat".
  eapply memsat_ge; eauto.
  SSSCase "EF_builtin".
  exists abs. constructor; auto.
  SSSSCase "ok_abs_result".
  econstructor.
  SSSSSCase "result".
  unfold analysis. rewrite Heqo. eauto.
  SSSSSCase "regsat".
  intros; destruct (peq res0 r); [subst | eapply regsat_assign_other; eauto;
    eapply regsat_ge; [eauto | eapply RegMap.ge_trans; eauto]].
  unfold regsat, valsat. rewrite Regmap.gss. destruct v; auto.
  inv H1. specialize (GENV _ _ H4). rewrite GENV.
  eapply PTSet.ge_trans. apply RegMap.get_ge; apply RGE. apply RegMap.get_add_same.
  apply PTSet.In_add_lt. simpl. tauto.
  SSSSSCase "memsat".
  eapply memsat_ge; eauto.
  SSSCase "EF_vload".
  exists abs. constructor; auto.
  SSSSCase "ok_abs_result".
  econstructor.
  SSSSSCase "result".
  unfold analysis. rewrite Heqo. eauto.
  SSSSSCase "regsat".
  intros; destruct (peq res0 r); [subst | eapply regsat_assign_other; eauto;
    eapply regsat_ge; [eauto | eapply RegMap.ge_trans; eauto]].
  unfold regsat, valsat. rewrite Regmap.gss. destruct v; simpl; auto.
  regsat_tac.
  eapply RegMap.get_ge. eauto. apply RegMap.get_add_same. apply PTSet.In_top.
  eapply PTSet.ge_trans. apply RegMap.get_ge. eauto. apply RegMap.get_add_same.
  SSSSSCase "memsat".
  eapply memsat_ge; eauto.
  inv H1. (* Check whether the store is volatile *)
  SSSCase "EF_vstore (volatile)".
  exists abs. constructor; auto.
  SSSSCase "ok_abs_result".
  econstructor.
  SSSSSCase "result".
  unfold analysis. rewrite Heqo. eauto.
  SSSSSCase "regsat".
  intros; destruct (peq res0 r); [subst | eapply regsat_assign_other; eauto;
    eapply regsat_ge; [eauto | eapply RegMap.ge_trans; eauto]].
  unfold regsat, valsat. rewrite Regmap.gss. auto.
  SSSSSCase "memsat".
  eapply memsat_ge; eauto. eapply MemMap.ge_trans; eauto.
  SSSCase "EF_vstore (not volatile)".
  exists abs. constructor; auto.
  SSSSCase "ok_stack".
  erewrite Mem.nextblock_store; eauto.
  SSSSCase "ok_abs_mem".
  eapply ok_abs_mem_store; eauto.
  SSSSCase "ok_abs_result".
  econstructor.
  SSSSSCase "result".
  unfold analysis. rewrite Heqo. eauto.
  SSSSSCase "regsat".
  intros; destruct (peq res0 r); [subst | eapply regsat_assign_other; eauto;
    eapply regsat_ge; [eauto | eapply RegMap.ge_trans; eauto]].
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
  eapply PTSet.ge_trans. repeat intro. apply In_add_ptset_to_image; auto.
  apply H0. easy.
  SSSSSSSCase "Didn't overlap offset o".
  simpl in LOAD.
  erewrite Mem.load_store_other in LOAD; eauto; [|right; right; omega]. merge.
  destruct (abs b0) as []_eqn; [|contradiction].
  destruct v; auto.
  destruct (abs b) as []_eqn.
  SSSSSSSSCase "abs b = Some".
  now apply MGE'.
  SSSSSSSSCase "abs b = None".
  eapply PTSet.ge_trans; eauto.
  SSSSSSSCase "Didn't overlap offset o, for another reason".
  simpl in LOAD.
  erewrite Mem.load_store_other in LOAD; eauto; [|right; left; omega]. merge.
  destruct (abs b0) as []_eqn; [|contradiction].
  destruct v; auto.
  destruct (abs b) as []_eqn.
  SSSSSSSSCase "abs b = Some".
  now apply MGE'.
  SSSSSSSSCase "abs b = None".
  eapply PTSet.ge_trans; eauto.
  SSSSSSCase "Didn't store in b0".
  simpl in LOAD. erewrite Mem.load_store_other in LOAD; eauto. merge.
  destruct (abs b0) as []_eqn; [|contradiction].
  destruct v; auto.
  destruct (abs b1) as []_eqn.
  SSSSSSSCase "abs b1 = Some".
  now apply MGE'.
  SSSSSSSCase "abs b1 = None".
  eapply PTSet.ge_trans; eauto.
  SSSCase "EF_vload_global".
  exists abs. constructor; auto.
  SSSSCase "ok_abs_result".
  econstructor.
  SSSSSCase "result".
  unfold analysis. rewrite Heqo. eauto.
  SSSSSCase "regsat".
  intros; destruct (peq res0 r); [subst | eapply regsat_assign_other; eauto;
    eapply regsat_ge; [eauto | eapply RegMap.ge_trans; eauto]].
  unfold regsat, valsat. rewrite Regmap.gss. destruct v; auto.
  regsat_tac.
  eapply RegMap.get_ge. eauto. apply RegMap.get_add_same. apply PTSet.In_top.
  eapply PTSet.ge_trans. apply RegMap.get_ge. eauto. apply RegMap.get_add_same.
  SSSSSCase "memsat".
  eapply memsat_ge; eauto.
  inv H2. (* Check whether the store is volatile *)
  SSSCase "EF_vstore_global (volatile)".
  exists abs. constructor; auto.
  SSSSCase "ok_abs_result".
  econstructor.
  SSSSSCase "result".
  unfold analysis. rewrite Heqo. eauto.
  SSSSSCase "regsat".
  intros; destruct (peq res0 r); [subst | eapply regsat_assign_other; eauto;
    eapply regsat_ge; [eauto | eapply RegMap.ge_trans; eauto]].
  unfold regsat, valsat. rewrite Regmap.gss. auto.
  SSSSSCase "memsat".
  eapply memsat_ge; eauto. eapply MemMap.ge_trans; eauto.
  SSSCase "EF_vstore (not volatile)".
  exists abs. constructor; auto.
  SSSSCase "ok_stack".
  erewrite Mem.nextblock_store; eauto.
  SSSSCase "ok_abs_mem".
  eapply ok_abs_mem_store; eauto.
  SSSSCase "ok_abs_result".
  econstructor.
  SSSSSCase "result".
  unfold analysis. rewrite Heqo. eauto.
  SSSSSCase "regsat".
  intros; destruct (peq res0 r); [subst | eapply regsat_assign_other; eauto;
    eapply regsat_ge; [eauto | eapply RegMap.ge_trans; eauto]].
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
  apply MemMap.get_add_same. exact IN.
  SSSSSSSSCase "abs b = None".
  eapply PTSet.ge_trans. apply MemMap.get_add_same. easy.
  SSSSSSSCase "Didn't overlap offset o".
  simpl in LOAD.
  erewrite Mem.load_store_other in LOAD; eauto; [|right; right; omega]. merge.
  destruct (abs b) as []_eqn.
  SSSSSSSSCase "abs b = Some".
  now apply MGE'.
  SSSSSSSSCase "abs b = None".
  eapply PTSet.ge_trans; eauto.
  SSSSSSSCase "Didn't overlap offset o, for another reason".
  simpl in LOAD.
  erewrite Mem.load_store_other in LOAD; eauto; [|right; left; omega]. merge.
  destruct (abs b) as []_eqn.
  SSSSSSSSCase "abs b = Some".
  now apply MGE'.
  SSSSSSSSCase "abs b = None".
  eapply PTSet.ge_trans; eauto.
  SSSSSSCase "Didn't store in b0".
  simpl in LOAD. erewrite Mem.load_store_other in LOAD; eauto. merge.
  destruct (abs b0) as []_eqn; [|contradiction].
  destruct v; auto.
  destruct (abs b1) as []_eqn.
  SSSSSSSCase "abs b1 = Some".
  now apply MGE'.
  SSSSSSSCase "abs b1 = None".
  eapply PTSet.ge_trans; eauto.
  SSSCase "EF_malloc".
  exists (fun x => if zeq x b then Some (Alloc pc) else abs x).
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
  unfold analysis. rewrite Heqo. eauto.
  SSSSSCase "regsat".
  intros; destruct (peq res0 r); [subst | ].
  SSSSSSCase "res = r".
  unfold regsat, valsat. rewrite Regmap.gss.
  destruct (zeq b b); [merge|congruence].
  eapply RegMap.get_ge. eauto. apply RegMap.get_add_same. apply PTSet.In_singleton.
  SSSSSSCase "res <> r".
  unfold regsat, valsat. rewrite Regmap.gso; [|auto]. destruct (rs#r) as []_eqn; auto.
  regsat_intro rs r. destruct (zeq b0 b).
  SSSSSSSCase "b0 = b".
  subst. eapply RegMap.get_ge. eauto. destruct (abs b) as []_eqn.
  SSSSSSSSCase "abs b = Some".
  exfalso. eapply Mem.fresh_block_alloc; eauto. apply MEM. congruence.
  SSSSSSSSCase "abs b = None".
  eapply RegMap.get_ge. apply RegMap.ge_add. apply IN. apply PTSet.In_top.
  SSSSSSSCase "b0 <> b".
  destruct (abs b0) as []_eqn.
  SSSSSSSSCase "abs b0 = Some".
  eapply RegMap.get_ge. eauto. eapply RegMap.get_ge. apply RegMap.ge_add. auto.
  SSSSSSSSCase "abs b0 = None".
  eapply PTSet.ge_trans. apply RegMap.get_ge. eauto.
  eapply PTSet.ge_trans. apply RegMap.get_ge. apply RegMap.ge_add. auto.
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
  unfold analysis. rewrite Heqo. eauto.
  SSSSSCase "regsat".
  intros; destruct (peq res0 r); [subst | eapply regsat_assign_other; eauto;
    eapply regsat_ge; [eauto | eapply RegMap.ge_trans; eauto]].
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
  unfold analysis. rewrite Heqo. eauto.
  SSSSSCase "regsat".
  intros; destruct (peq res0 r); [subst | eapply regsat_assign_other; eauto;
    eapply regsat_ge; [eauto | eapply RegMap.ge_trans; eauto]].
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
  eapply In_unknown_offset; eauto. apply PTSet.ge_refl.
  SSSSSSSCase "abs bdst = None".
  eapply Mem.load_valid_access in LOAD. eapply Mem.valid_access_implies in LOAD.
  eapply Mem.valid_access_valid_block in LOAD.
  eapply Mem.storebytes_valid_block_2 in LOAD; eauto.
  apply MEM in LOAD. congruence. constructor.
  SSSSSSCase "b <> bdst".
  specialize (MSAT b o v). feed MSAT. simpl. erewrite <- Mem.load_storebytes_other; eauto.
  destruct (abs b); [|contradiction]. destruct v; auto. destruct (abs b0).
  SSSSSSSCase "abs b0 = Some".
  now apply MGE'.
  SSSSSSSCase "abs b0 = None".
  eapply PTSet.ge_trans. apply ge_add_ptset_to_image. auto.
  SSSCase "EF_annot".
  exists abs. constructor; auto.
  SSSSCase "ok_abs_result".
  econstructor.
  SSSSSCase "result".
  unfold analysis. rewrite Heqo. eauto.
  SSSSSCase "regsat".
  intros; destruct (peq res0 r); [subst | eapply regsat_assign_other; eauto;
    eapply regsat_ge; [eauto | eapply RegMap.ge_trans; eauto]].
  unfold regsat, valsat. rewrite Regmap.gss. auto.
  SSSSSCase "memsat".
  eapply memsat_ge; eauto.
  SSSCase "EF_annot_val".
  exists abs. constructor; auto.
  SSSSCase "ok_abs_result".
  econstructor.
  SSSSSCase "result".
  unfold analysis. rewrite Heqo. eauto.
  SSSSSCase "regsat".
  intros; destruct (peq res0 r); [subst | eapply regsat_assign_other; eauto;
    eapply regsat_ge; [eauto | eapply RegMap.ge_trans; eauto]].
  unfold regsat, valsat. rewrite Regmap.gss. destruct v; auto.
  inv H1. specialize (GENV _ _ H5). rewrite GENV.
  destruct args. inv H. destruct args; inv H. inv H0.
  regsat_intro rs r0. rewrite GENV in IN.
  eapply RegMap.get_ge. eauto. apply RegMap.get_add_same. auto.
  SSSSSCase "memsat".
  eapply memsat_ge; eauto. eapply MemMap.ge_trans; eauto.
  SCase "Kildall failed".
  rewrite PMap.gi in RPC. inv RPC.
  inv STEP; try solve [
    exists abs; constructor; auto; econstructor; eauto;
      unfold analysis; rewrite Heqo; rewrite PMap.gi; reflexivity
  ].
  SSCase "Iop".
  exists abs; constructor; auto.
  SSSCase "ok_abs_result".
  econstructor.
  SSSSCase "result".
  unfold analysis. rewrite Heqo. rewrite PMap.gi. reflexivity.
  SSSSCase "regsat".
  apply regsat_top.
  SSSSCase "memsat".
  apply memsat_top. auto.
  SSCase "Iload".
  exists abs; constructor; auto.
  SSSCase "ok_abs_result".
  econstructor.
  SSSSCase "result".
  unfold analysis. rewrite Heqo. rewrite PMap.gi. reflexivity.
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
  unfold analysis. rewrite Heqo. rewrite PMap.gi. reflexivity.
  SSSSCase "regsat".
  apply regsat_top.
  SSSSCase "memsat".
  apply memsat_top. eapply ok_abs_mem_store; eauto.
  SSCase "Ibuiltin".
  destruct ef; inv H13; merge; try solve [
    exists abs; constructor; auto; econstructor;
    [ unfold analysis; rewrite Heqo; rewrite PMap.gi; reflexivity
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
  unfold analysis. rewrite Heqo. rewrite Regmap.gi. reflexivity.
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
  unfold analysis. rewrite Heqo. rewrite Regmap.gi. reflexivity.
  SSSSSCase "regsat".
  apply regsat_top.
  SSSSSCase "memsat".
  apply memsat_top. eapply ok_abs_mem_store; eauto.
  SSSCase "EF_vstore_global".
  exists abs. inv H1; constructor; auto.
  econstructor.
  unfold analysis. rewrite Heqo. rewrite Regmap.gi. reflexivity.
  apply regsat_top.
  apply memsat_top. auto.
  erewrite Mem.nextblock_store; eauto.
  eapply ok_abs_mem_store; eauto.
  econstructor.
  unfold analysis. rewrite Heqo. rewrite Regmap.gi. reflexivity.
  apply regsat_top.
  apply memsat_top. eapply ok_abs_mem_store; eauto.
  SSSCase "EF_malloc".
  exists (fun x => if zeq x b then Some (Alloc pc) else abs x).
  (* We will need this twice, so let's prove it upfront... *)
  assert (OKAM:
    ok_abs_mem
    (fun x : Z => if zeq x b then Some (Alloc pc) else abs x)
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
  unfold analysis. rewrite Heqo. rewrite PMap.gi. reflexivity.
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
  unfold analysis. rewrite Heqo. rewrite PMap.gi. reflexivity.
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
  unfold analysis. rewrite Heqo. rewrite PMap.gi. reflexivity.
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
  unfold analysis in RPC. destruct (failure_prone_analysis f) as []_eqn.
  SSSSCase "Kildall terminated".
  pose proof Heqo as FPS.
  eapply Solver.fixpoint_solution with (n:=pc)(s:=pc') in FPS; [|
    unfold successors; unfold successors_list; rewrite PTree.gmap1;
      rewrite H6; simpl; auto; eapply list_nth_z_in; eauto].
  unfold transf in FPS. rewrite H6 in FPS. unfold Solver.L.ge in FPS.
  destruct (t#pc') as [rmap' mmap']_eqn. rewrite RPC in FPS. destruct FPS as [RGE MGE].
  econstructor.
  SSSSSCase "result".
  unfold analysis. rewrite Heqo. eauto.
  SSSSSCase "regsat".
  eapply regsat_ge; eauto. eapply RegMap.ge_trans; eauto. apply RegMap.ge_add.
  SSSSSCase "ret".
  eapply PTSet.ge_trans. apply RegMap.get_ge; eauto.
  eapply PTSet.ge_trans. apply RegMap.get_add_same. apply PTSet.ge_refl.
  SSSSSCase "mem".
  easy.
  SSSSCase "Kildall failed".
  econstructor.
  SSSSSCase "result".
  unfold analysis. rewrite Heqo. rewrite PMap.gi. eauto.
  SSSSSCase "regsat".
  eapply regsat_ge; eauto. apply RegMap.ge_top.
  SSSSSCase "ret".
  apply RegMap.get_top.
  SSSSSCase "mem".
  apply MemMap.ge_refl.
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
    if zeq b stk then Some Stack else
      match abs b with
      | Some ab => Some (
          match ab with
          | Global i => Global i
          | Globals  => Globals
          | _        => Other
          end
        )
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
  destruct (failure_prone_analysis f0) as []_eqn.
  SSCase "Kildall will terminate".
  destruct t. destruct t. pose proof Heqo as FA.
  eapply Solver.fixpoint_entry in Heqo; [|constructor; eauto].
  destruct ((t, t1, t0) # (fn_entrypoint f0)) as [rmap mmap]_eqn.
  setoid_rewrite Heqp in Heqo. unfold entry_result in Heqo.
  destruct Heqo as [RGE MGE].
  econstructor.
  SSSCase "result".
  unfold analysis. rewrite FA. eauto.
  SSSCase "regsat".
  eapply regsat_ge; eauto.
  generalize (fn_params f0). intros. unalias.
  destruct ((init_regs args l)#r) as []_eqn; auto.
  assert (In r l).
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
  apply RegMap.get_add_same. apply PTSet.In_top.
  now apply RegMap.ge_add.
  destruct (abs b).
  eapply fold_left_adds_prop; eauto; intros.
  apply RegMap.get_add_same. apply PTSet.In_top.
  now apply RegMap.ge_add.
  eapply fold_left_adds_prop; eauto; intros.
  apply RegMap.get_add_same.
  eapply PTSet.ge_trans; eauto. now apply RegMap.ge_add.
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
  apply MemMap.get_add_lt. destruct a; simpl; tauto. apply PTSet.In_top.

  SSSSSSCase "b0 <> stk".
  destruct (abs b0) as []_eqn.
  SSSSSSSCase "abs b0 = Some".
  unfold entry_mmap.
  apply MemMap.get_add_lt. destruct a; simpl; tauto. apply PTSet.In_top.
  SSSSSSSCase "abs b0 = None".
  unfold entry_mmap. apply MemMap.get_add_lt. destruct a; simpl; tauto.
  SSSSSCase "abs b = None".
  eapply load_valid_block in LOAD. eapply Mem.valid_block_alloc_inv in LOAD; eauto.
  intuition. apply MEM in H; auto.
  SSCase "Kildall won't terminate".
  econstructor; intros.
  SSSCase "result".
  unfold analysis. rewrite Heqo. rewrite PMap.gi. auto.
  SSSCase "regsat".
  unalias.
  destruct ((init_regs args (fn_params f0))#r); auto.
  destruct (zeq b stk).
  subst. apply RegMap.get_top. apply PTSet.In_top.
  destruct (abs b); apply RegMap.get_top; apply PTSet.In_top.
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
  subst. apply MemMap.get_top. apply PTSet.In_top.
  SSSSSSCase "b0 <> stk".
  destruct (abs b0) as []_eqn.
  apply MemMap.get_top. apply PTSet.In_top.
  apply MemMap.get_top.
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
  exists (fun x => if zeq x b then Some Other else abs x).
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
    | None   => if (zlt b (Mem.nextblock m0)) then Some Other else None
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
  destruct (abs b). apply RET. apply PTSet.In_top.
  destruct (zlt b (Mem.nextblock m0)); [|auto].
  apply RET. apply PTSet.In_top.
  SSSCase "res <> r".
  specialize (RSAT r). rewrite Regmap.gso; [|auto]. destruct (rs0#r); auto.
  destruct (abs b). auto.
  destruct (zlt b (Mem.nextblock m0)); [|auto].
  apply RSAT. apply PTSet.In_top.
  SSCase "memsat".
  unalias. intros. destruct (abs b). destruct v0; auto.
  destruct (abs b0); destruct (zlt b0 (Mem.nextblock m0));
  repeat intro; apply MTOP; apply MemMap.get_top; apply PTSet.In_top.
  destruct (zlt b (Mem.nextblock m0)). destruct v0; auto.
  destruct (abs b0).
  apply MTOP; apply MemMap.get_top; apply PTSet.In_top.
  destruct (zlt b0 (Mem.nextblock m0));
  repeat intro; apply MTOP; apply MemMap.get_top; apply PTSet.In_top.
  apply load_valid_block in LOAD. congruence.
Qed.
