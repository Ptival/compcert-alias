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

(** Operators and addressing modes.  The abstract syntax and dynamic
  semantics for the CminorSel, RTL, LTL and Mach languages depend on the
  following types, defined in this library:
- [condition]:  boolean conditions for conditional branches;
- [operation]: arithmetic and logical operations;
- [addressing]: addressing modes for load and store operations.

  These types are PowerPC-specific and correspond roughly to what the 
  processor can compute in one instruction.  In other terms, these
  types reflect the state of the program after instruction selection.
  For a processor-independent set of operations, see the abstract
  syntax and dynamic semantics of the Cminor language.
*)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memdata.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.

Set Implicit Arguments.

(** Conditions (boolean-valued operators). *)

Inductive condition : Type :=
  | Ccomp: comparison -> condition      (**r signed integer comparison *)
  | Ccompu: comparison -> condition     (**r unsigned integer comparison *)
  | Ccompimm: comparison -> int -> condition (**r signed integer comparison with a constant *)
  | Ccompuimm: comparison -> int -> condition  (**r unsigned integer comparison with a constant *)
  | Ccompf: comparison -> condition     (**r floating-point comparison *)
  | Cnotcompf: comparison -> condition  (**r negation of a floating-point comparison *)
  | Cmaskzero: int -> condition         (**r test [(arg & constant) == 0] *)
  | Cmasknotzero: int -> condition.     (**r test [(arg & constant) != 0] *)

(** Arithmetic and logical operations.  In the descriptions, [rd] is the
  result of the operation and [r1], [r2], etc, are the arguments. *)

Inductive operation : Type :=
  | Omove: operation                    (**r [rd = r1] *)
  | Ointconst: int -> operation         (**r [rd] is set to the given integer constant *)
  | Ofloatconst: float -> operation     (**r [rd] is set to the given float constant *)
  | Oaddrsymbol: ident -> int -> operation (**r [rd] is set to the the address of the symbol plus the offset *)
  | Oaddrstack: int -> operation        (**r [rd] is set to the stack pointer plus the given offset *)
(*c Integer arithmetic: *)
  | Ocast8signed: operation             (**r [rd] is 8-bit sign extension of [r1] *)
  | Ocast16signed: operation            (**r [rd] is 16-bit sign extension of [r1] *)
  | Oadd: operation                     (**r [rd = r1 + r2] *)
  | Oaddimm: int -> operation           (**r [rd = r1 + n] *)
  | Osub: operation                     (**r [rd = r1 - r2] *)
  | Osubimm: int -> operation           (**r [rd = n - r1] *)
  | Omul: operation                     (**r [rd = r1 * r2] *)
  | Omulimm: int -> operation           (**r [rd = r1 * n] *)
  | Odiv: operation                     (**r [rd = r1 / r2] (signed) *)
  | Odivu: operation                    (**r [rd = r1 / r2] (unsigned) *)
  | Oand: operation                     (**r [rd = r1 & r2] *)
  | Oandimm: int -> operation           (**r [rd = r1 & n] *)
  | Oor: operation                      (**r [rd = r1 | r2] *)
  | Oorimm: int -> operation            (**r [rd = r1 | n] *)
  | Oxor: operation                     (**r [rd = r1 ^ r2] *)
  | Oxorimm: int -> operation           (**r [rd = r1 ^ n] *)
  | Onand: operation                    (**r [rd = ~(r1 & r2)] *)
  | Onor: operation                     (**r [rd = ~(r1 | r2)] *)
  | Onxor: operation                    (**r [rd = ~(r1 ^ r2)] *)
  | Oshl: operation                     (**r [rd = r1 << r2] *)
  | Oshr: operation                     (**r [rd = r1 >> r2] (signed) *)
  | Oshrimm: int -> operation           (**r [rd = r1 >> n] (signed) *)
  | Oshrximm: int -> operation          (**r [rd = r1 / 2^n] (signed) *)
  | Oshru: operation                    (**r [rd = r1 >> r2] (unsigned) *)
  | Orolm: int -> int -> operation      (**r rotate left and mask *)
  | Oroli: int -> int -> operation      (**r rotate left and insert *)
(*c Floating-point arithmetic: *)
  | Onegf: operation                    (**r [rd = - r1] *)
  | Oabsf: operation                    (**r [rd = abs(r1)] *)
  | Oaddf: operation                    (**r [rd = r1 + r2] *)
  | Osubf: operation                    (**r [rd = r1 - r2] *)
  | Omulf: operation                    (**r [rd = r1 * r2] *)
  | Odivf: operation                    (**r [rd = r1 / r2] *)
  | Omuladdf: operation                 (**r [rd = r1 * r2 + r3] *)
  | Omulsubf: operation                 (**r [rd = r1 * r2 - r3] *)
  | Osingleoffloat: operation           (**r [rd] is [r1] truncated to single-precision float *)
(*c Conversions between int and float: *)
  | Ointoffloat: operation              (**r [rd = signed_int_of_float(r1)] *)
  | Ofloatofwords: operation            (**r [rd = float_of_words(r1,r2)] *)
(*c Boolean tests: *)
  | Ocmp: condition -> operation.       (**r [rd = 1] if condition holds, [rd = 0] otherwise. *)

(** Addressing modes.  [r1], [r2], etc, are the arguments to the 
  addressing. *)

Inductive addressing: Type :=
  | Aindexed: int -> addressing         (**r Address is [r1 + offset] *)
  | Aindexed2: addressing               (**r Address is [r1 + r2] *)
  | Aglobal: ident -> int -> addressing (**r Address is [symbol + offset] *)
  | Abased: ident -> int -> addressing (**r Address is [symbol + offset + r1] *)
  | Ainstack: int -> addressing.        (**r Address is [stack_pointer + offset] *)

(** Comparison functions (used in module [CSE]). *)

Definition eq_operation (x y: operation): {x=y} + {x<>y}.
Proof.
  generalize Int.eq_dec; intro.
  generalize Float.eq_dec; intro.
  assert (forall (x y: ident), {x=y}+{x<>y}). exact peq.
  assert (forall (x y: comparison), {x=y}+{x<>y}). decide equality.
  assert (forall (x y: condition), {x=y}+{x<>y}). decide equality.
  decide equality.
Qed.

Definition eq_addressing (x y: addressing) : {x=y} + {x<>y}.
Proof.
  generalize Int.eq_dec; intro.
  assert (forall (x y: ident), {x=y}+{x<>y}). exact peq.
  decide equality.
Qed.

(** * Evaluation functions *)

(** Evaluation of conditions, operators and addressing modes applied
  to lists of values.  Return [None] when the computation is undefined:
  wrong number of arguments, arguments of the wrong types, undefined 
  operations such as division by zero.  [eval_condition] returns a boolean,
  [eval_operation] and [eval_addressing] return a value. *)

Definition symbol_address (F V: Type) (genv: Genv.t F V) (id: ident) (ofs: int) : val :=
  match Genv.find_symbol genv id with
  | Some b => Vptr b ofs
  | None => Vundef
  end.

Definition eval_condition (cond: condition) (vl: list val) (m: mem): option bool :=
  match cond, vl with
  | Ccomp c, v1 :: v2 :: nil => Val.cmp_bool c v1 v2
  | Ccompu c, v1 :: v2 :: nil => Val.cmpu_bool (Mem.valid_pointer m) c v1 v2
  | Ccompimm c n, v1 :: nil => Val.cmp_bool c v1 (Vint n)
  | Ccompuimm c n, v1 :: nil => Val.cmpu_bool (Mem.valid_pointer m) c v1 (Vint n)
  | Ccompf c, v1 :: v2 :: nil => Val.cmpf_bool c v1 v2
  | Cnotcompf c, v1 :: v2 :: nil => option_map negb (Val.cmpf_bool c v1 v2)
  | Cmaskzero n, Vint n1 :: nil => Some (Int.eq (Int.and n1 n) Int.zero)
  | Cmasknotzero n, Vint n1 :: nil => Some (negb (Int.eq (Int.and n1 n) Int.zero))
  | _, _ => None
  end.

Definition eval_operation
             (F V: Type) (genv: Genv.t F V) (sp: val)
             (op: operation) (vl: list val) (m: mem): option val :=
  match op, vl with
  | Omove, v1::nil => Some v1
  | Ointconst n, nil => Some (Vint n)
  | Ofloatconst n, nil => Some (Vfloat n)
  | Oaddrsymbol s ofs, nil => Some (symbol_address genv s ofs) 
  | Oaddrstack ofs, nil => Some (Val.add sp (Vint ofs))
  | Ocast8signed, v1::nil => Some (Val.sign_ext 8 v1)
  | Ocast16signed, v1::nil => Some (Val.sign_ext 16 v1)
  | Oadd, v1::v2::nil => Some (Val.add v1 v2)
  | Oaddimm n, v1::nil => Some (Val.add v1 (Vint n))
  | Osub, v1::v2::nil => Some (Val.sub v1 v2)
  | Osubimm n, v1::nil => Some (Val.sub (Vint n) v1)
  | Omul, v1::v2::nil => Some (Val.mul v1 v2)
  | Omulimm n, v1::nil => Some (Val.mul v1 (Vint n))
  | Odiv, v1::v2::nil => Val.divs v1 v2
  | Odivu, v1::v2::nil => Val.divu v1 v2
  | Oand, v1::v2::nil => Some(Val.and v1 v2)
  | Oandimm n, v1::nil => Some (Val.and v1 (Vint n))
  | Oor, v1::v2::nil => Some(Val.or v1 v2)
  | Oorimm n, v1::nil => Some (Val.or v1 (Vint n))
  | Oxor, v1::v2::nil => Some(Val.xor v1 v2)
  | Oxorimm n, v1::nil => Some (Val.xor v1 (Vint n))
  | Onand, v1::v2::nil => Some (Val.notint (Val.and v1 v2))
  | Onor, v1::v2::nil => Some (Val.notint (Val.or v1 v2))
  | Onxor, v1::v2::nil => Some (Val.notint (Val.xor v1 v2))
  | Oshl, v1::v2::nil => Some (Val.shl v1 v2)
  | Oshr, v1::v2::nil => Some (Val.shr v1 v2)
  | Oshrimm n, v1::nil => Some (Val.shr v1 (Vint n))
  | Oshrximm n, v1::nil => Some (Val.shrx v1 (Vint n))
  | Oshru, v1::v2::nil => Some (Val.shru v1 v2)
  | Orolm amount mask, v1::nil => Some (Val.rolm v1 amount mask)
  | Oroli amount mask, v1::v2::nil =>
      Some(Val.or (Val.and v1 (Vint (Int.not mask))) (Val.rolm v2 amount mask))
  | Onegf, v1::nil => Some(Val.negf v1)
  | Oabsf, v1::nil => Some(Val.absf v1)
  | Oaddf, v1::v2::nil => Some(Val.addf v1 v2)
  | Osubf, v1::v2::nil => Some(Val.subf v1 v2)
  | Omulf, v1::v2::nil => Some(Val.mulf v1 v2)
  | Odivf, v1::v2::nil => Some(Val.divf v1 v2)
  | Omuladdf, v1::v2::v3::nil => Some(Val.addf (Val.mulf v1 v2) v3)
  | Omulsubf, v1::v2::v3::nil => Some(Val.subf (Val.mulf v1 v2) v3)
  | Osingleoffloat, v1::nil => Some(Val.singleoffloat v1)
  | Ointoffloat, v1::nil => Val.intoffloat v1
  | Ofloatofwords, v1::v2::nil => Some(Val.floatofwords v1 v2)
  | Ocmp c, _ => Some(Val.of_optbool (eval_condition c vl m))
  | _, _ => None
  end.

Definition eval_addressing
    (F V: Type) (genv: Genv.t F V) (sp: val)
    (addr: addressing) (vl: list val) : option val :=
  match addr, vl with
  | Aindexed n, v1::nil => Some (Val.add v1 (Vint n))
  | Aindexed2, v1::v2::nil => Some (Val.add v1 v2)
  | Aglobal s ofs, nil => Some (symbol_address genv s ofs)
  | Abased s ofs, v1::nil => Some (Val.add (symbol_address genv s ofs) v1)
  | Ainstack ofs, nil => Some(Val.add sp (Vint ofs))
  | _, _ => None
  end.

Ltac FuncInv :=
  match goal with
  | H: (match ?x with nil => _ | _ :: _ => _ end = Some _) |- _ =>
      destruct x; simpl in H; try discriminate; FuncInv
  | H: (match ?v with Vundef => _ | Vint _ => _ | Vfloat _ => _ | Vptr _ _ => _ end = Some _) |- _ =>
      destruct v; simpl in H; try discriminate; FuncInv
  | H: (Some _ = Some _) |- _ =>
      injection H; intros; clear H; FuncInv
  | _ =>
      idtac
  end.

(** * Static typing of conditions, operators and addressing modes. *)

Definition type_of_condition (c: condition) : list typ :=
  match c with
  | Ccomp _ => Tint :: Tint :: nil
  | Ccompu _ => Tint :: Tint :: nil
  | Ccompimm _ _ => Tint :: nil
  | Ccompuimm _ _ => Tint :: nil
  | Ccompf _ => Tfloat :: Tfloat :: nil
  | Cnotcompf _ => Tfloat :: Tfloat :: nil
  | Cmaskzero _ => Tint :: nil
  | Cmasknotzero _ => Tint :: nil
  end.

Definition type_of_operation (op: operation) : list typ * typ :=
  match op with
  | Omove => (nil, Tint)   (* treated specially *)
  | Ointconst _ => (nil, Tint)
  | Ofloatconst _ => (nil, Tfloat)
  | Oaddrsymbol _ _ => (nil, Tint)
  | Oaddrstack _ => (nil, Tint)
  | Ocast8signed => (Tint :: nil, Tint)
  | Ocast16signed => (Tint :: nil, Tint)
  | Oadd => (Tint :: Tint :: nil, Tint)
  | Oaddimm _ => (Tint :: nil, Tint)
  | Osub => (Tint :: Tint :: nil, Tint)
  | Osubimm _ => (Tint :: nil, Tint)
  | Omul => (Tint :: Tint :: nil, Tint)
  | Omulimm _ => (Tint :: nil, Tint)
  | Odiv => (Tint :: Tint :: nil, Tint)
  | Odivu => (Tint :: Tint :: nil, Tint)
  | Oand => (Tint :: Tint :: nil, Tint)
  | Oandimm _ => (Tint :: nil, Tint)
  | Oor => (Tint :: Tint :: nil, Tint)
  | Oorimm _ => (Tint :: nil, Tint)
  | Oxor => (Tint :: Tint :: nil, Tint)
  | Oxorimm _ => (Tint :: nil, Tint)
  | Onand => (Tint :: Tint :: nil, Tint)
  | Onor => (Tint :: Tint :: nil, Tint)
  | Onxor => (Tint :: Tint :: nil, Tint)
  | Oshl => (Tint :: Tint :: nil, Tint)
  | Oshr => (Tint :: Tint :: nil, Tint)
  | Oshrimm _ => (Tint :: nil, Tint)
  | Oshrximm _ => (Tint :: nil, Tint)
  | Oshru => (Tint :: Tint :: nil, Tint)
  | Orolm _ _ => (Tint :: nil, Tint)
  | Oroli _ _ => (Tint :: Tint :: nil, Tint)
  | Onegf => (Tfloat :: nil, Tfloat)
  | Oabsf => (Tfloat :: nil, Tfloat)
  | Oaddf => (Tfloat :: Tfloat :: nil, Tfloat)
  | Osubf => (Tfloat :: Tfloat :: nil, Tfloat)
  | Omulf => (Tfloat :: Tfloat :: nil, Tfloat)
  | Odivf => (Tfloat :: Tfloat :: nil, Tfloat)
  | Omuladdf => (Tfloat :: Tfloat :: Tfloat :: nil, Tfloat)
  | Omulsubf => (Tfloat :: Tfloat :: Tfloat :: nil, Tfloat)
  | Osingleoffloat => (Tfloat :: nil, Tfloat)
  | Ointoffloat => (Tfloat :: nil, Tint)
  | Ofloatofwords => (Tint :: Tint :: nil, Tfloat)
  | Ocmp c => (type_of_condition c, Tint)
  end.

Definition type_of_addressing (addr: addressing) : list typ :=
  match addr with
  | Aindexed _ => Tint :: nil
  | Aindexed2 => Tint :: Tint :: nil
  | Aglobal _ _ => nil
  | Abased _ _ => Tint :: nil
  | Ainstack _ => nil
  end.

(** Weak type soundness results for [eval_operation]:
  the result values, when defined, are always of the type predicted
  by [type_of_operation]. *)

Section SOUNDNESS.

Variable A V: Type.
Variable genv: Genv.t A V.

Lemma type_of_operation_sound:
  forall op vl sp v m,
  op <> Omove ->
  eval_operation genv sp op vl m = Some v ->
  Val.has_type v (snd (type_of_operation op)).
Proof with (try exact I).
  intros.
  destruct op; simpl in H0; FuncInv; subst; simpl.
  congruence.
  exact I.
  exact I.
  unfold symbol_address. destruct (Genv.find_symbol genv i)...
  destruct sp...
  destruct v0...
  destruct v0...
  destruct v0; destruct v1...
  destruct v0...
  destruct v0; destruct v1... simpl. destruct (zeq b b0)...
  destruct v0...
  destruct v0; destruct v1...
  destruct v0...
  destruct v0; destruct v1; simpl in *; inv H0. destruct (Int.eq i0 Int.zero); inv H2...
  destruct v0; destruct v1; simpl in *; inv H0. destruct (Int.eq i0 Int.zero); inv H2...
  destruct v0; destruct v1...
  destruct v0...
  destruct v0; destruct v1...
  destruct v0...
  destruct v0; destruct v1...
  destruct v0...
  destruct v0; destruct v1...
  destruct v0; destruct v1...
  destruct v0; destruct v1...
  destruct v0; destruct v1; simpl... destruct (Int.ltu i0 Int.iwordsize)...
  destruct v0; destruct v1; simpl... destruct (Int.ltu i0 Int.iwordsize)...
  destruct v0; simpl... destruct (Int.ltu i Int.iwordsize)...
  destruct v0; simpl... destruct (Int.ltu i Int.iwordsize)...
  destruct v0; destruct v1; simpl... destruct (Int.ltu i0 Int.iwordsize)...
  destruct v0...
  destruct v0; destruct v1...
  destruct v0...
  destruct v0...
  destruct v0; destruct v1...
  destruct v0; destruct v1...
  destruct v0; destruct v1...
  destruct v0; destruct v1...
  destruct v0; destruct v1; destruct v2...
  destruct v0; destruct v1; destruct v2...
  destruct v0...
  destruct v0; simpl in H0; inv H0. destruct (Float.intoffloat f); inv H2...
  destruct v0; destruct v1...
  destruct (eval_condition c vl m); simpl... destruct b... 
Qed.

Lemma type_of_chunk_correct:
  forall chunk m addr v,
  Mem.loadv chunk m addr = Some v ->
  Val.has_type v (type_of_chunk chunk).
Proof.
  intro chunk.
  assert (forall v, Val.has_type (Val.load_result chunk v) (type_of_chunk chunk)).
  destruct v; destruct chunk; exact I.
  intros until v. unfold Mem.loadv. 
  destruct addr; intros; try discriminate.
  eapply Mem.load_type; eauto.
Qed.

End SOUNDNESS.

(** * Manipulating and transforming operations *)

(** Recognition of move operations. *)

Definition is_move_operation
    (A: Type) (op: operation) (args: list A) : option A :=
  match op, args with
  | Omove, arg :: nil => Some arg
  | _, _ => None
  end.

Lemma is_move_operation_correct:
  forall (A: Type) (op: operation) (args: list A) (a: A),
  is_move_operation op args = Some a ->
  op = Omove /\ args = a :: nil.
Proof.
  intros until a. unfold is_move_operation; destruct op;
  try (intros; discriminate).
  destruct args. intros; discriminate.
  destruct args. intros. intuition congruence. 
  intros; discriminate.
Qed.

(** [negate_condition cond] returns a condition that is logically
  equivalent to the negation of [cond]. *)

Definition negate_condition (cond: condition): condition :=
  match cond with
  | Ccomp c => Ccomp(negate_comparison c)
  | Ccompu c => Ccompu(negate_comparison c)
  | Ccompimm c n => Ccompimm (negate_comparison c) n
  | Ccompuimm c n => Ccompuimm (negate_comparison c) n
  | Ccompf c => Cnotcompf c
  | Cnotcompf c => Ccompf c
  | Cmaskzero n => Cmasknotzero n
  | Cmasknotzero n => Cmaskzero n
  end.

Lemma eval_negate_condition:
  forall cond vl m b,
  eval_condition cond vl m = Some b ->
  eval_condition (negate_condition cond) vl m = Some (negb b).
Proof.
  intros. 
  destruct cond; simpl in H; FuncInv; simpl.
  rewrite Val.negate_cmp_bool; rewrite H; auto.
  rewrite Val.negate_cmpu_bool; rewrite H; auto.
  rewrite Val.negate_cmp_bool; rewrite H; auto.
  rewrite Val.negate_cmpu_bool; rewrite H; auto.
  rewrite H; auto.
  destruct (Val.cmpf_bool c v v0); simpl in H; inv H. rewrite negb_elim; auto. 
  rewrite H0; auto.
  rewrite <- H0. rewrite negb_elim; auto.
Qed.

(** Shifting stack-relative references.  This is used in [Stacking]. *)

Definition shift_stack_addressing (delta: int) (addr: addressing) :=
  match addr with
  | Ainstack ofs => Ainstack (Int.add delta ofs)
  | _ => addr
  end.

Definition shift_stack_operation (delta: int) (op: operation) :=
  match op with
  | Oaddrstack ofs => Oaddrstack (Int.add delta ofs)
  | _ => op
  end.

Lemma type_shift_stack_addressing:
  forall delta addr, type_of_addressing (shift_stack_addressing delta addr) = type_of_addressing addr.
Proof.
  intros. destruct addr; auto. 
Qed.

Lemma type_shift_stack_operation:
  forall delta op, type_of_operation (shift_stack_operation delta op) = type_of_operation op.
Proof.
  intros. destruct op; auto.
Qed.

Lemma eval_shift_stack_addressing:
  forall F V (ge: Genv.t F V) sp addr vl delta,
  eval_addressing ge sp (shift_stack_addressing delta addr) vl =
  eval_addressing ge (Val.add sp (Vint delta)) addr vl.
Proof.
  intros. destruct addr; simpl; auto.
  rewrite Val.add_assoc. simpl. auto.
Qed.

Lemma eval_shift_stack_operation:
  forall F V (ge: Genv.t F V) sp op vl m delta,
  eval_operation ge sp (shift_stack_operation delta op) vl m =
  eval_operation ge (Val.add sp (Vint delta)) op vl m.
Proof.
  intros. destruct op; simpl; auto.
  rewrite Val.add_assoc. simpl. auto.
Qed.

(** Transformation of addressing modes with two operands or more
  into an equivalent arithmetic operation.  This is used in the [Reload]
  pass when a store instruction cannot be reloaded directly because
  it runs out of temporary registers. *)

(** For the PowerPC, there is only one binary addressing mode: [Aindexed2].
  The corresponding operation is [Oadd]. *)

Definition op_for_binary_addressing (addr: addressing) : operation := Oadd.

Lemma eval_op_for_binary_addressing:
  forall (F V: Type) (ge: Genv.t F V) sp addr args v m,
  (length args >= 2)%nat ->
  eval_addressing ge sp addr args = Some v ->
  eval_operation ge sp (op_for_binary_addressing addr) args m = Some v.
Proof.
  intros.
  destruct addr; simpl in H0; FuncInv; simpl in H; try omegaContradiction.
  simpl; congruence.
Qed.

Lemma type_op_for_binary_addressing:
  forall addr,
  (length (type_of_addressing addr) >= 2)%nat ->
  type_of_operation (op_for_binary_addressing addr) = (type_of_addressing addr, Tint).
Proof.
  intros. destruct addr; simpl in H; reflexivity || omegaContradiction.
Qed.

(** Two-address operations.  There is only one: rotate-mask-insert. *)

Definition two_address_op (op: operation) : bool :=
  match op with
  | Oroli _ _ => true
  | _ => false
  end.

(** Operations that are so cheap to recompute that CSE should not factor them out. *)

Definition is_trivial_op (op: operation) : bool :=
  match op with
  | Omove => true
  | Ointconst _ => true
  | Oaddrsymbol _ _ => true
  | Oaddrstack _ => true
  | _ => false
  end.

(** Operations that depend on the memory state. *)

Definition op_depends_on_memory (op: operation) : bool :=
  match op with
  | Ocmp (Ccompu _) => true
  | _ => false
  end.

Lemma op_depends_on_memory_correct:
  forall (F V: Type) (ge: Genv.t F V) sp op args m1 m2,
  op_depends_on_memory op = false ->
  eval_operation ge sp op args m1 = eval_operation ge sp op args m2.
Proof.
  intros until m2. destruct op; simpl; try congruence.
  destruct c; simpl; auto; discriminate. 
Qed.

(** * Invariance and compatibility properties. *)

(** [eval_operation] and [eval_addressing] depend on a global environment
  for resolving references to global symbols.  We show that they give
  the same results if a global environment is replaced by another that
  assigns the same addresses to the same symbols. *)

Section GENV_TRANSF.

Variable F1 F2 V1 V2: Type.
Variable ge1: Genv.t F1 V1.
Variable ge2: Genv.t F2 V2.
Hypothesis agree_on_symbols:
  forall (s: ident), Genv.find_symbol ge2 s = Genv.find_symbol ge1 s.

Lemma eval_operation_preserved:
  forall sp op vl m,
  eval_operation ge2 sp op vl m = eval_operation ge1 sp op vl m.
Proof.
  intros. destruct op; simpl; auto. 
  destruct vl; auto. decEq. unfold symbol_address. rewrite agree_on_symbols. auto.
Qed.

Lemma eval_addressing_preserved:
  forall sp addr vl,
  eval_addressing ge2 sp addr vl = eval_addressing ge1 sp addr vl.
Proof.
  intros. destruct addr; simpl; auto; unfold symbol_address; rewrite agree_on_symbols; auto.
Qed.

End GENV_TRANSF.

(** Compatibility of the evaluation functions with value injections. *)

Section EVAL_COMPAT.

Variable F V: Type.
Variable genv: Genv.t F V.
Variable f: meminj.

Hypothesis symbol_address_inj: 
  forall id ofs,
  val_inject f (symbol_address genv id ofs) (symbol_address genv id ofs).

Variable m1: mem.
Variable m2: mem.

Hypothesis valid_pointer_inj:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.valid_pointer m1 b1 (Int.unsigned ofs) = true ->
  Mem.valid_pointer m2 b2 (Int.unsigned (Int.add ofs (Int.repr delta))) = true.

Hypothesis valid_pointer_no_overflow:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.valid_pointer m1 b1 (Int.unsigned ofs) = true ->
  0 <= Int.unsigned ofs + Int.unsigned (Int.repr delta) <= Int.max_unsigned.

Hypothesis valid_different_pointers_inj:
  forall b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  b1 <> b2 ->
  Mem.valid_pointer m1 b1 (Int.unsigned ofs1) = true ->
  Mem.valid_pointer m1 b2 (Int.unsigned ofs2) = true ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Int.unsigned (Int.add ofs1 (Int.repr delta1)) <> Int.unsigned (Int.add ofs2 (Int.repr delta2)).

Ltac InvInject :=
  match goal with
  | [ H: val_inject _ (Vint _) _ |- _ ] =>
      inv H; InvInject
  | [ H: val_inject _ (Vfloat _) _ |- _ ] =>
      inv H; InvInject
  | [ H: val_inject _ (Vptr _ _) _ |- _ ] =>
      inv H; InvInject
  | [ H: val_list_inject _ nil _ |- _ ] =>
      inv H; InvInject
  | [ H: val_list_inject _ (_ :: _) _ |- _ ] =>
      inv H; InvInject
  | _ => idtac
  end.

Remark val_add_inj:
  forall v1 v1' v2 v2',
  val_inject f v1 v1' -> val_inject f v2 v2' -> val_inject f (Val.add v1 v2) (Val.add v1' v2').
Proof.
  intros. inv H; inv H0; simpl; econstructor; eauto. 
  repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
Qed.

Lemma eval_condition_inj:
  forall cond vl1 vl2 b,
  val_list_inject f vl1 vl2 ->
  eval_condition cond vl1 m1 = Some b ->
  eval_condition cond vl2 m2 = Some b.
Proof.
Opaque Int.add.
  assert (CMPU:
    forall c v1 v2 v1' v2' b,
    val_inject f v1 v1' ->
    val_inject f v2 v2' ->
    Val.cmpu_bool (Mem.valid_pointer m1) c v1 v2 = Some b ->
    Val.cmpu_bool (Mem.valid_pointer m2) c v1' v2' = Some b).
  intros. inv H; simpl in H1; try discriminate; inv H0; simpl in H1; try discriminate; simpl; auto.
  destruct (Mem.valid_pointer m1 b1 (Int.unsigned ofs1)) as []_eqn; try discriminate.
  destruct (Mem.valid_pointer m1 b0 (Int.unsigned ofs0)) as []_eqn; try discriminate.
  rewrite (valid_pointer_inj _ H2 Heqb4).
  rewrite (valid_pointer_inj _ H Heqb0). simpl.
  destruct (zeq b1 b0); simpl in H1.
  inv H1. rewrite H in H2; inv H2. rewrite zeq_true. 
  decEq. apply Int.translate_cmpu.
  eapply valid_pointer_no_overflow; eauto.
  eapply valid_pointer_no_overflow; eauto.
  exploit valid_different_pointers_inj; eauto. intros P.
  destruct (zeq b2 b3); auto.
  destruct P. congruence. 
  destruct c; simpl in H1; inv H1.
  simpl; decEq. rewrite Int.eq_false; auto. congruence.
  simpl; decEq. rewrite Int.eq_false; auto. congruence.

  intros. destruct cond; simpl in H0; FuncInv; InvInject; simpl; auto.
  inv H3; inv H2; simpl in H0; inv H0; auto.
  eauto.
  inv H3; simpl in H0; inv H0; auto.
  eauto. 
  inv H3; inv H2; simpl in H0; inv H0; auto.
  inv H3; inv H2; simpl in H0; inv H0; auto.
Qed.

Ltac TrivialExists :=
  match goal with
  | [ |- exists v2, Some ?v1 = Some v2 /\ val_inject _ _ v2 ] =>
      exists v1; split; auto
  | _ => idtac
  end.

Lemma eval_operation_inj:
  forall op sp1 vl1 sp2 vl2 v1,
  val_inject f sp1 sp2 ->
  val_list_inject f vl1 vl2 ->
  eval_operation genv sp1 op vl1 m1 = Some v1 ->
  exists v2, eval_operation genv sp2 op vl2 m2 = Some v2 /\ val_inject f v1 v2.
Proof.
  intros. destruct op; simpl in H1; simpl; FuncInv; InvInject; TrivialExists.
  inv H; simpl; econstructor; eauto. repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  inv H4; simpl; auto.
  inv H4; simpl; auto.
  apply val_add_inj; auto.
  apply val_add_inj; auto.
  inv H4; inv H2; simpl; auto. econstructor; eauto. 
    rewrite Int.sub_add_l. auto.
    destruct (zeq b1 b0); auto. subst. rewrite H1 in H0. inv H0. rewrite zeq_true. 
    rewrite Int.sub_shifted. auto.
  inv H4; auto. 
  inv H4; inv H2; simpl; auto.
  inv H4; simpl; auto.
  inv H4; inv H3; simpl in H1; inv H1. simpl. 
    destruct (Int.eq i0 Int.zero); inv H2. TrivialExists.
  inv H4; inv H3; simpl in H1; inv H1. simpl. 
    destruct (Int.eq i0 Int.zero); inv H2. TrivialExists.
  inv H4; inv H2; simpl; auto.
  inv H4; simpl; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; simpl; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; simpl; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; inv H2; simpl; auto. destruct (Int.ltu i0 Int.iwordsize); auto.
  inv H4; inv H2; simpl; auto. destruct (Int.ltu i0 Int.iwordsize); auto.
  inv H4; simpl; auto. destruct (Int.ltu i Int.iwordsize); auto.
  inv H4; simpl; auto. destruct (Int.ltu i Int.iwordsize); auto.
  inv H4; inv H2; simpl; auto. destruct (Int.ltu i0 Int.iwordsize); auto.
  inv H4; simpl; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; simpl; auto.
  inv H4; simpl; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; simpl; auto; inv H2; simpl; auto; inv H3; simpl; auto.
  inv H4; simpl; auto; inv H2; simpl; auto; inv H3; simpl; auto.
  inv H4; simpl; auto.
  inv H4; simpl in H1; inv H1. simpl. destruct (Float.intoffloat f0); simpl in H2; inv H2.
  exists (Vint i); auto.
  inv H4; inv H2; simpl; auto.
  subst v1. destruct (eval_condition c vl1 m1) as []_eqn.
  exploit eval_condition_inj; eauto. intros EQ; rewrite EQ.
  destruct b; simpl; constructor.
  simpl; constructor.
Qed.

Lemma eval_addressing_inj:
  forall addr sp1 vl1 sp2 vl2 v1,
  val_inject f sp1 sp2 ->
  val_list_inject f vl1 vl2 ->
  eval_addressing genv sp1 addr vl1 = Some v1 ->
  exists v2, eval_addressing genv sp2 addr vl2 = Some v2 /\ val_inject f v1 v2.
Proof.
  intros. destruct addr; simpl in H1; simpl; FuncInv; InvInject; TrivialExists.
  apply val_add_inj; auto.
  apply val_add_inj; auto.
  apply val_add_inj; auto.
  apply val_add_inj; auto.
Qed.

End EVAL_COMPAT.

(** Compatibility of the evaluation functions with the ``is less defined'' relation over values. *)

Section EVAL_LESSDEF.

Variable F V: Type.
Variable genv: Genv.t F V.

Remark valid_pointer_extends:
  forall m1 m2, Mem.extends m1 m2 ->
  forall b1 ofs b2 delta,
  Some(b1, 0) = Some(b2, delta) ->
  Mem.valid_pointer m1 b1 (Int.unsigned ofs) = true ->
  Mem.valid_pointer m2 b2 (Int.unsigned (Int.add ofs (Int.repr delta))) = true.
Proof.
  intros. inv H0. rewrite Int.add_zero. eapply Mem.valid_pointer_extends; eauto. 
Qed.

Remark valid_pointer_no_overflow_extends:
  forall m1 b1 ofs b2 delta,
  Some(b1, 0) = Some(b2, delta) ->
  Mem.valid_pointer m1 b1 (Int.unsigned ofs) = true ->
  0 <= Int.unsigned ofs + Int.unsigned (Int.repr delta) <= Int.max_unsigned.
Proof.
  intros. inv H. rewrite Zplus_0_r. apply Int.unsigned_range_2.
Qed.

Remark valid_different_pointers_extends:
  forall m1 b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  b1 <> b2 ->
  Mem.valid_pointer m1 b1 (Int.unsigned ofs1) = true ->
  Mem.valid_pointer m1 b2 (Int.unsigned ofs2) = true ->
  Some(b1, 0) = Some (b1', delta1) ->
  Some(b2, 0) = Some (b2', delta2) ->
  b1' <> b2' \/
  Int.unsigned(Int.add ofs1 (Int.repr delta1)) <> Int.unsigned(Int.add ofs2 (Int.repr delta2)).
Proof.
  intros. inv H2; inv H3. auto.
Qed.

Lemma eval_condition_lessdef:
  forall cond vl1 vl2 b m1 m2,
  Val.lessdef_list vl1 vl2 ->
  Mem.extends m1 m2 ->
  eval_condition cond vl1 m1 = Some b ->
  eval_condition cond vl2 m2 = Some b.
Proof.
  intros. eapply eval_condition_inj with (f := fun b => Some(b, 0)) (m1 := m1).
  apply valid_pointer_extends; auto.
  apply valid_pointer_no_overflow_extends; auto. 
  apply valid_different_pointers_extends; auto.
  rewrite <- val_list_inject_lessdef. eauto. auto.
Qed.

Lemma eval_operation_lessdef:
  forall sp op vl1 vl2 v1 m1 m2,
  Val.lessdef_list vl1 vl2 ->
  Mem.extends m1 m2 ->
  eval_operation genv sp op vl1 m1 = Some v1 ->
  exists v2, eval_operation genv sp op vl2 m2 = Some v2 /\ Val.lessdef v1 v2.
Proof.
  intros. rewrite val_list_inject_lessdef in H.
  assert (exists v2 : val,
          eval_operation genv sp op vl2 m2 = Some v2
          /\ val_inject (fun b => Some(b, 0)) v1 v2).
  eapply eval_operation_inj with (m1 := m1) (sp1 := sp).
  intros. rewrite <- val_inject_lessdef; auto.
  apply valid_pointer_extends; auto.
  apply valid_pointer_no_overflow_extends; auto. 
  apply valid_different_pointers_extends; auto.
  rewrite <- val_inject_lessdef; auto.
  eauto. auto. 
  destruct H2 as [v2 [A B]]. exists v2; split; auto. rewrite val_inject_lessdef; auto. 
Qed.

Lemma eval_addressing_lessdef:
  forall sp addr vl1 vl2 v1,
  Val.lessdef_list vl1 vl2 ->
  eval_addressing genv sp addr vl1 = Some v1 ->
  exists v2, eval_addressing genv sp addr vl2 = Some v2 /\ Val.lessdef v1 v2.
Proof.
  intros. rewrite val_list_inject_lessdef in H.
  assert (exists v2 : val,
          eval_addressing genv sp addr vl2 = Some v2
          /\ val_inject (fun b => Some(b, 0)) v1 v2).
  eapply eval_addressing_inj with (sp1 := sp).
  intros. rewrite <- val_inject_lessdef; auto.
  rewrite <- val_inject_lessdef; auto.
  eauto. auto. 
  destruct H1 as [v2 [A B]]. exists v2; split; auto. rewrite val_inject_lessdef; auto. 
Qed.

End EVAL_LESSDEF.

(** Compatibility of the evaluation functions with memory injections. *)

Section EVAL_INJECT.

Variable F V: Type.
Variable genv: Genv.t F V.
Variable f: meminj.
Hypothesis globals: meminj_preserves_globals genv f.
Variable sp1: block.
Variable sp2: block.
Variable delta: Z.
Hypothesis sp_inj: f sp1 = Some(sp2, delta).

Remark symbol_address_inject:
  forall id ofs, val_inject f (symbol_address genv id ofs) (symbol_address genv id ofs).
Proof.
  intros. unfold symbol_address. destruct (Genv.find_symbol genv id) as []_eqn; auto.
  exploit (proj1 globals); eauto. intros. 
  econstructor; eauto. rewrite Int.add_zero; auto.
Qed.

Lemma eval_condition_inject:
  forall cond vl1 vl2 b m1 m2,
  val_list_inject f vl1 vl2 ->
  Mem.inject f m1 m2 ->
  eval_condition cond vl1 m1 = Some b ->
  eval_condition cond vl2 m2 = Some b.
Proof.
  intros. eapply eval_condition_inj with (f := f) (m1 := m1); eauto.
  intros; eapply Mem.valid_pointer_inject_val; eauto.
  intros; eapply Mem.valid_pointer_inject_no_overflow; eauto.
  intros; eapply Mem.different_pointers_inject; eauto.
Qed.

Lemma eval_addressing_inject:
  forall addr vl1 vl2 v1,
  val_list_inject f vl1 vl2 ->
  eval_addressing genv (Vptr sp1 Int.zero) addr vl1 = Some v1 ->
  exists v2, 
     eval_addressing genv (Vptr sp2 Int.zero) (shift_stack_addressing (Int.repr delta) addr) vl2 = Some v2
  /\ val_inject f v1 v2.
Proof.
  intros. 
  rewrite eval_shift_stack_addressing. simpl.
  eapply eval_addressing_inj with (sp1 := Vptr sp1 Int.zero); eauto.
  exact symbol_address_inject.
Qed.

Lemma eval_operation_inject:
  forall op vl1 vl2 v1 m1 m2,
  val_list_inject f vl1 vl2 ->
  Mem.inject f m1 m2 ->
  eval_operation genv (Vptr sp1 Int.zero) op vl1 m1 = Some v1 ->
  exists v2,
     eval_operation genv (Vptr sp2 Int.zero) (shift_stack_operation (Int.repr delta) op) vl2 m2 = Some v2
  /\ val_inject f v1 v2.
Proof.
  intros. 
  rewrite eval_shift_stack_operation. simpl.
  eapply eval_operation_inj with (sp1 := Vptr sp1 Int.zero) (m1 := m1); eauto.
  exact symbol_address_inject.
  intros; eapply Mem.valid_pointer_inject_val; eauto.
  intros; eapply Mem.valid_pointer_inject_no_overflow; eauto.
  intros; eapply Mem.different_pointers_inject; eauto.
Qed.

End EVAL_INJECT.

(** * Masks for rotate and mask instructions *)

(** Recognition of integers that are acceptable as immediate operands
  to the [rlwim] PowerPC instruction.  These integers are of the form
  [000011110000] or [111100001111], that is, a run of one bits
  surrounded by zero bits, or conversely.  We recognize these integers by
  running the following automaton on the bits.  The accepting states are
  2, 3, 4, 5, and 6.
<<
               0          1          0
              / \        / \        / \
              \ /        \ /        \ /
        -0--> [1] --1--> [2] --0--> [3]
       /     
     [0]
       \
        -1--> [4] --0--> [5] --1--> [6]
              / \        / \        / \
              \ /        \ /        \ /
               1          0          1
>>
*)

Inductive rlw_state: Type :=
  | RLW_S0 : rlw_state
  | RLW_S1 : rlw_state
  | RLW_S2 : rlw_state
  | RLW_S3 : rlw_state
  | RLW_S4 : rlw_state
  | RLW_S5 : rlw_state
  | RLW_S6 : rlw_state
  | RLW_Sbad : rlw_state.

Definition rlw_transition (s: rlw_state) (b: bool) : rlw_state :=
  match s, b with
  | RLW_S0, false => RLW_S1
  | RLW_S0, true  => RLW_S4
  | RLW_S1, false => RLW_S1
  | RLW_S1, true  => RLW_S2
  | RLW_S2, false => RLW_S3
  | RLW_S2, true  => RLW_S2
  | RLW_S3, false => RLW_S3
  | RLW_S3, true  => RLW_Sbad
  | RLW_S4, false => RLW_S5
  | RLW_S4, true  => RLW_S4
  | RLW_S5, false => RLW_S5
  | RLW_S5, true  => RLW_S6
  | RLW_S6, false => RLW_Sbad
  | RLW_S6, true  => RLW_S6
  | RLW_Sbad, _ => RLW_Sbad
  end.

Definition rlw_accepting (s: rlw_state) : bool :=
  match s with
  | RLW_S0 => false
  | RLW_S1 => false
  | RLW_S2 => true
  | RLW_S3 => true
  | RLW_S4 => true
  | RLW_S5 => true
  | RLW_S6 => true
  | RLW_Sbad => false
  end.

Fixpoint is_rlw_mask_rec (n: nat) (s: rlw_state) (x: Z) {struct n} : bool :=
  match n with
  | O =>
      rlw_accepting s
  | S m =>
      let (b, y) := Int.Z_bin_decomp x in
      is_rlw_mask_rec m (rlw_transition s b) y
  end.

Definition is_rlw_mask (x: int) : bool :=
  is_rlw_mask_rec Int.wordsize RLW_S0 (Int.unsigned x).
