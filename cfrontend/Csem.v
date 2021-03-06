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

(** Dynamic semantics for the Compcert C language *)

Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Csyntax.
Require Import Smallstep.

(** * Semantics of type-dependent operations *)

(** Semantics of casts.  [sem_cast v1 t1 t2 = Some v2] if value [v1],
  viewed with static type [t1], can be cast to type [t2],
  resulting in value [v2].  *)

Definition cast_int_int (sz: intsize) (sg: signedness) (i: int) : int :=
  match sz, sg with
  | I8, Signed => Int.sign_ext 8 i
  | I8, Unsigned => Int.zero_ext 8 i
  | I16, Signed => Int.sign_ext 16 i
  | I16, Unsigned => Int.zero_ext 16 i 
  | I32, _ => i
  | IBool, _ => if Int.eq i Int.zero then Int.zero else Int.one
  end.

Definition cast_int_float (si : signedness) (i: int) : float :=
  match si with
  | Signed => Float.floatofint i
  | Unsigned => Float.floatofintu i
  end.

Definition cast_float_int (si : signedness) (f: float) : option int :=
  match si with
  | Signed => Float.intoffloat f
  | Unsigned => Float.intuoffloat f
  end.

Definition cast_float_float (sz: floatsize) (f: float) : float :=
  match sz with
  | F32 => Float.singleoffloat f
  | F64 => f
  end.

Function sem_cast (v: val) (t1 t2: type) : option val :=
  match classify_cast t1 t2 with
  | cast_case_neutral =>
      match v with
      | Vint _ | Vptr _ _ => Some v
      | _ => None
      end
  | cast_case_i2i sz2 si2 =>
      match v with
      | Vint i => Some (Vint (cast_int_int sz2 si2 i))
      | _ => None
      end
  | cast_case_f2f sz2 =>
      match v with
      | Vfloat f => Some (Vfloat (cast_float_float sz2 f))
      | _ => None
      end
  | cast_case_i2f si1 sz2 =>
      match v with
      | Vint i => Some (Vfloat (cast_float_float sz2 (cast_int_float si1 i)))
      | _ => None
      end
  | cast_case_f2i sz2 si2 =>
      match v with
      | Vfloat f =>
          match cast_float_int si2 f with
          | Some i => Some (Vint (cast_int_int sz2 si2 i))
          | None => None
          end
      | _ => None
      end
  | cast_case_ip2bool =>
      match v with
      | Vint i => Some (Vint (cast_int_int IBool Signed i))
      | Vptr _ _ => Some (Vint Int.one)
      | _ => None
      end
  | cast_case_f2bool =>
      match v with
      | Vfloat f =>
          Some(Vint(if Float.cmp Ceq f Float.zero then Int.zero else Int.one))
      | _ => None
      end
  | cast_case_struct id1 fld1 id2 fld2 =>
      if ident_eq id1 id2 && fieldlist_eq fld1 fld2 then Some v else None
  | cast_case_union id1 fld1 id2 fld2 =>
      if ident_eq id1 id2 && fieldlist_eq fld1 fld2 then Some v else None
  | cast_case_void =>
      Some v
  | cast_case_default =>
      None
  end.

(** Interpretation of values as truth values.
  Non-zero integers, non-zero floats and non-null pointers are
  considered as true.  The integer zero (which also represents
  the null pointer) and the float 0.0 are false. *)

Function bool_val (v: val) (t: type) : option bool :=
  match v, t with
  | Vint n, (Tint _ _ _ | Tpointer _ _ | Tarray _ _ _ | Tfunction _ _) => Some (negb (Int.eq n Int.zero))
  | Vptr b ofs, (Tint _ _ _ | Tpointer _ _ | Tarray _ _ _ | Tfunction _ _) => Some true
  | Vfloat f, Tfloat sz _ => Some (negb(Float.cmp Ceq f Float.zero))
  | _, _ => None
  end.

(** The following [sem_] functions compute the result of an operator
  application.  Since operators are overloaded, the result depends
  both on the static types of the arguments and on their run-time values.
  For binary operations, the "usual binary conversions", adapted to a 32-bit
  platform, state that:
- If both arguments are of integer type, an integer operation is performed.
  For operations that behave differently at unsigned and signed types
  (e.g. division, modulus, comparisons), the unsigned operation is selected
  if at least one of the arguments is of type "unsigned int32", otherwise
  the signed operation is performed.
- If both arguments are of float type, a float operation is performed.
  We choose to perform all float arithmetic in double precision,
  even if both arguments are single-precision floats.
- If one argument has integer type and the other has float type,
  we convert the integer argument to float, then perform the float operation.
 *)

Function sem_neg (v: val) (ty: type) : option val :=
  match classify_neg ty with
  | neg_case_i sg =>
      match v with
      | Vint n => Some (Vint (Int.neg n))
      | _ => None
      end
  | neg_case_f =>
      match v with
      | Vfloat f => Some (Vfloat (Float.neg f))
      | _ => None
      end
  | neg_default => None
  end.

Function sem_notint (v: val) (ty: type): option val :=
  match classify_notint ty with
  | notint_case_i sg =>
      match v with
      | Vint n => Some (Vint (Int.xor n Int.mone))
      | _ => None
      end
  | notint_default => None
  end.

Function sem_notbool (v: val) (ty: type) : option val :=
  match classify_bool ty with
  | bool_case_ip =>
      match v with
      | Vint n => Some (Val.of_bool (Int.eq n Int.zero))
      | Vptr _ _ => Some Vfalse
      | _ => None
      end
  | bool_case_f =>
      match v with
      | Vfloat f => Some (Val.of_bool (Float.cmp Ceq f Float.zero))
      | _ => None
      end
  | bool_default => None
  end.

Function sem_add (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  match classify_add t1 t2 with 
  | add_case_ii sg =>                   (**r integer addition *)
      match v1, v2 with
      | Vint n1, Vint n2 => Some (Vint (Int.add n1 n2))
      | _,  _ => None
      end
  | add_case_ff =>                      (**r float addition *)
      match v1, v2 with
      | Vfloat n1, Vfloat n2 => Some (Vfloat (Float.add n1 n2))
      | _,  _ => None
      end
  | add_case_if sg =>                   (**r int plus float *)
      match v1, v2 with
      | Vint n1, Vfloat n2 => Some (Vfloat (Float.add (cast_int_float sg n1) n2))
      | _, _ => None
      end
  | add_case_fi sg =>                   (**r float plus int *)
      match v1, v2 with
      | Vfloat n1, Vint n2 => Some (Vfloat (Float.add n1 (cast_int_float sg n2)))
      | _, _ => None
      end
  | add_case_pi ty _ =>                 (**r pointer plus integer *)
      match v1,v2 with
      | Vptr b1 ofs1, Vint n2 => 
        Some (Vptr b1 (Int.add ofs1 (Int.mul (Int.repr (sizeof ty)) n2)))
      | _,  _ => None
      end   
  | add_case_ip ty _ =>                 (**r integer plus pointer *)
      match v1,v2 with
      | Vint n1, Vptr b2 ofs2 => 
        Some (Vptr b2 (Int.add ofs2 (Int.mul (Int.repr (sizeof ty)) n1)))
      | _,  _ => None
      end   
  | add_default => None
end.

Function sem_sub (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  match classify_sub t1 t2 with
  | sub_case_ii sg =>            (**r integer subtraction *)
      match v1,v2 with
      | Vint n1, Vint n2 => Some (Vint (Int.sub n1 n2))
      | _,  _ => None
      end 
  | sub_case_ff =>               (**r float subtraction *)
      match v1,v2 with
      | Vfloat f1, Vfloat f2 => Some (Vfloat(Float.sub f1 f2))
      | _,  _ => None
      end
  | sub_case_if sg =>            (**r int minus float *)
      match v1, v2 with
      | Vint n1, Vfloat n2 => Some (Vfloat (Float.sub (cast_int_float sg n1) n2))
      | _, _ => None
      end
  | sub_case_fi sg =>            (**r float minus int *)
      match v1, v2 with
      | Vfloat n1, Vint n2 => Some (Vfloat (Float.sub n1 (cast_int_float sg n2)))
      | _, _ => None
      end
  | sub_case_pi ty =>            (**r pointer minus integer *)
      match v1,v2 with
      | Vptr b1 ofs1, Vint n2 => 
            Some (Vptr b1 (Int.sub ofs1 (Int.mul (Int.repr (sizeof ty)) n2)))
      | _,  _ => None
      end
  | sub_case_pp ty =>          (**r pointer minus pointer *)
      match v1,v2 with
      | Vptr b1 ofs1, Vptr b2 ofs2 =>
          if zeq b1 b2 then
            if Int.eq (Int.repr (sizeof ty)) Int.zero then None
            else Some (Vint (Int.divu (Int.sub ofs1 ofs2) (Int.repr (sizeof ty))))
          else None
      | _, _ => None
      end
  | sub_default => None
  end.
 
Function sem_mul (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
 match classify_mul t1 t2 with
  | mul_case_ii sg =>
      match v1,v2 with
      | Vint n1, Vint n2 => Some (Vint (Int.mul n1 n2))
      | _,  _ => None
      end
  | mul_case_ff =>
      match v1,v2 with
      | Vfloat f1, Vfloat f2 => Some (Vfloat (Float.mul f1 f2))
      | _,  _ => None
      end
  | mul_case_if sg =>
      match v1, v2 with
      | Vint n1, Vfloat n2 => Some (Vfloat (Float.mul (cast_int_float sg n1) n2))
      | _, _ => None
      end
  | mul_case_fi sg =>
      match v1, v2 with
      | Vfloat n1, Vint n2 => Some (Vfloat (Float.mul n1 (cast_int_float sg n2)))
      | _, _ => None
      end
  | mul_default =>
      None
end.

Function sem_div (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
   match classify_div t1 t2 with
  | div_case_ii Unsigned =>
      match v1,v2 with
      | Vint n1, Vint n2 =>
          if Int.eq n2 Int.zero then None else Some (Vint (Int.divu n1 n2))
      | _,_ => None
      end
  | div_case_ii Signed =>
      match v1,v2 with
       | Vint n1, Vint n2 =>
          if Int.eq n2 Int.zero
          || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
          then None else Some (Vint(Int.divs n1 n2))
      | _,_ => None
      end
  | div_case_ff =>
      match v1,v2 with
      | Vfloat f1, Vfloat f2 => Some (Vfloat(Float.div f1 f2))
      | _,  _ => None
      end 
  | div_case_if sg =>
      match v1, v2 with
      | Vint n1, Vfloat n2 => Some (Vfloat (Float.div (cast_int_float sg n1) n2))
      | _, _ => None
      end
  | div_case_fi sg =>
      match v1, v2 with
      | Vfloat n1, Vint n2 => Some (Vfloat (Float.div n1 (cast_int_float sg n2)))
      | _, _ => None
      end
  | div_default =>
      None
end.

Function sem_mod (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  match classify_binint t1 t2 with
  | binint_case_ii Unsigned =>
      match v1, v2 with
      | Vint n1, Vint n2 =>
          if Int.eq n2 Int.zero then None else Some (Vint (Int.modu n1 n2))
      | _, _ => None
      end
  | binint_case_ii Signed =>
      match v1,v2 with
      | Vint n1, Vint n2 =>
          if Int.eq n2 Int.zero
          || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
          then None else Some (Vint (Int.mods n1 n2))
      | _, _ => None
      end
  | binint_default =>
      None
  end.

Function sem_and (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  match classify_binint t1 t2 with
  | binint_case_ii sg =>
      match v1, v2 with
      | Vint n1, Vint n2 => Some (Vint(Int.and n1 n2))
      | _, _ => None
      end
  | binint_default => None
  end.

Function sem_or (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  match classify_binint t1 t2 with
  | binint_case_ii sg =>
      match v1, v2 with
      | Vint n1, Vint n2 => Some (Vint(Int.or n1 n2))
      | _, _ => None
      end
  | binint_default => None
  end.

Function sem_xor (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  match classify_binint t1 t2 with
  | binint_case_ii sg =>
      match v1, v2 with
      | Vint n1, Vint n2 => Some (Vint(Int.xor n1 n2))
      | _, _ => None
      end
  | binint_default => None
  end.

Function sem_shl (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  match classify_shift t1 t2 with
  | shift_case_ii sg =>
      match v1, v2 with
      | Vint n1, Vint n2 =>
         if Int.ltu n2 Int.iwordsize then Some (Vint(Int.shl n1 n2)) else None
      | _, _ => None
      end
  | shift_default => None
  end.

Function sem_shr (v1: val) (t1: type) (v2: val) (t2: type): option val :=
  match classify_shift t1 t2 with 
  | shift_case_ii Unsigned =>
      match v1,v2 with 
      | Vint n1, Vint n2 =>
          if Int.ltu n2 Int.iwordsize then Some (Vint (Int.shru n1 n2)) else None
      | _,_ => None
      end
   | shift_case_ii Signed =>
      match v1,v2 with
      | Vint n1,  Vint n2 =>
          if Int.ltu n2 Int.iwordsize then Some (Vint (Int.shr n1 n2)) else None
      | _,  _ => None
      end
   | shift_default =>
      None
   end.

Function sem_cmp_mismatch (c: comparison): option val :=
  match c with
  | Ceq =>  Some Vfalse
  | Cne =>  Some Vtrue
  | _   => None
  end.

Function sem_cmp (c:comparison)
                  (v1: val) (t1: type) (v2: val) (t2: type)
                  (m: mem): option val :=
  match classify_cmp t1 t2 with
  | cmp_case_ii Signed =>
      match v1,v2 with
      | Vint n1, Vint n2 => Some (Val.of_bool (Int.cmp c n1 n2))
      | _,  _ => None
      end
  | cmp_case_ii Unsigned =>
      match v1,v2 with
      | Vint n1, Vint n2 => Some (Val.of_bool (Int.cmpu c n1 n2))
      | _,  _ => None
      end
  | cmp_case_pp =>
      match v1,v2 with
      | Vint n1, Vint n2 => Some (Val.of_bool (Int.cmpu c n1 n2))
      | Vptr b1 ofs1,  Vptr b2 ofs2  =>
          if Mem.valid_pointer m b1 (Int.unsigned ofs1)
          && Mem.valid_pointer m b2 (Int.unsigned ofs2) then
            if zeq b1 b2
            then Some (Val.of_bool (Int.cmpu c ofs1 ofs2))
            else sem_cmp_mismatch c
          else None
      | Vptr b ofs, Vint n =>
          if Int.eq n Int.zero then sem_cmp_mismatch c else None
      | Vint n, Vptr b ofs =>
          if Int.eq n Int.zero then sem_cmp_mismatch c else None
      | _,  _ => None
      end
  | cmp_case_ff =>
      match v1,v2 with
      | Vfloat f1, Vfloat f2 => Some (Val.of_bool (Float.cmp c f1 f2))  
      | _,  _ => None
      end
  | cmp_case_if sg =>
      match v1, v2 with
      | Vint n1, Vfloat n2 => Some (Val.of_bool (Float.cmp c (cast_int_float sg n1) n2))
      | _, _ => None
      end
  | cmp_case_fi sg =>
      match v1, v2 with
      | Vfloat n1, Vint n2 => Some (Val.of_bool (Float.cmp c n1 (cast_int_float sg n2)))
      | _, _ => None
      end
  | cmp_default => None
  end.

Definition sem_unary_operation
            (op: unary_operation) (v: val) (ty: type): option val :=
  match op with
  | Onotbool => sem_notbool v ty
  | Onotint => sem_notint v ty
  | Oneg => sem_neg v ty
  end.

Definition sem_binary_operation
    (op: binary_operation)
    (v1: val) (t1: type) (v2: val) (t2:type)
    (m: mem): option val :=
  match op with
  | Oadd => sem_add v1 t1 v2 t2
  | Osub => sem_sub v1 t1 v2 t2 
  | Omul => sem_mul v1 t1 v2 t2
  | Omod => sem_mod v1 t1 v2 t2
  | Odiv => sem_div v1 t1 v2 t2 
  | Oand => sem_and v1 t1 v2 t2
  | Oor  => sem_or v1 t1 v2 t2
  | Oxor  => sem_xor v1 t1 v2 t2
  | Oshl => sem_shl v1 t1 v2 t2
  | Oshr  => sem_shr v1 t1 v2 t2   
  | Oeq => sem_cmp Ceq v1 t1 v2 t2 m
  | One => sem_cmp Cne v1 t1 v2 t2 m
  | Olt => sem_cmp Clt v1 t1 v2 t2 m
  | Ogt => sem_cmp Cgt v1 t1 v2 t2 m
  | Ole => sem_cmp Cle v1 t1 v2 t2 m
  | Oge => sem_cmp Cge v1 t1 v2 t2 m
  end.

Definition sem_incrdecr (id: incr_or_decr) (v: val) (ty: type) :=
  match id with
  | Incr => sem_add v ty (Vint Int.one) type_int32s
  | Decr => sem_sub v ty (Vint Int.one) type_int32s
  end.

(** Common-sense relations between boolean operators *)

Lemma cast_bool_bool_val:
  forall v t,
  sem_cast v t (Tint IBool Signed noattr) =
  match bool_val v t with None => None | Some b => Some(Val.of_bool b) end.
Proof.
  intros. unfold sem_cast, bool_val. destruct t; simpl; destruct v; auto.
  destruct (Int.eq i0 Int.zero); auto. 
  destruct (Float.cmp Ceq f0 Float.zero); auto.
  destruct (Int.eq i Int.zero); auto. 
  destruct (Int.eq i Int.zero); auto. 
  destruct (Int.eq i Int.zero); auto. 
Qed.

Lemma notbool_bool_val:
  forall v t,
  sem_notbool v t =
  match bool_val v t with None => None | Some b => Some(Val.of_bool (negb b)) end.
Proof.
  assert (CB: forall i s a, classify_bool (Tint i s a) = bool_case_ip).
    intros. destruct i; auto. destruct s; auto. 
  intros. unfold sem_notbool, bool_val. destruct t; try rewrite CB; simpl; destruct v; auto.
  destruct (Int.eq i0 Int.zero); auto. 
  destruct (Float.cmp Ceq f0 Float.zero); auto.
  destruct (Int.eq i Int.zero); auto. 
  destruct (Int.eq i Int.zero); auto. 
  destruct (Int.eq i Int.zero); auto. 
Qed.

(** * Operational semantics *)

(** The semantics uses two environments.  The global environment
  maps names of functions and global variables to memory block references,
  and function pointers to their definitions.  (See module [Globalenvs].) *)

Definition genv := Genv.t fundef type.

(** The local environment maps local variables to block references and types.
  The current value of the variable is stored in the associated memory
  block. *)

Definition env := PTree.t (block * type). (* map variable -> location & type *)

Definition empty_env: env := (PTree.empty (block * type)).

(** [deref_loc ty m b ofs t v] computes the value of a datum
  of type [ty] residing in memory [m] at block [b], offset [ofs].
  If the type [ty] indicates an access by value, the corresponding
  memory load is performed.  If the type [ty] indicates an access by
  reference, the pointer [Vptr b ofs] is returned.  [v] is the value
  returned, and [t] the trace of observables (nonempty if this is
  a volatile access). *)

Inductive deref_loc {F V: Type} (ge: Genv.t F V) (ty: type) (m: mem) (b: block) (ofs: int) : trace -> val -> Prop :=
  | deref_loc_value: forall chunk v,
      access_mode ty = By_value chunk ->
      type_is_volatile ty = false ->
      Mem.loadv chunk m (Vptr b ofs) = Some v ->
      deref_loc ge ty m b ofs E0 v
  | deref_loc_volatile: forall chunk t v,
      access_mode ty = By_value chunk -> type_is_volatile ty = true ->
      volatile_load ge chunk m b ofs t v ->
      deref_loc ge ty m b ofs t v
  | deref_loc_reference:
      access_mode ty = By_reference ->
      deref_loc ge ty m b ofs E0 (Vptr b ofs)
  | deref_loc_copy:
      access_mode ty = By_copy ->
      deref_loc ge ty m b ofs E0 (Vptr b ofs).

(** Symmetrically, [assign_loc ty m b ofs v t m'] returns the
  memory state after storing the value [v] in the datum
  of type [ty] residing in memory [m] at block [b], offset [ofs].
  This is allowed only if [ty] indicates an access by value or by copy.
  [m'] is the updated memory state and [t] the trace of observables
  (nonempty if this is a volatile store). *)

Inductive assign_loc {F V: Type} (ge: Genv.t F V) (ty: type) (m: mem) (b: block) (ofs: int):
                                            val -> trace -> mem -> Prop :=
  | assign_loc_value: forall v chunk m',
      access_mode ty = By_value chunk ->
      type_is_volatile ty = false ->
      Mem.storev chunk m (Vptr b ofs) v = Some m' ->
      assign_loc ge ty m b ofs v E0 m'
  | assign_loc_volatile: forall v chunk t m',
      access_mode ty = By_value chunk -> type_is_volatile ty = true ->
      volatile_store ge chunk m b ofs v t m' ->
      assign_loc ge ty m b ofs v t m'
  | assign_loc_copy: forall b' ofs' bytes m',
      access_mode ty = By_copy ->
      (alignof ty | Int.unsigned ofs') -> (alignof ty | Int.unsigned ofs) ->
      b' <> b \/ Int.unsigned ofs' = Int.unsigned ofs
              \/ Int.unsigned ofs' + sizeof ty <= Int.unsigned ofs
              \/ Int.unsigned ofs + sizeof ty <= Int.unsigned ofs' ->
      Mem.loadbytes m b' (Int.unsigned ofs') (sizeof ty) = Some bytes ->
      Mem.storebytes m b (Int.unsigned ofs) bytes = Some m' ->
      assign_loc ge ty m b ofs (Vptr b' ofs') E0 m'.

(** Allocation of function-local variables.
  [alloc_variables e1 m1 vars e2 m2] allocates one memory block
  for each variable declared in [vars], and associates the variable
  name with this block.  [e1] and [m1] are the initial local environment
  and memory state.  [e2] and [m2] are the final local environment
  and memory state. *)

Inductive alloc_variables: env -> mem ->
                           list (ident * type) ->
                           env -> mem -> Prop :=
  | alloc_variables_nil:
      forall e m,
      alloc_variables e m nil e m
  | alloc_variables_cons:
      forall e m id ty vars m1 b1 m2 e2,
      Mem.alloc m 0 (sizeof ty) = (m1, b1) ->
      alloc_variables (PTree.set id (b1, ty) e) m1 vars e2 m2 ->
      alloc_variables e m ((id, ty) :: vars) e2 m2.

(** Initialization of local variables that are parameters to a function.
  [bind_parameters e m1 params args m2] stores the values [args]
  in the memory blocks corresponding to the variables [params].
  [m1] is the initial memory state and [m2] the final memory state. *)

Inductive bind_parameters {F V: Type} (ge: Genv.t F V) (e: env):
                           mem -> list (ident * type) -> list val ->
                           mem -> Prop :=
  | bind_parameters_nil:
      forall m,
      bind_parameters ge e m nil nil m
  | bind_parameters_cons:
      forall m id ty params v1 vl b m1 m2,
      PTree.get id e = Some(b, ty) ->
      assign_loc ge ty m b Int.zero v1 E0 m1 ->
      bind_parameters ge e m1 params vl m2 ->
      bind_parameters ge e m ((id, ty) :: params) (v1 :: vl) m2.

(** Return the list of blocks in the codomain of [e], with low and high bounds. *)

Definition block_of_binding (id_b_ty: ident * (block * type)) :=
  match id_b_ty with (id, (b, ty)) => (b, 0, sizeof ty) end.

Definition blocks_of_env (e: env) : list (block * Z * Z) :=
  List.map block_of_binding (PTree.elements e).

(** Selection of the appropriate case of a [switch], given the value [n]
  of the selector expression. *)

Fixpoint select_switch (n: int) (sl: labeled_statements)
                       {struct sl}: labeled_statements :=
  match sl with
  | LSdefault _ => sl
  | LScase c s sl' => if Int.eq c n then sl else select_switch n sl'
  end.

(** Turn a labeled statement into a sequence *)

Fixpoint seq_of_labeled_statement (sl: labeled_statements) : statement :=
  match sl with
  | LSdefault s => s
  | LScase c s sl' => Ssequence s (seq_of_labeled_statement sl')
  end.

Section SEMANTICS.

Variable ge: genv.

(** [type_of_global b] returns the type of the global variable or function
  at address [b]. *)

Definition type_of_global (b: block) : option type :=
  match Genv.find_var_info ge b with
  | Some gv => Some gv.(gvar_info)
  | None =>
      match Genv.find_funct_ptr ge b with
      | Some fd => Some(type_of_fundef fd)
      | None => None
      end
  end.

(** ** Reduction semantics for expressions *)

Section EXPR.

Variable e: env.

(** The semantics of expressions follows the popular Wright-Felleisen style.
  It is a small-step semantics that reduces one redex at a time.
  We first define head reductions (at the top of an expression, then
  use reduction contexts to define reduction within an expression. *)

(** Head reduction for l-values. *)

Inductive lred: expr -> mem -> expr -> mem -> Prop :=
  | red_var_local: forall x ty m b,
      e!x = Some(b, ty) ->
      lred (Evar x ty) m
           (Eloc b Int.zero ty) m
  | red_var_global: forall x ty m b,
      e!x = None ->
      Genv.find_symbol ge x = Some b ->
      type_of_global b = Some ty ->
      lred (Evar x ty) m
           (Eloc b Int.zero ty) m
  | red_deref: forall b ofs ty1 ty m,
      lred (Ederef (Eval (Vptr b ofs) ty1) ty) m
           (Eloc b ofs ty) m
  | red_field_struct: forall b ofs id fList a f ty m delta,
      field_offset f fList = OK delta ->
      lred (Efield (Eval (Vptr b ofs) (Tstruct id fList a)) f ty) m
           (Eloc b (Int.add ofs (Int.repr delta)) ty) m
  | red_field_union: forall b ofs id fList a f ty m,
      lred (Efield (Eval (Vptr b ofs) (Tunion id fList a)) f ty) m
           (Eloc b ofs ty) m.

(** Head reductions for r-values *)

Inductive rred: expr -> mem -> trace -> expr -> mem -> Prop :=
  | red_rvalof: forall b ofs ty m t v,
      deref_loc ge ty m b ofs t v ->
      rred (Evalof (Eloc b ofs ty) ty) m
         t (Eval v ty) m
  | red_addrof: forall b ofs ty1 ty m,
      rred (Eaddrof (Eloc b ofs ty1) ty) m
        E0 (Eval (Vptr b ofs) ty) m
  | red_unop: forall op v1 ty1 ty m v,
      sem_unary_operation op v1 ty1 = Some v ->
      rred (Eunop op (Eval v1 ty1) ty) m
        E0 (Eval v ty) m
  | red_binop: forall op v1 ty1 v2 ty2 ty m v,
      sem_binary_operation op v1 ty1 v2 ty2 m = Some v ->
      rred (Ebinop op (Eval v1 ty1) (Eval v2 ty2) ty) m
        E0 (Eval v ty) m
  | red_cast: forall ty v1 ty1 m v,
      sem_cast v1 ty1 ty = Some v ->
      rred (Ecast (Eval v1 ty1) ty) m
        E0 (Eval v ty) m
  | red_condition: forall v1 ty1 r1 r2 ty b m,
      bool_val v1 ty1 = Some b ->
      rred (Econdition (Eval v1 ty1) r1 r2 ty) m
        E0 (Eparen (if b then r1 else r2) ty) m
  | red_sizeof: forall ty1 ty m,
      rred (Esizeof ty1 ty) m
        E0 (Eval (Vint (Int.repr (sizeof ty1))) ty) m
  | red_alignof: forall ty1 ty m,
      rred (Ealignof ty1 ty) m
        E0 (Eval (Vint (Int.repr (alignof ty1))) ty) m
  | red_assign: forall b ofs ty1 v2 ty2 m v t m',
      sem_cast v2 ty2 ty1 = Some v ->
      assign_loc ge ty1 m b ofs v t m' ->
      rred (Eassign (Eloc b ofs ty1) (Eval v2 ty2) ty1) m
         t (Eval v ty1) m'
  | red_assignop: forall op b ofs ty1 v2 ty2 tyres m t v1,
      deref_loc ge ty1 m b ofs t v1 ->
      rred (Eassignop op (Eloc b ofs ty1) (Eval v2 ty2) tyres ty1) m
         t (Eassign (Eloc b ofs ty1)
                    (Ebinop op (Eval v1 ty1) (Eval v2 ty2) tyres) ty1) m
  | red_postincr: forall id b ofs ty m t v1 op,
      deref_loc ge ty m b ofs t v1 ->
      op = match id with Incr => Oadd | Decr => Osub end ->
      rred (Epostincr id (Eloc b ofs ty) ty) m
         t (Ecomma (Eassign (Eloc b ofs ty) 
                           (Ebinop op (Eval v1 ty) (Eval (Vint Int.one) type_int32s) (typeconv ty))
                           ty)
                   (Eval v1 ty) ty) m
  | red_comma: forall v ty1 r2 ty m,
      typeof r2 = ty ->
      rred (Ecomma (Eval v ty1) r2 ty) m
        E0 r2 m
  | red_paren: forall v1 ty1 ty m v,
      sem_cast v1 ty1 ty = Some v ->
      rred (Eparen (Eval v1 ty1) ty) m
        E0 (Eval v ty) m.

(** Head reduction for function calls.
    (More exactly, identification of function calls that can reduce.) *)

Inductive cast_arguments: exprlist -> typelist -> list val -> Prop :=
  | cast_args_nil:
      cast_arguments Enil Tnil nil
  | cast_args_cons: forall v ty el targ1 targs v1 vl,
      sem_cast v ty targ1 = Some v1 -> cast_arguments el targs vl ->
      cast_arguments (Econs (Eval v ty) el) (Tcons targ1 targs) (v1 :: vl).

Inductive callred: expr -> fundef -> list val -> type -> Prop :=
  | red_Ecall: forall vf tyf tyargs tyres el ty fd vargs,
      Genv.find_funct ge vf = Some fd ->
      cast_arguments el tyargs vargs ->
      type_of_fundef fd = Tfunction tyargs tyres ->
      classify_fun tyf = fun_case_f tyargs tyres ->
      callred (Ecall (Eval vf tyf) el ty)
              fd vargs ty.

(** Reduction contexts.  In accordance with C's nondeterministic semantics,
  we allow reduction both to the left and to the right of a binary operator.
  To enforce C's notion of sequence point, reductions within a conditional
  [a ? b : c] can only take place in [a], not in [b] nor [c];
  and reductions within a sequence [a, b] can only take place in [a], not in [b].

  Reduction contexts are represented by functions [C] from expressions to expressions,
  suitably constrained by the [context from to C] predicate below.
  Contexts are "kinded" with respect to l-values and r-values:
  [from] is the kind of the hole in the context and [to] is the kind of
  the term resulting from filling the hole.
*)

Inductive kind : Type := LV | RV.

Inductive context: kind -> kind -> (expr -> expr) -> Prop :=
  | ctx_top: forall k,
      context k k (fun x => x)
  | ctx_deref: forall k C ty,
      context k RV C -> context k LV (fun x => Ederef (C x) ty)
  | ctx_field: forall k C f ty,
      context k RV C -> context k LV (fun x => Efield (C x) f ty)
  | ctx_rvalof: forall k C ty,
      context k LV C -> context k RV (fun x => Evalof (C x) ty)
  | ctx_addrof: forall k C ty,
      context k LV C -> context k RV (fun x => Eaddrof (C x) ty)
  | ctx_unop: forall k C op ty,
      context k RV C -> context k RV (fun x => Eunop op (C x) ty)
  | ctx_binop_left: forall k C op e2 ty,
      context k RV C -> context k RV (fun x => Ebinop op (C x) e2 ty)
  | ctx_binop_right: forall k C op e1 ty,
      context k RV C -> context k RV (fun x => Ebinop op e1 (C x) ty)
  | ctx_cast: forall k C ty,
      context k RV C -> context k RV (fun x => Ecast (C x) ty)
  | ctx_condition: forall k C r2 r3 ty,
      context k RV C -> context k RV (fun x => Econdition (C x) r2 r3 ty)
  | ctx_assign_left: forall k C e2 ty,
      context k LV C -> context k RV (fun x => Eassign (C x) e2 ty)
  | ctx_assign_right: forall k C e1 ty,
      context k RV C -> context k RV (fun x => Eassign e1 (C x) ty)
  | ctx_assignop_left: forall k C op e2 tyres ty,
      context k LV C -> context k RV (fun x => Eassignop op (C x) e2 tyres ty)
  | ctx_assignop_right: forall k C op e1 tyres ty,
      context k RV C -> context k RV (fun x => Eassignop op e1 (C x) tyres ty)
  | ctx_postincr: forall k C id ty,
      context k LV C -> context k RV (fun x => Epostincr id (C x) ty)
  | ctx_call_left: forall k C el ty,
      context k RV C -> context k RV (fun x => Ecall (C x) el ty)
  | ctx_call_right: forall k C e1 ty,
      contextlist k C -> context k RV (fun x => Ecall e1 (C x) ty)
  | ctx_comma: forall k C e2 ty,
      context k RV C -> context k RV (fun x => Ecomma (C x) e2 ty)
  | ctx_paren: forall k C ty,
      context k RV C -> context k RV (fun x => Eparen (C x) ty)

with contextlist: kind -> (expr -> exprlist) -> Prop :=
  | ctx_list_head: forall k C el,
      context k RV C -> contextlist k (fun x => Econs (C x) el)
  | ctx_list_tail: forall k C e1,
      contextlist k C -> contextlist k (fun x => Econs e1 (C x)).

(** In a nondeterministic semantics, expressions can go wrong according
  to one reduction order while being defined according to another.
  Consider for instance [(x = 1) + (10 / x)] where [x] is initially [0].
  This expression goes wrong if evaluated right-to-left, but is defined
  if evaluated left-to-right.  Since our compiler is going to pick one
  particular evaluation order, we must make sure that all orders are safe,
  i.e. never evaluate a subexpression that goes wrong.

  Being safe is a stronger requirement than just not getting stuck during
  reductions.  Consider [f() + (10 / x)], where [f()] does not terminate.
  This expression is never stuck because the evaluation of [f()] can make
  infinitely many transitions.  Yet it contains a subexpression [10 / x]
  that can go wrong if [x = 0], and the compiler may choose to evaluate
  [10 / x] first, before calling [f()].  

  Therefore, we must make sure that not only an expression cannot get stuck,
  but none of its subexpressions can either.  We say that a subexpression
  is not immediately stuck if it is a value (of the appropriate kind)
  or it can reduce (at head or within). *)

Inductive imm_safe: kind -> expr -> mem -> Prop :=
  | imm_safe_val: forall v ty m,
      imm_safe RV (Eval v ty) m
  | imm_safe_loc: forall b ofs ty m,
      imm_safe LV (Eloc b ofs ty) m
  | imm_safe_lred: forall to C e m e' m',
      lred e m e' m' ->
      context LV to C ->
      imm_safe to (C e) m
  | imm_safe_rred: forall to C e m t e' m',
      rred e m t e' m' ->
      context RV to C ->
      imm_safe to (C e) m
  | imm_safe_callred: forall to C e m fd args ty,
      callred e fd args ty ->
      context RV to C ->
      imm_safe to (C e) m.

(* An expression is not stuck if none of the potential redexes contained within
   is immediately stuck. *)
(*
Definition not_stuck (e: expr) (m: mem) : Prop :=
  forall k C e' , 
  context k RV C -> e = C e' -> not_imm_stuck k e' m.
*)
End EXPR. 

(** ** Transition semantics. *)

(** Continuations describe the computations that remain to be performed
    after the statement or expression under consideration has
    evaluated completely. *)

Inductive cont: Type :=
  | Kstop: cont
  | Kdo: cont -> cont       (**r [Kdo k] = after [x] in [x;] *)
  | Kseq: statement -> cont -> cont    (**r [Kseq s2 k] = after [s1] in [s1;s2] *)
  | Kifthenelse: statement -> statement -> cont -> cont     (**r [Kifthenelse s1 s2 k] = after [x] in [if (x) { s1 } else { s2 }] *)
  | Kwhile1: expr -> statement -> cont -> cont      (**r [Kwhile1 x s k] = after [x] in [while(x) s] *)
  | Kwhile2: expr -> statement -> cont -> cont      (**r [Kwhile x s k] = after [s] in [while (x) s] *)
  | Kdowhile1: expr -> statement -> cont -> cont    (**r [Kdowhile1 x s k] = after [s] in [do s while (x)] *)
  | Kdowhile2: expr -> statement -> cont -> cont    (**r [Kdowhile2 x s k] = after [x] in [do s while (x)] *)
  | Kfor2: expr -> statement -> statement -> cont -> cont   (**r [Kfor2 e2 e3 s k] = after [e2] in [for(e1;e2;e3) s] *)
  | Kfor3: expr -> statement -> statement -> cont -> cont   (**r [Kfor3 e2 e3 s k] = after [s] in [for(e1;e2;e3) s] *)
  | Kfor4: expr -> statement -> statement -> cont -> cont   (**r [Kfor3 e2 e3 s k] = after [e3] in [for(e1;e2;e3) s] *)
  | Kswitch1: labeled_statements -> cont -> cont     (**r [Kswitch1 ls k] = after [e] in [switch(e) { ls }] *)
  | Kswitch2: cont -> cont       (**r catches [break] statements arising out of [switch] *)
  | Kreturn: cont -> cont        (**r [Kreturn k] = after [e] in [return e;] *)
  | Kcall: function ->           (**r calling function *)
           env ->                (**r local env of calling function *)
           (expr -> expr) ->     (**r context of the call *)
           type ->               (**r type of call expression *)
           cont -> cont.

(** Pop continuation until a call or stop *)

Fixpoint call_cont (k: cont) : cont :=
  match k with
  | Kstop => k
  | Kdo k => k
  | Kseq s k => call_cont k
  | Kifthenelse s1 s2 k => call_cont k
  | Kwhile1 e s k => call_cont k
  | Kwhile2 e s k => call_cont k
  | Kdowhile1 e s k => call_cont k
  | Kdowhile2 e s k => call_cont k
  | Kfor2 e2 e3 s k => call_cont k
  | Kfor3 e2 e3 s k => call_cont k
  | Kfor4 e2 e3 s k => call_cont k
  | Kswitch1 ls k => call_cont k
  | Kswitch2 k => call_cont k
  | Kreturn k => call_cont k
  | Kcall _ _ _ _ _ => k
  end.

Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ _ => True
  | _ => False
  end.

(** Execution states of the program are grouped in 4 classes corresponding
  to the part of the program we are currently executing.  It can be
  a statement ([State]), an expression ([ExprState]), a transition
  from a calling function to a called function ([Callstate]), or
  the symmetrical transition from a function back to its caller
  ([Returnstate]). *)

Inductive state: Type :=
  | State                               (**r execution of a statement *)
      (f: function)
      (s: statement)
      (k: cont)
      (e: env)
      (m: mem) : state
  | ExprState                           (**r reduction of an expression *)
      (f: function)
      (r: expr)
      (k: cont)
      (e: env)
      (m: mem) : state
  | Callstate                           (**r calling a function *)
      (fd: fundef)
      (args: list val)
      (k: cont)
      (m: mem) : state
  | Returnstate                         (**r returning from a function *)
      (res: val)
      (k: cont)
      (m: mem) : state
  | Stuckstate.                         (**r undefined behavior occurred *)
                 
(** Find the statement and manufacture the continuation 
  corresponding to a label. *)

Fixpoint find_label (lbl: label) (s: statement) (k: cont) 
                    {struct s}: option (statement * cont) :=
  match s with
  | Ssequence s1 s2 =>
      match find_label lbl s1 (Kseq s2 k) with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Sifthenelse a s1 s2 =>
      match find_label lbl s1 k with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Swhile a s1 =>
      find_label lbl s1 (Kwhile2 a s1 k)
  | Sdowhile a s1 =>
      find_label lbl s1 (Kdowhile1 a s1 k)
  | Sfor a1 a2 a3 s1 =>
      match find_label lbl a1 (Kseq (Sfor Sskip a2 a3 s1) k) with
      | Some sk => Some sk
      | None =>
          match find_label lbl s1 (Kfor3 a2 a3 s1 k) with
          | Some sk => Some sk
          | None => find_label lbl a3 (Kfor4 a2 a3 s1 k)
          end
      end
  | Sswitch e sl =>
      find_label_ls lbl sl (Kswitch2 k)
  | Slabel lbl' s' =>
      if ident_eq lbl lbl' then Some(s', k) else find_label lbl s' k
  | _ => None
  end

with find_label_ls (lbl: label) (sl: labeled_statements) (k: cont) 
                    {struct sl}: option (statement * cont) :=
  match sl with
  | LSdefault s => find_label lbl s k
  | LScase _ s sl' =>
      match find_label lbl s (Kseq (seq_of_labeled_statement sl') k) with
      | Some sk => Some sk
      | None => find_label_ls lbl sl' k
      end
  end.

(** We separate the transition rules in two groups:
- one group that deals with reductions over expressions;
- the other group that deals with everything else: statements, function calls, etc.

This makes it easy to express different reduction strategies for expressions:
the second group of rules can be reused as is. *)

Inductive estep: state -> trace -> state -> Prop :=

  | step_lred: forall C f a k e m a' m',
      lred e a m a' m' ->
      context LV RV C ->
      estep (ExprState f (C a) k e m)
         E0 (ExprState f (C a') k e m')

  | step_rred: forall C f a k e m t a' m',
      rred a m t a' m' ->
      context RV RV C ->
      estep (ExprState f (C a) k e m)
          t (ExprState f (C a') k e m')

  | step_call: forall C f a k e m fd vargs ty,
      callred a fd vargs ty ->
      context RV RV C ->
      estep (ExprState f (C a) k e m)
         E0 (Callstate fd vargs (Kcall f e C ty k) m)

  | step_stuck: forall C f a k e m K,
      context K RV C -> ~(imm_safe e K a m) ->
      estep (ExprState f (C a) k e m)
         E0 Stuckstate.

Inductive sstep: state -> trace -> state -> Prop :=

  | step_do_1: forall f x k e m,
      sstep (State f (Sdo x) k e m)
         E0 (ExprState f x (Kdo k) e m)
  | step_do_2: forall f v ty k e m,
      sstep (ExprState f (Eval v ty) (Kdo k) e m)
         E0 (State f Sskip k e m)

  | step_seq:  forall f s1 s2 k e m,
      sstep (State f (Ssequence s1 s2) k e m)
         E0 (State f s1 (Kseq s2 k) e m)
  | step_skip_seq: forall f s k e m,
      sstep (State f Sskip (Kseq s k) e m)
         E0 (State f s k e m)
  | step_continue_seq: forall f s k e m,
      sstep (State f Scontinue (Kseq s k) e m)
         E0 (State f Scontinue k e m)
  | step_break_seq: forall f s k e m,
      sstep (State f Sbreak (Kseq s k) e m)
         E0 (State f Sbreak k e m)

  | step_ifthenelse_1: forall f a s1 s2 k e m,
      sstep (State f (Sifthenelse a s1 s2) k e m)
         E0 (ExprState f a (Kifthenelse s1 s2 k) e m)
  | step_ifthenelse_2:  forall f v ty s1 s2 k e m b,
      bool_val v ty = Some b ->
      sstep (ExprState f (Eval v ty) (Kifthenelse s1 s2 k) e m)
         E0 (State f (if b then s1 else s2) k e m)

  | step_while: forall f x s k e m,
      sstep (State f (Swhile x s) k e m)
        E0 (ExprState f x (Kwhile1 x s k) e m)
  | step_while_false: forall f v ty x s k e m,
      bool_val v ty = Some false ->
      sstep (ExprState f (Eval v ty) (Kwhile1 x s k) e m)
        E0 (State f Sskip k e m)
  | step_while_true: forall f v ty x s k e m ,
      bool_val v ty = Some true ->
      sstep (ExprState f (Eval v ty) (Kwhile1 x s k) e m)
        E0 (State f s (Kwhile2 x s k) e m)
  | step_skip_or_continue_while: forall f s0 x s k e m,
      s0 = Sskip \/ s0 = Scontinue ->
      sstep (State f s0 (Kwhile2 x s k) e m)
        E0 (State f (Swhile x s) k e m)
  | step_break_while: forall f x s k e m,
      sstep (State f Sbreak (Kwhile2 x s k) e m)
        E0 (State f Sskip k e m)

  | step_dowhile: forall f a s k e m,
      sstep (State f (Sdowhile a s) k e m)
        E0 (State f s (Kdowhile1 a s k) e m)
  | step_skip_or_continue_dowhile: forall f s0 x s k e m,
      s0 = Sskip \/ s0 = Scontinue ->
      sstep (State f s0 (Kdowhile1 x s k) e m)
         E0 (ExprState f x (Kdowhile2 x s k) e m)
  | step_dowhile_false: forall f v ty x s k e m,
      bool_val v ty = Some false ->
      sstep (ExprState f (Eval v ty) (Kdowhile2 x s k) e m)
         E0 (State f Sskip k e m)
  | step_dowhile_true: forall f v ty x s k e m,
      bool_val v ty = Some true ->
      sstep (ExprState f (Eval v ty) (Kdowhile2 x s k) e m)
         E0 (State f (Sdowhile x s) k e m)
  | step_break_dowhile: forall f a s k e m,
      sstep (State f Sbreak (Kdowhile1 a s k) e m)
         E0 (State f Sskip k e m)

  | step_for_start: forall f a1 a2 a3 s k e m,
      a1 <> Sskip ->
      sstep (State f (Sfor a1 a2 a3 s) k e m)
         E0 (State f a1 (Kseq (Sfor Sskip a2 a3 s) k) e m)
  | step_for: forall f a2 a3 s k e m,
      sstep (State f (Sfor Sskip a2 a3 s) k e m)
         E0 (ExprState f a2 (Kfor2 a2 a3 s k) e m)
  | step_for_false: forall f v ty a2 a3 s k e m,
      bool_val v ty = Some false ->
      sstep (ExprState f (Eval v ty) (Kfor2 a2 a3 s k) e m)
         E0 (State f Sskip k e m)
  | step_for_true: forall f v ty a2 a3 s k e m,
      bool_val v ty = Some true ->
      sstep (ExprState f (Eval v ty) (Kfor2 a2 a3 s k) e m)
         E0 (State f s (Kfor3 a2 a3 s k) e m)
  | step_skip_or_continue_for3: forall f x a2 a3 s k e m,
      x = Sskip \/ x = Scontinue ->
      sstep (State f x (Kfor3 a2 a3 s k) e m)
         E0 (State f a3 (Kfor4 a2 a3 s k) e m)
  | step_break_for3: forall f a2 a3 s k e m,
      sstep (State f Sbreak (Kfor3 a2 a3 s k) e m)
         E0 (State f Sskip k e m)
  | step_skip_for4: forall f a2 a3 s k e m,
      sstep (State f Sskip (Kfor4 a2 a3 s k) e m)
         E0 (State f (Sfor Sskip a2 a3 s) k e m)

  | step_return_0: forall f k e m m',
      Mem.free_list m (blocks_of_env e) = Some m' ->
      sstep (State f (Sreturn None) k e m)
         E0 (Returnstate Vundef (call_cont k) m')
  | step_return_1: forall f x k e m,
      sstep (State f (Sreturn (Some x)) k e m)
         E0 (ExprState f x (Kreturn k) e  m)
  | step_return_2:  forall f v1 ty k e m v2 m',
      sem_cast v1 ty f.(fn_return) = Some v2 ->
      Mem.free_list m (blocks_of_env e) = Some m' ->
      sstep (ExprState f (Eval v1 ty) (Kreturn k) e m)
         E0 (Returnstate v2 (call_cont k) m')
  | step_skip_call: forall f k e m m',
      is_call_cont k ->
      f.(fn_return) = Tvoid ->
      Mem.free_list m (blocks_of_env e) = Some m' ->
      sstep (State f Sskip k e m)
         E0 (Returnstate Vundef k m')

  | step_switch: forall f x sl k e m,
      sstep (State f (Sswitch x sl) k e m)
         E0 (ExprState f x (Kswitch1 sl k) e m)
  | step_expr_switch: forall f n ty sl k e m,
      sstep (ExprState f (Eval (Vint n) ty) (Kswitch1 sl k) e m)
         E0 (State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch2 k) e m)
  | step_skip_break_switch: forall f x k e m,
      x = Sskip \/ x = Sbreak ->
      sstep (State f x (Kswitch2 k) e m)
         E0 (State f Sskip k e m)
  | step_continue_switch: forall f k e m,
      sstep (State f Scontinue (Kswitch2 k) e m)
         E0 (State f Scontinue k e m)

  | step_label: forall f lbl s k e m,
      sstep (State f (Slabel lbl s) k e m)
         E0 (State f s k e m)

  | step_goto: forall f lbl k e m s' k',
      find_label lbl f.(fn_body) (call_cont k) = Some (s', k') ->
      sstep (State f (Sgoto lbl) k e m)
         E0 (State f s' k' e m)

  | step_internal_function: forall f vargs k m e m1 m2,
      list_norepet (var_names (fn_params f) ++ var_names (fn_vars f)) ->
      alloc_variables empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 ->
      bind_parameters ge e m1 f.(fn_params) vargs m2 ->
      sstep (Callstate (Internal f) vargs k m)
         E0 (State f f.(fn_body) k e m2)

  | step_external_function: forall ef targs tres vargs k m vres t m',
      external_call ef  ge vargs m t vres m' ->
      sstep (Callstate (External ef targs tres) vargs k m)
          t (Returnstate vres k m')

  | step_returnstate: forall v f e C ty k m,
      sstep (Returnstate v (Kcall f e C ty k) m)
         E0 (ExprState f (C (Eval v ty)) k e m).

Definition step (S: state) (t: trace) (S': state) : Prop :=
  estep S t S' \/ sstep S t S'.

End SEMANTICS.

(** * Whole-program semantics *)

(** Execution of whole programs are described as sequences of transitions
  from an initial state to a final state.  An initial state is a [Callstate]
  corresponding to the invocation of the ``main'' function of the program
  without arguments and with an empty continuation. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction Tnil type_int32s ->
      initial_state p (Callstate f nil Kstop m0).

(** A final state is a [Returnstate] with an empty continuation. *)

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall r m,
      final_state (Returnstate (Vint r) Kstop m) r.

(** Wrapping up these definitions in a small-step semantics. *)

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

(** This semantics has the single-event property. *)

Lemma semantics_single_events: 
  forall p, single_events (semantics p).
Proof.
  intros; red; intros. destruct H. 
  set (ge := globalenv (semantics p)) in *.
  assert (DEREF: forall chunk m b ofs t v, deref_loc ge chunk m b ofs t v -> (length t <= 1)%nat).
    intros. inv H0; simpl; try omega. inv H3; simpl; try omega.
  assert (ASSIGN: forall chunk m b ofs t v m', assign_loc ge chunk m b ofs v t m' -> (length t <= 1)%nat).
    intros. inv H0; simpl; try omega. inv H3; simpl; try omega.
  inv H; simpl; try omega. inv H0; eauto; simpl; try omega.
  inv H; simpl; try omega. eapply external_call_trace_length; eauto.
Qed.
