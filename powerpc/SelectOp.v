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

(** Instruction selection for operators *)

(** The instruction selection pass recognizes opportunities for using
  combined arithmetic and logical operations and addressing modes
  offered by the target processor.  For instance, the expression [x + 1]
  can take advantage of the "immediate add" instruction of the processor,
  and on the PowerPC, the expression [(x >> 6) & 0xFF] can be turned
  into a "rotate and mask" instruction.

  This file defines functions for building CminorSel expressions and
  statements, especially expressions consisting of operator
  applications.  These functions examine their arguments to choose
  cheaper forms of operators whenever possible.

  For instance, [add e1 e2] will return a CminorSel expression semantically
  equivalent to [Eop Oadd (e1 ::: e2 ::: Enil)], but will use a
  [Oaddimm] operator if one of the arguments is an integer constant,
  or suppress the addition altogether if one of the arguments is the
  null integer.  In passing, we perform operator reassociation
  ([(e + c1) * c2] becomes [(e * c2) + (c1 * c2)]) and a small amount
  of constant propagation.

  On top of the "smart constructor" functions defined below,
  module [Selection] implements the actual instruction selection pass.
*)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Cminor.
Require Import Op.
Require Import CminorSel.

Open Local Scope cminorsel_scope.

(** ** Constants **)

Definition addrsymbol (id: ident) (ofs: int) :=
  Eop (Oaddrsymbol id ofs) Enil.

Definition addrstack (ofs: int) :=
  Eop (Oaddrstack ofs) Enil.

(** ** Integer logical negation *)

(** Original definition:
<<
Nondetfunction notint (e: expr) :=
  match e with
  | Eop (Ointconst n) Enil => Eop (Ointconst (Int.not n)) Enil
  | Eop Oand (t1:::t2:::Enil) => Eop Onand (t1:::t2:::Enil)
  | Eop Oor (t1:::t2:::Enil) => Eop Onor (t1:::t2:::Enil)
  | Eop Oxor (t1:::t2:::Enil) => Eop Onxor (t1:::t2:::Enil)
  | _ => Elet e (Eop Onor (Eletvar O ::: Eletvar O ::: Enil))
  end.
>>
*)

Inductive notint_cases: forall (e: expr), Type :=
  | notint_case1: forall n, notint_cases (Eop (Ointconst n) Enil)
  | notint_case2: forall t1 t2, notint_cases (Eop Oand (t1:::t2:::Enil))
  | notint_case3: forall t1 t2, notint_cases (Eop Oor (t1:::t2:::Enil))
  | notint_case4: forall t1 t2, notint_cases (Eop Oxor (t1:::t2:::Enil))
  | notint_default: forall (e: expr), notint_cases e.

Definition notint_match (e: expr) :=
  match e as zz1 return notint_cases zz1 with
  | Eop (Ointconst n) Enil => notint_case1 n
  | Eop Oand (t1:::t2:::Enil) => notint_case2 t1 t2
  | Eop Oor (t1:::t2:::Enil) => notint_case3 t1 t2
  | Eop Oxor (t1:::t2:::Enil) => notint_case4 t1 t2
  | e => notint_default e
  end.

Definition notint (e: expr) :=
  match notint_match e with
  | notint_case1 n => (* Eop (Ointconst n) Enil *) 
      Eop (Ointconst (Int.not n)) Enil
  | notint_case2 t1 t2 => (* Eop Oand (t1:::t2:::Enil) *) 
      Eop Onand (t1:::t2:::Enil)
  | notint_case3 t1 t2 => (* Eop Oor (t1:::t2:::Enil) *) 
      Eop Onor (t1:::t2:::Enil)
  | notint_case4 t1 t2 => (* Eop Oxor (t1:::t2:::Enil) *) 
      Eop Onxor (t1:::t2:::Enil)
  | notint_default e =>
      Elet e (Eop Onor (Eletvar O ::: Eletvar O ::: Enil))
  end.


(** ** Boolean negation *)

Definition notbool_base (e: expr) :=
  Eop (Ocmp (Ccompuimm Ceq Int.zero)) (e ::: Enil).

Fixpoint notbool (e: expr) {struct e} : expr :=
  match e with
  | Eop (Ointconst n) Enil =>
      Eop (Ointconst (if Int.eq n Int.zero then Int.one else Int.zero)) Enil
  | Eop (Ocmp cond) args =>
      Eop (Ocmp (negate_condition cond)) args
  | Econdition e1 e2 e3 =>
      Econdition e1 (notbool e2) (notbool e3)
  | _ =>
      notbool_base e
  end.

(** ** Integer addition and pointer addition *)

(** Original definition:
<<
Nondetfunction addimm (n: int) (e: expr) :=
  if Int.eq n Int.zero then e else
  match e with
  | Eop (Ointconst m) Enil       => Eop (Ointconst(Int.add n m)) Enil
  | Eop (Oaddrsymbol s m) Enil   => Eop (Oaddrsymbol s (Int.add n m)) Enil
  | Eop (Oaddrstack m) Enil      => Eop (Oaddrstack (Int.add n m)) Enil
  | Eop (Oaddimm m) (t ::: Enil) => Eop (Oaddimm(Int.add n m)) (t ::: Enil)
  | _                            => Eop (Oaddimm n) (e ::: Enil)
  end.
>>
*)

Inductive addimm_cases: forall (e: expr), Type :=
  | addimm_case1: forall m, addimm_cases (Eop (Ointconst m) Enil)
  | addimm_case2: forall s m, addimm_cases (Eop (Oaddrsymbol s m) Enil)
  | addimm_case3: forall m, addimm_cases (Eop (Oaddrstack m) Enil)
  | addimm_case4: forall m t, addimm_cases (Eop (Oaddimm m) (t ::: Enil))
  | addimm_default: forall (e: expr), addimm_cases e.

Definition addimm_match (e: expr) :=
  match e as zz1 return addimm_cases zz1 with
  | Eop (Ointconst m) Enil => addimm_case1 m
  | Eop (Oaddrsymbol s m) Enil => addimm_case2 s m
  | Eop (Oaddrstack m) Enil => addimm_case3 m
  | Eop (Oaddimm m) (t ::: Enil) => addimm_case4 m t
  | e => addimm_default e
  end.

Definition addimm (n: int) (e: expr) :=
 if Int.eq n Int.zero then e else match addimm_match e with
  | addimm_case1 m => (* Eop (Ointconst m) Enil *) 
      Eop (Ointconst(Int.add n m)) Enil
  | addimm_case2 s m => (* Eop (Oaddrsymbol s m) Enil *) 
      Eop (Oaddrsymbol s (Int.add n m)) Enil
  | addimm_case3 m => (* Eop (Oaddrstack m) Enil *) 
      Eop (Oaddrstack (Int.add n m)) Enil
  | addimm_case4 m t => (* Eop (Oaddimm m) (t ::: Enil) *) 
      Eop (Oaddimm(Int.add n m)) (t ::: Enil)
  | addimm_default e =>
      Eop (Oaddimm n) (e ::: Enil)
  end.


(** Original definition:
<<
Nondetfunction add (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 =>
      addimm n1 t2
  | Eop (Oaddimm n1) (t1:::Enil), Eop (Oaddimm n2) (t2:::Enil) =>
      addimm (Int.add n1 n2) (Eop Oadd (t1:::t2:::Enil))
  | Eop (Oaddimm n1) (t1:::Enil), t2 =>
      addimm n1 (Eop Oadd (t1:::t2:::Enil))
  | Eop (Oaddrsymbol s n1) Enil, Eop (Oaddimm n2) (t2:::Enil) =>
      Eop Oadd (Eop (Oaddrsymbol s (Int.add n1 n2)) Enil ::: t2 ::: Enil)
  | Eop (Oaddrstack n1) Enil, Eop (Oaddimm n2) (t2:::Enil) =>
      Eop Oadd (Eop (Oaddrstack (Int.add n1 n2)) Enil ::: t2 ::: Enil)
  | t1, Eop (Ointconst n2) Enil =>
      addimm n2 t1
  | t1, Eop (Oaddimm n2) (t2:::Enil) =>
      addimm n2 (Eop Oadd (t1:::t2:::Enil))
  | _, _ =>
      Eop Oadd (e1:::e2:::Enil)
  end.
>>
*)

Inductive add_cases: forall (e1: expr) (e2: expr), Type :=
  | add_case1: forall n1 t2, add_cases (Eop (Ointconst n1) Enil) (t2)
  | add_case2: forall n1 t1 n2 t2, add_cases (Eop (Oaddimm n1) (t1:::Enil)) (Eop (Oaddimm n2) (t2:::Enil))
  | add_case3: forall n1 t1 t2, add_cases (Eop (Oaddimm n1) (t1:::Enil)) (t2)
  | add_case4: forall s n1 n2 t2, add_cases (Eop (Oaddrsymbol s n1) Enil) (Eop (Oaddimm n2) (t2:::Enil))
  | add_case5: forall n1 n2 t2, add_cases (Eop (Oaddrstack n1) Enil) (Eop (Oaddimm n2) (t2:::Enil))
  | add_case6: forall t1 n2, add_cases (t1) (Eop (Ointconst n2) Enil)
  | add_case7: forall t1 n2 t2, add_cases (t1) (Eop (Oaddimm n2) (t2:::Enil))
  | add_default: forall (e1: expr) (e2: expr), add_cases e1 e2.

Definition add_match (e1: expr) (e2: expr) :=
  match e1 as zz1, e2 as zz2 return add_cases zz1 zz2 with
  | Eop (Ointconst n1) Enil, t2 => add_case1 n1 t2
  | Eop (Oaddimm n1) (t1:::Enil), Eop (Oaddimm n2) (t2:::Enil) => add_case2 n1 t1 n2 t2
  | Eop (Oaddimm n1) (t1:::Enil), t2 => add_case3 n1 t1 t2
  | Eop (Oaddrsymbol s n1) Enil, Eop (Oaddimm n2) (t2:::Enil) => add_case4 s n1 n2 t2
  | Eop (Oaddrstack n1) Enil, Eop (Oaddimm n2) (t2:::Enil) => add_case5 n1 n2 t2
  | t1, Eop (Ointconst n2) Enil => add_case6 t1 n2
  | t1, Eop (Oaddimm n2) (t2:::Enil) => add_case7 t1 n2 t2
  | e1, e2 => add_default e1 e2
  end.

Definition add (e1: expr) (e2: expr) :=
  match add_match e1 e2 with
  | add_case1 n1 t2 => (* Eop (Ointconst n1) Enil, t2 *) 
      addimm n1 t2
  | add_case2 n1 t1 n2 t2 => (* Eop (Oaddimm n1) (t1:::Enil), Eop (Oaddimm n2) (t2:::Enil) *) 
      addimm (Int.add n1 n2) (Eop Oadd (t1:::t2:::Enil))
  | add_case3 n1 t1 t2 => (* Eop (Oaddimm n1) (t1:::Enil), t2 *) 
      addimm n1 (Eop Oadd (t1:::t2:::Enil))
  | add_case4 s n1 n2 t2 => (* Eop (Oaddrsymbol s n1) Enil, Eop (Oaddimm n2) (t2:::Enil) *) 
      Eop Oadd (Eop (Oaddrsymbol s (Int.add n1 n2)) Enil ::: t2 ::: Enil)
  | add_case5 n1 n2 t2 => (* Eop (Oaddrstack n1) Enil, Eop (Oaddimm n2) (t2:::Enil) *) 
      Eop Oadd (Eop (Oaddrstack (Int.add n1 n2)) Enil ::: t2 ::: Enil)
  | add_case6 t1 n2 => (* t1, Eop (Ointconst n2) Enil *) 
      addimm n2 t1
  | add_case7 t1 n2 t2 => (* t1, Eop (Oaddimm n2) (t2:::Enil) *) 
      addimm n2 (Eop Oadd (t1:::t2:::Enil))
  | add_default e1 e2 =>
      Eop Oadd (e1:::e2:::Enil)
  end.


(** ** Integer and pointer subtraction *)

(** Original definition:
<<
Nondetfunction sub (e1: expr) (e2: expr) :=
  match e1, e2 with
  | t1, Eop (Ointconst n2) Enil =>
      addimm (Int.neg n2) t1
  | Eop (Oaddimm n1) (t1:::Enil), Eop (Oaddimm n2) (t2:::Enil) =>
      addimm (Int.sub n1 n2) (Eop Osub (t1:::t2:::Enil))
  | Eop (Oaddimm n1) (t1:::Enil), t2 =>
      addimm n1 (Eop Osub (t1:::t2:::Enil))
  | t1, Eop (Oaddimm n2) (t2:::Enil) =>
      addimm (Int.neg n2) (Eop Osub (t1:::t2:::Enil))
  | _, _ =>
      Eop Osub (e1:::e2:::Enil)
  end.
>>
*)

Inductive sub_cases: forall (e1: expr) (e2: expr), Type :=
  | sub_case1: forall t1 n2, sub_cases (t1) (Eop (Ointconst n2) Enil)
  | sub_case2: forall n1 t1 n2 t2, sub_cases (Eop (Oaddimm n1) (t1:::Enil)) (Eop (Oaddimm n2) (t2:::Enil))
  | sub_case3: forall n1 t1 t2, sub_cases (Eop (Oaddimm n1) (t1:::Enil)) (t2)
  | sub_case4: forall t1 n2 t2, sub_cases (t1) (Eop (Oaddimm n2) (t2:::Enil))
  | sub_default: forall (e1: expr) (e2: expr), sub_cases e1 e2.

Definition sub_match (e1: expr) (e2: expr) :=
  match e1 as zz1, e2 as zz2 return sub_cases zz1 zz2 with
  | t1, Eop (Ointconst n2) Enil => sub_case1 t1 n2
  | Eop (Oaddimm n1) (t1:::Enil), Eop (Oaddimm n2) (t2:::Enil) => sub_case2 n1 t1 n2 t2
  | Eop (Oaddimm n1) (t1:::Enil), t2 => sub_case3 n1 t1 t2
  | t1, Eop (Oaddimm n2) (t2:::Enil) => sub_case4 t1 n2 t2
  | e1, e2 => sub_default e1 e2
  end.

Definition sub (e1: expr) (e2: expr) :=
  match sub_match e1 e2 with
  | sub_case1 t1 n2 => (* t1, Eop (Ointconst n2) Enil *) 
      addimm (Int.neg n2) t1
  | sub_case2 n1 t1 n2 t2 => (* Eop (Oaddimm n1) (t1:::Enil), Eop (Oaddimm n2) (t2:::Enil) *) 
      addimm (Int.sub n1 n2) (Eop Osub (t1:::t2:::Enil))
  | sub_case3 n1 t1 t2 => (* Eop (Oaddimm n1) (t1:::Enil), t2 *) 
      addimm n1 (Eop Osub (t1:::t2:::Enil))
  | sub_case4 t1 n2 t2 => (* t1, Eop (Oaddimm n2) (t2:::Enil) *) 
      addimm (Int.neg n2) (Eop Osub (t1:::t2:::Enil))
  | sub_default e1 e2 =>
      Eop Osub (e1:::e2:::Enil)
  end.


Definition negint (e: expr) := Eop (Osubimm Int.zero) (e ::: Enil).

(** ** Rotates and immediate shifts *)

(** Original definition:
<<
Nondetfunction rolm (e1: expr) (amount2: int) (mask2: int) :=
  match e1 with
  | Eop (Ointconst n1) Enil =>
      Eop (Ointconst(Int.and (Int.rol n1 amount2) mask2)) Enil
  | Eop (Orolm amount1 mask1) (t1:::Enil) =>
      Eop (Orolm (Int.modu (Int.add amount1 amount2) Int.iwordsize)
                 (Int.and (Int.rol mask1 amount2) mask2))
          (t1:::Enil)
  | _ =>
      Eop (Orolm amount2 mask2) (e1:::Enil)
  end.
>>
*)

Inductive rolm_cases: forall (e1: expr) , Type :=
  | rolm_case1: forall n1, rolm_cases (Eop (Ointconst n1) Enil)
  | rolm_case2: forall amount1 mask1 t1, rolm_cases (Eop (Orolm amount1 mask1) (t1:::Enil))
  | rolm_default: forall (e1: expr) , rolm_cases e1.

Definition rolm_match (e1: expr)  :=
  match e1 as zz1 return rolm_cases zz1 with
  | Eop (Ointconst n1) Enil => rolm_case1 n1
  | Eop (Orolm amount1 mask1) (t1:::Enil) => rolm_case2 amount1 mask1 t1
  | e1 => rolm_default e1
  end.

Definition rolm (e1: expr) (amount2: int) (mask2: int) :=
  match rolm_match e1 with
  | rolm_case1 n1 => (* Eop (Ointconst n1) Enil *) 
      Eop (Ointconst(Int.and (Int.rol n1 amount2) mask2)) Enil
  | rolm_case2 amount1 mask1 t1 => (* Eop (Orolm amount1 mask1) (t1:::Enil) *) 
      Eop (Orolm (Int.modu (Int.add amount1 amount2) Int.iwordsize) (Int.and (Int.rol mask1 amount2) mask2)) (t1:::Enil)
  | rolm_default e1 =>
      Eop (Orolm amount2 mask2) (e1:::Enil)
  end.


Definition shlimm (e1: expr) (n2: int) :=
  if Int.eq n2 Int.zero then
    e1
  else if Int.ltu n2 Int.iwordsize then
    rolm e1 n2 (Int.shl Int.mone n2)
  else
    Eop Oshl (e1:::Eop (Ointconst n2) Enil:::Enil).

Definition shrimm (e1: expr) (n2: int) :=
  if Int.eq n2 Int.zero then
    e1
  else
    Eop (Oshrimm n2) (e1:::Enil).

Definition shruimm (e1: expr) (n2: int) :=
  if Int.eq n2 Int.zero then
    e1
  else if Int.ltu n2 Int.iwordsize then
    rolm e1 (Int.sub Int.iwordsize n2) (Int.shru Int.mone n2)
  else
    Eop Oshru (e1:::Eop (Ointconst n2) Enil:::Enil).

(** ** Integer multiply *)

Definition mulimm_base (n1: int) (e2: expr) :=
  match Int.one_bits n1 with
  | i :: nil =>
      shlimm e2 i
  | i :: j :: nil =>
      Elet e2
        (Eop Oadd (shlimm (Eletvar 0) i :::
                   shlimm (Eletvar 0) j ::: Enil))
  | _ =>
      Eop (Omulimm n1) (e2:::Enil)
  end.

(** Original definition:
<<
Nondetfunction mulimm (n1: int) (e2: expr) :=
  if Int.eq n1 Int.zero then Eop (Ointconst Int.zero) Enil
  else if Int.eq n1 Int.one then e2
  else match e2 with
  | Eop (Ointconst n2) Enil => Eop (Ointconst(Int.mul n1 n2)) Enil
  | Eop (Oaddimm n2) (t2:::Enil) => addimm (Int.mul n1 n2) (mulimm_base n1 t2)
  | _ => mulimm_base n1 e2
  end.
>>
*)

Inductive mulimm_cases: forall (e2: expr), Type :=
  | mulimm_case1: forall n2, mulimm_cases (Eop (Ointconst n2) Enil)
  | mulimm_case2: forall n2 t2, mulimm_cases (Eop (Oaddimm n2) (t2:::Enil))
  | mulimm_default: forall (e2: expr), mulimm_cases e2.

Definition mulimm_match (e2: expr) :=
  match e2 as zz1 return mulimm_cases zz1 with
  | Eop (Ointconst n2) Enil => mulimm_case1 n2
  | Eop (Oaddimm n2) (t2:::Enil) => mulimm_case2 n2 t2
  | e2 => mulimm_default e2
  end.

Definition mulimm (n1: int) (e2: expr) :=
 if Int.eq n1 Int.zero then Eop (Ointconst Int.zero) Enil else if Int.eq n1 Int.one then e2 else match mulimm_match e2 with
  | mulimm_case1 n2 => (* Eop (Ointconst n2) Enil *) 
      Eop (Ointconst(Int.mul n1 n2)) Enil
  | mulimm_case2 n2 t2 => (* Eop (Oaddimm n2) (t2:::Enil) *) 
      addimm (Int.mul n1 n2) (mulimm_base n1 t2)
  | mulimm_default e2 =>
      mulimm_base n1 e2
  end.


(** Original definition:
<<
Nondetfunction mul (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 => mulimm n1 t2
  | t1, Eop (Ointconst n2) Enil => mulimm n2 t1
  | _, _ => Eop Omul (e1:::e2:::Enil)
  end.
>>
*)

Inductive mul_cases: forall (e1: expr) (e2: expr), Type :=
  | mul_case1: forall n1 t2, mul_cases (Eop (Ointconst n1) Enil) (t2)
  | mul_case2: forall t1 n2, mul_cases (t1) (Eop (Ointconst n2) Enil)
  | mul_default: forall (e1: expr) (e2: expr), mul_cases e1 e2.

Definition mul_match (e1: expr) (e2: expr) :=
  match e1 as zz1, e2 as zz2 return mul_cases zz1 zz2 with
  | Eop (Ointconst n1) Enil, t2 => mul_case1 n1 t2
  | t1, Eop (Ointconst n2) Enil => mul_case2 t1 n2
  | e1, e2 => mul_default e1 e2
  end.

Definition mul (e1: expr) (e2: expr) :=
  match mul_match e1 e2 with
  | mul_case1 n1 t2 => (* Eop (Ointconst n1) Enil, t2 *) 
      mulimm n1 t2
  | mul_case2 t1 n2 => (* t1, Eop (Ointconst n2) Enil *) 
      mulimm n2 t1
  | mul_default e1 e2 =>
      Eop Omul (e1:::e2:::Enil)
  end.


(** ** Bitwise and, or, xor *)

Definition andimm (n1: int) (e2: expr) := rolm e2 Int.zero n1.

(** Original definition:
<<
Nondetfunction and (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 => andimm n1 t2
  | t1, Eop (Ointconst n2) Enil => andimm n2 t1
  | _, _ => Eop Oand (e1:::e2:::Enil)
  end.
>>
*)

Inductive and_cases: forall (e1: expr) (e2: expr), Type :=
  | and_case1: forall n1 t2, and_cases (Eop (Ointconst n1) Enil) (t2)
  | and_case2: forall t1 n2, and_cases (t1) (Eop (Ointconst n2) Enil)
  | and_default: forall (e1: expr) (e2: expr), and_cases e1 e2.

Definition and_match (e1: expr) (e2: expr) :=
  match e1 as zz1, e2 as zz2 return and_cases zz1 zz2 with
  | Eop (Ointconst n1) Enil, t2 => and_case1 n1 t2
  | t1, Eop (Ointconst n2) Enil => and_case2 t1 n2
  | e1, e2 => and_default e1 e2
  end.

Definition and (e1: expr) (e2: expr) :=
  match and_match e1 e2 with
  | and_case1 n1 t2 => (* Eop (Ointconst n1) Enil, t2 *) 
      andimm n1 t2
  | and_case2 t1 n2 => (* t1, Eop (Ointconst n2) Enil *) 
      andimm n2 t1
  | and_default e1 e2 =>
      Eop Oand (e1:::e2:::Enil)
  end.


Definition same_expr_pure (e1 e2: expr) :=
  match e1, e2 with
  | Evar v1, Evar v2 => if ident_eq v1 v2 then true else false
  | _, _ => false
  end.

(** Original definition:
<<
Nondetfunction orimm (n1: int) (e2: expr) :=
  match e2 with
  | Eop (Ointconst n2) Enil => Eop (Ointconst (Int.or n1 n2)) Enil
  | Eop (Oorimm n2) (t2:::Enil) => Eop (Oorimm (Int.or n1 n2)) (t2:::Enil)
  | _ => Eop (Oorimm n1) (e2:::Enil)
  end.
>>
*)

Inductive orimm_cases: forall (e2: expr), Type :=
  | orimm_case1: forall n2, orimm_cases (Eop (Ointconst n2) Enil)
  | orimm_case2: forall n2 t2, orimm_cases (Eop (Oorimm n2) (t2:::Enil))
  | orimm_default: forall (e2: expr), orimm_cases e2.

Definition orimm_match (e2: expr) :=
  match e2 as zz1 return orimm_cases zz1 with
  | Eop (Ointconst n2) Enil => orimm_case1 n2
  | Eop (Oorimm n2) (t2:::Enil) => orimm_case2 n2 t2
  | e2 => orimm_default e2
  end.

Definition orimm (n1: int) (e2: expr) :=
  match orimm_match e2 with
  | orimm_case1 n2 => (* Eop (Ointconst n2) Enil *) 
      Eop (Ointconst (Int.or n1 n2)) Enil
  | orimm_case2 n2 t2 => (* Eop (Oorimm n2) (t2:::Enil) *) 
      Eop (Oorimm (Int.or n1 n2)) (t2:::Enil)
  | orimm_default e2 =>
      Eop (Oorimm n1) (e2:::Enil)
  end.


(** Original definition:
<<
Nondetfunction or (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop (Orolm amount1  mask1) (t1:::Enil), Eop (Orolm amount2 mask2) (t2:::Enil) =>
      if Int.eq amount1 amount2
      && same_expr_pure t1 t2 then
        Eop (Orolm amount1 (Int.or mask1 mask2)) (t1:::Enil)
      else if Int.eq amount1 Int.zero
           && Int.eq mask1 (Int.not mask2) then
        Eop (Oroli amount2 mask2) (t1:::t2:::Enil)
      else if Int.eq amount2 Int.zero
           && Int.eq mask2 (Int.not mask1) then
        Eop (Oroli amount1 mask1) (t2:::t1:::Enil)
      else
        Eop Oor (e1:::e2:::Enil)
  | Eop (Ointconst n1) Enil, t2 => orimm n1 t2
  | t1, Eop (Ointconst n2) Enil => orimm n2 t1
  | _, _ => Eop Oor (e1:::e2:::Enil)
  end.
>>
*)

Inductive or_cases: forall (e1: expr) (e2: expr), Type :=
  | or_case1: forall amount1 mask1 t1 amount2 mask2 t2, or_cases (Eop (Orolm amount1 mask1) (t1:::Enil)) (Eop (Orolm amount2 mask2) (t2:::Enil))
  | or_case2: forall n1 t2, or_cases (Eop (Ointconst n1) Enil) (t2)
  | or_case3: forall t1 n2, or_cases (t1) (Eop (Ointconst n2) Enil)
  | or_default: forall (e1: expr) (e2: expr), or_cases e1 e2.

Definition or_match (e1: expr) (e2: expr) :=
  match e1 as zz1, e2 as zz2 return or_cases zz1 zz2 with
  | Eop (Orolm amount1 mask1) (t1:::Enil), Eop (Orolm amount2 mask2) (t2:::Enil) => or_case1 amount1 mask1 t1 amount2 mask2 t2
  | Eop (Ointconst n1) Enil, t2 => or_case2 n1 t2
  | t1, Eop (Ointconst n2) Enil => or_case3 t1 n2
  | e1, e2 => or_default e1 e2
  end.

Definition or (e1: expr) (e2: expr) :=
  match or_match e1 e2 with
  | or_case1 amount1 mask1 t1 amount2 mask2 t2 => (* Eop (Orolm amount1 mask1) (t1:::Enil), Eop (Orolm amount2 mask2) (t2:::Enil) *) 
      if Int.eq amount1 amount2 && same_expr_pure t1 t2 then Eop (Orolm amount1 (Int.or mask1 mask2)) (t1:::Enil) else if Int.eq amount1 Int.zero && Int.eq mask1 (Int.not mask2) then Eop (Oroli amount2 mask2) (t1:::t2:::Enil) else if Int.eq amount2 Int.zero && Int.eq mask2 (Int.not mask1) then Eop (Oroli amount1 mask1) (t2:::t1:::Enil) else Eop Oor (e1:::e2:::Enil)
  | or_case2 n1 t2 => (* Eop (Ointconst n1) Enil, t2 *) 
      orimm n1 t2
  | or_case3 t1 n2 => (* t1, Eop (Ointconst n2) Enil *) 
      orimm n2 t1
  | or_default e1 e2 =>
      Eop Oor (e1:::e2:::Enil)
  end.


(** Original definition:
<<
Nondetfunction xorimm (n1: int) (e2: expr) :=
  match e2 with
  | Eop (Ointconst n2) Enil => Eop (Ointconst (Int.xor n1 n2)) Enil
  | Eop (Oxorimm n2) (t2:::Enil) => Eop (Oxorimm (Int.xor n1 n2)) (t2:::Enil)
  | _ => Eop (Oxorimm n1) (e2:::Enil)
  end.
>>
*)

Inductive xorimm_cases: forall (e2: expr), Type :=
  | xorimm_case1: forall n2, xorimm_cases (Eop (Ointconst n2) Enil)
  | xorimm_case2: forall n2 t2, xorimm_cases (Eop (Oxorimm n2) (t2:::Enil))
  | xorimm_default: forall (e2: expr), xorimm_cases e2.

Definition xorimm_match (e2: expr) :=
  match e2 as zz1 return xorimm_cases zz1 with
  | Eop (Ointconst n2) Enil => xorimm_case1 n2
  | Eop (Oxorimm n2) (t2:::Enil) => xorimm_case2 n2 t2
  | e2 => xorimm_default e2
  end.

Definition xorimm (n1: int) (e2: expr) :=
  match xorimm_match e2 with
  | xorimm_case1 n2 => (* Eop (Ointconst n2) Enil *) 
      Eop (Ointconst (Int.xor n1 n2)) Enil
  | xorimm_case2 n2 t2 => (* Eop (Oxorimm n2) (t2:::Enil) *) 
      Eop (Oxorimm (Int.xor n1 n2)) (t2:::Enil)
  | xorimm_default e2 =>
      Eop (Oxorimm n1) (e2:::Enil)
  end.


(** Original definition:
<<
Nondetfunction xor (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 => xorimm n1 t2
  | t1, Eop (Ointconst n2) Enil => xorimm n2 t1
  | _, _ => Eop Oxor (e1:::e2:::Enil)
  end.
>>
*)

Inductive xor_cases: forall (e1: expr) (e2: expr), Type :=
  | xor_case1: forall n1 t2, xor_cases (Eop (Ointconst n1) Enil) (t2)
  | xor_case2: forall t1 n2, xor_cases (t1) (Eop (Ointconst n2) Enil)
  | xor_default: forall (e1: expr) (e2: expr), xor_cases e1 e2.

Definition xor_match (e1: expr) (e2: expr) :=
  match e1 as zz1, e2 as zz2 return xor_cases zz1 zz2 with
  | Eop (Ointconst n1) Enil, t2 => xor_case1 n1 t2
  | t1, Eop (Ointconst n2) Enil => xor_case2 t1 n2
  | e1, e2 => xor_default e1 e2
  end.

Definition xor (e1: expr) (e2: expr) :=
  match xor_match e1 e2 with
  | xor_case1 n1 t2 => (* Eop (Ointconst n1) Enil, t2 *) 
      xorimm n1 t2
  | xor_case2 t1 n2 => (* t1, Eop (Ointconst n2) Enil *) 
      xorimm n2 t1
  | xor_default e1 e2 =>
      Eop Oxor (e1:::e2:::Enil)
  end.


(** ** Integer division and modulus *)

Definition divs (e1: expr) (e2: expr) := Eop Odiv (e1:::e2:::Enil).

Definition mod_aux (divop: operation) (e1 e2: expr) :=
  Elet e1
    (Elet (lift e2)
      (Eop Osub (Eletvar 1 :::
                 Eop Omul (Eop divop (Eletvar 1 ::: Eletvar 0 ::: Enil) :::
                           Eletvar 0 :::
                           Enil) :::
                 Enil))).

Definition mods := mod_aux Odiv.

Definition divuimm (e: expr) (n: int) :=
  match Int.is_power2 n with
  | Some l => shruimm e l
  | None   => Eop Odivu (e ::: Eop (Ointconst n) Enil ::: Enil)
  end.

(** Original definition:
<<
Nondetfunction divu (e1: expr) (e2: expr) :=
  match e2 with
  | Eop (Ointconst n2) Enil => divuimm e1 n2
  | _ => Eop Odivu (e1:::e2:::Enil)
  end.
>>
*)

Inductive divu_cases: forall (e2: expr), Type :=
  | divu_case1: forall n2, divu_cases (Eop (Ointconst n2) Enil)
  | divu_default: forall (e2: expr), divu_cases e2.

Definition divu_match (e2: expr) :=
  match e2 as zz1 return divu_cases zz1 with
  | Eop (Ointconst n2) Enil => divu_case1 n2
  | e2 => divu_default e2
  end.

Definition divu (e1: expr) (e2: expr) :=
  match divu_match e2 with
  | divu_case1 n2 => (* Eop (Ointconst n2) Enil *) 
      divuimm e1 n2
  | divu_default e2 =>
      Eop Odivu (e1:::e2:::Enil)
  end.


Definition moduimm (e: expr) (n: int) :=
  match Int.is_power2 n with
  | Some l => andimm (Int.sub n Int.one) e
  | None   => mod_aux Odivu e (Eop (Ointconst n) Enil)
  end.

(** Original definition:
<<
Nondetfunction modu (e1: expr) (e2: expr) :=
  match e2 with
  | Eop (Ointconst n2) Enil => moduimm e1 n2
  | _ => mod_aux Odivu e1 e2
  end.
>>
*)

Inductive modu_cases: forall (e2: expr), Type :=
  | modu_case1: forall n2, modu_cases (Eop (Ointconst n2) Enil)
  | modu_default: forall (e2: expr), modu_cases e2.

Definition modu_match (e2: expr) :=
  match e2 as zz1 return modu_cases zz1 with
  | Eop (Ointconst n2) Enil => modu_case1 n2
  | e2 => modu_default e2
  end.

Definition modu (e1: expr) (e2: expr) :=
  match modu_match e2 with
  | modu_case1 n2 => (* Eop (Ointconst n2) Enil *) 
      moduimm e1 n2
  | modu_default e2 =>
      mod_aux Odivu e1 e2
  end.


(** ** General shifts *)

(** Original definition:
<<
Nondetfunction shl (e1: expr) (e2: expr) :=
  match e2 with
  | Eop (Ointconst n2) Enil => shlimm e1 n2
  | _ => Eop Oshl (e1:::e2:::Enil)
  end.
>>
*)

Inductive shl_cases: forall (e2: expr), Type :=
  | shl_case1: forall n2, shl_cases (Eop (Ointconst n2) Enil)
  | shl_default: forall (e2: expr), shl_cases e2.

Definition shl_match (e2: expr) :=
  match e2 as zz1 return shl_cases zz1 with
  | Eop (Ointconst n2) Enil => shl_case1 n2
  | e2 => shl_default e2
  end.

Definition shl (e1: expr) (e2: expr) :=
  match shl_match e2 with
  | shl_case1 n2 => (* Eop (Ointconst n2) Enil *) 
      shlimm e1 n2
  | shl_default e2 =>
      Eop Oshl (e1:::e2:::Enil)
  end.


(** Original definition:
<<
Nondetfunction shr (e1: expr) (e2: expr) :=
  match e2 with
  | Eop (Ointconst n2) Enil => shrimm e1 n2
  | _ => Eop Oshr (e1:::e2:::Enil)
  end.
>>
*)

Inductive shr_cases: forall (e2: expr), Type :=
  | shr_case1: forall n2, shr_cases (Eop (Ointconst n2) Enil)
  | shr_default: forall (e2: expr), shr_cases e2.

Definition shr_match (e2: expr) :=
  match e2 as zz1 return shr_cases zz1 with
  | Eop (Ointconst n2) Enil => shr_case1 n2
  | e2 => shr_default e2
  end.

Definition shr (e1: expr) (e2: expr) :=
  match shr_match e2 with
  | shr_case1 n2 => (* Eop (Ointconst n2) Enil *) 
      shrimm e1 n2
  | shr_default e2 =>
      Eop Oshr (e1:::e2:::Enil)
  end.


(** Original definition:
<<
Nondetfunction shru (e1: expr) (e2: expr) :=
  match e2 with
  | Eop (Ointconst n2) Enil => shruimm e1 n2
  | _ => Eop Oshru (e1:::e2:::Enil)
  end.
>>
*)

Inductive shru_cases: forall (e2: expr), Type :=
  | shru_case1: forall n2, shru_cases (Eop (Ointconst n2) Enil)
  | shru_default: forall (e2: expr), shru_cases e2.

Definition shru_match (e2: expr) :=
  match e2 as zz1 return shru_cases zz1 with
  | Eop (Ointconst n2) Enil => shru_case1 n2
  | e2 => shru_default e2
  end.

Definition shru (e1: expr) (e2: expr) :=
  match shru_match e2 with
  | shru_case1 n2 => (* Eop (Ointconst n2) Enil *) 
      shruimm e1 n2
  | shru_default e2 =>
      Eop Oshru (e1:::e2:::Enil)
  end.


(** ** Floating-point arithmetic *)

Definition negf (e: expr) :=  Eop Onegf (e ::: Enil).
Definition absf (e: expr) :=  Eop Oabsf (e ::: Enil).

Parameter use_fused_mul : unit -> bool.

(** Original definition:
<<
Nondetfunction addf (e1: expr) (e2: expr) :=
  if negb(use_fused_mul tt) then Eop Oaddf (e1:::e2:::Enil) else 
  match e1, e2 with
  | Eop Omulf (t1:::t2:::Enil), t3 => Eop Omuladdf (t1:::t2:::t3:::Enil)
  | t1, Eop Omulf (t2:::t3:::Enil) => Eop Omuladdf (t2:::t3:::t1:::Enil)
  | _, _ => Eop Oaddf (e1:::e2:::Enil)
  end.
>>
*)

Inductive addf_cases: forall (e1: expr) (e2: expr), Type :=
  | addf_case1: forall t1 t2 t3, addf_cases (Eop Omulf (t1:::t2:::Enil)) (t3)
  | addf_case2: forall t1 t2 t3, addf_cases (t1) (Eop Omulf (t2:::t3:::Enil))
  | addf_default: forall (e1: expr) (e2: expr), addf_cases e1 e2.

Definition addf_match (e1: expr) (e2: expr) :=
  match e1 as zz1, e2 as zz2 return addf_cases zz1 zz2 with
  | Eop Omulf (t1:::t2:::Enil), t3 => addf_case1 t1 t2 t3
  | t1, Eop Omulf (t2:::t3:::Enil) => addf_case2 t1 t2 t3
  | e1, e2 => addf_default e1 e2
  end.

Definition addf (e1: expr) (e2: expr) :=
 if negb(use_fused_mul tt) then Eop Oaddf (e1:::e2:::Enil) else match addf_match e1 e2 with
  | addf_case1 t1 t2 t3 => (* Eop Omulf (t1:::t2:::Enil), t3 *) 
      Eop Omuladdf (t1:::t2:::t3:::Enil)
  | addf_case2 t1 t2 t3 => (* t1, Eop Omulf (t2:::t3:::Enil) *) 
      Eop Omuladdf (t2:::t3:::t1:::Enil)
  | addf_default e1 e2 =>
      Eop Oaddf (e1:::e2:::Enil)
  end.


(** Original definition:
<<
Nondetfunction subf (e1: expr) (e2: expr) :=
  if negb(use_fused_mul tt) then Eop Osubf (e1:::e2:::Enil) else 
  match e1 with
  | Eop Omulf (t1:::t2:::Enil) => Eop Omulsubf (t1:::t2:::e2:::Enil)
  | _ => Eop Osubf (e1:::e2:::Enil)
  end.
>>
*)

Inductive subf_cases: forall (e1: expr) , Type :=
  | subf_case1: forall t1 t2, subf_cases (Eop Omulf (t1:::t2:::Enil))
  | subf_default: forall (e1: expr) , subf_cases e1.

Definition subf_match (e1: expr)  :=
  match e1 as zz1 return subf_cases zz1 with
  | Eop Omulf (t1:::t2:::Enil) => subf_case1 t1 t2
  | e1 => subf_default e1
  end.

Definition subf (e1: expr) (e2: expr) :=
 if negb(use_fused_mul tt) then Eop Osubf (e1:::e2:::Enil) else match subf_match e1 with
  | subf_case1 t1 t2 => (* Eop Omulf (t1:::t2:::Enil) *) 
      Eop Omulsubf (t1:::t2:::e2:::Enil)
  | subf_default e1 =>
      Eop Osubf (e1:::e2:::Enil)
  end.


Definition mulf (e1 e2: expr) :=  Eop Omulf (e1 ::: e2 ::: Enil).
Definition divf (e1 e2: expr) :=  Eop Odivf (e1 ::: e2 ::: Enil).

(** ** Comparisons *)

(** Original definition:
<<
Nondetfunction comp (c: comparison) (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 =>
      Eop (Ocmp (Ccompimm (swap_comparison c) n1)) (t2 ::: Enil)
  | t1, Eop (Ointconst n2) Enil =>
      Eop (Ocmp (Ccompimm c n2)) (t1 ::: Enil)
  | _, _ =>
      Eop (Ocmp (Ccomp c)) (e1 ::: e2 ::: Enil)
  end.
>>
*)

Inductive comp_cases: forall (e1: expr) (e2: expr), Type :=
  | comp_case1: forall n1 t2, comp_cases (Eop (Ointconst n1) Enil) (t2)
  | comp_case2: forall t1 n2, comp_cases (t1) (Eop (Ointconst n2) Enil)
  | comp_default: forall (e1: expr) (e2: expr), comp_cases e1 e2.

Definition comp_match (e1: expr) (e2: expr) :=
  match e1 as zz1, e2 as zz2 return comp_cases zz1 zz2 with
  | Eop (Ointconst n1) Enil, t2 => comp_case1 n1 t2
  | t1, Eop (Ointconst n2) Enil => comp_case2 t1 n2
  | e1, e2 => comp_default e1 e2
  end.

Definition comp (c: comparison) (e1: expr) (e2: expr) :=
  match comp_match e1 e2 with
  | comp_case1 n1 t2 => (* Eop (Ointconst n1) Enil, t2 *) 
      Eop (Ocmp (Ccompimm (swap_comparison c) n1)) (t2 ::: Enil)
  | comp_case2 t1 n2 => (* t1, Eop (Ointconst n2) Enil *) 
      Eop (Ocmp (Ccompimm c n2)) (t1 ::: Enil)
  | comp_default e1 e2 =>
      Eop (Ocmp (Ccomp c)) (e1 ::: e2 ::: Enil)
  end.


(** Original definition:
<<
Nondetfunction compu (c: comparison) (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 =>
      Eop (Ocmp (Ccompuimm (swap_comparison c) n1)) (t2 ::: Enil)
  | t1, Eop (Ointconst n2) Enil =>
      Eop (Ocmp (Ccompuimm c n2)) (t1 ::: Enil)
  | _, _ =>
      Eop (Ocmp (Ccompu c)) (e1 ::: e2 ::: Enil)
  end.
>>
*)

Inductive compu_cases: forall (e1: expr) (e2: expr), Type :=
  | compu_case1: forall n1 t2, compu_cases (Eop (Ointconst n1) Enil) (t2)
  | compu_case2: forall t1 n2, compu_cases (t1) (Eop (Ointconst n2) Enil)
  | compu_default: forall (e1: expr) (e2: expr), compu_cases e1 e2.

Definition compu_match (e1: expr) (e2: expr) :=
  match e1 as zz1, e2 as zz2 return compu_cases zz1 zz2 with
  | Eop (Ointconst n1) Enil, t2 => compu_case1 n1 t2
  | t1, Eop (Ointconst n2) Enil => compu_case2 t1 n2
  | e1, e2 => compu_default e1 e2
  end.

Definition compu (c: comparison) (e1: expr) (e2: expr) :=
  match compu_match e1 e2 with
  | compu_case1 n1 t2 => (* Eop (Ointconst n1) Enil, t2 *) 
      Eop (Ocmp (Ccompuimm (swap_comparison c) n1)) (t2 ::: Enil)
  | compu_case2 t1 n2 => (* t1, Eop (Ointconst n2) Enil *) 
      Eop (Ocmp (Ccompuimm c n2)) (t1 ::: Enil)
  | compu_default e1 e2 =>
      Eop (Ocmp (Ccompu c)) (e1 ::: e2 ::: Enil)
  end.


Definition compf (c: comparison) (e1: expr) (e2: expr) :=
  Eop (Ocmp (Ccompf c)) (e1 ::: e2 ::: Enil).

(** ** Integer conversions *)

Definition cast8unsigned (e: expr) := andimm (Int.repr 255) e.
Definition cast8signed (e: expr) := Eop Ocast8signed (e ::: Enil).
Definition cast16unsigned (e: expr) := andimm (Int.repr 65535) e.
Definition cast16signed (e: expr) := Eop Ocast16signed (e ::: Enil).

(** ** Floating-point conversions *)

Definition intoffloat (e: expr) := Eop Ointoffloat (e ::: Enil).

Definition intuoffloat (e: expr) :=
  let f := Eop (Ofloatconst (Float.floatofintu Float.ox8000_0000)) Enil in
  Elet e
    (Econdition (CEcond (Ccompf Clt) (Eletvar O ::: f ::: Enil))
      (intoffloat (Eletvar O))
      (addimm Float.ox8000_0000 (intoffloat (subf (Eletvar O) f)))).

Definition floatofintu (e: expr) :=
  subf (Eop Ofloatofwords (Eop (Ointconst Float.ox4330_0000) Enil ::: e ::: Enil))
       (Eop (Ofloatconst (Float.from_words Float.ox4330_0000 Int.zero)) Enil).

Definition floatofint (e: expr) :=
  subf (Eop Ofloatofwords (Eop (Ointconst Float.ox4330_0000) Enil
                           ::: addimm Float.ox8000_0000 e ::: Enil))
       (Eop (Ofloatconst (Float.from_words Float.ox4330_0000 Float.ox8000_0000)) Enil).

Definition singleoffloat (e: expr) := Eop Osingleoffloat (e ::: Enil).

(** ** Recognition of addressing modes for load and store operations *)

(** Original definition:
<<
Nondetfunction addressing (chunk: memory_chunk) (e: expr) :=
  match e with
  | Eop (Oaddrsymbol s n) Enil => (Aglobal s n, Enil)
  | Eop (Oaddrstack n) Enil => (Ainstack n, Enil)
  | Eop Oadd (Eop (Oaddrsymbol s n) Enil ::: e2 ::: Enil) => (Abased s n, e2:::Enil)
  | Eop (Oaddimm n) (e1:::Enil) => (Aindexed n, e1:::Enil)
  | Eop Oadd (e1:::e2:::Enil) => (Aindexed2, e1:::e2:::Enil)
  | _ => (Aindexed Int.zero, e:::Enil)
  end.
>>
*)

Inductive addressing_cases: forall (e: expr), Type :=
  | addressing_case1: forall s n, addressing_cases (Eop (Oaddrsymbol s n) Enil)
  | addressing_case2: forall n, addressing_cases (Eop (Oaddrstack n) Enil)
  | addressing_case3: forall s n e2, addressing_cases (Eop Oadd (Eop (Oaddrsymbol s n) Enil ::: e2 ::: Enil))
  | addressing_case4: forall n e1, addressing_cases (Eop (Oaddimm n) (e1:::Enil))
  | addressing_case5: forall e1 e2, addressing_cases (Eop Oadd (e1:::e2:::Enil))
  | addressing_default: forall (e: expr), addressing_cases e.

Definition addressing_match (e: expr) :=
  match e as zz1 return addressing_cases zz1 with
  | Eop (Oaddrsymbol s n) Enil => addressing_case1 s n
  | Eop (Oaddrstack n) Enil => addressing_case2 n
  | Eop Oadd (Eop (Oaddrsymbol s n) Enil ::: e2 ::: Enil) => addressing_case3 s n e2
  | Eop (Oaddimm n) (e1:::Enil) => addressing_case4 n e1
  | Eop Oadd (e1:::e2:::Enil) => addressing_case5 e1 e2
  | e => addressing_default e
  end.

Definition addressing (chunk: memory_chunk) (e: expr) :=
  match addressing_match e with
  | addressing_case1 s n => (* Eop (Oaddrsymbol s n) Enil *) 
      (Aglobal s n, Enil)
  | addressing_case2 n => (* Eop (Oaddrstack n) Enil *) 
      (Ainstack n, Enil)
  | addressing_case3 s n e2 => (* Eop Oadd (Eop (Oaddrsymbol s n) Enil ::: e2 ::: Enil) *) 
      (Abased s n, e2:::Enil)
  | addressing_case4 n e1 => (* Eop (Oaddimm n) (e1:::Enil) *) 
      (Aindexed n, e1:::Enil)
  | addressing_case5 e1 e2 => (* Eop Oadd (e1:::e2:::Enil) *) 
      (Aindexed2, e1:::e2:::Enil)
  | addressing_default e =>
      (Aindexed Int.zero, e:::Enil)
  end.

