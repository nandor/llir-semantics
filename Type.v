(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import LLIR.Values.

Inductive ty_int: Type :=
  | I8
  | I16
  | I32
  | I64
  | I128
  .

Inductive ty_float: Type :=
  | F32
  | F64
  | F80
  .

Inductive ty : Type :=
  | TInt (i: ty_int)
  | TFloat (f: ty_float)
  .

Definition ptr_ty := TInt I64.
Definition syscall_ty := TInt I64.

Lemma type_dec:
  forall (t0: ty) (t1: ty),
    {t0 = t1} + {t0 <> t1}.
Proof.
  intros t0 t1.
  destruct t0; destruct t1; 
  try destruct i; try destruct i0;
  try destruct f; try destruct f0;
  match goal with
  | [ |- context [ ?a = ?b ] ] => left; reflexivity
  | [ |- _ ] => right; intros contra; inversion contra
  end.
Qed.

(* Returns the type of an integer constant. *)
Definition type_of_int (v: INT.t): ty :=
  match v with
  | INT.Int8 _ => TInt I8
  | INT.Int16 _ => TInt I16
  | INT.Int32 _ => TInt I32
  | INT.Int64 _ => TInt I64
  end.

(* Type of integers *)
Inductive TypeOfInt : INT.t -> ty -> Prop :=
  | ty_of_i8: forall (v: INT.I8.t), TypeOfInt (INT.Int8 v) (TInt I8)
  | ty_of_i16: forall (v: INT.I16.t), TypeOfInt (INT.Int16 v) (TInt I16)
  | ty_of_i32: forall (v: INT.I32.t), TypeOfInt (INT.Int32 v) (TInt I32)
  | ty_of_i64: forall (v: INT.I64.t), TypeOfInt (INT.Int64 v) (TInt I64)
  .

(* Decidability of TypeOfInt *)
Lemma TypeOfInt_dec:
  forall (v: INT.t) (t: ty),
    {TypeOfInt v t} + {~TypeOfInt v t}.
Proof.
  intros v t.
  destruct v; destruct t;
    try match goal with
    | [ |- context [ TFloat _ ]] => right; intros contra; inversion contra
    end;
    destruct i;
    try (left; constructor);
    right; intros contra;
    inversion contra.
Qed.

(* Predicate-Definition Equivalence *)
Lemma TypeOfInt_type_of_int:
  forall (v: INT.t) (t: ty),
    TypeOfInt v t <-> type_of_int v = t.
Proof.
  intros v t; split; intros H.
  - inversion H; constructor.
  - destruct v; simpl in H; subst; constructor.
Qed.
