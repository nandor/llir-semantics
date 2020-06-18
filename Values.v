(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.


Notation name := positive.

Notation node := positive.

Notation reg := positive.

Inductive bit : Type := I | O.

Module INT.
  Module Type VALUE.
    Parameter t: Type.
    Parameter is_zero: t -> bool.
    Parameter zero: t.
    Parameter eq_dec: forall (x: t) (y: t), {x = y} + {x <> y}.
    Parameter zero_is_zero: is_zero zero = true.
    Parameter non_zero_is_not_zero: forall (x: t), x <> zero -> is_zero x = false.
  End VALUE.

  Module DOUBLE (BASE : VALUE).
    Definition t := (BASE.t * BASE.t)%type.

    Definition is_zero v :=
      match v with
      | (lo, hi) => BASE.is_zero lo && BASE.is_zero hi
      end.

    Definition zero: t := (BASE.zero, BASE.zero).

    Lemma eq_dec: forall (x: t) (y: t), {x = y} + {x <> y}.
    Proof.
      intros x y.
      destruct x; destruct y.
      destruct (BASE.eq_dec t0 t2); destruct (BASE.eq_dec t1 t3); subst; auto;
      right; intros contra; inversion contra; contradiction.
    Qed.

    Lemma zero_is_zero: is_zero zero = true.
    Proof.
      simpl; rewrite BASE.zero_is_zero; auto.
    Qed.

    Lemma non_zero_is_not_zero: forall (x: t), x <> zero -> is_zero x = false.
    Proof.
      intros x Hnz.
      destruct x as [lo hi].
      destruct (BASE.eq_dec lo BASE.zero); destruct (BASE.eq_dec hi BASE.zero);
      unfold zero in Hnz; subst; try contradiction; simpl;
      try rewrite <- (BASE.non_zero_is_not_zero hi);
      try rewrite <- (BASE.non_zero_is_not_zero lo);
      try rewrite (BASE.non_zero_is_not_zero hi);
      try rewrite (BASE.non_zero_is_not_zero lo);
      try rewrite BASE.zero_is_zero;
      auto.
    Qed.
  End DOUBLE.

  Module I1 <: VALUE.
    Definition t := bit.

    Definition is_zero v :=
      match v with
      | I => false
      | O => true
      end.

    Definition zero: t := O.

    Lemma eq_dec: forall (x: t) (y: t), {x = y} + {x <> y}.
    Proof.
      intros x y.
      destruct x; destruct y; auto; right; intros contra; inversion contra.
    Qed.

    Lemma zero_is_zero: is_zero zero = true.
    Proof. reflexivity. Qed.

    Lemma non_zero_is_not_zero: forall (x: t), x <> zero -> is_zero x = false.
    Proof. intros x Hnz; destruct x; [reflexivity|contradiction]. Qed.
  End I1.

  Module I2 := DOUBLE I1.
  Module I4 := DOUBLE I2.
  Module I8 := DOUBLE I4.
  Module I16 := DOUBLE I8.
  Module I32 := DOUBLE I16.
  Module I64 := DOUBLE I32.

  Inductive t : Type :=
    | Int8 (v: I8.t)
    | Int16 (v: I16.t)
    | Int32 (v: I32.t)
    | Int64 (v: I64.t)
    .

  Definition is_zero (v: t): bool :=
    match v with
    | Int8 v => I8.is_zero v
    | Int16 v => I16.is_zero v
    | Int32 v => I32.is_zero v
    | Int64 v => I64.is_zero v
    end.

  Inductive IsZero: t -> Prop :=
    | z_int8: IsZero (Int8 I8.zero)
    | z_int16: IsZero (Int16 I16.zero)
    | z_int32: IsZero (Int32 I32.zero)
    | z_int64: IsZero (Int64 I64.zero)
    .

  Lemma is_zero_Zero:
    forall (v: t),
      is_zero v = true <-> IsZero v.
  Proof.
    intros v.
    split; intros H.
    {
      destruct v; inversion H as [H'];
        [ destruct (I8.eq_dec v I8.zero)
        | destruct (I16.eq_dec v I16.zero)
        | destruct (I32.eq_dec v I32.zero)
        | destruct (I64.eq_dec v I64.zero)
        ]; subst; try constructor;
        [ rewrite I8.non_zero_is_not_zero in H'
        | rewrite I16.non_zero_is_not_zero in H'
        | rewrite I32.non_zero_is_not_zero in H'
        | rewrite I64.non_zero_is_not_zero in H'
        ]; auto; inversion H'.
    }
    {
      inversion H; subst; simpl; reflexivity.
    }
  Qed.

  Inductive IsNonZero: t -> Prop :=
    | nz_int8:  forall (v: I8.t)  (NZ: v <> I8.zero),  IsNonZero (Int8 v)
    | nz_int16: forall (v: I16.t) (NZ: v <> I16.zero), IsNonZero (Int16 v)
    | nz_int32: forall (v: I32.t) (NZ: v <> I32.zero), IsNonZero (Int32 v)
    | nz_int64: forall (v: I64.t) (NZ: v <> I64.zero), IsNonZero (Int64 v)
    .

  Lemma is_zero_NonZero:
    forall (v: t),
      is_zero v = false <-> IsNonZero v.
  Proof.
    intros v.
    split; intros H.
    {
      destruct v; try constructor; inversion H as [H']; clear H;
      intros contra; subst; simpl in H'; inversion H'.
    }
    {
      inversion H; subst; clear H; auto; simpl;
        [ rewrite I8.non_zero_is_not_zero
        | rewrite I16.non_zero_is_not_zero
        | rewrite I32.non_zero_is_not_zero
        | rewrite I64.non_zero_is_not_zero
        ]; auto.
    }
  Qed.

  Lemma zero_dec: forall (v: t), {IsNonZero v} + {IsZero v}.
  Proof.
    intros v; destruct v.
    - destruct (I8.eq_dec  v I8.zero);  [right; subst|left]; constructor; auto.
    - destruct (I16.eq_dec v I16.zero); [right; subst|left]; constructor; auto.
    - destruct (I32.eq_dec v I32.zero); [right; subst|left]; constructor; auto.
    - destruct (I64.eq_dec v I64.zero); [right; subst|left]; constructor; auto.
  Qed.
End INT.

Inductive sym : Type :=
  (* Pointer to the program arguments. *)
  | SInit (object: positive) (offset: positive)
  (* Pointer into a stack frame *)
  | SFrame (frame: positive) (object: positive) (offset: nat)
  (* Pointer to a global data item *)
  | SAtom (segment: positive) (object: positive) (offset: nat)
  (* Pointer to a function. *)
  | SFunc (func: name)
  .

Inductive value : Type :=
  | VInt (v: INT.t)
  | VSym (s: sym)
  | VUnd
  .

Inductive quad : Type :=
  | QVal (v: INT.I64.t)
  | QSym (s: sym)
  | QUnd
  .

Definition is_true (v: value): bool :=
  match v with
  | VInt v => negb (INT.is_zero v)
  | VSym _ => true
  | VUnd => false
  end.

Inductive IsTrue: value -> Prop :=
  | is_true_int: forall (v: INT.t) (NZ: INT.IsNonZero v), IsTrue (VInt v)
  | is_true_sym: forall (s: sym), IsTrue (VSym s)
  | is_true_und: IsTrue VUnd
  .

Inductive IsFalse: value -> Prop :=
  | is_false_int: forall (v: INT.t) (Z: INT.IsZero v), IsFalse (VInt v)
  | is_false_und: IsFalse VUnd
  .

Lemma value_is_true_or_false: forall (v: value), {IsTrue v} + {IsFalse v}.
Proof.
  intros v; destruct v.
  - destruct (INT.zero_dec v); [left|right]; constructor; auto.
  - left; constructor.
  - right; constructor.
Qed.
