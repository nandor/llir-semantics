(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.


Notation name := positive.

Notation node := positive.

Notation reg := positive.



Inductive bit : Type :=
  | I
  | O
  .

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

Module INT1 <: VALUE.
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
End INT1.

Module INT2 := DOUBLE INT1.

Module INT4 := DOUBLE INT2.

Module INT8 := DOUBLE INT4.

Module INT16 := DOUBLE INT8.

Module INT32 := DOUBLE INT16.

Module INT64 := DOUBLE INT32.

Inductive sym : Type :=
  (* Pointer to the program arguments. *)
  | SInit (object: positive) (offset: positive)
  (* Pointer into a stack frame *)
  | SFrame (frame: positive) (object: positive) (offset: positive)
  (* Pointer to a global data item *)
  | SAtom (object: positive) (offset: positive)
  (* Pointer to a function. *)
  | SFunc (func: name)
  .

Inductive value : Type :=
  | V8 (v: INT8.t)
  | V16 (v: INT16.t)
  | V32 (v: INT32.t)
  | V64 (v: INT64.t)
  | VSym (v: sym)
  | VUnd
  .

Inductive quad : Type :=
  | QVal (v: INT64.t)
  | QSym (v: sym)
  | QUnd
  .

Definition is_true (v: value): bool :=
  match v with
  | V8 v => negb (INT8.is_zero v)
  | V16 v => negb (INT16.is_zero v)
  | V32 v => negb (INT32.is_zero v)
  | V64 v => negb (INT64.is_zero v)
  | VSym _ => true
  | VUnd => false
  end.

Inductive IsTrue: value -> Prop :=
  | is_true_v8:  forall (v: INT8.t)  (NZ: v <> INT8.zero),  IsTrue (V8 v)
  | is_true_v16: forall (v: INT16.t) (NZ: v <> INT16.zero), IsTrue (V16 v)
  | is_true_v32: forall (v: INT32.t) (NZ: v <> INT32.zero), IsTrue (V32 v)
  | is_true_v64: forall (v: INT64.t) (NZ: v <> INT64.zero), IsTrue (V64 v)
  | is_true_sym: forall (s: sym), IsTrue (VSym s)
  .

Lemma is_true_True:
  forall (v: value),
    is_true v = true <-> IsTrue v.
Proof.
  intros v.
  split; intros H.
  {
    destruct v; try constructor; inversion H as [H']; clear H;
    intros contra; subst; simpl in H'; inversion H'.
  }
  {
    inversion H; subst; clear H; auto; simpl;
      [ rewrite INT8.non_zero_is_not_zero
      | rewrite INT16.non_zero_is_not_zero
      | rewrite INT32.non_zero_is_not_zero
      | rewrite INT64.non_zero_is_not_zero
      ]; auto.
  }
Qed.

Inductive IsFalse: value -> Prop :=
  | is_false_v8:  IsFalse (V8  INT8.zero)
  | is_false_v16: IsFalse (V16 INT16.zero)
  | is_false_v32: IsFalse (V32 INT32.zero)
  | is_false_v64: IsFalse (V64 INT64.zero)
  | is_false_und: IsFalse VUnd
  .

Lemma is_true_False:
  forall (v: value),
    is_true v = false <-> IsFalse v.
Proof.
  intros v.
  split; intros H.
  {
    destruct v; try constructor; inversion H as [H'];
      [ destruct (INT8.eq_dec v INT8.zero)
      | destruct (INT16.eq_dec v INT16.zero)
      | destruct (INT32.eq_dec v INT32.zero)
      | destruct (INT64.eq_dec v INT64.zero)
      ]; subst; try constructor;
      [ rewrite INT8.non_zero_is_not_zero in H'
      | rewrite INT16.non_zero_is_not_zero in H'
      | rewrite INT32.non_zero_is_not_zero in H'
      | rewrite INT64.non_zero_is_not_zero in H'
      ]; auto; inversion H'.
  }
  {
    inversion H; subst; simpl; reflexivity.
  }
Qed.
