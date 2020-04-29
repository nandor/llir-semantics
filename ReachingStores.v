(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.PArith.PArith.
Require Import Coq.Lists.List.

Require Import LLIR.Maps.
Require Import LLIR.State.
Require Import LLIR.Aliasing.
Require Import LLIR.LLIR.
Require Import LLIR.Dom.

Import ListNotations.

Open Scope positive_scope.

Module Reach.
  Definition t := PTrie.t (PTrie.t positive).

  Definition eq: t -> t -> Prop :=
    PTrie.eq (PTrie.t positive) (PTrie.eq positive Pos.eq).

  Theorem eq_refl:
    forall x,
      eq x x.
  Proof.
    intros x.
    unfold eq.
    apply (PTrie.eq_refl (PTrie.t positive)).
    intros v.
    apply (PTrie.eq_refl positive).
    intros v'.
    apply Pos.eq_refl.
  Qed.

  Theorem eq_sym:
    forall x y,
      eq x y -> eq y x.
  Proof.
    intros x y.
    apply (PTrie.eq_sym (PTrie.t positive)).
    intros v1 v2.
    apply (PTrie.eq_sym positive).
    intros v1' v2'.
    apply Pos.eq_sym.
  Qed.

  Theorem eq_trans:
    forall x y z,
      eq x y -> eq y z -> eq x z.
  Proof.
    intros x y z.
    apply (PTrie.eq_trans (PTrie.t positive)).
    intros v1 v2 v3.
    apply (PTrie.eq_trans positive).
    intros v1' v2' v3'.
    apply Pos.eq_trans.
  Qed.

  Definition eqb: t -> t -> bool :=
    PTrie.eqb (PTrie.eqb Pos.eqb).

  Theorem eqb_correct:
    forall x y,
      eqb x y = true -> eq x y.
  Proof.
    intros x y.
    intro H.
    unfold eq.
    apply (PTrie.eqb_eq (PTrie.t positive) (PTrie.eqb Pos.eqb)).
    - intros a b.
      intro H'.
      apply (PTrie.eqb_eq positive Pos.eqb).
      + intros a' b'.
        intro H''.
        apply Pos.eqb_eq in H''.
        apply H''.
      + intros v.
        apply Pos.eq_refl.
      + apply H'.
    - intros v.
      apply (PTrie.eq_refl positive).
      intros v'.
      apply Pos.eq_refl.
    - apply H.
  Qed.

  Definition le (a: t) (b: t): Prop :=
    forall object offset writesA writeA,
      Some writesA = PTrie.get a object ->
      Some writeA = PTrie.get writesA offset ->
      (exists writesB writeB,
        Some writesB = PTrie.get b object /\
        Some writeB = PTrie.get writesB offset /\
        writeA = writeB
      ).

  Theorem le_refl:
    forall x y,
      eq x y -> le x y.
  Proof.
    intros x y.
    intro HPTriePTrieOptionPositive.
    unfold le.
    intros object offset writesA writeA.
    intros HwA HA.
    destruct (y ! object) as [writesB|] eqn:EQwrites.
    {
      exists writesB.
      generalize (HPTriePTrieOptionPositive object).
      rewrite <- HwA.
      rewrite EQwrites.
      intros HPTrieOptionPositive.
      destruct (writesB ! offset) as [writeB|] eqn:EQwrite.
      {
        exists writeB.
        generalize (HPTrieOptionPositive offset).
        rewrite EQwrite.
        rewrite <- HA.
        intros HOptionPositive.
        destruct writeA;
          destruct writeB;
          try unfold ge_write;
          split;
          try split;
          try rewrite HOptionPositive;
          try reflexivity.
      }
      {
        generalize (HPTrieOptionPositive offset).
        rewrite EQwrite.
        rewrite <- HA.
        intros H.
        inversion H.
      }
    }
    {
      generalize (HPTriePTrieOptionPositive object).
      rewrite EQwrites.
      rewrite <- HwA.
      intros H.
      inversion H.
    }
  Qed.

  Theorem le_trans:
    forall x y z,
      le x y -> le y z -> le x z.
  Proof.
    intros x y z.
    intro HPxy.
    intro HPyz.
    intros objects object writesX writeX.

    generalize (HPxy objects object writesX writeX).
    intros Hxy.
    intros HwX.
    intros HX.
    apply Hxy in HwX; try apply HX.
    destruct HwX as [writesY CCY].
    destruct CCY as [writeY CY].
    destruct CY.
    destruct H0.

    generalize (HPyz objects object writesY writeY).
    intros Hyz.
    apply Hyz in H; try apply H0.
    destruct H as [writesZ CCX].
    destruct CCX as [writeZ CX].
    destruct CX.
    destruct H2.

    exists writesZ.
    exists writeZ.
    split. apply H.
    split. apply H2.
    rewrite <- H3.
    rewrite H1.
    reflexivity.
  Qed.

  Definition top: t := PTrie.empty (PTrie.t positive).

  Theorem le_top:
    forall x,
      le top x.
  Proof.
    intro x.
    unfold le.
    intros object offset writes write.
    intros H.
    inversion H.
  Qed.

  Definition lub_offset (a: PTrie.t positive) (b: PTrie.t positive): PTrie.t positive :=
    PTrie.combine positive positive positive
      (fun av bv =>
        match av, bv with
        | Some av', Some bv' => if av' =? bv' then Some av' else None
        | _, _ => None
        end) a b.

  Definition lub (a: t) (b: t): t :=
    PTrie.combine (PTrie.t positive) (PTrie.t positive) (PTrie.t positive)
      (fun av bv =>
        match av, bv with
        | Some av', Some bv' => Some (lub_offset av' bv')
        | _, _ => None
        end) a b.

  Theorem ge_lub_left:
    forall x y,
      le (lub x y) x.
  Proof.
    intros x y.
    unfold le.
    intros object offset writesL writeL.
    intros HwL.
    intros HL.
    unfold lub in HwL.
    rewrite PTrie.combine_correct in HwL; try reflexivity.
    {
      destruct (x ! object) as [writesX|] eqn:EwX;
      destruct (y ! object) as [writesY|] eqn:EwY;
      try inversion HwL.
      {
        rewrite H0 in HL.
        unfold lub_offset in HL.
        rewrite PTrie.combine_correct in HL; try reflexivity; try apply writesL.
        exists writesX.
        destruct (writesX ! offset) as [writeX|] eqn:EX;
        destruct (writesY ! offset) as [writeY|] eqn:EY;
        try exists writeX; try (split; try split; try reflexivity);
        try inversion HL.
        destruct (writeX =? writeY) eqn:E.
        - inversion HL. reflexivity.
        - inversion HL.
      }
    }
    apply x.
  Qed.

  Theorem ge_lub_right:
    forall x y,
      le (lub x y) y.
  Proof.
    intros x y.
    unfold le.
    intros object offset writesL writeL.
    intros HwL.
    intros HL.
    unfold lub in HwL.
    rewrite PTrie.combine_correct in HwL; try reflexivity.
    {
      destruct (y ! object) as [writesY|] eqn:EwY;
      destruct (x ! object) as [writesX|] eqn:EwX;
      try inversion HwL.
      {
        rewrite H0 in HL.
        unfold lub_offset in HL.
        rewrite PTrie.combine_correct in HL; try reflexivity; try apply writesL.
        exists writesY.
        destruct (writesY ! offset) as [writeY|] eqn:EY;
        destruct (writesX ! offset) as [writeX|] eqn:EX;
        try exists writeY; try (split; try split; try reflexivity);
        try inversion HL.
        destruct (writeX =? writeY) eqn:E.
        - apply Pos.eqb_eq in E. rewrite <- E. inversion H1. reflexivity.
        - inversion HL.
      }
    }
    apply x.
  Qed.
End Reach.


Module Kildall.

  Definition state := PTrie.t Reach.t.

End Kildall.

Definition reaching_stores := PTrie.t (PTrie.t (PTrie.t reg)).

Axiom analyse_reaching_stores: 
  forall (f: func) (aa: points_to_set), reaching_stores.

Section ANALYSIS.
  Variable f: func.

  Section UTILITIES.
    Variable aa: points_to_set.
    Variable rs: reaching_stores.

    Definition get_store_to (k: node) (obj: Object): option reg :=
      match PTrie.get rs k with
      | Some objects =>
        match obj with
        | (object, offset) =>
          match PTrie.get objects object with
          | Some object' =>
            match PTrie.get object' offset with
            | Some write => Some write
            | _ => None
            end
          | _ => None
          end
        end
      | _ => None
      end.

    Inductive stored_at: node -> positive -> positive -> reg -> Prop :=
      | store_at:
        forall (n: node) (object: positive) (offset: positive) (val: reg),
          forall (addr: reg) (next: node),
            Some (LLSt addr val next) = f.(fn_insts) ! n ->
            Some [PTOffset object offset] = aa ! addr ->
            stored_at n object offset val
      .

    Inductive store_to_at: node -> reg -> positive -> positive -> Prop :=
      | store:
        forall (k: node) (val: reg) (object: positive) (offset: positive),
          Some val = get_store_to k (object, offset) -> 
          store_to_at k val object offset
      .
  End UTILITIES.

  Section PROPERTIES.
    Variable aa: points_to_set.
    Variable rs: reaching_stores.

    Theorem reaching_stores_dom:
      forall (use: node) (objects: PTrie.t (PTrie.t reg))
             (object: positive) (object': PTrie.t reg)
             (offset: positive) (write: reg) 
             (def: node),
        Some objects = PTrie.get rs use ->
        Some object' = PTrie.get objects object ->
        Some write = PTrie.get object' offset ->
        stored_at aa def object offset write ->
        Dominates f def use.
    Admitted.

    Theorem reaching_store_origin:
      forall (reach: node) (val: reg) (object: positive) (offset: positive),
        store_to_at rs reach val object offset ->
          exists (orig: node) (addr: reg) (next: node),
            stored_at aa orig object offset val
            /\
            Dominates f orig reach
            .
    Admitted.
  End PROPERTIES.
End ANALYSIS.

