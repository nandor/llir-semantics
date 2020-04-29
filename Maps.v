(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.EquivDec.

Import ListNotations.


Module Type PARTIAL_MAP.
  Parameter key: Type.
  Parameter t: Type -> Type.

  Parameter empty:
    forall (V: Type),
      t V.

  Parameter get:
    forall (V: Type),
      t V -> key -> option V.

  Parameter set:
    forall (V: Type),
      t V -> key -> V -> t V.

  Parameter remove:
    forall (V: Type),
      t V -> key -> t V.

  Parameter map:
    forall (A: Type) (B: Type),
      (key -> A -> B) -> t A -> t B.

  Parameter map_opt:
    forall (A: Type) (B: Type),
      (key -> A -> option B) -> t A -> t B.

  Parameter fold:
    forall (A: Type) (B: Type),
      (B -> key -> A -> B) -> t A -> B -> B.

  Parameter to_list:
    forall (V: Type),
      t V -> list (key * V).

  Parameter values:
    forall (V: Type),
      t V -> list V.

  Parameter eqb: forall (V: Type), (V -> V -> bool) -> t V -> t V -> bool.

End PARTIAL_MAP.

Module PTrie <: PARTIAL_MAP.
  Inductive tree (V: Type): Type :=
    | Leaf: tree V
    | Node: tree V -> option V -> tree V -> tree V
    .

  Arguments Leaf {V}.
  Arguments Node [V].

  Definition key := positive.

  Definition t := tree.

  Definition empty (V: Type) := Leaf : tree V.

  Fixpoint get (V: Type) (a: t V) (key: positive): option V :=
    match a with
    | Leaf => None
    | Node l o r =>
        match key with
        | xH => o
        | xO ii => get V l ii
        | xI ii => get V r ii
        end
    end.

  Fixpoint set (V: Type) (a: t V) (key: positive) (v: V): t V :=
    match key with
    | xH =>
      match a with
      | Leaf => Node Leaf (Some v) Leaf
      | Node l _ r => Node l (Some v) r
      end
    | xO ii =>
      match a with
      | Leaf => Node (set V Leaf ii v) None Leaf
      | Node l o r => Node (set V l ii v) o r
      end
    | xI ii =>
      match a with
      | Leaf => Node Leaf None (set V Leaf ii v)
      | Node l o r => Node l o (set V r ii v)
      end
    end.

  Fixpoint remove (V: Type) (a: t V) (key: positive): t V :=
    match a with
    | Leaf => Leaf
    | Node l o r =>
      match key with
      | xH => Node l None r
      | xO ii => Node (remove V l ii) o r
      | xI ii => Node l o (remove V r ii)
      end
    end.

  Fixpoint append (l: positive) (r: positive): positive :=
    match l with
    | xH => l
    | xO i => xO (append i r)
    | xI i => xI (append i r)
    end.

  Section MAP_OPT.
    Variables A B: Type.
    Variable f: key -> A -> option B.

    Fixpoint map_opt_helper (a: t A) (k: key): t B :=
      match a with
      | Leaf => Leaf
      | Node l v r =>
        let v' := match v with
          | None => None
          | Some v => f k v
          end
        in
        Node
          (map_opt_helper l (append (xO xH) k))
          v'
          (map_opt_helper r (append (xI xH) k))
      end.

    Definition map_opt (a: t A): t B := map_opt_helper a xH.
  End MAP_OPT.

  Section MAP.
    Variables A B: Type.
    Variable f: key -> A -> B.

    Definition map (a: t A): t B := map_opt A B (fun k a => Some (f k a)) a.
  End MAP.

  Fixpoint fold_helper (A: Type) (B: Type) (f: B -> key -> A -> B) (key: key) (t: t A) (v: B) : B :=
    match t with
    | Leaf => v
    | Node l None r =>
       let r' := fold_helper A B f (append key (xO xH)) r v in
       fold_helper A B f (append key (xI xH)) l r'
    | Node l (Some o) r =>
       let r' := fold_helper A B f (append key (xO xH)) r v in
       let o' := f r' key o in
       fold_helper A B f (append key (xI xH)) l o'
    end.

  Fixpoint fold (A: Type) (B: Type) (f: B -> key -> A -> B) (t: t A) (v: B) :=
    fold_helper A B f xH t v.

  Fixpoint to_list_helper (V: Type) (t: t V) (k: key) (acc: list (key * V)) :=
    match t with
    | Leaf => acc
    | Node l None r =>
      let r' := to_list_helper V r (append (xI xH) k) acc in
      to_list_helper V r (append (xO xH) k) acc
    | Node l (Some v) r =>
      let r' := to_list_helper V r (append (xI xH) k) acc in
      let v' := (k, v) :: r' in
      to_list_helper V r (append (xO xH) k) acc
    end.

  Definition to_list (V: Type) (t: t V) :=
    to_list_helper V t xH [].

  Section VALUES.
    Variable V: Type.

    Fixpoint values_helper (t: t V) (acc: list V) :=
      match t with
      | Leaf => acc
      | Node l None r => values_helper l (values_helper r acc)
      | Node l (Some v) r => values_helper l (v :: values_helper r acc)
      end.

    Fixpoint values (t: t V) := values_helper t nil.

    Theorem values_correct:
      forall (t: t V) (v: V),
        In v (values t) -> exists k, Some v = get V t k.
    Proof.
      induction t0; intros v; intros Hind.
      - inversion Hind.
      - destruct o.
        + 
    Qed.
  End VALUES.

  Section COMBINE.
    Variables A B C: Type.
    Variable f: option A -> option B -> option C.

    Hypothesis f_none : f None None = None.

    Fixpoint combine_l (a: t A): t C :=
      match a with
      | Leaf => Leaf
      | Node l v r => Node (combine_l l) (f v None) (combine_l r)
      end.

    Theorem combine_l_correct:
      forall (a: t A) (k: key),
        get C (combine_l a) k = f (get A a k) None.
    Proof.
      intros a.
      induction a; intros k; simpl.
      try rewrite f_none; reflexivity.
      destruct k; try reflexivity.
      apply IHa2.
      apply IHa1.
    Qed.

    Fixpoint combine_r (b: t B): t C :=
      match b with
      | Leaf => Leaf
      | Node l v r => Node (combine_r l) (f None v) (combine_r r)
      end.

    Theorem combine_r_correct:
      forall (b: t B) (k: key),
        get C (combine_r b) k = f None (get B b k).
    Proof.
      intros a.
      induction a; intros k; simpl.
      try rewrite f_none; reflexivity.
      destruct k; try reflexivity.
      apply IHa2.
      apply IHa1.
    Qed.

    Fixpoint combine (a: t A) (b: t B): t C :=
      match a, b with
      | Leaf, _ => combine_r b
      | _, Leaf => combine_l a
      | Node al av ar, Node bl bv br =>
        Node (combine al bl) (f av bv) (combine ar br)
      end.

    Theorem combine_correct:
      forall (a: t A) (b: t B) (c: t C) (k: key),
        get C (combine a b) k = f (get A a k) (get B b k).
    Proof.
      intros a.
      induction a; intros b c k.
      {
        simpl.
        rewrite <- combine_r_correct.
        reflexivity.
      }
      {
        destruct b; simpl.
        destruct k; try rewrite combine_l_correct; reflexivity.
        destruct k.
        - rewrite <- IHa2. reflexivity. apply c.
        - rewrite <- IHa1. reflexivity. apply c.
        - reflexivity.
      }
    Qed.

  End COMBINE.

  Section EXTENSIONAL_EQUALITY.
    Variable V: Type.
    Variable eqV: V -> V -> Prop.

    Hypothesis eqV_refl: forall v, eqV v v.
    Hypothesis eqV_sym: forall v1 v2, eqV v1 v2 -> eqV v2 v1.
    Hypothesis eqV_trans: forall v1 v2 v3, eqV v1 v2 -> eqV v2 v3 -> eqV v1 v3.

    Definition eq (t1: t V) (t2: t V) : Prop :=
      forall key,
        match get V t1 key, get V t2 key with
        | None, None => True
        | Some v1, Some v2 => eqV v1 v2
        | _, _ => False
        end.

    Lemma eq_refl:
      forall (t: t V),
        eq t t.
    Proof.
      intros t.
      unfold eq.
      intros key.
      destruct (get V t key).
      - apply eqV_refl.
      - reflexivity.
    Qed.

    Lemma eq_sym:
      forall (t1: t V) (t2: t V),
        eq t1 t2 -> eq t2 t1.
    Proof.
      intros t1 t2.
      unfold eq.
      intros H key.
      generalize (H key).
      destruct (get V t1 key); destruct (get V t2 key); try auto.
    Qed.

    Lemma eq_trans:
      forall t1 t2 t3,
        eq t1 t2 -> eq t2 t3 -> eq t1 t3.
    Proof.
      intros t1 t2 t3.
      intros H12 H23.
      intros key.
      generalize (H12 key).
      generalize (H23 key).
      destruct (get V t1 key); destruct (get V t2 key); destruct (get V t3 key); try auto.
      - intro H0. intro H1. apply (eqV_trans v v0 v1); auto.
      - intro H'. destruct H'.
    Qed.
  End EXTENSIONAL_EQUALITY.

  Section BOOLEAN_EQUALITY.
    Variable V: Type.
    Variable eqbV: V -> V -> bool.
    Variable eqV: V -> V -> Prop.

    Hypothesis eqbV_eqV: forall a b, eqbV a b = true -> eqV a b.
    Hypothesis eqV_refl: forall v, eqV v v.

    Fixpoint is_empty (a: t V): bool :=
      match a with
      | Leaf => true
      | Node _ (Some _) _ => false
      | Node l None r => is_empty l && is_empty r
      end.

    Theorem is_empty_correct:
      forall t,
        is_empty t = true -> forall key, get V t key = None.
    Proof.
      intros t.
      intro H.
      induction t.
      - intro k.
        reflexivity.
      - intro k.
        destruct o.
        + simpl in H.
          inversion H.
        + apply andb_true_iff in H.
          destruct H as [Hl Hr].
          simpl.
          destruct k; auto.
    Qed.

    Fixpoint eqb (a: t V) (b: t V): bool :=
      match a, b with
      | Leaf, Leaf => true
      | Leaf, _ =>
        is_empty b
      | _, Leaf =>
        is_empty a
      | Node al av ar, Node bl bv br =>
        match av, bv with
        | None, None => true
        | Some av', Some bv' => eqbV av' bv'
        | _, _ => false
        end && eqb al bl && eqb ar br
      end.

    Theorem is_empty_eqb_l:
      forall t,
        is_empty t = true -> eqb Leaf t = true.
    Proof.
      intros t.
      induction t; intros H.
      - simpl. reflexivity.
      - simpl.
        destruct o.
        + inversion H.
        + apply H.
    Qed.

    Theorem is_empty_eqb_r:
      forall t,
        is_empty t = true -> eqb t Leaf = true.
    Proof.
      intros t.
      induction t; intros H.
      - simpl. reflexivity.
      - simpl.
        destruct o.
        + inversion H.
        + apply H.
    Qed.

    Theorem eqb_correct:
      forall t1 t2,
        eqb t1 t2 = true -> forall k, get V t1 k = get V t2 k.
    Admitted.

    Theorem eqb_node:
      forall tl1 o1 tr1 tl2 o2 tr2,
        eqb (Node tl1 o1 tr1) (Node tl2 o2 tr2) = true ->
          (
            (o1 = None /\ o2 = None)
            \/
            exists v1 v2, Some v1 = o1 /\ Some v2 = o2 /\ eqbV v1 v2 = true
          )
          /\
          eqb tl1 tl2 = true
          /\
          eqb tr1 tr2 = true.
    Proof.
      destruct tl1; intros o1 tr1 tl2 o2 tr2; intro H.
      {
        apply andb_true_iff in H.
        destruct H as [Hc Hr].
        apply andb_true_iff in Hc.
        destruct Hc as [Hm Hl].
        repeat split.
        - destruct o1; destruct o2; try inversion Hm.
          + right.
            exists v.
            exists v0.
            repeat split; try reflexivity.
          + left.
            split; reflexivity.
        - destruct tl2.
          + unfold eqb. reflexivity.
          + apply is_empty_eqb_l. apply Hl.
        - apply Hr.
      }
      {
        apply andb_true_iff in H.
        destruct H as [Hc Hr].
        apply andb_true_iff in Hc.
        destruct Hc as [Hm Hl].
        fold eqb in Hl.
        fold eqb in Hr.
        repeat split.
        {
          destruct o1; destruct o2; try inversion Hm.
          + right.
            exists v.
            exists v0.
            repeat split; try reflexivity.
          + left.
            split; reflexivity.
        }
        {
          apply Hl.
        }
        {
          apply Hr.
        }
      }
    Qed.

    Theorem eqb_eq:
      forall t1 t2, eqb t1 t2 = true -> eq V eqV t1 t2.
    Proof.
      induction t1.
      {
        intros t2.
        intro H.
        destruct t2 eqn:Et2.
        - apply eq_refl. intro v. apply eqV_refl.
        - unfold eq.
          intros k.
          simpl.
          inversion H.
          assert (Ho: o = None).
          { destruct o. inversion H1. reflexivity. }
          rewrite Ho in H1.
          rewrite Ho.
          rewrite andb_true_iff in H1.
          destruct H1 as [Ht1 Ht2].
          assert (Hh1: forall key, get V t0_1 key = None).
          {  intro k'. apply is_empty_correct. apply Ht1. }
          assert (Hh2: forall key, get V t0_2 key = None).
          {  intro k'. apply is_empty_correct. apply Ht2. }
          destruct k; try (rewrite Hh2); try (rewrite Hh1); reflexivity.
      }
      {
        intros t2.
        intro H.
        destruct t2 eqn:Et2.
        {
          unfold eq. intros k. simpl.
          inversion H.
          assert (Ho: o = None).
          { destruct o. inversion H1. reflexivity. }
          rewrite Ho in H1.
          rewrite Ho.
          rewrite andb_true_iff in H1.
          destruct H1 as [Ht1 Ht2].
          assert (Hh1: forall key, get V t1_1 key = None).
          {  intro k'. apply is_empty_correct. apply Ht1. }
          assert (Hh2: forall key, get V t1_2 key = None).
          {  intro k'. apply is_empty_correct. apply Ht2. }
          destruct k; try (rewrite Hh2); try (rewrite Hh1); reflexivity.
        }
        {
          unfold eq. intros k.
          apply eqb_node in H.
          destruct H as [Hm Hc].
          destruct Hc as [Hl Hr].
          apply IHt1_1 in Hl. unfold eq in Hl.
          apply IHt1_2 in Hr. unfold eq in Hr.
          destruct k; simpl.
          - destruct (get V t1_2 k) eqn:E1; destruct (get V t0_2 k) eqn:E2;
              generalize (Hr k); intros Hgetr; rewrite E1 in Hgetr; rewrite E2 in Hgetr;
              try inversion Hgetr.
            + apply Hgetr.
            + reflexivity.
          - destruct (get V t1_1 k) eqn:E1; destruct (get V t0_1 k) eqn:E2;
              generalize (Hl k); intros Hgetl; rewrite E1 in Hgetl; rewrite E2 in Hgetl;
              try inversion Hgetl.
            + apply Hgetl.
            + reflexivity.
          - destruct Hm as [Hs|He].
            + destruct Hs.
              rewrite H.
              rewrite H0.
              reflexivity.
            + destruct He. destruct H. destruct H. destruct H0.
              rewrite <- H.
              rewrite <- H0.
              apply eqbV_eqV.
              apply H1.
        }
      }
    Qed.
  End BOOLEAN_EQUALITY.
End PTrie.


Arguments PTrie.get {V}.
Arguments PTrie.eqb {V}.

Notation "a ! b" := (PTrie.get a b) (at level 1).
