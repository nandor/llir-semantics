(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Require Import LLIR.State.
Require Import LLIR.LLIR.
Require Import LLIR.Maps.

Import ListNotations.

Section FUNCTION.
  Variable f: func.

  Definition entry: node := f.(fn_entry).

  Definition Succ (from: node) (to: node) :=
    match PTrie.get f.(fn_insts) from with
    | Some i => SuccessorOfInst i to
    | None => False
    end.

  Inductive Closure (x: node): node -> Prop :=
    | closure_refl:
      Closure x x
    | closure_step:
      forall (y: node) (STEP: Succ x y),
        Closure x y
    | closure_trans:
      forall (y: node) (z: node),
        Closure x y -> Closure y z -> Closure x z
    .

  Inductive Reachable: node -> Prop :=
    | reach_entry:
      Reachable f.(fn_entry)
    | reach_succ:
      forall (a: node) (b: node)
        (HD: Succ a b)
        (TL: Reachable a),
        Reachable b
    .

  Theorem reachable_closure:
    forall (n: node) (m:node),
      Reachable n -> Closure n m -> Reachable m.
  Proof.
    intros n m.
    intro HreachN.
    intro Hclosure.
    induction Hclosure.
    - apply HreachN.
    - apply (reach_succ x). apply STEP. apply HreachN.
    - apply IHHclosure1 in HreachN.
      apply IHHclosure2 in HreachN.
      apply HreachN.
  Qed.

  Inductive Path: node -> list node -> node -> Prop :=
    | path_nil:
      forall (n: node)
        (REACH: Reachable n),
        Path n nil n
    | path_cons:
      forall (from: node) (next: node) (to: node) (p: list node)
        (HD: Succ from next)
        (TL: Path next p to),
        Path from (from :: p) to
    .

  Theorem path_app:
    forall (xy: list node) (yz: list node) (x: node) (y: node) (z: node),
      Path x xy y ->
      Path y yz z ->
      Path x (xy ++ yz) z.
  Proof.
    induction xy; intros yz x y z Hxy Hyz.
    - simpl. inversion Hxy. apply Hyz.
    - rewrite <- app_comm_cons.
      inversion Hxy.
      apply (path_cons a next). apply HD.
      apply (IHxy yz next y z). apply TL. apply Hyz.
  Qed.

  Theorem path_next:
    forall (n: node) (m: node),
      Closure n m -> Reachable n -> exists p, Path n p m.
  Proof.
    intros n m.
    intros Hsucc.
    induction Hsucc.
    {
      intros Hreach.
      exists nil.
      apply path_nil.
      apply Hreach.
    }
    {
      intros Hreach.
      exists [x].
      apply (path_cons x y y). apply STEP. apply path_nil.
      apply (reach_succ x). apply STEP. apply Hreach.
    }
    {
      intros HreachX.
      assert (HreachY: Reachable y).
      { apply (reachable_closure x). apply HreachX. apply Hsucc1. }
      apply IHHsucc1 in HreachX.
      apply IHHsucc2 in HreachY.
      destruct HreachX.
      destruct HreachY.
      exists (x0 ++ x1).
      apply (path_app x0 x1 x y z). apply H. apply H0.
    }
  Qed.

  Theorem reachable_path:
    forall (n: node),
      Reachable n -> exists p, Path entry p n.
  Proof.
    intros n.
    intros Hreach.
    apply path_next.
    {
      induction Hreach.
      - apply closure_refl.
      - apply (closure_trans entry a b).
        apply IHHreach.
        apply closure_step. apply HD.
    }
    apply reach_entry.
  Qed.

  Inductive Dominates: node -> node -> Prop :=
    | dom_self:
      forall (n: node),
        Dominates n n
    | dom_path:
      forall (a: node) (b: node)
        (PATH: forall (p: list node), Path entry p b -> In a p)
        (REACH: Reachable a),
        Dominates a b
    .

  Theorem entry_dominates_all:
    forall (n: node),
      Reachable n -> Dominates entry n.
  Proof.
    intro n.
    intro Hreach.
    destruct (Pos.eq_dec n entry).
    + rewrite e. apply dom_self.
    + inversion Hreach.
      - rewrite <- H in n0. destruct n0; reflexivity.
      - apply dom_path.
        {
          intros p.
          intro Hpath.
          inversion Hpath.
          + rewrite H2 in n0. destruct n0. reflexivity.
          + simpl. auto.
        }
        {
          apply reach_entry.
        }
  Qed.

  Theorem dominator_of_entry:
    forall (n: node),
      Dominates n entry -> n = entry.
  Proof.
    intros n.
    destruct (Pos.eq_dec n entry).
    {
      intro H. apply e.
    }
    {
      intro H.
      inversion H.
      reflexivity.
      generalize (PATH nil).
      intros Hpath.
      assert (Hentry: Path entry nil entry). apply path_nil. apply reach_entry.
      apply Hpath in Hentry.
      inversion Hentry.
    }
  Qed.

  Theorem dom_antisym:
    forall (n: node) (m: node),
      Dominates n m ->
      Dominates m n ->
      m = n.
   Admitted.

  Theorem dom_trans:
    forall (n: node) (m: node) (p: node),
      Dominates n m -> Dominates m p -> Dominates n p.
  Admitted.

  Inductive StrictlyDominates: node -> node -> Prop :=
    | sdom_path:
        forall (a: node) (b: node)
          (DOM: Dominates a b)
          (STRICT: a <> b),
          StrictlyDominates a b
    .

  Theorem sdom_trans:
    forall (n: node) (m: node) (p: node),
      StrictlyDominates n m -> StrictlyDominates m p -> StrictlyDominates n p.
  Proof.
    intros n m p Hnm Hmp.
    inversion Hnm.
    inversion Hmp.
    constructor. 
    apply (dom_trans n m p); auto.
    intro contra. subst.
    assert (Heq: m = p). { apply (dom_antisym p m); auto. }
    auto.
  Qed.
End FUNCTION.

Lemma eq_cfg_dom:
  forall (f: func) (f': func),
    (forall (src: node) (dst: node), Succ f src dst <-> Succ f' src dst) ->
    forall (src: node) (dst: node),
      Dominates f src dst <-> 
      Dominates f' src dst.
Admitted.

