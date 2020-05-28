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

  Inductive Closure (x: node): node -> Prop :=
    | closure_refl:
      Closure x x
    | closure_step:
      forall (y: node) (STEP: SuccOf f x y),
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
        (HD: SuccOf f a b)
        (TL: Reachable a),
        Reachable b
    .

  Theorem reachable_closure:
    forall (n: node) (m:node),
      Reachable n -> Closure n m -> Reachable m.
  Proof.
    intros n m HreachN Hclosure.
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
        Path n [] n
    | path_cons:
      forall (from: node) (next: node) (to: node) (p: list node)
        (REACH: Reachable from)
        (HD: SuccOf f from next)
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
      apply (path_cons a next). apply REACH. apply HD.
      apply (IHxy yz next y z). apply TL. apply Hyz.
  Qed.

  Theorem path_app_inv:
    forall (xy: list node) (yz: list node) (x: node) (z: node),
      Path x (xy ++ yz) z ->
        exists (y: node), Path x xy y /\ Path y yz z.
  Proof.
    induction xy; intros yz x z Hpath.
    {
      exists x.
      split.
      + apply path_nil. inversion Hpath; apply REACH.
      + simpl in Hpath. apply Hpath.
    }
    {
      inversion Hpath.
      subst to a from.
      generalize (IHxy yz next z TL). intros Hind.
      destruct Hind as [y [Hl Hr]].
      exists y.
      split.
      {
        apply path_cons with (next := next).
        + apply REACH.
        + apply HD.
        + apply Hl.
      }
      {
        apply Hr.
      }
    }
  Qed.

  Theorem path_last:
    forall (n: node) (m: node) (nm: list node),
      n <> m -> Path n nm m -> 
        exists (p: node) (np: list node),
          nm = np ++ [p] /\ Path n np p /\ SuccOf f p m.
  Proof.
    intros n m nm Hne Hpath.
    inversion Hpath. apply Hne in H1. inversion H1.
    assert (Hneq: n :: p <> []). intros contra. inversion contra.
    generalize (List.exists_last Hneq). intros Hlast.
    destruct Hlast as [path' [p' Hlast]].
    exists p'. exists path'.
    assert (Hpath': Path n (path' ++ [p']) m).
    { rewrite <- Hlast. rewrite H0. apply Hpath. }
    generalize (path_app_inv path' [p'] n m Hpath'). intros Hstep.
    destruct Hstep as [y [Hl Hr]].
    inversion Hr.
    subst y from from0 to to0 p0.
    repeat split.
    - apply Hlast.
    - apply Hl.
    - inversion TL0. subst next0 n0. apply HD0.
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
      apply (path_cons x y y). apply Hreach. apply STEP. apply path_nil.
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
        (REACH: Reachable b),
        Dominates a b
    .

  Inductive StrictlyDominates: node -> node -> Prop :=
    | sdom_path:
        forall (a: node) (b: node)
          (DOM: Dominates a b)
          (STRICT: a <> b),
          StrictlyDominates a b
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
          apply Hreach.
        }
  Qed.

  Theorem dom_of_entry:
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

  Theorem dom_reaches:
    forall (n: node),
      Dominates entry n -> Reachable n.
  Proof.
    intros n Hdom.
    inversion Hdom. apply reach_entry. apply REACH.
  Qed.

  Lemma sdom_not_dom: 
    forall n m,
      StrictlyDominates n m -> ~Dominates m n.
  Admitted.

  Theorem dom_antisym:
    forall (n: node) (m: node),
      Dominates n m ->
      Dominates m n ->
      m = n.
  Proof.
    intros n m Hnm Hmn.
    destruct (Pos.eq_dec m n) as [|Ene]. apply e.
    apply sdom_not_dom in Hnm. inversion Hnm.
    apply sdom_path. apply Hmn. apply Ene.
  Qed.

  Theorem dom_trans:
    forall (n: node) (m: node) (p: node),
      Dominates n m -> Dominates m p -> Dominates n p.
  Admitted.

  Theorem dom_step:
    forall (n: node) (m: node),
      Reachable n
      /\
      SuccOf f n m
      /\
      entry <> m
      /\
      (forall (n': node), SuccOf f n' m -> n = n') ->
      Dominates n m.
  Proof.
    intros n m [Hreach [Hsucc [Hne Huniq]]].
    destruct (Pos.eq_dec n m). subst n. apply dom_self.
    apply dom_path.
    {
      intros path Hpath.
      inversion Hpath.
      {
        subst.
        assert (entry = entry). reflexivity. apply Hne in H. inversion H.
      }
      {
        subst.
        generalize (path_last entry m (entry :: p) Hne Hpath). intros Hsplit.
        destruct Hsplit as [path [np [Hp [_ Hsucc']]]].
        rewrite Hp.
        apply in_or_app.
        right. left. symmetry.
        apply Huniq. apply Hsucc'.
      }
    }
    {
      apply reach_succ with (a := n). apply Hsucc. apply Hreach.
    }
  Qed.

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

  Theorem sdom_irrefl:
    forall (n: node), ~(StrictlyDominates n n).
  Proof.
    intros n contra.
    inversion contra.
    apply STRICT.
    reflexivity.
  Qed.

  Inductive BasicBlock: node -> node -> Prop :=
    | block_header:
      forall (header: node)
        (REACH: Reachable header)
        (TERM: header = entry \/ forall (term: node), SuccOf f term header -> TermAt f term),
        BasicBlock header header
    | block_elem:
      forall (header: node) (prev: node) (elem: node)
        (NOT_HEADER: header <> elem)
        (NOT_ENTRY: entry <> elem)
        (BLOCK: BasicBlock header prev)
        (PRED: SuccOf f prev elem)
        (NOPHI: f.(fn_phis) ! elem = None)
        (UNIQ: forall (prev': node), SuccOf f prev' elem -> prev' = prev),
        BasicBlock header elem
    .

  Theorem bb_reaches:
    forall (header: node) (elem: node),
      BasicBlock header elem -> Reachable elem.
  Proof.
    intros header elem Hbb.
    induction Hbb. apply REACH.
    apply reach_succ with (a := prev); auto.
  Qed.

  Theorem bb_entry_header:
    BasicBlock entry entry.
  Proof.
    apply block_header.
    apply reach_entry.
    left. reflexivity.
  Qed.

  Theorem bb_header_dom_nodes:
    forall (header: node) (elem: node),
      BasicBlock header elem -> Dominates header elem.
  Proof.
    intros header elem Hbb.
    induction Hbb. apply dom_self.
    apply dom_trans with (m := prev); auto.
    apply dom_step.
    repeat split.
    + apply bb_reaches with (header := header). apply Hbb.
    + apply PRED.
    + apply NOT_ENTRY.
    + intros n Hsucc. symmetry. apply UNIQ. apply Hsucc.
  Qed.

  Inductive BasicBlockSucc: node -> node -> Prop :=
    | basic_block_succ:
      forall (from: node) (to: node) (term: node)
        (HDR_FROM: BasicBlock from term)
        (HDR_TO: BasicBlock to to)
        (SUCC: SuccOf f term to),
        BasicBlockSucc from to
    .

End FUNCTION.

Lemma eq_cfg_dom:
  forall (f: func) (f': func),
    (forall (src: node) (dst: node), SuccOf f src dst <-> SuccOf f' src dst) ->
    forall (src: node) (dst: node),
      Dominates f src dst <-> 
      Dominates f' src dst.
Admitted.

