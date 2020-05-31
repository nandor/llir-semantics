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
        Path n [n] n
    | path_cons:
      forall (from: node) (next: node) (to: node) (p: list node)
        (REACH: Reachable from)
        (TL: Path from p next)
        (HD: SuccOf f next to),
        Path from (to :: p) to
    .

  Theorem path_reaches_start:
    forall (x: node) (path: list node) (y: node),
      Path x path y -> Reachable x.
  Proof.
    intros x path y Hpath.
    inversion Hpath; apply REACH.
  Qed.

  Theorem path_reaches_end:
    forall (x: node) (path: list node) (y: node),
      Path x path y -> Reachable y.
  Proof.
    intros x path y Hpath.
    induction Hpath. apply REACH.
    subst. apply (reach_succ next). apply HD. apply IHHpath.
  Qed.

  Theorem start_in_path:
    forall (x: node) (path: list node) (y: node),
      Path x path y -> In x path.
  Proof.
    intros x path y Hpath.
    induction Hpath; intuition.
  Qed.

  Theorem last_in_path:
    forall (x: node) (path: list node) (y: node),
      Path x path y -> In y path.
  Proof.
    intros x path y Hpath.
    inversion Hpath; left; auto.
  Qed.

  Theorem path_app:
    forall (zy: list node) (yx: list node) (x: node) (y: node) (z: node),
      Path x (y::yx) y ->
      Path y zy z ->
      Path x (zy ++ yx) z.
  Proof.
    induction zy; intros yx x y z Hxy Hyz.
    - simpl. inversion Hyz; subst.
    - rewrite <- app_comm_cons.
      inversion Hyz; subst.
      + simpl. apply Hxy.
      + apply (path_cons x next).
        * apply (path_reaches_start x (y::yx) y Hxy).
        * apply (IHzy yx x y next Hxy).
          inversion Hyz; subst; apply TL.
        * apply HD.
  Qed.

  Theorem path_app_inv:
    forall (zy: list node) (yx: list node) (x: node) (y: node) (z: node),
      Path x (zy ++ [y] ++ yx) z ->
      Path x (y::yx) y /\ Path y (zy ++ [y]) z.
  Proof.
    induction zy; intros yx x y z Hpath.
    {
      simpl in Hpath.
      split; inversion Hpath; subst.
      + apply path_nil. apply REACH.
      + apply Hpath.
      + simpl. apply Hpath.
      + simpl. apply path_nil.
        apply (path_reaches_end x (z :: yx) z Hpath).
    }
    {
      inversion Hpath; subst.
      {
        assert (Hcontra: [] <> zy ++ y :: yx).
        {
          destruct zy; intros contra; simpl.
          + simpl in contra. inversion contra.
          + inversion contra.
        }
        apply Hcontra in H2; inversion H2.
      }
      {
        assert (y :: yx = [y] ++ yx). auto.
        rewrite H in TL.
        generalize (IHzy yx x y next TL). intros Hind.
        destruct Hind as [Hl Hr].
        split. apply Hl.
        apply path_cons with (next := next).
        + apply (path_reaches_end x (y :: yx) y Hl).
        + apply Hr.
        + apply HD.
      }
    }
  Qed.

  Theorem path_next:
    forall (n: node) (m: node),
      Closure n m -> Reachable n -> exists p, Path n p m.
  Proof.
    intros n m Hsucc HreachX.
    induction Hsucc.
    {
      exists [x].
      apply path_nil.
      apply HreachX.
    }
    {
      exists [y;x].
      apply (path_cons x x y).
      - apply HreachX.
      - apply path_nil. apply HreachX.
      - apply STEP.
    }
    {
      assert (HreachY: Reachable y).
      { apply (reachable_closure x). apply HreachX. apply Hsucc1. }
      apply IHHsucc1 in HreachX.
      apply IHHsucc2 in HreachY.
      destruct HreachX.
      destruct HreachY.
      inversion H; subst.
      + exists x1. apply H0.
      + exists (x1 ++ p).
        apply path_app with (y := y). apply H. apply H0.
    }
  Qed.

  Theorem reachable_path:
    forall (n: node),
      Reachable n -> exists p, Path entry p n.
  Proof.
    intros n Hreach.
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
    + inversion Hreach; subst.
      - contradiction.
      - apply dom_path.
        {
          intros p Hpath.
          inversion Hpath; subst.
          + contradiction.
          + right. apply start_in_path with (y := next). apply TL0.
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
    destruct (Pos.eq_dec n entry); intro H. apply e.
    inversion H; auto.
    generalize (PATH [entry]).
    intros Hpath.
    assert (Hentry: Path entry [entry] entry). apply path_nil. apply reach_entry.
    apply Hpath in Hentry.
    inversion Hentry; intuition.
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
      inversion Hpath; subst. contradiction.
      apply Huniq in HD.
      subst.
      right.
      apply last_in_path with (x := entry). apply TL.
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

  Inductive BasicBlockHeader: node -> Prop :=
    | block_header:
      forall (header: node)
        (REACH: Reachable header)
        (TERM: forall (term: node), SuccOf f term header -> TermAt f term)
        (INST: f.(fn_insts) ! header <> None),
        BasicBlockHeader header
    .

  Inductive BasicBlock: node -> node -> Prop :=
    | bb_header:
      forall (header: node)
        (HEADER: BasicBlockHeader header),
          BasicBlock header header
    | bb_elem:
      forall (header: node) (prev: node) (elem: node)
        (NOT_HEADER: header <> elem)
        (NOT_ENTRY: entry <> elem)
        (BLOCK: BasicBlock header prev)
        (PRED: SuccOf f prev elem)
        (NOT_TERM: ~TermAt f prev)
        (INST: f.(fn_insts) ! elem <> None)
        (NO_PHI: f.(fn_phis) ! elem = None)
        (UNIQ: forall (prev': node), SuccOf f prev' elem -> prev' = prev),
          BasicBlock header elem
    .

  Theorem bb_reaches:
    forall (header: node) (elem: node),
      BasicBlock header elem -> Reachable elem.
  Proof.
    intros header elem Hbb.
    induction Hbb.
    inversion HEADER.
    apply REACH.
    apply reach_succ with (a := prev); auto.
  Qed.

  Theorem bb_has_header:
    forall (header: node) (elem: node),
      BasicBlock header elem -> BasicBlockHeader header.
  Proof.
    intros header elem Hbb.
    induction Hbb.
    apply HEADER.
    apply IHHbb.
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

  Theorem bb_header_unique:
    forall (elem: node) (header: node) (header': node),
      BasicBlock header elem ->
      BasicBlock header' elem ->
      header = header'.
  Proof.
    intros elem header header'.
    intros Hbb Hbb'.
    induction Hbb'.
    {
      inversion Hbb; auto.
      inversion HEADER.
      apply TERM in PRED.
      apply NOT_TERM in PRED.
      inversion PRED.
    }
    {
      apply IHHbb'.
      inversion Hbb.
      {
        subst.
        inversion HEADER.
        apply TERM in PRED.
        apply NOT_TERM in PRED.
        inversion PRED.
      }
      {
        subst.
        apply UNIQ in PRED0.
        subst prev0.
        apply BLOCK.
      }
    }
  Qed.

  Inductive BasicBlockSucc: node -> node -> Prop :=
    | basic_block_succ:
      forall (from: node) (to: node) (term: node)
        (HDR_FROM: BasicBlock from term)
        (HDR_TO: BasicBlockHeader to)
        (SUCC: SuccOf f term to),
        BasicBlockSucc from to
    .

  Inductive BasicBlockPath: node -> list node -> node -> Prop :=
    | bb_path_nil:
      forall (n: node)
        (REACH: Reachable n)
        (HEADER: BasicBlockHeader n),
        BasicBlockPath n [n] n
    | bb_path_cons:
      forall (from: node) (next: node) (to: node) (p: list node)
        (REACH: Reachable from)
        (TL: BasicBlockPath from p next)
        (HD: BasicBlockSucc next to),
        BasicBlockPath from (to :: p) to
    .

  Inductive BasicBlockDominates: node -> node -> Prop :=
    | bb_dom_self:
      forall (n: node),
        BasicBlockDominates n n
    | bb_dom_path:
      forall (a: node) (b: node)
        (PATH: forall (p: list node), BasicBlockPath entry p b -> In a p)
        (REACH: Reachable b),
        BasicBlockDominates a b
    .
End FUNCTION.

Lemma eq_cfg_dom:
  forall (f: func) (f': func),
    (forall (src: node) (dst: node), SuccOf f src dst <-> SuccOf f' src dst) ->
    forall (src: node) (dst: node),
      Dominates f src dst <->
      Dominates f' src dst.
Admitted.

