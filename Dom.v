(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.

Require Import LLIR.Values.
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

  Inductive ReversePath: node -> list node -> node -> Prop :=
    | reverse_path_nil:
      forall (n: node)
        (REACH: Reachable n),
        ReversePath n [n] n
    | reverse_path_cons:
      forall (from: node) (next: node) (to: node) (p: list node)
        (REACH: Reachable from)
        (TL: ReversePath next p to)
        (HD: SuccOf f from next),
        ReversePath from (from :: p) to.

  Theorem reverse_path_app:
    forall (xy: list node) (yz: list node) (x: node) (y: node) (z: node),
      ReversePath x xy y ->
      ReversePath y (y::yz) z ->
      ReversePath x (xy ++ yz) z.
  Proof.
    induction xy; intros yz x y z Hxy Hyz.
    { inversion Hxy. }
    {
      rewrite <- app_comm_cons.
      inversion Hxy; subst; simpl; auto.
      apply reverse_path_cons with next; auto.
      apply (IHxy yz next y z); auto.
    }
  Qed.

  Remark rev_nil_nil: forall (A: Type) (p: list A),
    rev p = [] -> p = [].
  Proof.
    intros A p Hrev.
    destruct p; auto.
    simpl in Hrev.
    apply app_eq_nil in Hrev.
    destruct Hrev; inversion H0.
  Qed.

  Theorem path_reverse_path:
    forall (from: node) (to: node) (p: list node),
      Path from p to <-> ReversePath from (rev p) to.
  Proof.
    intros from to p; split; intros Hpath. 
    {
      induction Hpath; simpl.
      { constructor; auto. }
      {
        apply reverse_path_app with (y := next); auto.
        apply reverse_path_cons with (next := to); auto.
        - apply path_reaches_end with (x := from) (path := p); auto.
        - apply reverse_path_nil.
          apply reach_succ with (a := next); auto.
          apply path_reaches_end with (x := from) (path := p); auto.
      }
    }
    {
      dependent induction Hpath.
      {
        destruct p; [inversion x|].
        simpl in x; symmetry in x.
        apply app_eq_unit in x.
        destruct x as [[Hl Hr]|[_ H']].
        { apply rev_nil_nil in Hl; inversion Hr; subst; constructor; auto. }
        { inversion H'. }
      }
      {
        assert (H: rev (from :: p0) = rev (rev p)). { rewrite x; auto. }
        rewrite rev_involutive in H.
        simpl in H.
        subst p; clear x.
        apply path_app with next.
        { apply path_cons with from; auto; constructor; auto. }
        { apply IHHpath. rewrite rev_involutive. reflexivity. }
      }
    }
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
    | sdom_dom:
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
    apply sdom_dom. apply Hmn. apply Ene.
  Qed.

  Theorem in_path_split_app:
    forall (n: node) (m: node) (p: list node) (mid: node),
      Path n p m ->
      In mid p ->
      exists (l: list node) (r: list node),
        Path n (mid::l) mid
        /\
        p = r ++ [mid] ++ l.
  Proof.
    intros n m p mid Hpath Hin.
    induction Hpath.
    {
      inversion Hin; subst; [|inversion H].
      exists []. exists [].
      split; auto. constructor; auto.
    }
    {
      destruct (Pos.eq_dec mid to); subst.
      {
        exists p. exists [].
        split; auto.
        apply path_cons with (next := next); auto.
      }
      {
        destruct Hin.
        { symmetry in H. contradiction. }
        {
          apply IHHpath in H.
          destruct H as [l [r [Hpath' Happ]]].
          exists l. exists (to :: r).
          split; auto.
          rewrite <- app_comm_cons.
          rewrite Happ.
          reflexivity.
        }
      }
    }
  Qed.

  Theorem dom_trans:
    forall (n: node) (m: node) (p: node),
      Dominates n m -> Dominates m p -> Dominates n p.
  Proof.
    intros n m p Hnm Hmp.
    inversion Hmp; subst; auto.
    inversion Hnm; [subst; auto|].
    destruct (Pos.eq_dec m p); [subst; auto|].
    apply dom_path; auto.
    intros p' Hpath. remember Hpath as Hin; clear HeqHin. 
    apply PATH in Hin.
    generalize (in_path_split_app entry p p' m Hpath Hin); intros Hsplit.
    destruct Hsplit as [l [r [Hl Happ]]].
    rewrite Happ.
    apply in_or_app.
    right. apply PATH0. rewrite <- app_comm_cons. rewrite app_nil_l. auto.
  Qed.

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

  Theorem sdom_dominates:
    forall (n: node) (m: node),
      StrictlyDominates n m ->
      Dominates n m.
  Proof.
    intros n m Hsdom.
    inversion Hsdom.
    apply DOM.
  Qed.
End FUNCTION.

Lemma eq_cfg_reach:
  forall (f: func) (f': func),
    f.(fn_entry) = f'.(fn_entry) ->
    (forall (src: node) (dst: node), SuccOf f src dst <-> SuccOf f' src dst) ->
    forall (n: node),
      Reachable f n <-> Reachable f' n.
Proof.
  intros f f' Hentry Heq n.
  split; intros H.
  {
    induction H.
    { rewrite Hentry; constructor. }
    {
      apply reach_succ with (a := a); auto.
      apply Heq; auto.
    }
  }
  {
    induction H.
    { rewrite <- Hentry; constructor. }
    {
      apply reach_succ with (a := a); auto.
      apply Heq; auto.
    }
  }
Qed.

Lemma eq_cfg_path:
  forall (f: func) (f': func),
    f.(fn_entry) = f'.(fn_entry) ->
    (forall (src: node) (dst: node), SuccOf f src dst <-> SuccOf f' src dst) ->
    forall (src: node) (path: list node) (dst: node),
      Path f src path dst <-> Path f' src path dst.
Proof.
  intros f f' Hentry Heq src path dst.
  split; (intros H;induction H;
     [ apply path_nil;
       generalize (eq_cfg_reach f f' Hentry Heq n); intros Hr; apply Hr; auto
     | apply path_cons with (next := next); auto;
        [ generalize (eq_cfg_reach f f' Hentry Heq from); intros Hr; apply Hr; auto
        | apply Heq; auto
        ]
     ]).
Qed.

Lemma eq_cfg_dom:
  forall (f: func) (f': func),
    f.(fn_entry) = f'.(fn_entry) ->
    (forall (src: node) (dst: node), SuccOf f src dst <-> SuccOf f' src dst) ->
    forall (src: node) (dst: node),
      Dominates f src dst <-> Dominates f' src dst.
Proof.
  intros f f' Hentry Heq n.
  split; intros H.
  {
    induction H; constructor.
    {
      intros p Hpath. apply PATH.
      generalize (eq_cfg_path f f' Hentry Heq (entry f) p b); intros Hp; apply Hp.
      unfold entry; rewrite Hentry; auto.
    }
    {
      generalize (eq_cfg_reach f f' Hentry Heq b); intros Hr; apply Hr; auto.
    }
  }
  {
    induction H; constructor.
    {
      intros p Hpath. apply PATH.
      generalize (eq_cfg_path f f' Hentry Heq (entry f') p b); intros Hp; apply Hp.
      unfold entry; rewrite <- Hentry; auto.
    }
    {
      generalize (eq_cfg_reach f f' Hentry Heq b); intros Hr; apply Hr; auto.
    }
  }
Qed.