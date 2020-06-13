(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import FunInd.
Require Import Recdef.

Require Import LLIR.Dom.
Require Import LLIR.LLIR.
Require Import LLIR.Values.
Require Import LLIR.Maps.

Import ListNotations.

Section FUNCTION.
  Variable f: func.

  Definition entry: node := f.(fn_entry).

  Inductive BasicBlockHeader: node -> Prop :=
    | block_header:
      forall (header: node)
        (REACH: Reachable f header)
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
        (NOT_PREV: prev <> elem)
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
      BasicBlock header elem -> Reachable f elem.
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

  Theorem bb_is_header:
    forall (header: node),
      BasicBlock header header -> BasicBlockHeader header.
  Proof.
    intros header Hbb.
    inversion Hbb; auto; contradiction.
  Qed.

  Theorem bb_header_dom_nodes:
    forall (header: node) (elem: node),
      BasicBlock header elem -> Dominates f header elem.
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

  Theorem bb_elem_pred:
    forall (header: node) (elem: node),
      BasicBlock header elem ->
        BasicBlockHeader elem
        \/
        forall (prev: node),
          SuccOf f prev elem ->
            BasicBlock header prev /\ Dominates f prev elem.
  Proof.
    intros header elem Hblock.
    inversion Hblock.
    { left. auto. }
    {
      right.
      intros prev' Hsucc.
      apply UNIQ in Hsucc.
      subst prev'.
      split; auto.
      apply dom_path.
      {
        intros p Hpath.
        inversion Hpath; subst. contradiction.
        right.
        apply UNIQ in HD. subst next.
        apply (last_in_path f) with (x := entry). apply TL.
      }
      {
        apply reach_succ with (a := prev). apply PRED.
        apply bb_reaches with (header := header). apply BLOCK.
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
        (REACH: Reachable f n)
        (HEADER: BasicBlockHeader n),
        BasicBlockPath n [n] n
    | bb_path_cons:
      forall (from: node) (next: node) (to: node) (p: list node)
        (REACH: Reachable f from)
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
        (REACH: Reachable f b),
        BasicBlockDominates a b
    .

  Theorem bb_dom_dom:
    forall (n: node) (m: node),
      BasicBlockDominates n m -> Dominates f n m.
  Admitted.

  Theorem bb_elem_dom:
    forall (h: node) (e: node) (h': node) (e': node),
      h <> h' ->
      BasicBlock h e ->
      BasicBlock h' e' ->
      BasicBlockDominates h h' ->
      Dominates f e e'.
  Admitted.

  Theorem bb_elem_not_header:
    forall (h: node) (e: node),
      BasicBlock h e ->
      BasicBlockHeader e ->
      h = e.
  Proof.
    intros h e Hbb Hheader.
    inversion Hbb; auto.
    subst header elem.
    inversion Hheader.
    apply TERM in PRED.
    contradiction.
  Qed.

  Inductive SuccOfElem: node -> node -> Prop :=
    | succ_of_elem:
      forall (h: node) (n: node) (m: node)
        (NH: m <> h)
        (NE: n <> m)
        (BN: BasicBlock h n)
        (BM: BasicBlock h m)
        (SUCC: SuccOf f n m),
        SuccOfElem n m
    .

  Inductive PathToElem: node -> list node -> node -> Prop :=
    | path_elem_header:
      forall (n: node)
        (HEADER: BasicBlockHeader n),
        PathToElem n [n] n
    | path_elem_cons:
      forall (header: node) (prev: node) (elem: node) (p: list node)
        (TL: SuccOfElem prev elem)
        (HD: PathToElem header p prev)
        (NH: header <> elem),
        PathToElem header (elem :: p) elem
    .

  Theorem bb_path_to_elem:
    forall (h: node) (e: node),
      BasicBlock h e ->
        exists (p: list node), PathToElem h p e.
  Proof.
    intros h e Hbb.
    induction Hbb.
    {
      exists [header].
      apply path_elem_header.
      auto.
    }
    {
      destruct IHHbb as [p Hpath].
      exists (elem :: p).
      apply path_elem_cons with (prev := prev); auto.
      apply succ_of_elem with (h := header); auto.
      apply bb_elem with (prev := prev); auto.
    }
  Qed.

  Theorem bb_path_bb:
    forall (h: node) (e: node) (p: list node),
      PathToElem h p e -> BasicBlock h e.
  Proof.
    intros h e p Hpath.
    induction Hpath.
    + constructor; auto.
    + inversion TL.
      generalize (bb_header_unique prev header h IHHpath BN); intros Heq; subst.
      apply bb_elem with (prev := prev);
        inversion BM; subst; auto; try contradiction.
      - apply UNIQ in SUCC; subst prev0; auto.
      - intros prev' Hsucc.
        apply UNIQ in Hsucc; subst prev'.
        apply UNIQ in SUCC; subst prev.
        reflexivity.
  Qed.

  Theorem bb_path_no_loop:
    forall (h: node) (p: list node),
      PathToElem h p h -> p = [h].
  Proof.
    intros h p Hpath.
    inversion Hpath; auto.
    subst. contradiction.
  Qed.

  Theorem bb_path_no_term:
    forall (h: node) (e: node) (p: list node),
      PathToElem h p e ->
        forall (n: node),
          In n p -> n = e \/ ~TermAt f n.
  Proof.
    intros h e p Hpath.
    induction Hpath; intros n' Hin.
    inversion Hin; auto.
    destruct Hin; auto.
    generalize (IHHpath n' H). intros Hind. clear IHHpath.
    destruct Hind; auto.
    inversion TL.
    inversion BN; inversion BM; subst.
    - contradiction.
    - apply UNIQ in SUCC; subst; auto.
    - contradiction.
    - right. apply UNIQ0 in SUCC; subst; auto.
  Qed.

  Theorem bb_path_uniq:
    forall (h: node) (e: node) (p: list node) (p': list node),
      PathToElem h p e ->
      PathToElem h p' e ->
      p = p'.
  Proof.
    intros h e p p' Hp. generalize dependent p'.
    induction Hp; intros p' Hp'.
    symmetry; apply bb_path_no_loop; auto.
    inversion Hp'; subst; try contradiction.
    inversion TL; inversion TL0; inversion BM; subst; try contradiction.
    apply UNIQ in SUCC; subst.
    apply UNIQ in SUCC0; subst.
    apply IHHp in HD; subst p0.
    reflexivity.
  Qed.

  Definition get_bb_pred (e: node): option node :=
    match get_predecessors f e with
    | [p] =>
      match f.(fn_insts) ! p with
      | Some inst => if is_terminator inst then None else Some p
      | None => None
      end
    | _ => None
    end.

  Theorem bb_header_has_no_predecessor:
    forall (h: node),
      BasicBlockHeader h ->
      get_bb_pred h = None.
  Proof.
    intros h Hbb.
    inversion Hbb.
    unfold get_bb_pred.
    remember (get_predecessors f h) as some_pred eqn:Esome_pred.
    destruct some_pred; auto.
    destruct some_pred; auto.
    assert (Hk: SuccOf f k h).
    {
      apply get_predecessors_correct.
      rewrite <- Esome_pred.
      left; reflexivity.
    }
    inversion Hk.
    rewrite <- HN.
    apply TERM in Hk.
    inversion Hk.
    rewrite <- HN in INST0; inversion INST0; subst i0.
    inversion TERM0; simpl; reflexivity.
  Qed.

  Theorem bb_elem_has_predecessor:
    forall (h: node) (e: node),
      BasicBlock h e ->
      h <> e ->
      exists (p: node), Some p = get_bb_pred e.
  Proof.
    intros h e Hbb Hne.
    inversion Hbb; try contradiction.
    exists prev.
    unfold get_bb_pred.
    remember (get_predecessors f e) as some_pred eqn:Esome_pred.
    destruct some_pred.
    {
      apply get_predecessors_correct in PRED.
      rewrite <- Esome_pred in PRED.
      inversion PRED.
    }
    {
      assert (Hk: SuccOf f k e).
      {
        apply get_predecessors_correct.
        rewrite <- Esome_pred.
        left. reflexivity.
      }
      destruct some_pred.
      {
        inversion Hk. apply UNIQ in Hk. rewrite <- HN.
        inversion SUCC; simpl; subst k; try reflexivity;
        (assert (TermAt f prev);
        [ apply term_at with (i := i); auto; subst i; constructor
        | contradiction
        ]).
      }
      {
        assert (Hk0: SuccOf f k0 e).
        {
          apply get_predecessors_correct.
          rewrite <- Esome_pred.
          right. left.  reflexivity.
        }
        apply UNIQ in Hk; subst k.
        apply UNIQ in Hk0; subst k0.
        unfold get_predecessors in Esome_pred.
        destruct ((fn_insts f) ! e) eqn:E; try contradiction.
        assert (Hdup: NoDup (prev :: prev :: some_pred)).
        { unfold PTrie.key in *. rewrite Esome_pred. apply PTrie.keys_nodup. }
        apply NoDup_cons_iff in Hdup. destruct Hdup as [Hdup _].
        assert (Hcontra: In prev (prev :: some_pred)).
        { left. reflexivity. }
        contradiction.
      }
    }
  Qed.

  Theorem bb_elem_not_self:
    forall (h: node) (e: node) (p: node),
      BasicBlock h e ->
      Some p = get_bb_pred e ->
      p <> e.
  Proof.
    intros h e p Hblock Hsome contra.
    subst p.
    unfold get_bb_pred in Hsome.
    remember (get_predecessors f e) as preds.
    destruct preds; [inversion Hsome|].
    destruct preds; [|inversion Hsome].
    destruct ((fn_insts f) ! k) as [inst_k|] eqn:Einst_k; [|inversion Hsome].
    assert (Hsucc: SuccOf f k e).
    { apply get_predecessors_correct. rewrite <- Heqpreds. left. reflexivity. }
    inversion Hblock; subst.
    {
      inversion HEADER.
      apply TERM in Hsucc.
      inversion Hsucc.
      rewrite Einst_k in INST0; inversion INST0; subst i.
      inversion TERM0; subst; simpl in Hsome; inversion Hsome.
    }
    {
      apply UNIQ in Hsucc; subst k.
      unfold is_terminator in Hsome.
      destruct inst_k; inversion Hsome; subst e; contradiction.
    }
  Qed.

  Theorem get_bb_pred_succ:
    forall (n: reg) (m: reg),
      get_bb_pred n = Some m -> SuccOf f m n.
  Proof.
    intros n m Hpred. unfold get_bb_pred in Hpred.
    remember (get_predecessors f n) as preds.
    destruct preds; [inversion Hpred|].
    destruct preds; [|inversion Hpred].
    destruct ((fn_insts f) ! k) as [pred|] eqn:Epred; [|inversion Hpred].
    destruct pred; inversion Hpred; clear Hpred; subst k;
    apply get_predecessors_correct;
    rewrite <- Heqpreds;
    left; reflexivity.
  Qed.

  Hypothesis has_header:
    forall (e: node),
      (exists (h: node), BasicBlock h e) \/ (f.(fn_insts) ! e = None).

  Theorem  get_bb_pred_succ_of_elem:
    forall (n: node) (m: node),
      get_bb_pred n = Some m -> SuccOfElem m n.
  Proof.
    intros n m Hget.
    unfold get_bb_pred in Hget.
    remember (get_predecessors f n) as preds eqn:H.
    destruct preds; [inversion Hget|].
    destruct preds; [|inversion Hget].
    destruct ((fn_insts f) ! k) as [inst_k|] eqn:Einst_k; [|inversion Hget].
    assert (Hkm: k = m).
    { destruct inst_k; simpl in Hget; inversion Hget; reflexivity. }
    subst k.
    generalize (has_header n); intros Hheader.
    assert (Hsucc: SuccOf f m n).
    { apply get_predecessors_correct. rewrite <- H. left. reflexivity. }
    destruct Hheader as [[h Hbb]|Hnone].
    {
      inversion Hbb; subst.
      {
        inversion HEADER. apply TERM in Hsucc.
        inversion Hsucc.
        rewrite Einst_k in INST0; inversion INST0; clear INST0; subst i.
        inversion TERM0; subst inst_k; simpl in Hget; inversion Hget.
      }
      {
        apply succ_of_elem with (h := h); auto.
        {
          apply (bb_elem_not_self h); auto.
          unfold get_bb_pred.
          rewrite <- H; rewrite Einst_k; rewrite Hget; reflexivity.
        }
        { apply UNIQ in Hsucc; subst m; auto. }
      }
    }
    {
      unfold get_predecessors in H. rewrite Hnone in H. inversion H.
    }
  Defined.

  Theorem succ_of_elem_wf: well_founded SuccOfElem.
  Proof.
    intros n.
    generalize (has_header n); intros Hgraph; destruct Hgraph as [Hbb|Hnone].
    {
      destruct Hbb as [h Hbb].
      induction Hbb.
      {
        constructor. intros y Hsucc.
        inversion Hsucc; clear Hsucc; inversion HEADER; subst.
        inversion SUCC.
        inversion HEADER; subst.
        inversion BM; subst.
        { inversion HEADER0; subst; contradiction. }
        { apply TERM in PRED; contradiction. }
      }
      {
        constructor. intros y Hsucc.
        assert (Hprevy: y = prev).
        { apply UNIQ; inversion Hsucc; auto. }
        subst y.
        apply IHHbb.
      }
    }
    {
      constructor.
      intros pred Hr.
      inversion Hr; subst.
      inversion BM.
      { inversion HEADER; contradiction. }
      { contradiction. }
    }
  Defined.

  Function get_header (n: node) { wf SuccOfElem n }: node :=
    match get_bb_pred n with
    | Some n' => get_header n'
    | None => n
    end.
    { apply get_bb_pred_succ_of_elem. }
    { apply succ_of_elem_wf. }
  Qed.

  Function get_inst_index (n: node) { wf SuccOfElem n}: nat :=
    match get_bb_pred n with
    | Some n' => S (get_inst_index n')
    | None => 0
    end.
    { apply get_bb_pred_succ_of_elem. }
    { apply succ_of_elem_wf. }
  Qed.

  Theorem header_index_0:
    forall (h: node),
      BasicBlockHeader h -> get_inst_index h = 0.
  Proof.
    intros h Hbb.
    rewrite get_inst_index_equation.
    apply bb_header_has_no_predecessor in Hbb.
    rewrite Hbb.
    reflexivity.
  Qed.
End FUNCTION.
