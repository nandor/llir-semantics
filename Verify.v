(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Require Import LLIR.State.
Require Import LLIR.LLIR.
Require Import LLIR.Maps.

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.

Import ListNotations.



Definition Defs (i: inst) (r: reg): Prop :=
  match i with
  | LLLd _ dst _ => dst = r
  | LLSt _ _ _ => False
  | LLArg _ dst _ => dst = r
  | LLConst _ dst _ => dst = r
  | LLFrame _ dst _ => dst = r
  | LLGlobal _ dst _ => dst = r
  | LLExtern _ _ => False
  | LLInvoke _ _ dst _ _ => dst = r
  | LLRet _ => False
  | LLJcc _ _ _ => False
  | LLJmp _ => False
  | LLUnop _ _ dst _ => dst = r
  | LLBinop _ _ _ dst _ => dst = r
  end.

Definition Uses (i: inst) (r: reg): Prop :=
  match i with
  | LLLd addr _ _ => addr = r
  | LLSt addr val _ => addr = r \/ val = r
  | LLArg _ _ _ => False
  | LLConst _ _ _ => False
  | LLFrame _ _ _ => False
  | LLGlobal _ _ _ => False
  | LLExtern _ _ => False
  | LLInvoke callee args _ _ _ => callee = r \/ In r args
  | LLRet value => value = r
  | LLJcc cond _ _ => cond = r
  | LLJmp _ => False
  | LLUnop _ arg _ _ => arg = r
  | LLBinop _ lhs rhs _ _ => lhs = r \/ rhs = r
  end.

Definition SuccessorOfInst (i: inst) (succ: node): Prop :=
  match i with
  | LLLd _ _ next => next = succ
  | LLSt _ _ next => next = succ
  | LLArg _ _ next => next = succ
  | LLConst _ _ next => next = succ
  | LLFrame _ _ next => next = succ
  | LLGlobal _ _ next => next = succ
  | LLExtern _ next => next = succ
  | LLInvoke _ _ _ next exn => next = succ \/ exn = succ
  | LLRet _ => False
  | LLJcc _ bt bf => bt = succ \/ bf = succ
  | LLJmp target => target = succ
  | LLUnop _ _ _ next => next = succ
  | LLBinop _ _ _ _ next => next = succ
  end.

Section Dominator.
  Variable f: func.
  
  Definition entry: node := f.(fn_entry).

  Inductive Succ: node -> node -> Prop :=
    | succ_dir:
      forall (from: node) (to: node) (i: inst),
        Some i = PTrie.get f.(fn_insts) from ->
        SuccessorOfInst i to -> 
        Succ from to
    .

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
      forall (a: node) (b:node)
        (PATH: forall (p: list node), Path entry p b -> In a p)
        (REACH: Reachable a),
        Dominates a b.

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

End Dominator.

Definition is_valid (f: func): Prop :=
  forall (def: node) (use: node) (defr: inst) (user: inst) (r: reg),
    Some defr = PTrie.get f.(fn_insts) def ->
    Some user = PTrie.get f.(fn_insts) use ->
    Defs defr r ->
    Uses user r ->
    Dominates f def use.
