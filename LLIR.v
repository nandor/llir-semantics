(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Require Import LLIR.Maps.
Require Import LLIR.State.
Require Import LLIR.Values.

Import ListNotations.


Record object := mkobject
  { obj_size : positive
  ; obj_align: positive
  }.

Inductive ty : Type :=
  | I8
  | I16
  | I32
  | I64
  | I128
  | F32
  | F64
  | F80
  .

Inductive unop : Type :=
  | LLSext
  | LLZext
  | LLFext
  | LLXext
  | LLTrunc
  | LLNeg
  .

Inductive binop : Type :=
  | LLAdd
  | LLSub
  | LLMul
  | LLUDiv
  | LLSDiv
  | LLURem
  | LLSRem
  | LLCmp
  | LLSll
  | LLSra
  | LLSrl
  | LLXor
  | LLAnd
  | LLOr
  | LLRotl
  | LLUAddO
  | LLUMulO
  .

Inductive inst : Type :=
  | LLInvoke (callee: reg) (args: list reg) (dst: reg) (next: node) (exn: option node)
  | LLLd (addr: reg) (dst: reg) (next: node)
  | LLSt (addr: reg) (val: reg) (next: node)
  | LLArg (index: nat) (dst: reg) (next: node)
  | LLInt8 (value: INT8.t) (dst: reg) (next: node)
  | LLInt16 (value: INT16.t) (dst: reg) (next: node)
  | LLInt32 (value: INT32.t) (dst: reg) (next: node)
  | LLInt64 (value: INT64.t) (dst: reg) (next: node)
  | LLFrame (object: positive) (dst: reg) (next: node)
  | LLGlobal (object: positive) (dst: reg) (next: node)
  | LLExtern (id: positive) (next: node)
  | LLRet (value: reg)
  | LLRetVoid
  | LLJcc (cond: reg) (bt: node) (bf: node)
  | LLJmp (target: node)
  | LLUndef (ty: ty) (dst: reg) (next: node)
  | LLUnop (ty: ty) (op: unop) (arg: reg) (dst: reg) (next: node)
  | LLBinop (ty: ty) (op: binop) (lhs: reg) (rhs: reg) (dst: reg) (next: node)
  .

Inductive phi : Type :=
  | LLPhi (ins: list (node * reg)) (dst: reg)
  .

Definition phis := list phi.

Definition inst_map := PTrie.t inst.
Definition phi_map := PTrie.t phis.

Record func : Type := mkfunc
  { fn_stack: PTrie.t object
  ; fn_insts: inst_map
  ; fn_phis: phi_map
  ; fn_entry: node
  }.


Definition prog : Type := PTrie.t func.


Definition Defs (i: inst) (r: reg): Prop :=
  match i with
  | LLLd _ dst _ => dst = r
  | LLSt _ _ _ => False
  | LLArg _ dst _ => dst = r
  | LLInt8 _ dst _ => dst = r
  | LLInt16 _ dst _ => dst = r
  | LLInt32 _ dst _ => dst = r
  | LLInt64 _ dst _ => dst = r
  | LLFrame _ dst _ => dst = r
  | LLGlobal _ dst _ => dst = r
  | LLExtern _ _ => False
  | LLInvoke _ _ dst _ _ => dst = r
  | LLRet _ => False
  | LLRetVoid => False
  | LLJcc _ _ _ => False
  | LLJmp _ => False
  | LLUndef _ dst _ => dst = r
  | LLUnop _ _ _ dst _ => dst = r
  | LLBinop _ _ _ _ dst _ => dst = r
  end.

Definition PhiDefs (i: phi) (r: reg): Prop :=
  match i with
  | LLPhi _ dst => r = dst
  end.

Definition Uses (i: inst) (r: reg): Prop :=
  match i with
  | LLLd addr _ _ => addr = r
  | LLSt addr val _ => addr = r \/ val = r
  | LLArg _ _ _ => False
  | LLInt8 _ _ _ => False
  | LLInt16 _ _ _ => False
  | LLInt32 _ _ _ => False
  | LLInt64 _ _ _ => False
  | LLFrame _ _ _ => False
  | LLGlobal _ _ _ => False
  | LLExtern _ _ => False
  | LLInvoke callee args _ _ _ => callee = r \/ In r args
  | LLRet value => value = r
  | LLRetVoid => False
  | LLJcc cond _ _ => cond = r
  | LLJmp _ => False
  | LLUndef _ _ _ => False
  | LLUnop _ _ arg _ _ => arg = r
  | LLBinop _ _ lhs rhs _ _ => lhs = r \/ rhs = r
  end.

Definition Succeeds (i: inst) (succ: node): Prop :=
  match i with
  | LLLd _ _ next => next = succ
  | LLSt _ _ next => next = succ
  | LLArg _ _ next => next = succ
  | LLInt8 _ _ next => next = succ
  | LLInt16 _ _ next => next = succ
  | LLInt32 _ _ next => next = succ
  | LLInt64 _ _ next => next = succ
  | LLFrame _ _ next => next = succ
  | LLGlobal _ _ next => next = succ
  | LLExtern _ next => next = succ
  | LLInvoke _ _ _ next exn => next = succ \/ exn = Some succ
  | LLRet _ => False
  | LLRetVoid => False
  | LLJcc _ bt bf => bt = succ \/ bf = succ
  | LLJmp target => target = succ
  | LLUndef _ _ next => next = succ
  | LLUnop _ _ _ _ next => next = succ
  | LLBinop _ _ _ _ _ next => next = succ
  end.

Definition is_terminator (i: inst): bool :=
  match i with
  | LLInvoke _ _ _ _ _ => true
  | LLRet _ => true
  | LLRetVoid => true
  | LLJcc _ _ _ => true
  | LLJmp _ => true
  | LLLd _ _ _ => false
  | LLSt _ _ _ => false
  | LLArg _ _ _ => false
  | LLInt8 _ _ _ => false
  | LLInt16 _ _ _ => false
  | LLInt32 _ _ _ => false
  | LLInt64 _ _ _ => false
  | LLFrame _ _ _ => false
  | LLGlobal _ _ _ => false
  | LLExtern _ _ => false
  | LLUndef _ _ _ => false
  | LLUnop _ _ _ _ _ => false
  | LLBinop _ _ _ _ _ _ => false
  end.

Definition Terminator (i: inst): Prop :=
  is_terminator i = true.

Section FUNCTION.
  Variable f: func.

  Definition DefinedAt (n: node) (r: reg): Prop :=
    match f.(fn_insts) ! n with
    | None => False
    | Some inst => Defs inst r
    end.

  Definition PhiDefinedAt (n: node) (r: reg): Prop :=
    match f.(fn_phis) ! n with
    | None => False
    | Some phis => Exists (fun phi => PhiDefs phi r) phis
    end.

  Definition UsedAt (n: node) (r: reg): Prop :=
    match f.(fn_insts) ! n with
    | None => False
    | Some inst => Uses inst r
    end.

  Definition SuccOf (n: node) (m: node): Prop :=
    match f.(fn_insts) ! n, f.(fn_insts) ! m with
    | Some inst, Some _ => Succeeds inst m
    | _, _ => False
    end.

  Definition TermAt (n: node): Prop :=
    match f.(fn_insts) ! n with
    | None => False
    | Some inst => Terminator inst
    end.

End FUNCTION.

Definition get_successors (i: inst) :=
  match i with
  | LLLd _ _ next => [next]
  | LLSt _ _ next => [next]
  | LLArg _ _ next => [next]
  | LLInt8 _ _ next => [next]
  | LLInt16 _ _ next => [next]
  | LLInt32 _ _ next => [next]
  | LLInt64 _ _ next => [next]
  | LLFrame _ _ next => [next]
  | LLGlobal _ _ next => [next]
  | LLExtern _ next => [next]
  | LLInvoke _ _ _ next (Some exn) => [next; exn]
  | LLInvoke _ _ _ next _ => [next]
  | LLJcc _ bt bf => [bt; bf]
  | LLJmp target => [target]
  | LLUndef _ _ next => [next]
  | LLUnop _ _ _ _ next => [next]
  | LLBinop _ _ _ _ _ next => [next]
  | _ => []
  end.

Lemma get_successors_correct:
  forall (i: inst) (succ: node),
    In succ (get_successors i) <-> Succeeds i succ.
Proof.
  split.
  {
    intros Hin.
    unfold get_successors in Hin.
    unfold Succeeds.
    destruct i; try destruct exn;
    repeat (destruct Hin; destruct H; subst; try inversion H; auto).
  }
  {
    intros Hsucc.
    unfold Succeeds in Hsucc.
    unfold get_successors.
    destruct i; try destruct exn;
    try destruct Hsucc; try inversion H; subst; simpl; auto.
  }
Qed.

Definition get_predecessors (f: func) (n: node) :=
  match f.(fn_insts) ! n with
  | None => []
  | Some _ =>
    PTrie.keys
      (PTrie.filter (fun k v =>
        let succs := get_successors v in
        List.existsb (fun succ => Pos.eqb succ n) succs
      ) f.(fn_insts))
  end.

Lemma get_predecessors_correct:
  forall (f: func) (n: node) (pred: node),
    In pred (get_predecessors f n) <-> SuccOf f pred n.
Proof.
  intros f n pred.
  split.
  {
    intros Hin.
    unfold get_predecessors in Hin. unfold SuccOf. unfold Succeeds.
    destruct ((fn_insts f) ! n) eqn:Einst.
    {
      apply PTrie.keys_inversion in Hin.
      destruct Hin as [k Hin].
      apply PTrie.map_opt_inversion in Hin.
      destruct Hin as [inst [Hinst Hpred]].
      rewrite <- Hinst.
      unfold get_successors in Hpred. unfold existsb in Hpred.
      destruct inst; repeat match goal with
        | [ H: Pos.eqb ?v n = false |- _ ] =>
          clear H;
          simpl in *
        | [ H: Pos.eqb ?v n = true |- _ ] =>
          apply Pos.eqb_eq in H;
          subst n;
          simpl in Hpred;
          inversion Hpred;
          auto
        | [ H: context [ Pos.eqb ?v n ] |- _ ] =>
          destruct (Pos.eqb v n) eqn:E
        | [ H: Some ?v = None |- _ ] =>
          inversion H
        | [ H: context [ LLInvoke _ _ _ _ ?exn ] |- _ ] =>
          match exn with
          | context [ None ] => simpl
          | context [ Some ] => simpl
          | _ => destruct exn
          end
        end.
    }
    {
      inversion Hin.
    }
  }
  {
    intros Hsucc.
    unfold SuccOf in Hsucc.
    destruct ((fn_insts f) ! pred) as [inst|] eqn:Epred.
    {
      destruct ((fn_insts f) ! n) as [inst'|] eqn:En.
      {
        unfold Succeeds in Hsucc.
        unfold get_predecessors.
        rewrite En.
        destruct inst; try destruct exn; repeat match goal with
        | [ H: _ \/ _ |- _ ] =>
          destruct H
        | [ H: Some _ = Some _ |- _ ] =>
          inversion H; clear H
        | [ H: ?next = n |- _ ] =>
          apply PTrie.values_correct with (k := next)
        | [ H: (fn_insts f) ! pred = Some ?inst |- _ ] =>
          apply PTrie.keys_correct with (v := inst);
          apply PTrie.filter_correct;
            [ symmetry; apply Epred
            | apply List.existsb_exists; exists n;
              split;
              [ simpl; auto
              | apply Pos.eqb_refl
              ]
            ]
        end.
        inversion H.
      }
      {
        inversion Hsucc.
      }
    }
    {
      inversion Hsucc.
    }
  }
Qed.
