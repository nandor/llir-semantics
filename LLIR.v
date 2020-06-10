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

Inductive ty_int: Type :=
  | I8
  | I16
  | I32
  | I64
  | I128
  .

Inductive ty_float: Type :=
  | F32
  | F64
  | F80
  .

Inductive ty : Type :=
  | TInt (i: ty_int)
  | TFloat (f: ty_float)
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
  | LLLd (dst: (ty * reg)) (next: node) (addr: reg)
  | LLArg (dst: (ty * reg)) (next: node) (index: nat)
  | LLInt8 (dst: reg) (next: node) (value: INT8.t)
  | LLInt16 (dst: reg) (next: node) (value: INT16.t)
  | LLInt32 (dst: reg) (next: node) (value: INT32.t)
  | LLInt64 (dst: reg) (next: node) (value: INT64.t)
  | LLMov (dst: (ty * reg)) (next: node) (src: reg)
  | LLSelect (dst: (ty * reg)) (next: node) (cond: reg) (vt: reg) (vf: reg)
  | LLFrame (dst: reg) (next: node) (object: positive) (offset: nat)
  | LLGlobal (dst: reg) (next: node) (object: positive) (offset: nat)
  | LLUndef (dst: (ty * reg)) (next: node)
  | LLUnop (dst: (ty * reg)) (next: node) (op: unop) (arg: reg)
  | LLBinop (dst: (ty * reg)) (next: node) (op: binop) (lhs: reg) (rhs: reg)
  | LLSyscall (dst: reg) (next: node) (sno: reg) (args: list reg)
  | LLCall (dst: option (ty * reg)) (next: node) (callee: reg) (args: list reg)
  | LLInvoke (dst: option (ty * reg)) (next: node) (callee: reg) (args: list reg) (exn: node)
  | LLTCall (callee: reg) (args: list reg)
  | LLTInvoke (callee: reg) (args: list reg) (exn: node)
  | LLSt (next: node) (addr: reg) (val: reg)
  | LLRet (value: option reg)
  | LLJcc (cond: reg) (bt: node) (bf: node)
  | LLJmp (target: node)
  | LLTrap
  .

Inductive phi : Type :=
  | LLPhi (dst: (ty * reg)) (ins: list (node * reg))
  .

Definition inst_map := PTrie.t inst.
Definition phi_map := PTrie.t (list phi).

Record func : Type := mkfunc
  { fn_stack: PTrie.t object
  ; fn_insts: inst_map
  ; fn_phis: phi_map
  ; fn_entry: node
  }.


Definition prog : Type := PTrie.t func.


Definition InstDefs (i: inst) (r: reg): Prop :=
  match i with
  | LLLd (_, dst) _ _ => dst = r
  | LLArg (_, dst) _ _ => dst = r
  | LLInt8 dst _ _ => dst = r
  | LLInt16 dst _ _ => dst = r
  | LLInt32 dst _ _ => dst = r
  | LLInt64 dst _ _ => dst = r
  | LLMov (_, dst) _ _ => dst = r
  | LLFrame dst _ _ _ => dst = r
  | LLGlobal dst _ _ _ => dst = r
  | LLUndef (_, dst) _ => dst = r
  | LLUnop (_, dst) _ _ _ => dst = r
  | LLBinop (_, dst) _ _ _ _ => dst = r
  | LLSelect (_, dst) _ _ _ _ => dst = r
  | LLSyscall dst _ _ _ => dst = r
  | LLCall ret _ _ _ =>
    match ret with
    | None => False
    | Some (_, dst) => dst = r
    end
  | LLInvoke ret _ _ _ _ =>
    match ret with
    | None => False
    | Some (_, dst) => dst = r
    end
  | LLTCall _ _ => False
  | LLTInvoke _ _ _ => False
  | LLSt _ _ _ => False
  | LLRet _ => False
  | LLJcc _ _ _ => False
  | LLJmp _ => False
  | LLTrap => False
  end.


Definition PhiDefs (i: phi) (r: reg): Prop :=
  match i with
  | LLPhi (_, dst) _ => r = dst
  end.

Definition InstUses (i: inst) (r: reg): Prop :=
  match i with
  | LLLd _ _ addr => addr = r
  | LLArg _ _ _ => False
  | LLInt8 _ _ _ => False
  | LLInt16 _ _ _ => False
  | LLInt32 _ _ _ => False
  | LLInt64 _ _ _ => False
  | LLMov _ _ src => src = r
  | LLFrame _ _ _ _ => False
  | LLGlobal _ _ _ _ => False
  | LLUndef _ _ => False
  | LLUnop _ _ _ arg => arg = r
  | LLBinop _ _ _ lhs rhs => lhs = r \/ rhs = r
  | LLSelect _ _ cond vt vf => cond = r \/ vt = r \/ vf = r
  | LLSyscall _ _ sno args => sno = r \/ In r args
  | LLCall _ _ callee args => callee = r \/ In r args
  | LLInvoke _ _ callee args _ => callee = r \/ In r args
  | LLTCall callee args => callee = r \/ In r args
  | LLTInvoke callee args _ => callee = r \/ In r args
  | LLSt _ addr val => addr = r \/ val = r
  | LLRet value =>
    match value with
    | None => False
    | Some value' => value' = r
    end
  | LLJcc cond _ _ => cond = r
  | LLJmp _ => False
  | LLTrap => False
  end.

Definition PhiUses (p: phi) (n: reg) (r: reg): Prop :=
  match p with
  | LLPhi _ ins => Exists (fun phi_in =>
    match phi_in with
    | (n', r') => n' = n /\ r' = r
    end) ins
  end.

Definition PhiBlockUses (phis: list phi) (n: node) (r: reg): Prop :=
  Exists (fun phi => PhiUses phi n r) phis.

Definition Succeeds (i: inst) (succ: node): Prop :=
  match i with
  | LLLd _ next _ => next = succ
  | LLArg _ next _ => next = succ
  | LLInt8 _ next _ => next = succ
  | LLInt16 _ next _ => next = succ
  | LLInt32 _ next _ => next = succ
  | LLInt64 _ next _ => next = succ
  | LLMov _ next _ => next = succ
  | LLFrame _ next _ _ => next = succ
  | LLGlobal _ next _ _ => next = succ
  | LLUndef _ next => next = succ
  | LLUnop _ next _ _ => next = succ
  | LLBinop _ next _ _ _ => next = succ
  | LLSelect _ next _ _ _ => next = succ
  | LLSyscall _ next _ _ => next = succ
  | LLCall _ next _ _ => next = succ
  | LLInvoke _ next _ _ exn => next = succ \/ exn = succ
  | LLTCall _ _ => False
  | LLTInvoke _ _ exn => exn = succ
  | LLSt next _ _ => next = succ
  | LLRet _ => False
  | LLJcc _ bt bf => bt = succ \/ bf = succ
  | LLJmp target => target = succ
  | LLTrap => False
  end.

Definition is_terminator (i: inst): bool :=
  match i with
  | LLLd _ _ _ => false
  | LLArg _ _ _ => false
  | LLInt8 _ _ _ => false
  | LLInt16 _ _ _ => false
  | LLInt32 _ _ _ => false
  | LLInt64 _ _ _ => false
  | LLMov _ _ _ => false
  | LLFrame _ _ _ _ => false
  | LLGlobal _ _ _ _ => false
  | LLUndef _ _ => false
  | LLUnop _ _ _ _ => false
  | LLBinop _ _ _ _ _ => false
  | LLSelect _ _ _ _ _ => false
  | LLSyscall _ _ _ _ => false
  | LLCall _ _ _ _ => false
  | LLInvoke _ _ _ _ _ => true
  | LLTCall _ _ => true
  | LLTInvoke _ _ _ => true
  | LLSt next _ _ => false
  | LLRet _ => true
  | LLJcc _ _ _ => true
  | LLJmp _ => true
  | LLTrap => true
  end.

Definition Terminator (i: inst): Prop :=
  is_terminator i = true.

Section FUNCTION.
  Variable f: func.

  Inductive DefinedAt: node -> reg -> Prop :=
    | defined_at_inst:
      forall (n: node) (r: reg) (i: inst)
        (INST: Some i = f.(fn_insts) ! n)
        (DEFS: InstDefs i r),
        DefinedAt n r
    | defined_at_phi:
      forall (n: node) (r: reg) (phis: list phi)
        (PHIS: Some phis = f.(fn_phis) ! n)
        (DEFS: Exists (fun phi => PhiDefs phi r) phis),
        DefinedAt n r
    .

  Inductive UsedAt: node -> reg -> Prop :=
    | used_at_inst:
      forall (n: node) (r: reg) (i: inst)
        (INST: Some i = f.(fn_insts) ! n)
        (USES: InstUses i r),
        UsedAt n r
    | used_at_phi:
      forall (n: node) (r: reg) (block: node) (phis: list phi)
        (PHIS: Some phis = f.(fn_phis) ! block)
        (USES: PhiBlockUses phis n r),
        UsedAt n r
    .

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
  | LLLd _ next _ => [next]
  | LLArg _ next _ => [next]
  | LLInt8 _ next _ => [next]
  | LLInt16 _ next _ => [next]
  | LLInt32 _ next _ => [next]
  | LLInt64 _ next _ => [next]
  | LLMov _ next _ => [next]
  | LLFrame _ next _ _ => [next]
  | LLGlobal _ next _ _ => [next]
  | LLUndef _ next => [next]
  | LLUnop _ next _ _ => [next]
  | LLBinop _ next _ _ _ => [next]
  | LLSelect _ next _ _ _ => [next]
  | LLSyscall _ next _ _ => [next]
  | LLCall _ next _ _ => [next]
  | LLInvoke _ next _ _ exn => [next; exn]
  | LLTCall _ _ => []
  | LLTInvoke _ _ exn => [exn]
  | LLSt next _ _ => [next]
  | LLRet _ => []
  | LLJcc _ bt bf => [bt;bf]
  | LLJmp target => [target]
  | LLTrap => []
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
    destruct i;
    repeat (destruct Hin; destruct H; subst; try inversion H; auto).
  }
  {
    intros Hsucc.
    unfold Succeeds in Hsucc.
    unfold get_successors.
    destruct i;
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
    destruct ((fn_insts f) ! pred) as [inst|] eqn:Epred; [|inversion Hsucc].
    destruct ((fn_insts f) ! n) as [inst'|] eqn:En; [|inversion Hsucc].
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
  }
Qed.
