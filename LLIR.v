(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Require Import LLIR.Maps.
Require Import LLIR.State.
Require Import LLIR.Values.



Record object := mkobject
  { obj_size : positive
  ; align: positive
  }.

Inductive unop : Type :=
  | LLSext
  | LLZext
  | LLTrunc
  .

Inductive binop : Type :=
  | LLAdd
  | LLSub
  | LLCmp
  | LLSll
  | LLSra
  | LLSrl
  | LLXor
  | LLAnd
  | LLOr
  .

Inductive inst : Type :=
  | LLLd (addr: reg) (dst: reg) (next: node)
  | LLSt (addr: reg) (val: reg) (next: node)
  | LLArg (index: positive) (dst: reg) (next: node)
  | LLConst (value: qword) (dst: reg) (next: node)
  | LLFrame (object: positive) (dst: reg) (next: node)
  | LLGlobal (object: positive) (dst: reg) (next: node)
  | LLExtern (id: positive) (next: node)
  | LLInvoke (callee: reg) (args: list reg) (dst: reg) (next: node) (exn: node)
  | LLRet (value: reg)
  | LLJcc (cond: reg) (bt: node) (bf: node)
  | LLJmp (target: node)
  | LLUnop (op: unop) (arg: reg) (dst: reg) (next: node)
  | LLBinop (op: binop) (lhs: reg) (rhs: reg) (dst: reg) (next: node)
  .

Inductive phi : Type := LLPhi : list reg -> reg -> phi.

Definition phis := list phi.

Definition inst_map := PTrie.t inst.
Definition phi_map := PTrie.t phis.

Record func : Type := mkfunc
  { fn_args: positive
  ; fn_stack: PTrie.t object
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

Section FUNCTION.
  Variable f: func.

  Definition DefinedAt (n: node) (r: reg): Prop :=
    match f.(fn_insts) ! n with
    | None => False
    | Some inst => Defs inst r
    end.

  Definition UsedAt (n: node) (r: reg): Prop :=
    match f.(fn_insts) ! n with
    | None => False
    | Some inst => Uses inst r
    end.
End FUNCTION.