(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.ZArith.ZArith.

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
