(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Values.
Require Import LLIR.
Require Import State.
Require Import Maps.
Require Import Coq.Lists.List.

Import ListNotations.

Inductive trace: Type.

Inductive frame: Type :=
  | Frame:
    forall
      (f: func)
      (ret_pc: node)
      (vregs: PTrie.t value),
        frame.

Definition stk_state := list frame.

Axiom mem_state: Type.

Inductive state: Type :=
  | State:
      forall
        (stk: stk_state)
        (mem: mem_state)
        (pc: node),
        state
  .

Definition get_inst (stk: stk_state) (pc: node): option inst :=
  match stk with
  | (Frame f _ _) :: _ => f.(fn_insts) ! pc
  | _ => None
  end.

Axiom get_vreg: stk_state -> reg -> option value.

Axiom set_vreg: stk_state -> reg -> value -> option stk_state.

Axiom is_true: value -> Prop.

Axiom is_false: value -> Prop.

Axiom eval_unop: ty -> unop -> value -> option value.

Axiom eval_binop: ty -> binop -> value -> value -> option value.

Inductive step: state -> trace -> state -> Prop :=
  | eval_jmp:
    forall
      (stk: stk_state) (mem: mem_state) (tr: trace)
      (pc: node)
      (target: node),
      get_inst stk pc = Some (LLJmp target) ->
      step
        (State stk mem pc)
        tr
        (State stk mem target)
  | eval_jcc_true:
    forall
      (stk: stk_state) (mem: mem_state) (tr: trace)
      (pc: node)
      (cond: reg) (brancht: node) (branchf: node)
      (v: value),
      get_inst stk pc = Some (LLJcc cond brancht branchf) ->
      get_vreg stk cond = Some v ->
      is_true v ->
      step
        (State stk mem pc)
        tr
        (State stk mem brancht)
  | eval_jcc_false:
    forall
      (stk: stk_state) (mem: mem_state) (tr: trace)
      (pc: node)
      (cond: reg) (brancht: node) (branchf: node)
      (v: value),
      get_inst stk pc = Some (LLJcc cond brancht branchf) ->
      get_vreg stk cond = Some v ->
      is_false v ->
      step
        (State stk mem pc)
        tr
        (State stk mem brancht)
  | eval_unary:
    forall
      (stk: stk_state) (mem: mem_state) (tr: trace)
      (pc: node)
      (ty: ty) (op: unop) (arg: reg) (dst: reg) (next: node)
      (arg_value: value) (dst_value: value)
      (stk': stk_state),
      get_inst stk pc = Some (LLUnop ty op arg dst next) ->
      get_vreg stk arg = Some arg_value ->
      eval_unop ty op arg_value = Some dst_value ->
      set_vreg stk dst dst_value = Some stk' ->
      step
        (State stk mem pc)
        tr
        (State stk' mem next)
  | eval_binary:
    forall
      (stk: stk_state) (mem: mem_state) (tr: trace)
      (pc: node)
      (ty: ty) (op: binop) (lhs: reg) (rhs: reg) (dst: reg) (next: node)
      (lhs_value: value) (rhs_value: value) (dst_value: value)
      (stk': stk_state),
      get_inst stk pc = Some (LLBinop ty op lhs rhs dst next) ->
      get_vreg stk lhs = Some lhs_value ->
      get_vreg stk rhs = Some rhs_value ->
      eval_binop ty op lhs_value rhs_value = Some dst_value ->
      set_vreg stk dst dst_value = Some stk' ->
      step
        (State stk mem pc)
        tr
        (State stk' mem next)
  .

  (*
  | LLConst (value: qword) (dst: reg) (next: node)

  | LLLd (addr: reg) (dst: reg) (next: node)
  | LLSt (addr: reg) (val: reg) (next: node)

  | LLArg (index: positive) (dst: reg) (next: node)

  | LLFrame (object: positive) (dst: reg) (next: node)
  | LLGlobal (object: positive) (dst: reg) (next: node)
  | LLExtern (id: positive) (next: node)

  | LLCall (callee: reg) (args: list reg) (dst: reg) (next: node)
  | LLInvoke (callee: reg) (args: list reg) (dst: reg) (next: node) (exn: node)

  | LLRet (value: reg)
  *)
