(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Require Import LLIR.Values.
Require Import LLIR.Maps.
Require Import LLIR.LLIR.
Require Import LLIR.Dom.
Require Import LLIR.Eval.
Require Import LLIR.SSA.
Require Import LLIR.Block.

Import ListNotations.



Inductive event: Type.

Definition trace := list event.

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

Definition get_inst (p: prog) (stk: stk_state) (pc: node): option inst :=
  match stk with
  | f :: _ =>
    match p ! (f.(fr_func)) with
    | Some func => func.(fn_insts) ! pc
    | None => None
    end
  | _ => None
  end.

Axiom get_vreg: stk_state -> reg -> option value.

Axiom set_vreg: stk_state -> reg -> value -> option stk_state.

Axiom is_true: value -> Prop.

Axiom is_false: value -> Prop.

Axiom eval_unop: ty -> unop -> value -> option value.

Axiom eval_binop: ty -> binop -> value -> value -> option value.

Inductive step (p: prog): state -> trace -> state -> Prop :=
  | eval_jmp:
    forall
      (stk: stk_state) (mem: mem_state) (tr: trace)
      (pc: node)
      (target: node),
      get_inst p stk pc = Some (LLJmp target) ->
      step
        p
        (State stk mem pc)
        tr
        (State stk mem target)
  | eval_jcc_true:
    forall
      (stk: stk_state) (mem: mem_state) (tr: trace)
      (pc: node)
      (cond: reg) (brancht: node) (branchf: node)
      (v: value),
      get_inst p stk pc = Some (LLJcc cond brancht branchf) ->
      get_vreg stk cond = Some v ->
      is_true v ->
      step
        p
        (State stk mem pc)
        tr
        (State stk mem brancht)
  | eval_jcc_false:
    forall
      (stk: stk_state) (mem: mem_state) (tr: trace)
      (pc: node)
      (cond: reg) (brancht: node) (branchf: node)
      (v: value),
      get_inst p stk pc = Some (LLJcc cond brancht branchf) ->
      get_vreg stk cond = Some v ->
      is_false v ->
      step
        p
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
      get_inst p stk pc = Some (LLUnop (ty, dst) next op arg) ->
      get_vreg stk arg = Some arg_value ->
      eval_unop ty op arg_value = Some dst_value ->
      set_vreg stk dst dst_value = Some stk' ->
      step
        p
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
      get_inst p stk pc = Some (LLBinop (ty, dst) next op lhs rhs) ->
      get_vreg stk lhs = Some lhs_value ->
      get_vreg stk rhs = Some rhs_value ->
      eval_binop ty op lhs_value rhs_value = Some dst_value ->
      set_vreg stk dst dst_value = Some stk' ->
      step
        p
        (State stk mem pc)
        tr
        (State stk' mem next)
  .

Inductive star (p: prog): state -> trace -> state -> Prop :=
  | star_refl:
    forall (st: state),
      star p st [] st
  | star_step:
    forall
      (st0: state) (st1: state) (st2: state)
      (tr0: trace) (tr1: trace) (tr: trace)
      (STAR: star p st0 tr0 st1)
      (STEP: step p st1 tr1 st2),
      star p st0 (tr0 ++ tr1) st2
  .

Inductive stepN (p: prog): nat -> state -> trace -> state -> Prop :=
  | step_0:
    forall (st: state),
      stepN p 0 st [] st
  | step_S:
    forall
      (n: nat)
      (st0: state) (st1: state) (st2: state)
      (tr0: trace) (tr1: trace) (tr: trace)
      (STEP_N: stepN p n st0 tr0 st1)
      (STEP: step p st1 tr1 st2),
      stepN p (S n) st0 (tr0 ++ tr1) st2
  .

Inductive ExecutionAt (p: prog): stk_state -> mem_state -> func -> node -> Prop :=
  | exec_at:
    forall
      (fr_data: PTrie.t atom) (fr_regs: PTrie.t value) (fr_args: PTrie.t value)
      (fr_func: name) (fr_pc: node) (fr_retaddr: node)
      (frs: list frame) (mem: mem_state) (f: func)
      (FUNC: Some f = p ! fr_func)
      (INST: None <> f.(fn_insts) ! fr_pc)
      (r: reg),
      ExecutionAt
        p
        (mkframe fr_data fr_regs fr_args fr_func fr_pc fr_retaddr :: frs)
        mem
        f
        fr_pc
  .

Section FUNCTION.
  Variable f: func.
  Hypothesis f_is_valid: is_valid f.

  Definition has_header := fn_blocks_are_valid f f_is_valid.
  (*
  Theorem exec_bb:
    forall (h: node) (n: node),
      BasicBlock f h n ->
      forall (p: prog) (stk: stk_state) (mem: mem_state),
        ExecutionAt p stk mem f h ->
        exists (stk': stk_state) (mem': mem_state) (tr: trace),
          stepN
            p
            (get_inst_index f has_header n)
            (State stk mem h)
            tr
            (State stk' mem' n).
  Proof.
    intros h n Hbb.
    induction Hbb; intros p stk mem Hexec.
    {
      exists stk. exists mem. exists [].
      apply (header_index_0 f has_header) in HEADER.
      rewrite HEADER.
      constructor.
    }
    {
      inversion PRED.
      destruct i;
        try match goal with
        | [ H: Some ?inst = (fn_insts f) ! prev |- _ ] =>
          assert (TermAt f prev);
          [apply term_at with inst; auto; constructor |];
          contradiction
        end.
      {
        generalize (IHHbb p stk mem Hexec); intros Hstate.
        destruct Hstate as [stk0 [mem0 [tr0 Hstep0]]].
      }
    }
  Qed.
  *)

End FUNCTION.
