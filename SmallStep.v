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
Require Import LLIR.Typing.

Import ListNotations.

Inductive event: Type.

Definition trace := list event.

Definition stack := (positive, PTrie.t frame).

Inductive Heap: Type :=
  .

(*
Inductive state: Type :=
  | State:
    forall
      (stk: stack)
      (mem: Heap),
      state
  | Exit:
    forall
      (stk: PTrie.t frame)
      (mem: Heap),
      state
  .

Inductive Final: state -> Prop :=
  | final_exit:
    forall (stk: PTrie.t frame) (mem: Heap),
      Final (Exit stk mem)
  .

Inductive Executing: prog -> Stack -> inst -> Prop :=
  | executing:
    forall (p: prog) (stk
    


Definition get_inst (p: prog) (stk: Stack): option inst :=
  match stk with
  | stack fr _ _ =>
    match p ! (fr.(fr_func)) with
    | Some func => func.(fn_insts) ! (fr.(fr_pc))
    | None => None
    end
  end.

Definition get_vreg (stk: stk_state) (r: reg): value :=
  match stk with
  | (fr, _) => get_vreg fr r
  end.

Definition set_pc (stk: stk_state) (pc: node): stk_state :=
  match stk with
  | (fr, frs) => (set_pc fr pc, frs)
  end.

Definition set_vreg (stk: stk_state) (r: reg) (v: value): stk_state :=
  match stk with
  | (fr, frs) => (set_vreg fr r v, frs)
  end.

Definition set_vreg_pc (stk: stk_state) (r: reg) (v: value) (pc: node): stk_state :=
  match stk with
  | (fr, frs) => (set_vreg_pc fr r v pc, frs)
  end.

Lemma value_tf_dec: forall (v: value), IsTrue v \/ IsFalse v.
Proof.
  intros v; destruct v.
  - destruct (INT8.eq_dec  v INT8.zero);  [right; subst|left]; constructor; auto.
  - destruct (INT16.eq_dec v INT16.zero); [right; subst|left]; constructor; auto.
  - destruct (INT32.eq_dec v INT32.zero); [right; subst|left]; constructor; auto.
  - destruct (INT64.eq_dec v INT64.zero); [right; subst|left]; constructor; auto.
  - left; constructor.
  - right; constructor.
Qed.

Axiom eval_unop: ty -> unop -> value -> option value.

Axiom eval_binop: ty -> binop -> value -> value -> option value.

Inductive step (p: prog): state -> trace -> state -> Prop :=
  | eval_jmp:
    forall
      (stk: stk_state) (mem: mem_state) (tr: trace)
      (pc: node)
      (target: node),
      get_inst p stk = Some (LLJmp target) ->
      step
        p
        (State stk mem)
        tr
        (State (set_pc stk target) mem)
  | eval_jcc_true:
    forall
      (stk: stk_state) (mem: mem_state) (tr: trace)
      (cond: node) (pc: node)
      (brancht: node) (branchf: node),
      get_inst p stk = Some (LLJcc cond brancht branchf) ->
      IsTrue (get_vreg stk cond) ->
      step
        p
        (State stk mem)
        tr
        (State (set_pc stk brancht) mem)
  | eval_jcc_false:
    forall
      (stk: stk_state) (mem: mem_state) (tr: trace)
      (cond: node) (pc: node)
      (brancht: node) (branchf: node),
      get_inst p stk = Some (LLJcc cond brancht branchf) ->
      IsFalse (get_vreg stk cond) ->
      step
        p
        (State stk mem)
        tr
        (State (set_pc stk brancht) mem)
  | eval_unary:
    forall
      (stk: stk_state) (mem: mem_state) (tr: trace)
      (pc: node)
      (ty: ty) (op: unop) (arg: reg) (dst: reg) (next: node)
      (dst_value: value),
      get_inst p stk = Some (LLUnop (ty, dst) next op arg) ->
      eval_unop ty op (get_vreg stk arg) = Some dst_value ->
      step
        p
        (State stk mem)
        tr
        (State (set_vreg_pc stk dst dst_value next) mem)
  | eval_binary:
    forall
      (stk: stk_state) (mem: mem_state) (tr: trace)
      (pc: node)
      (ty: ty) (op: binop) (lhs: reg) (rhs: reg) (dst: reg) (next: node)
      (dst_value: value),
      get_inst p stk = Some (LLBinop (ty, dst) next op lhs rhs) ->
      eval_binop ty op (get_vreg stk lhs) (get_vreg stk rhs) = Some dst_value ->
      step
        p
        (State stk mem)
        tr
        (State (set_vreg_pc stk dst dst_value next) mem)
  .

Theorem well_typed_progress:
  forall (p: prog) (st: state),
    well_typed_prog p ->
    ~Final st ->
    exists (tr: trace) (st': state),
      step p st tr st'.
Proof.
  intros p st Hty Hfinal.
  destruct st.
  {
    clear Hfinal.
    destruct stk; destruct f.
  }
  { assert (Final (Exit stk mem)). constructor. contradiction. }
Qed.

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
      (frs: PTrie.t frame) (mem: mem_state) (f: func)
      (FUNC: Some f = p ! fr_func)
      (INST: None <> f.(fn_insts) ! fr_pc)
      (r: reg),
      ExecutionAt
        p
        (mkframe fr_data fr_regs fr_args fr_func fr_pc fr_retaddr, frs)
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
*)
