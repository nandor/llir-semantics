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
Require Import LLIR.Signal.
Require Import LLIR.Liveness.

Import ListNotations.

Inductive event: Type.

Definition trace := list event.

Inductive estate: Type :=
  | State (stk: stack) (h: heap)
  | Exit (stk: PTrie.t frame) (h: heap)
  | Signal (sig: signal)
  .

Inductive Normal: prog -> estate -> Prop :=
  | normal_state:
    forall
      (p: prog)
      (fr_id: positive) (frs: list positive) (frames: PTrie.t frame) (init: objects)
      (h: heap)
      (VP: valid_prog p)
      (FR: ValidFrame p fr_id frames)
      (FRS: forall (f: positive), In f frs -> ValidFrame p f frames),
      Normal p (State (mkstack fr_id frs frames init) h)
  .

Inductive Final: estate -> Prop :=
  | final_exit:
    forall (stk: PTrie.t frame) (h: heap),
      Final (Exit stk h)
  .

Inductive Executing: prog -> stack -> inst -> Prop :=
  | executing:
    forall
      (p: prog)
      (fr_id: positive) (frs: list positive) (frames: PTrie.t frame) (init: objects)
      (f: func) (fr: frame) (i: inst)
      (FRAME: Some fr  = frames ! fr_id)
      (FUNC: Some f = p ! (fr.(fr_func)))
      (INST: Some i = (f.(fn_insts)) ! (fr.(fr_pc))),
      Executing p (mkstack fr_id frs frames init) i
  .

Theorem valid_state_can_execute:
  forall (p: prog) (stk: stack) (h: heap),
    Normal p (State stk h) ->
    exists (i: inst), Executing p stk i.
Proof.
  intros p stk h Hvalid.
  inversion Hvalid; inversion FR.
  exists i.
  apply (executing p fr_id frs frames init f fr i); auto.
Qed.

Definition update_frame (stk: stack) (fn: frame -> frame): stack :=
  {| stk_fr := stk.(stk_fr)
   ; stk_frs := stk.(stk_frs)
   ; stk_frames := PTrie.update fn stk.(stk_frames) stk.(stk_fr)
   ; stk_init := stk.(stk_init)
   |}.

Definition get_vreg (stk: stack) (r: reg): option value :=
  match stk.(stk_frames) ! (stk.(stk_fr)) with
  | None => None
  | Some fr =>
    match fr.(fr_regs) ! r with
    | None => None
    | Some v => Some v
    end
  end.

Definition set_pc (stk: stack) (pc: node): stack :=
  update_frame stk (fun frame => set_pc frame pc).

Definition set_vreg (stk: stack) (r: reg) (v: value): stack :=
  update_frame stk (fun frame => set_vreg frame r v).

Definition set_vreg_pc (stk: stack) (r: reg) (v: value) (pc: node): stack :=
  update_frame stk (fun frame => set_vreg_pc frame r v pc).

Axiom eval_unop: ty -> unop -> value -> option value.

Axiom eval_binop: ty -> binop -> value -> value -> option value.

Inductive Load: heap -> value -> value -> Prop :=
  | load_int:
    forall (h: heap) (v: INT.t),
      Load h (VInt v) VUnd
  | load_und:
    forall (h: heap),
      Load h VUnd VUnd
  .

Inductive ExecutionAt (p: prog): stack -> heap -> func -> frame -> node -> Prop :=
  | exec_at:
    forall
      (stk_fr: positive) (stk_frs: list positive)
      (stk_frames: PTrie.t frame) (stk_init: objects)
      (fr_data: PTrie.t object) (fr_regs: PTrie.t value) (fr_args: PTrie.t value)
      (fr_func: name) (fr_pc: node)
      (h: heap) (f: func)
      (VALID: Normal p (State (mkstack stk_fr stk_frs stk_frames stk_init) h))
      (FRAME: Some (mkframe fr_data fr_regs fr_args fr_func fr_pc) = stk_frames ! stk_fr)
      (FUNC: Some f = p ! fr_func)
      (INST: None <> f.(fn_insts) ! fr_pc)
      (r: reg),
      ExecutionAt
        p
        (mkstack stk_fr stk_frs stk_frames stk_init)
        h
        f
        (mkframe fr_data fr_regs fr_args fr_func fr_pc)
        fr_pc
  .

Theorem uses_are_defined:
  forall
    (p: prog) (stk: stack) (h: heap) (f: func) (fr: frame) (pc: node) (r: reg),
    ExecutionAt p stk h f fr pc ->
    UsedAt f pc r ->
    exists (v: value), fr.(fr_regs) ! r = Some v.
Proof.
  intros p stk h f fr pc r Hexec Huse.
  inversion Hexec; subst; simpl.
  inversion VALID; subst.
  inversion FR.
  rewrite <- FRAME in FRAME0; inversion FRAME0 as [FRAME']; clear FRAME0.
  rewrite FRAME' in FUNC0; simpl in FUNC0; rewrite <- FUNC in FUNC0; 
  inversion FUNC0; clear FUNC0; subst f0.
  rewrite FRAME' in REGS; simpl in REGS.
  assert (Hlive: LiveAt f r pc). 
  {
    apply live_at with (p := [pc]) (use := pc).
    {
      apply path_nil.
      rewrite FRAME' in REACH; simpl in REACH; assumption.
    }
    {
      
    }
    {
      
    }
  }
  apply REGS in Hlive.
  destruct Hlive as [v Hreg]; exists v; auto.
Qed.

Inductive step (p: prog): estate -> trace -> estate -> Prop :=
  | eval_ld:
    forall
      (stk: stack) (h: heap) (tr: trace)
      (dst: reg) (t: ty) (next: node) (addr: reg)
      (addr_value: value) (dst_value: value)
      (EXEC: Executing p stk (LLLd (t, dst) next addr))
      (ADDR: Some addr_value = get_vreg stk addr)
      (LOAD: Load h addr_value dst_value),
      step
        p
        (State stk h)
        tr
        (State (set_vreg_pc stk dst VUnd next) h)
  | eval_jmp:
    forall
      (stk: stack) (h: heap) (tr: trace)
      (target: node)
      (EXEC: Executing p stk (LLJmp target)),
      step
        p
        (State stk h)
        tr
        (State (set_pc stk target) h)
  | eval_jcc_true:
    forall
      (stk: stack) (h: heap) (tr: trace)
      (cond: node)
      (brancht: node) (branchf: node)
      (cond_value: value)
      (EXEC: Executing p stk (LLJcc cond brancht branchf))
      (COND: Some cond_value = get_vreg stk cond)
      (TRUE: IsTrue cond_value),
      step
        p
        (State stk h)
        tr
        (State (set_pc stk brancht) h)
  | eval_jcc_false:
    forall
      (stk: stack) (h: heap) (tr: trace)
      (cond: node)
      (brancht: node) (branchf: node)
      (cond_value: value)
      (EXEC: Executing p stk (LLJcc cond brancht branchf))
      (COND: Some cond_value = get_vreg stk cond)
      (FALSE: IsFalse cond_value),
      step
        p
        (State stk h)
        tr
        (State (set_pc stk brancht) h)
  | eval_unary:
    forall
      (stk: stack) (h: heap) (tr: trace)
      (ty: ty) (op: unop) (arg: reg) (dst: reg) (next: node)
      (dst_value: value) (arg_value: value)
      (EXEC: Executing p stk (LLUnop (ty, dst) next op arg))
      (ARG: Some arg_value = get_vreg stk arg)
      (UNOP: eval_unop ty op arg_value = Some dst_value),
      step
        p
        (State stk h)
        tr
        (State (set_vreg_pc stk dst dst_value next) h)
  | eval_binary:
    forall
      (stk: stack) (h: heap) (tr: trace)
      (ty: ty) (op: binop) (lhs: reg) (rhs: reg) (dst: reg) (next: node)
      (lhs_value: value) (rhs_value: value) (dst_value: value)
      (EXEC: Executing p stk (LLBinop (ty, dst) next op lhs rhs))
      (LHS: Some lhs_value = get_vreg stk lhs)
      (RHS: Some rhs_value = get_vreg stk rhs)
      (BINOP: eval_binop ty op lhs_value rhs_value = Some dst_value),
      step
        p
        (State stk h)
        tr
        (State (set_vreg_pc stk dst dst_value next) h)
  .

Theorem well_typed_progress:
  forall (p: prog) (st: estate),
    well_typed_prog p ->
    valid_prog p ->
    Normal p st ->
    ~Final st ->
    exists (tr: trace) (st': estate),
      step p st tr st'.
Proof.
  intros p st Hwty Hvp Hv Hnf.
  destruct st.
  {
    generalize (valid_state_can_execute p stk h Hv); intros [i Hexec].
    inversion Hv as [
        p' stk_fr stk_frs stk_frames stk_init 
        h' Hvalid Hvalids Hp' Hstk
    ].
    inversion Hvalid.
    assert (H_f_valid: valid_func f).
    { unfold valid_prog in Hvp. apply Hvp with (n := fr_func fr); auto. }
    destruct H_f_valid as [_ Hdefs_are_unique _ Hdef_no_use Hphi_or_inst].
    inversion Hexec as [
        p'' stk_fr' stk_frs' stk_frames'' stk_init'' 
        func' frame' i'' FRAME' FUNC' 
        INST' Hp'' Hstk' Hinst
    ];
    rewrite <- Hstk in Hstk'; inversion Hstk'; clear Hstk';
    subst stk_fr' stk_frs' stk_frames'' stk_init'';
    rewrite <- FRAME in FRAME'; inversion FRAME'; subst frame';
    rewrite <- FUNC in FUNC'; inversion FUNC'; subst func'.
    assert (Hvf: valid_func f).
    { generalize (Hvp (fr_func fr) f FUNC); intros Hf; auto. }
    destruct i.
    {
      destruct dst as [t dst].
      generalize (eval_ld p stk h [] dst t next addr).
      remember (fr_pc fr) as pc.
      assert (LiveAt f addr pc).
      {
        apply (live_at f addr pc pc [pc]).
        { constructor; auto. }
        {
          intros def Hin. inversion Hin; try contradiction; subst def.
          assert (Hinst_used_at: InstUsedAt f pc addr).
          { apply inst_used_at with (i := i''); subst i''; auto; constructor. }
          intros contra; inversion contra.
          { generalize (Hdef_no_use pc addr DEF); intros Hc; contradiction. }
          {
            generalize (
          }
    }
    {
    }
    {
    }
    {
    }
  }
  { assert (Hf: Final (Exit stk h)); try constructor; contradiction. }
Qed.

Inductive star (p: prog): estate -> trace -> estate -> Prop :=
  | star_refl:
    forall (st: estate),
      star p st [] st
  | star_step:
    forall
      (st0: estate) (st1: estate) (st2: estate)
      (tr0: trace) (tr1: trace) (tr: trace)
      (STAR: star p st0 tr0 st1)
      (STEP: step p st1 tr1 st2),
      star p st0 (tr0 ++ tr1) st2
  .

Inductive stepN (p: prog): nat -> estate -> trace -> estate -> Prop :=
  | step_0:
    forall (st: estate),
      stepN p 0 st [] st
  | step_S:
    forall
      (n: nat)
      (st0: estate) (st1: estate) (st2: estate)
      (tr0: trace) (tr1: trace) (tr: trace)
      (STEP_N: stepN p n st0 tr0 st1)
      (STEP: step p st1 tr1 st2),
      stepN p (S n) st0 (tr0 ++ tr1) st2
  .

