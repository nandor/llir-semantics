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
  | Signal (stk: stack) (h: heap) (sig: signal)
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

Inductive Executing: prog -> stack -> frame -> func -> node -> inst -> Prop :=
  | executing:
    forall
      (p: prog)
      (fr_id: positive) (frs: list positive) (frames: PTrie.t frame) (init: objects)
      (f: func) (fr: frame) (i: inst)
      (FRAME: Some fr  = frames ! fr_id)
      (FUNC: Some f = p ! (fr.(fr_func)))
      (INST: Some i = (f.(fn_insts)) ! (fr.(fr_pc))),
      Executing p (mkstack fr_id frs frames init) fr f (fr.(fr_pc)) i
  .

Theorem valid_state_can_execute:
  forall (p: prog) (h: heap) (stk: stack),
    Normal p (State stk h) ->
    exists (fr: frame) (f: func) (pc: node) (i: inst),
      Executing p stk fr f pc i.
Proof.
  intros p h stk Hvalid.
  inversion Hvalid; inversion FR.
  exists fr; exists f; exists (fr_pc fr); exists i.
  apply (executing p fr_id frs frames init f fr i); auto.
Qed.

Theorem uses_are_defined:
  forall
    (p: prog) (h: heap)
    (stk: stack) (f: func) (fr: frame) (pc: node) (i: inst),
    Normal p (State stk h) ->
    Executing p stk fr f pc i ->
    forall (r: reg),
      UsedAt f pc r ->
      exists (v: value), fr.(fr_regs) ! r = Some v.
Proof.
  intros p h stk f fr pc i Hvalid Hexec r Huse.
  inversion Hexec; subst; simpl; clear Hexec.
  inversion Hvalid; clear Hvalid; subst.
  inversion FR.
  rewrite <- FRAME in FRAME0; inversion FRAME0 as [FRAME']; clear FRAME0;
  rewrite FRAME' in FUNC0; simpl in FUNC0; rewrite <- FUNC in FUNC0; 
  inversion FUNC0; clear FUNC0; subst f0 fr0 frames0 fr_id0.
  rewrite <- INST in INST0; inversion INST0 as [INST']; clear INST0; subst i0.
  remember (fr_pc fr) as pc.
  destruct fr eqn:Efr; simpl in Heqpc; simpl in FUNC; simpl in REGS; simpl.
  assert (Hlive: LiveAt f r pc).
  {
    apply live_at with (p := [pc]) (use := pc); auto.
    { apply path_nil; auto. }
    {
      intros def Hne Hin.
      inversion Hin; subst; contradiction.
    }
  }
  apply REGS in Hlive.
  destruct Hlive as [v Hreg]; exists v; auto.
Qed.

Definition update_frame (stk: stack) (fn: frame -> frame): stack :=
  {| stk_fr := stk.(stk_fr)
   ; stk_frs := stk.(stk_frs)
   ; stk_frames := PTrie.update fn stk.(stk_frames) stk.(stk_fr)
   ; stk_init := stk.(stk_init)
   |}.

Definition get_vreg (fr: frame) (r: reg): option value :=
  match fr.(fr_regs) ! r with
  | None => None
  | Some v => Some v
  end.

Definition set_pc (stk: stack) (pc: node): stack :=
  update_frame stk (fun frame => set_pc frame pc).

Definition set_vreg (stk: stack) (r: reg) (v: value): stack :=
  update_frame stk (fun frame => set_vreg frame r v).

Definition set_vreg_pc (stk: stack) (r: reg) (v: value) (pc: node): stack :=
  update_frame stk (fun frame => set_vreg_pc frame r v pc).

Axiom eval_unop: ty -> unop -> value -> option value.

Axiom eval_binop: ty -> binop -> value -> value -> option value.

(* Predicate expressing loads which do not result in a sigal *)
Inductive LoadSuccess: objects -> positive -> positive -> ty -> value -> Prop :=
  .

(* Loads which may result in a signal. *)
Inductive LoadSignal: objects -> positive -> positive -> ty -> signal -> Prop :=
  .

Inductive LoadVal: stack -> heap -> value -> ty -> value -> Prop :=
  .

Inductive LoadSig: stack -> heap -> value -> ty -> signal -> Prop :=
  .

Lemma load_value_or_signal:
  forall (stk: stack) (h: heap) (t: ty) (addr: value),
    {exists (v: value), LoadVal stk h addr t v} 
    +
    {exists (sig: signal), LoadSig stk h addr t sig}.
Admitted.

Inductive Argument: frame -> nat -> ty -> value -> Prop :=
  | arg_int:
    forall (fr: frame) (idx: nat) (t: ty) (v: INT.t)
      (ARG: Some (VInt v) = nth_error fr.(fr_args) idx)
      (TY: TypeOfInt v t),
      Argument fr idx t (VInt v)
  | arg_sym:
    forall (fr: frame) (idx: nat) (s: sym)
      (ARG: Some (VSym s) = nth_error fr.(fr_args) idx),
      Argument fr idx ptr_ty (VSym s)
  | arg_und:
    forall (fr: frame) (idx: nat) (t: ty)
      (ARG: Some VUnd = nth_error fr.(fr_args) idx),
      Argument fr idx t VUnd
  | arg_err:
    forall (fr: frame) (idx: nat) (t: ty)
      (ARG: None = nth_error fr.(fr_args) idx),
      Argument fr idx t VUnd
  | arg_und_int:
    forall (fr: frame) (idx: nat) (t: ty) (v: INT.t)
      (ARG: Some (VInt v) = nth_error fr.(fr_args) idx)
      (TY: ~TypeOfInt v t),
      Argument fr idx t VUnd
  | arg_und_sym:
    forall (fr: frame) (idx: nat) (t: ty) (s: sym)
      (ARG: Some (VSym s) = nth_error fr.(fr_args) idx)
      (TY: t <> ptr_ty),
      Argument fr idx t VUnd
  .

Lemma arg_det:
  forall (fr: frame) (idx: nat) (t: ty) (v0: value) (v1: value),
    Argument fr idx t v0 ->
    Argument fr idx t v1 ->
    v0 = v1.
Proof.
  intros fr idx t v0 v1 Ha0 Ha1.
  inversion Ha0; inversion Ha1; rewrite <- ARG in ARG0; inversion ARG0; 
  subst; auto; contradiction.
Qed.

Lemma arg_complete:
  forall (fr: frame) (idx: nat) (t: ty),
    exists (v: value), Argument fr idx t v.
Proof.
  intros fr idx t; destruct fr.
  destruct (nth_error fr_args idx) as [arg|] eqn:Earg.
  {
    destruct arg.
    {
      destruct (TypeOfInt_dec v t) as [Eq|Ne].
      + exists (VInt v); constructor; simpl; auto.
      + exists VUnd; apply arg_und_int with v; simpl; auto. 
    }
    {
      destruct (type_dec t ptr_ty).
      - exists (VSym s); subst t; apply arg_sym; simpl; auto.
      - exists VUnd; apply arg_und_sym with s; auto.
    }
    {
      exists VUnd; constructor; simpl; auto.
    }
  }
  {
    exists VUnd; apply arg_err; simpl; auto.
  }
Qed.

Inductive step (p: prog): estate -> trace -> estate -> Prop :=
  | eval_ld_value:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (dst: reg) (t: ty) (next: node) (addr: reg)
      (addr_value: value) (dst_value: value)
      (EXEC: Executing p stk fr f pc (LLLd (t, dst) next addr))
      (ADDR: Some addr_value = get_vreg fr addr)
      (LOAD: LoadVal stk h addr_value t dst_value),
      step
        p
        (State stk h)
        []
        (State (set_vreg_pc stk dst dst_value next) h)
  | eval_ld_sig:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (dst: reg) (t: ty) (next: node) (addr: reg)
      (addr_value: value) (sig: signal)
      (EXEC: Executing p stk fr f pc (LLLd (t, dst) next addr))
      (ADDR: Some addr_value = get_vreg fr addr)
      (LOAD: LoadSig stk h addr_value t sig),
      step
        p
        (State stk h)
        []
        (Signal stk h sig)
  | eval_arg:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (dst: reg) (t: ty) (next: node) (index: nat)
      (dst_value: value)
      (EXEC: Executing p stk fr f pc (LLArg (t, dst) next index))
      (LOAD: Argument fr index t dst_value),
      step
        p
        (State stk h)
        []
        (State (set_vreg_pc stk dst dst_value next) h)
  (*
  | eval_int8:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (dst: reg) (next: node) (v: INT.I8.t)
      (EXEC: Executing p stk fr f pc (LLInt8 dst next v)),
      step
        p
        (State stk
  *)
  | eval_jmp:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (target: node)
      (EXEC: Executing p stk fr f pc (LLJmp target)),
      step
        p
        (State stk h)
        []
        (State (set_pc stk target) h)
  | eval_jcc_true:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (cond: node)
      (brancht: node) (branchf: node)
      (cond_value: value)
      (EXEC: Executing p stk fr f pc (LLJcc cond brancht branchf))
      (COND: Some cond_value = get_vreg fr cond)
      (TRUE: IsTrue cond_value),
      step
        p
        (State stk h)
        []
        (State (set_pc stk brancht) h)
  | eval_jcc_false:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (cond: node)
      (brancht: node) (branchf: node)
      (cond_value: value)
      (EXEC: Executing p stk fr f pc (LLJcc cond brancht branchf))
      (COND: Some cond_value = get_vreg fr cond)
      (FALSE: IsFalse cond_value),
      step
        p
        (State stk h)
        []
        (State (set_pc stk brancht) h)
  | eval_unary:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (ty: ty) (op: unop) (arg: reg) (dst: reg) (next: node)
      (dst_value: value) (arg_value: value)
      (EXEC: Executing p stk fr f pc (LLUnop (ty, dst) next op arg))
      (ARG: Some arg_value = get_vreg fr arg)
      (UNOP: eval_unop ty op arg_value = Some dst_value),
      step
        p
        (State stk h)
        []
        (State (set_vreg_pc stk dst dst_value next) h)
  | eval_binary:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (ty: ty) (op: binop) (lhs: reg) (rhs: reg) (dst: reg) (next: node)
      (lhs_value: value) (rhs_value: value) (dst_value: value)
      (EXEC: Executing p stk fr f pc (LLBinop (ty, dst) next op lhs rhs))
      (LHS: Some lhs_value = get_vreg fr lhs)
      (RHS: Some rhs_value = get_vreg fr rhs)
      (BINOP: eval_binop ty op lhs_value rhs_value = Some dst_value),
      step
        p
        (State stk h)
        []
        (State (set_vreg_pc stk dst dst_value next) h)
  .

(*
Theorem well_typed_progress:
  forall (p: prog) (st: estate),
    well_typed_prog p ->
    valid_prog p ->
    Normal p st ->
    ~Final st ->
    exists (tr: trace) (st': estate),
      step p st tr st'.
Proof.
  intros p st Hwty Hvp Hv Hnf; destruct st.
  {
    generalize (valid_state_can_execute p h stk Hv); 
    intros [fr [f [pc [i Hexec]]]]; subst.
    inversion Hv as [
        p' stk_fr stk_frs stk_frames stk_init
        h' Hvalid Hvalids Hp' Hstk
    ]; subst p'.
    inversion Hexec as [
        p'' stk_fr' stk_frs' stk_frames'' stk_init''
        func' frame' i'' 
        FRAME' FUNC' INST' Hp'' Hstk' Hinst Hfunc' Epc Hi''
    ]; subst i'' func' frame' p''.
    assert (H_f_valid: valid_func f).
    { unfold valid_prog in Hvp. apply Hvp with (n := fr_func fr); auto. }
    generalize (uses_are_defined p h stk f fr pc i Hv Hexec); intros Hval.
    rewrite H.

    Ltac used_value f fr pc i sym sym_val Hsym:=
      match goal with
      | [ Hval: forall (r: reg), UsedAt f pc r -> _ |- _ ] =>
        let H := fresh in
        assert (H: UsedAt f pc sym);
        [ constructor; apply inst_used_at with i; subst i pc; auto; constructor
        |];
        apply Hval in H;
        let H' := fresh in
        destruct H as [sym_val H'];
        assert (Hsym: Some sym_val = get_vreg fr sym);
        [ unfold get_vreg; rewrite H'; reflexivity |]
      end.

    Ltac step_state :=
      match goal with
      | [ |- context [ step _ _ ?tr ?state ] ] => exists tr; exists state; auto
      end.

    destruct i eqn:Ei;
      try match goal with
      | [ dst: ty * reg |- _ ] => destruct dst as [t dst]
      end.
    {
      used_value f fr pc i addr addr_value Haddr.
      destruct (load_value_or_signal stk h t addr_value) as [Hload|Hsig].
      {
        destruct Hload as [dst_value Hload].
        generalize (eval_ld_value 
          p stk h fr f pc dst t next addr
          addr_value dst_value Hexec Haddr Hload
        ).
        step_state.
      }
      {
        destruct Hsig as [sig Hsig].
        generalize (eval_ld_sig 
          p stk h fr f pc dst t next addr
          addr_value sig Hexec Haddr Hsig
        ).
        step_state.
      }
    }
    {
      generalize (arg_complete fr index t); intros [dst_value Harg].
      generalize (eval_arg 
        p stk h fr f pc dst t next index dst_value
        Hexec Harg
      ).
      step_state.
    }
    {
      
    }
  }
Qed.
*)

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

