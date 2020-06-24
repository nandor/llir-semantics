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
Require Import LLIR.Syscall.
Require Import LLIR.Frame.
Require Import LLIR.State.

Import ListNotations.

Inductive event: Type.

Inductive estate: Type :=
  | State (stk: stack) (h: heap)
  | Exit (stk: frame_map) (h: heap)
  | Signal (stk: stack) (h: heap) (sig: signal)
  | Broken
  .

Inductive Normal: prog -> estate -> Prop :=
  | normal_state:
    forall
      (p: prog)
      (fr_id: positive) (frs: list positive)
      (next: positive) (frames: PTrie.t frame) (init: objects)
      (h: heap)
      (VP: valid_prog p)
      (FR: ValidTopFrame p fr_id frames)
      (FRS: forall (f: positive), In f frs -> ValidMidFrame p f frames),
      Normal p (State (mkstack fr_id frs next frames init) h)
  .

Inductive Final: estate -> Prop :=
  | final_exit:
    forall (stk: PTrie.t frame) (h: heap),
      Final (Exit stk h)
  | final_broken:
      Final (Broken)
  .

Inductive Executing: prog -> stack -> frame -> func -> node -> inst -> Prop :=
  | executing:
    forall
      (p: prog)
      (fr_id: positive) (frs: list positive)
      (next: positive) (frames: PTrie.t frame) (init: objects)
      (f: func) (fr: frame) (i: inst)
      (FRAME: Some fr  = frames ! fr_id)
      (FUNC: Some f = p ! (fr.(fr_func)))
      (INST: Some i = (f.(fn_insts)) ! (fr.(fr_pc))),
      Executing p (mkstack fr_id frs next frames init) fr f (fr.(fr_pc)) i
  .

Theorem valid_state_can_execute:
  forall (p: prog) (h: heap) (stk: stack),
    Normal p (State stk h) ->
    exists (fr: frame) (f: func) (pc: node) (i: inst),
      Executing p stk fr f pc i.
Proof.
  intros p h stk Hvalid.
  inversion Hvalid; inversion FR; inversion VALID.
  exists fr. exists f. exists (fr_pc fr). exists i.
  apply (executing p fr_id frs next frames init f fr i); auto.
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
  rewrite <- FRAME in FRAME0; inversion FRAME0 as [FRAME']; clear FRAME0.
  inversion VALID.
  rewrite FRAME' in FUNC0; simpl in FUNC0; rewrite <- FUNC in FUNC0;
  inversion FUNC0; clear FUNC0; subst f0 fr0 frames0 fr_id0.
  rewrite <- INST in INST0; inversion INST0 as [INST']; clear INST0; subst i0.
  remember (fr_pc fr) as pc.
  destruct fr eqn:Efr; simpl in Heqpc; simpl in FUNC; simpl in REGS; simpl.
  assert (Hlive: LiveAt f r pc).
  {
    apply live_at with (p := [pc]) (use := pc); auto.
    { apply reverse_path_nil; auto. }
  }
  apply REGS in Hlive.
  destruct Hlive as [v Hreg]; exists v; auto.
Qed.

Definition update_frame (stk: stack) (fn: frame -> frame): stack :=
  {| stk_fr := stk.(stk_fr)
   ; stk_frs := stk.(stk_frs)
   ; stk_next := stk.(stk_next)
   ; stk_frames := PTrie.update fn stk.(stk_frames) stk.(stk_fr)
   ; stk_init := stk.(stk_init)
   |}.

Definition stk_set_pc (stk: stack) (pc: node): stack :=
  update_frame stk (fun frame => set_pc frame pc).

Definition stk_set_vreg (stk: stack) (r: reg) (v: value): stack :=
  update_frame stk (fun frame => set_vreg frame r v).

Definition stk_set_vreg_pc (stk: stack) (r: reg) (v: value) (pc: node): stack :=
  update_frame stk (fun frame => set_vreg_pc frame r v pc).

Definition stk_jump_to_phi (stk: stack) (t: node): stack :=
  update_frame stk (fun frame => jump_to_phi frame t).

Axiom eval_unop: ty -> unop -> value -> option value.

Axiom eval_binop: ty -> binop -> value -> value -> option value.

(* Predicate expressing loads which do not result in a sigal *)
Inductive LoadVal: stack -> heap -> value -> ty -> value -> Prop :=
  .

(* Loads which may result in a signal. *)
Inductive LoadSig: stack -> heap -> value -> ty -> signal -> Prop :=
  .

Lemma load_value_or_signal:
  forall (stk: stack) (h: heap) (t: ty) (addr: value),
    (exists (v: value), LoadVal stk h addr t v)
    \/
    (exists (sig: signal), LoadSig stk h addr t sig).
Admitted.

(* Predicate expressing stores which do not result in a sigal *)
Inductive StoreVal: stack -> heap -> value -> value -> heap -> Prop :=
  .

(* Stores which may result in a signal. *)
Inductive StoreSig: stack -> heap -> value -> signal -> Prop :=
  .

(* Stores which break the program by overwriting code or stack *)
Inductive StoreBreak: stack -> heap -> value -> Prop :=
  .

Lemma store_value_signal_break:
  forall (stk: stack) (h: heap) (addr: value) (v: value),
    (exists (h': heap), StoreVal stk h addr v h')
    \/
    (exists (sig: signal), StoreSig stk h addr sig)
    \/
    StoreBreak stk h addr.
Admitted.

Inductive UnaryVal: value -> unop -> ty -> value -> Prop :=
  .

Inductive UnarySig: value -> unop -> ty -> signal -> Prop :=
  .

Lemma unary_value_or_signal:
  forall (op: unop) (arg: value) (arg_ty: ty) (dst_ty: ty),
    WellTypedUnop op arg_ty dst_ty ->
    TypeOfValue arg arg_ty ->
    (exists (v: value), TypeOfValue v dst_ty /\ UnaryVal arg op dst_ty v)
    \/
    (exists (sig: signal), UnarySig arg op dst_ty sig).
Admitted.

Inductive BinaryVal: value -> value -> binop -> ty -> value -> Prop :=
  .

Inductive BinarySig: value -> value -> binop -> ty -> signal -> Prop :=
  .

Lemma binary_value_or_signal:
  forall (op: binop) (lhs: value) (rhs: value)
    (lhs_ty: ty) (rhs_ty: ty) (dst_ty: ty),
    WellTypedBinop op lhs_ty rhs_ty dst_ty ->
    TypeOfValue lhs lhs_ty ->
    TypeOfValue rhs rhs_ty ->
    (exists (v: value), TypeOfValue v dst_ty /\ BinaryVal lhs rhs op dst_ty v)
    \/
    (exists (sig: signal), BinarySig lhs rhs op dst_ty sig).
Admitted.

Inductive Argument: frame -> nat -> ty -> value -> Prop :=
  | arg_int:
    forall (fr: frame) (idx: nat) (t: ty) (v: value)
      (ARG: Some v = nth_error fr.(fr_args) idx)
      (TY: TypeOfValue v t),
      Argument fr idx t v
  | arg_err:
    forall (fr: frame) (idx: nat) (t: ty)
      (ARG: None = nth_error fr.(fr_args) idx),
      Argument fr idx t VUnd
  | arg_und:
    forall (fr: frame) (idx: nat) (t: ty) (v: value)
      (ARG: Some v = nth_error fr.(fr_args) idx)
      (TY: ~TypeOfValue v t),
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
    destruct (TypeOfValue_dec arg t) as [Eq|Ne].
    { exists arg; constructor; auto. }
    { exists VUnd. apply arg_und with arg; auto. }
  }
  {
    exists VUnd; apply arg_err; simpl; auto.
  }
Qed.

Lemma syscall_args:
  forall
    (p: prog) (f: func)
    (fr: frame) (args: list reg) (env: type_env),
    (Some f = p ! (fr_func fr)) ->
    (forall (arg: reg),
      In arg args ->
      well_typed_reg env arg sys_arg_ty) ->
    (forall (arg: reg),
      LiveAt f arg (fr_pc fr) ->
      exists (v: value), Some v = (fr_regs fr) ! arg) ->
    (forall (arg: reg),
      In arg args ->
      LiveAt f arg (fr_pc fr)) ->
    (forall (r: reg) (v: value),
       Some v = (fr_regs fr) ! r ->
       exists (t: ty), Some t = env ! r /\ TypeOfValue v t) ->
    exists (values: list value), SyscallArgs fr args values.
Proof.
  intros p f fr args env Hf Htyped Hvals Hlive Hty_of.
  induction args; [exists []; constructor |].
  assert (Htypes': forall arg, In arg args -> well_typed_reg env arg sys_arg_ty).
  { intros arg Hin. apply Htyped. right. auto. }
  assert (Hlive': forall arg, In arg args -> LiveAt f arg (fr_pc fr)).
  { intros arg Hin. apply Hlive. right. auto. }
  generalize (IHargs Htypes' Hlive'); intros [values Hvalues].
  clear Htypes' Hlive' IHargs.
  assert (Hin: In a (a :: args)). { left; auto. }
  generalize (Hlive a Hin); intros Hlive_a.
  generalize (Hvals a Hlive_a); intros [v Hval_a].
  exists (v :: values); constructor; auto.
  generalize (Hty_of a v Hval_a); intros [t [Hty Hty_of_v]].
  generalize (Htyped a Hin); intros Hwt.
  inversion Hwt as [Hty'].
  rewrite <- Hty in Hty'; inversion Hty'; subst t; clear Hty'.
  inversion Hty_of_v; subst; try constructor.
  inversion TY; constructor.
Qed.

Inductive ReturnToFrame
  : prog ->
    stack ->
    positive ->
    list positive ->
    inst ->
    node ->
    Prop :=
  | return_to_frame:
    forall
      (p: prog)
      (next_id: positive)
      (next: positive) (frames: PTrie.t frame) (init: objects)
      (top: positive) (next: positive) (rest: list positive)
      (fr: frame) (f: func) (i: inst) (ret_pc: node)
      (FRAME: Some fr = frames ! next)
      (FUNC: Some f = p ! (fr.(fr_func)))
      (INST: Some i = f.(fn_insts) ! (fr.(fr_pc)))
      (SUCC: ReturnAddress i ret_pc),
      ReturnToFrame
        p
        (mkstack top (next :: rest) next_id frames init)
        next
        rest
        i
        ret_pc
  .

Inductive ReturnValue
  : frame ->
    option reg ->
    ty ->
    value ->
    Prop :=
  | return_none_und:
    forall (fr: frame) (t: ty),
      ReturnValue fr None t VUnd
  | return_some_match:
    forall (fr: frame) (arg: reg) (t: ty) (arg_value: value)
      (ARG: Some arg_value = fr.(fr_regs) ! arg)
      (TY: TypeOfValue arg_value t),
      ReturnValue fr (Some arg) t arg_value
  | return_some_und:
    forall (fr: frame) (arg: reg) (t: ty) (arg_value: value)
      (ARG: Some arg_value = fr.(fr_regs) ! arg)
      (TY: ~TypeOfValue arg_value t),
      ReturnValue fr (Some arg) t VUnd
  .

Inductive CallArgs : frame -> list reg -> list value -> Prop :=
  | arg_vals_nil:
    forall
      (fr: frame),
      CallArgs fr [] []
  | arg_vals_cons:
    forall
      (fr: frame)
      (arg_value: value) (arg_values: list value)
      (arg: reg) (args: list reg)
      (VALUE: Some arg_value = fr.(fr_regs) ! arg)
      (TAIL: CallArgs fr args arg_values),
      CallArgs fr (arg::args) (arg_value::arg_values)
  .

Lemma call_args:
  forall
    (p: prog) (f: func)
    (fr: frame) (args: list reg),
    (Some f = p ! (fr_func fr)) ->
    (forall (arg: reg),
      LiveAt f arg (fr_pc fr) ->
      exists (v: value), Some v = (fr_regs fr) ! arg) ->
    (forall (arg: reg),
      In arg args ->
      LiveAt f arg (fr_pc fr)) ->
    exists (values: list value), CallArgs fr args values.
Proof.
  intros p f fr args Hfn Hval Hlive.
  induction args; [exists []; constructor|].
  assert (Hin: In a (a :: args)). { left; auto. }
  destruct (Hval a (Hlive a Hin)) as [v Hv].
  assert (Hlive': forall arg, In arg args -> LiveAt f arg (fr_pc fr)).
  { intros arg Hin'. apply Hlive. right. auto. }
  destruct (IHargs Hlive') as [values Hvalues].
  exists (v::values); constructor; auto.
Qed.

Inductive step (p: prog): estate -> trace -> estate -> Prop :=
  | eval_st_value:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (next: node) (addr: reg) (arg: reg)
      (addr_value: value) (arg_value: value) (h': heap)
      (EXEC: Executing p stk fr f pc (LLSt next addr arg))
      (ADDR: Some addr_value = fr.(fr_regs) ! addr)
      (VALUE: Some arg_value = fr.(fr_regs) ! arg)
      (LOAD: StoreVal stk h addr_value arg_value h'),
      step
        p
        (State stk h)
        []
        (State (stk_set_pc stk next) h')
  | eval_st_sig:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (next: node) (addr: reg) (arg: reg)
      (addr_value: value) (sig: signal)
      (EXEC: Executing p stk fr f pc (LLSt next addr arg))
      (ADDR: Some addr_value = fr.(fr_regs) ! addr)
      (LOAD: StoreSig stk h addr_value sig),
      step
        p
        (State stk h)
        []
        (Signal stk h sig)
  | eval_st_break:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (next: node) (addr: reg) (arg: reg)
      (addr_value: value)
      (EXEC: Executing p stk fr f pc (LLSt next addr arg))
      (ADDR: Some addr_value = fr.(fr_regs) ! addr)
      (LOAD: StoreBreak stk h addr_value),
      step
        p
        (State stk h)
        []
        Broken
  | eval_ld_value:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (dst: reg) (t: ty) (next: node) (addr: reg)
      (addr_value: value) (dst_value: value)
      (EXEC: Executing p stk fr f pc (LLLd (t, dst) next addr))
      (ADDR: Some addr_value = fr.(fr_regs) ! addr)
      (LOAD: LoadVal stk h addr_value t dst_value),
      step
        p
        (State stk h)
        []
        (State (stk_set_vreg_pc stk dst dst_value next) h)
  | eval_ld_sig:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (dst: reg) (t: ty) (next: node) (addr: reg)
      (addr_value: value) (sig: signal)
      (EXEC: Executing p stk fr f pc (LLLd (t, dst) next addr))
      (ADDR: Some addr_value = fr.(fr_regs) ! addr)
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
        (State (stk_set_vreg_pc stk dst dst_value next) h)
  | eval_int:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (dst: reg) (next: node) (v: INT.t)
      (EXEC: Executing p stk fr f pc (LLInt dst next v)),
      step
        p
        (State stk h)
        []
        (State (stk_set_vreg_pc stk dst (VInt v) next) h)
  | eval_select_true:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (dst: reg) (t: ty) (next: node) (cond: reg) (lhs: reg) (rhs: reg)
      (cond_value: value) (lhs_value: value)
      (EXEC: Executing p stk fr f pc (LLSelect (t, dst) next cond lhs rhs))
      (COND: Some cond_value = fr.(fr_regs) ! cond)
      (LHS: Some lhs_value = fr.(fr_regs) ! lhs)
      (TRUE: IsTrue cond_value),
      step
        p
        (State stk h)
        []
        (State (stk_set_vreg_pc stk dst lhs_value next) h)
  | eval_select_false:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (dst: reg) (t: ty) (next: node) (cond: reg) (lhs: reg) (rhs: reg)
      (cond_value: value) (rhs_value: value)
      (EXEC: Executing p stk fr f pc (LLSelect (t, dst) next cond lhs rhs))
      (COND: Some cond_value = fr.(fr_regs) ! cond)
      (RHS: Some rhs_value = fr.(fr_regs) !  rhs)
      (TRUE: IsFalse cond_value),
      step
        p
        (State stk h)
        []
        (State (stk_set_vreg_pc stk dst rhs_value next) h)
  | eval_frame:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (dst: reg) (next: node) (object: positive) (offset: nat)
      (EXEC: Executing p stk fr f pc (LLFrame dst next object offset)),
      step
        p
        (State stk h)
        []
        (State
          (stk_set_vreg_pc stk dst
            (VSym (SFrame (stk_fr stk) object offset))
            next)
          h)
 | eval_global:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (dst: reg) (next: node)
      (segment: positive) (object: positive) (offset: nat)
      (EXEC: Executing p stk fr f pc (LLGlobal dst next segment object offset)),
      step
        p
        (State stk h)
        []
        (State
          (stk_set_vreg_pc stk dst
            (VSym (SAtom segment object offset))
            next)
          h)
  | eval_func:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (dst: reg) (next: node) (fn_id: name)
      (EXEC: Executing p stk fr f pc (LLFunc dst next fn_id)),
      step
        p
        (State stk h)
        []
        (State (stk_set_vreg_pc stk dst (VSym (SFunc fn_id)) next) h)
  | eval_und:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (t: ty) (dst: reg) (next: node)
      (EXEC: Executing p stk fr f pc (LLUndef (t, dst) next)),
      step
        p
        (State stk h)
        []
        (State (stk_set_vreg_pc stk dst (VUnd) next) h)
  | eval_jmp:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (target: node)
      (EXEC: Executing p stk fr f pc (LLJmp target)),
      step
        p
        (State stk h)
        []
        (State (stk_jump_to_phi stk target) h)
  | eval_jcc_true:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (cond: node)
      (brancht: node) (branchf: node)
      (cond_value: value)
      (EXEC: Executing p stk fr f pc (LLJcc cond brancht branchf))
      (COND: Some cond_value = fr.(fr_regs) ! cond)
      (TRUE: IsTrue cond_value),
      step
        p
        (State stk h)
        []
        (State (stk_jump_to_phi stk brancht) h)
  | eval_jcc_false:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (cond: node)
      (brancht: node) (branchf: node)
      (cond_value: value)
      (EXEC: Executing p stk fr f pc (LLJcc cond brancht branchf))
      (COND: Some cond_value = fr.(fr_regs) ! cond)
      (FALSE: IsFalse cond_value),
      step
        p
        (State stk h)
        []
        (State (stk_jump_to_phi stk branchf) h)
  | eval_unary_value:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (dst: reg) (ty: ty) (next: node) (op: unop) (arg: reg)
      (dst_value: value) (arg_value: value)
      (EXEC: Executing p stk fr f pc (LLUnop (ty, dst) next op arg))
      (ARG: Some arg_value = fr.(fr_regs) ! arg)
      (UNOP: UnaryVal arg_value op ty dst_value),
      step
        p
        (State stk h)
        []
        (State (stk_set_vreg_pc stk dst dst_value next) h)
  | eval_unary_signal:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (dst: reg) (ty: ty) (next: node) (op: unop) (arg: reg)
      (arg_value: value) (sig: signal)
      (EXEC: Executing p stk fr f pc (LLUnop (ty, dst) next op arg))
      (ARG: Some arg_value = fr.(fr_regs) ! arg)
      (SIG: UnarySig arg_value op ty sig),
      step
        p
        (State stk h)
        []
        (Signal stk h sig)
  | eval_binary_value:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (dst: reg) (t: ty) (op: binop) (lhs: reg) (rhs: reg) (next: node)
      (lhs_value: value) (rhs_value: value) (dst_value: value)
      (EXEC: Executing p stk fr f pc (LLBinop (t, dst) next op lhs rhs))
      (LHS: Some lhs_value = fr.(fr_regs) ! lhs)
      (RHS: Some rhs_value = fr.(fr_regs) ! rhs)
      (BINOP: BinaryVal lhs_value rhs_value op t dst_value),
      step
        p
        (State stk h)
        []
        (State (stk_set_vreg_pc stk dst dst_value next) h)
  | eval_binary_signal:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (dst: reg) (t: ty) (op: binop) (lhs: reg) (rhs: reg) (next: node)
      (lhs_value: value) (rhs_value: value) (sig: signal)
      (EXEC: Executing p stk fr f pc (LLBinop (t, dst) next op lhs rhs))
      (LHS: Some lhs_value = fr.(fr_regs) ! lhs)
      (RHS: Some rhs_value = fr.(fr_regs) ! rhs)
      (BINOP: BinarySig lhs_value rhs_value op t sig),
      step
        p
        (State stk h)
        []
        (Signal stk h sig)
  | eval_mov:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (dst: reg) (ty: ty) (next: node) (arg: reg)
      (arg_value: value)
      (EXEC: Executing p stk fr f pc (LLMov (ty, dst) next arg))
      (ARG: Some arg_value = fr.(fr_regs) ! arg),
      step
        p
        (State stk h)
        []
        (State (stk_set_vreg_pc stk dst arg_value next) h)
  | eval_syscall_ret:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (dst: reg) (next: node) (tr: trace)
      (args: list reg) (arg_values: list value)
      (sno: reg) (sno_call: syscall) (sno_value: value) (dst_value: INT.I64.t)
      (stk': stack) (h': heap)
      (ARGS: SyscallArgs fr args arg_values)
      (SNO: Some sno_value = fr.(fr_regs) ! sno)
      (SNO_CALL: SyscallNumber sno_value sno_call)
      (EXEC: Executing p stk fr f pc (LLSyscall dst next sno args))
      (SYS: SyscallRet sno_call arg_values stk h tr stk' h' dst_value),
      step
        p
        (State stk h)
        tr
        (State (stk_set_vreg_pc stk' dst (VInt (INT.Int64 dst_value)) next) h')
  | eval_syscall_sig:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (dst: reg) (next: node) (tr: trace)
      (args: list reg) (arg_values: list value)
      (sno: reg) (sno_call: syscall) (sno_value: value)
      (sig: signal)
      (ARGS: SyscallArgs fr args arg_values)
      (SNO: Some sno_value = fr.(fr_regs) ! sno)
      (SNO_CALL: SyscallNumber sno_value sno_call)
      (EXEC: Executing p stk fr f pc (LLSyscall dst next sno args))
      (SYS: SyscallSig sno_call arg_values stk h tr sig),
      step
        p
        (State stk h)
        tr
        (Signal stk h sig)
  | eval_syscall_nosys:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (dst: reg) (next: node) (tr: trace)
      (args: list reg) (arg_values: list value)
      (sno: reg) (sno_value: value)
      (ARGS: SyscallArgs fr args arg_values)
      (SNO: Some sno_value = fr.(fr_regs) ! sno)
      (SNO_NO_CALL: SyscallNoSys sno_value)
      (EXEC: Executing p stk fr f pc (LLSyscall dst next sno args)),
      step
        p
        (State stk h)
        tr
        (State (stk_set_vreg_pc stk dst (VInt (INT.Int64 ENOSYS)) next) h)
  | eval_syscall_und_enosys:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (dst: reg) (next: node) (tr: trace)
      (args: list reg) (arg_values: list value)
      (sno: reg) (sno_value: value)
      (ARGS: SyscallArgs fr args arg_values)
      (SNO: Some sno_value = fr.(fr_regs) ! sno)
      (SNO_NO_CALL: SyscallUndef sno_value)
      (EXEC: Executing p stk fr f pc (LLSyscall dst next sno args)),
      step
        p
        (State stk h)
        tr
        (State (stk_set_vreg_pc stk dst (VInt (INT.Int64 ENOSYS)) next) h)
 | eval_trap:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (EXEC: Executing p stk fr f pc LLTrap),
      step
        p
        (State stk h)
        []
        (Signal stk h SIGILL)
 | eval_ret_top:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node) (value: option reg)
      (EXEC: Executing p stk fr f pc (LLRet value))
      (TOP: TopFrame stk),
      step
        p
        (State stk h)
        []
        (Signal stk h SIGILL)
  | eval_ret_void:
    forall
      (stk: stack) (h: heap)
      (fr: frame) (f: func) (pc: node) (value: option reg)
       (rest: list positive)
      (i: inst) (callee: positive) (ret_pc: node)
      (EXEC: Executing p stk fr f pc (LLRet value))
      (NEXT: ReturnToFrame p stk callee rest i ret_pc)
      (VOID: VoidCallSite i),
      step
        p
        (State stk h)
        []
        (State
          (stk_jump_to_phi
            (mkstack
              callee
              rest
              (stk_next stk)
              (stk_frames stk)
              (stk_init stk))
            ret_pc)
          h)
  | eval_ret_value:
    forall
      (stk: stack) (h: heap)
      (fr: frame) (f: func) (pc: node) (v: option reg)
      (rest: list positive) (i: inst) (callee: positive)
      (t: ty) (dst: reg) (ret_pc: node) (ret_value: value)
      (EXEC: Executing p stk fr f pc (LLRet v))
      (NEXT: ReturnToFrame p stk callee rest i ret_pc)
      (SITE: CallSite i t dst)
      (RET: ReturnValue fr v t ret_value),
      step
        p
        (State stk h)
        []
        (State
          (stk_jump_to_phi
            (stk_set_vreg
              (mkstack
                callee
                rest
                (stk_next stk)
                (stk_frames stk)
                (stk_init stk))
              dst
              ret_value)
            ret_pc)
          h)
  | eval_call_broken:
    forall
      (stk: stack) (h: heap) (fr: frame) (f: func) (pc: node)
      (i: inst) (callee: reg) (callee_value: value)
      (EXEC: Executing p stk fr f pc i)
      (CALLEE: Callee i callee)
      (COND: Some callee_value = fr.(fr_regs) ! callee)
      (FUNC: ~Function callee_value),
      step
        p
        (State stk h)
        []
        Broken
  | eval_tcall:
    forall
      (stk: stack) (h: heap)
      (stk_fr: positive) (stk_frs: list positive) (stk_next: positive)
      (stk_frames: PTrie.t frame) (stk_init: objects)
      (fr: frame) (f: func) (pc: node) (callee: reg)
      (callee_func: name) (callee_f: func)
      (args: list reg) (arg_values: list value)
      (EXEC: Executing p stk fr f pc (LLTCall callee args))
      (CALEE: Some (VSym (SFunc callee_func)) = fr.(fr_regs) ! callee)
      (FUNC: Some callee_f = p ! callee_func)
      (ARGS: CallArgs fr args arg_values),
      step
        p
        (State (mkstack stk_fr stk_frs stk_next stk_frames stk_init) h)
        []
        (State
          (mkstack
            stk_next
            stk_frs
            (Pos.succ stk_next)
            (PTrie.set (PTrie.remove stk_frames stk_fr) stk_next
              (mkframe
                (create_frame callee_f)
                PTrie.empty
                arg_values
                callee_func
                callee_f.(fn_entry)
                ))
            stk_init)
          h)
  | eval_tinvoke:
    forall
      (stk: stack) (h: heap)
      (stk_fr: positive) (stk_frs: list positive) (stk_next: positive)
      (stk_frames: PTrie.t frame) (stk_init: objects)
      (fr: frame) (f: func) (pc: node) (callee: reg) (exn: node)
      (callee_func: name) (callee_f: func)
      (args: list reg) (arg_values: list value)
      (EXEC: Executing p stk fr f pc (LLTInvoke callee args exn))
      (CALEE: Some (VSym (SFunc callee_func)) = fr.(fr_regs) ! callee)
      (FUNC: Some callee_f = p ! callee_func)
      (ARGS: CallArgs fr args arg_values),
      step
        p
        (State (mkstack stk_fr stk_frs stk_next stk_frames stk_init) h)
        []
        (State
          (mkstack
            stk_next
            stk_frs
            (Pos.succ stk_next)
            (PTrie.set (PTrie.remove stk_frames stk_fr) stk_next
              (mkframe
                (create_frame callee_f)
                PTrie.empty
                arg_values
                callee_func
                callee_f.(fn_entry)
                ))
            stk_init)
          h)
  | eval_call:
    forall
      (stk: stack) (h: heap)
      (stk_fr: positive) (stk_frs: list positive) (stk_next: positive)
      (stk_frames: PTrie.t frame) (stk_init: objects)
      (fr: frame) (f: func) (pc: node) (callee: reg)
      (next: node) (dst: option (ty * reg))
      (callee_func: name) (callee_f: func)
      (args: list reg) (arg_values: list value)
      (EXEC: Executing p stk fr f pc (LLCall dst next callee args))
      (CALEE: Some (VSym (SFunc callee_func)) = fr.(fr_regs) ! callee)
      (FUNC: Some callee_f = p ! callee_func)
      (ARGS: CallArgs fr args arg_values),
      step
        p
        (State (mkstack stk_fr stk_frs stk_next stk_frames stk_init) h)
        []
        (State
          (mkstack
            stk_next
            (stk_fr :: stk_frs)
            (Pos.succ stk_next)
            (PTrie.set (PTrie.remove stk_frames stk_fr) stk_next
              (mkframe
                (create_frame callee_f)
                PTrie.empty
                arg_values
                callee_func
                callee_f.(fn_entry)
                ))
            stk_init)
          h)
  | eval_invoke:
    forall
      (stk: stack) (h: heap)
      (stk_fr: positive) (stk_frs: list positive) (stk_next: positive)
      (stk_frames: PTrie.t frame) (stk_init: objects)
      (fr: frame) (f: func) (pc: node) (callee: reg)
      (next: node) (dst: option (ty * reg)) (exn: node)
      (callee_func: name) (callee_f: func)
      (args: list reg) (arg_values: list value)
      (EXEC: Executing p stk fr f pc (LLInvoke dst next callee args exn))
      (CALEE: Some (VSym (SFunc callee_func)) = fr.(fr_regs) ! callee)
      (FUNC: Some callee_f = p ! callee_func)
      (ARGS: CallArgs fr args arg_values),
      step
        p
        (State (mkstack stk_fr stk_frs stk_next stk_frames stk_init) h)
        []
        (State
          (mkstack
            stk_next
            (stk_fr :: stk_frs)
            (Pos.succ stk_next)
            (PTrie.set (PTrie.remove stk_frames stk_fr) stk_next
              (mkframe
                (create_frame callee_f)
                PTrie.empty
                arg_values
                callee_func
                callee_f.(fn_entry)
                ))
            stk_init)
          h)
  .

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

