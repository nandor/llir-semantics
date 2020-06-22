(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Require Import LLIR.Maps.
Require Export LLIR.Values.
Require Export LLIR.Types.

Import ListNotations.



Record object := mkobject
  { obj_sizre : positive
  ; obj_align: positive
  }.

Inductive unop : Type :=
  | LLSext
  | LLZext
  | LLFext
  | LLXext
  | LLTrunc
  | LLNeg
  | LLBitcast
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
  | LLInt (dst: reg) (next: node) (value: INT.t)
  | LLSelect (dst: (ty * reg)) (next: node) (cond: reg) (vt: reg) (vf: reg)
  | LLFrame (dst: reg) (next: node) (object: positive) (offset: nat)
  | LLGlobal (dst: reg) (next: node) (segment: positive) (object: positive) (offset: nat)
  | LLFunc (dst: reg) (next: node) (func: name)
  | LLUndef (dst: (ty * reg)) (next: node)
  | LLUnop (dst: (ty * reg)) (next: node) (op: unop) (arg: reg)
  | LLBinop (dst: (ty * reg)) (next: node) (op: binop) (lhs: reg) (rhs: reg)
  | LLMov (dst: (ty * reg)) (next: node) (src: reg)
  | LLSyscall (dst: reg) (next: node) (sno: reg) (args: list reg)
  | LLCall (dst: option (ty * reg)) (next: node) (callee: reg) (args: list reg)
  | LLInvoke (dst: option (ty * reg)) (next: node) (callee: reg) (args: list reg) (exn: node)
  | LLTCall (callee: reg) (args: list reg)
  | LLTInvoke (callee: reg) (args: list reg) (exn: node)
  | LLSt (next: node) (addr: reg) (value: reg)
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


Inductive InstDefs: inst -> reg -> Prop :=
  | defs_ld:
    forall (t: ty) (dst: reg) (next: node) (addr: reg),
      InstDefs (LLLd (t, dst) next addr) dst
  | defs_arg:
    forall (t: ty) (dst: reg) (next: node) (index: nat),
      InstDefs (LLArg (t, dst) next index) dst
  | defs_int:
    forall (dst: reg) (next: node) (value: INT.t),
      InstDefs (LLInt dst next value) dst
  | defs_mov:
    forall (t: ty) (dst: reg) (next: node) (src: reg),
      InstDefs (LLMov (t, dst) next src) dst
  | defs_select:
    forall (t: ty) (dst: reg) (next: node) (cond: reg) (vt: reg) (vf: reg),
      InstDefs (LLSelect (t, dst) next cond vt vf) dst
  | defs_frame:
    forall (dst: reg) (next: node) (object: positive) (offset: nat),
      InstDefs (LLFrame dst next object offset) dst
  | defs_global:
    forall (dst: reg) (next: node) (segment: positive) (object: positive) (offset: nat),
      InstDefs (LLGlobal dst next segment object offset) dst
  | defs_func:
    forall (dst: reg) (next: node) (id: name),
      InstDefs (LLFunc dst next id) dst
  | defs_undef:
    forall (t: ty) (dst: reg) (next: node),
      InstDefs (LLUndef (t, dst) next) dst
  | defs_unop:
    forall (t: ty) (dst: reg) (next: node) (op: unop) (arg: reg),
      InstDefs (LLUnop (t, dst) next op arg) dst
  | defs_binop:
    forall (t: ty) (dst: reg) (next: node) (op: binop) (lhs: reg) (rhs: reg),
      InstDefs (LLBinop (t, dst) next op lhs rhs) dst
  | defs_syscall:
    forall (dst: reg) (next: node) (sno: reg) (args: list reg),
      InstDefs (LLSyscall dst next sno args) dst
  | defs_call:
    forall (t: ty) (dst: reg) (next: node) (callee: reg) (args: list reg),
      InstDefs (LLCall (Some (t, dst)) next callee args) dst
  | defs_invoke:
    forall (t: ty) (dst: reg) (next: node) (callee: reg) (args: list reg) (exn: node),
      InstDefs (LLInvoke (Some (t, dst)) next callee args exn) dst
  .


(* Returns the register defined by an instruction and its type. *)
Definition get_inst_ty_def (i: inst): option (ty * reg) :=
  match i with
  | LLSyscall dst _ _ _ => Some (sys_ret_ty, dst)
  | LLCall dst _ _ _ => dst
  | LLTCall _ _ => None
  | LLInvoke dst _ _ _ _ => dst
  | LLTInvoke _ _ _ => None

  | LLArg dst _ _ => Some dst
  | LLInt dst _ v =>
    let t := match v with
      | INT.Int8 _ => I8
      | INT.Int16 _ => I16
      | INT.Int32 _ => I32
      | INT.Int64 _ => I64
      end
    in Some (TInt t, dst)
  | LLMov dst _ _ => Some dst

  | LLFrame dst _ _ _ => Some (ptr_ty, dst)
  | LLGlobal dst _ _ _ _ => Some (ptr_ty, dst)
  | LLFunc dst _ _ => Some (ptr_ty, dst)

  | LLLd dst _ _ => Some dst
  | LLUndef dst _ => Some dst
  | LLUnop dst _ _ _ => Some dst
  | LLBinop dst _ _ _ _ => Some dst
  | LLSelect dst _ _ _ _ => Some dst

  | LLSt _ _ _ => None
  | LLRet _ => None
  | LLJcc _ _ _ => None
  | LLJmp _ => None
  | LLTrap => None
  end.

Definition get_inst_def (i: inst): option reg :=
  option_map snd (get_inst_ty_def i).

Lemma get_inst_def_defs:
  forall (i: inst) (r: reg),
    get_inst_def i = Some r <-> InstDefs i r.
Proof.
  intros i r; split; intros H.
  {
    destruct i;
      try match goal with
      | [ dst: option (ty * reg) |- _ ] => destruct dst
      end;
      try match goal with
      | [ dst: ty * reg |- _ ] => destruct dst
      end;
      inversion H as [Hr];
      try constructor.
  }
  {
    inversion H; simpl; reflexivity.
  }
Qed.

Inductive PhiDefs: phi -> reg -> Prop :=
  | defs_phi:
    forall (t: ty) (dst: reg) (ins: list (node * reg)),
      PhiDefs (LLPhi (t, dst) ins) dst
  .

Inductive InstUses: inst -> reg -> Prop :=
  | uses_ld:
    forall (dst: (ty * reg)) (next: node) (addr: reg),
      InstUses (LLLd dst next addr) addr
  | uses_mov:
    forall (dst: (ty * reg)) (next: node) (src: reg),
      InstUses (LLMov dst next src) src
  | uses_select_cond:
    forall (dst: (ty * reg)) (next: node) (cond: reg) (vt: reg) (vf: reg),
      InstUses (LLSelect dst next cond vt vf) cond
  | uses_select_true:
    forall (dst: (ty * reg)) (next: node) (cond: reg) (vt: reg) (vf: reg),
      InstUses (LLSelect dst next cond vt vf) vt
  | uses_select_false:
    forall (dst: (ty * reg)) (next: node) (cond: reg) (vt: reg) (vf: reg),
      InstUses (LLSelect dst next cond vt vf) vf
  | uses_unop:
    forall (dst: (ty * reg)) (next: node) (op: unop) (arg: reg),
      InstUses (LLUnop dst next op arg) arg
  | uses_binop_lhs:
    forall (dst: (ty * reg)) (next: node) (op: binop) (lhs: reg) (rhs: reg),
      InstUses (LLBinop dst next op lhs rhs) lhs
  | uses_binop_rhs:
    forall (dst: (ty * reg)) (next: node) (op: binop) (lhs: reg) (rhs: reg),
      InstUses (LLBinop dst next op lhs rhs) rhs
  | uses_syscall_sno:
    forall (dst: reg) (next: node) (sno: reg) (args: list reg),
      InstUses (LLSyscall dst next sno args) sno
  | uses_syscall_arg:
    forall (dst: reg) (next: node) (sno: reg) (arg: reg) (args: list reg)
      (ARG: In arg args),
      InstUses (LLSyscall dst next sno args) arg
  | uses_call_callee:
    forall (dst: option (ty * reg)) (next: node) (callee: reg) (args: list reg),
      InstUses (LLCall dst next callee args) callee
  | uses_call_arg:
    forall (dst: option (ty * reg)) (next: node) (callee: reg) (arg: reg) (args: list reg)
      (ARG: In arg args),
      InstUses (LLCall dst next callee args) arg
  | uses_invoke_callee:
    forall (dst: option (ty * reg)) (next: node) (callee: reg) (args: list reg) (exn: node),
      InstUses (LLInvoke dst next callee args exn) callee
  | uses_invoke_arg:
    forall (dst: option (ty * reg)) (next: node) (callee: reg) (arg: reg) (args: list reg) (exn: node)
      (ARG: In arg args),
      InstUses (LLInvoke dst next callee args exn) arg
  | uses_tcall_callee:
    forall (callee: reg) (args: list reg),
      InstUses (LLTCall callee args) callee
  | uses_tcall_arg:
    forall (callee: reg) (arg: reg) (args: list reg)
      (ARG: In arg args),
      InstUses (LLTCall callee args) arg
  | uses_tinvoke_callee:
    forall (callee: reg) (args: list reg) (exn: node),
      InstUses (LLTInvoke callee args exn) callee
  | uses_tinvoke_arg:
    forall (callee: reg) (arg: reg) (args: list reg) (exn: node)
      (ARG: In arg args),
      InstUses (LLTInvoke callee args exn) arg
  | uses_st_addr:
    forall (next: node) (addr: reg) (val: reg),
      InstUses (LLSt next addr val) addr
  | uses_st_val:
    forall (next: node) (addr: reg) (val: reg),
      InstUses (LLSt next addr val) val
  | uses_ret:
    forall (value: reg),
      InstUses (LLRet (Some value)) value
  | uses_jcc:
    forall (cond: reg) (bt: node) (bf: node),
      InstUses (LLJcc cond bt bf) cond
  .

Inductive PhiUses: phi -> reg -> reg -> Prop :=
  | phi_uses:
    forall (dst: (ty * reg)) (ins: list (node * reg)) (n: node) (r: reg)
      (ARG: In (n, r) ins),
      PhiUses (LLPhi dst ins) n r
  .

Definition PhiBlockUses (phis: list phi) (n: node) (r: reg): Prop :=
  Exists (fun phi => PhiUses phi n r) phis.

Inductive Succeeds: inst -> node -> Prop :=
  | succ_arg:
    forall (dst: (ty * reg)) (next: node) (index: nat),
      Succeeds (LLArg dst next index) next
  | succ_int:
    forall (dst: reg) (next: node) (value: INT.t),
      Succeeds (LLInt dst next value) next
  | succ_frame:
    forall (dst: reg) (next: node) (object: positive) (offset: nat),
      Succeeds (LLFrame dst next object offset) next
  | succ_global:
    forall (dst: reg) (next: node) (segment: positive) (object: positive) (offset: nat),
      Succeeds (LLGlobal dst next segment object offset) next
  | succ_func:
    forall (dst: reg) (next: node) (id: name),
      Succeeds (LLFunc dst next id) next
  | succ_undef:
    forall (dst: (ty * reg)) (next: node),
      Succeeds (LLUndef dst next) next
  | succ_ld:
    forall (dst: (ty * reg)) (next: node) (addr: reg),
      Succeeds (LLLd dst next addr) next
  | succ_mov:
    forall (dst: (ty * reg)) (next: node) (src: reg),
      Succeeds (LLMov dst next src) next
  | succ_select:
    forall (dst: (ty * reg)) (next: node) (cond: reg) (vt: reg) (vf: reg),
      Succeeds (LLSelect dst next cond vt vf) next
  | succ_unop:
    forall (dst: (ty * reg)) (next: node) (op: unop) (arg: reg),
      Succeeds (LLUnop dst next op arg) next
  | succ_binop:
    forall (dst: (ty * reg)) (next: node) (op: binop) (lhs: reg) (rhs: reg),
      Succeeds (LLBinop dst next op lhs rhs) next
  | succ_syscall:
    forall (dst: reg) (next: node) (sno: reg) (args: list reg),
      Succeeds (LLSyscall dst next sno args) next
  | succ_call:
    forall (dst: option (ty * reg)) (next: node) (callee: reg) (args: list reg),
      Succeeds (LLCall dst next callee args) next
  | succ_invoke_next:
    forall (dst: option (ty * reg)) (next: node) (callee: reg) (args: list reg) (exn: node),
      Succeeds (LLInvoke dst next callee args exn) next
  | succ_invoke_exn:
    forall (dst: option (ty * reg)) (next: node) (callee: reg) (args: list reg) (exn: node),
      Succeeds (LLInvoke dst next callee args exn) exn
  | succ_tinvoke:
    forall (callee: reg) (args: list reg) (exn: node),
      Succeeds (LLTInvoke callee args exn) exn
  | succ_st:
    forall (next: node) (addr: reg) (val: reg),
      Succeeds (LLSt next addr val) next
  | succ_jcc_true:
    forall (cond: reg) (bt: node) (bf: node),
      Succeeds (LLJcc cond bt bf) bt
  | succ_jcc_false:
    forall (cond: reg) (bt: node) (bf: node),
      Succeeds (LLJcc cond bt bf) bf
  | succ_jmp:
    forall (target: node),
      Succeeds (LLJmp target) target
  .

Definition is_terminator (i: inst): bool :=
  match i with
  | LLLd _ _ _ => false
  | LLArg _ _ _ => false
  | LLInt _ _ _ => false
  | LLMov _ _ _ => false
  | LLFrame _ _ _ _ => false
  | LLFunc _ _ _ => false
  | LLGlobal _ _ _ _ _ => false
  | LLUndef _ _ => false
  | LLUnop _ _ _ _ => false
  | LLBinop _ _ _ _ _ => false
  | LLSelect _ _ _ _ _ => false
  | LLSyscall _ _ _ _ => true
  | LLCall _ _ _ _ => true
  | LLInvoke _ _ _ _ _ => true
  | LLTCall _ _ => true
  | LLTInvoke _ _ _ => true
  | LLSt next _ _ => false
  | LLRet _ => true
  | LLJcc _ _ _ => true
  | LLJmp _ => true
  | LLTrap => true
  end.

Definition has_effect (i: inst): bool :=
  match i with
  | LLLd _ _ _ => false
  | LLArg _ _ _ => false
  | LLInt _ _ _ => false
  | LLMov _ _ _ => false
  | LLFrame _ _ _ _ => false
  | LLFunc _ _ _ => false
  | LLGlobal _ _ _ _ _ => false
  | LLUndef _ _ => false
  | LLUnop _ _ _ _ => false
  | LLBinop _ _ _ _ _ => false
  | LLSelect _ _ _ _ _ => false
  | LLSyscall _ _ _ _ => true
  | LLCall _ _ _ _ => true
  | LLInvoke _ _ _ _ _ => true
  | LLTCall _ _ => true
  | LLTInvoke _ _ _ => true
  | LLSt next _ _ => true
  | LLRet _ => false
  | LLJcc _ _ _ => false
  | LLJmp _ => false
  | LLTrap => true
  end.

Inductive Terminator: inst -> Prop :=
  | term_ret:
    forall (ret: option reg),
      Terminator (LLRet ret)
  | term_jcc:
    forall (cond: reg) (bt: node) (bf: node),
      Terminator (LLJcc cond bt bf)
  | term_jmp:
    forall (target: node),
      Terminator (LLJmp target)
  | term_trap:
    Terminator LLTrap
  | term_syscall:
    forall (dst: reg) (next: node) (sno: reg) (args: list reg),
      Terminator (LLSyscall dst next sno args)
  | term_call:
    forall (dst: option (ty * reg)) (next: node) (callee: reg) (args: list reg),
      Terminator (LLCall dst next callee args)
  | term_tcall:
    forall (callee: reg) (args: list reg),
      Terminator (LLTCall callee args)
  | term_tinvoke:
    forall (callee: reg) (args: list reg) (exn: node),
      Terminator (LLTInvoke callee args exn)
  | term_invoke:
    forall (dst: option (ty * reg)) (next: node) (callee: reg) (args: list reg) (exn: node),
      Terminator (LLInvoke dst next callee args exn)
  .

Inductive Callee: inst -> reg -> Prop :=
  | callee_call:
    forall (dst: option (ty * reg)) (next: node) (callee: reg) (args: list reg),
      Callee (LLCall dst next callee args) callee
  | callee_invoke:
    forall (dst: option (ty * reg)) (next: node) (callee: reg) (args: list reg) (exn: node),
      Callee (LLInvoke dst next callee args exn) callee
  | callee_tcall:
    forall (callee: reg) (args: list reg),
      Callee (LLTCall callee args) callee
  | callee_tinvoke:
    forall (callee: reg) (args: list reg) (exn: node),
      Callee (LLTInvoke callee args exn) callee
  .

Inductive VoidCallSite: inst -> Prop :=
  | void_site_call:
    forall (next: node) (callee: reg) (args: list reg),
      VoidCallSite (LLCall None next callee args)
  | void_site_invoke:
    forall (next: node) (callee: reg) (args: list reg) (exn: node),
      VoidCallSite (LLInvoke None next callee args exn)
  .

Inductive CallSite: inst -> ty -> reg -> Prop :=
  | call_site_call:
    forall (t: ty) (dst: reg) (next: node) (callee: reg) (args: list reg),
      CallSite (LLCall (Some (t, dst)) next callee args) t dst
  | call_site_invoke:
    forall (t: ty) (dst: reg) (next: node) (callee: reg) (args: list reg) (exn: node),
      CallSite (LLInvoke (Some (t, dst)) next callee args exn) t dst
  .

Inductive ReturnAddress: inst -> node -> Prop :=
  | ret_addr_call:
    forall (dst: option (ty * reg)) (next: node) (callee: reg) (args: list reg),
      ReturnAddress (LLCall dst next callee args) next
  | ret_addr_invoke:
    forall (dst: option (ty * reg)) (next: node) (callee: reg) (args: list reg) (exn: node),
      ReturnAddress (LLInvoke dst next callee args exn) next
  .

Lemma is_terminator_terminator:
  forall (i: inst),
    is_terminator i = true <-> Terminator i.
Proof.
  intros i. split; intros H; destruct i; try inversion H; constructor.
Qed.

Definition is_exit (i: inst): bool :=
  match i with
  | LLLd _ _ _ => false
  | LLArg _ _ _ => false
  | LLInt _ _ _ => false
  | LLMov _ _ _ => false
  | LLFrame _ _ _ _ => false
  | LLFunc _ _ _ => false
  | LLGlobal _ _ _ _ _ => false
  | LLUndef _ _ => false
  | LLUnop _ _ _ _ => false
  | LLBinop _ _ _ _ _ => false
  | LLSelect _ _ _ _ _ => false
  | LLSyscall _ _ _ _ => false
  | LLCall _ _ _ _ => false
  | LLInvoke _ _ _ _ _ => false
  | LLTCall _ _ => true
  | LLTInvoke _ _ _ => false
  | LLSt next _ _ => false
  | LLRet _ => true
  | LLJcc _ _ _ => false
  | LLJmp _ => false
  | LLTrap => true
  end.

Inductive Exit: inst -> Prop :=
  | exit_ret:
    forall (ret: option reg),
      Exit (LLRet ret)
  | exit_trap:
    Exit LLTrap
  | exit_tcall:
    forall (callee: reg) (args: list reg),
      Exit (LLTCall callee args)
  .

Lemma is_exit_exit:
  forall (i: inst),
    is_exit i = true <-> Exit i.
Proof.
  intros i.
  split; intros H.
  + destruct i; simpl in H; inversion H; constructor.
  + inversion H; simpl; reflexivity.
Qed.

Section FUNCTION.
  Variable f: func.

  Inductive InstDefinedAt: node -> reg -> Prop :=
    | inst_defined_at:
      forall (n: node) (r: reg) (i: inst)
        (INST: Some i = f.(fn_insts) ! n)
        (DEFS: InstDefs i r),
        InstDefinedAt n r
    .

  Inductive PhiDefinedAt: node -> reg -> Prop :=
    | phi_defined_at:
      forall (n: node) (r: reg) (phis: list phi)
        (PHIS: Some phis = f.(fn_phis) ! n)
        (DEFS: Exists (fun phi => PhiDefs phi r) phis),
        PhiDefinedAt n r
    .

  Inductive DefinedAt: node -> reg -> Prop :=
    | defined_at_inst:
      forall (n: node) (r: reg) (DEF: InstDefinedAt n r),
        DefinedAt n r
    | defined_at_phi:
      forall (n: node) (r: reg) (DEF: PhiDefinedAt n r),
        DefinedAt n r
    .

  Lemma inst_defined_at_dec:
    forall (n: node) (r: reg),
      {InstDefinedAt n r} + {~InstDefinedAt n r}.
  Proof.
    intros n r.
    destruct ((fn_insts f) ! n) as [inst|] eqn:Einst.
    {
      destruct (get_inst_def inst) as [dst|] eqn:Edst.
      {
        destruct (Pos.eq_dec dst r) as [Eq|Ne].
        {
          subst r. left. apply inst_defined_at with (i := inst); auto.
          apply get_inst_def_defs; auto.
        }
        {
          right; intros contra; inversion contra.
          rewrite Einst in INST; inversion INST; subst i.
          apply get_inst_def_defs in DEFS.
          rewrite Edst in DEFS; inversion DEFS.
          contradiction.
        }
      }
      {
        right; intros contra; inversion contra.
        apply get_inst_def_defs in DEFS.
        rewrite Einst in INST; inversion INST; subst i.
        rewrite Edst in DEFS; inversion DEFS.
      }
    }
    {
      right; intros contra; inversion contra.
      rewrite Einst in INST; inversion INST.
    }
  Qed.

  Lemma phi_defs_dec:
    forall (p: phi) (r: reg),
      {PhiDefs p r} + {~PhiDefs p r}.
  Proof.
    intros p r. destruct p; destruct dst.
    destruct (Pos.eq_dec p r); subst.
    - left; constructor.
    - right; intros contra; inversion contra; contradiction.
  Qed.

  Lemma phi_defined_at_dec:
    forall (n: node) (r: reg),
      {PhiDefinedAt n r} + {~PhiDefinedAt n r}.
  Proof.
    intros n r.
    destruct ((fn_phis f) ! n) as [phis|] eqn:Ephis.
    {
      destruct (Exists_dec (fun phi => PhiDefs phi r) phis).
      {
        intros phi.
        generalize (phi_defs_dec phi r); intros Hdec; destruct Hdec; auto.
      }
      {
        left. apply phi_defined_at with phis; auto.
      }
      {
        right; intros contra; inversion contra.
        rewrite Ephis in PHIS; inversion PHIS; subst.
        contradiction.
      }
    }
    {
      right; intros contra; inversion contra.
      rewrite Ephis in PHIS; inversion PHIS.
    }
  Qed.

  Lemma defined_at_dec:
    forall (n: node) (r: reg),
      {DefinedAt n r} + {~DefinedAt n r}.
  Proof.
    intros n r.
    destruct (inst_defined_at_dec n r).
    - left; apply defined_at_inst; auto.
    - destruct (phi_defined_at_dec n r).
      + left; apply defined_at_phi; auto.
      + right; intros contra; inversion contra; contradiction.
  Qed.

  Inductive InstUsedAt: node -> reg -> Prop :=
    | inst_used_at:
      forall (n: node) (r: reg) (i: inst)
        (INST: Some i = f.(fn_insts) ! n)
        (USES: InstUses i r),
        InstUsedAt n r.

  Inductive PhiUsedAt: node -> reg -> Prop :=
    | phi_used_at:
      forall (n: node) (r: reg) (block: node) (phis: list phi)
        (PHIS: Some phis = f.(fn_phis) ! block)
        (USES: PhiBlockUses phis n r),
        PhiUsedAt n r
    .

  Inductive UsedAt: node -> reg -> Prop :=
    | used_at_inst:
      forall (n: node) (r: reg) (USE: InstUsedAt n r),
        UsedAt n r
    | used_at_phi:
      forall (n: node) (r: reg) (USE: PhiUsedAt n r),
        UsedAt n r
    .

  Inductive SuccOf: node -> node -> Prop :=
    | succ_of:
        forall (n: node) (m: node) (i: inst)
          (HN: Some i = f.(fn_insts) ! n)
          (HM: None <> f.(fn_insts) ! m)
          (SUCC: Succeeds i m),
          SuccOf n m.

  Inductive TermAt: node -> Prop :=
    | term_at:
      forall (i: inst) (n: node)
        (INST: Some i = f.(fn_insts) ! n)
        (TERM: Terminator i),
        TermAt n.

  Lemma non_terminal_unique_successor:
    forall (n: node) (s: node) (s': node),
      ~TermAt n ->
       SuccOf n s ->
       SuccOf n s' ->
       s = s'.
  Proof.
    intros n s s' Hterm Hsucc Hsucc'.
    destruct ((fn_insts f) ! n) as [i|] eqn:Einst.
    {
      destruct i eqn:Ei;
        try (
          assert (TermAt n); 
          [apply term_at with i; subst; auto; constructor|]; 
          contradiction
        );
        inversion Hsucc; inversion Hsucc';
        rewrite Einst in HN; inversion HN; subst i0; clear HN; inversion SUCC;
        rewrite Einst in HN0; inversion HN0; subst i1; clear HN0; inversion SUCC0;
        subst; reflexivity.
    }
    {
      inversion Hsucc; rewrite Einst in HN; inversion HN.
    }
  Qed.

  Inductive ExitAt: node -> Prop :=
    | exit_at:
      forall (i: inst) (n: node)
        (INST: Some i = f.(fn_insts) ! n)
        (EXIT: Exit i),
        ExitAt n.

  Theorem exit_no_succ:
    forall (n: node),
      ExitAt n -> ~exists (m: node), SuccOf n m.
  Proof.
    intros n Hexit contra; destruct contra as [m Hsucc].
    inversion Hexit.
    inversion Hsucc.
    rewrite <- INST in HN; inversion HN; subst.
    inversion EXIT; subst; inversion SUCC; subst.
  Qed.
End FUNCTION.

Definition get_successors (i: inst) :=
  match i with
  | LLLd _ next _ => [next]
  | LLArg _ next _ => [next]
  | LLInt _ next _ => [next]
  | LLMov _ next _ => [next]
  | LLFrame _ next _ _ => [next]
  | LLFunc _ next _ => [next]
  | LLGlobal _ next _ _ _ => [next]
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
  split; intros H.
  {
    unfold get_successors in H.
    destruct i; repeat destruct H as [H|H];
    subst; try inversion H; constructor.
  }
  {
    inversion H; simpl; auto.
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
    unfold get_predecessors in Hin.
    destruct ((fn_insts f) ! n) eqn:Einst.
    {
      apply PTrie.keys_inversion in Hin.
      destruct Hin as [k Hin].
      apply PTrie.map_opt_inversion in Hin.
      destruct Hin as [inst [Hinst Hpred]].
      apply succ_of with (i := inst); auto.
      { intros contra. rewrite Einst in contra. inversion contra. }
      {
        unfold get_successors in Hpred. unfold existsb in Hpred.
        destruct inst; simpl;
          repeat match goal with
          | [ H: context [ Pos.eqb ?v n ] |- _ ] =>
            destruct (Pos.eqb v n) eqn:E;
            simpl in H;
            [apply Pos.eqb_eq in E; subst; constructor|clear E]
          | [ H: Some ?v = None |- _ ] =>
            inversion H
          end.
      }
    }
    {
      inversion Hin.
    }
  }
  {
    intros Hsucc.
    inversion Hsucc.
    destruct ((fn_insts f) ! n) as [inst'|] eqn:En; try contradiction.
    unfold get_predecessors.
    rewrite En. subst. clear HM.
    apply PTrie.keys_correct with (v := i).
    apply PTrie.filter_correct; auto.
    apply List.existsb_exists. exists n.
    split; [|apply Pos.eqb_eq; reflexivity].
    destruct i; inversion SUCC; simpl; auto.
  }
Qed.
