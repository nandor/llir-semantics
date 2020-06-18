(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Require Import LLIR.LLIR.
Require Import LLIR.Maps.
Require Import LLIR.Values.
Require Export LLIR.Type.


Definition type_env := PTrie.t ty.

(* Type environment from instructions. *)
Definition ty_env_inst (insts: inst_map): type_env :=
  PTrie.fold
    (fun env _ i =>
      match get_inst_ty_def i with
      | Some (ty, dst) => PTrie.set env dst ty
      | None => env
      end)
    insts PTrie.empty.

(* Type environment from phis. *)
Definition ty_env_phi (phis: phi_map): type_env :=
  PTrie.fold
    (fun env _ block =>
      List.fold_left
        (fun env p =>
          match p with
          | LLPhi (ty, dst) _ => PTrie.set env dst ty
          end)
        block env)
    phis PTrie.empty.

(* Type environment for all registers. *)
Definition ty_env (f: func): type_env :=
  PTrie.union (ty_env_inst f.(fn_insts)) (ty_env_phi f.(fn_phis)).

(* Holds if the evironment has the correct type for a reg. *)
Definition well_typed_reg (env: type_env) (r: reg) (t: ty) :=
  env ! r = Some t.

(* Typing rules for binary instructions. *)
Inductive WellTypedBinop: binop -> ty -> ty -> ty -> Prop :=
  | type_cmp:
    forall (t: ty) (dt: ty),
      WellTypedBinop LLCmp t t dt
  | type_add:
    forall (t: ty),
      WellTypedBinop LLAdd t t t
  | type_sll:
    forall (tl: ty_int) (tr: ty_int),
      WellTypedBinop LLSll (TInt tl) (TInt tr) (TInt tl)
  .

(* Typing rules for unary instructions. *)
Inductive WellTypedUnop: unop -> ty -> ty -> Prop :=
  | type_sext_i32_i64: WellTypedUnop LLSext (TInt I32) (TInt I64)
  .

(* Typing rules for instructions. *)
Inductive WellTypedInst: type_env -> inst -> Prop :=
  | type_jmp:
    forall (env: type_env) (target: node),
      WellTypedInst env (LLJmp target)
  | type_jcc:
    forall (env: type_env) (cond: reg) (bt: node) (bf: node) (i: ty_int)
      (COND_TY: well_typed_reg env cond (TInt i)),
      WellTypedInst env (LLJcc cond bt bf)
  | type_ret:
    forall (env: type_env) (ret: reg) (t: ty)
      (RET_TY: well_typed_reg env ret t),
      WellTypedInst env (LLRet (Some ret))
  | type_ret_void:
    forall (env: type_env),
      WellTypedInst env (LLRet None)
  | type_st:
    forall (env: type_env) (next: node) (addr: reg) (val: reg) (t: ty)
      (ADDR_TY: well_typed_reg env addr ptr_ty)
      (VAL_TY: well_typed_reg env val t),
      WellTypedInst env (LLSt next addr val)
  | type_undef:
    forall (env: type_env) (next: node) (dst: reg) (t: ty)
      (DST_TY: well_typed_reg env dst t),
      WellTypedInst env (LLUndef (t, dst) next)
  | type_ld:
    forall (env: type_env) (next: node) (dst: reg) (t: ty) (addr: reg)
      (ADDR_TY: well_typed_reg env addr ptr_ty)
      (DST_TY: well_typed_reg env dst t),
      WellTypedInst env (LLLd (t, dst) next addr)
  | type_frame:
    forall (env: type_env) (dst:reg) (next: node)
      (object: positive) (offset: nat)
      (DST_TY: well_typed_reg env dst ptr_ty),
      WellTypedInst env (LLFrame dst next object offset)
  | type_global:
    forall (env: type_env) (dst: reg) (next: node)
      (segment: positive) (object: positive) (offset: nat)
      (DST_TY: well_typed_reg env dst ptr_ty),
      WellTypedInst env (LLGlobal dst next segment object offset)
  | type_int:
    forall (env: type_env) (dst: reg) (next: node) (val: INT.t) (t: ty)
      (INT_TY: TypeOfInt val t)
      (DST_TY: well_typed_reg env dst t),
      WellTypedInst env (LLInt dst next val)
  | type_arg:
    forall (env: type_env) (t: ty) (dst: reg) (next: node) (idx: nat)
      (DST_TY: well_typed_reg env dst t),
      WellTypedInst env (LLArg (t, dst) next idx)
  | type_binop:
    forall (env: type_env) (op: binop) (next: node)
      (l: reg) (tl: ty) (r: reg) (tr: ty) (dst: reg) (t: ty)
      (LHS_TY: well_typed_reg env l tl)
      (RHS_TY: well_typed_reg env r tr)
      (DST_TY: well_typed_reg env dst t)
      (OP: WellTypedBinop op tl tr t),
      WellTypedInst env (LLBinop (t, dst) next op l r)
  | type_unop:
    forall (env: type_env) (op: unop) (next: node)
      (arg: reg) (argt: ty) (dst: reg) (t: ty)
      (ARG_TY: well_typed_reg env arg argt)
      (DST_TY: well_typed_reg env dst t)
      (OP: WellTypedUnop op argt t),
      WellTypedInst env (LLUnop (t, dst) next op arg)
  | type_mov:
    forall (env: type_env) (op: unop) (next: node)
      (arg: reg) (dst: reg) (t: ty)
      (ARG_TY: well_typed_reg env arg t)
      (DST_TY: well_typed_reg env dst t),
      WellTypedInst env (LLMov (t, dst) next arg)
  | type_invoke_void:
    forall (env: type_env) (next: node)
      (dst: reg) (t: ty)
      (callee: reg) (args: list reg) (exn: node)
      (CALLEE_TY: well_typed_reg env callee ptr_ty),
      WellTypedInst env (LLInvoke (Some (t, dst)) next callee args exn)
  | type_call_void:
    forall (env: type_env) (next: node)
      (callee: reg) (args: list reg)
      (CALLEE_TY: well_typed_reg env callee ptr_ty),
      WellTypedInst env (LLCall None next callee args)
  | type_call:
    forall (env: type_env) (next: node)
      (callee: reg) (args: list reg) (dst: reg) (t: ty)
      (CALLEE_TY: well_typed_reg env callee ptr_ty)
      (DST_TY: well_typed_reg env dst t),
      WellTypedInst env (LLCall (Some (t, dst)) next callee args)
  | type_tcall:
    forall (env: type_env)
      (callee: reg) (args: list reg)
      (CALLEE_TY: well_typed_reg env callee ptr_ty),
      WellTypedInst env (LLTCall callee args)
  | type_syscall:
    forall (env: type_env) (next: node)
      (sno: reg) (args: list reg) (tsno: ty_int) (dst: reg)
      (SNO_TY: well_typed_reg env sno sys_no_ty)
      (DST_TY: well_typed_reg env dst sys_ret_ty),
      WellTypedInst env (LLSyscall dst next sno args)
  | type_trap:
    forall (env: type_env),
      WellTypedInst env LLTrap
  .

Inductive WellTypedInsts: type_env -> inst_map -> Prop :=
  | well_typed_insts:
    forall
      (env: type_env) (insts: inst_map)
      (INSTS: forall (n: node) (i: inst), Some i = insts ! n -> WellTypedInst env i),
        WellTypedInsts env insts.

Inductive WellTypedPhi: type_env -> phi -> Prop :=
  | well_typed_phi:
    forall (env: type_env) (dst: reg) (t: ty) (ins: list (node * reg))
      (INS: forall (n: node) (r: reg), In (n, r) ins -> well_typed_reg env r t),
      WellTypedPhi env (LLPhi (t, dst) ins)
  .

Inductive WellTypedPhis: type_env -> phi_map -> Prop :=
  | well_typed_phis:
    forall
      (env: type_env) (phis: phi_map)
      (PHIS:
        forall (n: node) (block: list phi) (p: phi),
          Some block = phis ! n ->
          In p block ->
          WellTypedPhi env p),
    WellTypedPhis env phis.

Inductive WellTypedFunc: func -> Prop :=
  | well_typed_func:
    forall (f: func)
      (INSTS: WellTypedInsts (ty_env f) f.(fn_insts))
      (PHIS: WellTypedPhis (ty_env f) f.(fn_phis)),
      WellTypedFunc f
  .

Inductive WellTypedProg: prog -> Prop :=
  | well_typed_prog:
    forall (p: prog)
      (FUNCS: forall (n: name) (f: func), Some f = p ! n -> WellTypedFunc f),
      WellTypedProg p
  .
