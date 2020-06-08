(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Require Import LLIR.State.
Require Import LLIR.LLIR.
Require Import LLIR.Maps.
Require Import LLIR.Values.


Definition type_env := PTrie.t ty.



(* Interface containing all target-specific information. *)
Module Type ArchTy.
  Parameter ptr_ty: ty.
End ArchTy.

(* X86-specific typing. *)
Module X86_ArchTy <: ArchTy.
  Definition ptr_ty := TInt I64.
End X86_ArchTy.

(* Generic typing rules *)
Module Type Typing.
  Parameter ptr_ty: ty.
  Parameter ty_env: func -> type_env.
End Typing.

(* LLIR typing rules *)
Module Target_Typing (ARCH: ArchTy) <: Typing.
  Include ARCH.

  (* Returns the register defined by an instruction and its type. *)
  Definition get_inst_def (i: inst): option (ty * reg) :=
    match i with
    | LLInvoke dst _ _ _ _ => dst

    | LLArg dst _ _ => Some dst
    | LLInt8 dst _ _ => Some (TInt I8, dst)
    | LLInt16 dst _ _ => Some (TInt I16, dst)
    | LLInt32 dst _ _ => Some (TInt I32, dst)
    | LLInt64 dst _ _ => Some (TInt I64, dst)

    | LLFrame _ dst _ => Some (ARCH.ptr_ty, dst)
    | LLGlobal _ dst _ => Some (ARCH.ptr_ty, dst)

    | LLLd dst _ _ => Some dst
    | LLUndef dst _ => Some dst
    | LLUnop dst _ _ _ => Some dst
    | LLBinop dst _ _ _ _ => Some dst

    | LLSt _ _ _ => None
    | LLRet _ => None
    | LLJcc _ _ _ => None
    | LLJmp _ => None
    end.

  (* Type environment from instructions. *)
  Definition ty_env_inst (insts: inst_map): type_env :=
    PTrie.fold
      (fun env _ i =>
        match get_inst_def i with
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
  Inductive well_typed_binop: binop -> ty -> ty -> ty -> Prop :=
    | type_bin_cmp:
      forall (t: ty) (dt: ty),
        well_typed_binop LLCmp t t dt
    | type_bin_add:
      forall (t: ty),
        well_typed_binop LLAdd t t t
    .

  (* Typing rules for unary instructions. *)
  Inductive well_typed_unop: unop -> ty -> ty -> Prop :=
    .

  (* Typing rules for instructions. *)
  Inductive well_typed_inst: type_env -> inst -> Prop :=
    | type_jmp:
      forall (env: type_env) (target: node),
        well_typed_inst env (LLJmp target)
    | type_jcc:
      forall (env: type_env) (cond: reg) (bt: node) (bf: node) (i: ty_int)
        (COND_TY: well_typed_reg env cond (TInt i)),
        well_typed_inst env (LLJcc cond bt bf)
    | type_ret:
      forall (env: type_env) (ret: reg) (t: ty)
        (RET_TY: well_typed_reg env ret t),
        well_typed_inst env (LLRet (Some ret))
    | type_ret_void:
      forall (env: type_env),
        well_typed_inst env (LLRet None)
    | type_st:
      forall (env: type_env) (next: node) (addr: reg) (val: reg) (t: ty)
        (ADDR_TY: well_typed_reg env addr ARCH.ptr_ty)
        (VAL_TY: well_typed_reg env val t),
        well_typed_inst env (LLSt next addr val)
    | type_undef:
      forall (env: type_env) (next: node) (dst: reg) (t: ty),
        well_typed_inst env (LLUndef (t, dst) next)
    | type_ld:
      forall (env: type_env) (next: node) (dst: reg) (t: ty) (addr: reg)
        (ADDR_TY: well_typed_reg env addr ARCH.ptr_ty)
        (DST_TY: well_typed_reg env dst t),
        well_typed_inst env (LLLd (t, dst) next addr)
    | type_frame:
      forall (env: type_env) (dst:reg) (next: node) (object: positive)
        (DST_TY: well_typed_reg env dst ARCH.ptr_ty),
        well_typed_inst env (LLFrame dst next object)
    | type_global:
      forall (env: type_env) (dst: reg) (next: node) (object: positive)
        (DST_TY: well_typed_reg env dst ARCH.ptr_ty),
        well_typed_inst env (LLGlobal dst next object)
    | type_int8:
      forall (env: type_env) (dst: reg) (next: node) (val: INT8.t)
        (DST_TY: well_typed_reg env dst (TInt I8)),
        well_typed_inst env (LLInt8 dst next val)
    | type_int16:
      forall (env: type_env) (dst: reg) (next: node) (val: INT16.t)
        (DST_TY: well_typed_reg env dst (TInt I16)),
        well_typed_inst env (LLInt16 dst next val)
    | type_int32:
      forall (env: type_env) (dst: reg) (next: node) (val: INT32.t)
        (DST_TY: well_typed_reg env dst (TInt I32)),
        well_typed_inst env (LLInt32 dst next val)
    | type_int64:
      forall (env: type_env) (dst: reg) (next: node) (val: INT64.t)
        (DST_TY: well_typed_reg env dst (TInt I64)),
        well_typed_inst env (LLInt64 dst next val)
    | type_arg:
      forall (env: type_env) (t: ty) (dst: reg) (next: node) (idx: nat)
        (DST_TY: well_typed_reg env dst t),
        well_typed_inst env (LLArg (t, dst) next idx)
    | type_binop:
      forall (env: type_env) (op: binop) (next: node)
        (l: reg) (tl: ty) (r: reg) (tr: ty) (dst: reg) (t: ty)
        (LHS_TY: well_typed_reg env l tl)
        (RHS_TY: well_typed_reg env r tr)
        (DST_TY: well_typed_reg env dst t)
        (OP: well_typed_binop op tl tr t),
        well_typed_inst env (LLBinop (t, dst) next op l r)
    | type_unop:
      forall (env: type_env) (op: unop) (next: node)
        (arg: reg) (argt: ty) (dst: reg) (t: ty)
        (ARG_TY: well_typed_reg env arg argt)
        (OP: well_typed_unop op argt t),
        well_typed_inst env (LLUnop (t, dst) next op arg)
    | type_invoke_void:
      forall (env: type_env) (next: node)
        (dst: reg) (t: ty)
        (callee: reg) (args: list reg) (exn: option node)
        (CALLEE_TY: well_typed_reg env callee ARCH.ptr_ty),
        well_typed_inst env (LLInvoke (Some (t, dst)) next callee args exn)
    .

  Definition well_typed_insts (env: type_env) (insts: inst_map) :=
    forall (n: node) (i: inst),
      Some i = insts ! n -> well_typed_inst env i.

  Inductive well_typed_phi: type_env -> phi -> Prop :=
    | typed_phi:
      forall (env: type_env) (dst: reg) (t: ty) (ins: list (node * reg))
        (INS: forall (n: node) (r: reg), In (n, r) ins -> well_typed_reg env r t),
        well_typed_phi env (LLPhi (t, dst) ins)
    .

  Definition well_typed_phis (env: type_env) (phis: phi_map) :=
    forall (n: node) (block: list phi) (p: phi),
      Some block = phis ! n ->
      In p block ->
      well_typed_phi env p.

  Definition well_typed (f: func) :=
    well_typed_insts (ty_env f) f.(fn_insts)
    /\
    well_typed_phis (ty_env f) f.(fn_phis).
End Target_Typing.

Module X86_Typing := Target_Typing (X86_ArchTy).
