(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.Lists.List.

Require Import LLIR.State.
Require Import LLIR.LLIR.
Require Import LLIR.Maps.


Definition type_env := PTrie.t ty.

Definition ptr_ty := I64.



Definition get_inst_def (i: inst): option (ty * reg) :=
  match i with
  | LLInvoke dst _ _ _ _ => dst

  | LLArg dst _ _ => Some dst
  | LLInt8 dst _ _ => Some (I8, dst)
  | LLInt16 _ dst _ => Some (I16, dst)
  | LLInt32 _ dst _ => Some (I32, dst)
  | LLInt64 _ dst _ => Some (I64, dst)

  | LLFrame _ dst _ => Some (ptr_ty, dst)
  | LLGlobal _ dst _ => Some (ptr_ty, dst)

  | LLLd dst _ _ => Some dst
  | LLUndef dst _ => Some dst
  | LLUnop dst _ _ _ => Some dst
  | LLBinop dst _ _ _ _ => Some dst

  | LLSt _ _ _ => None
  | LLRet _ => None
  | LLJcc _ _ _ => None
  | LLJmp _ => None
  end.

Definition ty_env_inst (insts: inst_map): type_env :=
  PTrie.fold
    (fun env _ i => 
      match get_inst_def i with
      | Some (ty, dst) => PTrie.set env dst ty
      | None => env
      end)
    insts PTrie.empty.

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

Definition ty_env (f: func): type_env :=
  PTrie.union (ty_env_inst f.(fn_insts)) (ty_env_phi f.(fn_phis)).

Definition well_typed_reg (env: type_env) (r: reg) (ty: ty) :=
  env ! r = Some ty.

(*
Inductive well_typed_inst: type_env -> inst -> Prop := .
  | typed_jmp:

  | LLInvoke dst _ _ _ _ => dst

  | LLArg dst _ _ => Some dst
  | LLInt8 dst _ _ => Some (I8, dst)
  | LLInt16 _ dst _ => Some (I16, dst)
  | LLInt32 _ dst _ => Some (I32, dst)
  | LLInt64 _ dst _ => Some (I64, dst)

  | LLFrame _ dst _ => Some (ptr_ty, dst)
  | LLGlobal _ dst _ => Some (ptr_ty, dst)

  | LLLd dst _ _ => Some dst
  | LLUndef dst _ => Some dst
  | LLUnop dst _ _ _ => Some dst
  | LLBinop dst _ _ _ _ => Some dst

  | LLSt _ _ _ => None
  | LLRet _ => None
  | LLJcc _ _ _ => None
  | LLJmp _ => None
  *)
Definition well_typed_insts (env: type_env) (insts: inst_map) := 
  False.

Inductive well_typed_phi: type_env -> phi -> Prop :=
  | typed_phi:
    forall (env: type_env) (p: phi),
      well_typed_phi env p
  .

Definition well_typed_phis (env: type_env) (phis: phi_map) :=
  False.

Definition well_typed (f: func) :=
  well_typed_insts (ty_env f) f.(fn_insts)
  /\
  well_typed_phis (ty_env f) f.(fn_phis).

