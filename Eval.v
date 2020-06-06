(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Nat.

Require Import LLIR.State.
Require Import LLIR.LLIR.
Require Import LLIR.Values.
Require Import LLIR.Maps.
Require Import LLIR.Typing.

Import ListNotations.



Inductive syscall := .

Definition syscall_handler: Type := state -> syscall -> (state * qword).

Definition step_inst
  (f: func)
  (fr: frame)
  (frs: list frame)
  (i: inst): option state :=
  None.
(*
  match i with
  | LLArg dest next idx =>
    None

  | LLInt32 dst next val =>
    None

  | LLUnop (ty, dst) next op arg =>
    None

  | LLBinop (ty, dst) next op lhs rhs=>
    None

  | LLJcc cond bt bf =>
    None

  | LLRet val =>
    None

  | LLJmp target =>
    None

  (* TODO *)
  | LLInvoke callee args dst next exn => None
  | LLLd addr dst next => None
  | LLSt addr val next => None
  | LLInt8 val dst next => None
  | LLInt16 val dst next => None
  | LLFrame obj dst next => None
  | LLGlobal obj dst next => None
  | LLRetVoid => None
  | LLInt64 val dst next => None
  | LLUndef (ty, dst) next => None
  end.
*)

Definition step (p: prog) (st: state) (sys: syscall_handler): option state :=
  match st.(st_stack) with
  | fr :: frs =>
    match p ! (fr.(fr_func)) with
    | Some fn =>
      match fn.(fn_insts) ! (fr.(fr_pc)) with
      | Some inst =>
        step_inst fn fr frs inst
      | None =>
        None
      end
    | _ => None
    end
  | _ => None
  end.
