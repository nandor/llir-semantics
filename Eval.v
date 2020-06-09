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

Axiom step_binop: binop -> ty -> value -> value -> option value.

Axiom step_unop: unop -> ty -> value -> option value.

Axiom get_vreg: frame -> reg -> value.

Axiom set_vreg: frame -> reg -> value -> frame.

Axiom set_pc: frame -> node -> frame.

Axiom is_true: value -> option bool.

Axiom argext: ty -> value -> option value.

Definition step_inst
  (f: func)
  (fr: frame)
  (frs: list frame)
  (i: inst): option state :=

  match i with
  | LLArg (ty, dst) next idx =>
    match (fr.(fr_args) ! (Pos.of_nat idx)) with
    | None => None
    | Some v =>
      match argext ty v with
      | None => None
      | Some v' =>
        let fr' := set_pc (set_vreg fr dst v') next in
        Some {| st_stack := fr' :: frs |}
      end
    end

  | LLInt32 dst next val =>
    let fr' := set_pc (set_vreg fr dst (Val32 val)) next in
    Some {| st_stack := fr' :: frs |}

  | LLUnop (ty, dst) next op arg =>
    let varg := get_vreg fr arg in
    match step_unop op ty varg with
    | None => None
    | Some r =>
      let fr' := set_pc (set_vreg fr dst r) next in
      Some {| st_stack := fr' :: frs |}
    end

  | LLBinop (ty, dst) next op lhs rhs =>
    let vl := get_vreg fr lhs in
    let vr := get_vreg fr rhs in
    match step_binop op ty vl vr with
    | None => None
    | Some r =>
      let fr' := set_pc (set_vreg fr dst r) next in
      Some {| st_stack := fr' :: frs |}
    end

  | LLJcc cond bt bf =>
    let vc := get_vreg fr cond in
    match is_true vc with
    | None => None
    | Some true =>
      Some {| st_stack := set_pc fr bt :: frs |}
    | Some false =>
      Some {| st_stack := set_pc fr bf :: frs |}
    end

  | LLJmp target =>
    Some {| st_stack := set_pc fr target :: frs |}

  | LLRet val =>
    None

  (* TODO *)
  | _ => None
  end.

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
