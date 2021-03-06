(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Nat.

Require Import LLIR.LLIR.
Require Import LLIR.Maps.
Require Import LLIR.Typing.
Require Import LLIR.Dom.
Require Import LLIR.Frame.
Require Import LLIR.State.

Import ListNotations.

Definition set_frame (st: state) (fr: frame): state :=
  let stk := st.(st_stack) in
  {| st_stack :=
    {| stk_fr := stk.(stk_fr)
     ; stk_frs := stk.(stk_frs)
     ; stk_next := stk.(stk_next)
     ; stk_frames := PTrie.set stk.(stk_frames) stk.(stk_fr) fr
     ; stk_init := stk.(stk_init)
     |}
   ; st_heap := st.(st_heap)
   |}.

Axiom argext: ty -> value -> option value.

Definition step_inst (fr: frame) (st: state) (i: inst): option state :=
  match i with
  | LLArg (ty, dst) next idx =>
    match nth_error fr.(fr_args) idx  with
    | None => None
    | Some v =>
      match argext ty v with
      | None => None
      | Some v' =>
        let fr' := set_vreg_pc fr dst v' next in
        Some (set_frame st fr')
      end
    end

  | LLInt dst next val =>
    let fr' := set_vreg_pc fr dst (VInt val) next in
    Some (set_frame st fr')

  | LLUnop (ty, dst) next op arg =>
    match fr.(fr_regs) ! arg with
    | Some varg =>
      match step_unop op ty varg with
      | Some r =>
        let fr' := set_vreg_pc fr dst r next in
        Some (set_frame st fr')
      | None => None
      end
    | None => None
    end

  | LLBinop (ty, dst) next op lhs rhs =>
    match fr.(fr_regs) ! lhs with
    | Some vl =>
      match fr.(fr_regs) ! rhs with
      | Some vr =>
        match step_binop op ty vl vr with
        | None => None
        | Some r =>
          let fr' := set_vreg_pc fr dst r next in
          Some (set_frame st fr')
        end
      | None => None
      end
    | None => None
    end

  | LLJcc cond bt bf =>
    match fr.(fr_regs) ! cond with
    | Some vc =>
      match is_true vc with
      | true =>
        Some (set_frame st (set_pc fr bt))
      | false =>
        Some (set_frame st (set_pc fr bf))
      end
    | None => None
    end

  | LLJmp target =>
    Some (set_frame st (set_pc fr target))

  | LLRet val =>
    None

  (* TODO *)
  | _ => None
  end.

Definition step (p: prog) (st: state): option state :=
  match (st.(st_stack).(stk_frames)) ! (st.(st_stack).(stk_fr)) with
  | Some fr =>
    match p ! (fr.(fr_func)) with
    | Some fn =>
      match fn.(fn_insts) ! (fr.(fr_pc)) with
      | Some inst =>
        step_inst fr st inst
      | None =>
        None
      end
    | _ => None
    end
  | _ => None
  end.
