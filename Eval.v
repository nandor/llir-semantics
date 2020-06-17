(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Nat.

Require Import LLIR.LLIR.
Require Import LLIR.Maps.
Require Import LLIR.Typing.
Require Import LLIR.Liveness.
Require Import LLIR.Dom.

Import ListNotations.



Record object := mkdata
  { dt_size: positive
  ; dt_align: positive
  ; dt_data: PTrie.t quad
  }.

Definition objects := PTrie.t object.

Record frame := mkframe
  { fr_data: objects
  ; fr_regs: PTrie.t value
  ; fr_args: PTrie.t value
  ; fr_func: name
  ; fr_pc: node
  }.

Record stack := mkstack
  { stk_fr: positive
  ; stk_frs: list positive
  ; stk_frames: PTrie.t frame
  ; stk_init: objects
  }.

Record heap := mkheap
  {
  }.

Record state := mkstate
  { st_stack: stack
  ; st_heap: heap
  }.


Definition trace := list (positive * list value).

Section VALIDITY.
  Variable p: prog.

  Inductive ValidFrame: positive -> PTrie.t frame -> Prop :=
    | valid_frame:
      forall
        (fr_id: positive) (frames: PTrie.t frame)
        (data: objects) (args: PTrie.t value)
        (f: func) (i: inst) (fr: frame)
        (FRAME: Some fr = frames ! fr_id)
        (FUNC: Some f = p ! (fr.(fr_func)))
        (REACH: Reachable f (fr.(fr_pc)))
        (INST: Some i = f.(fn_insts) ! (fr.(fr_pc)))
        (REGS: forall (r: reg), LiveAt f r (fr.(fr_pc)) -> exists (v: value), Some v = fr.(fr_regs) ! r),
        ValidFrame fr_id frames
    .

  Inductive ValidState: state -> Prop :=
    | valid_state:
      forall
        (fr_id: positive) (frs: list positive) (frames: PTrie.t frame) (init: objects)
        (h: heap)
        (FR: ValidFrame fr_id frames)
        (FRS: forall (f: positive), In f frs -> ValidFrame f frames),
        ValidState (mkstate (mkstack fr_id frs frames init) h)
    .
End VALIDITY.

Definition set_frame (st: state) (fr: frame): state :=
  let stk := st.(st_stack) in
  {| st_stack :=
    {| stk_fr := stk.(stk_fr)
     ; stk_frs := stk.(stk_frs)
     ; stk_frames := PTrie.set stk.(stk_frames) stk.(stk_fr) fr
     ; stk_init := stk.(stk_init)
     |}
   ; st_heap := st.(st_heap)
   |}.

Axiom get_vreg: frame -> reg -> option value.

Axiom set_vreg: frame -> reg -> value -> frame.

Axiom set_pc: frame -> node -> frame.

Axiom set_vreg_pc: frame -> reg -> value -> node -> frame.

Axiom step_binop: binop -> ty -> value -> value -> option value.

Axiom step_unop: unop -> ty -> value -> option value.

Axiom argext: ty -> value -> option value.

Definition step_inst (fr: frame) (st: state) (i: inst): option state :=
  match i with
  | LLArg (ty, dst) next idx =>
    match (fr.(fr_args) ! (Pos.of_nat idx)) with
    | None => None
    | Some v =>
      match argext ty v with
      | None => None
      | Some v' =>
        let fr' := set_vreg_pc fr dst v' next in
        Some (set_frame st fr')
      end
    end

  | LLInt32 dst next val =>
    let fr' := set_vreg_pc fr dst (VInt (INT.Int32 val)) next in
    Some (set_frame st fr')

  | LLUnop (ty, dst) next op arg =>
    match get_vreg fr arg with
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
    match get_vreg fr lhs with
    | Some vl =>
      match get_vreg fr rhs with
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
    match get_vreg fr cond with
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
