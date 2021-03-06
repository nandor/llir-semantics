(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Nat.

Require Import LLIR.Maps.
Require Import LLIR.Values.
Require Import LLIR.LLIR.
Require Import LLIR.Dom.
Require Import LLIR.Liveness.
Require Import LLIR.Typing.


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
  ; fr_args: list value
  ; fr_func: name
  ; fr_pc: node
  }.

Definition frame_map := PTrie.t frame.

Record stack := mkstack
  { stk_fr: positive
  ; stk_frs: list positive
  ; stk_next: positive
  ; stk_frames: PTrie.t frame
  ; stk_init: objects
  }.

Inductive TopFrame: stack -> Prop :=
  | top_frame:
    forall
      (next: positive) (frames: PTrie.t frame) (init: objects) (top: positive),
      TopFrame (mkstack top [] next frames init)
  .

Inductive ReturnFrame: stack -> positive -> list positive -> Prop :=
  | return_frame:
    forall 
      (next: positive) (frames: PTrie.t frame) (init: objects) 
      (top: positive) (ret: positive)
      (frs: list positive),
      ReturnFrame (mkstack top (ret :: frs) next frames init) ret frs
  .

Lemma top_or_return:
  forall (stk: stack),
    TopFrame stk 
    \/
    exists (next: positive) (rest: list positive), 
      ReturnFrame stk next rest.
Proof.
  intros stk; destruct stk as [stk_fr' stk_frs' stk_frames' stk_init'].
  destruct stk_frs'.
  - left; constructor.
  - right; exists p; exists stk_frs'; constructor.
Qed.

Inductive ValidFrame : prog -> frame -> Prop :=
  | valid_frame:
    forall
      (p: prog) (fr: frame) (f: func) (i: inst)
      (FUNC: Some f = p ! (fr.(fr_func)))
      (REACH: Reachable f (fr.(fr_pc)))
      (INST: Some i = f.(fn_insts) ! (fr.(fr_pc)))
      (REGS:
        forall (r: reg),
          LiveAt f r (fr.(fr_pc)) ->
          exists (v: value),
            Some v = fr.(fr_regs) ! r)
      (FN_VALS:
        forall (r: reg) (fn: name),
          Some (VSym (SFunc fn)) = fr.(fr_regs) ! r -> p ! fn <> None)
      (VALS:
        forall (r: reg) (v: value),
          Some v = fr.(fr_regs) ! r ->
            exists (t: ty), Some t = (ty_env f) ! r /\ TypeOfValue v t),
      ValidFrame p fr
  .

Inductive ValidTopFrame : prog -> positive -> frame_map -> Prop :=
  | valid_top_frame:
    forall
      (p: prog) (fr_id: positive) (frames: frame_map) (fr: frame)
      (FRAME: Some fr = frames ! fr_id)
      (VALID: ValidFrame p fr),
      ValidTopFrame p fr_id frames
  .

Inductive ValidMidFrame : prog -> positive -> frame_map -> Prop :=
  | valid_mid_frame:
    forall
      (p: prog) (fr_id: positive) (frames: frame_map) (fr: frame) 
      (i: inst) (f: func)
      (FRAME: Some fr = frames ! fr_id)
      (VALID: ValidFrame p fr)
      (FUNC: Some f = p ! (fr.(fr_func)))
      (EXEC: Some i = f.(fn_insts) ! (fr.(fr_pc)))
      (RETURN: VoidCallSite i \/ (exists (t: ty) (dst: reg), CallSite i t dst)),
      ValidMidFrame p fr_id frames
  .

Inductive ValidStack : prog -> stack -> Prop :=
  | valid_stack:
    forall
      (p: prog)
      (fr_id: positive) (frs: list positive) 
      (next: positive) (frames: PTrie.t frame) (init: objects)
      (FR: ValidTopFrame p fr_id frames)
      (NEXT: forall (fr: positive), In fr frs -> ValidMidFrame p fr frames),
      ValidStack p (mkstack fr_id frs next frames init)
  .

Axiom set_vreg: frame -> reg -> value -> frame.

Definition set_pc (fr: frame) (pc: node): frame :=
  {| fr_data := fr_data fr
   ; fr_regs := fr_regs fr
   ; fr_args := fr_args fr
   ; fr_func := fr_func fr
   ; fr_pc := pc
   |}.

Axiom set_vreg_pc: frame -> reg -> value -> node -> frame.

Axiom step_binop: binop -> ty -> value -> value -> option value.

Axiom step_unop: unop -> ty -> value -> option value.

Axiom jump_to_phi: frame -> node -> frame.

Axiom load_from_object: objects -> positive -> positive -> ty -> option value.

Axiom create_frame: func -> objects.
