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
  ; stk_frames: PTrie.t frame
  ; stk_init: objects
  }.

Inductive TopFrame: stack -> Prop :=
  | top_frame:
    forall
      (frames: PTrie.t frame) (init: objects) (top: positive),
      TopFrame (mkstack top [] frames init)
  .

Inductive ReturnFrame: stack -> positive -> list positive -> Prop :=
  | return_frame:
    forall 
      (frames: PTrie.t frame) (init: objects) (top: positive) (ret: positive)
      (frs: list positive),
      ReturnFrame (mkstack top (ret :: frs) frames init) ret frs
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

Inductive ValidFrame: prog -> frame -> Prop :=
  | valid_frame:
    forall
      (p: prog) (fr: frame)
      (fr_id: positive) (frames: PTrie.t frame)
      (data: objects) (args: PTrie.t value)
      (f: func) (i: inst)
      (FUNC: Some f = p ! (fr.(fr_func)))
      (REACH: Reachable f (fr.(fr_pc)))
      (INST: Some i = f.(fn_insts) ! (fr.(fr_pc)))
      (REGS:
        forall (r: reg),
          LiveAt f r (fr.(fr_pc)) ->
          exists (v: value),
            Some v = fr.(fr_regs) ! r)
      (VALS:
        forall (r: reg) (v: value),
          Some v = fr.(fr_regs) ! r ->
            exists (t: ty), Some t = (ty_env f) ! r /\ TypeOfValue v t),
      ValidFrame p fr
  .
