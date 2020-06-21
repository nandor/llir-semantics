(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Require Import LLIR.LLIR.
Require Import LLIR.Maps.
Require Import LLIR.Typing.
Require Import LLIR.Frame.

Import ListNotations.

Record heap := mkheap
  { hp_segments: PTrie.t objects
  }.

Record state := mkstate
  { st_stack: stack
  ; st_heap: heap
  }.


Definition trace := list (positive * list value).

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

Inductive ValidState : prog -> state -> Prop :=
  | valid_state:
    forall
      (p: prog)
      (fr_id: positive) (frs: list positive) (frames: PTrie.t frame) (init: objects)
      (h: heap)
      (FR: ValidTopFrame p fr_id frames)
      (NEXT: forall (fr: positive), In fr frs -> ValidMidFrame p fr frames),
      ValidState p (mkstate (mkstack fr_id frs frames init) h)
  .

