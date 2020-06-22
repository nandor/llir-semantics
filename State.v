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

Inductive ValidState : prog -> state -> Prop :=
  | valid_state:
    forall
      (p: prog)
      (fr_id: positive) (frs: list positive) 
      (next: positive) (frames: PTrie.t frame) (init: objects)
      (h: heap)
      (FR: ValidTopFrame p fr_id frames)
      (NEXT: forall (fr: positive), In fr frs -> ValidMidFrame p fr frames),
      ValidState p (mkstate (mkstack fr_id frs next frames init) h)
  .

