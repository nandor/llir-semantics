(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.ZArith.ZArith.

Require Import LLIR.Values.
Require Import LLIR.Maps.

Notation node := positive.

Notation reg := positive.



Record atom := mkdata
  { dt_size: positive
  ; dt_data: PTrie.t qword
  }.

Record frame := mkframe
  { fr_data: PTrie.t atom
  ; fr_regs: PTrie.t qword
  ; fr_args: PTrie.t qword
  ; fr_func: positive
  ; fr_pc: node
  }.

Record state :=
  { st_stack: list frame
  }.


Definition trace := list (positive * list qword).
