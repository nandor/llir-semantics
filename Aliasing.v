(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.ZArith.ZArith.

Require Import LLIR.Maps.
Require Import LLIR.LLIR.

Inductive points_to_item :=
  | PTOffset (object: positive) (offset: positive)
  | PTRange (object: (option positive))
  .

Definition points_to_set :=
  PTrie.t (list points_to_item).


Axiom local_pta : func -> points_to_set.

