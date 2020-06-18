(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.Lists.List.
Require Import LLIR.LLIR.
Require Import LLIR.Dom.


Inductive LiveAt: func -> reg -> node -> Prop :=
  | live_at:
    forall
      (f: func) (r: reg) (n: node) (use: node) (p: list node)
      (PATH: Path f n p use)
      (NO_DEF: forall (def: node), def <> n -> In def p -> ~DefinedAt f def r)
      (USE: UsedAt f use r),
      LiveAt f r n.
