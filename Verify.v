(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Require Import LLIR.State.
Require Import LLIR.LLIR.
Require Import LLIR.Maps.
Require Import LLIR.Dom.

Import ListNotations.

Section VALIDITY.
  Variable f: func.

  Definition uses_have_defs :=
    forall (use: node) (r: reg),
      UsedAt f use r ->
      exists (def: node),
        DefinedAt f def r /\
        StrictlyDominates f def use.

  Definition defs_are_unique :=
    forall (def: node) (def': node) (r: reg),
      DefinedAt f def r ->
      DefinedAt f def' r ->
      def' = def.

  Definition well_ordered :=
    forall (def: node) (use: node),
      StrictlyDominates f def use -> Pos.lt def use.

  Definition is_valid := uses_have_defs /\ defs_are_unique /\ well_ordered.

  Theorem defs_dominate_uses:
    is_valid ->
    forall (def: node) (use: node) (r: reg),
      DefinedAt f def r ->
      UsedAt f use r ->
      StrictlyDominates f def use.
  Proof.
    intros Hvalid def use r.
    destruct Hvalid as [Huses_have_defs [Hdefs_are_unique _]].
    intros Hdef.
    intros Huse.
    unfold uses_have_defs in Huses_have_defs.
    generalize (Huses_have_defs use r Huse).
    intros Hdom.
    destruct Hdom as [dom [Hdef' Hdom]].
    generalize (Hdefs_are_unique def dom r Hdef Hdef').
    intros Heq. subst. auto.
  Qed.
End VALIDITY.
