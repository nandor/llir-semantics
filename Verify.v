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

  Record is_valid : Prop :=
    { fn_uses_have_defs: uses_have_defs
    ; fn_defs_are_unique: defs_are_unique
    ; fn_well_ordered: well_ordered
    }.

  Theorem defs_dominate_uses:
    is_valid ->
    forall (def: node) (use: node) (r: reg),
      DefinedAt f def r ->
      UsedAt f use r ->
      StrictlyDominates f def use.
  Proof.
    intros Hvalid def use r.
    destruct Hvalid as [Huses_have_defs Hdefs_are_unique _].
    intros Hdef.
    intros Huse.
    unfold uses_have_defs in Huses_have_defs.
    generalize (Huses_have_defs use r Huse).
    intros Hdom.
    destruct Hdom as [dom [Hdef' Hdom]].
    generalize (Hdefs_are_unique def dom r Hdef Hdef').
    intros Heq. subst. auto.
  Qed.

  Theorem no_use_of_def:
    is_valid ->
    forall (n: node) (r: reg),
      DefinedAt f n r -> ~ (UsedAt f n r).
  Proof.
    intros Hvalid n r Hdef Huse.
    generalize (defs_dominate_uses Hvalid n n r Hdef Huse).
    intros Hdom.
    inversion Hdom.
    auto.
  Qed.

  Theorem no_def_of_use:
    is_valid ->
    forall (n: node) (r: reg),
      UsedAt f n r -> ~ (DefinedAt f n r).
  Proof.
    intros Hvalid n r Huse Hdef.
    generalize(defs_dominate_uses Hvalid n n r Hdef Huse).
    intros Hdom.
    inversion Hdom.
    auto.
  Qed.
End VALIDITY.
