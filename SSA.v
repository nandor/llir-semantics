(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Require Import LLIR.LLIR.
Require Import LLIR.Maps.
Require Import LLIR.Dom.
Require Import LLIR.Block.

Import ListNotations.

Section FUNC_VALIDITY.
  Variable f: func.

  Definition uses_have_defs :=
    forall (use: node) (r: reg),
      UsedAt f use r ->
      exists (def: node),
        DefinedAt f def r /\
        Dominates f def use.

  Definition defs_are_unique :=
    forall (def: node) (def': node) (r: reg),
      DefinedAt f def r ->
      DefinedAt f def' r ->
      def' = def.

  Definition inst_does_not_use_defs :=
    forall (def: node) (r: reg),
      InstDefinedAt f def r -> ~InstUsedAt f def r.

  Definition blocks_are_valid :=
    forall (e: node),
      (exists (h: node), BasicBlock f h e) \/ (f.(fn_insts) ! e = None).

  Definition phi_or_inst :=
    forall (def: node) (r: reg),
      (InstDefinedAt f def r -> ~PhiDefinedAt f def r)
      /\
      (PhiDefinedAt f def r -> ~InstDefinedAt f def r).

  Record valid_func : Prop :=
    { fn_uses_have_defs: uses_have_defs
    ; fn_defs_are_unique: defs_are_unique
    ; fn_blocks_are_valid: blocks_are_valid
    ; fn_inst_does_not_use_defs: inst_does_not_use_defs
    ; fn_phi_or_inst: phi_or_inst
    }.

  Theorem defs_dominate_uses:
    valid_func ->
    forall (def: node) (use: node) (r: reg),
      DefinedAt f def r ->
      UsedAt f use r ->
      Dominates f def use.
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

  Theorem inst_does_not_defs_uses:
    valid_func ->
    forall (def: node) (r: reg),
      InstUsedAt f def r -> ~InstDefinedAt f def r.
  Proof.
    intros Hvalid def r Hused_at Hdefined_at.
    destruct Hvalid as [_ _ _ Hno_use].
    generalize (Hno_use def r Hdefined_at); intros contra.
    contradiction.
  Qed.

  Theorem inst_def_single_reg:
    forall (def: node) (r: reg) (r': reg),
      InstDefinedAt f def r ->
      InstDefinedAt f def r' ->
      r = r'.
  Proof.
    intros def r r' Hdef Hdef'.
    inversion Hdef; inversion Hdef'.
    rewrite <- INST0 in INST; inversion INST; subst i0.
    inversion DEFS; inversion DEFS0; subst; inversion H5; reflexivity.
  Qed.
End FUNC_VALIDITY.

Section PROG_VALIDITY.
  Variable p: prog.

  Definition valid_prog (p: prog) :=
    forall (n: name) (f: func),
      Some f = p ! n -> valid_func f.

End PROG_VALIDITY.
