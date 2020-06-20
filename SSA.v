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

  Inductive JoinPoint: node -> Prop :=
    | join_point:
      forall 
        (n: node) (p0: node) (p1: node)
        (PRED0: SuccOf f p0 n)
        (PRED1: SuccOf f p1 n)
        (NE: p0 <> p1),
        JoinPoint n.

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

  Definition phis_are_complete :=
    forall
      (n: node) (p: node) (block: list phi) 
      (t: ty) (r: reg) (ins: list (node * reg)),
      SuccOf f p n ->
      Some block = f.(fn_phis) ! n ->
      In (LLPhi (t, r) ins) block ->
      exists (r': reg), In (p, r') ins.

  Definition succs_are_valid :=
    forall
      (n: node) (m: node) (i: inst),
      Some i = f.(fn_insts) ! n ->
      Succeeds i m ->
      SuccOf f n m.

  Record valid_func : Prop :=
    { fn_uses_have_defs: uses_have_defs
    ; fn_defs_are_unique: defs_are_unique
    ; fn_blocks_are_valid: blocks_are_valid
    ; fn_inst_does_not_use_defs: inst_does_not_use_defs
    ; fn_phi_or_inst: phi_or_inst
    ; fn_phis_are_complete: phis_are_complete
    ; fn_succs_are_valid: succs_are_valid
    }.

  Theorem join_point_header:
    forall (n: node),
      valid_func ->
      JoinPoint n ->
      BasicBlockHeader f n.
  Proof.
    intros n Hvalid Hjoin; inversion Hjoin.
    generalize (fn_blocks_are_valid Hvalid n); intros Hblock.
    destruct Hblock as [[h Hbb]|Hno_inst].
    {
      constructor.
      {
        apply bb_reaches with h; auto.
      }
      {
        intros term Hsucc.
        inversion Hbb; subst.
        {
          inversion HEADER.
          apply TERM; auto.
        }
        {
          apply UNIQ in PRED0; apply UNIQ in PRED1; subst; contradiction.
        }
      }
      {
        inversion PRED0; auto.
      }
    }
    {
      inversion PRED0.
      rewrite Hno_inst in HM.
      contradiction.
    }
  Qed.

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
