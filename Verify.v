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
    forall (use: node) (use_inst: inst) (r: reg),
      Some use_inst = PTrie.get f.(fn_insts) use ->
      Uses use_inst r ->
      forall (def: node) (def_inst: inst),
        Some def_inst = PTrie.get f.(fn_insts) def ->
        Defs def_inst r ->
        Dominates f def use.

  Definition defs_are_unique :=
    forall (def: node) (def_inst: inst) (r: reg),
      Some def_inst = PTrie.get f.(fn_insts) def ->
      Defs def_inst r ->
      forall (other: inst) (n: node),
        Some other = PTrie.get f.(fn_insts) n /\ Defs other r -> n = def /\ other = def_inst.

  Definition is_valid := uses_have_defs /\ defs_are_unique.

  Theorem defs_dominate_uses:
    is_valid ->
    forall (def: node) (def_inst: inst) (use: node) (use_inst: inst) (r: reg),
      Some def_inst = PTrie.get f.(fn_insts) def ->
      Defs def_inst r ->
      Some use_inst = PTrie.get f.(fn_insts) use ->
      Uses use_inst r ->
      Dominates f def use.
  Proof.
    intros Hvalid def def_inst use use_inst r.
    destruct Hvalid as [Huses_have_defs Hdefs_are_unique].
    intros Hdef_inst.
    intros Hdef.
    intros Huse_inst.
    intros Huse.
    unfold uses_have_defs in Huses_have_defs.
    generalize (Huses_have_defs use use_inst r Huse_inst Huse).
    intros Hdom.
    apply (Hdom def def_inst). apply Hdef_inst. apply Hdef.
  Qed.
End VALIDITY.
