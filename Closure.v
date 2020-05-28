(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.funind.FunInd.
Require Import Coq.funind.Recdef.

Require Import LLIR.Maps.
Require Import LLIR.State.

Import ListNotations.



Definition relation := PTrie.t reg.


Section CLOSURE.

  Variable loads: relation.

  Inductive chain: reg -> reg -> Prop :=
    | closure_chain_elem:
      forall (dst: reg) (src: reg)
        (HE: Some src = loads ! dst),
        chain dst src
    | closure_chain_step:
      forall (dst: reg) (mid: reg) (src: reg)
        (HL: chain mid src)
        (HR: chain dst mid),
        chain dst src
    .

  Definition is_relation (l: relation): Prop :=
    forall (dst: reg) (src: reg),
      Some src = l ! dst -> chain dst src.

  Lemma is_valid_empty:
    is_relation PTrie.empty.
  Proof.
    intros dst src Hin. inversion Hin.
  Qed.

  Hypothesis H_loads_valid: is_relation loads.

  Definition find_match (l: relation) (src: reg): reg :=
    match l ! src with
    | None => src
    | Some dst => dst
    end.

  Lemma find_match_chain:
    forall (l: relation),
      is_relation l ->
      forall (s: reg) (s': reg),
        s' = find_match l s -> s = s' \/ chain s s'.
  Proof.
    intros l Hvalid src src' Hfind.
    unfold find_match in Hfind.
    destruct (l ! src) eqn:E; try symmetry in E.
    - right. apply Hvalid. subst src'. auto.
    - left. auto.
  Qed.

  Definition update_map (l: relation) (d': reg) (s': reg): relation :=
    PTrie.map (fun d s => if Pos.eqb s d' then s' else s) l.

  Example update_map_example :=
    << (2%positive, 3%positive)
    ;  (1%positive, 3%positive)
    ;  (5%positive, 3%positive)
    >>.

  Example update_map_example' :=
    update_map update_map_example 3%positive 5%positive.

  Fact update_map_2: update_map_example' ! 2%positive = Some 5%positive.
  Proof. auto. Qed.
  Fact update_map_1: update_map_example' ! 1%positive = Some 5%positive.
  Proof. auto. Qed.
  Fact update_map_5: update_map_example' ! 5%positive = Some 5%positive.
  Proof. auto. Qed.

  Lemma update_map_chain:
    forall (l: relation),
      is_relation l ->
      forall (d: reg) (s: reg),
        chain d s ->
        is_relation (update_map l d s).
  Proof.
    intros l Hvalid d s Hin d' s' Hdef.
    unfold update_map in Hdef.
    apply PTrie.map_in in Hdef.
    destruct Hdef as [a [Heq Hif]].
    destruct (Pos.eqb a d) eqn:E.
    - apply Pos.eqb_eq in E. subst a s'.
      apply (closure_chain_step d' d s).
      apply Hin.
      apply Hvalid. apply Heq.
    - subst. apply Hvalid. apply Heq.
  Qed.

  Definition closure_helper (acc: relation) (dst: reg) (src: reg): relation :=
    let src' := find_match acc src in
    let acc_u := update_map acc dst src' in
    PTrie.set acc_u dst src'.

  Definition closure_helper_valid:
    forall (dst: PTrie.key) (src: reg) (acc: relation),
      is_relation acc ->
      Some src = loads ! dst ->
      is_relation (closure_helper acc dst src).
  Proof.
    intros dst src acc Hvalid_acc Helem dst' src' Helem'.
    unfold closure_helper in Helem'.
    remember (find_match acc src) as s'.
    remember (update_map acc dst s') as acc'.
    rewrite PTrie.set_get in Helem'.
    destruct (Pos.eqb dst dst') eqn:E.
    {
      apply Pos.eqb_eq in E. subst dst.
      inversion Helem'. subst s'.
      generalize (find_match_chain acc Hvalid_acc src src' H0).
      intros Hfm.
      rewrite <- H0.
      destruct Hfm.
      {
        subst src.
        apply H_loads_valid.
        apply Helem.
      }
      {
        apply closure_chain_step with (mid := src).
        apply H.
        apply H_loads_valid. apply Helem.
      }
    }
    {
      assert (Hchain: chain dst s').
      {
        generalize (find_match_chain acc Hvalid_acc src s' Heqs').
        intros Hfm.
        destruct Hfm.
        {
          subst src.
          apply H_loads_valid. apply Helem.
        }
        {
          apply closure_chain_step with (mid := src).
          apply H.
          apply H_loads_valid. apply Helem.
        }
      }
      assert (Hvalid_acc': is_relation acc').
      {
        generalize (update_map_chain acc Hvalid_acc dst s' Hchain).
        intros Hvalid.
        subst acc'.
        apply Hvalid.
      }
      apply Hvalid_acc'.
      apply Helem'.
    }
  Qed.

  Example closure_helper_example :=
    << (2%positive, 5%positive)
    ;  (3%positive, 5%positive)
    >>.

  Definition closure_helper_example' :=
    closure_helper closure_helper_example 5%positive 6%positive.

  Fact closure_helper_2: closure_helper_example' ! 2%positive = Some 6%positive.
  Proof. auto. Qed.
  Fact closure_helper_3: closure_helper_example' ! 3%positive = Some 6%positive.
  Proof. auto. Qed.
  Fact closure_helper_5: closure_helper_example' ! 5%positive = Some 6%positive.
  Proof. auto. Qed.

  Definition closure (l: relation) :=
    PTrie.fold closure_helper l PTrie.empty.

  Definition closure_valid:
    is_relation (closure loads).
  Proof.
    unfold closure.
    apply PTrie.fold_prop with
      (pE := fun k v => Some v = loads ! k).
    + intros k a acc Hacc Hin.
      apply closure_helper_valid. apply Hacc. apply Hin.
    + apply is_valid_empty.
    + intros k a Hin. apply Hin.
  Qed.

  Example chain_example :=
    << ( 4%positive, 3%positive)
    ;  ( 3%positive, 2%positive)
    ;  ( 2%positive, 1%positive)
    >>.

  Definition chain_example' := closure chain_example.

  Fact chain_4: chain_example' ! 4%positive = Some 1%positive.
  Proof. auto. Qed.
  Fact chain_3: chain_example' ! 3%positive = Some 1%positive.
  Proof. auto. Qed.
  Fact chain_2: chain_example' ! 2%positive = Some 1%positive.
  Proof. auto. Qed.

End CLOSURE.



