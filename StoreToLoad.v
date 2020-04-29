(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Require Import LLIR.Aliasing.
Require Import LLIR.LLIR.
Require Import LLIR.Maps.
Require Import LLIR.State.
Require Import LLIR.Values.
Require Import LLIR.Verify.
Require Import LLIR.ReachingStores.
Require Import LLIR.Dom.

Import ListNotations.


Section PROPAGATION.
  Variable f: func.
  Variable rs: reaching_stores.
  Variable aa: points_to_set.

  Definition get_propagated_loads: list (reg * reg) :=
    PTrie.values (reg * reg) (PTrie.map_opt inst (reg * reg) 
      (fun k inst =>
        match inst with
        | LLLd addr dst next =>
          match get_load_addr aa addr with
          | Some obj => 
            match get_store_to rs k obj with
            | Some src => Some (dst, src)
            | None => None
            end
          | None => None
          end
        | _ => None
        end
      ) f.(fn_insts)).

  Lemma propagate_src_dst:
    forall (dst: reg) (src: reg),
      In (dst, src) get_propagated_loads ->
        exists (k: node) (addr: reg) (object: positive) (offset: positive),
          loads_from f aa k dst addr object offset /\
          store_to_at rs k src object offset.
  Proof.
    intros src dst.
    intros Helem.
    unfold get_propagated_loads in Helem.
    apply PTrie.values_correct in Helem.
    destruct Helem as [k Helem].
    exists k.
    apply PTrie.map_opt_correct in Helem.
    destruct Helem as [inst].
    destruct H as [Hinst Hfunc].
    destruct inst; inversion Hfunc; clear H0.
    destruct (get_load_addr aa addr) eqn:Hload; inversion Hfunc; clear H0.
    destruct (get_store_to rs k o) eqn:Hstore; inversion Hfunc; clear H0.
    destruct o as [object offset].
    exists addr.
    exists object.
    exists offset.
    inversion Hfunc.
    rewrite <- H0 in Hfunc. rewrite <- H0. rewrite <- H0 in Hinst. clear H0. clear dst0.
    rewrite <- H2. rewrite <- H2 in Hstore. clear H1. clear H2. clear Hfunc. clear r.
    split.
    - apply load with (next := next). symmetry. apply Hload. apply Hinst.
    - apply store. symmetry. apply Hstore.
  Qed.

  Lemma src_dominates_dst:
    is_valid f ->
      forall (src: reg) (dst: reg),
        In (dst, src) get_propagated_loads -> 
          forall (def: node) (use: node),
            DefinedAt f def src ->
            UsedAt f use dst ->
            Dominates f def use.
  Proof.
    intros Hvalid.
    intros src dst.
    intros Helem.
    apply propagate_src_dst in Helem.
    destruct Helem as [k Helem].
    destruct Helem as [ld_addr Helem].
    destruct Helem as [object Helem].
    destruct Helem as [offset Helem].
    destruct Helem as [Hload Hstore].
    assert (Hstore': store_to_at rs k src object offset). { apply Hstore. }
    apply (reaching_store_origin f aa) in Hstore'.
    destruct Hstore' as [store Hstore'].
    destruct Hstore' as [val Hstore'].
    destruct Hstore' as [next Hstore'].
    destruct Hstore' as [Hstore' Hdom].
    inversion Hstore'.
    assert (Hvalid': is_valid f). { apply Hvalid. }
    destruct Hvalid' as [Hdef_dom_uses Hdefs_unique].
    intros def use.
    intros Hdef_src.
    intros Huse_dst.
    apply (dom_trans f def store use).
    {
      generalize (Hdef_dom_uses store).
      intros H'.
      assert (Hst_uses_src: Uses (LLSt addr src next) src).
      { unfold Uses. right. reflexivity. }
      destruct ((fn_insts f) ! def) eqn:E.
      {
        symmetry in E.
        generalize (H' (LLSt addr src next0) src H Hst_uses_src def i E).
        intros H''.
        apply H''.
        unfold DefinedAt in Hdef_src.
        rewrite <- E in Hdef_src.
        apply Hdef_src.
      }
      {
        unfold DefinedAt in Hdef_src.
        rewrite E in Hdef_src.
        inversion Hdef_src.
      }
    }
    {
      apply (dom_trans f store k use).
      {
        inversion Hstore.
        inversion Hstore'.
        unfold get_store_to in H5.
        destruct (rs ! k) as [use'|] eqn:Euse'; inversion H5.
        destruct (use' ! object) as [object'|] eqn:Eobject'; inversion H5.
        destruct (object' ! offset) as [offset'|] eqn:Eoffset'; inversion H5.
        inversion H5. rewrite <- H5 in Eoffset'.
        apply (reaching_stores_dom f aa rs k use' object object' offset src); try symmetry.
        - apply Euse'.
        - apply Eobject'.
        - apply Eoffset'.
        - apply (store_at f aa store object offset src addr0 next1).
          + apply H10.
          + apply H11.
      }
      {
        inversion Hload.
        destruct (f.(fn_insts) ! use) eqn:Euse.
        + apply defs_dominate_uses with 
            (def_inst := LLLd ld_addr dst next1)
            (use_inst := i)
            (r := dst).
          - apply Hvalid.
          - apply H6.
          - unfold Defs. reflexivity.
          - symmetry. apply Euse.
          - unfold UsedAt in Huse_dst.
            rewrite Euse in Huse_dst.
            apply Huse_dst.
        + unfold UsedAt in Huse_dst.
          rewrite Euse in Huse_dst.
          inversion Huse_dst.
      }
    }
  Qed.
End PROPAGATION.

Definition propagate_store_to_load (f: func): func :=
  let aa := local_pta f in
  let rs := analyse_reaching_stores f aa in
  let loads := get_propagated_loads f rs aa in
  mkfunc f.(fn_args) f.(fn_stack) f.(fn_insts) f.(fn_phis) f.(fn_entry).

