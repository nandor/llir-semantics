(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
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

Definition propagate_loads (f: func) (rs: reaching_stores) (aa: points_to_set): list (reg * reg) :=
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

Fixpoint closure_chain (src: reg) (pairs: list (reg * reg)): (option reg * list (reg * reg)) :=
  match pairs with
  | nil => (None, nil)
  | (dst', src') :: pairs' =>
    match dst' =? src with
    | true => (Some src', pairs')
    | false => 
      match closure_chain src pairs' with
      | (None, pairs'') => (None, nil)
      | (v, pairs'') => (v, (dst', src') :: pairs'')
      end
    end
  end.

Theorem closure_chain_length:
  forall (pairs: list (reg * reg)) (src: reg) (p: reg * reg),
    Nat.lt (length (snd (closure_chain src (p::pairs)))) (S (length pairs)).
Proof.
  induction pairs; try intros.
  { 
    unfold closure_chain.
    destruct p.
    destruct (r =? src); simpl; apply Nat.lt_0_1.
  }
  {
    simpl.
    destruct p.
    destruct (r =? src); try apply Nat.lt_succ_diag_r.
    destruct a.
    destruct (r1 =? src) eqn:E; try apply Nat.lt_succ_diag_r.
    destruct (closure_chain src pairs) eqn:Hc.
    destruct o.
    + simpl.
      rewrite <- Nat.succ_lt_mono.
      generalize (IHpairs src (r1, r1)).
      unfold closure_chain.
      rewrite E.
      fold closure_chain.
      intro H.
      rewrite Hc in H.
      simpl in H.
      apply H.
    + simpl.
      apply Nat.lt_0_succ.
  }
Qed.

Program Fixpoint closure_step (src: reg) (pairs: list (reg * reg)) { measure (length pairs) } :=
  match closure_chain src pairs with
  | (None, _) => src
  | (Some v, pairs') => closure_step v pairs'
  end.
Obligation 1.
  rename Heq_anonymous into Heq.
  unfold closure_chain in Heq.
  destruct pairs.
  - inversion Heq.
  - destruct p as [x y].
    destruct (x =? src) eqn:Ex.
    {
      inversion Heq.
      simpl.
      apply Nat.lt_succ_r.
      reflexivity.
    }
    {
      fold closure_chain in Heq.
      simpl.
      destruct (closure_chain src pairs) eqn:E.
      destruct o.
      - inversion Heq.
        assert ((x, y) :: l = snd (closure_chain src ((x, y) :: pairs))).
        {
          simpl.
          rewrite Ex.
          rewrite E.
          simpl.
          reflexivity.
        }
        rewrite H.
        apply closure_chain_length.
      - inversion Heq.
    }
Qed.

Definition closure (pairs: list (reg * reg)): list (reg * reg) :=
  List.map 
    (fun pair =>
      match pair with
      | (dst, src) => (dst, closure_step src pairs)
      end)
    pairs.

Definition propagate_store_to_load (f: func): func :=
  let aa := local_pta f in
  let rs := analyse_reaching_stores f aa in
  let loads := closure (propagate_loads f rs aa) in
  mkfunc f.(fn_args) f.(fn_stack) f.(fn_insts) f.(fn_phis) f.(fn_entry).

Section PROPERTIES.
  Variable f: func.
  Variable rs: reaching_stores.
  Variable aa: points_to_set.

  Hypothesis H_f_valid: is_valid f.

  Lemma propagate_src_dst:
    forall (loads: list (reg * reg)) (dst: reg) (src: reg),
      loads = propagate_loads f rs aa ->
      In (dst, src) loads ->
        exists (k: node) (addr: reg) (object: positive) (offset: positive),
          loads_from f aa k dst addr object offset /\
          store_to_at rs k src object offset.
  Proof.
    intros loads src dst.
    intro Hprop.
    intro Helem.
    rewrite Hprop in Helem.
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

  Definition reg_dom (src: reg) (dst: reg): Prop :=
    forall (def: node) (use: node),
      DefinedAt f def src ->
      UsedAt f use dst ->
      Dominates f def use.

  Lemma src_dominates_dst:
    forall (loads: list (reg * reg)) (src: reg) (dst: reg),
      loads = propagate_loads f rs aa ->
      In (dst, src) loads -> reg_dom src dst.
  Proof.
    intros loads src dst.
    intro Hprop.
    intro Helem.
    apply (propagate_src_dst loads dst src Hprop) in Helem.
    destruct Helem as [k Helem].
    destruct Helem as [ld_addr Helem].
    destruct Helem as [object Helem].
    destruct Helem as [offset Helem].
    destruct Helem as [Hload Hstore].
    assert (Hstore': store_to_at rs k src object offset).
    { apply Hstore. }
    apply (reaching_store_origin f aa) in Hstore'.
    destruct Hstore' as [store Hstore'].
    destruct Hstore' as [val Hstore'].
    destruct Hstore' as [next Hstore'].
    destruct Hstore' as [Hstore' Hdom].
    inversion Hstore'.
    assert (H_f_valid': is_valid f). { apply H_f_valid. }
    destruct H_f_valid' as [Hdef_dom_uses Hdefs_unique].
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
          - apply H_f_valid.
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

  Lemma propagate_load_unique:
    forall (loads: list (reg * reg)) (dst: reg) (src: reg),
      loads = propagate_loads f rs aa ->
      In (dst, src) loads ->
        forall (src': reg), In (dst, src') loads -> src = src'.
  Proof.
    intros loads  dst src.
    intro Hloads.
    intro Hin.
    intro src'.
    intro Hin'.
    generalize (propagate_src_dst loads dst src Hloads Hin).
    intros Hexists.
    generalize (propagate_src_dst loads dst src' Hloads Hin').
    intros Hexists'.
    destruct Hexists as [k [addr [object [offset [Hload Hstore]]]]].
    destruct Hexists' as [k' [addr' [object' [offset' [Hload' Hstore']]]]].
    inversion Hload.
    assert (Hdef: Defs (LLLd addr dst next) dst). reflexivity.
    destruct H_f_valid as [_ Hunique].
    inversion Hload'.
    generalize (Hunique k' (LLLd addr' dst next0) dst H7 Hdef (LLLd addr dst next) k).
    intro Huniq.
    assert (Heq: k = k' /\ LLLd addr dst next = LLLd addr' dst next0).
    {
      apply Huniq.
      split.
      - apply H0.
      - simpl. reflexivity.
    }
    destruct Heq as [Hk_eq Hld_eq].
    inversion Hld_eq as [Haddr].
    rewrite <- Haddr in H6.
    rewrite <- H6 in H.
    inversion H.
    rewrite <- H15 in Hstore'.
    rewrite <- H16 in Hstore'.
    inversion Hstore.
    inversion Hstore'.
    rewrite <- Hk_eq in H21.
    rewrite <- H14 in H21.
    inversion H21.
    reflexivity.
  Qed.
End PROPERTIES.


