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
Require Import LLIR.Transform.

Import ListNotations.



Definition find_load_reg (insts: inst_map) (rs: reaching_stores) (aa: points_to_set): PTrie.t reg :=
  PTrie.extract reg (PTrie.map_opt inst (reg * reg) 
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
    ) insts).

Definition rewrite_reg (loads: PTrie.t reg) (r: reg): reg :=
  match PTrie.get loads r with
  | None => r
  | Some reg' => reg'
  end.


Definition rewrite_inst (i: inst) (loads: PTrie.t reg): inst :=
  rewrite_uses i (rewrite_reg loads).


Definition rewrite_insts (insts: inst_map) (loads: PTrie.t reg): inst_map :=
  PTrie.map inst inst (fun k inst => rewrite_inst inst loads) insts.


Definition propagate_store_to_load (f: func): func :=
  let aa := local_pta f in
  let rs := analyse_reaching_stores f aa in
  let loads := find_load_reg f.(fn_insts) rs aa in
  let fn_insts := rewrite_insts f.(fn_insts) loads in
  mkfunc f.(fn_args) f.(fn_stack) fn_insts f.(fn_phis) f.(fn_entry).


Section LOAD_PROPERTIES.
  Variable f: func.
  Variable rs: reaching_stores.
  Variable aa: points_to_set.

  Hypothesis H_f_valid: is_valid f.

  Lemma propagate_src_dst:
    forall (loads: PTrie.t reg) (dst: reg) (src: reg),
      loads = find_load_reg f.(fn_insts) rs aa ->
      Some src = PTrie.get loads dst ->
        exists (k: node) (addr: reg) (object: positive) (offset: positive),
          loads_from f aa k dst addr object offset /\
          store_reaches rs k src object offset.
  Proof.
    intros loads src dst.
    intro Hprop.
    intro Helem.
    rewrite Hprop in Helem.
    apply PTrie.extract_correct in Helem.
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
    rewrite <- H0 in Hfunc. 
    rewrite <- H0. 
    rewrite <- H0 in Hinst. 
    rewrite <- H2. 
    rewrite <- H2 in Hstore.
    split.
    - apply load with (next := next). symmetry. apply Hload. apply Hinst.
    - apply store. symmetry. apply Hstore.
  Qed.

  Definition reg_dom (src: reg) (dst: reg): Prop :=
    forall (def: node) (use: node),
      DefinedAt f def src ->
      UsedAt f use dst ->
      StrictlyDominates f def use.

  Lemma src_dominates_dst:
    forall (loads: PTrie.t reg) (src: reg) (dst: reg),
      loads = find_load_reg f.(fn_insts) rs aa ->
      Some src = PTrie.get loads dst -> 
      reg_dom src dst.
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
    assert (Hstore': store_reaches rs k src object offset).
    { apply Hstore. }
    apply (reaching_store_origin f aa) in Hstore'.
    destruct Hstore' as [store Hstore'].
    destruct Hstore' as [val Hstore'].
    destruct Hstore' as [next Hstore'].
    destruct Hstore' as [Hstore' Hdom].
    inversion Hstore'.
    assert (H_f_valid': is_valid f). { apply H_f_valid. }
    destruct H_f_valid' as [Hdef_dom_uses Hdefs_unique _].
    unfold defs_are_unique in Hdefs_unique.
    intros def use.
    intros Hdef_src.
    intros Huse_dst.
    apply (sdom_trans f def store use).
    {
      generalize (Hdef_dom_uses store).
      intros H'.
      assert (Hsrc_used_at_store: UsedAt f store src).
      { unfold UsedAt. rewrite <- H. unfold Uses. auto. }
      destruct ((fn_insts f) ! def) eqn:E.
      {
        symmetry in E.
        generalize (H' src Hsrc_used_at_store).
        intros H''.
        destruct H'' as [def' [Hdef' Hdom']].
        assert (def = def').
        { apply Hdefs_unique with (r := src). apply Hdef'. apply Hdef_src. }
        subst.
        apply Hdom'.
      }
      {
        unfold DefinedAt in Hdef_src.
        rewrite E in Hdef_src.
        inversion Hdef_src.
      }
    }
    {
      apply (sdom_trans f store k use).
      {
        inversion Hstore.
        inversion Hstore'.
        unfold get_store_to in H5.
        destruct (rs ! k) as [use'|] eqn:Euse'; inversion H5.
        destruct (use' ! object) as [object'|] eqn:Eobject'; inversion H5.
        destruct (object' ! offset) as [offset'|] eqn:Eoffset'; inversion H5.
        inversion H5. rewrite <- H5 in Eoffset'.
        apply (reaching_stores_dom f aa rs k use' object object' offset src); 
          try symmetry.
        - apply Euse'.
        - apply Eobject'.
        - apply Eoffset'.
        - apply (store_at f aa store object offset src addr0 next1).
          + apply H10.
          + apply H11.
      }
      {
        inversion Hload.
        unfold uses_have_defs in Hdef_dom_uses.
        subst.
        assert (HdefK: DefinedAt f k dst). 
        { unfold DefinedAt. rewrite <- H6. unfold Defs. reflexivity. }
        destruct (f.(fn_insts) ! use) eqn:Euse.
        + generalize (Hdef_dom_uses use dst Huse_dst).
          intros H''.
          destruct H'' as [def' [Hdef' Hdom']].
          assert (def' = k).
          { apply Hdefs_unique with (r := dst).  apply HdefK. apply Hdef'. }
          subst.
          apply Hdom'.
        + unfold UsedAt in Huse_dst.
          rewrite Euse in Huse_dst.
          inversion Huse_dst.
      }
    }
  Qed.

  Lemma propagate_load_unique:
    forall (loads: PTrie.t reg) (dst: reg) (src: reg),
      loads = find_load_reg f.(fn_insts) rs aa ->
      Some src = PTrie.get loads dst ->
        forall (src': reg), Some src' = PTrie.get loads dst -> src = src'.
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
    destruct H_f_valid as [_ Hunique _].
    unfold defs_are_unique in Hunique.
    inversion Hload'.
    generalize (Hunique k' k dst). intro Huniq.
    assert (Hkk: k = k').
    { 
      apply Huniq; unfold DefinedAt.
      - rewrite <- H7. unfold Defs. auto.
      - rewrite <- H0. unfold Defs. auto.
    }
    assert (Hld_eq: LLLd addr dst next = LLLd addr' dst next0).
    { subst. rewrite <- H0 in H7. inversion H7. trivial. }
    inversion Hld_eq as [Haddr].
    rewrite <- Haddr in H6.
    rewrite <- H6 in H.
    inversion H.
    rewrite <- H15 in Hstore'.
    rewrite <- H16 in Hstore'.
    inversion Hstore.
    inversion Hstore'.
    subst.
    rewrite <- H14 in H21.
    inversion H21.
    reflexivity.
  Qed.

  Lemma propagate_load_no_refl:
    forall (loads: PTrie.t reg) (dst: reg) (src: reg),
      loads = find_load_reg f.(fn_insts) rs aa ->
      Some src = PTrie.get loads dst -> 
      src <> dst.
  Proof.
    intros loads dst src.
    intros Hloads.
    intros Hin.
    apply propagate_src_dst in Hin; try apply Hloads.
    intro contra. subst.
    destruct Hin as [k [addr [object [offset [Hload Hstore]]]]].
    inversion Hload.
    inversion Hstore.
    subst.
    apply (reaching_store_origin f aa) in Hstore.
    destruct Hstore as [orig [_ [_ [Hstore dom]]]].
    inversion Hstore.
    subst.
    assert (Huse: Uses (LLSt addr0 dst next0) dst). unfold Uses. auto.
    destruct H_f_valid as [Huses_have_defs Hdefs_are_unique _].
    unfold uses_have_defs in Huses_have_defs.
    unfold defs_are_unique in Hdefs_are_unique.
    assert (Huse_dst: UsedAt f orig dst). 
    { unfold UsedAt. rewrite <- H1. unfold Uses. auto. }
    generalize (Huses_have_defs orig dst Huse_dst).
    intros Hdef_exists.
    destruct Hdef_exists as [def [Hdef Hdom]].
    clear Huses_have_defs.
    assert (Hkdef: k = def).
    { 
      apply Hdefs_are_unique with (r := dst). 
      - apply Hdef.
      - unfold DefinedAt. rewrite <- H0. unfold Defs. auto.
    }
    subst.
    inversion Hdom.
    inversion dom.
    generalize (dom_antisym f orig def DOM0 DOM).
    intros eq. apply STRICT in eq. inversion eq.
  Qed.

  Lemma propagate_use_origin:
    forall (loads: PTrie.t reg) (user: inst) (user': inst) (r: reg),
      loads = find_load_reg f.(fn_insts) rs aa ->
      user' = rewrite_inst user loads ->
      Uses user r ->
      (
        (PTrie.get loads r = None /\ Uses user' r)
        \/
        (exists (r': reg), Some r' = PTrie.get loads r /\ Uses user' r')
      ).
  Proof.
    intros loads user user' r Hloads Huser' Huses.
    unfold rewrite_inst in Huser'.
    unfold rewrite_uses in Huser'.
    unfold rewrite_reg in Huser'.
    destruct (PTrie.get loads r) eqn:Eload.
    {
      right.
      exists r0.
      split; auto.
      destruct user; inversion Huses;
        subst;
        try rewrite Eload;
        unfold Uses;
        try reflexivity.
      + left. reflexivity.
      + right. reflexivity.
      + left. reflexivity.
      + unfold Uses in Huses.
        destruct Huses.
        - left. subst. rewrite Eload. reflexivity.
        - right.
          apply in_map_iff.
          exists r.
          split.
          rewrite Eload. reflexivity.
          apply H.
      + left. reflexivity.
      + right. reflexivity.
    }
    {
      left.
      split; try reflexivity.
      destruct user; destruct Huses;
        unfold Uses;
        rewrite Huser';
        try rewrite H;
        try rewrite Eload;
        auto.
      right.
      apply in_map_iff.
      exists r.
      rewrite Eload.
      split. reflexivity. apply H.
    }
  Qed.

  Lemma propagate_use_inversion:
    forall (loads: PTrie.t reg) (user: inst) (user': inst) (r: reg),
      loads = find_load_reg f.(fn_insts) rs aa ->
      user' = rewrite_inst user loads ->
      Uses user' r ->
      (
        (PTrie.get loads r = None /\ Uses user r)
        \/
        (exists (r': reg), PTrie.get loads r' = Some r /\ Uses user r')
      ).
  Proof.
    intros loads user user' r Hloads Huser' Huses.
    rewrite Huser' in Huses.
    unfold rewrite_inst in Huses.
    unfold rewrite_uses in Huses.
    unfold rewrite_reg in Huses.
    unfold rewrite_inst in Huser'.
    unfold rewrite_uses in Huser'.
    unfold rewrite_reg in Huser'.
    unfold Uses in Huses.
    unfold Uses.
    destruct user eqn:Euser; destruct Huses;
      repeat match goal with
      | [ |- context [loads ! ?reg] ] => 
        destruct (loads ! reg) eqn:?reg
      | [ H: _ ! ?reg = Some ?v |- context [ _ ! _ = Some ?v ] ] => 
        right; exists reg; auto
      | [ H: _ = ?r |- context [ Some ?r ] ] => 
        rewrite <- H
      | [ H0: ?loads ! ?reg = None, H1: ?loads ! ?reg = Some _ |- _ ] =>
        rewrite H0 in H1; inversion H1
      | [ |- _ ] =>
        subst; auto
      end.
    - right.
      apply in_map_iff in H.
      destruct H as [x [Hr Hin]].
      remember (find_load_reg (fn_insts f) rs aa) as loads.
      destruct (Pos.eq_dec r x).
      { 
        destruct (loads ! x) eqn:E.
        { 
          generalize (propagate_load_no_refl loads x x).
          intros Hrefl. 
          apply Hrefl in Heqloads.
          - contradiction Heqloads. reflexivity.
          - symmetry. subst. apply E.
        }
        {
          subst. rewrite E in r0. inversion r0.
        }
      }
      { 
        destruct (loads ! x) eqn:E; subst.
        * exists x. split. apply E. right. apply Hin.
        * rewrite E in r0. inversion r0.
      }
    - apply in_map_iff in H.
      destruct H as [x [Hr Hin]].
      remember (find_load_reg (fn_insts f) rs aa) as loads.
      destruct (Pos.eq_dec r x).
      {
        left. rewrite e. auto.
      }
      {
        destruct (loads ! x) eqn:E.
        {
          subst. right. exists x. 
          split. apply E. right. apply Hin.
        }
        {
          subst. left. split; auto.
        }
      }
  Qed.

End LOAD_PROPERTIES.

Section PROPAGATE_PROPERTIES.
  Variable f: func.
  Hypothesis H_f_valid: is_valid f.

  Lemma preserves_succ:
    forall (src: node) (dst: node),
      Succ f src dst <-> 
      Succ (propagate_store_to_load f) src dst.
  Proof.
    remember (local_pta f) as aa.
    remember (analyse_reaching_stores f aa) as rs.
    remember ((find_load_reg (fn_insts f) rs aa)) as loads.
    intros src dst.
    split.
    {
      intros Hsucc.
      unfold propagate_store_to_load.
      unfold rewrite_insts.
      unfold rewrite_inst.
      unfold Succ in *.
      simpl.
      rewrite PTrie.map_get.
      destruct ((fn_insts f) ! src); try inversion Hsucc.
      unfold rewrite_uses. simpl.
      unfold SuccessorOfInst in *.
      destruct i; subst; auto.
    }
    {
      intros Hsucc.
      unfold propagate_store_to_load in *.
      unfold rewrite_insts in *.
      unfold rewrite_inst in *.
      unfold Succ in *.
      simpl in Hsucc.
      rewrite PTrie.map_get in Hsucc.
      destruct ((fn_insts f) ! src); try inversion Hsucc.
      simpl in Hsucc.
      unfold SuccessorOfInst in *.
      destruct i; subst; auto.
    }
  Qed.

  Lemma preserves_dom:
    forall (src: node) (dst: node),
      Dominates f src dst <-> 
      Dominates (propagate_store_to_load f) src dst.
  Proof.
    intros src dst.
    split; 
      intros Hdom;
      apply (eq_cfg_dom f (propagate_store_to_load f));
      try apply preserves_succ;
      try apply Hdom.
  Qed.

  Lemma preserves_sdom:
    forall (src: node) (dst: node),
      StrictlyDominates f src dst <-> 
      StrictlyDominates (propagate_store_to_load f) src dst.
  Proof.
    intros src dst.
    split; 
      intro Hdom; inversion Hdom; 
      subst; 
      apply sdom_path; try apply STRICT; apply preserves_dom; apply DOM.
  Qed.

  Lemma preserves_defs:
    forall (n: node) (r: reg),
      DefinedAt (propagate_store_to_load f) n r <-> DefinedAt f n r.
  Proof.
    intros n reg.
    split.
    {
      intro Hdef'.
      unfold DefinedAt in Hdef'.
      destruct ((fn_insts (propagate_store_to_load f)) ! n) eqn:E; 
        try inversion Hdef'.
      unfold propagate_store_to_load, rewrite_insts in E.
      simpl in E. symmetry in E.
      apply PTrie.map_in in E.
      destruct E as [inst [Hloc Hdef]].
      unfold DefinedAt.
      rewrite <- Hloc.
      rewrite Hdef in Hdef'.
      unfold rewrite_inst, rewrite_uses in Hdef'.
      unfold Defs in Hdef'. unfold Defs.
      destruct inst; auto.
    }
    {
      intros Hdef.
      unfold DefinedAt in Hdef.
      destruct ((fn_insts f) ! n) eqn:E; try inversion Hdef.
      unfold propagate_store_to_load, rewrite_insts.
      unfold DefinedAt.
      simpl.
      rewrite PTrie.map_get.
      unfold option_map.
      rewrite E.
      unfold rewrite_inst.
      unfold rewrite_uses.
      unfold Defs in  *.
      destruct i; auto.
    }
  Qed.

  Theorem preserves_validity:
    is_valid (propagate_store_to_load f).
  Proof.
    remember (propagate_store_to_load f) as f'.
    remember (local_pta f) as aa.
    remember (analyse_reaching_stores f aa) as rs.
    remember ((find_load_reg (fn_insts f) rs aa)) as loads.
    destruct H_f_valid as [Hdefs Huniq Hord].
    repeat split.
    (* Defs have uses *)
    {
      unfold uses_have_defs.
      intros use r.
      intros Hused.
      rewrite Heqf' in Hused.
      unfold propagate_store_to_load in Hused.
      rewrite <- Heqaa in Hused.
      rewrite <- Heqrs in Hused.
      rewrite <- Heqloads in Hused.
      unfold UsedAt in Hused.
      simpl in Hused.
      destruct ((rewrite_insts (fn_insts f) loads) ! use) as [user'|] eqn:E;
        try inversion Hused.
      unfold rewrite_insts in E.
      symmetry in E.
      apply PTrie.map_in in E.
      destruct E.
      destruct H as [Hin Hwr].
      generalize (propagate_use_inversion f rs aa H_f_valid loads x user' r Heqloads Hwr Hused).
      intros Hinv.
      generalize (Hdefs use r).
      intros Huse_implies_def.
      destruct Hinv.
      {
        destruct H as [Hload Huse].
        assert (Huse_at: UsedAt f use r).
        { unfold UsedAt. rewrite <- Hin. apply Huse. }
        apply Huse_implies_def in Huse_at.
        destruct Huse_at as [def [Hdef Hdom]].
        exists def.
        split.
        {
          unfold DefinedAt.
          destruct ((fn_insts f') ! def) eqn:E.
          {
            rewrite Heqf' in E.
            unfold propagate_store_to_load, rewrite_insts, rewrite_inst in E.
            simpl in E.
            symmetry in E.
            apply PTrie.map_in in E.
            destruct E as [a [Hin_a Hrw_a]].
            unfold DefinedAt in Hdef.
            rewrite <- Hin_a in Hdef.
            rewrite Hrw_a.
            unfold rewrite_uses.
            unfold Defs.
            unfold Defs in Hdef.
            destruct a; subst; auto.
          }
          {
            rewrite Heqf' in E.
            unfold propagate_store_to_load, rewrite_insts, rewrite_inst in E.
            simpl in E.
            rewrite PTrie.map_get in E.
            unfold option_map in E.
            unfold DefinedAt in Hdef.
            destruct ((fn_insts f) ! def) eqn:E'; inversion E.
            inversion Hdom.
            inversion DOM; subst; auto.
          }
        }
        {
          rewrite Heqf'.
          apply preserves_sdom.
          apply Hdom.
        }
      }
      {
        destruct H as [r' [Hsubst Huse]].
        symmetry in Hsubst.
        generalize (propagate_src_dst f rs aa loads r' r Heqloads Hsubst).
        intro Hprop.
        destruct Hprop as [k [addr [object [offset]]]].
        destruct H as [Hload Hstore].
        inversion Hstore.
        subst object0 offset0 val k0.
        generalize (reaching_store_origin f aa rs k r object offset Hstore).
        intros Hdef.
        destruct Hdef as [def' [_ [_ [Hstored_at Hsdom']]]].
        inversion Hstored_at.
        subst object0 offset0 val n.
        assert (Huse_of_r: UsedAt f def' r).
        { unfold UsedAt. rewrite <- H0. unfold Uses. right. reflexivity. }
        generalize (Hdefs def' r Huse_of_r).
        intros Hdef.
        destruct Hdef as [def [Hdef Hsdom]].
        exists def.
        split; rewrite Heqf'.
        - apply preserves_defs. apply Hdef.
        - apply preserves_sdom.
          apply (sdom_trans f def k use).
          + apply (sdom_trans f def def' k). apply Hsdom. apply Hsdom'.
          + inversion Hload.
            assert (Hdef_of_r': DefinedAt f k r').
            { unfold DefinedAt. rewrite <- H3. unfold Defs. auto. }
            assert (Huse_of_r': UsedAt f use r').
            { unfold UsedAt. rewrite <- Hin. apply Huse. }
            apply defs_dominate_uses with (r := r').
            apply H_f_valid.
            apply Hdef_of_r'.
            apply Huse_of_r'.
      }
    }
    (* Uses are unique *)
    {
      unfold defs_are_unique.
      intros def def' r.
      rewrite Heqf'.
      intros Hdef_def.
      apply preserves_defs in Hdef_def.
      intros Hdef_def'.
      apply preserves_defs in Hdef_def'.
      generalize (Huniq def def' r).
      intros Huniqr.
      apply Huniqr. apply Hdef_def. apply Hdef_def'.
    }
    {
      unfold well_ordered.
      intros def use.
      intros Hsdom.
      generalize (Hord def use).
      intros Hord'.
      apply Hord'.
      apply preserves_sdom.
      rewrite <- Heqf'.
      apply Hsdom.
    }
  Qed.
End PROPAGATE_PROPERTIES.
