(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Require Import LLIR.Aliasing.
Require Import LLIR.LLIR.
Require Import LLIR.Maps.
Require Import LLIR.Closure.
Require Import LLIR.State.
Require Import LLIR.Values.
Require Import LLIR.SSA.
Require Import LLIR.ReachingStores.
Require Import LLIR.Dom.
Require Import LLIR.Transform.

Import ListNotations.



Definition find_load_reg
    (insts: inst_map)
    (rs: ReachingStores.t)
    (aa: Aliasing.t): PTrie.t reg :=
  PTrie.extract (PTrie.map_opt
    (fun k inst =>
      match inst with
      | LLLd (ty, dst) next addr =>
        match Aliasing.get_precise_addr aa addr with
        | Some obj =>
          match ReachingStores.get_store_to rs k obj with
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
  rewrite_inst_uses i (rewrite_reg loads).

Definition rewrite_insts (insts: inst_map) (loads: PTrie.t reg): inst_map :=
  PTrie.map (fun k i => rewrite_inst i loads) insts.

Definition rewrite_phi (p: phi) (loads: PTrie.t reg): phi :=
  rewrite_phi_uses p (rewrite_reg loads).

Definition rewrite_phi_block (phis: list phi) (loads: PTrie.t reg): list phi :=
  List.map (fun p => rewrite_phi p loads) phis.

Definition rewrite_phis (phis: phi_map) (loads: PTrie.t reg): phi_map :=
  PTrie.map (fun k phis => rewrite_phi_block phis loads) phis.

Definition propagate_store_to_load (f: func): func :=
  let aa := Aliasing.analyse f in
  let rs := ReachingStores.analyse f aa in
  let loads := closure (find_load_reg f.(fn_insts) rs aa) in
  let fn_insts := rewrite_insts f.(fn_insts) loads in
  let fn_phis := rewrite_phis f.(fn_phis) loads in
  mkfunc f.(fn_stack) fn_insts fn_phis f.(fn_entry).

Section LOAD_PROPERTIES.
  Variable f: func.
  Variable aa: Aliasing.t.
  Variable rs: ReachingStores.t.
  Variable loads: relation.
  Variable loads': relation.

  Hypothesis H_f_valid: is_valid f.
  Hypothesis Heqloads: loads = find_load_reg f.(fn_insts) rs aa.
  Hypothesis Heqloads': loads' = closure loads.

  Lemma H_loads_relation: is_relation loads loads.
  Proof.
    intros dst src. intros H. apply closure_chain_elem. apply H.
  Qed.

  Lemma H_loads_relation': is_relation loads loads'.
  Proof.
    subst loads'. apply closure_valid. apply H_loads_relation.
  Qed.

  Lemma propagate_src_dst:
    forall (dst: reg) (src: reg),
      Some src = loads ! dst ->
        exists (k: node) (addr: reg) (object: positive) (offset: positive),
          Aliasing.loads_from f aa k dst addr object offset /\
          ReachingStores.store_reaches rs k src object offset.
  Proof.
    intros src dst Helem.
    subst loads.
    apply PTrie.extract_inversion in Helem.
    destruct Helem as [k Helem].
    exists k.
    apply PTrie.map_opt_inversion in Helem.
    destruct Helem as [inst].
    destruct H as [Hinst Hfunc].
    destruct inst; inversion Hfunc. destruct dst0.
    destruct (Aliasing.get_precise_addr aa addr) eqn:Hload; inversion Hfunc; clear H0.
    destruct (ReachingStores.get_store_to rs k o) eqn:Hstore; inversion Hfunc; clear H0.
    destruct o as [object offset].
    exists addr. exists object. exists offset.
    inversion Hfunc; subst.
    split.
    - apply Aliasing.load with (next := next) (t := t); [symmetry|]; assumption.
    - apply ReachingStores.store. symmetry. assumption.
  Qed.

  Lemma propagate_sdom:
    forall (dst: reg) (src: reg),
      Some src = loads ! dst ->
        exists (ks: node) (kd: node),
          DefinedAt f ks src /\
          DefinedAt f kd dst /\
          StrictlyDominates f ks kd.
  Proof.
    intros dst src Hin.
    apply propagate_src_dst in Hin.
    destruct Hin as [k [addr [object [offset [Hload Hstore]]]]].
    inversion Hload.
    apply ReachingStores.reaching_store_origin with (f := f) (aa := aa) in Hstore.
    destruct Hstore as [orig [Hst_at Hsdom]].
    inversion Hst_at.
    assert (Hused_at: UsedAt f orig src).
    {
      apply used_at_inst with (i := LLSt addr1 src next0); auto.
      unfold InstUses; auto.
    }
    destruct H_f_valid as [Huses_have_defs Huniq].
    unfold uses_have_defs in Huses_have_defs.
    generalize (Huses_have_defs orig src Hused_at).
    intros Hdef.
    destruct Hdef as [def [Hdefs Hdom]].
    exists def. exists k.
    split. apply Hdefs.
    split.
    {
      apply defined_at_inst with (i := LLLd (t, dst) next addr); auto.
      unfold InstDefs; auto.
    }
    apply sdom_dom.
    apply dom_trans with (m := orig); auto. inversion Hsdom; auto.
    intros contra.
    subst.
    inversion Hsdom.
    subst.
    generalize (dom_antisym f k orig Hdom DOM).
    intros contra. contradiction.
  Qed.

  Lemma propagate_chain_sdom:
    forall (dst: reg) (src: reg),
      chain loads dst src ->
        exists (ks: node) (kd: node),
          DefinedAt f ks src /\
          DefinedAt f kd dst /\
          StrictlyDominates f ks kd.
  Proof.
    intros dst src Hchain.
    induction Hchain.
    + apply propagate_sdom with (dst := dst). apply HE.
    + destruct IHHchain1 as [ks1 [kd1 [Hdef1s [Hdef1d Hdom1]]]].
      destruct IHHchain2 as [ks2 [kd2 [Hdef2s [Hdef2d Hdom2]]]].
      assert (kd1 = ks2).
      {
        destruct H_f_valid as [_ Huniq].
        unfold defs_are_unique in Huniq.
        apply Huniq with (r := mid). apply Hdef2s. apply Hdef1d.
      }
      subst kd1. clear Hdef2s.
      exists ks1. exists kd2.
      split. apply Hdef1s.
      split. apply Hdef2d.
      apply sdom_trans with (m := ks2).
      apply Hdom1. apply Hdom2.
  Qed.

  Lemma propagate_load_irrefl:
    forall (dst: reg) (src: reg),
      chain loads dst src ->
      src <> dst.
  Proof.
    intros dst src Hin.
    intro contra.
    subst dst.
    apply propagate_chain_sdom in Hin.
    destruct Hin as [ks [kd [Hdefs [Hdefd Hdom]]]].
    destruct H_f_valid as [_ Huniq].
    unfold defs_are_unique in Huniq.
    assert (Hkeq: ks = kd).
    { apply Huniq with (r := src). apply Hdefd. apply Hdefs. }
    subst kd.
    apply sdom_irrefl in Hdom.
    apply Hdom.
  Qed.

  Lemma propagate_inst_use_inversion:
    forall (user: inst) (user': inst) (r: reg),
      user' = rewrite_inst user loads' ->
      InstUses user' r ->
      (
        (PTrie.get loads' r = None /\ InstUses user r)
        \/
        (exists (r': reg), PTrie.get loads' r' = Some r /\ InstUses user r')
      ).
  Proof.
    intros user user' r Huser' Huses.
    rewrite Huser' in Huses.
    unfold rewrite_inst in Huses.
    unfold rewrite_inst_uses in Huses.
    unfold rewrite_reg in Huses.
    unfold rewrite_inst in Huser'.
    unfold rewrite_inst_uses in Huser'.
    unfold rewrite_reg in Huser'.
    unfold InstUses in Huses.
    unfold InstUses.
    destruct user eqn:Euser;
      repeat match goal with
      | [ |- context [loads' ! ?reg] ] =>
        destruct (loads' ! reg) eqn:?reg
      | [ H: _ ! ?reg = Some ?v |- context [ _ ! _ = Some ?v ] ] =>
        right; exists reg; auto
      | [ H: _ = ?r |- context [ Some ?r ] ] =>
        rewrite <- H
      | [ H0: ?loads ! ?reg = None, H1: ?loads ! ?reg = Some _ |- _ ] =>
        rewrite H0 in H1; inversion H1
      | [ H: ?a = ?b |- _ ] =>
        subst b
      | [ H: (_ = r) \/ _ |- _ ] =>
        destruct H
      | [ H: False |- _ ] =>
        inversion H
      | [ dst: ty * reg |- _] =>
        destruct dst
      | [H: In ?r ?args |- _ ] =>
        apply in_map_iff in H;
        destruct H as [x [Hr Hin]]
      | [ H: context [ option_map ?f ?v ] |- _ ] =>
        destruct value; simpl in H
      | [ |- _ ] =>
        auto
      end.
  Qed.

  Lemma propagate_phi_use_inversion:
    forall (user: phi) (user': phi) (n: node) (r: reg),
      user' = rewrite_phi user loads' ->
      PhiUses user' n r ->
      (
        (PTrie.get loads' r = None /\ PhiUses user n r)
        \/
        (exists (r': reg), PTrie.get loads' r' = Some r /\ PhiUses user n r')
      ).
  Proof.
    intros user user' n r Huser' Huses.
    rewrite Huser' in Huses.
    unfold rewrite_phi in Huses.
    unfold rewrite_phi_uses in Huses.
    unfold rewrite_reg in Huses.
    unfold rewrite_phi in Huser'.
    unfold rewrite_phi_uses in Huser'.
    unfold rewrite_reg in Huser'.
    unfold PhiUses in Huses.
    unfold PhiUses.
    destruct user.

    apply Exists_exists in Huses.
    destruct Huses as [[n' r'] [Hin [Hn Hr]]]. subst n' r'.
    apply in_map_iff in Hin.
    destruct Hin as [[n' r'] [Heq Hin]].

    destruct (Pos.eq_dec r r').
    {
      subst r'.
      destruct (loads' ! r) eqn:E.
      {
        inversion Heq. subst n' p.
        right. exists r; split; auto.
        apply Exists_exists. exists (n, r). auto.
      }
      {
        left. split; auto.
        apply Exists_exists.
        inversion Heq.
        exists (n', r); repeat split; auto.
      }
    }
    {
      destruct (loads' ! r') eqn:E; inversion Heq.
      {
        subst n' p.
        right. exists r'. split; auto.
        apply Exists_exists. exists (n, r'). auto.
      }
      {
        subst r'. contradiction.
      }
    }
  Qed.

  Lemma propagate_phi_block_use_inversion:
    forall (user: list phi) (user': list phi) (n: node) (r: reg),
      user' = rewrite_phi_block user loads' ->
      PhiBlockUses user' n r ->
      (
        (PTrie.get loads' r = None /\ PhiBlockUses user n r)
        \/
        (exists (r': reg), PTrie.get loads' r' = Some r /\ PhiBlockUses user n r')
      ).
  Proof.
    intros user user' n r Huser' Huses.
    unfold PhiBlockUses in Huses.
    apply Exists_exists in Huses.
    destruct Huses as [phi' [Hphi_in' Hphi']].
    rewrite Huser' in Hphi_in'.
    unfold rewrite_phi_block in Hphi_in'.
    apply List.in_map_iff in Hphi_in'.
    destruct Hphi_in' as [phi [Hphi_in Hphi]].
    symmetry in Hphi_in.
    generalize (propagate_phi_use_inversion phi phi' n r Hphi_in Hphi').
    intros Hinv.
    destruct Hinv as [[Hloads Huse]|[r' [Hloads Huse]]].
    {
      left. split; auto.
      unfold PhiBlockUses. apply Exists_exists.
      exists phi; auto.
    }
    {
      right. exists r'. split; auto.
      unfold PhiBlockUses. apply Exists_exists.
      exists phi; auto.
    }
  Qed.
End LOAD_PROPERTIES.

Section PROPAGATE_PROPERTIES.
  Variable f: func.
  Hypothesis H_f_valid: is_valid f.

  Lemma preserves_succ:
    forall (src: node) (dst: node),
      SuccOf f src dst <->
      SuccOf (propagate_store_to_load f) src dst.
  Proof.
    remember (Aliasing.analyse f) as aa.
    remember (ReachingStores.analyse f aa) as rs.
    remember ((find_load_reg (fn_insts f) rs aa)) as loads.
    intros src dst.
    split.
    {
      intros Hsucc.
      unfold propagate_store_to_load.
      unfold rewrite_insts.
      unfold rewrite_inst.
      unfold SuccOf in *.
      simpl.
      rewrite PTrie.map_get.
      rewrite PTrie.map_get.
      destruct ((fn_insts f) ! src) as [inst|]; try inversion Hsucc.
      destruct ((fn_insts f) ! dst) as [inst'|]; try inversion Hsucc.
      unfold rewrite_inst_uses. simpl.
      unfold Succeeds in *.
      destruct inst; try destruct dst0; subst; auto.
    }
    {
      intros Hsucc.
      unfold propagate_store_to_load in *.
      unfold rewrite_insts in *.
      unfold rewrite_inst in *.
      unfold SuccOf in *.
      simpl in Hsucc.
      rewrite PTrie.map_get in Hsucc.
      rewrite PTrie.map_get in Hsucc.
      destruct ((fn_insts f) ! src) as [inst|]; try inversion Hsucc.
      destruct ((fn_insts f) ! dst) as [inst'|]; try inversion Hsucc.
      simpl in Hsucc.
      unfold Succeeds in *.
      destruct inst; try destruct dst0; subst; auto.
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
      apply sdom_dom; try apply STRICT; apply preserves_dom; apply DOM.
  Qed.

  Lemma preserves_defs:
    forall (n: node) (r: reg),
      DefinedAt (propagate_store_to_load f) n r <-> DefinedAt f n r.
  Proof.
    intros n reg.
    split.
    {
      intro Hdef'; inversion Hdef'.
      {
        unfold propagate_store_to_load, rewrite_insts in INST.
        simpl in INST. apply PTrie.map_in in INST.
        destruct INST as [inst [Hloc Hdef]]. subst i.
        apply defined_at_inst with (i := inst). apply Hloc.
        unfold rewrite_inst, rewrite_inst_uses, InstDefs in DEFS. unfold InstDefs.
        destruct inst; try destruct dst; auto.
      }
      {
        unfold propagate_store_to_load, rewrite_phis in PHIS.
        simpl in PHIS. apply PTrie.map_in in PHIS.
        destruct PHIS as [phis_f [Hloc_phis Hdef_phis]].
        apply defined_at_phi with (phis := phis_f). apply Hloc_phis.
        apply Exists_exists in DEFS.
        destruct DEFS as [phi' [Hin_phi Hdef_phi']].
        rewrite Hdef_phis in Hin_phi.
        apply List.in_map_iff in Hin_phi.
        destruct Hin_phi as [phi [Hrw Hin]].
        apply Exists_exists.
        exists phi. split. auto.
        unfold PhiDefs in *.
        destruct phi'; destruct phi.
        unfold rewrite_phi, rewrite_phi_uses in Hrw.
        inversion Hrw.
        auto.
      }
    }
    {
      intros Hdef.
      inversion Hdef.
      {
        unfold propagate_store_to_load, rewrite_insts.
        remember (Aliasing.analyse f) as aa.
        remember (ReachingStores.analyse f aa) as rs.
        remember ((find_load_reg (fn_insts f) rs aa)) as loads.
        remember (closure loads) as loads'.
        apply defined_at_inst with (i := rewrite_inst i loads').
        {
          simpl.
          rewrite PTrie.map_get.
          unfold option_map.
          rewrite <- INST.
          auto.
        }
        {
          unfold InstDefs in *.
          destruct i; try destruct dst; auto.
        }
      }
      {
        apply Exists_exists in DEFS.
        destruct DEFS as [phi [Hin_phi Hdef_phi]].
        remember (Aliasing.analyse f) as aa.
        remember (ReachingStores.analyse f aa) as rs.
        remember ((find_load_reg (fn_insts f) rs aa)) as loads.
        remember (closure loads) as loads'.
        apply defined_at_phi with (phis := rewrite_phi_block phis loads').
        {
          unfold propagate_store_to_load, rewrite_phis. simpl.
          rewrite PTrie.map_get.
          unfold option_map.
          rewrite <- PHIS.
          rewrite <- Heqaa.
          rewrite <- Heqrs.
          rewrite <- Heqloads.
          rewrite <- Heqloads'.
          reflexivity.
        }
        {
          apply Exists_exists.
          exists (rewrite_phi phi loads').
          split.
          {
            unfold rewrite_phi_block.
            apply List.in_map_iff.
            exists phi.
            split; auto.
          }
          {
            unfold PhiDefs in *.
            destruct phi.
            auto.
          }
        }
      }
    }
  Qed.

  Theorem preserves_validity:
    is_valid (propagate_store_to_load f).
  Proof.
    remember (propagate_store_to_load f) as f'.
    remember (Aliasing.analyse f) as aa.
    remember (ReachingStores.analyse f aa) as rs.
    remember ((find_load_reg (fn_insts f) rs aa)) as loads.
    remember (closure loads) as loads'.
    destruct H_f_valid as [Hdefs Huniq].
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
      rewrite <- Heqloads' in Hused.
      inversion Hused; clear Hused.
      {
        simpl in INST.
        unfold rewrite_insts in INST.
        apply PTrie.map_in in INST.
        destruct INST as [i_use [Hin Hwr]].
        generalize (propagate_inst_use_inversion loads' i_use i r Hwr USES).
        intros Hinv.
        generalize (Hdefs use r).
        intros Huse_implies_def.
        destruct Hinv as [[Hload Huse]|[r' [Hsubst Huse]]].
        {
          assert (Huse_at: UsedAt f use r).
          {
            apply used_at_inst with (i := i_use).
            + rewrite <- Hin. reflexivity.
            + apply Huse.
          }
          apply Huse_implies_def in Huse_at.
          destruct Huse_at as [def [Hdef Hdom]].
          exists def.
          rewrite Heqf'.
          split.
          + apply preserves_defs. apply Hdef.
          + apply preserves_dom. apply Hdom.
        }
        {
          assert (Hchain: chain loads r' r).
          {
            apply (H_loads_relation' loads loads' Heqloads').
            symmetry. apply Hsubst.
          }
          generalize (propagate_chain_sdom
            f aa rs loads loads'
            H_f_valid
            Heqloads Heqloads'
            r' r
            Hchain).
          intros Hprop.
          destruct Hprop as [ks [kd [Hdefks [Hdefkd Hdom]]]].
          exists ks.
          split.
          {
            rewrite Heqf'.
            apply preserves_defs.
            apply Hdefks.
          }
          {
            rewrite Heqf'.
            apply preserves_dom.
            clear Huse_implies_def.
            apply dom_trans with (m := kd). inversion Hdom; auto.
            assert (Hused_at_r': UsedAt f use r').
            { apply used_at_inst with (i := i_use). apply Hin. apply Huse. }
            apply defs_dominate_uses with (r := r').
            apply H_f_valid. apply Hdefkd.
            apply Hused_at_r'.
          }
        }
      }
      {
        simpl in PHIS.
        unfold rewrite_phis in PHIS.
        apply PTrie.map_in in PHIS.
        destruct PHIS as [phis' [Hin Hwr]].
        generalize (propagate_phi_block_use_inversion loads' phis' phis use r Hwr USES).
        intros Hinv.
        generalize (Hdefs use r).
        intros Huse_implies_def.
        destruct Hinv as [[_ Huses]|[r' [Hsubst Huse]]].
        {
          assert (Huse_at: UsedAt f use r).
          {
            apply used_at_phi with (block := block) (phis := phis').
            apply Hin.
            apply Huses.
          }
          apply Huse_implies_def in Huse_at.
          destruct Huse_at as [def [Hdef Hdom]].
          exists def.
          rewrite Heqf'.
          split.
          + apply preserves_defs. auto.
          + apply preserves_dom. auto.
        }
        {
          assert (Hchain: chain loads r' r).
          {
            apply (H_loads_relation' loads loads' Heqloads').
            symmetry. apply Hsubst.
          }
          generalize (propagate_chain_sdom
            f aa rs loads loads'
            H_f_valid
            Heqloads Heqloads'
            r' r
            Hchain).
          intros Hprop.
          destruct Hprop as [ks [kd [Hdefks [Hdefkd Hdom]]]].
          exists ks.
          split.
          {
            rewrite Heqf'.
            apply preserves_defs.
            apply Hdefks.
          }
          {
            rewrite Heqf'.
            apply preserves_dom.
            clear Huse_implies_def.
            apply dom_trans with (m := kd). inversion Hdom; auto.
            assert (Hused_at_r': UsedAt f use r').
            { apply used_at_phi with (block := block) (phis := phis'). apply Hin. apply Huse. }
            apply defs_dominate_uses with (r := r').
            apply H_f_valid. apply Hdefkd.
            apply Hused_at_r'.
          }
        }
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
  Qed.
End PROPAGATE_PROPERTIES.
