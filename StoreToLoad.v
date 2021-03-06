(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Require Import LLIR.Aliasing.
Require Import LLIR.LLIR.
Require Import LLIR.Maps.
Require Import LLIR.Closure.
Require Import LLIR.Values.
Require Import LLIR.SSA.
Require Import LLIR.ReachingStores.
Require Import LLIR.Dom.
Require Import LLIR.Block.
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

  Hypothesis H_f_valid: valid_func f.
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
      constructor;
      apply inst_used_at with (i := LLSt addr1 src next0);
      auto; constructor.
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
      constructor;
      apply inst_defined_at with (i := LLLd (t, dst) next addr);
      auto; constructor.
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
    subst user'.
    destruct user eqn:Euser; inversion Huses; clear Huses;
    match goal with
    | [ H: Some ?v' = option_map (rewrite_reg loads') ?v |- _ ] =>
      destruct v as [v''|]eqn:Ev; simpl in H; inversion H as [H'];
      subst v'; symmetry in H'; rewrite <- H'
    | [ |- _ ] =>
      idtac
    end;
    match goal with
    | [ H: rewrite_reg loads' ?old = r
      |- context [ loads' ! (rewrite_reg loads' ?old) = None ]
      ] =>
      unfold rewrite_reg in H;
      unfold rewrite_reg;
      destruct (loads' ! old) eqn:Eold;
      [ subst p; right; exists old; split; [auto|constructor]
      | left; split; [assumption|constructor]
      ]
    | [ ARGS: In r (map (rewrite_reg loads') ?args)
      , ARG: ?arg = r
      |- _
      ] =>
      apply in_map_iff in ARGS;
      destruct ARGS as [x [RW IN]];
      unfold rewrite_reg in RW;
      destruct (loads' ! r) eqn:Er;
      [ right; exists x; destruct (loads' ! x) eqn:Ex; split;
        [ subst; auto
        | constructor; auto
        | subst; rewrite Ex in Er; inversion Er
        | constructor; auto
        ]
      | destruct (loads' ! x) eqn:Ex;
        [ right; exists x; split; [subst|constructor]; auto
        | left; split; subst; constructor; auto
        ]
      ]
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
    inversion Huses as [dst ins n' r' ARG H]; subst n' r'.
    destruct user; inversion H; subst ins.
    apply in_map_iff in ARG.
    destruct ARG as [[n' r'] [Heq Hin]].
    destruct (Pos.eq_dec r r').
    {
      subst r'.
      inversion Heq. subst n'.
      destruct (loads' ! r) eqn:E.
      {
        right. exists r; split; auto.
        constructor; auto.
      }
      {
        left. split; auto.
        constructor; auto.
      }
    }
    {
      destruct (loads' ! r') eqn:E; inversion Heq.
      {
        subst n' p.
        right. exists r'. split; auto.
        constructor; auto.
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
  Hypothesis H_f_valid: valid_func f.

  Lemma preserves_succ:
    forall (src: node) (dst: node),
      SuccOf f src dst <->
      SuccOf (propagate_store_to_load f) src dst.
  Proof.
    intros src dst.
    split.
    {
      intros Hsucc.
      unfold propagate_store_to_load.
      remember (Aliasing.analyse f) as aa.
      remember (ReachingStores.analyse f aa) as rs.
      remember ((find_load_reg (fn_insts f) rs aa)) as loads.
      remember (closure loads) as loads'.
      inversion Hsucc.
      apply succ_of with (i := rewrite_inst i loads'); simpl.
      {
        unfold rewrite_insts.
        rewrite PTrie.map_get.
        rewrite <- HN; simpl.
        reflexivity.
      }
      {
        unfold rewrite_insts.
        rewrite PTrie.map_get.
        destruct ((fn_insts f) ! dst) eqn:Edst; [|contradiction].
        simpl. intros contra. inversion contra.
      }
      {
        unfold rewrite_inst.
        unfold rewrite_inst_uses.
        inversion SUCC; subst; constructor.
      }
    }
    {
      intros Hsucc.
      inversion Hsucc.
      unfold propagate_store_to_load in *.
      unfold rewrite_insts in *.
      unfold rewrite_inst in *.
      simpl in HN; rewrite PTrie.map_get in HN.
      simpl in HM; rewrite PTrie.map_get in HM.
      remember (Aliasing.analyse f) as aa.
      remember (ReachingStores.analyse f aa) as rs.
      remember ((find_load_reg (fn_insts f) rs aa)) as loads.
      remember (closure loads) as loads'.
      destruct ((fn_insts f) ! src) as [isrc|] eqn:Esrc; simpl in HN; inversion HN.
      unfold rewrite_inst_uses in HN.
      destruct ((fn_insts f) ! dst) as [idst|] eqn:Edst; simpl in HM; try contradiction.
      apply succ_of with (i := isrc).
      { auto. }
      { rewrite Edst; intros contra; inversion contra. }
      { destruct isrc; subst i; simpl in SUCC; inversion SUCC; constructor. }
    }
  Qed.

  Lemma preserves_entry:
    f.(fn_entry) = (propagate_store_to_load f).(fn_entry).
  Proof.
    unfold propagate_store_to_load; auto.
  Qed.

  Lemma preserves_dom:
    forall (src: node) (dst: node),
      Dominates f src dst <->
      Dominates (propagate_store_to_load f) src dst.
  Proof.
    intros src dst.
    split; intros Hdom;
      apply (eq_cfg_dom f (propagate_store_to_load f)
        preserves_entry preserves_succ);
      auto.
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

  Lemma preserves_term:
    forall (n: node),
      TermAt f n <-> TermAt (propagate_store_to_load f) n.
  Proof.
    intros n.
    split; intros H;
      unfold propagate_store_to_load in *;
      unfold rewrite_insts in *;
      remember (Aliasing.analyse f) as aa;
      remember (ReachingStores.analyse f aa) as rs;
      remember ((find_load_reg (fn_insts f) rs aa)) as loads;
      remember (closure loads) as loads'.
    {
      inversion H.
      apply term_at with (i := rewrite_inst i loads').
      { simpl. rewrite PTrie.map_get. rewrite <- INST. simpl. auto. }
      {
        inversion TERM;
        unfold rewrite_inst; unfold rewrite_inst_uses;
        constructor.
      }
    }
    {
      inversion H.
      simpl in INST.
      rewrite PTrie.map_get in INST.
      destruct ((fn_insts f) ! n) as [inst|] eqn:Einst; simpl in INST; inversion INST.
      apply term_at with (i := inst); auto.
      subst i.
      unfold rewrite_inst in TERM; unfold rewrite_inst_uses in TERM.
      destruct inst; inversion TERM; constructor.
    }
  Qed.

  Lemma preserves_join_points:
    forall (n: node),
      JoinPoint f n <-> JoinPoint (propagate_store_to_load f) n.
  Proof.
    intros n; split; intros H; inversion H;
      apply join_point with p0 p1; auto;
      apply preserves_succ; auto.
  Qed.

  Lemma preserves_blocks:
    forall (h: node) (e: node),
      BasicBlock f h e <->
      BasicBlock (propagate_store_to_load f) h e.
  Proof.
    intros h e.
    split; intros H.
    {
      induction H.
      {
        inversion HEADER.
        apply bb_header.
        apply block_header.
        {
          apply (eq_cfg_reach f (propagate_store_to_load f)
            preserves_entry preserves_succ); auto.
        }
        {
          intros term Hsucc.
          apply preserves_succ in Hsucc.
          apply TERM in Hsucc.
          apply preserves_term; auto.
        }
        {
          intros contra.
          destruct ((fn_insts f) ! header) eqn:Eheader; try contradiction.
          unfold propagate_store_to_load in contra.
          unfold rewrite_insts in contra.
          simpl in contra.
          rewrite PTrie.map_get in contra.
          rewrite Eheader in contra.
          simpl in contra.
          inversion contra.
        }
      }
      {
        apply bb_elem with (prev := prev); auto.
        { apply preserves_succ; auto. }
        { intros contra. apply preserves_term in contra. contradiction. }
        {
          intros contra.
          destruct ((fn_insts f) ! elem) eqn:Eheader; try contradiction.
          unfold propagate_store_to_load in contra.
          unfold rewrite_insts in contra.
          simpl in contra.
          rewrite PTrie.map_get in contra.
          rewrite Eheader in contra.
          simpl in contra.
          inversion contra.
        }
        {
          unfold propagate_store_to_load.
          unfold rewrite_phis.
          simpl.
          rewrite PTrie.map_get.
          rewrite NO_PHI.
          simpl.
          reflexivity.
        }
        {
          intros prev' Hsucc.
          apply UNIQ.
          apply preserves_succ; auto.
        }
      }
    }
    {
      induction H.
      {
        inversion HEADER.
        apply bb_header.
        apply block_header.
        {
          apply (eq_cfg_reach f (propagate_store_to_load f)
            preserves_entry preserves_succ); auto.
        }
        {
          intros term Hsucc.
          apply preserves_succ in Hsucc.
          apply TERM in Hsucc.
          apply preserves_term; auto.
        }
        {
          intros contra.
          destruct ((fn_insts (propagate_store_to_load f)) ! header) eqn:Eheader;
            try contradiction.
          unfold propagate_store_to_load in Eheader.
          unfold rewrite_insts in Eheader.
          simpl in Eheader.
          rewrite PTrie.map_get in Eheader.
          rewrite contra in Eheader.
          simpl in Eheader.
          inversion Eheader.
        }
      }
      {
        apply bb_elem with (prev := prev); auto.
        { apply preserves_succ; auto. }
        { intros contra. apply preserves_term in contra. contradiction. }
        {
          intros contra.
          destruct ((fn_insts (propagate_store_to_load f)) ! elem) eqn:Eheader;
            try contradiction.
          unfold propagate_store_to_load in Eheader.
          unfold rewrite_insts in Eheader.
          simpl in Eheader.
          rewrite PTrie.map_get in Eheader.
          rewrite contra in Eheader.
          simpl in Eheader.
          inversion Eheader.
        }
        {
          unfold propagate_store_to_load in NO_PHI.
          unfold rewrite_phis in NO_PHI.
          simpl in NO_PHI.
          rewrite PTrie.map_get in NO_PHI.
          destruct ((fn_phis f) ! elem) eqn:Ephi; try reflexivity.
          simpl in NO_PHI.
          inversion NO_PHI.
        }
        {
          intros prev' Hsucc.
          apply UNIQ.
          apply preserves_succ; auto.
        }
      }
    }
  Qed.

  Lemma preserves_inst_defs:
    forall (n: node) (r: reg),
      InstDefinedAt (propagate_store_to_load f) n r <-> InstDefinedAt f n r.
  Proof.
    intros n reg; split.
    {
      intro Hdef'; inversion Hdef'.
      unfold propagate_store_to_load, rewrite_insts in INST.
      simpl in INST. apply PTrie.map_in in INST.
      destruct INST as [inst [Hloc Hdef]]. subst i.
      apply inst_defined_at with (i := inst). apply Hloc.
      unfold rewrite_inst, rewrite_inst_uses in DEFS.
      destruct inst; inversion DEFS; constructor.
    }
    {
      intros Hdef; inversion Hdef.
      unfold propagate_store_to_load, rewrite_insts.
      remember (Aliasing.analyse f) as aa.
      remember (ReachingStores.analyse f aa) as rs.
      remember ((find_load_reg (fn_insts f) rs aa)) as loads.
      remember (closure loads) as loads'.
      apply inst_defined_at with (i := rewrite_inst i loads').
      {
        simpl.
        rewrite PTrie.map_get.
        unfold option_map.
        rewrite <- INST.
        auto.
      }
      {
        unfold rewrite_inst; unfold rewrite_inst_uses.
        destruct i; try destruct dst; inversion DEFS; constructor.
      }
    }
  Qed.

  Lemma preserves_phi_defs:
    forall (n: node) (r: reg),
      PhiDefinedAt (propagate_store_to_load f) n r <-> PhiDefinedAt f n r.
  Proof.
    intros n reg; split.
    {
      intro Hdef'; inversion Hdef'.
      unfold propagate_store_to_load, rewrite_phis in PHIS.
      simpl in PHIS. apply PTrie.map_in in PHIS.
      destruct PHIS as [phis_f [Hloc_phis Hdef_phis]].
      apply phi_defined_at with (phis := phis_f). apply Hloc_phis.
      apply Exists_exists in DEFS.
      destruct DEFS as [phi' [Hin_phi Hdef_phi']].
      rewrite Hdef_phis in Hin_phi.
      apply List.in_map_iff in Hin_phi.
      destruct Hin_phi as [phi [Hrw Hin]].
      apply Exists_exists.
      exists phi. split. auto.
      destruct phi'; destruct phi.
      unfold rewrite_phi, rewrite_phi_uses in Hrw.
      inversion Hrw.
      inversion Hdef_phi'.
      constructor.
    }
    {
      intros Hdef; inversion Hdef.
      apply Exists_exists in DEFS.
      destruct DEFS as [phi [Hin_phi Hdef_phi]].
      remember (Aliasing.analyse f) as aa.
      remember (ReachingStores.analyse f aa) as rs.
      remember ((find_load_reg (fn_insts f) rs aa)) as loads.
      remember (closure loads) as loads'.
      apply phi_defined_at with (phis := rewrite_phi_block phis loads').
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
          unfold rewrite_phi; unfold rewrite_phi_uses.
          destruct phi.
          inversion Hdef_phi.
          constructor.
        }
      }
    }
  Qed.

  Lemma preserves_defs:
    forall (n: node) (r: reg),
      DefinedAt (propagate_store_to_load f) n r <-> DefinedAt f n r.
  Proof.
    intros n r; split.
    {
      intros Hdef; inversion Hdef.
      - apply defined_at_inst; apply preserves_inst_defs; auto.
      - apply defined_at_phi; apply preserves_phi_defs; auto.
    }
    {
      intros Hdef; inversion Hdef.
      - apply defined_at_inst; apply preserves_inst_defs; auto.
      - apply defined_at_phi; apply preserves_phi_defs; auto.
    }
  Qed.

  Theorem preserves_validity:
    valid_func (propagate_store_to_load f).
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
      inversion Hused; clear Hused; inversion USE.
      {
        simpl in INST.
        unfold rewrite_insts in INST.
        apply PTrie.map_in in INST.
        destruct INST as [i_use [Hin Hwr]].
        generalize (propagate_inst_use_inversion
          f aa rs loads loads' Heqloads Heqloads'
          i_use i r Hwr USES
        ).
        intros Hinv.
        generalize (Hdefs use r).
        intros Huse_implies_def.
        destruct Hinv as [[Hload Huse]|[r' [Hsubst Huse]]].
        {
          assert (Huse_at: UsedAt f use r).
          {
            apply used_at_inst; apply inst_used_at with (i := i_use).
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
            {
              apply used_at_inst;
              apply inst_used_at with (i := i_use).
              apply Hin. apply Huse.
            }
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
            apply used_at_phi;
            apply phi_used_at with (block := block) (phis := phis').
            apply Hin. apply Huses.
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
            {
              apply used_at_phi;
              apply phi_used_at with (block := block) (phis := phis').
              apply Hin. apply Huse.
            }
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
    (* Blocks are valid *)
    {
      unfold blocks_are_valid.
      intros e.
      generalize (fn_blocks_are_valid e); intros Hblocks.
      destruct Hblocks as [[h Hbb]|Hnone].
      {
        left.
        apply preserves_blocks in Hbb. rewrite <- Heqf' in Hbb.
        exists h; auto.
      }
      {
        right.
        subst f'.
        unfold propagate_store_to_load; unfold rewrite_insts; simpl.
        rewrite PTrie.map_get.
        rewrite Hnone.
        simpl; auto.
      }
    }
    (* Insts do not use defs *)
    {
      unfold inst_does_not_use_defs.
      intros def r Hdef contra; inversion contra.
      rewrite Heqf' in Hdef; apply preserves_inst_defs in Hdef.
      rewrite Heqf' in INST;
      unfold propagate_store_to_load in INST; unfold rewrite_insts in INST;
      simpl in INST; rewrite PTrie.map_get in INST.
      destruct ((fn_insts f) ! def) as [i'|] eqn:Ei; inversion INST as [INST'].
      rewrite <- Heqaa in INST';
      rewrite <- Heqrs in INST';
      rewrite <- Heqloads in INST';
      rewrite <- Heqloads' in INST'.
      generalize (propagate_inst_use_inversion
        f aa rs loads loads' Heqloads Heqloads'
        i' i r INST' USES); intros Hprop.
      destruct Hprop as [[Hload Huses]|[r' [Hload Huses]]].
      {
        generalize (fn_inst_does_not_use_defs def r Hdef); intros Hcontra.
        assert (Hused_at: InstUsedAt f def r).
        { apply inst_used_at with (i := i'); auto. }
        contradiction.
      }
      {
        clear INST.
        inversion Hdef; rewrite Ei in INST; inversion INST; subst i0.
        symmetry in Hload.
        generalize (H_loads_relation' loads loads' Heqloads' r' r Hload); intros Hchain.
        generalize (propagate_chain_sdom
          f aa rs loads loads' H_f_valid Heqloads Heqloads'
          r' r Hchain); intros [ks [kd [Hks [Hkd Hsdom]]]].
        assert (Hdef_at: DefinedAt f def r). { constructor; auto. }
        generalize (Huniq ks def r Hks Hdef_at); intros Hksd; subst ks.
        assert (Hused_at: UsedAt f def r').
        { constructor. apply inst_used_at with (i := i'); auto. }
        generalize (defs_dominate_uses f H_f_valid kd def r' Hkd Hused_at); intros Hdom.
        inversion Hsdom.
        generalize (dom_antisym f kd def Hdom DOM); intros Hkddef.
        contradiction.
      }
    }
    (* Phi or instruction *)
    {
      intros Hdef_at Hphi_at.
      rewrite Heqf' in Hdef_at; rewrite Heqf' in Hphi_at.
      apply preserves_inst_defs in Hdef_at.
      apply preserves_phi_defs in Hphi_at.
      generalize (fn_phi_or_inst def r); intros [Hip _].
      apply Hip in Hdef_at.
      contradiction.
    }
    {
      intros Hphi_at Hdef_at.
      rewrite Heqf' in Hdef_at; rewrite Heqf' in Hphi_at.
      apply preserves_inst_defs in Hdef_at.
      apply preserves_phi_defs in Hphi_at.
      generalize (fn_phi_or_inst def r); intros [Hip _].
      apply Hip in Hdef_at.
      contradiction.
    }
    (* Phis are complete *)
    {
      intros n p block t r ins Hsucc Hphis Hin.
      rewrite Heqf' in Hphis.
      unfold propagate_store_to_load in Hphis.
      simpl in Hphis.
      rewrite <- Heqaa in Hphis.
      rewrite <- Heqrs in Hphis.
      rewrite <- Heqloads in Hphis.
      unfold rewrite_phis in Hphis.
      rewrite PTrie.map_get in Hphis.
      destruct ((fn_phis f) ! n) as [block'|] eqn:Eblock; [|inversion Hphis].
      inversion Hphis as [Hphis']; subst block; clear Hphis.
      unfold rewrite_phi_block in Hin.
      rewrite in_map_iff in Hin.
      destruct Hin as [phi [Hphi Hin ]].
      unfold rewrite_phi in Hphi; unfold rewrite_phi_uses in Hphi.
      destruct phi as [[t' dst'] ins']; inversion Hphi; subst t' dst'.
      rewrite Heqf' in Hsucc; apply preserves_succ in Hsucc.
      symmetry in Eblock.
      generalize (fn_phis_are_complete 
        n p block' t r ins' Hsucc Eblock Hin
      ); intros [r' Hinr].
      exists (rewrite_reg (closure loads) r').
      apply in_map_iff. exists (p, r'); split; auto.
    }
    (* Succs are valid *)
    {
      intros n m i Hinst Hsucc.
      rewrite Heqf'.
      apply preserves_succ.
      rewrite Heqf' in Hinst.
      unfold propagate_store_to_load in Hinst.
      simpl in Hinst.
      rewrite <- Heqaa in Hinst.
      rewrite <- Heqrs in Hinst.
      rewrite <- Heqloads in Hinst.
      unfold rewrite_insts in Hinst.
      rewrite PTrie.map_get in Hinst.
      destruct ((fn_insts f) ! n) as [i'|] eqn:Ei'; [|inversion Hinst].
      simpl in Hinst; inversion Hinst as [Hinst'].
      symmetry in Ei'.
      apply (fn_succs_are_valid n m i' Ei').
      destruct i'; rewrite Hinst' in Hsucc;
      unfold rewrite_inst in Hsucc;
      unfold rewrite_inst_uses in Hsucc;
      inversion Hsucc; subst; constructor.
    }
  Qed.

End PROPAGATE_PROPERTIES.
