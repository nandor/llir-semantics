(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.

Require Import LLIR.LLIR.
Require Import LLIR.Maps.
Require Import LLIR.Dom.
Require Import LLIR.State.

Import ListNotations.

Ltac inst_inversion_proof fn :=
  intros inst n Heq;
  unfold fn in Heq; unfold fn_insts in Heq;
  repeat rewrite PTrie.set_get in Heq;
  unfold fst in Heq; unfold snd in Heq;
  repeat match goal with
  | [ Heq: context [Pos.eqb ?v n] |- _ ] =>
    destruct (Pos.eqb v n) eqn:E;
    [ left; apply Pos.eqb_eq in E; subst n; split; auto | clear E; right]
  end;
  auto.

Ltac phi_inversion_proof fn :=
  intros int n Heq;
  unfold fn in Heq; unfold fn_phis in Heq;
  repeat rewrite PTrie.set_get in Heq;
  unfold fst in Heq; unfold snd in Heq;
  repeat match goal with
  | [ Heq: context [Pos.eqb ?v n] |- _ ] =>
    destruct (Pos.eqb v n) eqn:E;
    [ left; apply Pos.eqb_eq in E; subst n; split; auto | clear E; right]
  end;
  auto.

Ltac defined_at_inversion_proof fn fn_inst_inversion fn_phi_inversion :=
  intros n r Hdef_at;
  inversion Hdef_at as [n' r' i INST DEFS|n' r' phi PHIS DEFS];
  [
    unfold InstDefs in *;
    apply fn_inst_inversion in INST;
    repeat (destruct INST as [Hdef|INST];
      [
        destruct Hdef as [Hn Hsome_inst];
        inversion Hsome_inst as [Hinst];
        rewrite <- Hinst in DEFS;
        inversion DEFS;
        subst n r;
        repeat match goal with
        | [ |- (?n = ?n /\ ?r = ?r) \/ _ ] => left; split; reflexivity
        | [ |- ?n = ?n /\ ?r = ?r ] => split; reflexivity
        | [ |- _ ] => right
        end
      |]);
    inversion INST
  |
    unfold PhiDefs in *;
    apply fn_phi_inversion in PHIS;
    repeat (destruct PHIS as [Hdef|PHIS];
      [
        destruct Hdef as [Hn Hsome_inst];
        inversion Hsome_inst as [Hinst];
        rewrite <- Hinst in DEFS;
        apply Exists_exists in DEFS;
        destruct DEFS as [phi' [Hin Hdst]];
        repeat (destruct Hin as [Hphi|Hin];
          [ rewrite <- Hphi in Hdst; subst n r;
            repeat match goal with
            | [ |- (?n = ?n /\ ?r = ?r) \/ _ ] => left; split; reflexivity
            | [ |- ?n = ?n /\ ?r = ?r ] => split; reflexivity
            | [ |- _ ] => right
            end
          |
          ]);
        inversion Hin
      |]);
    inversion PHIS
  ].

Ltac defs_are_unique_proof defined_at_inversion :=
  intros def def' r Hdef Hdef';
  apply defined_at_inversion in Hdef;
  apply defined_at_inversion in Hdef';
  repeat destruct Hdef as [Hdef|Hdef];
  repeat destruct Hdef' as [Hdef'|Hdef'];
  destruct Hdef as [Hd Hn];
  destruct Hdef' as [Hd' Hn'];
  subst r def def'; auto; try inversion Hn'.

Ltac used_at_inversion_proof fn fn_inst_inversion fn_phi_inversion :=
  intros n r Hused_at;
  inversion Hused_at as [n' r' i INST USES|n' r' block phis PHIS USES];
  [
    clear Hused_at; unfold InstUses in *;
    apply fn_inst_inversion in INST;
    repeat (destruct INST as [[Hn Hinst]|INST];
      [ inversion Hinst; clear Hinst; subst i n n' r'
      |
      ]);
      repeat match goal with
      | [ H: False |- _ ] => inversion H
      | [ H: ?a = r \/ ?b = r |- _ ] => destruct H
      end;
      try subst r;
      repeat match goal with
      | [ |- (?n = ?n /\ ?r = ?r) \/ _ ] => left; split; reflexivity
      | [ |- ?n = ?n /\ ?r = ?r ] => split; reflexivity
      | [ |- _ ] => right
      end;
    inversion INST
  |
    clear Hused_at; unfold PhiBlockUses in *;
    apply fn_phi_inversion in PHIS;
    repeat (destruct PHIS as [[Hb Hphis]|PHIS];
      [ inversion Hphis; subst phis; clear Hphis;
        apply Exists_exists in USES;
        destruct USES as [x [Hin Huses]];
        repeat (destruct Hin as [Hphi|Hin];
          [ subst x; unfold PhiUses in Huses;
            apply Exists_exists in Huses;
            destruct Huses as [[n'' r''] [Hphi_in [Hn Hr]]];
            subst n'' r'';
            repeat (destruct Hphi_in as [Hbr|Hphi_in];
              [ inversion Hbr; subst n' r'
              | simpl in Hphi_in
              ])
          | simpl in Hin
          ]);
          repeat match goal with
          | [ H: False |- _ ] => inversion H
          | [ |- (?n = ?n /\ ?r = ?r) \/ _ ] => left; split; reflexivity
          | [ |- ?n = ?n /\ ?r = ?r ] => split; reflexivity
          | [ |- _ ] => right
          end
      |]);
    inversion PHIS
  ].

Ltac reach_pred_step fn pred :=
  apply reach_succ with (a := pred);
  [
    unfold SuccOf;
    simpl;
    auto
  |
  ].

Ltac block_elem_proof fn fn_inv p proof_prev :=
  apply bb_elem with (prev := p);
  [ intro contra; inversion contra
  | intro contra; inversion contra
  | apply proof_prev
  | compute; reflexivity
  | compute; intro contra; inversion contra
  | auto
  | intros prev' Hsucc;
    unfold SuccOf in Hsucc; unfold Succeeds in Hsucc;
    remember ((fn_insts fn) ! prev') as inst eqn:Hinst;
    symmetry in Hinst;
    apply fn_inv in Hinst;
    repeat destruct Hinst as [[Hl Hr]|Hinst]; subst inst; auto; try inversion Hsucc; try inversion H
  ].

Ltac block_header_proof fn fn_inv bb_reach :=
  apply block_header;
  [ apply bb_reach
  | intros term Hsucc;
    unfold SuccOf in Hsucc; unfold Succeeds in Hsucc; unfold TermAt;
    remember ((fn_insts fn) ! term) as inst eqn:H;
    symmetry in H;
    apply fn_inv in H;
    repeat destruct H as [[Hl Hr]|H];
      subst inst; try subst term; simpl; auto;
      inversion Hsucc; inversion H
  | intros contra; inversion contra
  ].

Ltac bb_headers_proof fn func_inversion :=
  intros header Hbb;
  inversion Hbb as [header'' REACH TERM NODE];
  remember ((fn_insts fn) ! header) as inst eqn:Einst;
  remember (get_predecessors fn header) as pred eqn:Epred;
  apply func_inversion in Einst;
  repeat (destruct Einst as [[Ehdr Ei]|Einst]; [auto; (
    rewrite <- Ehdr in Epred;
    compute in Epred;
    match goal with
    | [ E: pred = [ ?p ] |- _ ] =>
      assert (Hsucc: SuccOf fn p header);
      subst header;
      compute;
      auto;
      apply TERM in Hsucc;
      compute in Hsucc;
      inversion Hsucc
    end)|]);
  apply NODE in Einst; inversion Einst.


Ltac bb_inversion_proof fn func_inversion func_headers :=
  intros header elem BLOCK;
  destruct ((fn_insts fn) ! elem) eqn:Einst;
  [ symmetry in Einst;
  apply func_inversion in Einst;
    repeat (destruct Einst as [[Helem _]|Einst];
      [ repeat match goal with
        | [ H: ?e = elem |- ?n = header /\ ?e = elem ] =>
          split; [|subst; reflexivity]
        | [ H: ?e = elem |- (?n = header /\ ?e = elem) \/ _ ] =>
          left
        | [ H: ?e = elem |- _ ] =>
          right
        end;
        repeat (inversion BLOCK as
          [ header' HEADER
          | header' prev' elem' _ _ BLOCK' PRED NOT_TERM _ _ UNIQ
          ]; subst;
          [ match goal with
            | [ |- ?n = ?n ] =>
              reflexivity
            | [ |- _ ] =>
              apply func_headers in HEADER;
              repeat destruct HEADER as [HEADER|HEADER];
              inversion HEADER
            end
          | apply get_predecessors_correct in PRED;
            simpl in PRED;
            repeat (destruct PRED as [PRED|PRED]; [|inversion PRED]);
            match goal with
            | [ H: False |- _ ] => inversion H
            | [ |- _ ] =>
              rewrite <- PRED in NOT_TERM;
              compute in NOT_TERM;
              match goal with
              | [ H: true = true -> False |- _ ] =>
                assert(H': true = true); [reflexivity|]; apply H in H'; inversion H'
              | [ |- _ ] =>
                clear BLOCK UNIQ NOT_TERM;
                rename BLOCK' into BLOCK;
                rename PRED into Helem;
                rename prev' into elem
              end
            end
          ])
    |]);
    inversion Einst
  | inversion BLOCK as
      [ header' [header'' _ _ INST]
      | header' prev' elem' _ _ _ PRED NOT_TERM INST _ UNIQ
      ]; apply INST in Einst; inversion Einst
  ].

Ltac bb_succ_inversion_proof bb_headers bb_inversion :=
  intros from to [from' to' term HDR_FROM HDR_TO SUCC];
  apply bb_headers in HDR_TO;
  apply bb_inversion in HDR_FROM;
  repeat destruct HDR_FROM as [HDR_FROM|HDR_FROM];
  repeat destruct HDR_TO as [HDR_TO|HDR_TO];
  destruct HDR_FROM as [Hfrom Htem];
  subst; compute in SUCC;
  try destruct SUCC as [SUCC|SUCC];
  inversion SUCC; auto; repeat (right; auto).

Definition dominator_solution_correct fn doms :=
  Some [fn.(fn_entry)] = doms ! (fn.(fn_entry))
  /\
  forall (n: node),
    BasicBlockHeader fn n ->
      exists (doms_n: list node),
        Some doms_n = doms ! n
        /\
        In n doms_n
        /\
        forall (n': node),
          In n' doms_n ->
            n = n'
            \/
            forall (pred: node),
              BasicBlockSucc fn pred n ->
                exists (doms_pred: list node),
                  Some doms_pred = doms ! pred
                  /\
                  In n' doms_pred.

Ltac dominator_solution_proof fn solution func_bb_headers func_bb_succ_inversion :=
  split; [ compute; reflexivity | ];
  intros n Hbb;
  apply func_bb_headers in Hbb;
  repeat destruct Hbb as [Hbb|Hbb];
    remember (solution ! n) as some_doms_n eqn:Edoms_n;
    compute in Edoms_n; subst n;
    match goal with
    | [ H: some_doms_n = Some ?doms_n |- _ ] => exists doms_n
    end;
    (repeat split; [auto|compute; auto|]);
    intros n' Hin;
    repeat destruct Hin as [Hin|Hin]; auto;
    right;
    intros pred Hpred;
    apply func_bb_succ_inversion in Hpred;
    repeat destruct Hpred as [Hpred|Hpred];
    destruct Hpred as [Hl Hr];
    try inversion Hr;
    remember (solution ! pred) as some_doms_pred eqn:Edoms_pred;
    rewrite <- Hl in Edoms_pred;
    compute in Edoms_pred;
    match goal with
    | [ H: some_doms_pred = Some ?doms_n |- _ ] => exists doms_n
    end;
    subst some_doms_pred; (split; [reflexivity|]); subst; simpl; auto.

Definition dominator_solution_dom fn doms :=
  forall (n: node) (m: node),
    BasicBlockHeader fn n ->
    BasicBlockHeader fn m ->
    (exists (doms_n: list node), Some doms_n = doms ! n /\ In m doms_n) ->
    BasicBlockDominates fn m n.

Theorem correct_implies_dom:
  forall (f: func) (sol: PTrie.t (list node)),
    dominator_solution_correct f sol -> dominator_solution_dom f sol.
Proof.
  intros f sol Hcorrect n m Hbbn Hbbm Hin.
  destruct Hcorrect as [Hentry Hheaders].
  apply bb_dom_path.
  {
    intros path Hpath.
    remember (entry f) as entry.
    induction Hpath.
    {
      generalize (Hheaders n Hbbn).
      intros [doms_n' [Hdoms_n' [Hin' Hpred]]].
      destruct Hin as [doms_n [Hdoms_n Hin]].
      rewrite <- Hdoms_n' in Hdoms_n.
      inversion Hdoms_n.
      subst n doms_n'.
      unfold entry in *.
      inversion Hentry as [Hentry_explicit].
      rewrite <- Hdoms_n' in Hentry_explicit.
      inversion Hentry_explicit as [Hdoms_n_explicit].
      subst doms_n.
      intuition.
    }
    {
      assert (Hbb_next: BasicBlockHeader f next).
      {
        inversion HD.
        apply bb_has_header with (elem := term).
        apply HDR_FROM.
      }
      destruct (Pos.eq_dec to m) as [Eeq|Ene]. left. auto.
      right. apply IHHpath; auto.
      {
        destruct Hin as [doms_n' [Hdoms_n' Hin_m_doms_n]].
        generalize (Hheaders to Hbbn). intros Hdoms_next.
        destruct Hdoms_next as [doms_next [Hdoms_next [Hin_next Hpred_next]]].
        rewrite <- Hdoms_next in Hdoms_n'.
        inversion Hdoms_n'. subst doms_n'.

        generalize (Hpred_next m Hin_m_doms_n). intros Hm.
        destruct Hm. contradiction.

        generalize (H next HD). intros Hpred.
        destruct Hpred as [doms_pred [Hdoms_pred Hin_pred]].
        exists doms_pred. split; auto.
      }
    }
  }
  {
    inversion Hbbn. apply REACH.
  }
Qed.
