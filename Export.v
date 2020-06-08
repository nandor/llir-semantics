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
Require Import LLIR.Typing.

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

Ltac defined_at_proof :=
  repeat split; match goal with
    | [ |- DefinedAt ?fn ?n ?n ] =>
      remember ((fn_insts fn) ! n) as some_inst eqn:Esome_inst;
      compute in Esome_inst;
      destruct some_inst as [inst|];
      inversion Esome_inst as [Einst];
      clear Esome_inst;
      apply defined_at_inst with (i := inst); rewrite Einst; auto;
      unfold InstDefs; auto
    | [ |- DefinedAt ?fn ?n _ ] =>
      remember ((fn_phis fn) ! n) as some_phis eqn:Esome_phis;
      compute in Esome_phis;
      destruct some_phis as [phis|];
      inversion Esome_phis as [Ephis];
      clear Esome_phis;
      apply defined_at_phi with (phis := phis); rewrite Ephis; auto;
      apply Exists_exists;
      match goal with
      | [ HPhi: context [ LLPhi (?ty, ?reg) ?ins ] |- context [ PhiDefs _ ?reg] ] =>
        exists (LLPhi (ty, reg) ins)
      end;
      split; [unfold In|unfold PhiDefs]; intuition
    end.

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

Ltac bb_headers_inversion_proof fn func_inversion :=
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
  forall (n: node) (m: node) (doms_n: list node),
    BasicBlockHeader fn n ->
    BasicBlockHeader fn m ->
    Some doms_n = doms ! n ->
    In m doms_n ->
    BasicBlockDominates fn m n.

Theorem correct_implies_dom:
  forall (f: func) (sol: PTrie.t (list node)),
    dominator_solution_correct f sol -> dominator_solution_dom f sol.
Proof.
  intros f sol Hcorrect n m doms_n Hbbn Hbbm Hsome_sol Hin.
  destruct Hcorrect as [Hentry Hheaders].
  apply bb_dom_path.
  {
    intros path Hpath.
    remember (entry f) as entry.
    generalize dependent doms_n.
    induction Hpath; intros doms_n Hdoms_n Hin.
    {
      subst. unfold entry in *.
      rewrite <- Hentry in Hdoms_n.
      inversion Hdoms_n. subst doms_n.
      apply Hin.
    }
    {
      assert (Hbb_next: BasicBlockHeader f next).
      {
        inversion HD.
        apply bb_has_header with (elem := term).
        apply HDR_FROM.
      }
      destruct (Pos.eq_dec to m) as [Eeq|Ene]. left. auto.
      right.
      generalize (Hheaders next Hbb_next). intros Hprev.
      destruct Hprev as [doms_n' [Hdoms_n' [Hin' Hprev']]].
      apply IHHpath with (doms_n := doms_n'); auto.
      {
        generalize (Hheaders to Hbbn). intros Hdoms_next.
        destruct Hdoms_next as [doms_next [Hdoms_next [Hin_next Hpred_next]]].
        rewrite <- Hdoms_next in Hdoms_n.
        inversion Hdoms_n. subst doms_n.
        generalize (Hpred_next m Hin). intros Hm.
        destruct Hm. contradiction.
        generalize (H next HD). intros Hpred.
        destruct Hpred as [doms_pred [Hdoms_pred Hin_pred]].
        rewrite <- Hdoms_n' in Hdoms_pred.
        inversion Hdoms_pred.
        subst doms_pred.
        auto.
      }
    }
  }
  {
    inversion Hbbn. apply REACH.
  }
Qed.

Ltac bb_dom_step func func_bb_headers Hbb :=
  match goal with
  | [ |- Dominates _ _ ?node ] =>
    remember (get_predecessors func node) as preds eqn:Epreds; compute in Epreds;
    match goal with
    | [ H: preds = [?n] |- _ ] =>
      remember n as pred eqn:Epred;
      try rewrite Epred in Hbb;
      try rewrite Epred;
      clear Epreds preds;
      assert (Hsucc: SuccOf func pred node); [subst pred; compute; reflexivity|];
      apply bb_elem_pred in Hbb;
      destruct Hbb as [H|H];
        [ apply func_bb_headers in H;
          repeat destruct H as [H|H];
          inversion H
        | generalize (H pred Hsucc); intros Hinv;
          match goal with
          | [ H: pred = ?h |- Dominates _ ?h _ ] =>
            clear Epreds Hsucc;
            subst pred;
            destruct Hinv as [_ Hdom]; auto
          | [ |- _ ] =>
            destruct Hinv as [Hbb Hdom];
            apply dom_trans with (m := pred); subst pred; auto;
            clear Hsucc Hdom H
          end
        ]
    end
  end.

Ltac uses_have_defs_proof
    func
    func_used_at_inversion
    func_defined_at
    func_bb
    func_bb_headers_inversion
    func_dominator_solution
    func_dominator_solution_correct :=
  intros n r Hused_at;
  apply func_used_at_inversion in Hused_at;
  repeat destruct Hused_at as [Hused_at|Hused_at];
  destruct Hused_at as [Hn Hr]; subst n;
  remember func_defined_at as H eqn:Eh; clear Eh;
  repeat match goal with
  | [ H: DefinedAt _ ?n ?v /\ _ |- exists _, _ ] =>
    destruct H as [H' H]
  | [ Hr: ?v = r, H': DefinedAt _ ?n ?v |- _ ] =>
    exists n; subst r; split; [apply H'|clear H']; try clear H
  | [ H: DefinedAt _ _ _ |- exists _, _ ] => clear H
  end;
  remember func_bb as H eqn:Eh; clear Eh;
  repeat match goal with
  | [ H: BasicBlock _ ?header ?node /\ _ |- Dominates _ ?node _ ] =>
    destruct H as [Hfrom H]
  | [ H: BasicBlock _ ?header ?node |- Dominates _ ?node _ ] =>
    destruct H as [Hfrom H]

  | [ H: BasicBlock _ ?header ?node /\ _ |- Dominates _ _ ?node ] =>
    destruct H as [Hto H]
  | [ H: BasicBlock _ ?header ?node |- Dominates _ _ ?node ] =>
    destruct H as [Hto H]

  | [ H: BasicBlock _ _ _ /\ _ |- Dominates _ _ ?node ] =>
    destruct H as [_ H]
  end;
  try clear H; match goal with
  | [ Hfrom: BasicBlock _ ?header ?from, Hto: BasicBlock _ ?header ?to |- _ ] =>
    clear Hfrom; repeat bb_dom_step func func_bb_headers_inversion Hto
  | [ |- Dominates _ ?n ?n ] =>
    apply dom_self
  | [ Hfrom: BasicBlock _ ?b ?e, Hto: BasicBlock _ ?b' ?e' |- Dominates _ ?e ?e' ] =>
    apply bb_elem_dom with (h := b) (h' := b'); auto;
    [ intros contra; inversion contra
    | generalize (correct_implies_dom func func_dominator_solution func_dominator_solution_correct);
      intros Hdoms;
      apply bb_has_header in Hfrom;
      apply bb_has_header in Hto;
      remember (func_dominator_solution ! b') as some_doms_n eqn:Esome_doms_n;
      compute in Esome_doms_n;
      destruct some_doms_n as [doms_n|]; inversion Esome_doms_n;
      generalize (Hdoms b' b doms_n Hto Hfrom Esome_doms_n); intros Hds;
      apply Hds; subst doms_n; unfold In; intuition
    ]
  end.

Ltac bb_proof func func_inst_inversion func_bb_headers :=
  repeat split;
  repeat match goal with
  | [ |- BasicBlock _ ?h ?h ] => apply bb_header; apply func_bb_headers
  | [ |- BasicBlock _ ?h ?e ] =>
    remember (get_predecessors func e) as preds eqn:Epreds; compute in Epreds;
    match goal with
    | [ H: preds = [?n] |- _ ] =>
      remember n as pred eqn:Hpred; try rewrite Hpred; clear Epreds preds;
      apply bb_elem with (prev := pred); subst pred;
      simpl;
      match goal with
      | [ |- forall _, _ ] =>
        intros pred' Hsucc; unfold SuccOf in Hsucc;
        remember ((fn_insts func) ! pred') as inst eqn:Einst;
        apply func_inst_inversion in Einst;
        repeat (destruct Einst as [[Eprev Ei]|Einst];
          [ subst inst pred'; compute in Hsucc;
            repeat destruct Hsucc as [Hsucc|Hsucc];
            try reflexivity; try inversion Hsucc
          |]);
          subst inst; inversion Hsucc
      | [ |- ?a <> ?b ] =>
        intros contra; inversion contra
      | [ |- ~ TermAt _ _ ] =>
        compute; intros contra; inversion contra
      | [ |- SuccOf _ _ _ ] =>
        compute; reflexivity
      | [ |- None = None ] =>
        reflexivity
      | [ |- _ ] =>
        idtac
      end
    end
  end.

Module X86_Proofs.
  Ltac well_typed_insts fn insts_inversion :=
    intros n i Hin;
    apply insts_inversion in Hin;
    remember (X86_Typing.ty_env fn) as env eqn:Henv;
    repeat (destruct Hin as [[Hn Hi]|Hin];
      [ inversion Hi as [Hi'];
        try (constructor; subst env; constructor)
      |]);
      try match goal with
      | |- context [ LLBinop (?t, ?dst) _ ?op ?lhs ?rhs ] =>
        remember (env ! lhs) as tl eqn:El; rewrite Henv in El;
        remember (env ! rhs) as tr eqn:Er; rewrite Henv in Er;
        compute in El; compute in Er;
        match goal with
        | [ El: tl = Some ?tl', Er: tr = Some ?tr' |- _ ] =>
          apply X86_Typing.type_binop with (tl := tl') (tr := tr');
          subst; constructor
        end
      | |- context [ LLJcc ?cond _ _ ] =>
        remember (env ! cond) as tc eqn:Econd; rewrite Henv in Econd;
        compute in Econd;
        match goal with
        | [ Econd: tc = Some (TInt ?tc') |- _ ] =>
          apply X86_Typing.type_jcc with (i := tc')
        end;
        subst; constructor
      | |- context [ LLRet (Some ?v) ] =>
        remember (env ! v) as tv eqn:Ev; rewrite Henv in Ev;
        compute in Ev;
        match goal with
        | [ El: tv = Some ?tv' |- _ ] =>
          apply X86_Typing.type_ret with (t := tv')
        end;
        subst; constructor
      end;
    inversion Hin.

  Ltac well_typed_phis fn phi_inversion :=
    intros n i phi Hblocks Hin;
    remember (X86_Typing.ty_env fn) as env eqn:Henv;
    apply phi_inversion in Hblocks;
    repeat (destruct Hblocks as [[Hn Hphis]|Hblocks];
      [ inversion Hphis as [Hphis']; subst i; clear Hphis;
        repeat (destruct Hin as [Hphi|Hin];
          [ subst phi; constructor;
            intros n' r H;
            repeat destruct H as [H|H]; inversion H; subst; constructor
          |]);
        inversion Hin
      |]);
    inversion Hblocks.

  Ltac well_typed fn insts_inversion phi_inversion :=
    split;
      [ well_typed_insts fn insts_inversion
      | well_typed_phis fn phi_inversion
      ].
End X86_Proofs.
