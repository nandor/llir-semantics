(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.

Require Import LLIR.LLIR.
Require Import LLIR.Maps.
Require Import LLIR.Dom.
Require Import LLIR.Values.
Require Import LLIR.Typing.

Import ListNotations.

Ltac succ_of_proof :=
  match goal with
  | [ |- SuccOf ?fn ?from ?to ] =>
    remember ((fn_insts fn) ! from) as some_inst eqn:Esome_inst;
    compute in Esome_inst;
    match goal with
    | [ H: some_inst = Some ?inst' |- _ ] =>
      remember inst' as inst eqn:Einst;
      apply succ_of with (i := inst); subst inst;
      [ auto
      | intros contra; inversion contra
      | constructor
      ]
    end
  end.

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

Ltac defined_at_inversion_proof fn inst_inversion phi_inversion :=
  intros n r Hdef_at;
  inversion Hdef_at as [n' r' i INST DEFS|n' r' phi PHIS DEFS];
  [
    apply inst_inversion in INST;
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
    apply phi_inversion in PHIS;
    repeat (destruct PHIS as [Hdef|PHIS];
      [
        destruct Hdef as [Hn Hsome_inst];
        inversion Hsome_inst as [Hinst]; clear Hsome_inst;
        rewrite <- Hinst in DEFS;
        apply Exists_exists in DEFS;
        destruct DEFS as [phi' [Hin Hdst]];
        inversion Hdst; subst;
        repeat (destruct Hin as [Hphi|Hin];
          [
            inversion Hphi; subst;
            repeat match goal with
            | [ |- (?n = ?n /\ ?r = ?r) \/ _ ] => left; split; reflexivity
            | [ |- ?n = ?n /\ ?r = ?r ] => split; reflexivity
            | [ |- _ ] => right
            end
          |]);
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
      constructor
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
      split; [unfold In; intuition|constructor]
    end.

Ltac defs_are_unique_proof defined_at_inversion :=
  intros def def' r Hdef Hdef';
  apply defined_at_inversion in Hdef;
  apply defined_at_inversion in Hdef';
  try contradiction;
  repeat destruct Hdef as [Hdef|Hdef];
  repeat destruct Hdef' as [Hdef'|Hdef'];
  destruct Hdef as [Hd Hn];
  destruct Hdef' as [Hd' Hn'];
  subst r def def'; auto; try inversion Hn'.

Ltac used_at_inversion_proof fn inst_inversion phi_inversion :=
  intros n r Hused_at;
  inversion Hused_at as [n' r' i INST USES|n' r' block phis PHIS USES];
  [
    clear Hused_at;
    apply inst_inversion in INST;
    repeat (destruct INST as [[Hn Hinst]|INST];
      [ inversion Hinst; clear Hinst; subst i n n' r'; inversion USES
      |
      ]);
      repeat match goal with
      | [ H: _ = r \/ _ |- _ ] => destruct H
      | [ H: In _ _ |- _ ] => destruct H
      end;
      repeat match goal with
      | [ |- (?n = ?n /\ ?r = ?r) \/ _ ] => left; split; reflexivity
      | [ |- ?n = ?n /\ ?r = ?r ] => split; reflexivity
      | [ |- _ ] => right
      end;
    inversion INST
  |
    clear Hused_at; subst n' r';
    apply phi_inversion in PHIS;
    repeat (destruct PHIS as [[Hb Hphis]|PHIS];
      [ inversion Hphis; subst phis; clear Hphis;
        apply Exists_exists in USES;
        destruct USES as [x [Hin Huses]];
        repeat (destruct Hin as [Hphi|Hin];
          [ subst x;
            inversion Huses as [dst ins n'' r'' Hphi_in Hdst Hn Hr];
            subst n'' r'';
            repeat (destruct Hphi_in as [Hbr|Hphi_in];
              [ inversion Hbr; subst n r
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

Ltac bb_headers_inversion_proof fn inst_inversion :=
  intros header Hbb;
  inversion Hbb as [header'' REACH TERM NODE];
  remember ((fn_insts fn) ! header) as inst eqn:Einst;
  remember (get_predecessors fn header) as pred eqn:Epred;
  apply inst_inversion in Einst;
  repeat (destruct Einst as [[Ehdr Ei]|Einst]; [auto; (
    rewrite <- Ehdr in Epred;
    compute in Epred;
    match goal with
    | [ E: pred = [ ?p ] |- _ ] =>
      remember ((fn_insts fn) ! p) as some_inst' eqn:Esome_inst';
      compute in Esome_inst';
      assert (Hsucc: SuccOf fn p header); [
      match goal with
      | [ E: some_inst' = Some ?inst' |- _ ] =>
        apply succ_of with (i := inst'); subst;
        [ auto
        | compute; intros contra; inversion contra
        | constructor]
      end|];
      subst header; compute; auto;
      apply TERM in Hsucc;
      inversion Hsucc as [i n INST TERMINATOR];
      subst; compute in INST; inversion INST; subst i;
      inversion TERMINATOR
    end)|]);
    contradiction.

Ltac bb_inversion_step bb_headers_inversion :=
  match goal with
  | [ BLOCK: BasicBlock _ _ _ |- _ ] =>
    let HEADER := fresh in
    let UNIQ := fresh in
    let NOT_ENTRY := fresh in
    let NOT_TERM := fresh in
    let NOT_HEADER := fresh in
    let NOT_PREV := fresh in
    let BLOCK' := fresh in
    let INST := fresh in
    let NO_PHI := fresh in
    inversion BLOCK as
      [ header' HEADER
      | header' prev' elem' NOT_HEADER NOT_ENTRY NOT_PREV BLOCK' PRED NOT_TERM INST NO_PHI UNIQ
      ];
      subst;
      [ match goal with
        | [ |- ?n = ?n ] => reflexivity
        | [ H: BasicBlockHeader _ _ |- _ ] =>
          apply bb_headers_inversion in H;
          repeat destruct H as [H|H];
          inversion H
        end
      | apply get_predecessors_correct in PRED;
        compute in PRED;
        repeat destruct PRED as [PRED|PRED]; subst;
        match goal with
        | [ BLOCK: BasicBlock ?fn ?header ?hdr
          , BLOCK': BasicBlock ?fn ?header ?term
          |- ?hdr = ?header
          ] =>
            remember ((fn_insts fn) ! term) as some_t eqn:Esome_t;
            compute in Esome_t;
            match goal with
            | [ H: some_t = Some ?inst |- _ ] =>
              remember inst as t eqn: Et;
              assert (TermAt fn term);
              [ apply term_at with (i := t); subst t; auto; constructor|];
              contradiction
            end
        | [ |- _ ] => idtac
        end;
        try contradiction;
        clear UNIQ NOT_ENTRY NOT_TERM NOT_HEADER NOT_PREV BLOCK INST NO_PHI
      ]
  end.

Ltac bb_inversion_proof fn inst_inversion bb_headers_inversion :=
  intros header elem BLOCK;
  destruct ((fn_insts fn) ! elem) eqn:Einst;
  [ symmetry in Einst;
    apply inst_inversion in Einst;
    repeat destruct Einst as [[Helem _]|Einst];
      repeat match goal with
      | [ H: ?e = elem |- ?n = header /\ ?e = elem ] =>
        split; subst elem; try reflexivity
      | [ H: ?e = elem |- (?n = header /\ ?e = elem) \/ _ ] =>
        left
      | [ H: ?e = elem |- _ ] =>
        right
      | [ H: Some _ = None |- _ ] =>
        inversion H
      end;
      repeat bb_inversion_step bb_headers_inversion
  | inversion BLOCK as
      [ header' [header'' REACH TERM INST]
      | header' prev' elem' NOT_HEADER NOT_ENTRY NOT_PREV BLOCK' PRED NOT_TERM INST
      ]; apply INST in Einst; inversion Einst
  ].

Ltac bb_succ_inversion_proof bb_headers_inversion bb_inversion :=
  intros from to [from' to' term HDR_FROM HDR_TO SUCC];
  apply bb_headers_inversion in HDR_TO;
  apply bb_inversion in HDR_FROM;
  repeat destruct HDR_FROM as [HDR_FROM|HDR_FROM];
  repeat destruct HDR_TO as [HDR_TO|HDR_TO];
  destruct HDR_FROM as [Hfrom Htem];
  inversion SUCC as [n m inst HN HM SUCCEEDS Hn Hm]; subst;
  compute in HN; inversion HN as [Hinst]; clear HN; subst inst;
  inversion SUCCEEDS;
  auto; repeat (right; auto).

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

Ltac dominator_solution_proof
    fn
    solution
    bb_headers_inversion
    func_bb_succ_inversion :=
  split; [ compute; reflexivity | ];
  intros n Hbb;
  apply bb_headers_inversion in Hbb;
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
    try contradiction;
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

Ltac bb_dom_step fn bb_headers_inversion Hbb :=
  match goal with
  | [ |- Dominates _ _ ?node ] =>
    remember (get_predecessors fn node) as preds eqn:Epreds; compute in Epreds;
    match goal with
    | [ H: preds = [?n] |- _ ] =>
      remember n as pred eqn:Epred;
      try rewrite Epred in Hbb;
      try rewrite Epred;
      clear Epreds preds;
      assert (Hsucc: SuccOf fn pred node); [subst pred; succ_of_proof|];
      apply bb_elem_pred in Hbb;
      destruct Hbb as [H|H];
        [ apply bb_headers_inversion in H;
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
    fn
    used_at_inversion
    defined_at
    bb
    bb_headers_inversion
    dominator_solution
    dominator_solution_correct :=
  intros n r Hused_at;
  apply used_at_inversion in Hused_at;
  try contradiction;
  repeat destruct Hused_at as [Hused_at|Hused_at];
  destruct Hused_at as [Hn Hr]; subst n;
  remember defined_at as H eqn:Eh; clear Eh;
  repeat match goal with
  | [ H: DefinedAt _ ?n ?v /\ _ |- exists _, _ ] =>
    destruct H
  | [ Hr: ?v = r, H': DefinedAt _ ?n ?v |- _ ] =>
    exists n; subst r; split; [apply H'|clear H']
  end;
  repeat match goal with
  | [ H: DefinedAt _ _ _ |- _ ] => clear H
  end;
  remember bb as H eqn:Eh; clear Eh;
  repeat match goal with
  | [ H: BasicBlock _ _ _ /\ _ |- Dominates _ _ _ ] =>
    destruct H
  end;
  match goal with
  | [ Hfrom: BasicBlock _ ?header ?from
    , Hto: BasicBlock _ ?header ?to
    |- Dominates _ ?from ?to
    ] =>
    clear Hfrom; repeat bb_dom_step fn bb_headers_inversion Hto
  | [ |- Dominates _ ?n ?n ] =>
    apply dom_self
  | [ HBlock: BasicBlock _ ?b ?e |- Dominates _ ?b ?e ] =>
    apply bb_header_dom_nodes; assumption
  | [ Hfrom: BasicBlock _ ?b ?e, Hto: BasicBlock _ ?b' ?e' |- Dominates _ ?e ?e' ] =>
    apply bb_elem_dom with (h := b) (h' := b'); auto;
    [ intros contra; inversion contra
    | generalize (correct_implies_dom fn dominator_solution dominator_solution_correct);
      intros Hdoms;
      apply bb_has_header in Hfrom;
      apply bb_has_header in Hto;
      remember (dominator_solution ! b') as some_doms_n eqn:Esome_doms_n;
      compute in Esome_doms_n;
      destruct some_doms_n as [doms_n|]; inversion Esome_doms_n;
      generalize (Hdoms b' b doms_n Hto Hfrom Esome_doms_n); intros Hds;
      apply Hds; subst doms_n; unfold In; intuition
    ]
  end.

Ltac bb_proof_step node inst_inversion :=
  remember node as pred eqn:Hpred; try rewrite Hpred;
  apply bb_elem with (prev := pred); subst pred; simpl;
    [ intros contra; inversion contra
    | intros contra; inversion contra
    | intros contra; inversion contra
    |
    | match goal with
      | [ |- SuccOf ?fn ?from _ ] =>
        remember ((fn_insts fn) ! from) as some_inst eqn:Esome_inst;
        compute in Esome_inst;
        match goal with
        | [ H: some_inst = Some ?inst' |- _ ] =>
          remember inst' as inst eqn:Einst;
          apply succ_of with (i := inst); subst;
          [ auto
          | intros contra; inversion contra
          | constructor
          ]
        end
      end
    | intros contra;
      inversion contra as [i n INST TERM];
      compute in INST; inversion INST; subst i;
      inversion TERM
    | intros contra; inversion contra
    | reflexivity
    | intros pred' Hsucc;
      inversion Hsucc as [n m i HN HM SUCC Hn Hm]; subst;
      apply inst_inversion in HN;
      repeat (destruct HN as [[Eprev Ei]|HN];
        [ let H := fresh in
          subst pred'; try reflexivity; inversion Ei as [H]; subst i;
          inversion SUCC
        |]);
      inversion HN
    ].

Ltac bb_proof fn inst_inversion bb_headers :=
 repeat split; repeat
    match goal with
    | [ |- BasicBlock _ ?h ?h ] => apply bb_header; apply bb_headers
    | [ |- BasicBlock ?fn ?h ?e ] =>
      remember (get_predecessors fn e) as preds eqn:Epreds; compute in Epreds;
      match goal with
      | [ H: preds = [?n] |- _ ] =>
        clear H preds;
        bb_proof_step n inst_inversion
      end
   end.

Ltac type_proof env Henv :=
  match goal with
  | |- context [ LLBinop (?t, ?dst) _ ?op ?lhs ?rhs ] =>
    remember (env ! lhs) as tl eqn:El; rewrite Henv in El;
    remember (env ! rhs) as tr eqn:Er; rewrite Henv in Er;
    compute in El; compute in Er;
    match goal with
    | [ El: tl = Some ?tl', Er: tr = Some ?tr' |- _ ] =>
      apply type_binop with (tl := tl') (tr := tr');
      subst; constructor
    end
  | |- context [ LLJcc ?cond _ _ ] =>
    remember (env ! cond) as tc eqn:Econd; rewrite Henv in Econd;
    compute in Econd;
    match goal with
    | [ Econd: tc = Some (TInt ?tc') |- _ ] =>
      apply type_jcc with (i := tc')
    end;
    subst; constructor
  | |- context [ LLRet (Some ?v) ] =>
    remember (env ! v) as tv eqn:Ev; rewrite Henv in Ev;
    compute in Ev;
    match goal with
    | [ El: tv = Some ?tv' |- _ ] =>
      apply type_ret with (t := tv')
    end;
    subst; constructor
  | |- context [ LLSt _ ?a ?v ] =>
    remember (env ! v) as tv eqn:Ev; rewrite Henv in Ev;
    compute in Ev;
    match goal with
    | [ Ev: tv = Some ?tv' |- _ ] =>
      apply type_st with (t := tv')
    end;
    subst; constructor
  | |- context [ LLUnop (?t, ?dst) _ ?op ?arg ] =>
    remember (env ! arg) as ta eqn:Ea; rewrite Henv in Ea;
    compute in Ea;
    match goal with
    | [ El: ta = Some ?ta' |- _ ] =>
      apply type_unop with (argt := ta')
    end;
    subst; constructor
  | |- context [ LLSyscall ?dst _ ?sno _ ] =>
    remember (env ! dst) as td eqn:Ed; rewrite Henv in Ed;
    remember (env ! sno) as ts eqn:Es; rewrite Henv in Es;
    compute in Es; compute in Ed;
    match goal with
    | [ El: ts = Some (TInt ?ts'), Ed: td = Some ?td' |- _ ] =>
      apply type_syscall with (t := td') (tsno := ts')
    end;
    subst; constructor
  end.

Ltac well_typed_insts fn inst_inversion :=
  intros n i Hin;
  apply inst_inversion in Hin;
  remember (ty_env fn) as env eqn:Henv;
  repeat (destruct Hin as [[Hn Hi]|Hin];
    [ inversion Hi as [Hi'];
      try (constructor; subst env; constructor)
    |]);
    try type_proof env Henv;
  inversion Hin.

Ltac well_typed_phis fn phi_inversion :=
  intros n i phi Hblocks Hin;
  remember (ty_env fn) as env eqn:Henv;
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

Ltac well_typed_func_proof fn inst_inversion phi_inversion :=
  split;
    [ well_typed_insts fn inst_inversion
    | well_typed_phis fn phi_inversion
    ].
