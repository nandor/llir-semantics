Require Import Coq.ZArith.ZArith.
Require Import LLIR.LLIR.
Require Import LLIR.Maps.
Require Import LLIR.Values.
Require Import LLIR.Verify.
Require Import LLIR.State.
Require Import LLIR.Export.
Require Import LLIR.Dom.
Require Import Coq.Lists.List.
Import ListNotations.

Definition fib: func := 
  {| fn_stack :=
    << >>
  ; fn_insts :=
    << (1%positive, LLArg 0 1%positive 2%positive)
    ;  (2%positive, LLInt32 (((((O, O), (O, O)), ((O, O), (O, O))), (((O, O), (O, O)), ((O, O), (O, O)))), ((((O, O), (O, O)), ((O, O), (O, O))), (((O, O), (O, O)), ((O, O), (O, O))))) 2%positive 3%positive)
    ;  (3%positive, LLInt32 (((((O, O), (O, O)), ((O, O), (O, O))), (((O, O), (O, O)), ((O, O), (O, O)))), ((((O, O), (O, O)), ((O, O), (O, O))), (((O, O), (O, O)), ((O, O), (O, I))))) 3%positive 4%positive)
    ;  (4%positive, LLBinop I8 LLCmp 1%positive 2%positive 4%positive 5%positive)
    ;  (5%positive, LLJcc 4%positive 17%positive 6%positive)
    ;  (6%positive, LLInt32 (((((I, I), (I, I)), ((I, I), (I, I))), (((I, I), (I, I)), ((I, I), (I, I)))), ((((I, I), (I, I)), ((I, I), (I, I))), (((I, I), (I, I)), ((I, I), (I, I))))) 6%positive 7%positive)
    ;  (7%positive, LLInt32 (((((O, O), (O, O)), ((O, O), (O, O))), (((O, O), (O, O)), ((O, O), (O, O)))), ((((O, O), (O, O)), ((O, O), (O, O))), (((O, O), (O, O)), ((O, O), (O, O))))) 7%positive 8%positive)
    ;  (8%positive, LLJmp 12%positive)
    ;  (12%positive, LLBinop I32 LLAdd 9%positive 11%positive 12%positive 13%positive)
    ;  (13%positive, LLBinop I32 LLAdd 10%positive 6%positive 13%positive 14%positive)
    ;  (14%positive, LLBinop I8 LLCmp 13%positive 2%positive 14%positive 15%positive)
    ;  (15%positive, LLJcc 14%positive 12%positive 17%positive)
    ;  (17%positive, LLRet 16%positive)
    >>
  ; fn_phis := 
    << (12%positive
       , [ LLPhi
           [ (8%positive, 3%positive)
           ; (15%positive, 12%positive)
           ]
           9%positive
         ; LLPhi
           [ (8%positive, 1%positive)
           ; (15%positive, 13%positive)
           ]
           10%positive
         ; LLPhi
           [ (8%positive, 7%positive)
           ; (15%positive, 9%positive)
           ]
           11%positive
         ]
       )
    ;  (17%positive
       , [ LLPhi
           [ (5%positive, 3%positive)
           ; (15%positive, 12%positive)
           ]
           16%positive
         ]
       )
    >>
  ; fn_entry := 1%positive
  |}.

Theorem fib_inst_inversion:
  forall (inst: option inst) (n: node),
  inst = (fn_insts fib) ! n ->
    (1%positive = n /\ Some (LLArg 0 1%positive 2%positive) = inst)
    \/
    (2%positive = n /\ Some (LLInt32 (((((O, O), (O, O)), ((O, O), (O, O))), (((O, O), (O, O)), ((O, O), (O, O)))), ((((O, O), (O, O)), ((O, O), (O, O))), (((O, O), (O, O)), ((O, O), (O, O))))) 2%positive 3%positive) = inst)
    \/
    (3%positive = n /\ Some (LLInt32 (((((O, O), (O, O)), ((O, O), (O, O))), (((O, O), (O, O)), ((O, O), (O, O)))), ((((O, O), (O, O)), ((O, O), (O, O))), (((O, O), (O, O)), ((O, O), (O, I))))) 3%positive 4%positive) = inst)
    \/
    (4%positive = n /\ Some (LLBinop I8 LLCmp 1%positive 2%positive 4%positive 5%positive) = inst)
    \/
    (5%positive = n /\ Some (LLJcc 4%positive 17%positive 6%positive) = inst)
    \/
    (6%positive = n /\ Some (LLInt32 (((((I, I), (I, I)), ((I, I), (I, I))), (((I, I), (I, I)), ((I, I), (I, I)))), ((((I, I), (I, I)), ((I, I), (I, I))), (((I, I), (I, I)), ((I, I), (I, I))))) 6%positive 7%positive) = inst)
    \/
    (7%positive = n /\ Some (LLInt32 (((((O, O), (O, O)), ((O, O), (O, O))), (((O, O), (O, O)), ((O, O), (O, O)))), ((((O, O), (O, O)), ((O, O), (O, O))), (((O, O), (O, O)), ((O, O), (O, O))))) 7%positive 8%positive) = inst)
    \/
    (8%positive = n /\ Some (LLJmp 12%positive) = inst)
    \/
    (12%positive = n /\ Some (LLBinop I32 LLAdd 9%positive 11%positive 12%positive 13%positive) = inst)
    \/
    (13%positive = n /\ Some (LLBinop I32 LLAdd 10%positive 6%positive 13%positive 14%positive) = inst)
    \/
    (14%positive = n /\ Some (LLBinop I8 LLCmp 13%positive 2%positive 14%positive 15%positive) = inst)
    \/
    (15%positive = n /\ Some (LLJcc 14%positive 12%positive 17%positive) = inst)
    \/
    (17%positive = n /\ Some (LLRet 16%positive) = inst)
    \/
    inst = None.
Proof. inst_inversion_proof fib. Qed.

Theorem fib_phi_inversion:
  forall (phis: option (list phi)) (n: node),
  phis = (fn_phis fib) ! n ->
    (12%positive = n /\ Some [LLPhi [ (8%positive, 3%positive); (15%positive, 12%positive)] 9%positive; LLPhi [ (8%positive, 1%positive); (15%positive, 13%positive)] 10%positive; LLPhi [ (8%positive, 7%positive); (15%positive, 9%positive)] 11%positive] = phis)
    \/
    (17%positive = n /\ Some [LLPhi [ (5%positive, 3%positive); (15%positive, 12%positive)] 16%positive] = phis)
    \/
    phis = None.
Proof. phi_inversion_proof fib. Qed.

Theorem fib_defined_at_inversion:
  forall (n: node) (r: reg),
    DefinedAt fib n r -> 
      (1%positive = n /\ 1%positive = r)
      \/
      (2%positive = n /\ 2%positive = r)
      \/
      (3%positive = n /\ 3%positive = r)
      \/
      (4%positive = n /\ 4%positive = r)
      \/
      (6%positive = n /\ 6%positive = r)
      \/
      (7%positive = n /\ 7%positive = r)
      \/
      (12%positive = n /\ 12%positive = r)
      \/
      (13%positive = n /\ 13%positive = r)
      \/
      (14%positive = n /\ 14%positive = r)
      \/
      (12%positive = n /\ 9%positive = r)
      \/
      (12%positive = n /\ 10%positive = r)
      \/
      (12%positive = n /\ 11%positive = r)
      \/
      (17%positive = n /\ 16%positive = r).
Proof. defined_at_inversion_proof fib fib_inst_inversion fib_phi_inversion. Qed.

Theorem fib_defined_at:
  DefinedAt fib 1%positive 1%positive
  /\
  DefinedAt fib 2%positive 2%positive
  /\
  DefinedAt fib 3%positive 3%positive
  /\
  DefinedAt fib 4%positive 4%positive
  /\
  DefinedAt fib 6%positive 6%positive
  /\
  DefinedAt fib 7%positive 7%positive
  /\
  DefinedAt fib 12%positive 12%positive
  /\
  DefinedAt fib 13%positive 13%positive
  /\
  DefinedAt fib 14%positive 14%positive
  /\
  DefinedAt fib 12%positive 9%positive
  /\
  DefinedAt fib 12%positive 10%positive
  /\
  DefinedAt fib 12%positive 11%positive
  /\
  DefinedAt fib 17%positive 16%positive.
Proof. defined_at_proof fib. Qed.

Theorem fib_used_at_inversion:
  forall (n: node) (r: reg),
    UsedAt fib n r -> 
      (4%positive = n /\ 1%positive = r)
      \/
      (4%positive = n /\ 2%positive = r)
      \/
      (5%positive = n /\ 4%positive = r)
      \/
      (8%positive = n /\ 3%positive = r)
      \/
      (15%positive = n /\ 12%positive = r)
      \/
      (8%positive = n /\ 1%positive = r)
      \/
      (15%positive = n /\ 13%positive = r)
      \/
      (8%positive = n /\ 7%positive = r)
      \/
      (15%positive = n /\ 9%positive = r)
      \/
      (12%positive = n /\ 9%positive = r)
      \/
      (12%positive = n /\ 11%positive = r)
      \/
      (13%positive = n /\ 10%positive = r)
      \/
      (13%positive = n /\ 6%positive = r)
      \/
      (14%positive = n /\ 13%positive = r)
      \/
      (14%positive = n /\ 2%positive = r)
      \/
      (15%positive = n /\ 14%positive = r)
      \/
      (5%positive = n /\ 3%positive = r)
      \/
      (15%positive = n /\ 12%positive = r)
      \/
      (17%positive = n /\ 16%positive = r).
Proof. used_at_inversion_proof fib fib_inst_inversion fib_phi_inversion. Qed.

Theorem fib_bb_headers_inversion: 
  forall (header: node), 
    BasicBlockHeader fib header ->
      1%positive = header
      \/
      6%positive = header
      \/
      12%positive = header
      \/
      17%positive = header.
Proof. bb_headers_inversion_proof fib fib_inst_inversion. Qed.

Theorem fib_bb_headers:
      BasicBlockHeader fib 1%positive
      /\
      BasicBlockHeader fib 6%positive
      /\
      BasicBlockHeader fib 12%positive
      /\
      BasicBlockHeader fib 17%positive.
Admitted.

Theorem fib_bb_inversion: 
  forall (header: node) (elem: node),
    BasicBlock fib header elem ->
      1%positive = header /\ 1%positive = elem
      \/
      1%positive = header /\ 2%positive = elem
      \/
      1%positive = header /\ 3%positive = elem
      \/
      1%positive = header /\ 4%positive = elem
      \/
      1%positive = header /\ 5%positive = elem
      \/
      6%positive = header /\ 6%positive = elem
      \/
      6%positive = header /\ 7%positive = elem
      \/
      6%positive = header /\ 8%positive = elem
      \/
      12%positive = header /\ 12%positive = elem
      \/
      12%positive = header /\ 13%positive = elem
      \/
      12%positive = header /\ 14%positive = elem
      \/
      12%positive = header /\ 15%positive = elem
      \/
      17%positive = header /\ 17%positive = elem.
Proof. bb_inversion_proof fib fib_inst_inversion fib_bb_headers_inversion. Qed.

Theorem fib_bb:
  BasicBlock fib 1%positive 1%positive
  /\
  BasicBlock fib 1%positive 2%positive
  /\
  BasicBlock fib 1%positive 3%positive
  /\
  BasicBlock fib 1%positive 4%positive
  /\
  BasicBlock fib 1%positive 5%positive
  /\
  BasicBlock fib 6%positive 6%positive
  /\
  BasicBlock fib 6%positive 7%positive
  /\
  BasicBlock fib 6%positive 8%positive
  /\
  BasicBlock fib 12%positive 12%positive
  /\
  BasicBlock fib 12%positive 13%positive
  /\
  BasicBlock fib 12%positive 14%positive
  /\
  BasicBlock fib 12%positive 15%positive
  /\
  BasicBlock fib 17%positive 17%positive.
Admitted.

Theorem fib_bb_succ_inversion: 
  forall (from: node) (to: node),
    BasicBlockSucc fib from to ->
      1%positive = from /\ 17%positive = to
      \/
      1%positive = from /\ 6%positive = to
      \/
      6%positive = from /\ 12%positive = to
      \/
      12%positive = from /\ 12%positive = to
      \/
      12%positive = from /\ 17%positive = to.
Proof. bb_succ_inversion_proof fib_bb_headers_inversion fib_bb_inversion. Qed.

Definition fib_dominator_solution := 
  << (12%positive, [1%positive; 6%positive; 12%positive])
  ;  (6%positive, [1%positive; 6%positive])
  ;  (17%positive, [1%positive; 17%positive])
  ;  (1%positive, [1%positive])
  >>.

Theorem fib_dominator_solution_correct: dominator_solution_correct fib fib_dominator_solution.
Proof. dominator_solution_proof fib fib_dominator_solution fib_bb_headers_inversion fib_bb_succ_inversion. Qed.

Theorem fib_defs_are_unique: defs_are_unique fib.
Proof. defs_are_unique_proof fib_defined_at_inversion. Qed.

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
  
Theorem fib_uses_have_defs: uses_have_defs fib.
Proof. uses_have_defs_proof
    fib
    fib_used_at_inversion
    fib_defined_at
    fib_bb
    fib_bb_headers_inversion
    fib_dominator_solution
    fib_dominator_solution_correct. Qed.