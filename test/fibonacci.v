Require Import Coq.ZArith.ZArith.
Require Import LLIR.LLIR.
Require Import LLIR.Maps.
Require Import LLIR.Values.
Require Import LLIR.SSA.
Require Import LLIR.State.
Require Import LLIR.Export.
Require Import LLIR.Dom.
Require Import LLIR.Typing.
Require Import Coq.Lists.List.
Import ListNotations.

Definition fib: func := 
  {| fn_stack :=
    << >>
  ; fn_insts :=
    << (1%positive, LLArg (TInt I32, 1%positive) 2%positive 0)
    ;  (2%positive, LLInt32 2%positive 3%positive (((((O, O), (O, O)), ((O, O), (O, O))), (((O, O), (O, O)), ((O, O), (O, O)))), ((((O, O), (O, O)), ((O, O), (O, O))), (((O, O), (O, O)), ((O, O), (O, O))))))
    ;  (3%positive, LLInt32 3%positive 4%positive (((((O, O), (O, O)), ((O, O), (O, O))), (((O, O), (O, O)), ((O, O), (O, O)))), ((((O, O), (O, O)), ((O, O), (O, O))), (((O, O), (O, O)), ((O, O), (O, I))))))
    ;  (4%positive, LLBinop (TInt I8, 4%positive) 5%positive LLCmp 1%positive 2%positive )
    ;  (5%positive, LLJcc 4%positive 17%positive 6%positive)
    ;  (6%positive, LLInt32 6%positive 7%positive (((((I, I), (I, I)), ((I, I), (I, I))), (((I, I), (I, I)), ((I, I), (I, I)))), ((((I, I), (I, I)), ((I, I), (I, I))), (((I, I), (I, I)), ((I, I), (I, I))))))
    ;  (7%positive, LLInt32 7%positive 8%positive (((((O, O), (O, O)), ((O, O), (O, O))), (((O, O), (O, O)), ((O, O), (O, O)))), ((((O, O), (O, O)), ((O, O), (O, O))), (((O, O), (O, O)), ((O, O), (O, O))))))
    ;  (8%positive, LLJmp 12%positive)
    ;  (12%positive, LLBinop (TInt I32, 12%positive) 13%positive LLAdd 9%positive 11%positive )
    ;  (13%positive, LLBinop (TInt I32, 13%positive) 14%positive LLAdd 10%positive 6%positive )
    ;  (14%positive, LLBinop (TInt I8, 14%positive) 15%positive LLCmp 13%positive 2%positive )
    ;  (15%positive, LLJcc 14%positive 12%positive 17%positive)
    ;  (17%positive, LLRet (Some 16%positive))
    >>
  ; fn_phis := 
    << (12%positive
       , [ LLPhi (TInt I32, 9%positive) [ (8%positive, 3%positive)
           ; (15%positive, 12%positive)
           ]
         ; LLPhi (TInt I32, 10%positive) [ (8%positive, 1%positive)
           ; (15%positive, 13%positive)
           ]
         ; LLPhi (TInt I32, 11%positive) [ (8%positive, 7%positive)
           ; (15%positive, 9%positive)
           ]
         ]
       )
    ;  (17%positive
       , [ LLPhi (TInt I32, 16%positive) [ (5%positive, 3%positive)
           ; (15%positive, 12%positive)
           ]
         ]
       )
    >>
  ; fn_entry := 1%positive
  |}.

Theorem fib_inst_inversion:
  forall (inst: option inst) (n: node),
  inst = (fn_insts fib) ! n ->
    (1%positive = n /\ Some (LLArg (TInt I32, 1%positive) 2%positive 0) = inst)
    \/
    (2%positive = n /\ Some (LLInt32 2%positive 3%positive (((((O, O), (O, O)), ((O, O), (O, O))), (((O, O), (O, O)), ((O, O), (O, O)))), ((((O, O), (O, O)), ((O, O), (O, O))), (((O, O), (O, O)), ((O, O), (O, O)))))) = inst)
    \/
    (3%positive = n /\ Some (LLInt32 3%positive 4%positive (((((O, O), (O, O)), ((O, O), (O, O))), (((O, O), (O, O)), ((O, O), (O, O)))), ((((O, O), (O, O)), ((O, O), (O, O))), (((O, O), (O, O)), ((O, O), (O, I)))))) = inst)
    \/
    (4%positive = n /\ Some (LLBinop (TInt I8, 4%positive) 5%positive LLCmp 1%positive 2%positive ) = inst)
    \/
    (5%positive = n /\ Some (LLJcc 4%positive 17%positive 6%positive) = inst)
    \/
    (6%positive = n /\ Some (LLInt32 6%positive 7%positive (((((I, I), (I, I)), ((I, I), (I, I))), (((I, I), (I, I)), ((I, I), (I, I)))), ((((I, I), (I, I)), ((I, I), (I, I))), (((I, I), (I, I)), ((I, I), (I, I)))))) = inst)
    \/
    (7%positive = n /\ Some (LLInt32 7%positive 8%positive (((((O, O), (O, O)), ((O, O), (O, O))), (((O, O), (O, O)), ((O, O), (O, O)))), ((((O, O), (O, O)), ((O, O), (O, O))), (((O, O), (O, O)), ((O, O), (O, O)))))) = inst)
    \/
    (8%positive = n /\ Some (LLJmp 12%positive) = inst)
    \/
    (12%positive = n /\ Some (LLBinop (TInt I32, 12%positive) 13%positive LLAdd 9%positive 11%positive ) = inst)
    \/
    (13%positive = n /\ Some (LLBinop (TInt I32, 13%positive) 14%positive LLAdd 10%positive 6%positive ) = inst)
    \/
    (14%positive = n /\ Some (LLBinop (TInt I8, 14%positive) 15%positive LLCmp 13%positive 2%positive ) = inst)
    \/
    (15%positive = n /\ Some (LLJcc 14%positive 12%positive 17%positive) = inst)
    \/
    (17%positive = n /\ Some (LLRet (Some 16%positive)) = inst)
    \/
    inst = None.
Proof. inst_inversion_proof fib. Qed.

Theorem fib_phi_inversion:
  forall (phis: option (list phi)) (n: node),
  phis = (fn_phis fib) ! n ->
    (12%positive = n /\ Some [LLPhi (TInt I32, 9%positive) [ (8%positive, 3%positive); (15%positive, 12%positive)]; LLPhi (TInt I32, 10%positive) [ (8%positive, 1%positive); (15%positive, 13%positive)]; LLPhi (TInt I32, 11%positive) [ (8%positive, 7%positive); (15%positive, 9%positive)]] = phis)
    \/
    (17%positive = n /\ Some [LLPhi (TInt I32, 16%positive) [ (5%positive, 3%positive); (15%positive, 12%positive)]] = phis)
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
Proof. defined_at_proof. Qed.

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
Proof. bb_proof fib fib_inst_inversion fib_bb_headers . Qed.

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

Theorem fib_uses_have_defs: uses_have_defs fib.
Proof. uses_have_defs_proof fib fib_used_at_inversion fib_defined_at fib_bb fib_bb_headers_inversion fib_dominator_solution fib_dominator_solution_correct. Qed.

Theorem fib_well_typed: X86_Typing.well_typed fib.
Proof. X86_Proofs.well_typed fib fib_inst_inversion fib_phi_inversion. Qed.

