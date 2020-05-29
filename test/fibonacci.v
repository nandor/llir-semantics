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

Theorem fib_inversion:
  forall (inst: option inst) (n: node),
  (fn_insts fib) ! n = inst ->
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
Proof. inversion_proof fib. Qed.

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
      (14%positive = n /\ 14%positive = r).
Proof. defined_at_proof fib_inversion fib. Qed.

Theorem fib_used_at_inversion:
  forall (n: node) (r: reg),
    UsedAt fib n r -> 
      (4%positive = n /\ 1%positive = r)
      \/
      (4%positive = n /\ 2%positive = r)
      \/
      (5%positive = n /\ 4%positive = r)
      \/
      (9%positive = n /\ 3%positive = r)
      \/
      (9%positive = n /\ 12%positive = r)
      \/
      (10%positive = n /\ 1%positive = r)
      \/
      (10%positive = n /\ 13%positive = r)
      \/
      (11%positive = n /\ 7%positive = r)
      \/
      (11%positive = n /\ 9%positive = r)
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
      (16%positive = n /\ 3%positive = r)
      \/
      (16%positive = n /\ 12%positive = r)
      \/
      (17%positive = n /\ 16%positive = r).
Proof. used_at_inversion_proof fib fib_inversion. Qed.

Theorem fib_defs_are_unique: defs_are_unique fib.
Proof. defs_are_unique_proof fib_defined_at_inversion. Qed.

Theorem fib_bb_headers: 
  forall (header: node), 
    BlockHeader fib header ->
      1%positive = header
      \/
      6%positive = header
      \/
      12%positive = header
      \/
      17%positive = header.
Proof. bb_headers_proof fib fib_inversion. Qed.

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
Proof. bb_inversion_proof fib fib_inversion fib_bb_headers. Qed.

Definition fib_dominator_solution := 
  << (12%positive, [1%positive; 6%positive; 12%positive])
  ;  (6%positive, [1%positive; 6%positive])
  ;  (17%positive, [1%positive; 17%positive])
  ;  (1%positive, [1%positive])
  >>.

