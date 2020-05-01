(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.PArith.PArith.
Require Import Coq.Lists.List.

Require Import LLIR.Maps.
Require Import LLIR.State.
Require Import LLIR.Aliasing.
Require Import LLIR.LLIR.
Require Import LLIR.Verify.



Definition rewrite_uses (i: inst) (f: reg -> reg): inst :=
  match i with
  | LLLd addr dst next => LLLd (f addr) dst next
  | LLSt addr val next => LLSt (f addr) (f val) next
  | LLArg index dst next => i
  | LLConst value dst next => i
  | LLFrame object dst next => i
  | LLGlobal object dst next => i
  | LLExtern id next => i
  | LLInvoke t args dst next exn => LLInvoke (f t) (List.map f args) dst next exn
  | LLRet value => LLRet (f value)
  | LLJcc cond bt bf => LLJcc (f cond) bt bf
  | LLJmp target => i
  | LLUnop op arg dst next => LLUnop op (f arg) dst next
  | LLBinop op lhs rhs dst next => LLBinop op (f lhs) (f rhs) dst next
  end.


Theorem use_rewritten:
  forall (i: inst) (src: reg) (f: reg -> reg),
    Uses i src -> Uses (rewrite_uses i f) (f src).
Proof.
  destruct i; intros src f Huse; simpl; inversion Huse; try rewrite H; auto.
  right. apply List.in_map_iff. exists src.
  split. reflexivity. apply H. 
Qed.
