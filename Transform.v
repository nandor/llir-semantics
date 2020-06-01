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



Definition rewrite_inst_uses (i: inst) (f: reg -> reg): inst :=
  match i with
  | LLLd addr dst next => LLLd (f addr) dst next
  | LLSt addr val next => LLSt (f addr) (f val) next
  | LLArg index dst next => i
  | LLInt8 _ _ _ => i
  | LLInt16 _ _ _ => i
  | LLInt32 _ _ _ => i
  | LLInt64 _ _ _ => i
  | LLFrame object dst next => i
  | LLGlobal object dst next => i
  | LLExtern id next => i
  | LLInvoke t args dst next exn => LLInvoke (f t) (List.map f args) dst next exn
  | LLRet value => LLRet (f value)
  | LLRetVoid => LLRetVoid
  | LLJcc cond bt bf => LLJcc (f cond) bt bf
  | LLJmp target => i
  | LLUndef _ _ _ => i
  | LLUnop ty op arg dst next => LLUnop ty op (f arg) dst next
  | LLBinop ty op lhs rhs dst next => LLBinop ty op (f lhs) (f rhs) dst next
  end.

Theorem inst_use_rewritten:
  forall (i: inst) (r: reg) (f: reg -> reg),
    InstUses i r -> InstUses (rewrite_inst_uses i f) (f r).
Proof.
  destruct i; intros src f Huse; simpl; inversion Huse; try rewrite H; auto.
  right. apply List.in_map_iff. exists src.
  split. reflexivity. apply H.
Qed.

Definition rewrite_phi_uses (p: phi) (f: reg -> reg): phi :=
  match p with
  | LLPhi ins dst => LLPhi (List.map (fun phi_in =>
    match phi_in with
    | (block, r) => (block, f r)
    end) ins) dst
  end.

Theorem phi_use_rewritten:
  forall (p: phi) (n: node) (r: reg) (f: reg -> reg),
    PhiUses p n r -> PhiUses (rewrite_phi_uses p f) n (f r).
Proof.
  destruct p; intros n r f Huse; simpl.
  unfold PhiUses in Huse.
  apply Exists_exists in Huse.
  destruct Huse as [[n' r'] [Hin [Hn Hr]]]. subst n' r'.
  apply Exists_exists.
  exists (n, f r).
  split; auto.
  apply in_map_iff.
  exists (n, r).
  auto.
Qed.
