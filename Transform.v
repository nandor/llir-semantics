(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.PArith.PArith.
Require Import Coq.Lists.List.

Require Import LLIR.Maps.
Require Import LLIR.Aliasing.
Require Import LLIR.LLIR.



Definition rewrite_inst_uses (i: inst) (f: reg -> reg): inst :=
  match i with
  | LLTrap => i
  | LLArg _ _ _ => i
  | LLInt8 _ _ _ => i
  | LLInt16 _ _ _ => i
  | LLInt32 _ _ _ => i
  | LLInt64 _ _ _ => i
  | LLJmp _ => i
  | LLUndef _ _ => i
  | LLFrame _ _ _ _ => i
  | LLGlobal _ _ _ _ _ => i
  | LLFunc _ _ _ => i
  | LLMov dst next src =>
    LLMov dst next (f src)
  | LLLd dst next addr =>
    LLLd dst next (f addr)
  | LLSt next addr val =>
    LLSt next (f addr) (f val)
  | LLSyscall dst next sno args =>
    LLSyscall dst next (f sno) (List.map f args)
  | LLCall dst next callee args =>
    LLCall dst next (f callee) (List.map f args)
  | LLInvoke dst next callee args exn =>
    LLInvoke dst next (f callee) (List.map f args) exn
  | LLTCall callee args =>
    LLTCall (f callee) (List.map f args)
  | LLTInvoke callee args exn =>
    LLTInvoke (f callee) (List.map f args) exn
  | LLRet value =>
    LLRet (option_map f value)
  | LLJcc cond bt bf =>
    LLJcc (f cond) bt bf
  | LLUnop dst next op arg =>
    LLUnop dst next op (f arg)
  | LLBinop dst next op lhs rhs =>
    LLBinop dst next op (f lhs) (f rhs)
  | LLSelect dst next cond vt vf =>
    LLSelect dst next (f cond) (f vt) (f vf)
  end.

Theorem inst_use_rewritten:
  forall (i: inst) (r: reg) (f: reg -> reg),
    InstUses i r -> InstUses (rewrite_inst_uses i f) (f r).
Proof.
  destruct i; intros r f Huse; simpl; inversion Huse; constructor;
  apply in_map_iff; exists r; auto.
Qed.

Definition rewrite_phi_uses (p: phi) (f: reg -> reg): phi :=
  match p with
  | LLPhi dst ins => LLPhi dst (List.map (fun phi_in =>
    match phi_in with
    | (block, r) => (block, f r)
    end) ins)
  end.

Theorem phi_use_rewritten:
  forall (p: phi) (n: node) (r: reg) (f: reg -> reg),
    PhiUses p n r -> PhiUses (rewrite_phi_uses p f) n (f r).
Proof.
  destruct p; intros n r f Huse; simpl.
  inversion Huse; constructor.
  apply in_map_iff.
  exists (n, r).
  auto.
Qed.
