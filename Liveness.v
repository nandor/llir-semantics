(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import LLIR.LLIR.
Require Import LLIR.Dom.


Inductive LiveAt: func -> reg -> node -> Prop :=
  | live_at:
    forall
      (f: func) (r: reg) (n: node) (use: node) (p: list node)
      (PATH: ReversePath f n p use)
      (NO_DEF: forall (def: node), In def (tl p) -> ~DefinedAt f def r)
      (USE: UsedAt f use r),
      LiveAt f r n.

Theorem live_at_succ:
  forall (f: func) (r: reg) (n: node),
    LiveAt f r n ->
    UsedAt f n r
    \/
    exists (s: node), SuccOf f n s /\ LiveAt f r s.
Proof.
  intros f r n Hlive; inversion Hlive; subst.
  inversion PATH; subst.
  { left; auto. }
  {
    right; exists next; split; auto.
    apply live_at with use p0; auto.
    intros def Hin.
    destruct p0; [inversion Hin|].
    simpl in NO_DEF; simpl in Hin.
    apply NO_DEF; right; assumption.
  }
Qed.
