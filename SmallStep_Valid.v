(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Require Import LLIR.Values.
Require Import LLIR.Maps.
Require Import LLIR.LLIR.
Require Import LLIR.Dom.
Require Import LLIR.Eval.
Require Import LLIR.SSA.
Require Import LLIR.Block.
Require Import LLIR.Typing.
Require Import LLIR.Signal.
Require Import LLIR.Liveness.
Require Import LLIR.Syscall.
Require Import LLIR.Frame.
Require Import LLIR.State.
Require Import LLIR.SmallStep.

Import ListNotations.



Theorem small_step_valid:
  forall (p: prog) (st: estate) (st': estate) (tr: trace),
    WellTypedProg p ->
    valid_prog p ->
    Normal p st ->
    step p st tr st' ->
    ~Final st' ->
    Normal p st'.
(*
Proof.
  intros p st st' tr Hwt Hvp Hnormal Hstep Hnf;
    inversion Hnormal; clear Hnormal; subst p0;
    inversion Hstep; clear Hstep; subst tr;
    inversion EXEC; inversion FR; inversion VALID;
    subst p0 p1 p2 fr2 frames1 fr_id1 f0 fr0;
    try (
      rewrite <- H in H0; rewrite <- H3 in H0; inversion H0; clear H0;
      subst h0 init0 frames0 next1 frs0 fr_id0;
      rewrite <- FRAME in FRAME0; inversion FRAME0; clear FRAME0; subst fr1;
      rewrite <- FUNC in FUNC0; inversion FUNC0; clear FUNC0; subst f1
    );
    (
      assert (Hvalid_func: valid_func f);
      [ unfold valid_prog in Hvp; apply Hvp with (fr_func fr); auto |]
    );
    try match goal with
    | [ H: context [ stk_set_pc _ ?next ] |- _ ] => 
      assert (Hsucc: SuccOf f pc next);
        [ apply ((fn_succs_are_valid f Hvalid_func) pc next i); 
          subst;
          auto;
          constructor 
        |]
    end;
    subst pc.
  {
    destruct ((fn_insts f) ! next0) as [inext|] eqn:Einext; [|contradiction].
    constructor; auto.
    {
      apply valid_top_frame with (fr := set_pc fr next0).
      {
        rewrite PTrie.update_eq; simpl.
        rewrite <- FRAME; simpl.
        reflexivity.
      }
      {
        apply valid_frame with f inext; 
        unfold stk_set_pc; unfold set_pc; simpl; auto.
        apply reach_succ with (a := fr_pc fr); auto.
        intros r Hlive.
        
      }
    }
    {
    }
  }
Qed.
*)
Admitted.