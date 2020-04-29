(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Nat.

Require Import LLIR.State.
Require Import LLIR.LLIR.



Fixpoint step (p: prog) (st: state) (tr: trace): (state * trace) :=
  (st, tr).

(*
Inductive star : prog -> state -> state -> Prop :=
  | star_refl :
    forall (p: prog) (s: state),
    star p s s
  | star_step :
    forall (p: prog) (s: state) (s': state) (s'': state),
    star p s s' ->
    step p s' = s'' ->
    star p s s''
  .

Inductive starN : nat -> prog -> state -> state -> Prop :=
  | starN_refl :
    forall (p: prog) (s: state),
    starN 0 p s s
  | starN_step :
    forall (n: nat) (p: prog) (s: state) (s': state) (s'': state),
    starN n p s s' ->
    step p s' = s'' ->
    starN (S n) p s s''
  .

Remark starN_star :
  forall p s s',
  (exists n, starN n p s s') -> star p s s'.
Proof.
  intros p s s'.
  intros H.
  destruct H.
  induction H.
  - constructor.
  - apply (star_step p s s').
    + apply IHstarN.
    + apply H0.
Qed.

Remark star_starN :
  forall p s s',
  star p s s' -> exists n, starN n p s s'.
Proof.
  intros p s s'.
  intros H.
  induction H.
  - exists 0. constructor.
  - destruct IHstar.
    exists (S x).
    apply (starN_step x p s s').
    + apply H1.
    + apply H0.
Qed.
*)
