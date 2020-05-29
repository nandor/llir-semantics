(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Require Import LLIR.LLIR.
Require Import LLIR.Maps.
Require Import LLIR.Dom.
Require Import LLIR.State.

Import ListNotations.


Ltac inversion_proof fn :=
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

Ltac defined_at_proof inv fn :=
  intros n r Hdef_at;
  unfold DefinedAt in *;
  unfold Defs in *;
  destruct ((fn_insts fn) ! n) eqn:Edef; try inversion Hdef_at;
  apply inv in Edef;
  repeat (destruct Edef as [Hdef|Edef]; try destruct Hdef as [Hi Hinst];
    [ try left;
      inversion Hinst as [Hinst_i]; rewrite <- Hinst_i in *;
      match goal with
      | [ Hi: ?v = n |- context [ ?v = n ] ] =>
        subst r; subst n; auto
      | [ H: False |- _ ] =>
        inversion H
      end
    | match goal with
      | [ H: context [ ?v = n ] |- (?v = n /\ _) \/ _ ] =>
        auto
      | _ =>
        try right
      end
    ]);
  inversion Edef.

Ltac defs_are_unique_proof inv :=
  intros def def' r Hdef Hdef';
  apply inv in Hdef;
  apply inv in Hdef';
  repeat destruct Hdef as [Hd|Hdef]; repeat destruct Hdef' as [Hd'|Hdef'];
  repeat match goal with
  | [ H: ?v = ?def /\ ?v = r |- _ ] => destruct H; subst def
  | [ |- ?v = ?v ] => reflexivity
  | [ |- _ ] => subst r; auto
  end.

Ltac used_at_inversion_proof fn inv :=
  intros n r Hused_at;
  unfold UsedAt in *;
  unfold Uses in *;
  destruct ((fn_insts fn) ! n) eqn:Edef; try inversion Hused_at;
  apply inv in Edef;
  repeat match goal with
  | [ H: ?v = n /\ Some ?inst = Some ?name |- _ ] =>
    destruct H as [Hn Hinst];
    inversion Hinst;
    subst name
  | [ H: False |- _ ] => inversion H
  | [ H: ?a \/ ?b |- _ ] => destruct H
  end;
  match goal with
  | [ Hn: ?vn = n, Hr: ?vr = r |- _] =>
    assert (Hcase: vn = n /\ vr = r); [ split; [apply Hn|apply Hr] |]
  | [ |- _ ] => simpl
  end;
  repeat match goal with
  | [ H: ?vn = n /\ ?vr = r |- (?vn = n /\ ?vr = r) \/ _ ] => left; apply H
  | [ H: ?vn = n /\ ?vr = r |- (?vn = n /\ ?vr = r) ] => apply H
  | [ |- _ ] => right
  end;
  inversion H.

Ltac reach_pred_step func pred :=
  apply reach_succ with (a := pred);
  [
    unfold SuccOf;
    simpl;
    auto
  |
  ].

Ltac block_elem_proof func func_inv p proof_prev :=
  apply bb_elem with (prev := p);
  [ intro contra; inversion contra
  | intro contra; inversion contra
  | apply proof_prev
  | compute; reflexivity
  | compute; intro contra; inversion contra
  | auto
  | intros prev' Hsucc;
    unfold SuccOf in Hsucc; unfold Succeeds in Hsucc;
    remember ((fn_insts func) ! prev') as inst eqn:Hinst;
    symmetry in Hinst;
    apply func_inv in Hinst;
    repeat destruct Hinst as [[Hl Hr]|Hinst]; subst inst; auto; try inversion Hsucc; try inversion H
  ].

Ltac block_header_proof func func_inv bb_reach :=
  apply block_header;
  [ apply bb_reach
  | intros term Hsucc;
    unfold SuccOf in Hsucc; unfold Succeeds in Hsucc; unfold TermAt;
    remember ((fn_insts func) ! term) as inst eqn:H;
    symmetry in H;
    apply func_inv in H;
    repeat destruct H as [[Hl Hr]|H];
      subst inst; try subst term; simpl; auto;
      inversion Hsucc; inversion H
  | intros contra; inversion contra
  ].

Ltac bb_headers_proof func func_inversion :=
  intros header Hbb;
  inversion Hbb as [header'' REACH TERM NODE];
  remember ((fn_insts func) ! header) as inst eqn:Einst;
  remember (get_predecessors func header) as pred eqn:Epred;
  symmetry in Einst;
  apply func_inversion in Einst;
  repeat (destruct Einst as [[Ehdr Ei]|Einst]; [auto; (
    rewrite <- Ehdr in Epred;
    compute in Epred;
    match goal with
    | [ E: pred = [ ?p ] |- _ ] =>
      assert (Hsucc: SuccOf func p header);
      subst header;
      compute;
      auto;
      apply TERM in Hsucc;
      compute in Hsucc;
      inversion Hsucc
    end)|]);
  apply NODE in Einst; inversion Einst.

(*
Proof.
  intros header elem Hbb.
  destruct ((fn_insts fib) ! elem) eqn:Einst.
  {
    apply fib_inversion in Einst.
    repeat destruct Einst as [[Helem Hinst]|Einst];
      repeat match goal with
      | [ H: Some _ = Some _ |- _ ] =>
        inversion H; clear H
      | [ H: ?e = elem |- ?n = header /\ ?e = elem ] =>
        split; [clear H0|apply Helem]
      | [ H: ?e = elem |- (?n = header /\ ?e = elem) \/ _ ] =>
        left
      | [ H: ?e = elem |- _ ] =>
        right
      | [ H: ?e = elem |- ?e = header ] =>
        inversion Hbb; clear Hbb;
        [ auto
        |
        ]
      | [ H: SuccOf fib ?prev elem |- _ ] =>
        apply get_predecessors_correct in H;
        rewrite <- Helem in H;
        simpl in H;
        repeat destruct H as [Hpred|H]; subst; compute in NOT_TERM
      | [ H: False |- _ ] =>
        inversion H
      | [ H: true = true -> False |- _ ] =>
        assert (Ht: true = true); [reflexivity|];
        apply H in Ht; inversion Ht
      end.

    {
      inversion Hbb.
      {
        subst.

      }
      {

      }
  }
  {
    inversion Hbb; [ inversion HEADER |]; apply INST in Einst; inversion Einst.
  }
Qed.
*)
