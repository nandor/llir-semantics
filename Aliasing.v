(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Require Import LLIR.Maps.
Require Import LLIR.LLIR.
Require Import LLIR.State.

Import ListNotations.



Inductive points_to_item :=
  | PTOffset (object: positive) (offset: positive)
  | PTRange (object: (option positive))
  .

Definition points_to_set :=
  PTrie.t (list points_to_item).

Definition Object := (positive * positive)%type.

Axiom local_pta : func -> points_to_set.

Section ANALYSIS.
  Variable f: func.

  Section UTILITIES.
    Variable aa: points_to_set.

    Definition get_load_addr (addr: reg): option Object :=
      match PTrie.get aa addr with
      | Some addrs => 
        match addrs with
        | [PTOffset object offset] =>
          Some (object, offset)
        | _ => None
        end
      | _ => None
      end.

    Inductive loads_from: reg -> reg -> reg -> positive -> positive -> Prop :=
      | load:
        forall (k: node) (val: reg) (addr: reg) 
               (object: positive) (offset: positive) 
               (next: node),
          Some (object, offset) = get_load_addr addr ->
          Some (LLLd addr val next) = f.(fn_insts) ! k ->
          loads_from k val addr object offset
      .

  End UTILITIES.
End ANALYSIS.