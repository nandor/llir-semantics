(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Require Import LLIR.Maps.
Require Import LLIR.LLIR.

Import ListNotations.

Module Aliasing.
  Inductive location :=
    | Offset (ident: positive) (offset: positive)
    | Range (ident: positive)
    .

  Inductive object :=
    | Object (ident: positive) (offset: positive)
    .

  Parameter t: Type.

  Parameter analyse: func -> t.

  Parameter get_precise_addr: t -> reg -> option object.

  Section PROPERTIES.
    Variable f: func.
    Variable aa: t.
    Hypothesis Haa_result: aa = analyse f.

    Inductive loads_from: reg -> reg -> reg -> positive -> positive -> Prop :=
      | load:
        forall (k: node) (dst: reg) (addr: reg) (t: ty)
               (object: positive) (offset: positive)
               (next: node),
          Some (Object object offset) = get_precise_addr aa addr ->
          Some (LLLd (t, dst) next addr) = f.(fn_insts) ! k ->
          loads_from k dst addr object offset
      .
  End PROPERTIES.
End Aliasing.
