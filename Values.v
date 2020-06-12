(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.


Notation name := positive.

Notation node := positive.

Notation reg := positive.



Inductive bit : Type :=
  | I
  | O
  .

Module Type VALUE.
  Parameter t : Type.
End VALUE.

Module DOUBLE (BASE : VALUE).
  Definition t := (BASE.t * BASE.t)%type.
End DOUBLE.

Module INT1 <: VALUE.
  Definition t := bit.
End INT1.

Module INT2 := DOUBLE INT1.

Module INT4 := DOUBLE INT2.

Module INT8 := DOUBLE INT4.

Module INT16 := DOUBLE INT8.

Module INT32 := DOUBLE INT16.

Module INT64 := DOUBLE INT32.



Definition nibble := INT4.t.
Definition byte := INT8.t.
Definition word := INT16.t.
Definition dword := INT32.t.

Inductive sym : Type :=
  | SFrame (frame: positive) (object: positive) (offset: positive)
  | SAtom (object: positive) (offset: positive)
  | SAlloc (object: positive) (offset: positive)
  | SFunc (func: name)
  .

Inductive qword : Type :=
  | QVal (val: INT64.t)
  | QSym (val: sym)
  .

Inductive value : Type :=
  | Val8 (v: INT8.t)
  | Val16 (v: INT16.t)
  | Val32 (v: INT32.t)
  | Val64 (v: INT64.t)
  .
