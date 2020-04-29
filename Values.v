(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.



Definition name := positive.



Module Type VALUE.
  Parameter t : Type.
End VALUE.

Module DOUBLE (BASE : VALUE).
  Definition t := (BASE.t * BASE.t)%type.
End DOUBLE.

Module Nibble <: VALUE.
  Definition t := (bool * bool * bool * bool)%type.
End Nibble.

Module Byte := DOUBLE Nibble.

Module Word := DOUBLE Byte.

Module DoubleWord := DOUBLE Word.

Module QuadWord := DOUBLE DoubleWord.



Definition nibble := Nibble.t.
Definition byte := Byte.t.
Definition word := Word.t.
Definition dword := DoubleWord.t.

Inductive sym : Type :=
  | SFrame (frame: positive) (object: positive) (offset: positive)
  | SAtom (object: positive) (offset: positive)
  | SAlloc (object: positive) (offset: positive)
  | SFunc (func: name)
  .

Inductive qword : Type :=
  | QVal (val: QuadWord.t)
  | QSym (val: sym)
  .

