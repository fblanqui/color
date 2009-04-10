(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Pierre-Yves Strub, 2009-04-09

Wrapper for Coq's FMaps definition + facts
*)

Set Implicit Arguments.

Require Import LogicUtil.

Require Import FMaps.
Require Import FMapAVL.
Require Import FMapFacts.

Module Make (X : OrderedType).
  Module XMap      := FMapAVL.Make (X).
  Module XMapProp  := Properties (XMap).
  Module XMapFacts := Facts (XMap).

  Export X XMap XMapProp XMapFacts.
End Make.
