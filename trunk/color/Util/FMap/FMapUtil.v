(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Pierre-Yves Strub, 2009-04-09

Wrapper for Coq's FMaps definition + facts
*)

Set Implicit Arguments.

Require Import LogicUtil FMaps FMapAVL FMapFacts.

Module Make (X : OrderedType).

  Module Export XMap := FMapAVL.Make X.
  Module Export XMapProps := Properties XMap.
  Module Export XMapFacts := Facts XMap.
  Module Export XMapOrdProps := OrdProperties XMap.

  Import X.

End Make.
