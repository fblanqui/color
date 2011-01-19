(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Pierre-Yves Strub, 2009-04-09

Wrapper for Coq's FMaps definition + facts
*)

Set Implicit Arguments.

Require Import LogicUtil FMaps FMapAVL FMapFacts.

Module Make (Export X : OrderedType).

  Module Export XMap := FMapAVL.Make X.
  Module Export XMapProp := Properties XMap.
  Module Export XMapFacts := Facts XMap.

(***********************************************************************)
(* monotony properties of fold *)

Section fold_mon.

  Variables (elt A : Type) (le : A -> A -> Prop).

  Infix "<=" := le.

  Variables (F : key -> elt -> A -> A)
    (Fmon : forall k x a b, a <= b -> a <= F k x b).

  Lemma fold_mon : forall m a b, a <= b -> a <= fold F m b.

  Proof.
  intros m a b. apply fold_rec; intros. hyp. apply Fmon. auto.
  Qed.

End fold_mon.

End Make.
