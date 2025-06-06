(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2014-12-11

* Basic consequences of Description.constructive_definite_description
*)

Set Implicit Arguments.

From Stdlib Require Import ClassicalDescription.

Arguments constructive_definite_description [A P] _.

Notation cdd := constructive_definite_description.
Notation dec := excluded_middle_informative.

Lemma dec1 A (P : A->Prop) x : {P x}+{~P x}.

Proof. apply dec. Qed.

Lemma eq_dec {A} (x y : A) : {x=y}+{x<>y}.

Proof. apply dec. Qed.
