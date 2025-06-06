From Stdlib Require Import Bool.


Lemma impl_bool_def : 
  forall p q, orb (negb p) q = true -> p = true -> q = true.
Proof.
  intros p q H H0; subst;exact H.
Qed.
