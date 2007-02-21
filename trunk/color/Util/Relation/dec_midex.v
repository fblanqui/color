(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Stephane Le Roux, 2007-02-20

excluded middle and decidability for relation.
*)

(***********************************************************************)
(* ON EXCLUDED MIDDLE AND DECIDABILITY *)

Require Import Relations. 

Set Implicit Arguments.

Section EM_DEC.

Variable A : Set.
Variable R : relation A.

Definition eq_midex :=  forall x y : A, x=y \/ x<>y.
Definition rel_midex := forall x y, R x y \/ ~R x y.

Definition eq_dec := forall x y : A, {x=y}+{x<>y}.
Definition rel_dec := forall x y, {R x y}+{~R x y}.

Lemma eq_dec_midex : eq_dec -> eq_midex.

Proof.
do 3 intro. destruct (H x y); tauto.  
Qed.

Lemma rel_dec_midex : rel_dec -> rel_midex.

Proof.
do 3 intro. destruct (H x y); tauto. 
Qed.

Lemma bool_rel_dec :
{f : A -> A -> bool | forall x y : A, if f x y then R x y else ~R x y} -> rel_dec.

Proof. 
intros (f,H) x y. generalize (H x y). case (f x y) ; intros ; tauto.
Qed.

Lemma rel_dec_bool : 
rel_dec -> { f : A -> A -> bool | forall x y : A, if f x y then R x y else ~R x y }.

Proof.
intro H. exists (fun x y : A => if H x y then true else false).
intros x y. destruct (H x y) ; trivial.
Qed.

End EM_DEC.