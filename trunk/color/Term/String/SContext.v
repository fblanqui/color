(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-12-05

one-hole contexts
*)

(* $Id: SContext.v,v 1.1 2007-05-25 16:24:22 blanqui Exp $ *)

Set Implicit Arguments.

Require Export LogicUtil.

Section S.

Require Export VSignature.

Variable Sig : Signature.

Require Export List.

Notation string := (list Sig).

(***********************************************************************)
(** contexts and replacement of the hole *)

Record context : Type := mkContext { lft : string; rgt : string }.

Definition fill c s := lft c ++ s ++ rgt c.

(***********************************************************************)
(** context composition *)

Definition comp c d := mkContext (lft c ++ lft d) (rgt d ++ rgt c).

Lemma fill_comp : forall c d u, fill c (fill d u) = fill (comp c d) u.

Proof.
intros. destruct c. destruct d.
unfold fill. simpl. repeat rewrite app_ass. refl.
Qed.

End S.
