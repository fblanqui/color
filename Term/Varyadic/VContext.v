(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-12-05

one-hole contexts
*)

(* $Id: VContext.v,v 1.2 2007-01-19 17:22:39 blanqui Exp $ *)

Set Implicit Arguments.

Require Export LogicUtil.

Section S.

Require Export VSignature.

Variable Sig : Signature.

Require Export VTerm.

Notation term := (term Sig).
Notation terms := (list term).

(***********************************************************************)
(** contexts and replacement of the hole *)

Inductive context : Set :=
  | Hole : context
  | Cont : forall f : Sig, terms -> context -> terms -> context.

Fixpoint fill (c : context) (t : term) {struct c} : term :=
  match c with
    | Hole => t
    | Cont f v1 c' v2 => Fun f (v1 ++ fill c' t :: v2)
  end.

(***********************************************************************)
(** context composition *)

Fixpoint comp (C : context) : context -> context :=
  match C with
    | Hole => fun E => E
    | Cont f ts1 D ts2 => fun E => Cont f ts1 (comp D E) ts2
  end.

Lemma fill_comp : forall C D u, fill C (fill D u) = fill (comp C D) u.

Proof.
induction C; simpl; intros. refl. rewrite (IHC D u). refl.
Qed.

End S.

Implicit Arguments Hole [Sig].
