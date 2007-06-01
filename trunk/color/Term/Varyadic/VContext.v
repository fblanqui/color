(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-12-05

one-hole contexts
*)

(* $Id: VContext.v,v 1.3 2007-06-01 19:32:09 koper Exp $ *)

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

(***********************************************************************)
(** subterm ordering *)

Definition subterm_eq u t := exists C, t = fill C u.

Definition subterm u t := exists C, C <> Hole /\ t = fill C u.

Lemma subterm_immediate : forall f v a, In a v -> subterm a (Fun f v).

Proof.
Admitted.    

(***********************************************************************)
(** subterm-based induction principle *)

Lemma subterm_rect : forall (P : term -> Type)
  (IH : forall t, (forall u, subterm u t -> P u) -> P t),
  forall t, P t.

Proof.
Admitted.

Definition subterm_ind : forall (P : term -> Prop)
  (IH : forall t, (forall u, subterm u t -> P u) -> P t),
  forall t, P t := subterm_rect.

Definition subterm_rec : forall (P : term -> Set)
  (IH : forall t, (forall u, subterm u t -> P u) -> P t),
  forall t, P t := subterm_rect.

End S.

Implicit Arguments Hole [Sig].
