(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-12-05

substitutions
*)

(* $Id: VSubstitution.v,v 1.4 2008-10-06 03:22:32 blanqui Exp $ *)

Set Implicit Arguments.

Section S.

Require Export VSignature.

Variable Sig : Signature.

Require Export VTerm.

Notation term := (term Sig).
Notation terms := (list term).

(***********************************************************************)
(* definition of substitutions as functions from variables to terms *)

Definition substitution := variable -> term.

(* application of a substitution *)

Fixpoint sub (s : substitution) (t : term) {struct t} : term :=
  match t with
    | Var x => s x
    | Fun f ts =>
      let fix subs (ts : terms) : terms :=
	match ts with
	  | nil => nil
	  | cons t ts' => sub s t :: subs ts'
	end
	in Fun f (subs ts)
  end.

Lemma sub_fun : forall s f v, sub s (Fun f v) = Fun f (map (sub s) v).

Proof.
intros f s. induction v; simpl; refl.
Qed.

Section properties.

Variable succ : relation term.

Definition substitution_closed :=
  forall t1 t2 s, succ t1 t2 -> succ (sub s t1) (sub s t2).

End properties.

End S.
