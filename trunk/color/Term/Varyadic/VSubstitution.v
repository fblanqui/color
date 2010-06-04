(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-12-05

substitutions
*)

Set Implicit Arguments.

Require Import LogicUtil.
Require Import VTerm.

Section S.

Variable Sig : Signature.

Notation term := (term Sig). Notation terms := (list term).

Definition substitution := variable -> term.

Fixpoint sub (s : substitution) (t : term) {struct t} : term :=
  match t with
    | Var x => s x
    | Fun f ts => Fun f (map (sub s) ts)
  end.

Lemma sub_fun : forall s f ts, sub s (Fun f ts) = Fun f (map (sub s) ts).

Proof.
refl.
Qed.

Section properties.

Require Import Relations.

Variable succ : relation term.

Definition substitution_closed :=
  forall t1 t2 s, succ t1 t2 -> succ (sub s t1) (sub s t2).

End properties.

End S.