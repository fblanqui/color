(************************************************************************
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-02-09

interpretation of algebraic terms with arity
************************************************************************)

(* $Id: AInterpretation.v,v 1.2 2006-10-24 12:41:36 blanqui Exp $ *)

Set Implicit Arguments.

Section S.

Require Export ASignature.

Variable Sig : Signature.

Require Export ATerm.

Notation term := (term Sig).
Notation terms := (vector term).
Notation "'args' f" := (terms (arity f)) (at level 70).

(***********************************************************************)
(* interpretation of symbols *)

Require Export NaryFunction.

Record interpretation : Type := mkInterpretation {
  domain : Set;
  fint : forall f : Sig, naryFunction domain (arity f)
}.

(***********************************************************************)
(* interpretation of terms *)

Variable I : interpretation.

Notation D := (domain I).

Definition valuation := variable -> D.

Variable xint : valuation.

Fixpoint term_int (t : term) : D :=
  match t with
    | Var x => xint x
    | Fun f ts =>
      let fix terms_int n (ts : terms n) {struct ts} : vector D n :=
        match ts in vector _ n return vector D n with
          | Vnil => Vnil
          | Vcons t' n' ts' => Vcons (term_int t') (terms_int n' ts')
        end
      in fint I f (terms_int (arity f) ts)
  end.

Lemma term_int_fun : forall f ts,
  term_int (Fun f ts) = fint I f (Vmap term_int ts).

Proof.
intros. simpl. apply (f_equal (fint I f)). induction ts. auto.
rewrite IHts. auto.
Qed.

(***********************************************************************)
(* gives the vector (xint 0) .. (xint (n-1)) *)

Fixpoint fval (n : nat) : vector D n :=
  match n as n0 return vector _ n0 with
    | O => Vnil
    | S p => Vadd (fval p) (xint p)
  end.

Lemma fval_eq : forall n x (H : lt x n), Vnth (fval n) H = xint x.

Proof.
intro n. elim n.
 intros x Hx. elimtype False. apply (lt_n_O _ Hx).
 intros p Hrec x H0. simpl fval.
 case (le_lt_eq_dec _ _ (le_S_n _ _ H0)); intro H1.
  rewrite (Vnth_addl (fval p) (xint p) H0 H1). apply Hrec.
  rewrite Vnth_addr. 2: assumption. rewrite H1. reflexivity.
Qed.

End S.

Implicit Arguments mkInterpretation [Sig domain].
