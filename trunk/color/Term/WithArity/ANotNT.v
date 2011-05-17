(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2011-05-17

general results on non-non-termination of rewrite relations
*)

Set Implicit Arguments.

Require Import ATrs RelUtil LogicUtil ListUtil Bool VecUtil ACalls.

Section S.

  Variables (Sig : Signature) (R : rules Sig).

(***********************************************************************)
(** the subterms of a terminating term terminate *)

  Lemma subterm_eq_notNT : forall t u,
    subterm_eq t u -> ~NT (red R) u -> ~NT (red R) t.

  Proof.
    intros t u tu hu ht. destruct ht as [f [h0 hf]].
    destruct tu as [c hc]. absurd (NT (red R) u). hyp.
    exists (fun i => fill c (f i)). subst. intuition.
    intro i. apply red_fill. apply hf.
  Qed.

(***********************************************************************)
(** a constructor-headed term terminates if its subterms terminate *)

  Section notNT_undef_fun.

    Variable hyp : forallb (@is_notvar_lhs Sig) R = true.

    Lemma notNT_undef_fun : forall f, defined f R = false ->
      forall ts, Vforall (fun t => ~NT (red R) t) ts ->
        ~NT (red R) (Fun f ts).

    Proof.
      intros f hf ts hts [g [h0 hg]]. ded (hg 0). redtac.
    Abort.

  End notNT_undef_fun.

End S.
