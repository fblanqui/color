(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sidi Ould-Biha & Frederic Blanqui, 2010-05-04

*)

Set Implicit Arguments.

Require Import ATrs RelUtil ClassicUtil LogicUtil ARelation ClassicalEpsilon
  NatUtil SN ASN BoolUtil VecUtil ListUtil AReduct
  ACalls ADP AInfSeq NotSN_IS NatLeast.

(***********************************************************************)
(** Equivalence between WF and IS *)
Axiom WF_eq_notIS : forall A (R : relation A), WF R <-> forall f, ~IS R f.

Definition nonSN_min_set Sig (R : list (rule Sig)) (t : term Sig) :=
 (exists f, f 0 = t /\ IS (red R) f) /\
 (forall x, subterm x t -> forall g, g 0 = x -> ~IS (red R) g).

Axiom SN_notIS_min : forall Sig (R : list (rule Sig)) x, ~SN (red R) x ->
 exists t, subterm_eq t x /\ nonSN_min_set R t.

Lemma WF_notIS_min : forall Sig (R : list (rule Sig)), ~WF (red R) ->
 exists t, nonSN_min_set R t.
Proof.
intros. destruct (not_all_ex_not _ _ H). destruct (SN_notIS_min H0).
exists x0; intuition.
Qed.

Axiom int_red_IS : forall Sig (R : list (rule Sig)) f, IS (int_red R) f ->
 exists g, subterm (g 0) (f 0) /\ IS (red R) g.

Section WF_IS_for_TRS.
Variable Sig : Signature.

Notation term := (term Sig). Notation terms := (vector term).
Notation rule := (rule Sig). Notation rules := (list rule).

Lemma WF_min_term_succ : forall (R : rules) t, nonSN_min_set R t ->
 exists a, In a R /\ (exists s, exists u, (int_red R)# t (sub s (lhs a)) /\
 (hd_red R) (sub s (lhs a)) (sub s (rhs a)) /\
 supterm_eq (sub s (rhs a)) (sub s u) /\ nonSN_min_set R (sub s u)).
Proof.
intros. destruct H as [[f [H H0]] H1].
assert (exists i, (hd_red R) (f i) (f (S i))).
apply not_all_not_ex. intro. generalize (H2 0).
assert (IS (int_red R) f).
intro n. destruct (H0 n) as [l [r [c [s H3]]]].
destruct c. destruct (H2 n). exists l; exists r; exists s. simpl in H3. auto.
exists l; exists r; exists (Cont f0 e v c v0); exists s. split; auto.
intro T; inversion T.
intro. destruct (int_red_IS H3) as [g [Hg1 Hg2]]. rewrite <-H in H1.
apply (H1 (g 0) Hg1 g (eq_refl _) Hg2).
pose (k := projT1 (ch_min _ H2)).
destruct (H0 k) as [l [r [c [s [Rk Hk]]]]].
exists {| lhs := l; rhs := r |}; split; auto.
exists s. simpl.
Admitted.

End WF_IS_for_TRS.

Axiom WF_IS_DP : forall Sig, forall M D : rules Sig, D [= (dp M) -> 
  ~WF (hd_red_Mod (red M #) D) -> exists f, exists g, ISModMin M D f g.
