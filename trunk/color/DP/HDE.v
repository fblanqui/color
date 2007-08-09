(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Leo Ducas, 2007-08-06

HDE
*)
(** HDE : a simple overGraph on DP ; Head_equality *)

Require Export ADPGraph.

Set Implicit Arguments.

Section S.


Variable Sig : Signature.
Notation rule := (rule Sig).
Notation rules := (list rule).
Notation lhs := (@lhs Sig).
Notation rhs := (@rhs Sig).



Variable R : rules.

Variable Sig_eq_dec : forall (x y :Sig) , {x=y} +{~x=y}.
Variable hyp : rules_preserv_vars R.

Notation DP := (dp R).
Notation DPG := (dp_graph R).

Variable rule_eq_dec :forall (x y :rule) , {x=y} +{~x=y}.
Definition dim := length DP.


Definition hde (r1 r2:rule) := In r1 DP /\ In r2 DP /\
  match (rhs r1) with 
  |Var n => True
  |Fun f v => match lhs r2 with
    |Var m => True
    |Fun g w => f=g 
    end
  end.

Lemma hde_restricted : is_restricted hde DP.
Proof.
unfold is_restricted.
intros.
unfold hde in H;tauto.
Qed.

Lemma in_rule_dec (a:rule) L : {In a L} + {~ In a L}.
Proof.
intros.
induction L; auto.
simpl;destruct IHL; destruct (rule_eq_dec a a0);subst;try tauto.
right. intuition; auto.
Defined.

Lemma hde_dec r1 r2 : {hde r1 r2} + {~hde r1 r2}.
Proof.
intros.
unfold hde.

destruct (in_rule_dec r1 DP); try tauto.
destruct (in_rule_dec r2 DP); try tauto.
destruct (rhs r1). left;auto. destruct (lhs r2); auto. 
destruct (Sig_eq_dec f f0);try tauto.
Defined.


Lemma int_red_preserv_hd t1 t2 : int_red R t1 t2 ->
 exists f, exists v,exists w, t1=Fun f v /\ t2=Fun f w.
Proof.
intros.
do 5 destruct H. intuition.
destruct x1. try congruence.
simpl in *.
exists f.
exists (Vcast (Vapp v (Vcons (fill x1 (ASubstitution.app x2 x)) v0)) e).
exists (Vcast (Vapp v (Vcons (fill x1 (ASubstitution.app x2 x0)) v0)) e).
tauto.
Qed.

Lemma int_red_rtc_preserv_hd t1 t2 : (int_red R) # t1 t2 ->
t1=t2 \/ exists f, exists v,exists w, t1=Fun f v /\ t2=Fun f w.
Proof.
intros.
induction H;try auto.
right; apply int_red_preserv_hd. auto.
destruct IHclos_refl_trans1;destruct IHclos_refl_trans2;subst;auto.
right.
do 3 destruct H1.
do 3 destruct H2.
intuition;subst;auto.
inversion H1. subst.
exists x3;exists x1;exists x5. auto.
Qed.

Lemma dp_graph_incl_hde : DPG << hde.
Proof.
unfold inclusion;intros.
destruct x;destruct y.
destruct H. destruct H0.
do 2 destruct H1.
unfold hde;destruct lhs0;destruct rhs;simpl;auto.
intuition;auto.

deduce (int_red_rtc_preserv_hd H1).
destruct H2.
simpl in H2. inversion H2;auto.

do 4 destruct H2.
inversion H2.
inversion H3.
congruence.
Qed.
End S.