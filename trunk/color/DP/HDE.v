(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Leo Ducas, 2007-08-06

HDE
*)
(** HDE : a simple overGraph on DP ; Head_equality *)

Require Export AGraph.

Set Implicit Arguments.

Section S.


Variable Sig : Signature.
Notation rule := (rule Sig).
Notation rules := (list rule).
Notation lhs := (@lhs Sig).
Notation rhs := (@rhs Sig).



Variable E R : rules.


Notation Sig_eq_dec := (@eq_symbol_dec Sig).

Variable hyp : rules_preserv_vars R.

Notation rule_eq_dec := (@eq_rule_dec Sig).
Notation dim := (length R).


Definition hde (r1 r2:rule) := In r1 R /\ In r2 R /\
  match (rhs r1) with 
  |Var n => True
  |Fun f v => match lhs r2 with
    |Var m => True
    |Fun g w => f=g 
    end
  end.

Lemma hde_restricted : is_restricted hde R.
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

destruct (in_rule_dec r1 R); try tauto.
destruct (in_rule_dec r2 R); try tauto.
destruct (rhs r1). left;auto. destruct (lhs r2); auto. 
destruct (Sig_eq_dec f f0);try tauto.
Defined.


Lemma int_red_preserv_hd t1 t2 : int_red E t1 t2 ->
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

Lemma int_red_rtc_preserv_hd t1 t2 : (int_red E) # t1 t2 ->
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

Lemma int_red_hd_rules_graph_incl_hde : hd_rules_graph (int_red E#) R  << hde.
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

Require Export ADuplicateSymb.
End S.

Section S2.


Variable Sig : Signature.
Notation rule := (rule (dup_sig Sig)).
Notation rules := (list rule).
Notation lhs := (@lhs (dup_sig Sig)).
Notation rhs := (@rhs (dup_sig Sig)).



Variable E R : rules.

Variable Sig_eq_dec : forall (x y :Sig) , {x=y} +{~x=y}.

Variable hyp : rules_preserv_vars R.

Definition rule_eq_dec := @eq_rule_dec (dup_sig Sig).
Definition dim := length R.

Definition int_lhs_rules_only Sig L :=
(forall l r, In (mkRule l r) L -> exists f, exists v, l=@Fun (dup_sig Sig) (int_symb Sig f) v).

Variable int_hyp : int_lhs_rules_only E. 

Lemma dup_int_rules_int_red f v t: red E (@Fun (dup_sig Sig) (hd_symb _ f) v) t -> 
int_red E (@Fun (dup_sig Sig) (hd_symb _ f) v) t.
Proof.
intros.
redtac.
exists l; exists r;exists c;exists s.
split.
destruct c. simpl in *.
deduce (int_hyp _ _ H).
do 2 destruct H2; subst.
rewrite app_fun in H0.
inversion H0.

congruence.

tauto.
Qed.

Lemma dup_int_rules_int_red_rtc_aux  u t: red E # u t ->forall f v, u=(@Fun (dup_sig Sig) (hd_symb _ f) v)-> 
int_red E # u t /\ exists w, t=(@Fun (dup_sig Sig) (hd_symb _ f) w) .
Proof.
intros u t H.
induction H; intros.
assert (int_red E # x y).
apply rt_step.
rewrite H0.
apply dup_int_rules_int_red. subst;auto.
split.  auto.
clear H.
deduce (int_red_rtc_preserv_hd H1).
destruct H.
exists v. subst. rewrite H;auto.
do 3 destruct H;subst.
destruct H. inversion H. subst.
exists x2. apply refl_equal.

split. apply rt_refl.
exists v;auto.
deduce (IHclos_refl_trans1 _ _ H1).
clear IHclos_refl_trans1.
destruct H2.
destruct H3 as [w].
deduce (IHclos_refl_trans2 _ _ H3).
destruct H4. destruct H5.
split.
eapply rt_trans;eauto.
exists x0. auto.
Qed.

Lemma dup_int_rules_int_red_rtc  f v t: red E # (@Fun (dup_sig Sig) (hd_symb _ f) v) t -> 
int_red E # (@Fun (dup_sig Sig) (hd_symb _ f) v) t.
Proof.
intros.
deduce (dup_int_rules_int_red_rtc_aux H (refl_equal _)).
tauto.
Qed. 
 

Definition hd_rhs_rules_only Sig L :=
(forall l r, In (mkRule l r) L -> exists f, exists v, r=@Fun (dup_sig Sig) (hd_symb Sig f) v).
Variable hd_hyp : hd_rhs_rules_only R.


Lemma dup_hd_rules_graph_incl_hde : 
hd_rules_graph (red E #) R << hde R.
Proof.
unfold inclusion;intros.
destruct H. intuition.  destruct H2. destruct H0.
destruct x. deduce (hd_hyp _ _ H).
do 2 destruct H2.
simpl in *. subst.
rewrite app_fun in H0.
apply (@int_red_hd_rules_graph_incl_hde _ E R (mkRule lhs (@Fun (dup_sig Sig) (hd_symb Sig x) x2)) y).
unfold hd_rules_graph.
split. tauto. split. tauto.
exists x0. exists x1.
normalize (rhs (mkRule lhs (@Fun (dup_sig Sig) (hd_symb Sig x) x2))).
rewrite app_fun.
change ((int_red E #) (@Fun (dup_sig Sig) (hd_symb Sig x) (Vmap (ASubstitution.app x1) x2))
  (ASubstitution.app x1 (shift x0 (S2.lhs y)))).
apply dup_int_rules_int_red_rtc. auto.
Qed.


End S2.



Lemma In_cons (A:Set) (x a:A) l : In x (a::l) <-> a=x \/ In x l. 
Proof.
intros.
simpl. tauto.
Qed.


Ltac prove_int_lhs_rules_only:= match goal with
  | |- int_lhs_rules_only ?L =>
  unfold int_lhs_rules_only;
  normalize L;
let aux l r H0 := match (type of H0) with
  | In ?X nil => simpl in H0; tauto
  | In ?Y ((mkRule ?L ?R)::?Q) => rewrite In_cons in H0;
	destruct H0;[inversion H0;subst l;
	 ( match L with 
    | (Fun  (int_symb ?i ?f) ?v)  => exists f;exists v;auto end)
  | idtac] end in
  let l:=fresh in let r:=fresh in let H:=fresh in intros l r H;
  repeat aux l r H
     end.

Ltac prove_hd_rhs_rules_only:= match goal with
  | |- hd_rhs_rules_only ?L =>
  unfold hd_rhs_rules_only;
  normalize L;
let aux l r H0 := match (type of H0) with
  | In ?X nil => simpl in H0; tauto
  | In ?Y ((mkRule ?L ?R)::?Q) => rewrite In_cons in H0;
	destruct H0;[inversion H0;subst l;
	 ( match R with 
    | (Fun  (hd_symb ?i ?f) ?v)  => exists f;exists v;auto end)
  | idtac] end in
  let l:=fresh in let r:=fresh in let H:=fresh in intros l r H;
  repeat aux l r H
     end.


