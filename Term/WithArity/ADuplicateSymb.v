(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Leo Ducas, 2007-08-06

ADuplicateSymb
*)

(** Duplicate symbol to differentiate interal redution from head reduction *)

Set Implicit Arguments.

Require Export ATerm.
Require Export ATrs.
Require Export ASignature.

Section S.
Variable Sig : Signature.
Definition symb := symbol Sig.
Definition ar := @arity Sig.
Definition eq_symb_dec := @eq_symbol_dec Sig.



Section Definitions.
Variable R : list (rule Sig).

Inductive dup_symb  : Set :=
  |hd_symb :  symb -> dup_symb
  |int_symb :  symb -> dup_symb .

Definition dup_ar s := match s with
  |hd_symb s' => ar s'
  |int_symb s' => ar s'
  end.

Lemma eq_dup_symb_dec : forall f g : dup_symb, {f=g}+{~f=g}.
Proof.
intros.
decide equality;apply eq_symb_dec.
Defined.

Definition dup_sig : Signature := mkSignature dup_ar eq_dup_symb_dec.


Fixpoint dup_int_term (t:term Sig) := match t with
  |Var x => Var x
  |Fun f v => @Fun dup_sig (int_symb f) (Vmap dup_int_term v)
  end.

Lemma dup_int_term_fun f v : 
dup_int_term (Fun f v) = @Fun dup_sig (int_symb f) (Vmap dup_int_term v).
Proof.
intros.
trivial.
Qed.


Definition dup_hd_term (t:term Sig) := match t with
  |Var x => Var x
  |Fun f v => @Fun dup_sig (hd_symb f) (Vmap dup_int_term v)
  end.




Lemma dup_hd_term_fun f v : 
dup_hd_term (Fun f v) = @Fun dup_sig (hd_symb f) (Vmap dup_int_term v).
Proof.
intros.
trivial.
Qed.


Definition dup_int_rule r := mkRule (dup_int_term (lhs r)) (dup_int_term (rhs r)).

Definition dup_hd_rule r := mkRule (dup_hd_term (lhs r)) (dup_hd_term (rhs r)).

Definition dup_int_rules := map dup_int_rule R.

Definition dup_hd_rules := map dup_hd_rule R.

Definition dup_int_subst (s:substitution Sig) n := dup_int_term (s n).

Lemma dup_int_subst_spec s t: 
(app (dup_int_subst s) (dup_int_term t))= dup_int_term (app s t).
Proof.
intros.
pattern t.
set (Q:=Vforall (fun t0 : term Sig =>
 app (dup_int_subst s) (dup_int_term t0) = dup_int_term (app s t0))).
apply term_ind with (Q:=Q).
(* Var *)
intro; unfold dup_int_subst; simpl. apply refl_equal.
(* Fun *)
intros. rewrite dup_int_term_fun.
do 2 rewrite app_fun. rewrite dup_int_term_fun.
unfold Q in H.
cut ( (Vmap (app (dup_int_subst s)) (Vmap dup_int_term v)) =
 (Vmap dup_int_term (Vmap (app s) v))).
intros. rewrite <- H0. auto.
do 2 rewrite Vmap_map.
apply Vmap_eq. apply H.
(* Vnil *)
unfold Q;simpl;auto.
(* Vcons *)
unfold Q;simpl;auto.
Qed.

Lemma dup_int_subst_hd_dup s f v:
(app (dup_int_subst s) (dup_hd_term (Fun f v)))= dup_hd_term (app s (Fun f v)).
Proof.
intros.
rewrite dup_hd_term_fun. do 2 rewrite app_fun. rewrite dup_hd_term_fun.
cut ((Vmap (app (dup_int_subst s)) (Vmap dup_int_term v)) =
 (Vmap dup_int_term (Vmap (app s) v)) ).
intro. rewrite <- H. apply refl_equal.
do 2 rewrite Vmap_map.
apply Vmap_eq_ext. 
apply dup_int_subst_spec.
Qed. 


Lemma hd_red_dup_hd_red (hyp :no_lhs_variable R)
(hyp' :no_rhs_variable R) t u: hd_red R t u -> 
hd_red (dup_hd_rules) (dup_hd_term t) (dup_hd_term u).
Proof.
intros. redtac. unfold hd_red.
exists (dup_hd_term l). exists (dup_hd_term r). exists (dup_int_subst s).
split.
unfold dup_hd_rules. 
change (In (dup_hd_rule (mkRule l r)) (map dup_hd_rule R)).
apply in_map. auto.
destruct l.
cut False. tauto. 
 unfold no_lhs_variable in hyp.
deduce (hyp _ _ H). simpl in H2;tauto.

rewrite  dup_int_subst_hd_dup.
split;subst. apply refl_equal.

destruct r.
cut False. tauto. 
unfold no_rhs_variable in hyp'.
deduce (hyp' _ _ H). simpl in H0;tauto.

rewrite  dup_int_subst_hd_dup.
split;subst.
Qed.

Fixpoint dup_int_context c := match c with
  |Hole => Hole
  |Cont f _ _ H v c' w => @Cont dup_sig (int_symb f) _ _ H 
  (Vmap dup_int_term  v) (dup_int_context c') (Vmap dup_int_term w)
  end.

Lemma dup_int_context_spec c s l :
dup_int_term (fill c (app s l)) =
fill (dup_int_context c) (app (dup_int_subst s) (dup_int_term l)).
Proof.
induction c;intros.
simpl.
rewrite dup_int_subst_spec. apply refl_equal.
simpl.
cut (
Vmap dup_int_term (Vcast (Vapp v (Vcons (fill c (app s l)) v0)) e)=
  (Vcast
     (Vapp (Vmap dup_int_term v)
        (Vcons
           (fill (dup_int_context c) (app (dup_int_subst s) (dup_int_term l)))
           (Vmap dup_int_term v0))) e)).
intro. rewrite H;auto.
rewrite Vmap_cast.
rewrite Vmap_app.
simpl.
rewrite IHc.
auto.
Qed.

Lemma red_dup_int_red t u : red R t u ->
red (dup_int_rules) (dup_int_term t) (dup_int_term u).
Proof.
intros. redtac.
exists (dup_int_term l). exists (dup_int_term r).
exists (dup_int_context c). exists (dup_int_subst s).
split.
change (In (dup_int_rule (mkRule l r)) (map dup_int_rule R)).
apply in_map. auto.
do 2 rewrite <- dup_int_context_spec.
split;subst;apply refl_equal.
Qed.


Definition dup_hd_context c := match c with
  |Hole => Hole
  |Cont f _ _ H v c' w => @Cont dup_sig (hd_symb f) _ _ H 
  (Vmap dup_int_term  v) (dup_int_context c') (Vmap dup_int_term w)
  end.


Lemma int_red_dup_int_red t u : int_red R t u ->
red (dup_int_rules) (dup_hd_term t) (dup_hd_term u).
Proof.
intros. redtac.
exists (dup_int_term l). exists (dup_int_term r).
exists (dup_hd_context c). exists (dup_int_subst s).
destruct c. tauto.
split.
change (In (dup_int_rule (mkRule l r)) (map dup_int_rule R)).
apply in_map. auto.
subst;simpl.
split;rewrite Vmap_cast;rewrite Vmap_app;
simpl;rewrite <- dup_int_context_spec;auto.
Qed.
End Definitions.

Section WF_duplicate.
Require Export AGraph.
Variables E R : (list (rule Sig)).
Variable no_lhs_var : no_lhs_variable R.
Variable no_rhs_var : no_rhs_variable R.


Lemma WF_duplicate_hd_int_red :
WF(hd_red_mod (dup_int_rules E) (dup_hd_rules R))
-> WF(hd_red_Mod (int_red E #) R).
Proof.
intros.
set(rel:=hd_red_mod (dup_int_rules E) (dup_hd_rules R)).
set(rel' :=Rof rel (dup_hd_term)).
apply (@WF_incl _  (hd_red_Mod (int_red E #) R) rel').
unfold rel',rel,hd_red_Mod,hd_red_mod.

unfold inclusion;intros.
destruct H0 as [z];exists (dup_hd_term z).
destruct H0;split.
clear H1.
induction H0.
apply rt_step.
apply int_red_dup_int_red. auto.
apply rt_refl.
eapply rt_trans. apply IHclos_refl_trans1. tauto.
apply  hd_red_dup_hd_red;auto.
subst rel rel'.
apply WF_inverse;auto.
Qed.


End WF_duplicate.
End S.
