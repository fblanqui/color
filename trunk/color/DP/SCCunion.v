(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Leo Ducas, 2007-08-06

SCCUnion
*)

(** Modular termination proof through SCC of an over-DPGraph*)

Require Export SCCTopoOrdering.
Require Export ADPGraph.
Require Export ATerm.
Require Export ATrs.
Require Export ListPermutation.
Section S.

Variable Sig : Signature.
Notation rule := (rule Sig).
Notation rules := (list rule).
Notation lhs := (@lhs Sig).
Notation rhs := (@rhs Sig).

Variable R : rules.

Variable hyp : rules_preserv_vars R.


Notation DP := (dp R).
Notation DPG := (dp_graph R).

Variable rule_eq_dec :forall (x y :rule) , {x=y} +{~x=y}.
Definition dim := length DP.

Variable ODPG : relation rule.
Variable over_DPG : DPG << ODPG.
Variable restriction : is_restricted ODPG DP.
Variable rp_free: repeat_free DP.
Variable ODPG_dec : forall x y, {ODPG x y} + {~ ODPG x y }.


Definition hyps := mkSCC_dec_hyps _ rule_eq_dec _ _ restriction rp_free ODPG_dec.


Variables 
	(M : matrix dim dim)
  (HM: M= SCC_mat_effective hyps) .


Section chain_restriction.

Notation empty := (fun _ _ => False ).

Definition proj1_sig2 T P Q (e :@sig2 T P Q) := match e with
   | exist2 a b c => a
   end.

Definition s_SCC's := proj1_sig2 _ _ _
(sorted_SCC' hyps M HM).

Notation ODPGquo' :=(Rquo' hyps M HM ).
Notation le_ODPGquo' := (le_Rquo' hyps M HM).


(** s_SCCs properties *)

Lemma s_SCC's_spec_cover i : i<dim -> In i s_SCC's.
Proof.
intros.
unfold s_SCC's.
destruct( sorted_SCC' hyps).
unfold proj1_sig2.
unfold permutation,meq in *.
deduce (p i).
rewrite nfirst_multiplicity in H0.
destruct(lt_ge_dec i (length (hyp_Dom hyps)));try omega.
cut(exists j,j=i /\ In j x). intros;destruct H1. destruct H1. rewrite <- H1;auto.
apply (multiplicity_in (@eq nat) eq_nat_dec).   omega.
assert (length (hyp_Dom hyps) = dim);intuition.
rewrite <- H1 in H. assert(False). omega. tauto.
Qed.

Lemma s_SCC's_spec_bound i : In i s_SCC's -> i<dim .
Proof.
intros.
unfold s_SCC's in H.
destruct( sorted_SCC' hyps).
unfold proj1_sig2 in *.
generalize p;intros.
unfold permutation,meq in p.
deduce (p i).
rewrite nfirst_multiplicity in H0.
destruct(lt_ge_dec i (length (hyp_Dom hyps)));try omega.
assert (dim=(length (hyp_Dom hyps))). auto. rewrite H1 in *;auto.
cut(exists j,j=i /\ In j (nfirst_list dim)). intros;destruct H1. destruct H1. 
rewrite nfirst_exact in H2. subst i;auto.
eapply permutation_in.
intuition.
apply permutation_sym. eauto.
auto.
Qed.


(** chain restricted to an SCC *)
Notation SCC'_tag := (SCC'_tag hyps).
Notation SCC' :=(SCC' hyps).
Notation SCC'_dec :=(SCC'_dec hyps).

Definition hd_red_SCC' i t1 t2 := exists l, exists r, exists s,
  SCC'_tag M HM (mkRule l r) = Some i  /\ t1 = app s l /\ t2 = app s r.



Lemma hd_red_SCC'_cover t1 t2 : hd_red DP t1 t2 -> exists i, hd_red_SCC' i t1 t2 /\ i<dim.
Proof.
intros.
unfold hd_red in *.
do 4 destruct H;destruct H0.
cut (exists n, SCC'_tag  M HM (mkRule x x0) = Some n).
intro.
destruct H2 as [i].
exists i. split. exists x;exists x0;exists x1.
split;try tauto.
unfold dim.
apply (list_find_first_Some_bound (SCC' (mkRule x x0)) (SCC'_dec M HM (mkRule x x0)) ).
intuition.
deduce (list_find_first_exist (SCC' (mkRule x x0)) (SCC'_dec M HM (mkRule x x0)) _ DP H).
assert (SCC'_tag M HM (mkRule x x0) <> None). apply H2.
split;try tauto. left;auto.
destruct (SCC'_tag M HM (mkRule x x0)). exists n;auto. congruence.
Qed.


Definition chain_SCC' i :=  int_red R # @ hd_red_SCC' i.
Notation union := (Relation_Operators.union).

Definition sorted_chain_SCC' := map chain_SCC' s_SCC's.

(** union of chain_SCC' *)

Definition chain_SCC'_union := fold_right (@union (term Sig)) (fun _ _ => False ) sorted_chain_SCC'.

Lemma union_list_spec (A:Set) L (x y:A) (r : relation A):
(In r L) -> r x y ->  (fold_right (@union A) (fun _ _ => False ) L) x y.
Proof.
intros.
induction L.
simpl in *;tauto.
simpl in *.
destruct H. destruct H.
subst;left;auto.
right;tauto.
Qed.

Lemma union_list_spec2 (A:Set) L (x y:A) : (fold_right (@union A) (fun _ _ => False ) L) x y 
-> exists r, In r L /\ r x y.
Proof.
intros.
induction L.
simpl in *;tauto.
simpl in *.
destruct H. exists a;split;tauto.
destruct (IHL H). exists x0.
split;try tauto.
Qed.


Theorem chain_SCC'_cover : chain R << chain_SCC'_union.
Proof.
unfold inclusion.
intros.
unfold chain in H. do 2 destruct H.
inversion H0. do 2 destruct H1.
deduce (hd_red_SCC'_cover _ _ H0).
destruct H2 as [i].
assert (chain_SCC' i x y).
exists x0;tauto. 
unfold chain_SCC'_union.
eapply union_list_spec;eauto.
unfold sorted_chain_SCC'.
apply in_map.
apply s_SCC's_spec_cover;tauto.
Qed.

(** properties of the total order RT relatively to restricted chain *)

Notation RT_ODPG := (RT hyps M HM).

Lemma compose_empty i j: RT_ODPG i j -> chain_SCC' j @ chain_SCC' i << empty.
Proof.
intros.
unfold inclusion.
intros x y H0.
destruct H0 as [z]. destruct H0.

assert (~ ODPGquo' j i). 
unfold RT in  *.
destruct (topo_sortable_Rquo' ). simpl in *.
intuition.
deduce (l (nfirst_list dim )). clear l.
set (RTbis :=(fun x y : nat => x0 (nfirst_list dim) x y = true)) in *.
change (RTbis i j) in H.
assert (RTbis j i).
destruct H3. intuition.
apply H5.
deduce (Rquo_restricted hyps M HM j i).
split;try split;try tauto; destruct H2;try tauto.
unfold irreflexive in *. intuition. destruct H3;intuition. apply (H7 i).
eapply H5;eassumption.


assert (ODPGquo' j i). 
unfold Rquo'. intuition.
unfold Rquo in *.
unfold chain_SCC' in *.
destruct H0 as [x']. destruct H0.
destruct H1 as [z']. destruct H1.
destruct H3 as [t1]. destruct H3 as [r1]. destruct H3 as [s1].
exists (mkRule t1 r1); split;try tauto.
destruct H4 as [t2]. destruct H4 as [r2]. destruct H4 as [s2].
exists (mkRule t2 r2); split;try tauto.
apply (over_DPG (mkRule t1 r1) (mkRule t2 r2)).
eapply chain_dp2_dp_graph;intuition. unfold chain_dp.


split. assert (SCC' (mkRule t1 r1) (mkRule t1 r1)).
rewrite (SCC'_tag_exact hyps M HM ).
split;try tauto. congruence. destruct H7. tauto.
exists s1. split;simpl;auto;eauto. intuition.


split. assert (SCC' (mkRule t2 r2) (mkRule t2 r2)).
rewrite (SCC'_tag_exact hyps M HM ) .
split;try tauto. congruence. destruct H7;tauto.
exists s2. split;simpl;auto;eauto. congruence.

subst j.
unfold RT in *.
destruct (topo_sortable_Rquo'). simpl in *.
deduce (l (nfirst_list dim)). clear l.
destruct H3. intuition. unfold irreflexive in H6. deduce (H6 i). auto.
tauto.
Qed.

(** Proof of the modular termination criterion *)
Require Export Union.
Lemma sort_transitive (B:Set) (a:B) L rel :
 transitive rel -> sort rel (a::L) -> forall x, In x L  -> rel a x.
Proof.
intros.
induction L. destruct H1. 
simpl in H1; destruct H1.
subst. inversion H0;subst;auto. inversion H4;subst;auto.

apply IHL;auto.  inversion H0;inversion H4.
subst. apply cons_sort.  subst;auto.
inversion H5. subst. inversion H9. 
apply nil_leA. subst. apply cons_leA.
eapply H; eauto.
Qed.

Require Export ListUtil.
Lemma In_map_elim_Type  (A B : Type) (f : A->B) :
forall x l, In x (map f l) -> exists y, In y l /\ x = f y.
Proof.
intros.
induction l; simpl in H. tauto.
destruct H.
exists a; split;simpl; try congruence. left;auto.
destruct IHl. auto. destruct H0.
 exists x0;split;simpl; try congruence. right;auto.
Qed.

Lemma WF_SCC'_union_aux L : (forall i, In i L -> WF (chain_SCC' i)) -> sort RT_ODPG L -> 
WF ((fold_right (@union _) empty) (map chain_SCC' L)).
Proof.
intros.
induction L; simpl in *.
intro.
apply SN_intro. intros;tauto.
inversion H0. subst a0; subst l. 
eapply WF_incl. apply union_commut.
apply WF_union.
unfold inclusion. intros. cut False;try tauto.
destruct H1 as [z]. destruct H1.
deduce (union_list_spec2 _ _ _ _ H1). destruct H5 as [r]. destruct H5.

assert (exists b, In b L /\ r = chain_SCC' b).
apply In_map_elim_Type;auto.
destruct H7 as [b]. destruct H7;subst r.
cut (RT_ODPG a b). intro. eapply (compose_empty a b H8 x y ). exists z; tauto.
eapply sort_transitive. unfold RT; destruct topo_sortable_Rquo'. simpl in *. 
deduce (l (nfirst_list dim)).
destruct H8. intuition.
eassumption. auto.

apply IHL. intros. apply H. right;auto.
destruct H0;auto. apply H. left;auto.
Qed.

Lemma WF_SCC'_union : (forall i, i<dim -> WF (chain_SCC' i)) -> WF (chain R).
Proof.
intros.
eapply WF_incl.
apply chain_SCC'_cover. unfold chain_SCC'_union,sorted_chain_SCC'. 
eapply WF_SCC'_union_aux.
intros. apply H. apply  s_SCC's_spec_bound. auto.
unfold s_SCC's; destruct sorted_SCC'. simpl in *. auto.
Qed.

End chain_restriction.


(** Somme lemma to proof trivial case of sub-problem termination *)
Fixpoint SCC'_list_aux i L {struct L} := match L with
  | nil => nil
  | x::q => match eq_opt_nat_dec (SCC'_tag hyps M HM x) (Some i) with
    |left _ => x:: (SCC'_list_aux i q)
    |right _ => (SCC'_list_aux i q)
    end
  end.

Lemma SCC'_list_aux_exact i L r : In r (SCC'_list_aux i L) <-> In r L /\ (SCC'_tag hyps M HM r)=(Some i).
Proof.
intros.
induction L.
simpl in *. tauto.

split;intro.
simpl in *.
destruct (eq_opt_nat_dec (SCC'_tag hyps M HM a) (Some i));destruct (rule_eq_dec a r);simpl in *;intuition.
subst a;tauto.

destruct H.
simpl in *.
destruct (eq_opt_nat_dec (SCC'_tag hyps M HM a) (Some i));destruct H;simpl in *; try subst a;tauto.
Qed.

Definition SCC'_list i := SCC'_list_aux i DP.

Lemma SCC_list_exact i r : In r (SCC'_list i) <->(SCC'_tag hyps M HM r)=(Some i).
Proof.
intros;split;intro.
unfold SCC'_list in H.
rewrite SCC'_list_aux_exact in H. tauto.

unfold SCC'_list;rewrite SCC'_list_aux_exact;split;try tauto.
assert (SCC' hyps r r).
rewrite (SCC'_tag_exact hyps M HM).
intuition. congruence. unfold SCC' in H0.
tauto.
Qed. 
 
Lemma chain_SCC'_red_mod i: chain_SCC' i << red_mod R (SCC'_list i).
Proof.
unfold inclusion; intros.
unfold red_mod.
do 2 destruct H.

exists x0.
split.
deduce (@int_red_incl_red _ R). 
deduce (incl_rtc H1).
apply H2;auto.

apply hd_red_incl_red. 
 unfold hd_red_SCC'  in H0. unfold hd_red.
do 3 destruct H0.
exists x1;exists x2;exists x3.
rewrite  SCC_list_exact.
intuition.
Qed.


Lemma red_mod_SCC_trivial_empty : WF (red_mod R nil).
Proof.
unfold WF;intro;
apply SN_intro;intros.
do 2 destruct H.
do 4 destruct H0. simpl in *;tauto.
Qed.

Lemma WF_chain_SCC_trivial i : SCC'_list i=nil -> WF (chain_SCC' i).
Proof.
intros.
eapply WF_incl.
apply chain_SCC'_red_mod.
rewrite H.
apply red_mod_SCC_trivial_empty.
Qed.
 

Lemma red_mod_SCC_trivial_singl i r : SCC'_list i = (r::nil) -> ~ODPG r r ->  WF (chain_SCC' i).
Proof.
intros.
unfold WF. intros.
apply SN_intro. intros y Hy.
apply SN_intro. intros z Hz.
cut (DPG r r). intro. assert False;try tauto. apply H0.
apply  over_DPG;auto.

assert (In r (SCC'_list i)). rewrite H;simpl;auto.
unfold SCC'_list in H1. rewrite SCC'_list_aux_exact in H1. destruct H1.

eapply chain_dp2_dp_graph; auto; unfold red_mod in *;unfold chain_SCC' in *.
destruct Hy. destruct H3.

 unfold chain_dp. split;auto.
do 4 destruct H4. exists x3.
assert (r=(mkRule x1 x2)). rewrite <- SCC_list_exact in H4. rewrite H in H4; simpl in *;tauto.
rewrite H6;simpl. destruct H5;subst x0.  split; eauto.
 
 unfold chain_dp. split;auto.
destruct Hz. destruct H3.
do 4 destruct H4. exists x3.
assert (r=(mkRule x1 x2)). rewrite <- SCC_list_exact in H4. rewrite H in H4; simpl in *;tauto.
rewrite H6;simpl. destruct H5;subst x0.  split; eauto.
Qed. 
 

End S. 