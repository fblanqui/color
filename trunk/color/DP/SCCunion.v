(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Leo Ducas, 2007-08-06

Modular termination proof through SCC of an over DPGraph
*)

Set Implicit Arguments.

Require Export SCCTopoOrdering.
Require Export AGraph.
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

Variable S : relation (term Sig).
Variable R : rules.
Variable hyp : rules_preserv_vars R.

Notation DPG := (hd_rules_graph S R).

Definition rule_eq_dec := @ATrs.eq_rule_dec Sig.
Definition dim := length R.

Variable ODPG : relation rule.
Variable over_DPG : DPG << ODPG.
Variable restriction : is_restricted ODPG R.
Variable rp_free: repeat_free R.
Variable ODPG_dec : forall x y, {ODPG x y} + {~ ODPG x y }.

Definition hyps := mkSCC_dec_hyps rule_eq_dec restriction rp_free ODPG_dec.

Variables (M : matrix dim dim) (HM : M = SCC_mat_effective hyps) .

Section chain_restriction.

Notation empty := (fun _ _ => False).

Definition proj1_sig2 T P Q (e : @sig2 T P Q) :=
  match e with
    | exist2 a b c => a
  end.

Definition s_SCC's := proj1_sig2 (sorted_SCC' hyps HM).

Notation ODPGquo' :=(Rquo' hyps HM ).
Notation le_ODPGquo' := (le_Rquo' hyps HM).

(** s_SCCs properties *)

Lemma s_SCC's_spec_cover i : i < dim -> In i s_SCC's.

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
rewrite <- H1 in H. assert False. omega. tauto.
Qed.

Lemma s_SCC's_spec_bound i : In i s_SCC's -> i < dim.

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
  SCC'_tag M HM (mkRule l r) = Some i /\ t1 = app s l /\ t2 = app s r.

Lemma hd_red_SCC'_cover t1 t2 : hd_red R t1 t2 ->
  exists i, hd_red_SCC' i t1 t2 /\ i<dim.

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
apply (list_find_first_Some_bound (SCC' (mkRule x x0))
  (SCC'_dec M HM (mkRule x x0)) ).
intuition.
deduce (list_find_first_exist (SCC' (mkRule x x0))
  (SCC'_dec M HM (mkRule x x0)) _ R H).
assert (SCC'_tag M HM (mkRule x x0) <> None). apply H2.
split;try tauto. left;auto.
destruct (SCC'_tag M HM (mkRule x x0)). exists n;auto. congruence.
Qed.


Definition hd_red_Mod_SCC' i :=  S @ hd_red_SCC' i.

Notation union := Relation_Operators.union.

Definition sorted_hd_red_Mod_SCC' := map hd_red_Mod_SCC' s_SCC's.

(** union of chain_SCC' *)

Definition hd_red_Mod_SCC'_union := fold_right (@union (term Sig))
  empty sorted_hd_red_Mod_SCC'.

Lemma union_list_spec : forall (A : Set) L (x y : A) (r : relation A),
  (In r L) -> r x y ->  (fold_right (@union A) empty L) x y.

Proof.
intros.
induction L.
simpl in *;tauto.
simpl in *.
destruct H. destruct H.
subst;left;auto.
right;tauto.
Qed.

Lemma union_list_spec2 : forall (A : Set) L (x y : A),
  fold_right (@union A) empty L x y -> exists r, In r L /\ r x y.

Proof.
intros.
induction L.
simpl in *;tauto.
simpl in *.
destruct H. exists a;split;tauto.
destruct (IHL H). exists x0.
split;try tauto.
Qed.

Theorem hd_red_Mod_SCC'_cover : hd_red_Mod S R << hd_red_Mod_SCC'_union.

Proof.
unfold inclusion.
intros.
unfold hd_red_Mod_SCC'_union in H.
unfold hd_red_Mod in H.
do 2 destruct H.
deduce (hd_red_SCC'_cover H0).
destruct H1 as [i].
assert (hd_red_Mod_SCC' i x y).
exists x0;tauto. 
unfold hd_red_Mod_SCC'_union.
eapply union_list_spec;eauto.
unfold sorted_hd_red_Mod_SCC'.
apply in_map.
apply s_SCC's_spec_cover;tauto.
Qed.

(** properties of the total order RT relatively to restricted chain *)

Notation RT_ODPG := (RT hyps HM).

Lemma compose_empty : forall i j, RT_ODPG i j ->
  hd_red_Mod_SCC' j @ hd_red_Mod_SCC' i << empty.

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
deduce (@Rquo_restricted hyps M HM j i).
split;try split;try tauto; destruct H2;try tauto.
unfold irreflexive in *. intuition. destruct H3;intuition. apply (H7 i).
eapply H5;eassumption.

assert (ODPGquo' j i). 
unfold Rquo'. intuition.
unfold Rquo in *.
unfold hd_red_Mod_SCC' in *.
destruct H0 as [x']. destruct H0.
destruct H1 as [z']. destruct H1.
destruct H3 as [t1]. destruct H3 as [r1]. destruct H3 as [s1].
exists (mkRule t1 r1); split;try tauto.
destruct H4 as [t2]. destruct H4 as [r2]. destruct H4 as [s2].
exists (mkRule t2 r2); split;try tauto.
apply (over_DPG ).
eapply hd_red_Mod_rule2_hd_rules_graph;intuition. unfold hd_red_Mod_rule.

split. assert (SCC' (mkRule t1 r1) (mkRule t1 r1)).
rewrite (SCC'_tag_exact hyps HM ).
split;try tauto. congruence. destruct H7. tauto.
exists s1. subst x'. split;simpl;auto;eauto. intuition.

split. assert (SCC' (mkRule t2 r2) (mkRule t2 r2)).
rewrite (SCC'_tag_exact hyps HM ) .
split;try tauto. congruence. destruct H7;tauto.
exists s2. subst z. split;simpl;auto;eauto. congruence.

subst j.
unfold RT in *.
destruct (topo_sortable_Rquo'). simpl in *.
deduce (l (nfirst_list dim)). clear l.
destruct H3. intuition. unfold irreflexive in H6. deduce (H6 i). auto.
tauto.
Qed.

(** Proof of the Modular termination criterion *)

Require Export Union.

Lemma sort_transitive : forall (B : Set) (a : B) L rel,
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

Lemma In_map_elim_Type : forall (A B : Type) (f : A->B),
  forall x l, In x (map f l) -> exists y, In y l /\ x = f y.

Proof.
intros.
induction l; simpl in H. tauto.
destruct H.
exists a; split;simpl; try congruence. left;auto.
destruct IHl. auto. destruct H0.
 exists x0;split;simpl; try congruence. right;auto.
Qed.

Lemma WF_SCC'_union_aux : forall L,
  (forall i, In i L -> WF (hd_red_Mod_SCC' i)) -> sort RT_ODPG L -> 
  WF ((fold_right (@union _) empty) (map hd_red_Mod_SCC' L)).

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
deduce (union_list_spec2 _ _ _ H1). destruct H5 as [r]. destruct H5.

assert (exists b, In b L /\ r = hd_red_Mod_SCC' b).
apply In_map_elim_Type;auto.
destruct H7 as [b]. destruct H7;subst r.
cut (RT_ODPG a b). intro. eapply (compose_empty H8 ). exists z; eauto.
eapply sort_transitive. unfold RT; destruct topo_sortable_Rquo'. simpl in *. 
deduce (l (nfirst_list dim)).
destruct H8. intuition.
eassumption. auto.

apply IHL. intros. apply H. right;auto.
destruct H0;auto. apply H. left;auto.
Qed.

Lemma WF_SCC'_union :
  (forall i, i<dim -> WF (hd_red_Mod_SCC' i)) -> WF (hd_red_Mod S R).

Proof.
intros.
eapply WF_incl.
apply hd_red_Mod_SCC'_cover.
unfold hd_red_Mod_SCC'_union, sorted_hd_red_Mod_SCC'. 
eapply WF_SCC'_union_aux.
intros. apply H. apply  s_SCC's_spec_bound. auto.
unfold s_SCC's; destruct sorted_SCC'. simpl in *. auto.
Qed.

End chain_restriction.

Fixpoint SCC'_list_aux i L {struct L} :=
  match L with
    | nil => nil
    | x :: q =>
      match eq_opt_nat_dec (SCC'_tag hyps HM x) (Some i) with
        | left _ => x :: @SCC'_list_aux i q
        |right _ => @SCC'_list_aux i q
      end
  end.

Lemma SCC'_list_aux_exact : forall i L r,
  In r (SCC'_list_aux i L) <-> In r L /\ SCC'_tag hyps HM r = Some i.

Proof.
intros.
induction L.
simpl in *. tauto.

split; intro.
simpl in *.
destruct (eq_opt_nat_dec (SCC'_tag hyps HM a) (Some i));
destruct (rule_eq_dec a r); simpl in *; intuition.
subst a; tauto.

destruct H.
simpl in *.
destruct (eq_opt_nat_dec (SCC'_tag hyps HM a) (Some i));
destruct H; simpl in *; try subst a;tauto.
Qed.

Lemma repeat_free_SCC'_list_aux : forall i L, 
  repeat_free L -> repeat_free (SCC'_list_aux i L).

Proof.
induction L; intros; simpl. tauto.
simpl in H. destruct H.
destruct (eq_opt_nat_dec (SCC'_tag hyps HM a) (Some i));try tauto.
split. rewrite SCC'_list_aux_exact. tauto.
 tauto.
Qed.

Definition SCC'_list i := SCC'_list_aux i R.

Lemma SCC'_list_exact : forall i r,
  In r (SCC'_list i) <-> SCC'_tag hyps  HM r = Some i.

Proof.
intros;split;intro.
unfold SCC'_list in H.
rewrite SCC'_list_aux_exact in H. tauto.

unfold SCC'_list;rewrite SCC'_list_aux_exact;split;try tauto.
assert (SCC' hyps r r).
rewrite (SCC'_tag_exact hyps HM).
intuition. congruence. unfold SCC' in H0.
tauto.
Qed.

Lemma repeat_free_SCC'_list : forall i, repeat_free (SCC'_list i).

Proof.
unfold SCC'_list;intros.
apply repeat_free_SCC'_list_aux. auto.
Qed.
 
Lemma chain_SCC'_red_Mod : forall i,
  hd_red_Mod_SCC' i << hd_red_Mod S (SCC'_list i).

Proof.
unfold inclusion; intros.
do 2 destruct H.
exists x0. split. auto.

unfold hd_red_SCC'  in H0. unfold hd_red.
do 3 destruct H0.
exists x1;exists x2;exists x3.
rewrite  SCC'_list_exact.
intuition.
Qed.

(** A faster way to compute SCC'_list but only half-certified *)

Definition SCC_list_fast i (Hi : i < dim) :=
  listfilter R (list_of_vec (Vnth M Hi)).

Lemma list_find_first_exact : forall (B : Set) (P : B -> Prop) P_dec l i,
  list_find_first P P_dec l = Some i ->
  exists z, (element_at l i) = Some z /\ P z.

Proof.
induction l;intros.
simpl in H. discriminate.
simpl in H. destruct (P_dec a).
inversion H. exists a;subst;simpl;tauto.

destruct(list_find_first P P_dec l);try discriminate.
inversion H;subst.
simpl.
apply IHl;auto.
Qed.

Lemma incl_SCC_list_fast i (Hi : i < dim) :
  Vnth (Vnth M Hi) Hi = true -> incl (SCC'_list i) (SCC_list_fast Hi).

Proof.
intros.
assert(M[[i,i]] = true).
unfold mat_unbound;destruct (le_gt_dec dim i). cut False;try tauto;omega.
assert (g=Hi). unfold gt in *; apply lt_unique. subst;auto.

unfold incl. intros. rewrite SCC'_list_exact in H1.
unfold SCC'_tag in H1. simpl in *.
deduce (list_find_first_exact _ _ _ H1).
destruct H2 as [r]; destruct H2; destruct H3; destruct H3. 
subst a. unfold SCC_list_fast. eapply listfilter_in. eauto.
rewrite <- H. apply list_of_vec_exact.
destruct H4; deduce (eq_In_find_first _ _ rule_eq_dec H4); do 2 destruct H6.

assert (x<dim). unfold dim. eapply list_find_first_Some_bound. eauto.

unfold SCC_list_fast. eapply listfilter_in. eauto.

assert ((M [[i, x]]) = true). rewrite HM. 
deduce (sym_SCC H3). clear H3. rename H9 into H3.
 rewrite  (SCC_effective_exact hyps HM) in H3.
unfold SCC_effective in H3. simpl in H3.
unfold nattodom in H3. simpl in *. rewrite H6 in H3. 
deduce (eq_In_find_first _ _ rule_eq_dec H5).
do 2 destruct H9. rewrite H9 in H3.

assert (i=x0). eapply repeat_free_unique; eauto. subst x0.
unfold gofmat in H3. rewrite HM in H3. auto.

unfold mat_unbound in H9 ;destruct (le_gt_dec dim i). cut False;try tauto;omega.
destruct (le_gt_dec dim x). cut False;try tauto;omega.
rewrite <- H9. unfold gt in *. 
assert (g=Hi). apply lt_unique. subst g; apply list_of_vec_exact.
Qed.

Lemma hd_red_Mod_SCC'_hd_red_Mod_fast : forall i (Hi : i < dim),
  Vnth (Vnth M Hi) Hi = true ->
  hd_red_Mod_SCC' i << hd_red_Mod S (SCC_list_fast Hi).

Proof.
intros.
eapply incl_trans.
apply chain_SCC'_red_Mod.
deduce (incl_SCC_list_fast Hi H).
unfold inclusion;intros.
destruct H1 as [z];exists z. destruct H1;split;auto.
do 4 destruct H2. destruct H3.
exists x0;exists x1;exists x2; split;try split;try tauto.
apply H0. auto.
Qed.

(** Somme lemma to proof trivial case of sub-problem termination *)

Lemma red_Mod_SCC_trivial_empty : WF (hd_red_Mod S nil).

Proof.
unfold WF;intro;
apply SN_intro;intros.
do 2 destruct H.
do 4 destruct H0. simpl in *;tauto.
Qed.

Lemma WF_chain_SCC_trivial : forall i,
  SCC'_list i = nil -> WF (hd_red_Mod_SCC' i).

Proof.
intros.
eapply WF_incl.
apply chain_SCC'_red_Mod.
rewrite H.
apply red_Mod_SCC_trivial_empty.
Qed.

Lemma red_Mod_SCC_trivial_singl : forall i r,
  SCC'_list i = r :: nil -> ~ODPG r r ->  WF (hd_red_Mod_SCC' i).

Proof.
intros.
unfold WF. intros.
apply SN_intro. intros y Hy.
apply SN_intro. intros z Hz.
cut (DPG r r). intro. assert False;try tauto. apply H0.
apply  over_DPG;auto.

assert (In r (SCC'_list i)). rewrite H;simpl;auto.
unfold SCC'_list in H1. rewrite SCC'_list_aux_exact in H1. destruct H1.

eapply hd_red_Mod_rule2_hd_rules_graph; auto; unfold red_mod in *;
unfold hd_red_Mod_SCC' in *.
destruct Hy. destruct H3.

unfold hd_red_Mod_rule. split;auto.
do 4 destruct H4. exists x3.
assert (r=(mkRule x1 x2)). rewrite <- SCC'_list_exact in H4. rewrite H in H4;
simpl in *;tauto.
rewrite H6;simpl. destruct H5;subst x0.  split; eauto.
 
unfold hd_red_Mod_rule. split;auto.
destruct Hz. destruct H3.
do 4 destruct H4. exists x3.
assert (r=(mkRule x1 x2)). rewrite <- SCC'_list_exact in H4. rewrite H in H4;
simpl in *;tauto.
rewrite H6;simpl. destruct H5;subst x0.  split; eauto.
Qed.

Lemma WF_hd_red_Mod_SCC_fast_trivial : forall i (Hi : i < dim),
  SCC_list_fast Hi = nil -> WF( hd_red_Mod_SCC' i).

Proof.
intros i Hi;intros.
set (L:=SCC'_list i).
assert (L=SCC'_list i);auto. destruct L.
apply WF_chain_SCC_trivial. auto.
destruct L.
destruct (ODPG_dec h h).
assert (R [i] =Some h).
assert (In h (SCC'_list i)). rewrite <-H0;simpl;auto.
rewrite SCC'_list_exact in H1. generalize H1;intro.
unfold SCC'_tag in H1. simpl in *. 
deduce (list_find_first_exact _ _ _ H1).
do 2 destruct H3.
rewrite (SCC'_tag_exact hyps  HM) in H4.
intuition. cut (x=h). intro;subst x;auto.
rewrite H5 in H2. rewrite <- SCC'_list_exact in H2.
rewrite <-H0 in H2;simpl in *. intuition.

cut (M[[i,i]]=true). intros.
unfold mat_unbound in H2.
destruct (le_gt_dec dim i);try discriminate.
unfold gt in *;assert (g=Hi). apply lt_unique. subst g.
deduce (incl_SCC_list_fast Hi H2).
rewrite H in *. rewrite <- H0 in *. unfold incl in H3.
deduce (H3 h). simpl in *. tauto.
assert (SCC ODPG h h). split;apply t_step;auto.
rewrite (SCC_effective_exact hyps HM) in H2.
unfold SCC_effective in H2. simpl in *. unfold nattodom in H2.
deduce (restriction o);intuition.
deduce (eq_In_find_first _ _ rule_eq_dec H4).
do 2 destruct H3.
deduce(@repeat_free_unique rule R h rp_free _ _ H1 H6). subst x.
rewrite H3 in H2. intuition.

eapply red_Mod_SCC_trivial_singl ;eauto.
 
deduce(repeat_free_SCC'_list i).
rewrite <-H0 in H1;simpl in H1;intuition. clear H1 H4 H5.
assert(In h (SCC'_list i));assert(In h0 (SCC'_list i)); try rewrite <- H0;
simpl;auto.
rewrite SCC'_list_exact in *. rewrite <- H2 in H1.
assert (SCC' hyps h h0). rewrite (SCC'_tag_exact hyps HM);auto. split;congruence.
destruct H4. destruct H4. assert False;auto. tauto.
rewrite H2 in H1. unfold SCC'_tag in *. 
deduce (In_find_first2 _ _ _ (SCC'_dec hyps HM h0) H2).
deduce (In_find_first2 _ _ _ (SCC'_dec hyps HM h) H1).
do 2 destruct H6. do 2 destruct H7. simpl in *.
assert (x=x0). congruence. subst x0.

assert (SCC ODPG x x).
destruct(rule_eq_dec x h). subst h.
eapply trans_SCC.  apply H4. apply sym_SCC.  apply H4.
do 2 destruct H9; try subst x;try tauto. simpl in *.
eapply trans_SCC. apply sym_SCC.  apply H9.  apply H9.
cut (M[[i,i]]=true). intros.
unfold mat_unbound in H11.
destruct (le_gt_dec dim i). cut False;try tauto;omega.
unfold gt in *. assert (g=Hi). apply lt_unique. subst g.
deduce (incl_SCC_list_fast Hi H11).
rewrite H in *. rewrite <- H0 in *. unfold incl in H12.
deduce (H12 h). simpl in *. tauto.

rewrite (SCC_effective_exact hyps HM) in H10.
unfold SCC_effective in H10. simpl in *. unfold nattodom in H10.
assert (In x R ). eapply element_at_in. exists i;auto.
deduce (eq_In_find_first _ _ rule_eq_dec H11).
do 2 destruct H12.
deduce(@repeat_free_unique rule R _ rp_free _ _ H13 H6). subst x0.
rewrite H12 in H10. intuition.
Qed.

End S.

Ltac use_SCC_tag h M S R t :=
  let x := fresh in
    set (x := (SCC_tag_fast h M t));
      normalize_in x (SCC_tag_fast h M t);
      match (eval compute in x) with
        | Some ?X1 =>
          let Hi := fresh in
            assert (Hi : X1 < dim R);
              normalize (dim R);
              [omega |
                let L:=fresh in
                  set (L := (SCC_list_fast R M Hi));
                    normalize_in L (SCC_list_fast R M Hi);
                    assert (WF(hd_red_Mod S L)); subst L];
              clear x; clear Hi
        | ?X2 => idtac
      end.

Ltac use_SCC_hyp h M R Hi := 
  let b:=fresh in
    set (b := Vnth (Vnth M Hi) Hi);
      normalize_in b (Vnth (Vnth M Hi) Hi);
      match (eval compute in b) with
        | false => apply WF_hd_red_Mod_SCC_fast_trivial with (Hi:=Hi);
          eauto;clear b
        | true => eapply WF_incl;
          [eapply hd_red_Mod_SCC'_hd_red_Mod_fast with (Hi:=Hi) | auto];
	  auto;clear b
      end.

Ltac use_SCC_all_hyps h m R i Hi Hj :=
  let rec aux x :=
    match x with
      | 0 => elimtype False; omega
      | S ?y => destruct i; [use_SCC_hyp h m R Hi | aux y]
    end in	
    match (type of Hj) with
      | le ?X ?Y => aux Y
    end.

Ltac SCC_name n1 n2 :=
  match goal with 
    | |- WF (chain ?R) => set (n1 := (dp R)); set (n2 := int_red R #)
    | |- WF (hd_red_mod ?E ?R) => set (n1 := R); set (n2 := red E #)
    | |- WF (?X @ hd_red ?R) => set (n1 := R); set (n2 := X)
    | |- WF (hd_red_Mod ?E ?R) => set (n1 := R); set (n2 := E)
  end.

Implicit Arguments WF_SCC'_union [Sig R ODPG M].
 
