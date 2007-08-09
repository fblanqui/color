(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Leo Ducas, 2007-08-06

SCCTopoOrdering
*)

(** We build here the quotient graph by the relation SCC, which is Topo Sortable *)

Set Implicit Arguments.

Require Export SCC_dec.

Section SCC_quotient.

Variable hyps : TSCC_dec_hyps.

Notation A:=(hyp_A hyps).
Notation A_eq_dec:=(hyp_A_eq_dec hyps).
Notation Dom:=(hyp_Dom hyps).
Notation R:=(hyp_R hyps).
Notation restriction:=(hyp_restriction hyps).
Notation rp_free:=(hyp_rp_free hyps).
Notation R_dec:=(hyp_R_dec hyps).
Notation dim := (length Dom).
Variables 
	(M : matrix dim dim)
  (HM: M= SCC_mat_effective hyps) .
(* We represent the quotient of the Domain by SCC with a function to nat *)
Notation SCC:=(SCC R).
Notation SCC_dec := (SCC_effective_dec hyps HM).

(** We give a second definition of SCC :SCC' now isolated points are also considered as SCC
(refl cosure) *)
Definition SCC' x y:= (SCC %) x y/\ In x Dom /\ In y Dom.

Lemma In_dec (x:A) l: {In x l}+{~ In x l}.
Proof. 
intros.
induction l.
auto.
simpl.
destruct (A_eq_dec a x);auto.
destruct IHl.
left;auto.
right;tauto.
Defined.

Lemma SCC'_dec : forall x y, {SCC' x y} + {~SCC' x y}.
Proof.
intros.
unfold SCC'.
unfold clos_refl.
destruct (A_eq_dec x y);auto.
subst; destruct (In_dec y Dom).
left;auto.
right;tauto.
destruct (SCC_dec x y);
destruct (In_dec y Dom);destruct (In_dec x Dom);
rewrite <- SCC_effective_exact in *; try tauto.
Defined.

Lemma trans_SCC' : forall x y z, SCC' x y -> SCC' y z -> SCC' x z.
intros.
unfold SCC' in *.
destruct H;destruct H0.
split;try split;try tauto.
destruct H;destruct H0;subst;auto.
left;auto.
right;auto.
right;auto.
right;eapply trans_SCC.
eauto. assumption.
Qed.

Lemma sym_SCC' : forall x y ,SCC' x y -> SCC' y x.
Proof.
intros;destruct H.
split;try tauto.
destruct H.
left;auto.
right;apply sym_SCC;auto.
Qed.

(* SCC'_tag map each vertex of the graph to its SCC number *)
Definition SCC'_tag x := list_find_first (SCC' x) (SCC'_dec x) Dom.


Lemma In_find_first2 (l:list A) P P_dec z:
 list_find_first P P_dec l = Some z -> exists y, element_at l z= Some y /\ P y.
Proof.
intros l P P_dec; induction l;intros.
simpl in H. discriminate;tauto.
simpl in H.
destruct (P_dec a).
inversion H;subst.
exists a;simpl;split; auto.
destruct ( list_find_first P P_dec l);try discriminate;try tauto.
assert (Some n0=Some n0).
trivial.
deduce (IHl n0 H0).
destruct H1.
exists x.
inversion H.
simpl;auto.
Qed.


Lemma SCC'_tag_exact x y: SCC' x y <-> SCC'_tag x = SCC'_tag y /\ SCC'_tag x <> None.
Proof.
intros.
split;intros.
unfold SCC'_tag in *.
split.
apply list_find_first_indep.
intros.
split;intros;eapply trans_SCC';auto;eauto.
apply  sym_SCC';auto.
eapply list_find_first_exist;unfold SCC' in *.
Focus 2. eassumption.
tauto.

destruct H.
assert (exists n, SCC'_tag x = Some n).
destruct (SCC'_tag x);try tauto.
exists n;tauto.
destruct H1.
generalize H1;intro.
rewrite H in H2.

unfold SCC'_tag in H1.
unfold SCC'_tag in H2.

deduce (In_find_first2 _ _ _ H1).
deduce (In_find_first2 _ _ _ H2).
destruct H3;destruct H4.
destruct H3;destruct H4.
rewrite H3 in H4.
inversion H4.
subst x1.
eapply trans_SCC'.
eassumption.
apply sym_SCC'.
auto.
Qed.

Check Vcons.
(* faster way to compute SCC'_tag but not certified *)
Fixpoint bools_find_first n (v : vector bool n) {struct v} := match n with
  |0 => None
  |S i => match v with
    |Vnil => None
    |Vcons true i w =>Some 0
    |Vcons false i w => match bools_find_first w with 
       |None => None
       |Some r => Some (S r)
       end
    end
  end.

Definition SCC_tag_fast M t := 
  let oi:= list_find_first (eq t) (A_eq_dec t) Dom in
  match oi with 
  |None => None
  |Some i => match le_gt_dec dim i with
     |right Hi => @bools_find_first dim (Vnth M Hi)
     |left _ => None
     end
   end.





(* Quotient relation *)


Definition Rquo (x y :nat) :=
exists r, SCC'_tag r = Some  x /\ exists s,  SCC'_tag s = Some y /\ R r s.

Lemma Rquo_restricted : is_restricted Rquo (nfirst_list dim).
Proof.
unfold is_restricted;intros.
do 2 rewrite nfirst_exact.
unfold Rquo in H.
do 2 destruct H. do 2 destruct H0. unfold SCC'_tag in *.
split;  eapply list_find_first_Some_bound;eauto.
Qed.

Lemma eq_opt_nat_dec (x y : option nat) : {x=y} + {~x= y}.
Proof.
intros.
destruct x;destruct y.
destruct (eq_nat_dec n n0);auto.
right;auto;intuition.
inversion H;tauto.
right;discriminate.
right;discriminate.
left;auto.
Defined.



Lemma exists_in_list_dec (L : list A) P (P_dec :forall r, {P r}+{~P r}) :
 {exists r, P r /\ In r L } + {~exists r, P r /\ In r L }.
Proof.
intros. 
induction L.
right. intuition.
do 2 destruct H;simpl in H;auto.
destruct (P_dec a).
left;exists a;simpl;auto.
destruct IHL.
 left. destruct e. exists x.
simpl;tauto.

right;intuition.
do 2 destruct H.
simpl in H0. destruct H0. subst;tauto.
apply n0.
exists x;auto.
Defined.


(** Decidability of the quotient relation *)
Lemma Rquo_dec x y : {Rquo x y} + {~Rquo x y}.
Proof.
intros;simpl in *.
unfold Rquo.
cut(
{(exists r : A,
    SCC'_tag r = Some x /\ (exists s : A, SCC'_tag s = Some y /\ R r s) /\ In r Dom)} +
{~
 (exists r : A,
    SCC'_tag r = Some x /\ (exists s : A, SCC'_tag s = Some y /\ R r s) /\ In r Dom)} ).
intro.
destruct H.
left; destruct e;exists x0;tauto.
right. intuition.
apply n.
do 2 destruct H.
exists x0;intuition.
destruct H0;deduce (restriction x0 x1).
tauto.
cut (
{(exists r : A,
    (fun t =>SCC'_tag t = Some x /\
    (exists s : A, SCC'_tag s = Some y /\ R t s)) r /\ In r Dom)} +
{~
 (exists r : A,
    (fun t =>SCC'_tag t = Some x /\
    (exists s : A, SCC'_tag s = Some y /\ R t s)) r /\ In r Dom)}).

intro.
destruct H.  left;destruct e;auto. exists x0. intuition.
right. intuition. apply n. destruct H. exists x0. intuition.
 
apply exists_in_list_dec.
intros.

destruct (eq_opt_nat_dec (SCC'_tag r) (Some x)).
Focus 2.
right. tauto.
cut ({ (exists s : A, SCC'_tag s = Some y /\ R r s)} +
{~ (exists s : A, SCC'_tag s = Some y /\ R r s)}).
intros. destruct H.  left. intuition. right; intuition.

change ({(exists s : A,(fun t => SCC'_tag t = Some y /\ R r t) s)} +
{~ (exists s : A,(fun t => SCC'_tag t = Some y /\ R r t) s)}).
assert (
{(exists s : A, (fun t : A => SCC'_tag t = Some y /\ R r t) s /\ In s Dom)} +
{~ (exists s : A, (fun t : A => SCC'_tag t = Some y /\ R r t) s /\In s Dom) }).

apply exists_in_list_dec.

intro; destruct (eq_opt_nat_dec (SCC'_tag r0) (Some y));
destruct(R_dec r r0).
left; auto. right;tauto. right;tauto. right;tauto.

destruct H.
left; destruct e0;exists x0;tauto.
right;intuition;apply n.
destruct H.
exists x0;intuition.
deduce (restriction r x0);tauto.
Defined.


(** This new relation will be acyclic *)
Definition Rquo' x y := Rquo x y /\ x <> y.

Lemma Rquo'_dec x y : {Rquo' x y} + {~Rquo' x y}.
Proof.
unfold Rquo';intros;destruct (eq_nat_dec x y);destruct (Rquo_dec x y);auto;
right;tauto.
Defined.


Require Export Total.

(** A path in the quotient relation gives a path in the relation *)
Lemma Rquo'_path L x y: is_path Rquo' x y L -> 
exists r, SCC'_tag r = Some x /\ exists s,  SCC'_tag s = Some y /\ R! r s.
Proof.
induction L;intros;simpl in *.
unfold Rquo',Rquo in H.
do 2 destruct H.
exists x0;intuition.
destruct H2;exists x1;intuition.

destruct H.
unfold Rquo',Rquo in H.
do 2 destruct H.
exists x0;intuition.
destruct H3;destruct H.

deduce (IHL _ _ H0).
do 2 destruct H4.
do 2 destruct H5;exists x3.
intuition.
eapply t_trans;eauto.
destruct (A_eq_dec x1 x2).
subst x1.
apply t_step. auto.
eapply t_trans.
apply t_step. eauto.

cut (SCC' x1 x2).
intros.
do 2 destruct H7;try tauto.
destruct H7;auto.

rewrite SCC'_tag_exact.
intuition.
congruence.
rewrite H in H7.
discriminate.
Qed.

(** Rquo' is acyclic *)
Lemma irrefl_tc_Rquo' : irreflexive (Rquo'!).
Proof.
unfold irreflexive. intuition.
deduce (clos_trans_path H).
destruct H0 as [L]. destruct L.
simpl in H0;destruct H0;auto.

simpl in H0;destruct H0. deduce (Rquo'_path L n x H1).
do 2 destruct H2. do 2 destruct H3.
unfold Rquo' in H0. destruct H0. unfold Rquo in H0.
do 2 destruct H0. do 2 destruct H6.
cut (R! x3 x2). intro. cut (x=n). intuition.
cut (SCC' x3 x2). intro. rewrite  SCC'_tag_exact in H9.
destruct H9;congruence.

unfold SCC'. intuition;deduce (restriction x2 x3);try tauto.
right. split;auto. apply t_step;auto.

cut((R #) x3 x2). intro.
deduce (rtc_split H8).
destruct H9;try tauto.
subst x3;congruence.

assert (R# x3 x0). cut (SCC' x3 x0).
intro. do 2 destruct H8. subst x3;intuition.
destruct H8. apply ( tc_incl_rtc ). intuition.

rewrite  SCC'_tag_exact. split. congruence. rewrite H6. discriminate.

eapply (rt_trans); eauto.
assert (R# x0 x1). apply ( tc_incl_rtc ). intuition.

eapply (rt_trans); eauto.
cut (SCC' x1 x2). intro. do 2 destruct H10.
subst x1;intuition. destruct H10.
apply ( tc_incl_rtc ). intuition.
rewrite  SCC'_tag_exact.
split. congruence.
rewrite H3. discriminate.
Qed.
 

(** Rquo' is topo_sortable *)
Lemma topo_sortable_Rquo' : topo_sortable Rquo'.
Proof.
apply antisym_topo_sortable_topo_sortable.
apply possible_antisym_topo_sort;auto.
unfold eq_dec; apply eq_nat_dec.
unfold rel_dec; apply Rquo'_dec.
apply irrefl_tc_Rquo'.
Qed. 


Require Export Heap.
Require Export Sorting.

(** We will now sort the SCC in the sens of list *)
(* We need an order on a whole type *)
Definition bnat := { x : nat | x < dim}. 


(** Lots of technical meaningless lemmas *)
Lemma eq_bnat_dec (x y:bnat) :{x = y} + {x<> y}.
Proof.
intros.
destruct (eq_nat_dec (proj1_sig x) (proj1_sig y));
unfold proj1_sig in *.
destruct x. destruct y.
subst;simpl. left.
cut (l=l0). intro;subst. intuition.
apply lt_unique.
destruct x. destruct y.
right;intuition;inversion H;tauto.
Defined.

Lemma bnat_spec x: x<dim <-> exists y:bnat,  (proj1_sig y)=x.
Proof.
split;intro.
Focus 2.
destruct H. destruct x0. simpl in *. intuition.
exists (exist (fun x => x<dim) x H). simpl. refl.
Qed.


Lemma lt_ge_dec x y : {x<y} + { x>= y}.
Proof.
intros.
destruct (lt_eq_lt_dec x y); auto;try destruct s;auto with *.
Defined.

Fixpoint natlist_to_bnatlist L := match L with
  | nil => nil
  | x::q => match lt_ge_dec x dim with 
     |left H =>(exist (fun x => x<dim) x H)::natlist_to_bnatlist q
     |right _ => natlist_to_bnatlist q
     end
  end.
 
Definition bnatlist :=  (natlist_to_bnatlist (nfirst_list dim)).

Lemma natlist_to_bnatlist_spec x L (H:x<dim) : In x L -> In (exist (fun x => x<dim) x H) 
(natlist_to_bnatlist L).
Proof.
intros.
induction L.
simpl in H0;tauto.
simpl.
destruct(lt_ge_dec a dim).
simpl.
simpl in H0; destruct H0. subst.

left.
deduce (lt_unique l H);subst;auto.
right;tauto.

simpl in H0; destruct H0. subst.
cut False;try tauto;try omega.
tauto.
Qed.


Lemma bnatlist_exact (x:bnat) : In x bnatlist.
Proof.
intros.
unfold bnatlist. destruct x. apply natlist_to_bnatlist_spec.
rewrite nfirst_exact. auto.
Qed.

Definition le_Rquo' (x y :nat) :=  ~Rquo'! y x /\ x<dim /\ y < dim.

Lemma sort_incl_aux (B : Set) (T S:relation B) a L : T<< S -> lelistA T a L  -> lelistA S a L.
Proof.
induction L;intros. intuition.
destruct H0;intuition.
Qed.

Lemma sort_incl (B:Set) (T S:relation B) L : T<< S -> sort T L -> sort S L.
Proof.
intros;induction L. intuition.
inversion H0.
apply cons_sort;intuition.
subst.
eapply sort_incl_aux;eassumption.
Qed.

Lemma map_lelistA_bnat_to_nat RT (a:bnat) L :
lelistA (fun x y : bnat => RT (proj1_sig x) (proj1_sig y)) a L ->
lelistA RT (proj1_sig a) (map (fun y:bnat =>proj1_sig y) L).
Proof.
induction L;intros.
simpl;apply nil_leA.
simpl.
inversion H;subst.
apply cons_leA;auto.
Qed.

Lemma map_sort_bnat_to_nat RT L : 
sort  (fun x y : bnat => RT (proj1_sig x) (proj1_sig y)) L ->
sort RT (map (fun y:bnat =>proj1_sig y) L).
Proof.
induction L;intros.
simpl;apply nil_sort.
simpl.
inversion H; apply cons_sort;try tauto.
apply  map_lelistA_bnat_to_nat.
intuition.
Qed.

Require Export Permutation.
Require Export Multiset.

Section multiplicity.
Lemma nfirst_multiplicity n i : multiplicity (list_contents (@eq nat) eq_nat_dec (nfirst_list n)) i = 
if lt_ge_dec i n then 1 else 0.
Proof. 
induction n;intros. simpl.
destruct (lt_ge_dec i 0);omega.
simpl.
rewrite IHn.
destruct(lt_ge_dec i n);destruct(eq_nat_dec n i);destruct(lt_ge_dec i (S n));try omega.
Qed.

Lemma bnfirst_multiplicity n (i:bnat) :
 multiplicity (list_contents (@eq bnat) eq_bnat_dec (natlist_to_bnatlist (nfirst_list n))) i = 
if lt_ge_dec (proj1_sig i) n then 1 else 0.
Proof.
destruct i as [i hi].
simpl.
induction n.
simpl.
destruct (lt_ge_dec i 0);omega.

simpl;destruct(lt_ge_dec n dim);simpl; rewrite IHn;destruct(eq_nat_dec n i);
destruct(lt_ge_dec i n);destruct(lt_ge_dec i (S n));subst;simpl;try omega;try congruence.

destruct(eq_bnat_dec (exist (fun x : nat => x < dim) i l) (exist (fun x : nat => x < dim) i hi));try omega.
deduce (lt_unique l hi);subst; congruence.

destruct(eq_bnat_dec (exist (fun x : nat => x < dim) n l) (exist (fun x : nat => x < dim) i hi));
try omega; congruence.

destruct(eq_bnat_dec (exist (fun x : nat => x < dim) n l) (exist (fun x : nat => x < dim) i hi));
try omega; congruence.

Qed.


Lemma map_multiplicity a (l : a<dim) mb:
  multiplicity (list_contents (eq (A:=bnat)) eq_bnat_dec mb)
       (exist (fun x : nat => x < dim) a l) =
      multiplicity   (list_contents (eq (A:=nat)) eq_nat_dec
     (map (fun y : bnat => proj1_sig y) mb)) a.
Proof.
induction mb.
simpl;auto.
simpl.
rewrite IHmb.
destruct(eq_nat_dec (proj1_sig a0) a);
destruct(eq_bnat_dec a0 (exist (fun x : nat => x < dim) a l));try omega;try congruence.

destruct a0.
simpl in *.
subst.
deduce (lt_unique l l0).
congruence.

destruct a0.
simpl in *.
congruence.
Qed.

Lemma lemme_foo a (H:a>=dim) mb: 
multiplicity (list_contents (eq (A:=nat)) eq_nat_dec
     (map (fun y : bnat => proj1_sig y) mb)) a =0.
Proof.
induction mb.
simpl;auto.
simpl.
destruct(eq_nat_dec (proj1_sig a0) a).
destruct a0;simpl in *;subst;omega.
simpl. apply IHmb.
Qed.


Lemma rp_free_lelistA_strict (B: Set) a S (mb : list B) (HL :repeat_free (a::mb)) :
lelistA (S %) a mb -> lelistA S a mb.
Proof.
intros.
induction mb;intuition.

simpl in *.
inversion H;subst.
apply cons_leA.
destruct H1;subst;try tauto.
Qed.

Lemma rp_free_sort_strict (B: Set) S (mb : list B) (HL :repeat_free mb) :
sort (S %) mb -> sort S mb.
Proof.
intros.
induction mb.
apply nil_sort.
generalize HL;intro.
simpl in HL0.
inversion H;subst.
assert (sort S mb). tauto. clear IHmb.
apply cons_sort;auto.
apply rp_free_lelistA_strict;auto.
Qed.

Variables 
 (B:Set)
 (B_eq_dec : forall x y : B,{x=y} + {x<>y}).

Lemma In_multiplicity mb a : In a mb ->
multiplicity (list_contents (eq (A:=B)) B_eq_dec mb) a >=1.
Proof.
intros; induction mb;simpl in *;try tauto.
destruct H;destruct (B_eq_dec a0 a);subst;try congruence;simpl;try omega.
tauto.
Qed.


Lemma multiplicity_repeat_free mb : (forall a, 
multiplicity (list_contents (eq (A:=B)) B_eq_dec mb) a <=1 )
-> repeat_free mb.
Proof.
intros.
induction mb;simpl;auto.

simpl in H.
split.
deduce (H a).
intuition.
deduce (In_multiplicity _ _ H1).
destruct(B_eq_dec a a);auto.
omega.
apply IHmb.
intros.
deduce (H a0).
destruct (B_eq_dec a a0);simpl in *;omega.
Qed.

End multiplicity.

(** Definition of a total order on the SCC which include the natural order on SCC*)
Definition RT x y := (proj1_sig  topo_sortable_Rquo') (nfirst_list dim) x y = true.


Lemma Rquo'_incl_RT : Rquo' << RT.
Proof.
  unfold inclusion;intros.
  unfold RT.
  destruct (topo_sortable_Rquo').
  simpl.
  deduce (l (nfirst_list dim)).
  destruct H0.
  intuition.  
  apply H2. 
  generalize H;intro.
    unfold Rquo' ,Rquo,  SCC'_tag in H;
    auto; do 3 destruct H; do 2 destruct H7.
  split;try split; try tauto;
  rewrite (nfirst_exact);eapply list_find_first_Some_bound; eauto.
Qed. 


(** The SCC can be sorted *)
Theorem sorted_SCC' : {m : list nat | sort RT m &
 Permutation.permutation (@eq nat) eq_nat_dec (nfirst_list dim) m}.
Proof.
unfold RT.
destruct topo_sortable_Rquo' as [F HF];simpl.

set (RTb := (fun x y : bnat => (F (nfirst_list dim)  (proj1_sig x) (proj1_sig y)) = true)) in *.
cut ({m : list bnat | sort RTb m & 
Permutation.permutation (eq (A:=bnat)) eq_bnat_dec bnatlist m}).

intro.
destruct H as [mb].
exists (map (fun y:bnat =>proj1_sig y) mb). apply map_sort_bnat_to_nat. intuition.

unfold permutation in *.
unfold meq in *.
intros. rewrite nfirst_multiplicity in *.
destruct (lt_ge_dec a dim).
deduce (p ((exist (fun x => x<dim) a l))).
rewrite (bnfirst_multiplicity dim) in *.
simpl in H. destruct (lt_ge_dec a dim);try omega.
rewrite map_multiplicity in H;auto.
rewrite lemme_foo;auto.

cut( {m : list bnat | sort (RTb %) m & 
permutation (eq (A:=bnat)) eq_bnat_dec bnatlist m}).
intro. destruct H as [mb].
exists mb;auto.
apply rp_free_sort_strict;auto.

eapply multiplicity_repeat_free. 
intros.
unfold permutation in *;unfold meq in *.
rewrite <- p.
unfold bnatlist.
rewrite  bnfirst_multiplicity.
destruct (lt_ge_dec (proj1_sig a) dim);omega.


apply treesort.
deduce (HF (nfirst_list dim)). destruct H;intuition.

intros.
unfold total in H4.
destruct x;destruct y.
assert (trichotomy (fun x0 y0 : nat => F (nfirst_list dim) x0 y0 = true)  x x0).
apply H4;rewrite nfirst_exact;auto. 

unfold trichotomy in H3.
destruct (eq_nat_dec x x0). left;left;subst x;auto.
assert (l=l0). apply(lt_unique). subst l;auto. 

assert({F (nfirst_list dim) x x0 = true}+{~F (nfirst_list dim) x x0 = true}).
destruct( F (nfirst_list dim) x x0);auto.

destruct H5.
left;auto. right; auto.
right;auto. right; tauto.

apply rc_trans.
intros.
unfold RTb in *. simpl in *.
deduce (HF (nfirst_list dim)).
destruct H.
intuition.
unfold transitive in *.
intros. eapply H0; eauto.
Qed.

End SCC_quotient.
