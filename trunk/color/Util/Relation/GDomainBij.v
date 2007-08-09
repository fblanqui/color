(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Leo Ducas, 2007-08-06

GDomainBij
*)

(* given a list Dom, we make a bijection between element of Dom and [[0,n-1]],
and relation restricted to Dom with relation restricted to [[1,n]] *)

Set Implicit Arguments.

Require Export ListUtil.
Require Export SCC.
Require Export ListExtras.
Require Export Path.
Require Export Iter.
Require Export AdjMat.
Section Definitions.
Variable A : Set.
Variable A_eq_dec :forall (x:A) (y:A), {x=y} +{~x=y}.
Variable Dom : list A.
Variable R : relation A.
Variable R' :relation nat.


(** Definition of the Bijection of graphs *)
Definition domtonat x y:= 
 match Dom[x] with
 |None => False
 |Some a =>
   match Dom[y] with
   |None => False
   |Some b => R a b
   end
 end.

Definition nattodom x y:=
match list_find_first (eq x) (A_eq_dec x) Dom with
  |None => False
  |Some a =>
  match list_find_first (eq y) (A_eq_dec y) Dom with
   |None => False
   |Some b => R' a b
   end
 end.


End Definitions.

(** Some properties *)
Section bijection.


Lemma eq_In_find_first (A : Set) x l ( A_eq_dec :forall (x:A) (y:A), {x=y} +{~x=y}):
In x l -> exists z, list_find_first (eq x) (A_eq_dec x) l = Some z /\ l[z]=Some x.
intros; induction l.
unfold In in H;tauto.
simpl in H.
destruct (A_eq_dec x a);subst.
exists 0;split;simpl;auto with *.
destruct (A_eq_dec a a); auto with *;tauto.
destruct H;subst;try tauto.

deduce (IHl H);destruct H0 as [z];destruct H0.
exists (S z);split;simpl;auto with *.
destruct (A_eq_dec x a);subst;try tauto.
destruct (list_find_first (eq x) (A_eq_dec x) l);subst;try tauto;
inversion H0;subst;auto.
Qed.

Lemma eq_list_find_first_exact (A : Set) l x z ( A_eq_dec :forall (x:A) (y:A), {x=y} +{~x=y}):
list_find_first (eq x) (A_eq_dec x) l = Some z -> l[z]=Some x.
Proof.
intro;intro.
induction l;intros;simpl in *. discriminate.
destruct (A_eq_dec x a);subst.
inversion H;subst;auto with *.

assert (exists i,list_find_first (eq x) (A_eq_dec x) l=Some i).
destruct (list_find_first (eq x) (A_eq_dec x) l);try discriminate.
exists n0;auto with *.
destruct H0.
deduce(IHl _ _ _ H0).
rewrite H0 in H.
destruct z;inversion H;subst;assumption.
Qed.


Variable A : Set.
Variable A_eq_dec :forall (x:A) (y:A), {x=y} +{~x=y}.
Variable Dom : list A.
Variable R : relation A.

Lemma domtonat_elim  : forall a b, (domtonat Dom R) a b -> exists x,exists y,
R x y /\ Dom [a] = Some x /\ Dom [b] = Some y.
intros.
unfold domtonat in H.
destruct (Dom[a]);destruct (Dom[b]);try discriminate;try tauto.
exists a0;exists a1;intuition; auto.
Qed.




Lemma domtonat_is_restricted : is_restricted (domtonat Dom R) (nfirst_list (length Dom)).
Proof.
unfold is_restricted;intros.
repeat rewrite nfirst_exact;deduce (domtonat_elim x y H).
repeat destruct H0;destruct H1.
deduce(element_at_in2 _ _  H1).
deduce(element_at_in2 _ _  H2).
tauto.
Qed.

Variable restriction : is_restricted R Dom.

Lemma nattodom_elim :forall x y (R' : relation nat),
nattodom A_eq_dec Dom (R') x y -> exists a, exists b,
R' a b /\ Dom [a] = Some x /\ Dom [b] = Some y.
intros;unfold nattodom in H.
assert (exists a, list_find_first (eq x) (A_eq_dec x) Dom =Some a).
destruct (list_find_first (eq x) (A_eq_dec x) Dom ); try tauto.
exists n;auto. destruct H0; subst. rewrite H0 in H.
assert (exists b,list_find_first (eq y) (A_eq_dec y) Dom =Some b).
destruct (list_find_first (eq y) (A_eq_dec y) Dom ); try tauto.
exists n;auto. destruct H1; subst;rewrite H1 in H.
deduce(eq_list_find_first_exact _ _ _  H1).
deduce(eq_list_find_first_exact _ _ _ H0).
exists x0;exists x1;intuition;auto.
Qed.


Lemma nattodom_elim2 :forall x y (R' : relation nat),
nattodom A_eq_dec Dom (R') x y -> exists a, exists b,
R' a b /\ list_find_first (eq x) (A_eq_dec x) Dom = Some a
/\ list_find_first (eq y) (A_eq_dec y) Dom = Some b.

intros;unfold nattodom in H.
assert (exists a, list_find_first (eq x) (A_eq_dec x) Dom =Some a).
destruct (list_find_first (eq x) (A_eq_dec x) Dom ); try tauto.
exists n;auto. destruct H0; subst. rewrite H0 in H.
assert (exists b,list_find_first (eq y) (A_eq_dec y) Dom =Some b).
destruct (list_find_first (eq y) (A_eq_dec y) Dom ); try tauto.
exists n;auto. destruct H1; subst;rewrite H1 in H.
deduce(eq_list_find_first_exact _ _ _ H1).
deduce(eq_list_find_first_exact _ _ _ H0).
exists x0;exists x1;intuition;auto.
Qed.


Lemma dom_change:forall x y,
nattodom A_eq_dec Dom (domtonat Dom R) x y <-> R x y.
intros;split;intro.
deduce (nattodom_elim _ _ _ H).
repeat destruct H0;destruct H1.
unfold domtonat in H0.
rewrite H1 in H0;rewrite H2 in H0;auto.

unfold is_restricted in restriction.
deduce (restriction H);destruct H0.
deduce (eq_In_find_first _ _  A_eq_dec H0);deduce (eq_In_find_first _ _ A_eq_dec H1).
destruct H2;destruct H2;destruct H3;destruct H3.
unfold nattodom.
rewrite H2;rewrite H3.
unfold domtonat.
rewrite H4;rewrite H5;auto.
Qed.

Lemma domtonat_dec ( Rdec :forall x y, {R x y}+{~R x y}): forall x y,
{domtonat Dom R x y}+{~(domtonat Dom R x y)}.
Proof.
intros.
unfold domtonat.
destruct (Dom[x]). destruct (Dom[y]). apply Rdec.
tauto. tauto.
Defined.

End bijection.



(** composition is mapped to composition *)
Section compose.
Variable A : Set.
Variable A_eq_dec :forall (x:A) (y:A), {x=y} +{~x=y}.
Variable Dom : list A.
Variable R R': relation nat.
Variable restriction : is_restricted R (nfirst_list (length Dom)).
Variable restriction' : is_restricted R' (nfirst_list (length Dom)).
Variable rp_free: repeat_free Dom.

Lemma dom_change_compose: forall x y,
nattodom A_eq_dec Dom (R @ R') x y
<-> ((nattodom A_eq_dec Dom R)@ nattodom A_eq_dec Dom R') x y.
intros;split;intro.
deduce (nattodom_elim A_eq_dec _ _ _ _ H).
repeat destruct H0;destruct H1.
unfold compose; deduce (restriction H0); destruct H4.
rewrite nfirst_exact in H5; rewrite element_at_exists in H5.
destruct H5 as [z]; exists z.
deduce (element_at_in2  _ _ H1).
deduce (element_at_in2  _ _ H3).
deduce (element_at_in2  _ _ H5).
unfold nattodom.
destruct H6; clear H9.
destruct H7; clear H9.
destruct H8; clear H9.
deduce (eq_In_find_first _ _ (A_eq_dec) H6);destruct H9;destruct H9.
deduce (eq_In_find_first _ _ (A_eq_dec) H7); destruct H11; destruct H11.
deduce (eq_In_find_first _ _ (A_eq_dec) H8);destruct H13;destruct H13.
deduce (repeat_free_unique _ rp_free _ _ H1 H10).
deduce (repeat_free_unique _ rp_free _ _ H3 H12).
deduce (repeat_free_unique _ rp_free _ _ H5 H14).
subst;rewrite H9;rewrite H11; rewrite H13;auto.

unfold compose in H; destruct H as [z];destruct H.
unfold nattodom in *.
destruct (list_find_first (eq x) (A_eq_dec x));auto with *.
destruct (list_find_first (eq y) (A_eq_dec y));auto with *.
destruct (list_find_first (eq z) (A_eq_dec z));auto with *.
unfold compose;exists n1;auto with *.
tauto.
destruct (list_find_first (eq z) (A_eq_dec z));auto with *.
Qed.

End compose.


(** iteration mapped to iteration *)
Section iter.
Variable A : Set.
Variable A_eq_dec :forall (x:A) (y:A), {x=y} +{~x=y}.
Variable Dom : list A.
Variable R : relation A.
Variable restriction : is_restricted R Dom.
Variable rp_free: repeat_free Dom.

Lemma iter_preserv_restriction : forall n, is_restricted (iter R n) Dom.
intro;induction n;try trivial.
simpl;unfold is_restricted;unfold compose.
intros;destruct H as [z];destruct H.
intuition.
deduce(restriction H);tauto.
deduce(IHn _ _ H0);tauto.
Qed.




Lemma dom_change_iter : forall n x y,
nattodom A_eq_dec Dom (iter (domtonat Dom R) n) x y
<-> (iter R n) x y.
intro n; induction n;intros;simpl.
apply dom_change;auto.
split;intros.
rewrite dom_change_compose in H.
unfold compose in *.
destruct H as [z];destruct H;exists z.
rewrite dom_change in H;rewrite IHn in H0;auto with *.
apply domtonat_is_restricted.
assumption.

unfold compose in H;destruct H as [z];destruct H.
rewrite dom_change_compose.
apply domtonat_is_restricted.
assumption. unfold compose;exists z;split.
rewrite dom_change; assumption.
rewrite IHn;assumption.
Qed. 




Lemma dom_change_tc: forall x y, 
nattodom  A_eq_dec Dom ((domtonat Dom R)!) x y <-> R! x y.

split;intros.

deduce(nattodom_elim2 A_eq_dec _ _ _ _ H);do 3 destruct H0.
deduce (tc_iter H0);unfold Iter in *;unfold Iter_ge in *.
destruct H2 as [n]. destruct H2;destruct H1.
eapply (iter_tc R n);rewrite <- dom_change_iter.
unfold nattodom;rewrite H1;rewrite H4;trivial.

deduce (tc_iter H);unfold Iter in *;unfold Iter_ge in *.
destruct H0 as [n];destruct H0.
rewrite <- dom_change_iter in H1.
unfold nattodom in *.
destruct (list_find_first (eq x) (A_eq_dec x) Dom);auto with *.
destruct (list_find_first (eq y) (A_eq_dec y) Dom);auto with *.
deduce (iter_tc (domtonat Dom R) n);auto.
Qed.

End iter.

(** inteserction mapped to intersection *)
Section intersection.
Variable A : Set.
Variable A_eq_dec :forall (x:A) (y:A), {x=y} +{~x=y}.
Variable Dom : list A.
Variable R R': relation nat.


Lemma dom_change_inter : forall x y,
nattodom A_eq_dec Dom (intersection R R') x y
<-> (nattodom A_eq_dec Dom R) x y /\ (nattodom A_eq_dec Dom R') x y.
split;intros;
unfold nattodom in *;
destruct (list_find_first (eq x) (A_eq_dec x) Dom);auto with *;
destruct (list_find_first (eq y) (A_eq_dec y) Dom);auto with *.
Qed.

End intersection.

(** transposition mapped to transposition *)
Section transpose.
Variable A : Set.
Variable A_eq_dec :forall (x:A) (y:A), {x=y} +{~x=y}.
Variable Dom : list A.
Variable R : relation nat.


Lemma dom_change_transp : forall x y,
nattodom A_eq_dec Dom (transp R ) x y
<-> transp (nattodom A_eq_dec Dom R) x y.
split;intros;unfold transp in *;
unfold nattodom in *;
destruct (list_find_first (eq x) (A_eq_dec x) Dom);auto with *;
destruct (list_find_first (eq y) (A_eq_dec y) Dom);auto with *.
Qed.

End transpose.

(** SCC mapped to SCC *)
Section domSCC.
Variable A : Set.
Variable A_eq_dec :forall (x:A) (y:A), {x=y} +{~x=y}.
Variable Dom : list A.
Variable R : relation A.
Variable restriction : is_restricted R Dom.
Variable rp_free: repeat_free Dom.


Theorem dom_change_SCC : forall x y,
nattodom  A_eq_dec Dom (SCC (domtonat  Dom R)) x y <-> SCC  R x y.
split;intros;unfold SCC in *.
change ((R !) x y /\ transp (R !) x y).
change (nattodom A_eq_dec Dom (intersection (domtonat Dom R !) 
(transp (domtonat Dom R !))) x y) in H.
rewrite dom_change_inter in H.
destruct H;rewrite dom_change_transp in H0.
unfold transp in *.
rewrite dom_change_tc in *;auto with *.

change ((R !) x y /\ transp (R !) x y) in H.
change (nattodom A_eq_dec Dom (intersection (domtonat Dom R !) 
(transp (domtonat Dom R !))) x y).
rewrite dom_change_inter.
destruct H;rewrite dom_change_transp.
unfold transp in *.
rewrite dom_change_tc;auto with *;rewrite dom_change_tc;auto with *.
Qed.
End domSCC.
