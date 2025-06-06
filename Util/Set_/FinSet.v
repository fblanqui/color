(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2014-12-11

* Finite sets and their cardinal

Standard definition of set finiteness (existence of a bijection to
some prefix of nat) and definition of the cardinal of a finite set
(using Church's iota). *)

Set Implicit Arguments.

From Stdlib Require Import Basics Morphisms Setoid.
From CoLoR Require Import ClassicUtil IotaUtil EpsilonUtil LogicUtil NatUtil
     FunUtil ListUtil ListNodup SetUtil BoundNat.

Section S.

  Variable A : Type.

  Notation set := (set A).

(****************************************************************************)
(** * Definition of finiteness *)

  Definition finite (P : set) := exists n (f : N n -> elts P), bijective f.

(****************************************************************************)
(** * Properties of [finite] *)

(** Finiteness is invariant by set equivalence. *)

  Global Instance finite_equiv : Proper (equiv ==> impl) finite.

  Proof.
    intros P Q PQ [n [f [f_inj f_surj]]].
    set (g := fun k : N n => elts_equiv PQ (f k)).
    ex n g. split.
    (* g is injective. *)
    intros x y e. apply f_inj. apply sig_eq in e. revert e. unfold g.
    case_eq (f x); intros a_val a ef. case_eq (f y); intros b_val b eg.
    simpl. intro e. apply sig_eq. auto.
    (* g is surjective. *)
    intro y. assert (QP : Q [=] P). hyp.
    destruct (f_surj (elts_equiv QP y)) as [x hx].
    ex x. unfold g. rewrite <- hx. apply sig_eq. destruct y as [y_val y].
    refl.
  Qed.

(** Finiteness of sets defined by a list of elements. *)

  Lemma finite_of_list_nodup l : nodup l -> finite (of_list l).

  Proof.
    destruct l.
    (* l = nil *)
    intros _. exists 0. exists any_of_N0. split.
    intros [x_val x]. intros; lia.
    intros [y_val y]. contradiction.
    (* l <> nil *)
    rename l into l'. set (l := a :: l').
    intro hl. set (n := length l). ex n.
    assert (i : forall k : N n, k < n). intros [k_val k]. simpl. lia.
    set (f := fun k : N n => elt (P:=of_list l) (nth_In a (i k))). ex f.
    split.
    (* f injective *)
    intros [x_val x] [y_val y]. unfold f; simpl. intro e. apply N_eq; simpl.
    apply sig_eq in e; simpl in e. subst n. eapply inj_nth_nodup.
    2: apply hl. apply eq_dec. hyp. hyp. apply e.
    (* f surjective *)
    intros [y_val y]. gen (In_nth a y); intros [k [k1 k2]].
    ex (N_ k1). apply sig_eq; simpl. auto.
  Qed.

  Lemma finite_of_list l : finite (of_list l).

  Proof.
    assert (e : of_list l [=] of_list (remdup eq_dec l)).
    intro x. unfold mem, of_list. sym. apply In_remdup.
    rewrite e. apply finite_of_list_nodup. apply nodup_remdup.
  Qed.

(** A set [P] is finite if there is a surjection from [N n] to [P]. *)

  Lemma finite_surj P n (f : N n -> elts P) : surjective f -> finite P.

  Proof.
    intro f_surj. rewrite (of_map_L f_surj). apply finite_of_list.
  Qed.

(** A set [P] is finite iff it can be defined by a list of elements. *)

  Lemma finite_eq P : finite P <-> exists l, P [=] of_list l.

  Proof.
    split.
    (* -> *)
    intros [n [f [f_inj f_surj]]].
    ex (map (elt_val o f) (L n)). apply of_map_L. hyp.
    (* <- *)
    intros [l e]. rewrite e. apply finite_of_list.
  Qed.

(** Finiteness is contravariant wrt inclusion. *)

  Global Instance finite_subset : Proper (subset --> impl) finite.

  Proof.
    intros P Q QP. rewrite !finite_eq. intros [l e]. ex (select (dec1 Q) l).
    gen (select_correct (dec1 Q) l). gen (select_complete (dec1 Q) l). fo.
  Qed.

(** A set [P] is finite iff it can be defined by a non-duplicating
list of elements. *)

  Lemma finite_eq_nodup P : finite P <-> exists l, P [=] of_list l /\ nodup l.

  Proof.
    split. rewrite finite_eq. intros [l e]. ex (remdup eq_dec l). split.
    rewrite e. intro x. sym. apply In_remdup. apply nodup_remdup.
    intros [l [e _]]. rewrite e. apply finite_of_list.
  Qed.

(****************************************************************************)
(** * List of the elements of a finite set. *)

  Definition list_of_finite P : finite P -> list A.

  Proof.
    (*COQ: rewrite finite_eq_nodup.(*makes Stack overflow!*)*)
    intro P_fin. rewrite finite_eq_nodup in P_fin. apply cid in P_fin.
    destruct P_fin as [l _]. exact l.
  Defined.

  Lemma finite_eq_of_list P (P_fin : finite P) :
    P [=] of_list (list_of_finite P_fin).

  Proof.
    unfold list_of_finite.
    destruct (cid (iff_impl_subrelation (finite P)
               (exists l : list A, P [=] of_list l /\ nodup l)
               (finite_eq_nodup P) P_fin)). tauto.
  Qed.

  Lemma nodup_list_of_finite P (P_fin : finite P) :
    nodup (list_of_finite P_fin).

  Proof.
    unfold list_of_finite.
    destruct (cid (iff_impl_subrelation (finite P)
               (exists l : list A, P [=] of_list l /\ nodup l)
               (finite_eq_nodup P) P_fin)). tauto.
  Qed.

  Lemma In_list_of_finite x P (P_fin : finite P) :
    In x (list_of_finite P_fin) <-> P x.

  Proof.
    unfold list_of_finite.
    destruct (cid (iff_impl_subrelation (finite P)
               (exists l : list A, P [=] of_list l /\ nodup l)
               (finite_eq_nodup P) P_fin)). fo.
  Qed.

(****************************************************************************)
(** Finiteness of [empty]. *)

  Lemma empty_of_list : empty [=] of_list (@nil A).

  Proof. fo. Qed.

  Lemma finite_empty : finite empty.

  Proof. rewrite empty_of_list. apply finite_of_list. Qed.

(****************************************************************************)
(** [add] preserves finiteness. *)

  Lemma finite_add a P : finite P -> finite (add a P).

  Proof.
    destruct (classic (mem a P)).
    (*COQ: rewrite add_already_in does not work here*)
    intro P_fin. rewrite add_already_in; hyp.
    rewrite finite_eq; intros [l e].
    rewrite e, <- of_cons. apply finite_of_list.
  Qed.

  Lemma finite_add_eq a P : finite (add a P) <-> finite P.

  Proof.
    split. 2: apply finite_add. destruct (classic (mem a P)).
    rewrite add_already_in; auto.
    rewrite finite_eq; intros [l e].
    rewrite <- (rem_add H), e , <- (of_remove eq_dec). apply finite_of_list.
  Qed.

(****************************************************************************)
(** Finiteness of a [singleton]. *)

  Lemma finite_singleton a : finite (singleton a).

  Proof. unfold singleton. apply finite_add. apply finite_empty. Defined.

(****************************************************************************)
(** [rem] preserves finiteness. *)

  Lemma finite_rem a P : finite P -> finite (rem a P).

  Proof.
    destruct (classic (mem a P)).
    rewrite finite_eq; intros [l e].
    rewrite e, <- (of_remove eq_dec). apply finite_of_list.
    intro P_fin. rewrite rem_notin; hyp.
  Qed.

  Lemma finite_rem_eq a P : finite (rem a P) <-> finite P.

  Proof.
    split. 2: apply finite_rem. destruct (classic (mem a P)).
    rewrite finite_eq; intros [l e].
    rewrite <- (add_rem eq_dec H), e, <- of_cons. apply finite_of_list.
    rewrite rem_notin; auto.
  Qed.

(****************************************************************************)
(** [union] preserves finiteness. *)

  Lemma finite_union P Q : finite P -> finite Q -> finite (union P Q).

  Proof.
    rewrite 2!finite_eq. intros [p hp] [q hq]. rewrite hp, hq, <- of_app.
    apply finite_of_list.
  Qed.

  Lemma finite_union_eq P Q : finite (union P Q) <-> finite P /\ finite Q.

  Proof.
    split. 2: intros [P_fin Q_fin]; apply finite_union; hyp.
    revert P Q. cut (forall P Q, finite (union P Q) -> finite P).
    intros L P Q PUQ_fin. split; eapply L. apply PUQ_fin.
    rewrite union_com. apply PUQ_fin.
    intros P Q. rewrite !finite_eq. intros [l hl]. ex (select (dec1 P) l).
    intro x. split.
    intro xP. hnf. apply select_complete; fo.
    intro xPl. hnf in xPl. apply select_correct in xPl. fo.
  Qed.

(****************************************************************************)
(** [diff] preserves finiteness. *)

  Lemma finite_diff P : finite P -> forall Q, finite (diff P Q).

  Proof.
    rewrite finite_eq. intros [l Pl]. intro Q. rewrite finite_eq.
    ex (select (fun x => dec (~mem x Q)) l). split; intro hx.
    apply select_complete; fo.
    unfold mem, of_list in hx. apply select_correct in hx. fo.
  Qed.

(****************************************************************************)
(** * Type of finite sets. *)

  Definition Pf := sig finite.

  Definition mk_Pf P (P_fin : finite P) : Pf := exist P_fin.

  Coercion mk_Pf : finite >-> Pf.

  Definition Pf_val (P : Pf) : set := proj1_sig P.

  Coercion Pf_val : Pf >-> SetUtil.set.

  Definition Pf_prf (P : Pf) : finite (Pf_val P) := proj2_sig P.

  Coercion Pf_prf : Pf >-> finite.

(****************************************************************************)
(** Inclusion and equivalence of finite sets. *)

  Definition Pf_subset (P Q : Pf) := P [<=] Q.

  Global Instance Pf_subset_preorder : PreOrder Pf_subset.

  Proof. fo. Qed.

  Definition Pf_equiv (P Q : Pf) := P [=] Q.

  Infix "=f=" := Pf_equiv (at level 70).

  Global Instance Pf_equiv_Equivalence : Equivalence Pf_equiv.

  Proof. fo. Qed.

  Global Instance Pf_val_subset : Proper (Pf_subset ==> subset) Pf_val.

  Proof. fo. Qed.

  Global Instance Pf_val_equiv : Proper (Pf_equiv ==> equiv) Pf_val.

  Proof. fo. Qed.

  Lemma Pf_equiv_of {P Q : Pf} : P [=] Q -> P =f= Q.

  Proof. unfold Pf_equiv. auto. Qed.

  (*FIXME?Coq warning:
  witness does not respect the uniform inheritance condition*)
  Coercion Pf_equiv_of : equiv >-> Pf_equiv.

  Lemma Pf_equiv_of_gen (P Q : Pf) P_val Q_val :
    P [=] P_val -> Q [=] Q_val -> P_val [=] Q_val -> P =f= Q.

  Proof. intros e1 e2. unfold Pf_equiv. rewrite e1, e2. auto. Qed.

  Definition Pf_equiv_of2 {P Q : Pf} :=
    Pf_equiv_of_gen P Q (reflexivity _) (reflexivity _).

(****************************************************************************)
(** Constructors of finite sets. *)

  Definition Pf_of_list l : Pf := finite_of_list l.

  Definition Pf_empty : Pf := finite_empty.

  Definition Pf_add x (P : Pf) : Pf := finite_add x P.

  Global Instance Pf_add_subset :
    Proper (eq ==> Pf_subset ==> Pf_subset) Pf_add.

  Proof. intros x y xy P Q. unfold Pf_subset; simpl. apply add_subset. hyp. Qed.

  Global Instance Pf_add_equiv : Proper (eq ==> Pf_equiv ==> Pf_equiv) Pf_add.

  Proof. intros x y xy P Q. unfold Pf_equiv; simpl. apply add_equiv. hyp. Qed.

  Definition Pf_singleton x : Pf := finite_singleton x.

  Lemma Pf_singleton_eq x : Pf_singleton x =f= Pf_add x Pf_empty.

  Proof. refl. Qed.

  Definition Pf_rem x (P : Pf) : Pf := finite_rem x P.

  Global Instance Pf_rem_subset :
    Proper (eq ==> Pf_subset ==> Pf_subset) Pf_rem.

  Proof. intros x y xy P Q. unfold Pf_subset; simpl. apply rem_subset. hyp. Qed.

  Global Instance Pf_rem_equiv : Proper (eq ==> Pf_equiv ==> Pf_equiv) Pf_rem.

  Proof. intros x y xy P Q. unfold Pf_equiv; simpl. apply rem_equiv. hyp. Qed.

  Definition Pf_union (P Q : Pf) : Pf := finite_union P Q.

  Global Instance Pf_union_subset :
    Proper (Pf_subset ==> Pf_subset ==> Pf_subset) Pf_union.

  Proof.
    intros P Q PQ R S RS. unfold Pf_subset in *; simpl in *.
    apply union_subset; hyp.
  Qed.

  Global Instance Pf_union_equiv :
    Proper (Pf_equiv ==> Pf_equiv ==> Pf_equiv) Pf_union.

  Proof.
    intros P Q PQ R S RS. unfold Pf_equiv in *; simpl in *.
    apply union_equiv; hyp.
  Qed.

  Definition Pf_diff (P Q : Pf) : Pf := finite_diff P Q.

  Global Instance Pf_diff_subset :
    Proper (Pf_subset ==> Pf_subset --> Pf_subset) Pf_diff.

  Proof.
    intros P Q PQ R S SR. unfold flip, Pf_subset in *; simpl in *.
    apply diff_subset; hyp.
  Qed.

  Global Instance Pf_diff_equiv :
    Proper (Pf_equiv ==> Pf_equiv ==> Pf_equiv) Pf_diff.

  Proof.
    intros P Q PQ R S RS. unfold Pf_equiv in *; simpl in *.
    apply diff_equiv; hyp.
  Qed.

  Lemma Pf_equiv_of_list (P : Pf) : P =f= Pf_of_list (list_of_finite P).

  Proof. apply finite_eq_of_list. Qed.

  Lemma Pf_add_of_list a (l : list A) :
    Pf_add a (Pf_of_list l) =f= Pf_of_list (a :: l). 

  Proof. unfold Pf_equiv; simpl. rewrite <- of_cons. refl. Qed.

(****************************************************************************)
(** Induction principle on finite sets. *)

  Lemma Pf_ind (P : Pf -> Prop) (P_equiv : Proper (Pf_equiv ==> impl) P)
    (P0 : P Pf_empty)
    (PS : forall a (X : Pf), ~mem a X -> P X -> P (Pf_add a X)) :
    forall X, P X.

  Proof.
    intro X. rewrite Pf_equiv_of_list. gen (nodup_list_of_finite X).
    gen (list_of_finite X). induction l; intro lnd.
    eapply P_equiv. 2: apply P0. fo.
    rewrite <- Pf_add_of_list. fo.
  Qed.
 
(****************************************************************************)
(** * Cardinal of a finite set *)

  Lemma card_uniq P :
    finite P -> exists! n, exists (f : N n -> elts P), bijective f.

  Proof.
    intros [n [f [f_inj f_surj]]]. ex n. split. ex f. fo.
    intros m [g [g_inj g_surj]]. apply Nat.le_antisymm.
    apply N_inj_le with (f := inverse g_surj o f). inj.
    apply N_inj_le with (f := inverse f_surj o g). inj.
  Qed.

  Definition card : Pf -> nat.

  Proof.
    intros [P P_fin]. destruct (cdd (card_uniq P_fin)) as [n _]. exact n.
  Defined.

  Global Instance card_subset : Proper (Pf_subset ==> le) card.

  Proof.
    intros [P P_fin] [Q Q_fin] PQ. unfold card.
    destruct (cdd (card_uniq P_fin)) as [p [f [f_inj f_surj]]].
    destruct (cdd (card_uniq Q_fin)) as [q [g [g_inj g_surj]]].
    apply N_inj_le with (f := inverse g_surj o elts_subset PQ o f). inj.
    apply inj_elts_subset.
  Qed.

  Global Instance card_equiv : Proper (Pf_equiv ==> eq) card.

  Proof.
    intros [P P_fin] [Q Q_fin] PQ. unfold Pf_equiv in PQ.
    rewrite equiv_subset2 in PQ. destruct PQ as [PQ QP].
    gen (card_subset PQ). gen (card_subset QP). lia.
  Qed.

(****************************************************************************)
(** Induction on finite sets through their cardinals. *)

  Lemma card_ind (P : Pf -> Prop) (H : forall n X, card X = n -> P X) :
    forall X, P X.

  Proof. intro X. eapply H. refl. Qed.

(****************************************************************************)
(** * Cardinal of some finite set constructors. *)

(** Cardinal of a set defined by a list of elements. *)

  Lemma card_of_list_le_length_gen l (h : finite (of_list l)) :
    card h <= length l.

  Proof.
    unfold card.
    case_eq (mk_Pf h); intros P P_fin e; apply sig_eq in e; simpl in e; subst.
    destruct (cdd (card_uniq P_fin)) as [n [f [f_inj f_surj]]].
    destruct n. lia.
    set (g := fun i : N (S n) =>
                let (_, xl) := f i in N_ (pos_lt_length eq_dec xl)).
    apply N_inj_le with (f := g). intros i j. unfold g.
    case_eq (f i); intros x xl hx. case_eq (f j); intros y yl hy e.
    apply N_eq in e; simpl in e. apply inj_pos in e. 2: fo.
    subst y. apply f_inj. rewrite hx, hy. apply sig_eq. refl.
  Qed.

  Lemma card_of_list_le_length l : card (Pf_of_list l) <= length l.

  Proof. apply card_of_list_le_length_gen. Qed.

(** Cardinal of the empty set. *)

  Lemma card_empty_gen (h : finite empty) : card h = 0.

  Proof.
    cut (card h <= 0). lia. change (card h <= length (@nil A)).
    assert (e : Pf_equiv h (finite_of_list nil)). fo. rewrite e.
    apply card_of_list_le_length.
  Qed.

  Lemma card_empty : card Pf_empty = 0.

  Proof. apply card_empty_gen. Qed.

(** A set of null cardinality is empty. *)

  Lemma card_0 {P} : card P = 0 -> P =f= Pf_empty.

  Proof.
    unfold card. destruct P as [P P_fin].
    destruct (cdd (card_uniq P_fin)) as [n [f [f_inj f_surj]]]. intro; subst.
    unfold Pf_equiv; simpl. intro x. split. 2: fo.
    intro hx. destruct (f_surj (elt hx)) as [k _]. destruct k. lia.
  Qed.

(** Cardinal of a set defined by a non-duplcating list of elements. *)

  Lemma card_of_list_eq_length_gen l (h : finite (of_list l)) :
    nodup l -> card h = length l.

  Proof.
    intro l_nodup. destruct (dec (l = nil)) as [hl|hl].
    subst. rewrite card_empty_gen. refl.
    assert (a : A). destruct l. cong. exact a.
    apply Nat.le_antisymm. apply card_of_list_le_length_gen.
    unfold card. case_eq (mk_Pf h); intros P P_fin e.
    apply sig_eq in e; simpl in e; subst.
    destruct (cdd (card_uniq P_fin)) as [n [f [f_inj f_surj]]].
    apply N_inj_le with (f := fun x : N (length l) =>
      inverse f_surj (elt (P:=of_list l) (nth_In a x))).
    intros [x_val x] [y_val y] e. apply N_eq; simpl.
    apply inj_inverse in e. apply sig_eq in e; simpl in e.
    apply inj_nth_nodup in e; auto. apply eq_dec.
  Qed.

  Lemma card_of_list_eq_length l : nodup l -> card (Pf_of_list l) = length l.

  Proof. apply card_of_list_eq_length_gen. Qed.

  Lemma Pf_eq_of_list (P : Pf) : P =f= Pf_of_list (list_of_finite P).

  Proof. apply finite_eq_of_list. Qed.

  Lemma card_eq P : card P = length (list_of_finite P).

  Proof.
    rewrite Pf_eq_of_list at 1. rewrite card_of_list_eq_length. refl.
    apply nodup_list_of_finite.
  Qed.

(** Cardinal of [add]. *)

  Lemma card_add a P :
    card (Pf_add a P) = card P + if dec (mem a P) then 0 else 1.

  Proof.
    destruct (dec (mem a P)).
    (* a in P *)
    rewrite <- plus_n_O. apply card_equiv. apply Pf_equiv_of; simpl.
    apply add_already_in. hyp.
    (* a not in P *)
    rewrite (Pf_eq_of_list P).
    set (l := list_of_finite P). set (P' := Pf_of_list l).
    rewrite (Pf_equiv_of2 (P:=Pf_add a P') (Q:=Pf_of_list (a::l))).
    rewrite card_of_list_eq_length. simpl length.
    unfold P', l. rewrite <- Pf_eq_of_list, <- card_eq. lia.
    simpl. split. unfold l. rewrite In_list_of_finite. hyp.
    apply nodup_list_of_finite.
    simpl. sym. apply of_cons.
  Qed.

(** Cardinal of [singleton]. *)

  Lemma card_singleton a : card (Pf_singleton a) = 1.

  Proof.
    rewrite Pf_singleton_eq, card_add, card_empty.
    destruct (dec (mem a Pf_empty)). firstorder with arith. refl.
  Qed.

(** Cardinal of [rem]. *)

  Lemma card_rem a P :
    card (Pf_rem a P) = card P - if dec (mem a P) then 1 else 0.

  Proof.
    destruct (dec (mem a P)).
    (* a in P *)
    rewrite (Pf_eq_of_list P).
    set (l := list_of_finite P). set (P' := Pf_of_list l).
    rewrite (Pf_equiv_of2 (P:=Pf_rem a P') (Q:=Pf_of_list (remove eq_dec a l))).
    assert (h : nodup l). apply nodup_list_of_finite.
    unfold P'. rewrite !card_of_list_eq_length, length_remove_nodup; auto.
    unfold l. rewrite In_list_of_finite. hyp. apply nodup_remove. hyp.
    simpl. sym. apply of_remove.
    (* a not in P *)
    rewrite Nat.sub_0_r. apply card_equiv. unfold Pf_equiv. simpl.
    apply rem_notin. hyp.
  Qed.

(** A set of non-null cardinality has at least one element. *)

  Lemma card_S {P n} : card P = S n ->
    exists a Q, P =f= Pf_add a Q /\ ~mem a Q /\ card Q = n.
 
  Proof.
    intro e. gen e. unfold card at 1. destruct P as [P P_fin]; simpl.
    destruct (cdd (card_uniq P_fin)) as [p [f f_bij]]; simpl. intro; subst.
    destruct (f zero) as [a aP]. ex a (Pf_rem a P_fin).
    split. unfold Pf_equiv; simpl. rewrite (add_rem eq_dec). refl. hyp.
    split. apply notin_rem.
    rewrite card_rem. unfold mk_Pf at 1. rewrite e.
    destruct (dec (mem a P_fin)). lia. contr.
  Qed.

(****************************************************************************)
(** * Type of subsets of some cardinality. *)

  Section Pcard.

    Variables (P : set) (n : nat).

    Definition Pcard := { Q : Pf | Q [<=] P /\ card Q = n }.

    Definition mk_Pcard (Q : Pf) : Q [<=] P -> card Q = n -> Pcard.

    Proof. intros QP h. ex Q. auto. Defined.

    Definition Pcard_val (Q : Pcard) : Pf := proj1_sig Q.

    Global Coercion Pcard_val : Pcard >-> Pf.

    Definition Pcard_equiv (Q R : Pcard) := Q =f= R.

    Global Instance Pcard_equiv_Equivalence : Equivalence Pcard_equiv.

    Proof. fo. Qed.

  End Pcard.

  Arguments mk_Pcard [P n Q] _ _.
  Arguments Pcard_equiv {P n} _ _.

  Infix "=c=" := Pcard_equiv (at level 70).

  Definition Pcard_subset n P P' : P [<=] P' -> Pcard P n -> Pcard P' n.

  Proof. intros PP' [Q [Q1 Q2]]. ex Q. split. trans P; hyp. hyp. Defined.

  Lemma Pcard_subset_inj n R P (PR : P [<=] R) Q (QR : Q [<=] R) :
    forall (x : Pcard P n) (y : Pcard Q n),
      x [=] y -> Pcard_subset PR x =c= Pcard_subset QR y.

  Proof. intros [X [XP Xn]] [Y [YQ Yn]] e. hyp. Qed.

  Lemma Pcard_subset_equiv P Q (PQ : P [<=] Q) n R :
    forall x : Pcard P n, x [=] R -> Pcard_subset PQ x [=] R.

  Proof. intros [X [XP Xn]] xR. hyp. Qed.

End S.

Arguments Pcard_equiv {A P n} _ _.
Arguments mk_Pcard [A P n Q] _ _.
