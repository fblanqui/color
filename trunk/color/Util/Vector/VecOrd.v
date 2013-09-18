(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-01-24


* Component-wise extension of a relation to vectors and product ordering
*)

Set Implicit Arguments.

Require Import LogicUtil VecUtil RelUtil NatUtil RelMidex.

(***********************************************************************)
(** * Component-wise extension to vectors on [A] of a relation on [A]. *)

Fixpoint Vrel1 n A (R : relation A) : relation (vector A n) :=
  match n with
    | O => fun _ _ => False
    | S n => fun v1 v2 => symprod R (Vrel1 R) (Vhead_tail v1) (Vhead_tail v2)
  end.

Definition Vrel1_app n A (R : relation A) : relation (vector A n) :=
  fun v1 v2 : vector A n =>
    exists i (vi : vector A i) x j (vj : vector A j) h y,
      v1 = Vcast (Vapp vi (Vcons x vj)) h
      /\ v2 = Vcast (Vapp vi (Vcons y vj)) h /\ R x y.

Definition Vrel1_nth n A (R : relation A) : relation (vector A n) :=
  fun v1 v2 : vector A n =>
    exists i (hi : i<n), R (Vnth v1 hi) (Vnth v2 hi)
      /\ forall j (hj : j<n), j <> i -> Vnth v1 hj = Vnth v2 hj.

(***********************************************************************)
(** Properties of [Vrel1]. *)

Section S.

  Variables (A : Type) (R : relation A).

  Lemma Vrel1_cons_intro : forall x1 x2 n (v1 v2 : vector A n),
    (R x1 x2 /\ v1 = v2) \/ (x1 = x2 /\ Vrel1 R v1 v2)
    -> Vrel1 R (Vcons x1 v1) (Vcons x2 v2).

  Proof.
    intros. simpl. unfold Vhead_tail. simpl. destruct H; destruct H.
    subst v2. apply left_sym. hyp.
    subst x2. apply right_sym. hyp.
  Qed.

  Lemma Vrel1_cons_elim : forall x1 x2 n (v1 v2 : vector A n),
    Vrel1 R (Vcons x1 v1) (Vcons x2 v2) ->
    (R x1 x2 /\ v1 = v2) \/ (x1 = x2 /\ Vrel1 R v1 v2).

  Proof.
    intros. simpl in H. unfold Vhead_tail in H. simpl in H. inversion H.
    left. auto. right. auto.
  Qed.

  Lemma Vrel1_add_intro : forall x1 x2 n (v1 v2 : vector A n),
    (R x1 x2 /\ v1 = v2) \/ (x1 = x2 /\ Vrel1 R v1 v2)
    -> Vrel1 R (Vadd v1 x1) (Vadd v2 x2).

  Proof.
    intros x1 x2. induction n; intros v1 v2.
    VOtac. intuition. apply left_sym. hyp.
    VSntac v1; VSntac v2. simpl Vadd. intros [[h1 h2]|[h1 h2]].
    Veqtac. apply Vrel1_cons_intro. right. fo.
    subst x2. destruct (Vrel1_cons_elim h2) as [[i1 i2]|[i1 i2]].
    rewrite i2. apply Vrel1_cons_intro. left. fo.
    apply Vrel1_cons_intro. right. fo.
  Qed.

  Lemma Vrel1_app_intro_l : forall n (v : vector A n) m (v1 v2 : vector A m),
    Vrel1 R v1 v2 -> Vrel1 R (Vapp v v1) (Vapp v v2).

  Proof.
    induction v; intros. hyp.
    simpl. unfold Vhead_tail. simpl. apply right_sym. apply IHv. hyp.
  Qed.

  Lemma Vrel1_cast_intro : forall m n (h : m=n) (v1 v2 : vector A m),
    Vrel1 R v1 v2 -> Vrel1 R (Vcast v1 h) (Vcast v2 h).

  Proof.
    induction v1; intros; destruct n; intros.
    contr. discr. discr.
    assert (n0 = n). apply eq_add_S. hyp. subst n0.
    assert (h = refl_equal (S n)). apply eq_unique. subst h.
    rewrite (Vcast_refl (Vcons h0 v1)). rewrite (Vcast_refl v2). hyp.
  Qed.

  Lemma Vrel1_cast_elim : forall m n (h : m=n) (v1 v2 : vector A m),
    Vrel1 R (Vcast v1 h) (Vcast v2 h) -> Vrel1 R v1 v2.

  Proof.
    induction m; destruct n; intros.
    assert (h = refl_equal 0). apply eq_unique. subst h. contr.
    discr. discr.
    assert (v1 = Vcons (Vhead v1) (Vtail v1)). apply VSn_eq. rewrite H0.
    assert (v2 = Vcons (Vhead v2) (Vtail v2)). apply VSn_eq. rewrite H1.
    rewrite H0, H1 in H. simpl in H. unfold Vhead_tail in H. simpl in H.
    apply Vrel1_cons_intro. inversion H. left. split. hyp.
    eapply Vcast_eq_elim with (m := n). apply H6.
    right. split. refl. eapply IHm with (n := n). apply H3.
  Qed.

(***********************************************************************)
(** Equivalence between [Vrel1] and [Vrel1_app]. *)

  Lemma Vrel1_app_impl : forall n (v1 v2 : vector A n),
    Vrel1 R v1 v2 -> Vrel1_app R v1 v2.

  Proof.
    induction v1; simpl. intros. contr. intro. VSntac v2.
    unfold Vhead_tail. simpl. intro. inversion H0.
    ex 0 (@Vnil A) h n (Vtail v2) (refl_equal (S n)) (Vhead v2).
    split. rewrite Vcast_refl. refl.
    split. rewrite Vcast_refl. refl. hyp.
    ded (IHv1 (Vtail v2) H2). do 8 destruct H6. destruct H7. rewrite H6, H7.
    ex (S x0) (Vcons (Vhead v2) x1) x2 x3 x4.
    assert (S x0 + S x3 = S n). omega. ex H9 x6.
    simpl. intuition. apply Vtail_eq. apply Vcast_pi.
    apply Vtail_eq. apply Vcast_pi.
  Qed.

  Lemma Vrel1_app_iff : forall n (v1 v2 : vector A n),
    Vrel1 R v1 v2 <-> Vrel1_app R v1 v2.

  Proof.
    intros n v1 v2. split. apply Vrel1_app_impl.
    intros [i [vi [x [j [vj [h [y [h1 [h2 h3]]]]]]]]]; subst.
    rewrite 2!Vcast_refl. apply Vrel1_app_intro_l. apply Vrel1_cons_intro. fo.
  Qed.

  Lemma Vrel1_app_eq n : @Vrel1 n _ R == @Vrel1_app n _ R.

  Proof. rewrite rel_eq. apply Vrel1_app_iff. Qed.

(***********************************************************************)
(** Equivalence between [Vrel1] and [Vrel1_nth]. *)

  Lemma Vrel1_nth_iff : forall n (v1 v2 : vector A n),
    Vrel1 R v1 v2 <-> Vrel1_nth R v1 v2.

  Proof.
    intros n v1 v2. rewrite Vrel1_app_iff. split.

    intros [i [vi [x [j [vj [h [y [h1 [h2 h3]]]]]]]]];
      subst; rewrite !Vcast_refl.
    exists i. assert (hi : i<i+S j). omega. exists hi.
    rewrite !Vnth_app_cons. intuition.
    rewrite !Vnth_app. destruct (le_gt_dec i j0). 2: refl.
    rewrite !Vnth_cons. destruct (lt_ge_dec 0 (j0-i)). 2: omega.
    apply Vnth_eq. refl.

    intros [i [hi [i1 i2]]].
    assert (ki : 0+i<=n). omega. ex i (Vsub v1 ki) (Vnth v1 hi).
    assert (kj : S i+(n-i-1)<=n). omega. ex (n-i-1) (Vsub v1 kj).
    assert (k : i+S(n-i-1)=n). omega. ex k (Vnth v2 hi).
    split; [idtac|split;[idtac|hyp]].

    apply Veq_nth. intros j hj. rewrite Vnth_cast, Vnth_app.
    destruct (le_gt_dec i j). rewrite Vnth_cons. destruct (lt_ge_dec 0 (j-i)).
    rewrite Vnth_sub. apply Vnth_eq. omega.
    apply Vnth_eq. omega.
    rewrite Vnth_sub. apply Vnth_eq. refl.

    apply Veq_nth. intros j hj. rewrite Vnth_cast, Vnth_app.
    destruct (le_gt_dec i j). rewrite Vnth_cons. destruct (lt_ge_dec 0 (j-i)).
    rewrite Vnth_sub.
    trans (Vnth v1 hj). sym. apply i2. omega. apply Vnth_eq. omega.
    apply Vnth_eq. omega.
    rewrite Vnth_sub.
    trans (Vnth v1 hj). sym. apply i2. omega. apply Vnth_eq. refl.
  Qed.

  Lemma Vrel1_sub : forall n (v1 v2 : vector A n) p q (h : p+q<=n),
    Vrel1 R v1 v2 -> (Vrel1 R)% (Vsub v1 h) (Vsub v2 h).

  Proof.
    intros n v1 v2 p q k. rewrite Vrel1_nth_iff.
    intros [i [hi [i1 i2]]]. destruct (lt_dec i p).
    left. apply Veq_nth. intros j hj. rewrite !Vnth_sub. apply i2. omega.
    destruct (ge_dec i (p+q)).
    left. apply Veq_nth. intros j hj. rewrite !Vnth_sub. apply i2. omega.
    right. rewrite Vrel1_nth_iff.
    exists (i-p). assert (l : i-p<q). omega. exists l. split.
    rewrite !Vnth_sub. erewrite Vnth_eq, Vnth_eq with (v:=v2). apply i1.
    omega. omega.
    intros j hj m. rewrite !Vnth_sub. apply i2. omega.
  Qed.

(***********************************************************************)
(** Properties of [Vrel1] wrt termination. *)

  Require Import SN.

  Lemma Vforall_SN_rel1 : forall n (v : vector A n),
    Vforall (SN R) v -> SN (Vrel1 R) v.

  Proof.
    induction v; intros; apply SN_intro; intros. contr. simpl.
    eapply SN_inverse with (f := @Vhead_tail A n) (R := symprod R (Vrel1 R)).
    VSntac y. unfold Vhead_tail. simpl. simpl in H. destruct H.
    rewrite H1 in H0. inversion H0.
    apply SN_symprod. eapply SN_inv. apply H. hyp.
    rewrite <- H7. apply IHv. hyp.
    apply SN_symprod. rewrite <- H6. hyp.
    eapply SN_inv. apply IHv. apply H2. hyp.
  Qed.

  Lemma SN_rel1_head : forall n (v : vector A (S n)),
    SN (Vrel1 R) v -> SN R (Vhead v).

  Proof.
    induction 1. VSntac x. apply SN_intro. intros.
    ded (H0 (Vcons y (Vtail x))). apply H3. rewrite H1. simpl.
    unfold Vhead_tail. simpl. apply left_sym. hyp.
  Qed.

  Lemma SN_rel1_cons_head : forall a n (v : vector A n),
    SN (Vrel1 R) (Vcons a v) -> SN R a.

  Proof. intros. ded (SN_rel1_head H). hyp. Qed.

  Lemma SN_rel1_tail : forall n (v : vector A (S n)),
    SN (Vrel1 R) v -> SN (Vrel1 R) (Vtail v).

  Proof.
    induction 1. VSntac x. apply SN_intro. intros.
    ded (H0 (Vcons (Vhead x) y)). rewrite H1 in H3. apply H3.
    simpl. unfold Vhead_tail. simpl. apply right_sym. hyp.
  Qed.

  Lemma SN_rel1_cons_tail : forall a n (v : vector A n),
    SN (Vrel1 R) (Vcons a v) -> SN (Vrel1 R) v.

  Proof. intros. ded (SN_rel1_tail H). hyp. Qed.

  Lemma SN_rel1_forall : forall n (v : vector A n),
    SN (Vrel1 R) v -> Vforall (SN R) v.

  Proof.
    induction v; intros; simpl. exact I. split.
    apply (SN_rel1_head H). apply IHv. apply (SN_rel1_tail H).
  Qed.

End S.

Arguments Vrel1_app_impl [A R n v1 v2] _.
Arguments Vrel1_sub [A R n v1 v2 p q] h _.

(***********************************************************************)
(** Compatibility of [Vrel1] with [same_relation]. *)

Require Import Morphisms.

Instance Vrel1_app_same_rel n A :
  Proper (same_relation ==> same_relation) (@Vrel1_app n A).

Proof.
  intros R R' RR'. rewrite rel_eq. intros v1 v2. unfold Vrel1.
  split; intros [i [vi [x [j [vj [h [y [h1 [h2 h3]]]]]]]]];
    ex i vi x j vj h y; fo.
Qed.

Instance Vrel1_same_rel n A :
  Proper (same_relation ==> same_relation) (@Vrel1 n A).

Proof.
  intros R R' RR'. rewrite 2!Vrel1_app_eq. apply Vrel1_app_same_rel. hyp.
Qed.

(***********************************************************************)
(** Distributivity of [Vrel1] wrt [union]. *)

Lemma Vrel1_app_union n A (R S : relation A) :
  @Vrel1_app n _ (R U S) == @Vrel1_app n _ R U @Vrel1_app n _ S.

Proof.
  rewrite rel_eq; intros v1 v2. split.
  intros [i [vi [x [j [vj [h [y [h1 [h2 [h3|h3]]]]]]]]]].
  left. ex i vi x j vj h y. intuition.
  right. ex i vi x j vj h y. intuition.
  intros [h|h]; destruct h as [i [vi [x [j [vj [h [y [h1 [h2 h3]]]]]]]]];
    ex i vi x j vj h y; intuition.
Qed.

Lemma Vrel1_union n A (R S : relation A) :
  @Vrel1 n _ (R U S) == @Vrel1 n _ R U @Vrel1 n _ S.

Proof. rewrite !Vrel1_app_eq. apply Vrel1_app_union. Qed.

(***********************************************************************)
(** * Product relation on vectors. *)

Definition Vreln {n A} (R : relation A) : relation (vector A n) :=
  Vforall2n R (n:=n).

Section Vreln.

  Variables (A : Type) (R : relation A).

  (** [Vreln] preserves reflexivity, symmetry and transitivity. *)

  Global Instance Vreln_refl :
    Reflexive R -> forall n, Reflexive (Vreln (n:=n) R).

  Proof. intros h n x. apply Vforall2n_intro. refl. Qed.

  Global Instance Vreln_trans :
    Transitive R -> forall n, Transitive (Vreln (n:=n) R).

  Proof.
    intros h n x y z xy yz. apply Vforall2n_intro. intros i ip.
    trans (Vnth y ip); apply Vforall2n_nth; hyp.
  Qed.

  Global Instance Vreln_sym :
    Symmetric R -> forall n, Symmetric (Vreln (n:=n) R).

  Proof.
    intros h n x y xy. apply Vforall2n_intro. intros i ip. sym.
    apply Vforall2n_nth. hyp.
  Qed.

  Global Instance Vreln_equiv :
    Equivalence R -> forall n, Equivalence (Vreln (n:=n) R).

  Proof.
    constructor. apply Vreln_refl; class. apply Vreln_sym; class.
    apply Vreln_trans; class.
  Qed.

  (** Decidability of [Vreln]. *)

  Lemma Vreln_dec : rel_dec R -> forall n, rel_dec (Vreln (n:=n) R).

  Proof.
    intros R_dec n P Q. destruct (Vforall2n_dec R_dec P Q); intuition.
  Defined.

  (** Syntactic properties of [Vreln]. *)

  Lemma Vreln_tail_intro : forall n (v v' : vector A (S n)),
    Vreln R v v' -> Vreln R (Vtail v) (Vtail v').

  Proof. intros. unfold Vreln. apply Vforall2n_tail. hyp. Qed.

  Lemma Vreln_cons : forall u v n (us vs : vector A n),
    Vreln R (Vcons u us) (Vcons v vs) <-> R u v /\ Vreln R us vs.

  Proof. fo. Qed.

  Lemma Vreln_cons_elim : forall n (u v : vector A n) x y,
    Vreln R (Vcons x u) (Vcons y v) -> Vreln R u v.

  Proof. fo. Qed.

  Lemma Vreln_app_elim_l n1 (v1 v1' : vector A n1) n2 (v2 v2' : vector A n2) :
    Vreln R (Vapp v1 v2) (Vapp v1' v2') -> Vreln R v1 v1'.

  Proof.
    intro h. apply Vforall2n_intro. intros i hi.
    assert (hi' : i < n1+n2). omega.
    assert (a1 : Vnth v1 hi = Vnth (Vapp v1 v2) hi').
    rewrite Vnth_app. destruct (Compare_dec.le_gt_dec n1 i).
    omega. apply Vnth_eq. refl.
    assert (a2 : Vnth v1' hi = Vnth (Vapp v1' v2') hi').
    rewrite Vnth_app. destruct (Compare_dec.le_gt_dec n1 i).
    omega. apply Vnth_eq. refl.
    rewrite a1, a2. apply Vforall2n_nth. hyp.
  Qed.

  Lemma Vreln_app_elim_r n1 (v1 v1' : vector A n1) n2 (v2 v2' : vector A n2) :
    Vreln R (Vapp v1 v2) (Vapp v1' v2') -> Vreln R v2 v2'.

  Proof.
    intro h. apply Vforall2n_intro. intros i hi.
    assert (hi' : n1+i < n1+n2). omega.
    assert (a1 : Vnth v2 hi = Vnth (Vapp v1 v2) hi').
    rewrite Vnth_app. destruct (Compare_dec.le_gt_dec n1 (n1+i)).
    apply Vnth_eq. omega. omega.
    assert (a2 : Vnth v2' hi = Vnth (Vapp v1' v2') hi').
    rewrite Vnth_app. destruct (Compare_dec.le_gt_dec n1 (n1+i)).
    apply Vnth_eq. omega. omega.
    rewrite a1, a2. apply Vforall2n_nth. hyp.
  Qed.

  Lemma Vreln_cast n (u v : vector A n) n' (h h' : n=n') :
    Vreln R (Vcast u h) (Vcast v h') <-> Vreln R u v.

  Proof. subst n'. rewrite 2!Vcast_refl. refl. Qed.

  (*FIXME: change arguments order of Vnth to declare Vnth_Vreln as
  Proper Instance?*)
  Lemma Vreln_elim_nth : forall n (ts us : vector A n) i (hi : i<n),
    Vreln R ts us -> R (Vnth ts hi) (Vnth us hi).

  Proof.
    induction ts; intros us i hi e. omega. VSntac us; simpl.
    rewrite H, Vreln_cons in e. destruct e as [e1 e2]. destruct i as [|i]; fo.
  Qed.

  Lemma Vreln_sub_intro : forall n (v1 v2 : vector A n) p q (h : p+q<=n),
    Vreln R v1 v2 -> Vreln R (Vsub v1 h) (Vsub v2 h).

  Proof.
    intros n v1 v2 p q h e. apply Vforall2n_intro; intros i hi.
    rewrite !Vnth_sub. apply Vforall2n_nth. hyp.
  Qed.

  (** Morphisms. *)

  Global Instance Vopt_filter_reln n (ks : vector nat n) p :
    Proper (Vreln R ==> Vreln (opt_r R)) (Vopt_filter ks (p:=p)).

  Proof.
    intros ts ts' tsts'. apply Vforall2n_intro. intros i hi.
    rewrite !Vnth_opt_filter. destruct (lt_dec (Vnth ks hi)).
    apply opt_r_Some. apply Vreln_elim_nth. hyp. apply opt_r_None.
  Qed.

End Vreln.

Arguments Vreln_sub_intro [A R n v1 v2 p q] _ _.
Arguments Vreln_elim_nth [A R n ts us i] _ _.

(***********************************************************************)
(** ** Extension of a relation on vectors of [option A]

so that [Vreln_opt (n:=n) R us vs] if there are [k <= n], [xs, ys :
vector A k] such that [us = Vapp (Vmap Some xs) (Vconst None (n-k))],
[vs = Vapp (Vmap Some ys) (Vconst None (n-k))] and [Reln R xs ys]. *)

Definition Vreln_opt {n A} (R : relation A) : relation (vector (option A) n) :=
  fun us vs => exists i (h : i <= n),
    Vreln (opt R) (Vsub us (Veq_app_aux1 h)) (Vsub vs (Veq_app_aux1 h))
    /\ Vreln (opt_r empty_rel) (Vsub us (Veq_app_aux2 h))
                                (Vsub vs (Veq_app_aux2 h)).

Lemma Vreln_opt_filter A p (ts us : vector A p) (R : relation A) :
  forall n (ks : vector nat n), sorted ks ->
    (forall i (ip : i < p), Vin i ks -> R (Vnth ts ip) (Vnth us ip)) ->
    Vreln_opt R (Vopt_filter ks ts) (Vopt_filter ks us).

Proof.
  induction ks as [|k n ks IH]; intros kks_sorted tsus; simpl.
  (* Vnil *)
  assert (a : 0<=0). omega. ex 0 a. rewrite !Vsub_nil, !Vreln_cast. split; refl.
  (* Vcons *)
  destruct (lt_dec k p).
  (* k < p *)
  gen (sorted_cons_elim kks_sorted); intro ks_sorted.
  assert (tsus' : forall i (ip:i<p), Vin i ks -> R (Vnth ts ip) (Vnth us ip)).
  intros i ip hi. apply tsus. simpl. auto.
  gen (IH ks_sorted tsus'). intros [i [i1 [i2 i3]]].
  assert (a : S i <= S n). omega. ex (S i) a. split.

  apply Vforall2n_intro. intros j jSi. rewrite !Vnth_sub, !Vnth_cons. simpl.
  destruct (lt_ge_dec 0 j).
  assert (b : j - 1 < i). omega. gen (Vreln_elim_nth b i2). rewrite !Vnth_sub.
  erewrite Vnth_eq. erewrite Vnth_eq with (v := Vopt_filter ks us).
  apply impl_refl. omega. omega.
  apply opt_intro. apply tsus. fo.

  apply Vforall2n_intro. intros j hj. rewrite !Vnth_sub, !Vnth_cons.
  destruct (lt_ge_dec 0 (S i + j)). 2: omega.
  assert (b : j < n - i). omega. gen (Vreln_elim_nth b i3). rewrite !Vnth_sub.
  erewrite Vnth_eq. erewrite Vnth_eq with (v := Vopt_filter ks us).
  apply impl_refl. omega. omega.
  (* k >= p *)
  assert (a : 0 <= S n). omega. ex 0 a. split.
  apply Vforall2n_intro. intros j hj. omega.
  apply Vforall2n_intro. intros j hj. rewrite !Vnth_sub, !Vnth_cons. simpl.
  destruct (lt_ge_dec 0 j). 2: apply opt_r_None. rewrite !Vnth_opt_filter.
  match goal with |- context C [lt_dec (Vnth ks ?x) p] => set (h := x) end.
  destruct (lt_dec (Vnth ks h) p). 2: apply opt_r_None. exfalso.
  unfold sorted in kks_sorted.
  assert (ai : 0 < S n). omega. assert (aj : j < S n). omega.
  gen (kks_sorted _ ai _ aj l). rewrite !Vnth_cons.
  destruct (lt_ge_dec 0 0). omega. destruct (lt_ge_dec 0 j). 2: omega.
  rewrite Vnth_eq with (h2:=h). omega. omega.
Qed.
