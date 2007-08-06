(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-04-02
- Frederic Blanqui, 2005-01-27
- Adam Koprowski and Hans Zantema, 2007-03-26

extension of the Coq library Bool/Bvector
*)

(* $Id: VecUtil.v,v 1.20 2007-08-06 16:08:38 blanqui Exp $ *)

Set Implicit Arguments.

Require Export LogicUtil.
Require Export Bvector.

Implicit Arguments Vnil [A].
Implicit Arguments Vcons.
Implicit Arguments Vhead.
Implicit Arguments Vtail.
Implicit Arguments Vconst.

(*Ltac Veqtac := repeat
  match goal with
    | H : @Vcons ?B ?x _ ?v = Vcons ?x ?w |- _ =>
      let H1 := fresh in let H3 := fresh in
      (injection H; intro H1; assert (H3 : v = w);
      [apply (inj_pairT2 nat (fun n => @vector B n)); assumption | clear H H1])
    | H : @Vcons ?B ?x _ ?v = Vcons ?y ?w |- _ =>
      let H1 := fresh in let H2 := fresh in let H3 := fresh in
      (injection H; intros H1 H2; subst x; assert (H3 : v = w);
      [apply (inj_pairT2 nat (fun n => @vector B n)); assumption | clear H H1])
  end.*)

Require Export NatUtil.

Ltac Veqtac := repeat
  match goal with
    | H : @Vcons ?B ?x _ ?v = Vcons ?x ?w |- _ =>
      let H1 := fresh in
      (injection H; intro H1; deduce (inj_pairT2 eq_nat_dec H1); clear H)
    | H : @Vcons ?B ?x _ ?v = Vcons ?y ?w |- _ =>
      let H1 := fresh in let H2 := fresh in
      (injection H; intros H1 H2; subst x; deduce (inj_pairT2 eq_nat_dec H1);
        clear H)
  end.

Section S.

Variable A : Set.

Notation vec := (vector A).

(***********************************************************************)
(** elementary identities *)

Definition Vid n : vec n -> vec n :=
  match n return vec n -> vec n with
    | O => fun _ => Vnil
    | _ => fun v => Vcons (Vhead v) (Vtail v)
  end.

Lemma Vid_eq : forall n (v : vec n), v = Vid v.

Proof.
destruct v; auto.
Defined.

Lemma VSn_eq : forall n (v : vec (S n)), v = Vcons (Vhead v) (Vtail v).

Proof.
intros.
change (Vcons (Vhead v) (Vtail v)) with (Vid v).
apply Vid_eq.
Defined.

Ltac VSntac y :=
  match type of y with
    | vector _ (S _) => let H := fresh in
      (assert (H : y = Vcons (Vhead y) (Vtail y)); [apply VSn_eq | rewrite H])
  end.

Lemma Vcons_eq : forall a1 a2 n (v1 v2 : vec n),
  a1 = a2 -> v1 = v2 -> Vcons a1 v1 = Vcons a2 v2.

Proof.
intros. subst a1. subst v1. reflexivity.
Qed.

Lemma Vtail_eq : forall a n (v1 v2 : vec n), v1 = v2 -> 
  Vcons a v1 = Vcons a v2.

Proof.
intros. apply Vcons_eq. reflexivity. assumption.
Qed.

(***********************************************************************)
(** cast *)

Require Export NatUtil.

Fixpoint Vcast m (v : vec m) {struct v} : forall n, m=n -> vec n :=
  match v in vector _ m return forall n, m=n -> vec n with
    | Vnil => fun n =>
      match n return O = n -> vec n with
	| O => fun _ => Vnil
	| S n' => fun H => False_rec (vec (S n')) (O_S n' H)
      end
    | Vcons x m' w => fun n =>
      match n return S m' = n -> vec n with
	| O => fun H => False_rec (vec O) (S_neq_O H)
	| S n' => fun H => Vcons x (Vcast w (f_equal pred H))
      end
  end.

Lemma Vcast_refl_eq : forall n (v : vec n) (H : n=n), Vcast v H = v.

Proof.
induction v; simpl; intros. reflexivity.
assert (E : Vcast v (f_equal pred H) = v). apply IHv.
simpl in E. rewrite E. reflexivity.
Defined.

Lemma Vcast_refl : forall n (v : vec n), Vcast v (refl_equal n) = v.

Proof.
intros. apply Vcast_refl_eq.
Defined.

Lemma Vcast_eq_elim : forall n (v1 v2 : vec n) m (h : n = m),
  Vcast v1 h = Vcast v2 h -> v1 = v2.

Proof.
intros until v1. destruct v1; intros; destruct m.
simpl in H. rewrite <- (Vcast_refl_eq v2 h). assumption.
discriminate. discriminate.
assert (n = m). apply eq_add_S. assumption. subst n.
assert (h = refl_equal (S m)). apply (UIP eq_nat_dec). subst h.
simpl in H. rewrite (Vcast_refl v1) in H. rewrite (Vcast_refl v2) in H.
assumption.
Qed.

Lemma Vcast_cast_eq : forall n (v : vec n) m (h1 : n=m) p (h2 : m=p) (h3 : n=p),
  Vcast (Vcast v h1) h2 = Vcast v h3.

Proof.
induction v; intro m; case m; intros until p; case p; simpl; intros;
  (discriminate || auto).
apply Vtail_eq. apply IHv.
Qed.

Lemma Vcast_cast : forall n (v : vec n) m (h1 : n=m) p (h2 : m=p),
  Vcast (Vcast v h1) h2 = Vcast v (trans_eq h1 h2).

Proof.
intros. apply Vcast_cast_eq.
Qed.

Lemma Vcast_eq_intror : forall n1 (v1 : vec n1) n0 (h1 : n1=n0)
  n2 (v2 : vec n2) (h2 : n2=n0) (h : n1=n2),
  Vcast v1 h = v2 -> Vcast v1 h1 = Vcast v2 h2.

Proof.
induction v1; intros until n0; case n0; intros until v2; case v2; simpl; 
intros; (discriminate || auto). Veqtac. apply Vtail_eq. eapply IHv1. apply H1.
Qed.

Lemma Vcast_eq : forall n (v : vec n) p (h1 : n=p) (h2 : n=p),
  Vcast v h1 = Vcast v h2.

Proof.
induction v; intros until p; case p; intros; simpl; (discriminate || auto).
apply Vtail_eq. apply IHv.
Qed.

Lemma Vcast_lr : forall n1 (v1 : vec n1) n2 (v2 : vec n2) (h12 : n1=n2)
  (h21 : n2=n1), Vcast v1 h12 = v2 -> v1 = Vcast v2 h21.

Proof.
induction v1; induction v2; simpl; intros. refl. discriminate. discriminate.
Veqtac. apply Vtail_eq. eapply IHv1. apply H1.
Qed.

Lemma Vcast_rl : forall n1 (v1 : vec n1) n2 (v2 : vec n2) (h12 : n1=n2)
  (h21 : n2=n1), v1 = Vcast v2 h21 -> Vcast v1 h12 = v2.

Proof.
induction v1; induction v2; simpl; intros. refl. discriminate. discriminate.
Veqtac. apply Vtail_eq. eapply IHv1. apply H1.
Qed.

Lemma Vcast_introrl : forall n1 (v1 : vec n1) n2 (v2 : vec n2) (h21 : n2=n1),
  Vcast v1 (sym_eq h21) = v2 -> v1 = Vcast v2 h21.

Proof.
intros. eapply Vcast_lr. apply H.
Qed.

Lemma Vcast_elimlr : forall n1 (v1 : vec n1) n2 (v2 : vec n2) (h12 : n1=n2),
  Vcast v1 h12 = v2 -> v1 = Vcast v2 (sym_eq h12).

Proof.
intros. eapply Vcast_lr. apply H.
Qed.

(***********************************************************************)
(** null vector *)

Lemma VO_eq : forall v : vec O, v = Vnil.

Proof.
cut (forall n (v : vec n) (h: n=0), Vcast v h = Vnil).
intros. deduce (H 0 v (refl_equal 0)). rewrite Vcast_refl in H0. assumption.
destruct v. auto. intro. discriminate.
Defined.

Ltac VOtac := repeat
  match goal with
    | v : vector _ O |- _ => assert (v = Vnil); [apply VO_eq | subst v]
  end.

(***********************************************************************)
(** add an element at the end *)

Fixpoint Vadd n (v : vec n) (x : A) { struct v } : vec (S n) :=
  match v in vector _ n return vec (S n) with
    | Vnil => Vcons x Vnil
    | Vcons a _ v' => Vcons a (Vadd v' x)
  end.

(***********************************************************************)
(** i-th element *)

Require Export Arith.

Fixpoint Vnth n (v : vec n) {struct v} : forall i, i<n -> A :=
  match v in vector _ n return forall i, i<n -> A with
    | Vnil => fun i H => False_rec A (lt_n_O i H)
    | Vcons x p v' => fun i =>
      match i return i < S p -> A with
	| O => fun _ => x
	| S j => fun H => Vnth v' (lt_S_n H)
      end
  end.

Lemma Vhead_nth : forall n (v : vec (S n)), Vhead v = Vnth v (lt_O_Sn n).

Proof.
intros. VSntac v. reflexivity.
Qed.

Require Export NatUtil.
Require Omega.

Lemma Vnth_eq : forall n (v : vec n) i1 (h1 : i1<n) i2 (h2 : i2<n),
  i1 = i2 -> Vnth v h1 = Vnth v h2.

Proof.
induction v; intro; case i1.
intro. absurd (0 <= 0); omega.
intros n h1. absurd (0 <= S n); omega.
intros. subst i2. reflexivity.
intros. subst i2. simpl. apply IHv. reflexivity.
Qed.

Lemma Vnth_tail : forall n (v : vec (S n)) i (h : i < n),
  Vnth (Vtail v) h = Vnth v (lt_n_S h).

Proof.
intros. VSntac v. simpl. apply Vnth_eq. reflexivity.
Qed.

Lemma Vnth_cons : forall k n (v : vec n) a (H1 : S k < S n) (H2 : k < n),
 Vnth (Vcons a v) H1 = Vnth v H2.

Proof.
intros. simpl. assert (H : lt_S_n H1 = H2). apply lt_unique.
rewrite H. reflexivity.
Qed.

Lemma Veq_nth : forall n (v v' : vec n), 
  (forall i (ip : i < n), Vnth v ip = Vnth v' ip) -> v = v'.

Proof.
induction n; intros.
VOtac. refl.
VSntac v. VSntac v'. apply Vcons_eq.
do 2 rewrite Vhead_nth. apply H.
apply IHn. intros. do 2 rewrite Vnth_tail. apply H.
Qed.

Lemma Vnth_head : forall x n (v : vec n) k (h : k < S n),
  k = 0 -> Vnth (Vcons x v) h = x.

Proof.
intros. subst k. reflexivity.
Qed.

Lemma Vnth_addl : forall k n (v : vec n) a (H1 : k < S n) (H2 : k < n),
  Vnth (Vadd v a) H1 = Vnth v H2.

Proof.
intros. assert (H3 : H1 = (le_S _ _ H2)). apply lt_unique.
subst H1. generalize dependent k. generalize dependent n. intro n. elim n.
 intros v k H. elimtype False. apply (lt_n_O _ H).
 intros n' Hrec v k H. rewrite (VSn_eq v). destruct k.
  simpl. reflexivity.
  simpl Vadd.
  assert (H' : k < S n'). auto with arith.
  rewrite (Vnth_cons (Vadd (Vtail v) a) (Vhead v) (le_S (S (S k)) (S n') H) H').
  assert (H'' : k < n'). auto with arith.
  rewrite (Vnth_cons (Vtail v) (Vhead v) H H'').
  generalize (Hrec (Vtail v) k H''). intro H0.
  assert (H1 : H' = le_S (S k) n' H''). apply lt_unique. rewrite H1. clear H1.
  assumption.
Qed.

Lemma Vnth_addr : forall k n (v : vec n) a (H1 : k < S n) (H2 : k = n),
  Vnth (Vadd v a) H1 = a.

Proof.
intros. subst k. assert (H2 : H1 = lt_n_Sn n). apply lt_unique. subst H1.
generalize dependent v. intro v. elim v.
simpl. reflexivity.
intros a' p' v' Hrec. simpl Vadd.
rewrite (Vnth_cons (Vadd v' a) a' (lt_n_Sn (S p')) (lt_n_Sn p')).
assumption.
Qed.

Lemma Vnth_const : forall n (a : A) i (ip : i < n),
  Vnth (Vconst a n) ip = a.

Proof.
induction n; intros. absurd_arith.
destruct i. trivial.
simpl. rewrite IHn. refl.
Qed.

(***********************************************************************)
(** replacement of i-th element *)

Lemma Vreplace : forall n (v : vec n) i (ip : i < n) (a : A), vec n.

Proof.
induction n; intros.  
elimtype False. exact (lt_n_O i ip). 
destruct i. exact (Vcons a (Vtail v)).  
exact (Vcons (Vhead v) (IHn (Vtail v) i (lt_S_n ip) a)).
Defined.

Lemma Vreplace_tail : forall n i (ip : S i < S n) (v : vec (S n)) (a : A),
  Vreplace v ip a = Vcons (Vhead v) (Vreplace (Vtail v) (lt_S_n ip) a).

Proof.
destruct n; intros. absurd_arith.
destruct i; refl.
Qed.

(***********************************************************************)
(** concatenation *)

Fixpoint Vapp n1 n2 (v1 : vec n1) (v2 : vec n2) {struct v1} : vec (n1+n2) :=
  match v1 in vector _ n1 return vec (n1+n2) with
    | Vnil => v2
    | Vcons a _ v' => Vcons a (Vapp v' v2)
  end.

Lemma Vapp_cons : forall a n1 n2 (v1 : vec n1) (v2 : vec n2),
  Vapp (Vcons a v1) v2 = Vcons a (Vapp v1 v2).

Proof.
intros. simpl. reflexivity.
Qed.

Lemma Vapp_nil_eq : forall n (v : vec n) (w : vec 0) (h : n=n+0),
  Vapp v w = Vcast v h.

Proof.
induction v; intros. VOtac. reflexivity.
simpl. apply Vtail_eq. apply IHv.
Qed.

Lemma Vapp_nil : forall n (v : vec n) (w : vec 0), 
  Vapp v w = Vcast v (plus_n_O n).

Proof.
intros. apply Vapp_nil_eq.
Qed.

Lemma Vapp_rcast_eq : forall n1 (v1 : vec n1) n2 (v2 : vec n2) p2 (h1 : n2=p2)
  (h2 : n1+n2=n1+p2), Vapp v1 (Vcast v2 h1) = Vcast (Vapp v1 v2) h2.

Proof.
induction v1; simpl; intros.
assert (h1=h2). apply (UIP eq_nat_dec). rewrite H. refl.
apply Vtail_eq. apply IHv1.
Qed.

Lemma Vapp_rcast : forall n1 (v1 : vec n1) n2 (v2 : vec n2) p2 (h1 : n2=p2),
  Vapp v1 (Vcast v2 h1) = Vcast (Vapp v1 v2) (plus_reg_l_inv n1 h1).

Proof.
intros. apply Vapp_rcast_eq.
Qed.

Lemma Vapp_lcast_eq : forall n1 (v1 : vec n1) n2 (v2 : vec n2) p1 (h1 : n1=p1)
  (h2 : n1+n2=p1+n2), Vapp (Vcast v1 h1) v2 = Vcast (Vapp v1 v2) h2.

Proof.
induction v1; intros until p1; case p1; simpl; intros.
rewrite Vcast_refl_eq. reflexivity. discriminate. discriminate.
apply Vtail_eq. apply IHv1.
Qed.

Lemma Vapp_lcast :  forall n1 (v1 : vec n1) n2 (v2 : vec n2) p1 (h1 : n1=p1),
  Vapp (Vcast v1 h1) v2 = Vcast (Vapp v1 v2) (plus_reg_r_inv n2 h1).

Proof.
intros. apply Vapp_lcast_eq.
Qed.

Lemma Vapp_assoc_eq : forall n1 (v1 : vec n1) n2 (v2 : vec n2) n3 (v3 : vec n3)
  (h : n1+(n2+n3) = (n1+n2)+n3),
  Vapp (Vapp v1 v2) v3 = Vcast (Vapp v1 (Vapp v2 v3)) h.

Proof.
induction v1; intros; simpl.
rewrite Vcast_refl_eq. reflexivity.
apply Vtail_eq. apply IHv1.
Qed.

Lemma Vapp_assoc : forall n1 (v1 : vec n1) n2 (v2 : vec n2) n3 (v3 : vec n3),
  Vapp (Vapp v1 v2) v3 = Vcast (Vapp v1 (Vapp v2 v3)) (plus_assoc n1 n2 n3).

Proof.
intros. apply Vapp_assoc_eq.
Qed.

Lemma Vapp_eq : forall n1 (v1 v1' : vec n1) n2 (v2 v2' : vec n2),
  v1 = v1' -> v2 = v2' -> Vapp v1 v2 = Vapp v1' v2'.

Proof.
intros. rewrite H. rewrite H0. reflexivity.
Qed.

(***********************************************************************)
(** breaking a vector in various pieces *)

Definition Vsplit n (v : vec (S n)) := (Vhead v, Vtail v).

Fixpoint Vbreak n1 n2 {struct n1} : vec (n1+n2) -> vec n1 * vec n2 :=
  match n1 as n1 return vec (n1+n2) -> vec n1 * vec n2
    with
    | O => fun v => (Vnil, v)
    | S p1 => fun v =>
      let w := Vbreak p1 n2 (Vtail v) in (Vcons (Vhead v) (fst w), snd w)
  end.

Implicit Arguments Vbreak [n1 n2].

Lemma Vbreak_app : forall n1 (v1 : vec n1) n2 (v2 : vec n2),
  Vbreak (Vapp v1 v2) = (v1, v2).

Proof.
induction n1; simpl; intros. VOtac. reflexivity. VSntac v1. simpl.
generalize (IHn1 (Vtail v1) n2 v2). intro. rewrite H0. reflexivity.
Qed.

Lemma Vbreak_eq_app : forall n1 n2 (v : vec (n1+n2)),
  v = Vapp (fst (Vbreak v)) (snd (Vbreak v)).

Proof.
intros n1 n2. elim n1.
 auto.
 clear n1. intros n1 Hrec. simpl.
 intro v.
 generalize (Hrec (Vtail v)).
intro H. transitivity (Vcons (Vhead v) (Vtail v)).
apply VSn_eq. rewrite H. auto.
Qed.

Lemma Vbreak_eq_app_cast : forall n n1 n2 (H : n1+n2=n) (v : vec n),
  v = Vcast (Vapp (fst (Vbreak (Vcast v (sym_equal H))))
    (snd (Vbreak (Vcast v (sym_equal H))))) H.

Proof.
intros until H. case H. simpl. intro v.
repeat rewrite Vcast_refl. apply Vbreak_eq_app.
Qed.

(***********************************************************************)
(** membership *)

Fixpoint Vin (x : A) n (v : vec n) {struct v} : Prop :=
  match v with
    | Vnil => False
    | Vcons y _ w => x = y \/ Vin x w
  end.

Lemma Vin_head : forall n (v : vec (S n)), Vin (Vhead v) v.

Proof.
intros. VSntac v. simpl. auto.
Qed.

Lemma Vin_tail : forall n x (v : vec (S n)), Vin x (Vtail v) -> Vin x v.

Proof.
  intros. VSntac v. simpl. auto.
Qed.

Lemma Vnth_in : forall n (v : vec n) k (h : k<n), Vin (Vnth v h) v.

Proof.
induction v. intros. absurd (k<0); omega.
intro. destruct k; simpl. auto. intro. right. apply IHv.
Qed.

Lemma Vin_nth : forall n (v : vec n) a, Vin a v ->
  exists i, exists ip : i < n, Vnth v ip = a.

Proof.
  induction n; intros. 
  VOtac. destruct H.
  VSntac v. rewrite H0 in H. destruct H.
  exists 0. exists (lt_O_Sn n). simpl. congruence.
  destruct (IHn (Vtail v) a H) as [j [jp v_j]]. 
  exists (S j). exists (lt_n_S jp). simpl.
  rewrite lt_Sn_nS. assumption.
Qed.

Lemma Vin_cast_intro : forall m n (H : m=n) (v : vec m) x,
  Vin x v -> Vin x (Vcast v H).

Proof.
intros m n H. case H. intros. rewrite Vcast_refl. assumption.
Qed.

Lemma Vin_cast_elim : forall m n (H : m=n) (v : vec m) x,
  Vin x (Vcast v H) -> Vin x v.

Proof.
intros m n H. case H. intros v x. rewrite Vcast_refl. auto.
Qed.

Implicit Arguments Vin_cast_elim [m n H v x].

Lemma Vin_appl : forall x n1 (v1 : vec n1) n2 (v2 : vec n2),
  Vin x v1 -> Vin x (Vapp v1 v2).

Proof.
induction v1; simpl; intros. contradiction. destruct H. auto.
right. apply IHv1. assumption.
Qed.

Lemma Vin_appr : forall x n1 (v1 : vec n1) n2 (v2 : vec n2),
  Vin x v2 -> Vin x (Vapp v1 v2).

Proof.
induction v1; simpl; intros. assumption. right. apply IHv1. assumption.
Qed.

Lemma Vin_app_cons : forall x n1 (v1 : vec n1) n2 (v2 : vec n2),
  Vin x (Vapp v1 (Vcons x v2)).

Proof.
induction v1; intros; simpl; auto.
Qed.

Lemma Vin_app : forall x n1 (v1 : vec n1) n2 (v2 : vec n2),
  Vin x (Vapp v1 v2) -> Vin x v1 \/ Vin x v2.

Proof.
induction v1; intros; simpl in * . auto. destruct H. auto.
assert (Vin x v1 \/ Vin x v2). apply IHv1. exact H. destruct H0; auto.
Qed.

Lemma S_add_S : forall n1 n2 n, n1 + S n2 = n -> S n1 + S n2 = S n.

Proof.
intros. subst n. reflexivity.
Qed.

Implicit Arguments S_add_S [n1 n2 n].

Lemma Vin_elim : forall x n (v : vec n),
  Vin x v -> exists n1, exists v1 : vec n1, exists n2, exists v2 : vec n2,
    exists H : n1 + S n2 = n, v = Vcast (Vapp v1 (Vcons x v2)) H.

Proof.
induction v; simpl. contradiction.
intro H. destruct H. clear IHv. subst x.
exists 0. exists (@Vnil A). exists n. exists v. exists (refl_equal (S n)).
rewrite Vcast_refl. reflexivity.
assert (exists n1, exists v1 : vec n1, exists n2, exists v2 : vec n2,
  exists H : n1 + S n2 = n, v = Vcast (Vapp v1 (Vcons x v2)) H). exact (IHv H).
destruct H0 as [n1]. destruct H0 as [v1]. destruct H0 as [n2].
destruct H0 as [v2].
destruct H0 as [H1].
exists (S n1). exists (Vcons a v1). exists n2. exists v2. exists (S_add_S H1).
rewrite H0. clear H0. simpl.
assert (f_equal pred (S_add_S H1) = H1). apply (UIP eq_nat_dec).
simpl in H0. rewrite H0. refl.
Qed.

(***********************************************************************)
(** proposition saying that all the elements of a vector satisfy some
predicate *)

Fixpoint Vforall (P : A->Prop) n (v : vec n) { struct v } : Prop :=
  match v with
    | Vnil => True
    | Vcons a _ w => P a /\ Vforall P w
  end.

Lemma Vforall_intro : forall (P : A->Prop) n (v : vec n),
  (forall x, Vin x v -> P x) -> Vforall P v.

Proof.
induction v; simpl; intros. exact I. split.
apply H. left. reflexivity. apply IHv. intros. apply H. right. assumption.
Qed.

Lemma Vforall_nth_intro : forall (P : A -> Prop) n (v : vec n),
  (forall i (ip : i < n), P (Vnth v ip)) -> Vforall P v.

Proof.
  intros. apply Vforall_intro. intros.
  destruct (Vin_nth v x H0) as [i [ip v_i]].
  rewrite <- v_i. apply H.
Qed.

Lemma Vforall_in : forall P x n (v : vec n), Vforall P v -> Vin x v -> P x.

Proof.
induction v; simpl.
contradiction.
intros Ha Hv. destruct Ha. destruct Hv.
rewrite H1. exact H.
auto.
Qed.

Lemma Vforall_nth : forall P n (v : vec n) i (ip : i < n), 
  Vforall P v -> P (Vnth v ip).

Proof.
  intros. apply Vforall_in with n v. assumption. apply Vnth_in.
Qed.

Lemma Vforall_incl : forall (P : A->Prop) n1 (v1 : vec n1) n2 (v2 : vec n2),
  (forall x, Vin x v1 -> Vin x v2) -> Vforall P v2 -> Vforall P v1.

Proof.
intros. apply Vforall_intro. intros. apply Vforall_in with (v := v2).
assumption. apply H. assumption.
Qed.

Lemma Vforall_cast : forall P n v p (h : n=p),
  Vforall P v -> Vforall P (Vcast v h).

Proof.
intros. apply Vforall_intro. intros.
eapply Vforall_in with (n := n). apply H. deduce (Vin_cast_elim H0). assumption.
Qed.

Lemma Vforall_imp : forall (P Q : A->Prop) n (v : vec n),
  Vforall P v -> (forall x, Vin x v -> P x -> Q x) -> Vforall Q v.

Proof.
intros. apply Vforall_intro. intros. apply H0. assumption.
eapply Vforall_in with (n := n). apply H. apply H1.
Qed.

Require Import RelMidex.

Lemma Vforall_dec : forall (P : A -> Prop) (P_dec : prop_dec P) n,
  prop_dec (fun v => @Vforall P n v).

Proof.
  induction n; unfold prop_dec; intros.
  VOtac. left. constructor.
  VSntac x. destruct (P_dec (Vhead x)).
  destruct (IHn (Vtail x)).
  left. simpl. split; assumption.
  right. intro V. destruct V. contradiction.
  right. intro V. destruct V. contradiction.
Defined.

Fixpoint Vsig_of_v (P : A->Prop) n (v : vec n) {struct v}
  : Vforall P v -> vector (sig P) n :=
  match v in vector _ n return Vforall P v -> vector (sig P) n with
    | Vnil => fun _ => Vnil
    | Vcons a _ w => fun H =>
      Vcons (exist P a (proj1 H)) (Vsig_of_v P w (proj2 H))
  end.

(***********************************************************************)
(** proposition saying that the elements of two vectors are pair-wise
in relation *)

Section Vforall2_sec.

Variable R : A -> A -> Prop.

Fixpoint Vforall2 n1 (v1 : vec n1) n2 (v2 : vec n2) {struct v1} : Prop :=
  match eq_nat_dec n1 n2 with
  | left _ =>
      match v1 with
      | Vnil => True
      | Vcons a _ v =>
          match v2 with
	  | Vnil => False
	  | Vcons b _ w => R a b /\ Vforall2 v w
	  end
      end
  | _ => False
  end.

Definition Vforall2n n (v1 v2 : vec n) := Vforall2 v1 v2.

Lemma Vforall2_tail : forall n (v1 v2 : vec (S n)), Vforall2 v1 v2 ->
  Vforall2 (Vtail v1) (Vtail v2).

Proof.
  intros.
  VSntac v1. rewrite H0 in H.
  VSntac v2. rewrite H1 in H.
  simpl in H. destruct (eq_nat_dec n n). 
  destruct H. assumption.
  contradiction.
Qed.

Lemma Vforall2_nth : forall n (v1 : vector A n) (v2 : vector A n) i 
  (ip : i < n), Vforall2n v1 v2 -> R (Vnth v1 ip) (Vnth v2 ip).

Proof.
  induction n; intros. absurd_arith.
  VSntac v1. VSntac v2. 
  destruct i. simpl.
  rewrite H0 in H. rewrite H1 in H.
  unfold Vforall2n in H. simpl in H.
  destruct (eq_nat_dec n n). destruct H. trivial.
  contradiction.
  simpl. apply IHn. 
  unfold Vforall2n. apply Vforall2_tail. assumption.
Qed.

Lemma Vforall2_intro : forall n (v1 : vec n) (v2 : vec n),
  (forall i (ip : i < n), R (Vnth v1 ip) (Vnth v2 ip)) -> Vforall2n v1 v2.

Proof.
  induction n; intros.
  VOtac. constructor.
  VSntac v1. VSntac v2.
  unfold Vforall2n. simpl. 
  destruct (eq_nat_dec n n). split.
  do 2 rewrite Vhead_nth. apply H.
  apply IHn. intros. 
  do 2 rewrite Vnth_tail. apply H.
  absurd_arith.
Qed.

Require Import RelDec.

Variable R_dec : rel_dec R.

Lemma Vforall2_dec : forall n1 (v1 : vector A n1) n2 (v2 : vector A n2), 
  {Vforall2 v1 v2} + {~Vforall2 v1 v2}.

Proof.
  induction v1; intros; destruct v2; simpl; auto.
  destruct (eq_nat_dec n n0); simpl; auto.
  destruct (IHv1 n0 v2); intuition.
  destruct (R_dec a a0); intuition.
Defined.

Lemma Vforall2n_dec : forall n, rel_dec (@Vforall2n n).

Proof.
  intros n v1 v2. unfold Vforall2n. apply Vforall2_dec.
Defined.

End Vforall2_sec.

(***********************************************************************)
(** vector construction *)

Definition Vbuild_spec : forall n (gen : forall i, i < n -> A), 
  { v : vec n | forall i (ip : i < n), Vnth v ip = gen i ip }.

Proof.
  induction n; intros.
  exists (Vnil (A:=A)). intros. 
  elimtype False. exact (lt_n_O i ip).   
  set (gen' := fun i H => gen (S i) (lt_n_S H)).
  set (access0 := lt_O_Sn n).
  destruct (IHn gen') as [v vs].
  exists (Vcons(gen 0 access0) v). intros.
  destruct i; simpl.
  rewrite (le_unique ip (lt_O_Sn n)). refl.
  rewrite vs. unfold gen'. rewrite (le_unique (lt_n_S (lt_S_n ip)) ip). refl.
Defined.

Definition Vbuild n gen : vec n := proj1_sig (Vbuild_spec gen).

Lemma Vbuild_nth : forall n gen i (ip : i < n), 
  Vnth (Vbuild gen) ip = gen i ip.

Proof.
  intros. unfold Vbuild. destruct (Vbuild_spec gen). simpl. apply e.
Qed.

Lemma Vbuild_head : forall n (gen : forall i, i < S n -> A),
  Vhead (Vbuild gen) = gen 0 (lt_O_Sn n).

Proof.
  intros. unfold Vbuild. destruct (Vbuild_spec gen). simpl.
  rewrite Vhead_nth. apply e.
Qed.

Lemma Vbuild_tail : forall n (gen : forall i, i < S n -> A),
  Vtail (Vbuild gen) = Vbuild (fun i ip => gen (S i) (lt_n_S ip)).

Proof.
  intros. apply Veq_nth. intros.
  rewrite Vnth_tail. do 2 rewrite Vbuild_nth. refl.
Qed.

(***********************************************************************)
(** iteration *)

(* Vfold_left f b [a1 .. an] = f .. (f (f b x1) x2) .. xn *)

Fixpoint Vfold_left (B:Set) (f : B->A->B) (b:B) n (v : vec n) {struct v} : B :=
  match v with
    | Vnil => b
    | Vcons a _ w => f (Vfold_left f b w) a
  end.

(* Vfold_right f [a1 .. an] b = f x1 (f x2 .. (f xn b) .. ) *)

Fixpoint Vfold_right (B:Set) (f : A->B->B) n (v : vec n) (b:B) {struct v} : B :=
  match v with
    | Vnil => b
    | Vcons a _ w => f a (Vfold_right f w b)
  end.

(***********************************************************************)
(** conversion to lists *)

Require Export List.

Fixpoint vec_of_list (l : list A) : vec (length l) :=
  match l as l return vec (length l) with
    | nil => Vnil
    | cons x m => Vcons x (vec_of_list m)
  end.

Fixpoint list_of_vec n (v : vec n) {struct v} : list A :=
  match v with
    | Vnil => nil
    | Vcons x _ v => x :: list_of_vec v
  end.

(***********************************************************************)
(** decidability of equality *)

Variable eq_dec : forall x y : A, {x=y}+{~x=y}.

Lemma eq_vec_dec : forall n (v1 v2 : vec n), {v1=v2}+{~v1=v2}.

Proof.
induction v1; intro. VOtac. auto. VSntac v2.
case (eq_dec a (Vhead v2)); intro.
rewrite e. case (IHv1 (Vtail v2)); intro. rewrite e0. auto.
right. unfold not. intro. Veqtac. auto.
right. unfold not. intro. Veqtac. auto.
Defined.

End S.

(***********************************************************************)
(** declaration of implicit arguments *)

Implicit Arguments VSn_eq [A n].
Implicit Arguments Vsig_of_v [A P n v].
Implicit Arguments Vbreak [A n1 n2].
Implicit Arguments Vbreak_eq_app [A n1 n2].
Implicit Arguments Vbreak_eq_app_cast [A n n1 n2].
Implicit Arguments Vforall_in [A P x n v].
Implicit Arguments Vin_cast_elim [A m n H v x].
Implicit Arguments Vin_elim [A x n v].
Implicit Arguments Vin_app [A x n1 v1 n2 v2].

(***********************************************************************)
(** tactics *)

Ltac VOtac := repeat
  match goal with
    | v : vector _ O |- _ => assert (v = Vnil); [apply VO_eq | subst v]
  end.

Ltac VSntac y :=
  match type of y with
    | vector _ (S _) => let H := fresh in
      (assert (H : y = Vcons (Vhead y) (Vtail y)); [apply VSn_eq | rewrite H])
  end.

Ltac castrefl h := rewrite (UIP_refl eq_nat_dec h); rewrite Vcast_refl; refl.

(***********************************************************************)
(** map *)

Section map.

Variables (A B : Set) (f : A->B).

Fixpoint Vmap n (v : vector A n) {struct v} : vector B n :=
  match v in vector _ n return vector B n with
    | Vnil => Vnil
    | Vcons a _ v' => Vcons (f a) (Vmap v')
  end.

Lemma Vnth_map : forall n (v : vector A n) i (H : i < n),
  Vnth (Vmap v) H = f (Vnth v H).

Proof.
intros n. elim n.
 intros v i H. elimtype False. apply (lt_n_O _ H).
 clear n. intros n Hrec v i. case i.
  intro. rewrite (VSn_eq v). simpl. reflexivity.
  clear i. intros i Hi. rewrite (VSn_eq v). simpl.
  apply (Hrec (Vtail v) i (lt_S_n Hi)).
Qed.

Lemma Vin_map : forall x n (v : vector A n), Vin x (Vmap v)
  -> exists y, Vin y v /\ x = f y.

Proof.
induction v; simpl; intros. contradiction. destruct H. subst x. exists a. auto.
assert (exists y, Vin y v /\ x = f y). apply IHv. assumption.
destruct H0 as [y]. exists y. intuition.
Qed.

Lemma Vin_map_intro : forall x n (v : vector A n),
  Vin x v -> Vin (f x) (Vmap v).

Proof.
induction v; simpl; intros. contradiction. destruct H. subst x. auto. intuition.
Qed.

Lemma Vforall_map_elim : forall (P : B->Prop) n (v : vector A n),
  Vforall P (Vmap v) -> Vforall (fun a : A => P (f a)) v.

Proof.
induction v; simpl; intuition.
Qed.

Lemma Vforall_map_intro : forall (P : B->Prop) n (v : vector A n),
  Vforall (fun a : A => P (f a)) v -> Vforall P (Vmap v).

Proof.
induction v; simpl; intuition.
Qed.

Lemma Vmap_app : forall n1 n2 (v1 : vector A n1) (v2 : vector A n2),
  Vmap (Vapp v1 v2) = Vapp (Vmap v1) (Vmap v2).

Proof.
intros; induction v1.
simpl; auto.
simpl. rewrite IHv1. reflexivity.
Qed.

Lemma Vmap_cast : forall m n (H : m=n) (v : vector A m),
  Vmap (Vcast v H) = Vcast (Vmap v) H.

Proof.
intros until H. case H. intro v. repeat rewrite Vcast_refl. reflexivity.
Qed.

Lemma Vmap_tail : forall n (v : vector A (S n)), Vmap (Vtail v) = Vtail (Vmap v).

Proof.
intros. VSntac v. reflexivity.
Qed.

Lemma Vmap_eq_nth : forall n (v1 : vector A n) (v2 : vector B n),
  (forall i (h : i<n), f (Vnth v1 h) = Vnth v2 h) -> Vmap v1 = v2.

Proof.
induction n; simpl; intros. VOtac. reflexivity.
VSntac v1. VSntac v2. simpl. apply Vcons_eq.
do 2 rewrite Vhead_nth. apply H.
apply IHn. intros. do 2 rewrite Vnth_tail. apply H.
Qed.

End map.

Implicit Arguments Vin_map [A B f x n v].
Implicit Arguments Vforall_map_elim [A B f P n v].
Implicit Arguments Vin_map_intro [A B x n v].

(***********************************************************************)
(** map with a binary function *)

Fixpoint Vmap2 (A B C : Set) (f : A->B->C) n {struct n}
  : vector A n -> vector B n -> vector C n :=
  match n as n return vector A n -> vector B n -> vector C n with
    | O => fun _ _ => Vnil
    | _ => fun v1 v2 =>
      Vcons (f (Vhead v1) (Vhead v2)) (Vmap2 f (Vtail v1) (Vtail v2))
  end.

(* map composition *)

Lemma Vmap_map : forall (A B C : Set) (f:A->B) (g:B->C) n (v : vector A n),
  Vmap g (Vmap f v) = Vmap (fun x : A => g (f x)) v.

Proof.
intros; induction v.
simpl; reflexivity.
simpl Vmap at 2. simpl Vmap at 1.
rewrite IHv. reflexivity.
Qed.

(* nth element in a map *)

Lemma Vmap2_nth : forall (A B C : Set) (f : A -> B -> C) n 
  (vl : vector A n) (vr : vector B n) i (ip : i < n),
  Vnth (Vmap2 f vl vr) ip = f (Vnth vl ip) (Vnth vr ip).
Proof.
  induction n; intros.
  VOtac. absurd_arith.
  VSntac vl. VSntac vr. destruct i. refl. 
  simpl. apply IHn.
Qed.

(***********************************************************************)
(** vforall and specifications *)

Fixpoint Vforall_of_vsig (A : Set) (P : A -> Prop) n (v : vector (sig P) n)
  {struct v} : Vforall P (Vmap (@proj1_sig A P) v) :=
  match v in vector _ n return Vforall P (Vmap (@proj1_sig A P) v) with
    | Vnil => I
    | Vcons a _ w => conj (@proj2_sig A P a) (Vforall_of_vsig w)
  end.

Lemma Vmap_proj1 : forall (A : Set) (P : A->Prop) n (v : vector A n)
  (Hv : Vforall P v), v = Vmap (@proj1_sig A P) (Vsig_of_v Hv).

Proof.
intros A P n v. elim v.
 simpl. intro. reflexivity.
 intros a p w. intro Hrec.
 simpl. intro Hv. case Hv. intros H1 H2. simpl Vmap.
 generalize (Hrec H2). intro H. apply Vcons_eq; auto.
Qed.

Implicit Arguments Vmap_proj1 [A P n v].

(***********************************************************************)
(** equality of vmap's *)

Lemma Vmap_eq : forall (A B : Set) (f g : A->B) n (v : vector A n),
  Vforall (fun a => f a = g a) v -> Vmap f v = Vmap g v.

Proof.
induction v; simpl; intros. reflexivity. destruct H. apply Vcons_eq; auto.
Qed.

Implicit Arguments Vmap_eq [A B f g n v].

Lemma Vmap_eq_ext : forall (A B : Set) (f g : A->B), (forall a, f a = g a) ->
  forall n (v : vector A n), Vmap f v = Vmap g v.

Proof.
induction v; intros; simpl. reflexivity. apply Vcons_eq; auto.
Qed.

Lemma Vmap_id : forall (A : Set) n (v : vector A n), Vmap (fun x => x) v = v.

Proof.
induction v. reflexivity. simpl. apply Vcons_eq; auto.
Qed.

Lemma Vmap_eq_id : forall (A : Set) (f : A->A) n (v : vector A n),
  Vforall (fun a => f a = a) v -> Vmap f v = v.

Proof.
intros. rewrite <- Vmap_id. apply Vmap_eq. assumption.
Qed.

Lemma Vmap_eq_ext_id : forall (A : Set) (f : A->A), (forall a, f a = a) ->
  forall n (v : vector A n), Vmap f v = v.

Proof.
intros. rewrite <- Vmap_id. apply Vmap_eq_ext. assumption.
Qed.
