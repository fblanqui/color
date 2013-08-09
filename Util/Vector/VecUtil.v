(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-04-02
- Frederic Blanqui, 2005-01-27 and later
- Adam Koprowski and Hans Zantema, 2007-03-26
- Joerg Endrullis, 2008-06-19
- Pierre-Yves Strub, 2009-04-09
- Wang Qian & Zhang Lianyi, 2009-05-06

extension of the Coq library Vector
*)

Set Implicit Arguments.

Require Import Vector Program LogicUtil NatUtil EqUtil RelMidex ListUtil
  BoolUtil.
Require Omega.

Notation vector := Vector.t.
Notation Vnil := Vector.nil.
Notation Vcons := Vector.cons.
Notation Vhead := Vector.hd.
Notation Vtail := Vector.tl.
Notation Vconst := Vector.const.

Arguments Vnil {A}.
Implicit Arguments Vcons [A n].
Implicit Arguments Vhead [A n].
Implicit Arguments Vtail [A n].
Implicit Arguments Vconst [A].

Ltac Veqtac := repeat
  match goal with
    | H : Vcons ?x ?v = Vcons ?x ?w |- _ =>
      let h := fresh in
      (injection H; intro h; ded (inj_pairT2 eq_nat_dec h);
        clear h; clear H)
    | H : Vcons ?x ?v = Vcons ?y ?w |- _ =>
      let h1 := fresh in let h2 := fresh in
      (injection H; intros h1 h2; ded (inj_pairT2 eq_nat_dec h1);
        clear h1; clear H)
  end.

(***********************************************************************)
(** elementary identities *)

Section Velementary.

  Variable A : Type. Notation vec := (vector A).

  Definition Vid n : vec n -> vec n :=
    match n with
      | O => fun _ => Vnil
      | _ => fun v => Vcons (Vhead v) (Vtail v)
    end.

  Lemma Vid_eq : forall n (v : vec n), v = Vid v.

  Proof. destruct v; auto. Defined.

  Lemma VSn_eq : forall n (v : vec (S n)), v = Vcons (Vhead v) (Vtail v).

  Proof.
    intros. change (Vcons (Vhead v) (Vtail v)) with (Vid v). apply Vid_eq.
  Defined.

  Lemma Vcons_eq_intro : forall a1 a2 n (v1 v2 : vec n),
    a1 = a2 -> v1 = v2 -> Vcons a1 v1 = Vcons a2 v2.

  Proof. intros. subst a1. subst v1. refl. Qed.

  Lemma Vcons_eq_elim : forall a1 a2 n (v1 v2 : vec n),
    Vcons a1 v1 = Vcons a2 v2 -> a1 = a2 /\ v1 = v2.

  Proof. intros. Veqtac. auto. Qed.

  Lemma Vcons_eq : forall a1 a2 n (v1 v2 : vec n),
    Vcons a1 v1 = Vcons a2 v2 <-> a1 = a2 /\ v1 = v2.

  Proof with auto.
    split; intros. 
    apply Vcons_eq_elim... 
    destruct H. apply Vcons_eq_intro...
  Qed.

  Lemma Vtail_eq : forall a n (v1 v2 : vec n),
    v1 = v2 -> Vcons a v1 = Vcons a v2.

  Proof. intros. apply Vcons_eq_intro. refl. hyp. Qed.

End Velementary.

Ltac VSntac y := let h := fresh in gen (VSn_eq y); intro h; try rewrite h.

Lemma VSn_inv : forall A n (v : vector A (S n)),
  exists x, exists w, v = Vcons x w.

Proof. intros. VSntac v. exists (Vhead v). exists (Vtail v). refl. Qed.

(***********************************************************************)
(** First element of a vector with default value if empty. *)

Definition Vfirst A default n (v : vector A n) : A :=
  match v with
    | Vnil => default
    | Vcons x _ _ => x
  end.

(***********************************************************************)
(** cast *)

Section Vcast.

  Variable A : Type. Notation vec := (vector A).

  Program Fixpoint Vcast m (v : vec m) n (mn : m = n) : vec n :=
    match v with
      | Vnil =>
        match n with
          | 0 => Vnil
          | _ => !
        end
      | Vcons x m' v' =>
        match n with
          | 0 => !
          | S n' => Vcons x (Vcast v' _)
        end
    end.

  Lemma Vcast_refl : forall n (v : vec n) (H : n=n), Vcast v H = v.

  Proof.
    induction v; simpl; intros. refl.
    match goal with |- Vcons _ ?v' = _ => assert (E : v' = v) end. apply IHv.
    simpl in E. rewrite E. refl.
  Defined.

  Lemma Vcast_eq_elim : forall n (v1 v2 : vec n) m (h : n = m),
    Vcast v1 h = Vcast v2 h -> v1 = v2.

  Proof.
    intros until v1. destruct v1; intros; destruct m.
    simpl in H. rewrite <- (Vcast_refl v2 h). hyp.
    discr. discr.
    assert (n = m). apply eq_add_S. hyp. subst n.
    assert (h0 = refl_equal (S m)). apply eq_unique. subst h0.
    simpl in H. do 2 rewrite Vcast_refl in H. hyp.
  Qed.

  Implicit Arguments Vcast_eq_elim [n v1 v2 m h].

  Lemma Vcast_cast_eq :
    forall n (v : vec n) m (h1 : n=m) p (h2 : m=p) (h3 : n=p),
      Vcast (Vcast v h1) h2 = Vcast v h3.

  Proof.
    induction v; intro m; case m; intros until p; case p; simpl; intros;
      (discr || auto).
    apply Vtail_eq. apply IHv.
  Qed.

  Lemma Vcast_cast : forall n (v : vec n) m (h1 : n=m) p (h2 : m=p),
    Vcast (Vcast v h1) h2 = Vcast v (trans_eq h1 h2).

  Proof. intros. apply Vcast_cast_eq. Qed.

  Lemma Vcast_eq_intror : forall n1 (v1 : vec n1) n0 (h1 : n1=n0)
    n2 (v2 : vec n2) (h2 : n2=n0) (h : n1=n2),
    Vcast v1 h = v2 -> Vcast v1 h1 = Vcast v2 h2.

  Proof.
    induction v1; intros until n0; case n0; intros until v2; case v2; simpl; 
      intros; (discr || auto). Veqtac. subst h0. apply Vtail_eq.
    eapply IHv1. apply H2.
  Qed.

  Lemma Vcast_eq_intro : forall n (v1 v2 : vec n) p (e : n=p),
    v1 = v2 -> Vcast v1 e = Vcast v2 e.

  Proof. induction v1; intros. subst v2. refl. rewrite H. refl. Qed.

  Lemma Vcast_eq : forall n (v1 v2 : vec n) p (e : n=p),
    Vcast v1 e = Vcast v2 e <-> v1 = v2.

  Proof. split; intro. apply (Vcast_eq_elim H). apply Vcast_eq_intro. hyp. Qed.

  Lemma Vcast_pi : forall n (v : vec n) p (h1 : n=p) (h2 : n=p),
    Vcast v h1 = Vcast v h2.

  Proof.
    induction v; intros until p; case p; intros; simpl; (discr || auto).
    apply Vtail_eq. apply IHv.
  Qed.

  Lemma Vcast_lr : forall n1 (v1 : vec n1) n2 (v2 : vec n2) (h12 : n1=n2)
    (h21 : n2=n1), Vcast v1 h12 = v2 -> v1 = Vcast v2 h21.

  Proof.
    induction v1; induction v2; simpl; intros. refl. discr. discr.
    Veqtac. subst h0. apply Vtail_eq. eapply IHv1. apply H2.
  Qed.

  Lemma Vcast_rl : forall n1 (v1 : vec n1) n2 (v2 : vec n2) (h12 : n1=n2)
    (h21 : n2=n1), v1 = Vcast v2 h21 -> Vcast v1 h12 = v2.

  Proof.
    induction v1; induction v2; simpl; intros. refl. discr. discr.
    Veqtac. subst h0. apply Vtail_eq. eapply IHv1. apply H2.
  Qed.

  Lemma Vcast_introrl : forall n1 (v1 : vec n1) n2 (v2 : vec n2) (h21 : n2=n1),
    Vcast v1 (sym_eq h21) = v2 -> v1 = Vcast v2 h21.

  Proof. intros. eapply Vcast_lr. apply H. Qed.

  Lemma Vcast_elimlr : forall n1 (v1 : vec n1) n2 (v2 : vec n2) (h12 : n1=n2),
    Vcast v1 h12 = v2 -> v1 = Vcast v2 (sym_eq h12).

  Proof. intros. eapply Vcast_lr. apply H. Qed.

End Vcast.

(***********************************************************************)
(** null vector *)

Section Vnull.

  Variable A : Type. Notation vec := (vector A).

  Lemma VO_eq : forall v : vec O, v = Vnil.

  Proof.
    cut (forall n (v : vec n) (h: n=0), Vcast v h = Vnil).
    intros. ded (H 0 v (refl_equal 0)). rewrite Vcast_refl in H0. hyp.
    destruct v. auto. intro. discr.
  Defined.

End Vnull.

Ltac VOtac := repeat
  match goal with
    | v : vector _ O |- _ => assert (v = Vnil); [apply VO_eq | subst v]
  end.

(***********************************************************************)
(** i-th element *)

Section Vnth.

  Variable A : Type. Notation vec := (vector A).

  Program Fixpoint Vnth n (v : vec n) : forall i, i < n -> A :=
    match v with
      | Vnil => fun i ip => !
      | Vcons x p v' => fun i =>
        match i with
          | 0 => fun _ => x
          | S j => fun H => Vnth v' (i:=j) _
        end
    end.
  Solve Obligations using program_simplify; auto with *.

  Lemma Vhead_nth : forall n (v : vec (S n)), Vhead v = Vnth v (lt_O_Sn n).

  Proof. intros. VSntac v. refl. Qed.

  Lemma Vnth_eq : forall n (v : vec n) i1 (h1 : i1<n) i2 (h2 : i2<n),
    i1 = i2 -> Vnth v h1 = Vnth v h2.

  Proof.
    induction v; intro; case i1.
    intro. absurd (0 <= 0); omega.
    intros n h1. absurd (0 <= S n); omega.
    intros. subst i2. refl.
    intros. subst i2. simpl. apply IHv. refl.
  Qed.

  Lemma Vnth_tail : forall n (v : vec (S n)) i (h : i < n),
    Vnth (Vtail v) h = Vnth v (lt_n_S h).

  Proof. intros. VSntac v. simpl. apply Vnth_eq. refl. Qed.

  Lemma Vnth_cons_head : forall x n (v : vec n) k (h : k < S n),
    k = 0 -> Vnth (Vcons x v) h = x.

  Proof. intros. subst k. refl. Qed.

  Lemma Vnth_cons_tail_aux : forall n i, i < S n -> i > 0 -> i-1 < n.

  Proof. Omega. Qed.

  Lemma Vnth_cons_tail : forall x n (v : vec n) i (h1:i<S n) (h2:i>0),
    Vnth (Vcons x v) h1 = Vnth v (Vnth_cons_tail_aux h1 h2).

  Proof. intros. simpl. destruct i. absurd_arith. apply Vnth_eq. omega. Qed.

  Lemma Vnth_cons : forall x n (v : vec n) i (h1:i<S n),
    Vnth (Vcons x v) h1 = match lt_ge_dec 0 i with
                            | left h2 => Vnth v (Vnth_cons_tail_aux h1 h2)
                            | _ => x
                          end.

  Proof.
    intros. case (lt_ge_dec 0 i); intro. apply Vnth_cons_tail.
    apply Vnth_cons_head. omega.
  Qed.

  Lemma Vnth_const : forall n (a : A) i (ip : i < n), Vnth (Vconst a n) ip = a.

  Proof.
    induction n; intros. absurd_arith.
    destruct i. trivial.
    simpl. rewrite IHn. refl.
  Qed.

  Lemma Vnth_cast_aux : forall n n' k, n = n' -> k < n' -> k < n.

  Proof. Omega. Qed.

  Lemma Vnth_cast : forall n (v : vec n) n' (e : n = n') k (h : k < n'),
    Vnth (Vcast v e) h = Vnth v (Vnth_cast_aux e h).

  Proof.
    induction v; simpl. destruct n'. intros. absurd_arith. discr.
    destruct n'. discr. intro e. inversion e. subst n'.
    destruct k. simpl. refl. intro h0. simpl. rewrite IHv. apply Vnth_eq.
    refl.
  Qed.

  Lemma Veq_nth : forall n (v v' : vec n), 
    (forall i (ip : i < n), Vnth v ip = Vnth v' ip) -> v = v'.

  Proof.
    induction n; intros.
    VOtac. refl.
    VSntac v. VSntac v'. apply Vcons_eq_intro.
    do 2 rewrite Vhead_nth. apply H.
    apply IHn. intros. do 2 rewrite Vnth_tail. apply H.
  Qed.

End Vnth.

Notation "v '[@' p ']'" := (Vnth v p) (at level 0) : vec_scope.

(***********************************************************************)
(** add an element at the end *)

Section Vadd.

  Variable A : Type. Notation vec := (vector A).

  Fixpoint Vadd n (v : vec n) (x : A) : vec (S n) :=
    match v with
      | Vnil => Vcons x Vnil
      | Vcons a _ v' => Vcons a (Vadd v' x)
    end.

  Lemma Vnth_addl : forall k n (v : vec n) a (H1 : k < S n) (H2 : k < n),
    Vnth (Vadd v a) H1 = Vnth v H2.

  Proof.
    intros. assert (H3 : H1 = (@le_S (S k) n H2)). apply lt_unique.
    subst H1. generalize dependent k. generalize dependent n. intro n. elim n.
    intros v k H. elimtype False. apply (lt_n_O _ H).
    intros n' Hrec v k H. rewrite (VSn_eq v). destruct k.
    simpl. refl.
    simpl Vadd.
    assert (H' : k < S n'). auto with arith. simpl. 
    assert (lt_S_n (le_S H) = le_S (lt_S_n H)). apply lt_unique. rewrite H0.
    rewrite Hrec. refl.
  Qed.

  Lemma Vnth_addr : forall k n (v : vec n) a (H1 : k < S n) (H2 : k = n),
    Vnth (Vadd v a) H1 = a.

  Proof.
    intros. subst k. assert (H2 : H1 = lt_n_Sn n). apply lt_unique. subst H1.
    generalize dependent v. intro v. elim v.
    simpl. refl.
    intros a' p' v' Hrec. simpl. rewrite <- Hrec at -1. apply Vnth_eq. refl.
  Qed.

  Lemma Vnth_add_aux : forall i n, i < S n -> i <> n -> i < n.

  Proof. Omega. Qed.

  Lemma Vnth_add : forall n (v : vec n) x i (h : i < S n),
    Vnth (Vadd v x) h =
    match eq_nat_dec i n with
      | left _ => x
      | right n => Vnth v (Vnth_add_aux h n)
    end.

  Proof.
    induction v; intros x i hi; simpl Vadd.
    (* nil *)
    destruct (eq_nat_dec i 0). apply Vnth_cons_head. hyp. omega.
    (* cons *)
    destruct (eq_nat_dec i (S n)).
    (* i = S n *)
    subst. rewrite Vnth_cons. destruct (lt_ge_dec 0 (S n)). 2: omega.
    rewrite IHv. destruct (eq_nat_dec (S n - 1) n). refl. omega.
    (* i <> S n *)
    rename h into y. rewrite Vnth_cons. destruct (lt_ge_dec 0 i).
    rewrite IHv. destruct (eq_nat_dec (i-1) n). omega.
    rewrite Vnth_cons. destruct (lt_ge_dec 0 i). 2: omega. apply Vnth_eq. refl.
    sym. apply Vnth_cons_head. omega.
  Qed.

  Lemma Vadd_cons : forall x n (v : vec (S n)),
    Vadd v x = Vcons (Vhead v) (Vadd (Vtail v) x).

  Proof. intro x. destruct n; intro v; rewrite (VSn_eq v) at 1; refl. Qed.

End Vadd.

(***********************************************************************)
(** replacement of i-th element *)

Section Vreplace.

  Variable A : Type. Notation vec := (vector A).

  Program Fixpoint Vreplace n (v : vec n) i (ip : i < n) (a : A) : vec n :=
    match v with 
      | Vnil => !
      | Vcons h _ v' => 
        match i with
          | 0 => Vcons a v'
          | S i' => Vcons h (Vreplace v' (i:=i') _ a)
        end
    end.
  Solve Obligations using program_simplify ; auto with *.

  Lemma Vreplace_tail : forall n i (ip : S i < S n) (v : vec (S n)) (a : A),
    Vreplace v ip a = Vcons (Vhead v) (Vreplace (Vtail v) (lt_S_n ip) a).

  Proof.
    destruct n; intros. absurd_arith. VSntac v. refl.
  Qed.

  Lemma Vnth_replace : forall n i (ip ip' : i < n) (v : vec n) (a : A),
    Vnth (Vreplace v ip a) ip' = a.

  Proof.
    induction n; intros.
    elimtype False. omega.
    VSntac v. destruct i. trivial.
    simpl. apply IHn.
  Qed.

  Lemma Vnth_replace_neq : forall n i (ip : i < n) j (jp : j < n) 
    (v : vec n) (a : A), i <> j -> Vnth (Vreplace v ip a) jp = Vnth v jp.

  Proof.
    induction n; intros.
    elimtype False. omega.
    VSntac v. destruct i; destruct j; trivial.
    elimtype False. omega.
    simpl. rewrite IHn. trivial. omega.
  Qed.

  Lemma Vreplace_pi : forall n (v : vec n) i1 i2 (h1 : i1 < n) (h2 : i2 < n) x,
    i1 = i2 -> Vreplace v h1 x = Vreplace v h2 x.

  Proof.
    intros. subst i2. revert i1 h1 h2. elim v; clear v; simpl; intros.
    absurd_arith. destruct i1. refl. apply Vtail_eq. apply H.
  Qed.

  Lemma Vreplace_eq_elim : forall n (v : vec n) i (h : i < n) x x',
    Vreplace v h x = Vreplace v h x' -> x = x'.

  Proof.
    intros. ded (f_equal (fun v => @Vnth A n v i h) H).
    repeat rewrite Vnth_replace in H0. hyp.
  Qed.

  Lemma Vreplace_nth_eq : forall n (v : vec n) i (h : i < n),
    Vreplace v h (Vnth v h) = v.

  Proof.
    intros. apply Veq_nth. intro j. case (eq_nat_dec i j); intro Eij.
    rewrite <- Eij. intro hj. rewrite (Vnth_eq v h hj); auto.
    apply Vnth_replace.
    intro hj. apply Vnth_replace_neq; auto.
  Qed.

End Vreplace.

(***********************************************************************)
(** concatenation *)

Section Vapp.

  Variable A : Type. Notation vec := (vector A).

  Fixpoint Vapp n1 n2 (v1 : vec n1) (v2 : vec n2) : vec (n1+n2) :=
    match v1 with
      | Vnil => v2
      | Vcons a _ v' => Vcons a (Vapp v' v2)
    end.

  Lemma Vapp_cons : forall a n1 n2 (v1 : vec n1) (v2 : vec n2),
    Vapp (Vcons a v1) v2 = Vcons a (Vapp v1 v2).

  Proof. refl. Qed.

  Lemma Vapp_nil_eq : forall n (v : vec n) (w : vec 0) (h : n=n+0),
    Vapp v w = Vcast v h.

  Proof.
    induction v; intros. VOtac. refl.
    simpl. apply Vtail_eq. apply IHv.
  Qed.

  Lemma Vapp_nil : forall n (v : vec n) (w : vec 0), 
    Vapp v w = Vcast v (plus_n_O n).

  Proof. intros. apply Vapp_nil_eq. Qed.

  Lemma Vapp_rcast_eq : forall n1 (v1 : vec n1) n2 (v2 : vec n2) p2
    (h1 : n2=p2) (h2 : n1+n2=n1+p2),
    Vapp v1 (Vcast v2 h1) = Vcast (Vapp v1 v2) h2.

  Proof.
    induction v1; simpl; intros.
    assert (h1=h2). apply eq_unique. rewrite H. refl.
    apply Vtail_eq. apply IHv1.
  Qed.

  Lemma Vapp_rcast : forall n1 (v1 : vec n1) n2 (v2 : vec n2) p2 (h1 : n2=p2),
    Vapp v1 (Vcast v2 h1) = Vcast (Vapp v1 v2) (plus_reg_l_inv n1 h1).

  Proof. intros. apply Vapp_rcast_eq. Qed.

  Lemma Vapp_lcast_eq : forall n1 (v1 : vec n1) n2 (v2 : vec n2) p1
    (h1 : n1=p1) (h2 : n1+n2=p1+n2),
    Vapp (Vcast v1 h1) v2 = Vcast (Vapp v1 v2) h2.

  Proof.
    induction v1; intros until p1; case p1; simpl; intros.
    rewrite Vcast_refl. refl. discr. discr.
    apply Vtail_eq. apply IHv1.
  Qed.

  Lemma Vapp_lcast :  forall n1 (v1 : vec n1) n2 (v2 : vec n2) p1 (h1 : n1=p1),
    Vapp (Vcast v1 h1) v2 = Vcast (Vapp v1 v2) (plus_reg_r_inv n2 h1).

  Proof.
    intros. apply Vapp_lcast_eq.
  Qed.

  Lemma Vapp_assoc_eq : forall n1 (v1 : vec n1) n2 (v2 : vec n2)
    n3 (v3 : vec n3) (h : n1+(n2+n3) = (n1+n2)+n3),
    Vapp (Vapp v1 v2) v3 = Vcast (Vapp v1 (Vapp v2 v3)) h.

  Proof.
    induction v1; intros; simpl.
    rewrite Vcast_refl. refl.
    apply Vtail_eq. apply IHv1.
  Qed.

  Lemma Vapp_assoc : forall n1 (v1 : vec n1) n2 (v2 : vec n2) n3 (v3 : vec n3),
    Vapp (Vapp v1 v2) v3 = Vcast (Vapp v1 (Vapp v2 v3)) (plus_assoc n1 n2 n3).

  Proof. intros. apply Vapp_assoc_eq. Qed.

  Lemma Vapp_eq_intro : forall n1 (v1 v1' : vec n1) n2 (v2 v2' : vec n2),
    v1 = v1' -> v2 = v2' -> Vapp v1 v2 = Vapp v1' v2'.

  Proof. intros. rewrite H. rewrite H0. refl. Qed.

  Lemma Vapp_eq : forall n1 (v1 v1' : vec n1) n2 (v2 v2' : vec n2),
    Vapp v1 v2 = Vapp v1' v2' <-> v1 = v1' /\ v2 = v2'.

  Proof.
    induction v1; simpl. intro. VOtac. simpl. intros. tauto.
    intro. VSntac v1'. simpl. split; intro. Veqtac. subst h.
    rewrite IHv1 in H3.
    intuition. rewrite H0. refl. destruct H0. Veqtac. subst h.
    apply Vcons_eq_intro. refl. rewrite IHv1. intuition.
  Qed.

  Lemma Vnth_app_aux : forall n1 n2 i, i < n1+n2 -> n1 <= i -> i - n1 < n2.

  Proof. Omega. Qed.

  Implicit Arguments Vnth_app_aux [n1 n2 i].

  Lemma Vnth_app : forall n1 (v1 : vec n1) n2 (v2 : vec n2) i (h : i < n1+n2),
    Vnth (Vapp v1 v2) h =
    match le_gt_dec n1 i with
      | left p => Vnth v2 (Vnth_app_aux h p)
      | right p => Vnth v1 p
    end.

  Proof.
    induction v1; intros. simpl. apply Vnth_eq. omega.
    destruct i. refl. simpl le_gt_dec. ded (IHv1 _ v2 i (lt_S_n h0)). revert H.
    case (le_gt_dec n i); simpl; intros.
    (* case 1 *)
    trans (Vnth v2 (Vnth_app_aux (lt_S_n h0) l)). hyp.
    apply Vnth_eq. omega.
    (* case 2 *)
    trans (Vnth v1 g). hyp. apply Vnth_eq. refl.
  Qed.

  Lemma Vnth_app_cons : forall n1 (v1 : vec n1) n2 (v2 : vec n2)
    (h : n1 < n1 + S n2) x, Vnth (Vapp v1 (Vcons x v2)) h = x.

  Proof. induction v1; intros; simpl. refl. apply IHv1. Qed.

  Lemma Vnth_app_cons_neq : forall n1 (v1 : vec n1) n2 (v2 : vec n2) k
    (h : k < n1 + S n2) x x',
    k <> n1 -> Vnth (Vapp v1 (Vcons x v2)) h = Vnth (Vapp v1 (Vcons x' v2)) h.

  Proof.
    induction v1; intros.
    simpl. destruct k. irrefl. refl.
    repeat rewrite Vapp_cons. destruct k. refl. apply IHv1. omega.
  Qed.

  Lemma Vapp_cast_aux : forall n1 n2 n2', n2 = n2' -> n1+n2 = n1+n2'.

  Proof. Omega. Qed.

  Lemma Vapp_cast : forall n1 (v1 : vec n1) n2 (v2 : vec n2) n2' (e : n2 = n2'),
    Vapp v1 (Vcast v2 e) = Vcast (Vapp v1 v2) (Vapp_cast_aux n1 e).

  Proof.
    induction v1; simpl; intros. apply Vcast_pi. apply Vtail_eq.
    rewrite IHv1. apply Vcast_pi.
  Qed.

  Lemma Vadd_app_aux : forall p q, p + S q = S (p+q).

  Proof. intros p q. omega. Qed.

  Lemma Vadd_app : forall p (v : vec p) q (w : vec q) x,
    Vadd (Vapp v w) x = Vcast (Vapp v (Vadd w x)) (Vadd_app_aux p q).

  Proof.
    induction v; simpl; intros q w x.
    rewrite Vcast_refl. refl.
    apply Vtail_eq. rewrite IHv. apply Vcast_pi.
  Qed.

End Vapp.

(***********************************************************************)
(** breaking a vector in various pieces *)

Section Vbreak.

  Variable A : Type. Notation vec := (vector A).

  Definition Vsplit n (v : vec (S n)) := (Vhead v, Vtail v).

  Fixpoint Vbreak n1 n2 : vec (n1+n2) -> vec n1 * vec n2 :=
    match n1 with
      | O => fun v => (Vnil, v)
      | S p1 => fun v =>
        let w := Vbreak p1 n2 (Vtail v) in 
          (Vcons (Vhead v) (fst w), snd w)
    end.

  Implicit Arguments Vbreak [n1 n2].

  Lemma Vbreak_app : forall n1 (v1 : vec n1) n2 (v2 : vec n2),
    Vbreak (Vapp v1 v2) = (v1, v2).

  Proof.
    induction n1; simpl; intros. VOtac. refl. VSntac v1. simpl.
    gen (IHn1 (Vtail v1) n2 v2). intro. rewrite H0. refl.
  Qed.

  Lemma Vbreak_eq_app : forall n1 n2 (v : vec (n1+n2)),
    v = Vapp (fst (Vbreak v)) (snd (Vbreak v)).

  Proof.
    intros n1 n2. elim n1.
    auto.
    clear n1. intros n1 Hrec. simpl.
    intro v.
    gen (Hrec (Vtail v)).
    intro H. trans (Vcons (Vhead v) (Vtail v)).
    apply VSn_eq. rewrite H. auto.
  Qed.

  Lemma Vbreak_eq_app_cast : forall n n1 n2 (H : n1+n2=n) (v : vec n),
    v = Vcast (Vapp (fst (Vbreak (Vcast v (sym_equal H))))
      (snd (Vbreak (Vcast v (sym_equal H))))) H.

  Proof.
    intros until H. case H. simpl. intro v.
    rewrite <- Vbreak_eq_app. do 2 rewrite Vcast_refl. refl.
  Qed.

End Vbreak.

(***********************************************************************)
(** membership *)

Section Vin.

  Variable A : Type. Notation vec := (vector A).

  Fixpoint Vin (x : A) n (v : vec n) : Prop :=
    match v with
      | Vnil => False
      | Vcons y _ w => y = x \/ Vin x w
    end.

  Lemma Vin_head : forall n (v : vec (S n)), Vin (Vhead v) v.

  Proof. intros. VSntac v. simpl. auto. Qed.

  Lemma Vin_tail : forall n x (v : vec (S n)), Vin x (Vtail v) -> Vin x v.

  Proof. intros. VSntac v. simpl. auto. Qed.

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
    rewrite lt_Sn_nS. hyp.
  Qed.

  Lemma Vin_cast_intro : forall m n (H : m=n) (v : vec m) x,
    Vin x v -> Vin x (Vcast v H).

  Proof.
    intros m n H. case H. intros. rewrite Vcast_refl. hyp.
  Qed.

  Lemma Vin_cast_elim : forall m n (H : m=n) (v : vec m) x,
    Vin x (Vcast v H) -> Vin x v.

  Proof. intros m n H. case H. intros v x. rewrite Vcast_refl. auto. Qed.

  Implicit Arguments Vin_cast_elim [m n H v x].

  Lemma Vin_cast : forall m n (H : m=n) (v : vec m) x,
    Vin x (Vcast v H) <-> Vin x v.

  Proof. intros m n H. case H. intros. rewrite Vcast_refl. tauto. Qed.

  Lemma Vin_appl : forall x n1 (v1 : vec n1) n2 (v2 : vec n2),
    Vin x v1 -> Vin x (Vapp v1 v2).

  Proof.
    induction v1; simpl; intros. contr. destruct H. auto.
    right. apply IHv1. hyp.
  Qed.

  Lemma Vin_appr : forall x n1 (v1 : vec n1) n2 (v2 : vec n2),
    Vin x v2 -> Vin x (Vapp v1 v2).

  Proof. induction v1; simpl; intros. hyp. right. apply IHv1. hyp. Qed.

  Lemma Vin_app_cons : forall x n1 (v1 : vec n1) n2 (v2 : vec n2),
    Vin x (Vapp v1 (Vcons x v2)).

  Proof. induction v1; intros; simpl; auto. Qed.

  Lemma Vin_app : forall x n1 (v1 : vec n1) n2 (v2 : vec n2),
    Vin x (Vapp v1 v2) -> Vin x v1 \/ Vin x v2.

  Proof.
    induction v1; intros; simpl in * . auto. destruct H. auto.
    assert (Vin x v1 \/ Vin x v2). apply IHv1. exact H. destruct H0; auto.
  Qed.

  Lemma Vin_elim : forall x n (v : vec n),
    Vin x v -> exists n1, exists v1 : vec n1, exists n2, exists v2 : vec n2,
      exists H : n1 + S n2 = n, v = Vcast (Vapp v1 (Vcons x v2)) H.

  Proof.
    induction v; simpl. contr.
    intro H. destruct H. clear IHv. subst x.
    exists 0 (@Vnil A) n. exists v (refl_equal (S n)).
    rewrite Vcast_refl. refl.
    assert (exists n1 (v1 : vec n1) n2 (v2 : vec n2) (H : n1 + S n2 = n),
      v = Vcast (Vapp v1 (Vcons x v2)) H). exact (IHv H).
    destruct H0 as [n1]. destruct H0 as [v1]. destruct H0 as [n2].
    destruct H0 as [v2].
    destruct H0 as [H1].
    exists (S n1). exists (Vcons h v1). exists n2. exists v2.
    exists (S_add_S H1).
    rewrite H0. clear H0. simpl.
    apply Vtail_eq. apply Vcast_pi. 
  Qed.

End Vin.

Implicit Arguments Vin_nth [A n v a].

(***********************************************************************)
(** sub-vector: Vsub v (h:i+k<=n) = [v_i, .., v_{i+k-1}] *)

Section Vsub.

  Variable A : Type. Notation vec := (vector A).

  Lemma Vsub_aux1 : forall i k' n : nat, i + S k' <= n -> i < n.

  Proof. Omega. Qed.

  Implicit Arguments Vsub_aux1 [i k' n].

  Lemma Vsub_aux2: forall i k' n : nat, i + S k' <= n -> S i + k' <= n.

  Proof. Omega. Qed.

  Implicit Arguments Vsub_aux2 [i k' n].

  Fixpoint Vsub n (v : vec n) i k : i+k<=n -> vec k :=
    match k as k return i+k<=n -> vec k with
      | 0 => fun _ => Vnil
      | S k' => fun h =>
        Vcons (Vnth v (Vsub_aux1 h)) (Vsub v (S i) k' (Vsub_aux2 h))
    end.

  Global Implicit Arguments Vsub [n i k].

  Lemma Vsub_nil_aux : forall i k (h:i+k<=0) (e : 0=k),
    Vsub Vnil h = Vcast Vnil e.

  Proof. destruct k; intros. refl. discr. Qed.

  Lemma Vsub_nil_aux1 : forall i k, i+k <= 0 -> 0=k.

  Proof. Omega. Qed.

  Implicit Arguments Vsub_nil_aux1 [i k].

  Lemma Vsub_nil : forall i k (h:i+k<=0),
    Vsub Vnil h = Vcast Vnil (Vsub_nil_aux1 h).

  Proof. intros. apply Vsub_nil_aux. Qed.

  Lemma Vnth_sub_aux : forall n i k j, i+k<=n -> j<k -> i+j<n.

  Proof. Omega. Qed.

  Implicit Arguments Vnth_sub_aux [n i k j].

  Lemma Vnth_sub : forall k n (v : vec n) i (h : i+k<=n) j (p : j<k),
    Vnth (Vsub v h) p = Vnth v (Vnth_sub_aux h p).

  Proof.
    induction k; intros. absurd_arith. simpl. destruct j. apply Vnth_eq. omega.
    rewrite IHk. apply Vnth_eq. omega.
  Qed.

  Lemma Vsub_cons_aux : forall n i k, S i + k <= S n -> i + k <= n.

  Proof. Omega. Qed.

  Lemma Vsub_cons : forall x i k n (v : vec n) (h : S i + k <= S n),
    Vsub (Vcons x v) h = Vsub v (Vsub_cons_aux h).

  Proof.
    intros. apply Veq_nth; intros. repeat rewrite Vnth_sub. simpl.
    apply Vnth_eq. omega.
  Qed.

  Lemma Vsub_pi : forall n (v : vec n) i k (h h' : i+k<=n),
    Vsub v h = Vsub v h'.

  Proof.
    intros. assert (h = h'). apply le_unique. subst. refl.
  Qed.

  Lemma Vsub_cast_aux : forall n (v : vec n) n' (e : n=n') i k (h : i+k<=n')
    (h' : i+k<=n), Vsub (Vcast v e) h = Vsub v h'.

  Proof.
    destruct v; destruct n'; simpl; intros. apply Vsub_pi. discr. discr.
    inversion e. subst n'. assert (Vcast v
    (Vcast_obligation_4 e refl_equal (JMeq_refl (Vcons h v)) refl_equal) = v).
    apply Vcast_refl. rewrite H. apply Vsub_pi.
  Qed.

  Lemma Vsub_cast_aux1 : forall n n' i k, n=n' -> i+k<=n' -> i+k<=n.

  Proof. Omega. Qed.

  Implicit Arguments Vsub_cast_aux1 [n n' i k].

  Lemma Vsub_cast : forall n (v : vec n) n' (e : n=n') i k (h : i+k<=n')
    (h' : i+k<=n), Vsub (Vcast v e) h = Vsub v (Vsub_cast_aux1 e h).

  Proof. intros. apply Vsub_cast_aux. Qed.

  Lemma Vcast_sub_aux1 : forall n i k j, i + k <= n -> k = j -> i + j <= n.

  Proof. Omega. Qed.

  Implicit Arguments Vcast_sub_aux1 [n i k j].

  Lemma Vcast_sub : forall n (v : vec n) i k (h : i + k <= n) j (e : k = j),
    Vcast (Vsub v h) e = Vsub v (Vcast_sub_aux1 h e).

  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_cast, !Vnth_sub.
    apply Vnth_eq. auto.
  Qed.

  Lemma Vcons_nth_aux1 : forall n i k, i < n -> S i+k <= n -> i+S k <= n.

  Proof. Omega. Qed.

  Lemma Vcons_nth : forall n (v : vec n) i k (h1 : i<n) (h2 : S i + k <= n),
    Vcons (Vnth v h1) (Vsub v h2) = Vsub v (Vcons_nth_aux1 h1 h2).

  Proof.
    intros. apply Veq_nth; intros.
    destruct i0; simpl; repeat rewrite Vnth_sub; apply Vnth_eq; omega.
  Qed.

  Lemma Vsub_cons_intro_aux : forall n (v : vec n) i k (h : i+k<=n)
    (h1 : i<n) (h2 : S i + pred k <= n) (e : S (pred k) = k),
    Vsub v h = Vcast (Vcons (Vnth v h1) (Vsub v h2)) e.

  Proof.
    intros. apply Veq_nth; intros. rewrite Vnth_cast.
    destruct i0; simpl; repeat rewrite Vnth_sub; apply Vnth_eq; omega.
  Qed.

  Lemma Vsub_cons_intro_aux1 : forall n i k, i+k<=n -> k>0 -> i<n.

  Proof. Omega. Qed.

  Implicit Arguments Vsub_cons_intro_aux1 [n i k].

  Lemma Vsub_cons_intro_aux2 : forall n i k, i+k<=n -> k>0 -> S i+pred k <= n.

  Proof. Omega. Qed.

  Implicit Arguments Vsub_cons_intro_aux2 [n i k].

  Lemma Vsub_cons_intro_aux3 : forall k, k>0 -> S(pred k) = k.

  Proof. Omega. Qed.

  Lemma Vsub_cons_intro :  forall n (v : vec n) i k (h : i+k<=n) (p : k>0),
    Vsub v h = Vcast (Vcons (Vnth v (Vsub_cons_intro_aux1 h p))
      (Vsub v (Vsub_cons_intro_aux2 h p))) (Vsub_cons_intro_aux3 p).

  Proof. intros. apply Vsub_cons_intro_aux. Qed.

  Lemma Veq_app_aux : forall n (v : vec n) i
    (h1 : 0 + i <= n) (h2 : i + (n - i) <= n) (e : i + (n - i) = n),
    v = Vcast (Vapp (Vsub v h1) (Vsub v h2)) e.

  Proof.
    induction v; intros.
    (* Vnil *)
    apply Veq_nth; intros. absurd_arith.
    (* Vcons *)
    destruct i; simpl; apply Vtail_eq; repeat rewrite Vsub_cons.
    (* i = 0 *)
    apply Veq_nth; intros. rewrite Vnth_cast. rewrite Vnth_sub.
    apply Vnth_eq. omega.
    (* i > 0 *)
    apply IHv.
  Qed.

  Lemma Veq_app_aux1 : forall n i, i <= n -> 0 + i <= n.

  Proof. Omega. Qed.

  Lemma Veq_app_aux2 : forall n i, i <= n -> i + (n - i) <= n.

  Proof. Omega. Qed.

  Lemma Veq_app_aux3 : forall n i, i <= n -> i + (n - i) = n.

  Proof. Omega. Qed.

  Lemma Veq_app : forall n (v : vec n) i (h : i<=n),
    v = Vcast (Vapp (Vsub v (Veq_app_aux1 h)) (Vsub v (Veq_app_aux2 h)))
    (Veq_app_aux3 h).

  Proof. intros. apply Veq_app_aux. Qed.

  Lemma Veq_app_cons_aux : forall n (v : vec n) i (h1 : 0 + i <= n) (h2 : i < n)
    (h3 : S i + (n - S i) <= n) (e : i + S (n - S i) = n),
    v = Vcast (Vapp (Vsub v h1) (Vcons (Vnth v h2) (Vsub v h3))) e.

  Proof.
    induction v; intros.
    (* Vnil *)
    apply Veq_nth; intros. absurd_arith.
    (* Vcons *)
    destruct i; simpl; apply Vtail_eq; repeat rewrite Vsub_cons.
    (* i = 0 *)
    apply Veq_nth; intros. rewrite Vnth_cast. rewrite Vnth_sub.
    apply Vnth_eq. omega.
    (* i > 0 *)
    apply IHv.
  Qed.

  Lemma Veq_app_cons_aux1 : forall n i, i < n -> 0 + i <= n.

  Proof. Omega. Qed.

  Lemma Veq_app_cons_aux2 : forall n i, i < n -> S i + (n - S i) <= n.

  Proof. Omega. Qed.

  Lemma Veq_app_cons_aux3 : forall n i, i < n -> i + S (n - S i) = n.

  Proof. Omega. Qed.

  Lemma Veq_app_cons : forall n (v : vec n) i (h : i<n),
    v = Vcast (Vapp (Vsub v (Veq_app_cons_aux1 h))
      (Vcons (Vnth v h) (Vsub v (Veq_app_cons_aux2 h))))
    (Veq_app_cons_aux3 h).

  Proof. intros. apply Veq_app_cons_aux. Qed.

  Lemma Veq_sub_aux : forall n (v v' : vec n) i (h1 : 0+i<=n) (h2 : i+(n-i)<=n),
    Vsub v h1 = Vsub v' h1 -> Vsub v h2 = Vsub v' h2 -> v = v'.

  Proof.
    intros. assert (e:i+(n-i)=n). omega.
    rewrite (Veq_app_aux v h1 h2 e). rewrite (Veq_app_aux v' h1 h2 e).
    apply Vcast_eq_intro. apply Vapp_eq_intro; hyp.
  Qed.

  Lemma Veq_sub : forall n (v v' : vec n) i (h : i<=n),
    Vsub v (Veq_app_aux1 h) = Vsub v' (Veq_app_aux1 h) ->
    Vsub v (Veq_app_aux2 h) = Vsub v' (Veq_app_aux2 h) -> v = v'.

  Proof. intros. eapply Veq_sub_aux; ehyp. Qed.

  Lemma Veq_sub_cons_aux : forall n (v v' : vec n) i (h1 : 0+i<=n)
    (h2 : i<n) (h3 : S i+(n-S i)<=n), Vsub v h1 = Vsub v' h1 ->
    Vnth v h2 = Vnth v' h2 -> Vsub v h3 = Vsub v' h3 -> v = v'.

  Proof.
    intros. assert (e:i+S(n-S i)=n). omega.
    rewrite (Veq_app_cons_aux v h1 h2 h3 e).
    rewrite (Veq_app_cons_aux v' h1 h2 h3 e).
    apply Vcast_eq_intro. apply Vapp_eq_intro. hyp. apply Vcons_eq_intro; hyp.
  Qed.

  Lemma Veq_sub_cons : forall n (v v' : vec n) i (h : i<n),
    Vsub v (Veq_app_cons_aux1 h) = Vsub v' (Veq_app_cons_aux1 h) ->
    Vnth v h = Vnth v' h ->
    Vsub v (Veq_app_cons_aux2 h) = Vsub v' (Veq_app_cons_aux2 h) -> v = v'.

  Proof. intros. eapply Veq_sub_cons_aux; ehyp. Qed.

  Lemma Vsub_replace_l : forall n (v : vec n) i (h : i<n) x j k (p : j+k<=n),
    j+k <= i -> Vsub (Vreplace v h x) p = Vsub v p.

  Proof.
    intros. apply Veq_nth; intros. repeat rewrite Vnth_sub.
    rewrite Vnth_replace_neq. 2: omega. apply Vnth_eq. refl.
  Qed.

  Lemma Vsub_replace_r : forall n (v : vec n) i (h : i<n) x j k (p : j+k<=n),
    j > i -> Vsub (Vreplace v h x) p = Vsub v p.

  Proof.
    intros. apply Veq_nth; intros. repeat rewrite Vnth_sub.
    rewrite Vnth_replace_neq. 2: omega. apply Vnth_eq. refl.
  Qed.

  Lemma Vsub_app_l_aux : forall n1 n2 i, i <= n1 -> 0 + i <= n1 + n2.

  Proof. Omega. Qed.

  Lemma Vsub_app_l : forall n1 (v1 : vec n1) n2 (v2 : vec n2) (h : 0+n1<=n1+n2),
    Vsub (Vapp v1 v2) h = v1.

  Proof.
    induction v1; simpl; intros. refl. apply Vtail_eq. rewrite Vsub_cons.
    rewrite IHv1. refl.
  Qed.

  Lemma Vsub_id : forall n (v : vec n) (h:0+n<=n), Vsub v h = v.

  Proof.
    induction v; simpl; intros. refl. apply Vtail_eq. rewrite Vsub_cons.
    rewrite IHv. refl.
  Qed.

  Lemma Vsub_app_r : forall n1 (v1 : vec n1) n2 (v2 : vec n2)
    (h : n1+n2<=n1+n2), Vsub (Vapp v1 v2) h = v2.

  Proof.
    induction v1; simpl; intros. apply Vsub_id. rewrite Vsub_cons. rewrite IHv1.
    refl.
  Qed.

End Vsub.

(***********************************************************************)
(** remove last element *)

Section Vremove_last.

  Variable A : Type. Notation vec := (vector A).

  Lemma Vremove_last_aux : forall n, 0 + n <= S n.

  Proof. Omega. Qed.

  Definition Vremove_last A n (v : vector A (S n)) : vector A n :=
    Vsub v (Vremove_last_aux n).

  Lemma Vnth_remove_last_aux : forall i n, i<n -> i< S n.

  Proof. Omega. Qed.

  Lemma Vnth_remove_last : forall n (v : vec (S n)) i
    (h : i<n), Vnth (Vremove_last v) h = Vnth v (Vnth_remove_last_aux h).

  Proof.
    intros n v i h. unfold Vremove_last. rewrite Vnth_sub. apply Vnth_eq. refl.
  Qed.

  Lemma Vremove_last_add : forall n (v : vec n) x,
    Vremove_last (Vadd v x) = v.

  Proof.
    intros n v x. apply Veq_nth. intros i h.
    rewrite Vnth_remove_last, Vnth_add.
    destruct (eq_nat_dec i n). omega. apply Vnth_eq. refl.
  Qed.

End Vremove_last.

(***********************************************************************)
(** Last element of a vector with default value if empty. *)

Section Vlast.

  Variable A : Type. Notation vec := (vector A).

  Fixpoint Vlast default n (v : vector A n) : A :=
    match v with
      | Vnil => default
      | Vcons x _ v' => Vlast x v'
    end.

  Lemma Vlast_eq : forall x y n (v : vec (S n)), Vlast x v = Vlast y v.

  Proof. intros x y n v. VSntac v. simpl. refl. Qed.

  Lemma Vlast_nth : forall n (v : vec (S n)) x (h : n < S n),
    Vlast x v = Vnth v h.

  Proof.
    induction n; intros v x h.
    VSntac v. simpl. generalize (Vtail v); intro w; VOtac. simpl. refl.
    VSntac v. simpl. apply IHn.
  Qed.

  Lemma Vlast_tail : forall n (v : vec (S n)),
    Vlast (Vhead v) (Vtail v) = Vlast (Vhead v) v.

  Proof. intros n v. VSntac v. refl. Qed.

  Lemma VSn_add_default : forall x n (v : vec (S n)),
    v = Vadd (Vremove_last v) (Vlast x v).

  Proof.
    intros x n v. apply Veq_nth. intros i h.
    destruct (lt_dec i n).
    rewrite Vnth_addl with (H2:=l), Vnth_remove_last. apply Vnth_eq. refl.
    rewrite Vnth_addr. 2: omega.
    assert (e : i=n). omega. subst i. rewrite Vlast_nth with (h:=h). refl.
  Qed.

  Lemma VSn_add : forall n (v : vec (S n)),
    v = Vadd (Vremove_last v) (Vlast (Vhead v) v).

  Proof. intros n v. apply VSn_add_default. Qed.

End Vlast.

(***********************************************************************)
(** proposition saying that every element satisfies some predicate *)

Section Vforall.

  Variables (A : Type) (P : A -> Prop). Notation vec := (vector A).

  Fixpoint Vforall n (v : vec n) { struct v } : Prop :=
    match v with
      | Vnil => True
      | Vcons a _ w => P a /\ Vforall w
    end.

  Lemma Vforall_intro : forall n (v : vec n),
    (forall x, Vin x v -> P x) -> Vforall v.

  Proof.
    induction v; simpl; intros. exact I. split.
    apply H. left. refl. apply IHv. intros. apply H. right. hyp.
  Qed.

  Lemma Vforall_nth_intro : forall n (v : vec n),
    (forall i (ip : i < n), P (Vnth v ip)) -> Vforall v.

  Proof.
    intros. apply Vforall_intro. intros.
    destruct (Vin_nth H0) as [i [ip v_i]].
    rewrite <- v_i. apply H.
  Qed.

  Lemma Vforall_in : forall x n (v : vec n), Vforall v -> Vin x v -> P x.

  Proof.
    induction v; simpl. contr. intros Ha Hv. destruct Ha. destruct Hv.
    rewrite <- H1. exact H. auto.
  Qed.

  Lemma Vforall_eq : forall n (v : vec n),
    Vforall v <-> (forall x, Vin x v -> P x).

  Proof.
    split; intros. eapply Vforall_in. apply H. hyp. apply Vforall_intro. hyp.
  Qed.

  Lemma Vforall_nth : forall n (v : vec n) i (ip : i < n), 
    Vforall v -> P (Vnth v ip).

  Proof. intros. apply Vforall_in with n v. hyp. apply Vnth_in. Qed.

  Lemma Vforall_incl : forall n1 (v1 : vec n1) n2 (v2 : vec n2),
    (forall x, Vin x v1 -> Vin x v2) -> Vforall v2 -> Vforall v1.

  Proof.
    intros. apply Vforall_intro. intros. apply Vforall_in with (v := v2).
    hyp. apply H. hyp.
  Qed.

  Lemma Vforall_cast : forall n v p (h : n=p),
    Vforall (Vcast v h) <-> Vforall v.

  Proof.
    intros n v p h. rewrite 2!Vforall_eq. intuition.
    apply H. rewrite Vin_cast. hyp.
    apply H. rewrite Vin_cast in H0. hyp.
  Qed.

  Fixpoint Vsig_of_v n (v : vec n) : Vforall v -> vector (sig P) n :=
    match v in vector _ n return Vforall v -> vector (sig P) n with
      | Vnil => fun _ => Vnil
      | Vcons a _ w => fun H =>
        Vcons (exist P a (proj1 H)) (Vsig_of_v w (proj2 H))
    end.

  Lemma Vforall_app : forall p (v : vec p) q (w : vec q),
    Vforall (Vapp v w) <-> Vforall v /\ Vforall w.

  Proof. induction v; fo. Qed.

  Variable P_dec : forall x, {P x}+{~P x}.

  Lemma Vforall_dec : forall n (v : vec n), {Vforall v}+{~Vforall v}.

  Proof.
    induction n; intros.
    VOtac. left. constructor.
    VSntac v. destruct (P_dec (Vhead v)).
    destruct (IHn (Vtail v)).
    left. simpl. split; hyp.
    right. intro V. destruct V. contr.
    right. intro V. destruct V. contr.
  Defined.

End Vforall.

Lemma Vforall_imp : forall A (P Q : A -> Prop) n (v : vector A n),
  Vforall P v -> (forall x, Vin x v -> P x -> Q x) -> Vforall Q v.

Proof.
  intros. apply Vforall_intro. intros. apply H0. hyp.
  eapply Vforall_in with (n := n). apply H. apply H1.
Qed.

(***********************************************************************)
(** proposition saying that the elements of two vectors are pair-wise
in relation *)

Section Vforall2_sec.

  Variables (A B : Type) (R : A -> B -> Prop).

  Notation vecA := (vector A). Notation vecB := (vector B).

  Fixpoint Vforall2n_aux n1 (v1 : vecA n1) n2 (v2 : vecB n2) : Prop :=
    match v1, v2 with
      | Vnil, Vnil => True
      | Vcons a _ v, Vcons b _ w => R a b /\ Vforall2n_aux v w
      | _, _ => False
    end.

  Definition Vforall2n n (v1 : vecA n) (v2 : vecB n) := Vforall2n_aux v1 v2.

  Lemma Vforall2n_tail : forall n (v1 : vecA (S n)) (v2 : vecB (S n)),
    Vforall2n v1 v2 -> Vforall2n (Vtail v1) (Vtail v2).

  Proof.
    intros. revert H. VSntac v1. VSntac v2. unfold Vforall2n. simpl. tauto.
  Qed.

  Lemma Vforall2n_nth : forall n (v1 : vecA n) (v2 : vecB n) i 
    (ip : i < n), Vforall2n v1 v2 -> R (Vnth v1 ip) (Vnth v2 ip).

  Proof.
    induction v1; intros. absurd (i<0); omega. revert H. VSntac v2.
    unfold Vforall2n. destruct i; simpl. tauto. intuition.
  Qed.

  Lemma Vforall2n_intro : forall n (v1 : vecA n) (v2 : vecB n),
    (forall i (ip : i < n), R (Vnth v1 ip) (Vnth v2 ip)) -> Vforall2n v1 v2.

  Proof.
    unfold Vforall2n. induction v1; intros. VOtac. simpl. auto.
    revert H. VSntac v2. intro. split. apply (H0 0 (lt_O_Sn _)).
    apply IHv1. intros. assert (S i< S n). omega. ded (H0 _ H1). simpl in H2.
    assert (ip = lt_S_n H1). apply lt_unique. rewrite H3. hyp.
  Qed.

End Vforall2_sec.

Implicit Arguments Vforall2n_nth [A B R n v1 v2].

Require Import Relations RelDec.

Section Vforall2_dec.

  Variables (A : Type) (R : relation A) (R_dec : rel_dec R).

  Notation vec := (vector A).

  Lemma Vforall2n_aux_dec : forall n1 (v1 : vec n1) n2 (v2 : vec n2), 
    {Vforall2n_aux R v1 v2} + {~Vforall2n_aux R v1 v2}.

  Proof.
    induction v1; destruct v2; simpl; auto.
    destruct (IHv1 n0 v2); intuition.
    destruct (R_dec h h0); intuition.
  Defined.

  Lemma Vforall2n_dec : forall n, rel_dec (@Vforall2n A A R n).

  Proof. intros n v1 v2. unfold Vforall2n. apply Vforall2n_aux_dec. Defined.

End Vforall2_dec.

(***********************************************************************)
(** to say that some element of a vector satisfies some predicate *)

Section Vexists.

  Variables (A : Type) (P : A->Prop).

  Notation vec := (vector A).

  Fixpoint Vexists n (v : vec n) : Prop :=
    match v with
      | Vnil => False
      | Vcons a _ v' => P a \/ Vexists v'
    end.

  Lemma Vexists_eq : forall n (v : vec n),
    Vexists v <-> exists x, Vin x v /\ P x.

  Proof.
    induction v; simpl; intuition. destruct H. intuition. exists h. intuition.
    destruct H1. exists x. intuition. destruct H1. intuition. subst. auto.
    right. apply H0. exists x. intuition.
  Qed.

  Variable f : A->bool.

  Fixpoint bVexists n (v : vec n) : bool :=
    match v with
      | Vnil => false
      | Vcons a _ v' => f a || bVexists v'
    end.

  Lemma bVexists_ok_Vin : forall n (v : vec n),
    (forall x, Vin x v -> (f x = true <-> P x)) ->
    (bVexists v = true <-> Vexists v).

  Proof.
    induction v; simpl. intuition. split; intros.
    rewrite orb_eq in H0. destruct H0. rewrite H in H0. auto. auto.
    rewrite IHv in H0. auto. intros. rewrite H. tauto. auto.
    destruct H0. rewrite <- H in H0. rewrite H0. refl. auto.
    rewrite <- IHv in H0. rewrite H0. bool. refl.
    intros. rewrite H. tauto. auto.
  Qed.

  Variable f_ok : forall x, f x = true <-> P x.

  Lemma bVexists_ok : forall n (v : vec n), bVexists v = true <-> Vexists v.

  Proof.
    intros. rewrite bVexists_ok_Vin. tauto. intros. rewrite f_ok. tauto.
  Qed.

End Vexists.

(***********************************************************************)
(** vector construction *)

Section Vbuild.

  Variable A : Type. Notation vec := (vector A).

  Program Fixpoint Vbuild_spec (n : nat) (gen : forall i, i < n -> A) :
    { v : vec n | forall i (ip : i < n), Vnth v ip = gen i ip } :=
    match n with
      | 0 => Vnil
      | S p => 
        let gen' := fun i ip => gen (S i) _ in
          Vcons (gen 0 _) (@Vbuild_spec p gen')
    end.

  Solve Obligations using omega.
  Next Obligation.
  Proof.
    elimtype False. omega.
  Qed.
  Next Obligation.
    omega.
  Qed.
  Next Obligation.
    omega.
  Qed.
  Next Obligation.
    simpl. destruct i. apply (f_equal (gen 0)). apply lt_unique.
    rewrite e. apply (f_equal (gen (S i))). apply lt_unique.
  Defined.

  Definition Vbuild n gen : vec n := proj1_sig (Vbuild_spec gen).

  Lemma Vbuild_nth : forall n gen i (ip : i < n), 
    Vnth (Vbuild gen) ip = gen i ip.

  Proof.
    intros. unfold Vbuild. destruct (Vbuild_spec gen). simpl. apply e.
  Qed.

  Lemma Vbuild_in : forall n gen x, Vin x (Vbuild gen) -> 
    exists i, exists ip : i < n, x = gen i ip.

  Proof.
    intros n gen x H. set (w := Vin_nth H). decomp w.
    exists x0 x1. rewrite Vbuild_nth in H1. auto.
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
    intros. apply Veq_nth; intros.
    rewrite Vnth_tail. do 2 rewrite Vbuild_nth. refl.
  Qed.

  Lemma Vin_build : forall n (gen : forall i, i < n -> A) x,
    (exists i, exists ip : i < n, x = gen i ip) -> Vin x (Vbuild gen).

  Proof.
    intros. unfold Vbuild. destruct (Vbuild_spec gen). simpl.
    destruct H as [i [ip H]]. rewrite H, <- (e i ip). apply Vnth_in.
  Qed.

End Vbuild.

(***********************************************************************)
(** iteration *)

Section Vfolds.

  Variable A : Type. Notation vec := (vector A).

  (* Vfold_left f b [a1 .. an] = f .. (f (f b a1) a2) .. an *)

  Fixpoint Vfold_left (B : Type) (f : B->A->B) (b:B) n (v : vec n) : B :=
    match v with
      | Vnil => b
      | Vcons a _ w => f (Vfold_left f b w) a
    end.

  (* Vfold_right f [a1 .. an] b = f a1 (f a2 .. (f an b) .. ) *)

  Fixpoint Vfold_right (B : Type) (f : A->B->B) n (v : vec n) (b:B) : B :=
    match v with
      | Vnil => b
      | Vcons a _ w => f a (Vfold_right f w b)
    end.

  (* Vfold2 f x a{1..n} b{1..n} = f* a1 b1 (f* a2 b2 .. (f* an bn x) ..)
     Vfold2 f x a{1..n} b{1..p} = ⊥ if n ≠ p

     where f is partial
     and f* x y z = if z is Some v then f x y v else None *)

  Section FoldOpt2.

    Variable aT bT cT : Type.
    Variable x        : cT.
    Variable F        : aT -> bT -> cT -> option cT.

    Fixpoint Vfold2 nA nB (vA : vector aT nA) (vB : vector bT nB) :=
      match vA, vB with
        | Vnil, Vnil => Some x
        | Vcons xA nA sA, Vcons xB nB sB =>
          match Vfold2 sA sB with
            | Some v => F xA xB v
            | None   => None
          end
        | Vnil, Vcons _ _ _ => None
        | Vcons _ _ _, Vnil => None
      end .

  End FoldOpt2 .

End Vfolds.

(***********************************************************************)
(** conversion to lists *)

Require Import List.

Section vec_of_list.

  Variable A : Type. Notation vec := (vector A).

  Fixpoint vec_of_list (l : list A) : vec (length l) :=
    match l with
      | nil => Vnil
      | cons x m => Vcons x (vec_of_list m)
    end.

  Lemma vec_of_list_cons : forall a l,
    vec_of_list (a :: l) = Vcons a (vec_of_list l).

  Proof. auto. Qed.

  Fixpoint list_of_vec n (v : vec n) : list A :=
    match v with
      | Vnil => nil
      | Vcons x _ v => x :: list_of_vec v
    end.

  Lemma in_list_of_vec : forall n (v : vec n) x,
    In x (list_of_vec v) -> Vin x v.

  Proof. induction v; simpl; intros. hyp. destruct H; auto. Qed.

  Lemma list_of_vec_in : forall n (v : vec n) x,
    Vin x v -> In x (list_of_vec v).

  Proof.
    induction v; auto. intros. destruct H; simpl. auto. right. apply IHv. hyp.
  Qed.

  Lemma Vin_vec_of_list : forall l x, In x l <-> Vin x (vec_of_list l).

  Proof. induction l; simpl; intros. tauto. rewrite (IHl x). tauto. Qed.

  Lemma Vnth_vec_of_list : forall l d i (Hi : i < length l),
    Vnth (vec_of_list l) Hi = nth i l d.

  Proof.
    induction l. simpl. intros. absurd_arith.
    intros. rewrite vec_of_list_cons. destruct i; simpl; auto.
  Qed.

  Lemma vec_of_list_exact : forall i l (Hi : i < length(l)),
    element_at l i = Some (Vnth (vec_of_list l) Hi).

  Proof.
    induction i; intros.
    destruct l; simpl in *. contradict Hi; omega. auto.
    destruct l; simpl in *. contradict Hi; omega. apply IHi.
  Qed.

  Lemma list_of_vec_exact : forall i n (v : vec n) (Hi : i < n),
    element_at (list_of_vec v) i = Some (Vnth v Hi).

  Proof.
    induction i; intros.
    destruct v; simpl in *. contradict Hi; omega. auto.
    destruct v; simpl in *. contradict Hi; omega. apply IHi.
  Qed.

End vec_of_list.

(***********************************************************************)
(** decidability of equality *)

Section eq_dec.

  Variables (A : Type) (eq_dec : forall x y : A, {x=y}+{~x=y}).

  Notation vec := (vector A).

  Lemma eq_vec_dec : forall n (v1 v2 : vec n), {v1=v2}+{~v1=v2}.

  Proof.
    induction v1; intro. VOtac. auto. VSntac v2.
    case (eq_dec h (Vhead v2)); intro.
    rewrite e. case (IHv1 (Vtail v2)); intro. rewrite e0. auto.
    right. unfold not. intro. Veqtac. auto.
    right. unfold not. intro. Veqtac. auto.
  Defined.

End eq_dec.

(***********************************************************************)
(** boolean function testing equality *)

Section beq.

  Variables (A : Type) (beq : A -> A -> bool)
    (beq_ok : forall x y, beq x y = true <-> x = y).

  Notation vec := (vector A).

  Fixpoint beq_vec n (v : vec n) p (w : vec p) :=
    match v, w with
      | Vnil, Vnil => true
      | Vcons x _ v', Vcons y _ w' => beq x y && beq_vec v' w'
      | _, _ => false
    end.

  Lemma beq_vec_refl : forall n (v : vec n), beq_vec v v = true.

  Proof.
    induction v; simpl. refl.
    apply andb_intro. apply (beq_refl beq_ok). exact IHv.
  Qed.

  Lemma beq_vec_ok_length : forall n (v : vec n) p (w : vec p),
    beq_vec v w = true -> n = p.

  Proof.
    induction v; destruct w; simpl; intros; try (refl || discr).
    destruct (andb_elim H). ded (IHv _ _ H1). subst n0. refl.
  Qed.

  Implicit Arguments beq_vec_ok_length [n v p w].

  Lemma beq_vec_ok1_cast : forall n (v : vec n) p (w : vec p) (leq : n = p),
    beq_vec v w = true -> Vcast v leq = w.

  Proof.
    induction v; destruct w; simpl; intros; try (refl || discr).
    destruct (andb_elim H). rewrite beq_ok in H0. subst h0. apply Vtail_eq.
    apply IHv. hyp.
  Qed.

  Lemma beq_vec_ok1 : forall n (v w : vec n), beq_vec v w = true -> v = w.

  Proof.
    intros. rewrite <- (Vcast_refl v (refl_equal n)). apply beq_vec_ok1_cast.
    hyp.
  Qed.

  Lemma beq_vec_ok2 : forall n (v w : vec n), v = w -> beq_vec v w = true.

  Proof.
    induction v; intros. VOtac. refl. VSntac w. rewrite H0 in H. Veqtac.
    subst h. subst v. simpl. rewrite (beq_refl beq_ok). simpl.
    apply beq_vec_refl.
  Qed.

  Lemma beq_vec_ok : forall n (v w : vec n), beq_vec v w = true <-> v = w.

  Proof. split; intro. apply beq_vec_ok1. hyp. apply beq_vec_ok2. hyp. Qed.

End beq.

Implicit Arguments beq_vec_ok_length [n v p w].

Section beq_in.

  Variables (A : Type) (beq : A -> A -> bool).

  Notation vec := (vector A).

  Lemma beq_vec_ok_in1 : forall n (v : vec n)
    (hyp : forall x, Vin x v -> forall y, beq x y = true <-> x = y)
    p (w : vec p) (h : beq_vec beq v w = true),
    Vcast v (beq_vec_ok_length A beq h) = w.

  Proof.
    induction v; destruct w; simpl; intro; try (refl || discr).
    destruct (andb_elim h1).
    assert (ha : Vin h (Vcons h v)). simpl. auto.
    ded (hyp _ ha h0). rewrite H1 in H. subst h0. apply Vtail_eq.
    assert (hyp' : forall x, Vin x v -> forall y, beq x y = true <-> x=y).
    intros x hx. apply hyp. simpl. auto.
    destruct (andb_elim h1). ded (IHv hyp' _ w H2). rewrite <- H3.
    apply Vcast_pi.
  Qed.

  Lemma beq_vec_ok_in2 : forall n (v : vec n)
    (hyp : forall x, Vin x v -> forall y, beq x y = true <-> x = y) w,
    v = w -> beq_vec beq v w = true.

  Proof.
    induction v; intros. VOtac. refl. VSntac w. rewrite H0 in H. Veqtac.
    subst h. simpl. apply andb_intro. set (a := Vhead w).
    assert (Vin a (Vcons a v)). simpl. auto.
    ded (hyp _ H a). rewrite H1. refl.
    apply IHv. intros. apply hyp. simpl. auto. exact H3.
  Qed.

End beq_in.

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
Implicit Arguments beq_vec_ok_in1 [A beq n v p w].
Implicit Arguments beq_vec_ok_in2 [A beq n v w].
Implicit Arguments in_list_of_vec [A n v x].
Implicit Arguments Vforall_nth [A P n v i].
Implicit Arguments Vin_cast [A m n H v x].
Implicit Arguments Vsub [A n i k].
Implicit Arguments Vcast_eq_elim [A n v1 v2 m h].

(***********************************************************************)
(** map *)

Section map.

  Variables (A B : Type) (f : A->B).

  Notation vecA := (vector A). Notation vecB := (vector B).

  Fixpoint Vmap n (v : vecA n) : vecB n :=
    match v with
      | Vnil => Vnil
      | Vcons a _ v' => Vcons (f a) (Vmap v')
    end.

  Lemma Vnth_map : forall n (v : vecA n) i (H : i < n),
    Vnth (Vmap v) H = f (Vnth v H).

  Proof.
    intros n. elim n.
    intros v i H. elimtype False. apply (lt_n_O _ H).
    clear n. intros n Hrec v i. case i.
    intro. rewrite (VSn_eq v). simpl. refl.
    clear i. intros i Hi. rewrite (VSn_eq v). simpl.
    apply (Hrec (Vtail v) i (lt_S_n Hi)).
  Qed.

  Lemma Vin_map : forall x n (v : vecA n),
    Vin x (Vmap v) -> exists y, Vin y v /\ x = f y.

  Proof.
    induction v; simpl; intros. contr. destruct H. subst x. exists h.
    auto.
    assert (exists y, Vin y v /\ x = f y). apply IHv. hyp.
    destruct H0 as [y]. exists y. intuition.
  Qed.

  Lemma Vin_map_intro : forall x n (v : vecA n),
    Vin x v -> Vin (f x) (Vmap v).

  Proof.
    induction v; simpl; intros. contr. destruct H. subst x. auto.
    intuition.
  Qed.

  Lemma Vforall_map_elim : forall (P : B->Prop) n (v : vecA n),
    Vforall P (Vmap v) -> Vforall (fun a : A => P (f a)) v.

  Proof. induction v; simpl; intuition. Qed.

  Lemma Vforall_map_intro : forall (P : B->Prop) n (v : vecA n),
    Vforall (fun a : A => P (f a)) v -> Vforall P (Vmap v).

  Proof. induction v; simpl; intuition. Qed.

  Lemma Vmap_app : forall n1 n2 (v1 : vecA n1) (v2 : vecA n2),
    Vmap (Vapp v1 v2) = Vapp (Vmap v1) (Vmap v2).

  Proof.
    intros; induction v1.
    simpl; auto.
    simpl. rewrite IHv1. refl.
  Qed.

  Lemma Vmap_cast : forall m n (H : m=n) (v : vecA m),
    Vmap (Vcast v H) = Vcast (Vmap v) H.

  Proof.
    intros until H. case H. intro v. repeat rewrite Vcast_refl. refl.
  Qed.

  Lemma Vmap_tail : forall n (v : vecA (S n)),
    Vmap (Vtail v) = Vtail (Vmap v).

  Proof. intros. VSntac v. refl. Qed.

  Lemma Vmap_eq_nth : forall n (v1 : vecA n) (v2 : vecB n),
    (forall i (h : i<n), f (Vnth v1 h) = Vnth v2 h) -> Vmap v1 = v2.

  Proof.
    induction n; simpl; intros. VOtac. refl.
    VSntac v1. VSntac v2. simpl. apply Vcons_eq_intro.
    do 2 rewrite Vhead_nth. apply H.
    apply IHn. intros. do 2 rewrite Vnth_tail. apply H.
  Qed.

End map.

Implicit Arguments Vin_map [A B f x n v].
Implicit Arguments Vforall_map_elim [A B f P n v].
Implicit Arguments Vin_map_intro [A B x n v].

(***********************************************************************)
(** map first element *)

Section map_first.

  Variables (A B : Type) (default : B) (f : A->B).

  Notation vecA := (vector A).

  Definition Vmap_first n (v : vecA n) : B :=
    match v with
      | Vcons a _ _ => f a
      | _ => default
    end.

  Lemma Vmap_first_cast : forall n (v : vecA n) n' (h : n=n'),
    Vmap_first (Vcast v h) = Vmap_first v.

  Proof.
    destruct v; intros; destruct n'; try discr.
    rewrite Vcast_refl. refl.
    inversion h0. subst n'. rewrite Vcast_refl. refl.
  Qed.

End map_first.

(***********************************************************************)
(** map with a binary function *)

Section Vmap2.

  Variables A B C : Type.

  Fixpoint Vmap2 (f : A->B->C) n : vector A n -> vector B n -> vector C n :=
    match n with
      | O => fun _ _ => Vnil
      | _ => fun v1 v2 =>
        Vcons (f (Vhead v1) (Vhead v2)) (Vmap2 f (Vtail v1) (Vtail v2))
    end.

  (* map composition *)

  Lemma Vmap_map : forall (f:A->B) (g:B->C) n
    (v : vector A n), Vmap g (Vmap f v) = Vmap (fun x : A => g (f x)) v.

  Proof.
    intros; induction v.
    simpl; refl.
    simpl Vmap at 2. simpl Vmap at 1.
    rewrite IHv. refl.
  Qed.

  (* nth element in a map *)

  Lemma Vnth_map2 : forall (f : A -> B -> C) n 
    (vl : vector A n) (vr : vector B n) i (ip : i < n),
    Vnth (Vmap2 f vl vr) ip = f (Vnth vl ip) (Vnth vr ip).

  Proof.
    induction n; intros.
    VOtac. absurd_arith.
    VSntac vl. VSntac vr. destruct i. refl. 
    simpl. apply IHn.
  Qed.

End Vmap2.

(***********************************************************************)
(** vforall and specifications *)

Fixpoint Vforall_of_vsig (A : Type) (P : A -> Prop) n (v : vector (sig P) n)
  : Vforall P (Vmap (@proj1_sig A P) v) :=
  match v in vector _ n return Vforall P (Vmap (@proj1_sig A P) v) with
  | Vnil => I
  | Vcons a _ w => conj (@proj2_sig A P a) (Vforall_of_vsig w)
  end.

Lemma Vmap_proj1 : forall (A : Type) (P : A->Prop) n (v : vector A n)
  (Hv : Vforall P v), v = Vmap (@proj1_sig A P) (Vsig_of_v Hv).

Proof.
  intros A P n v. elim v.
  simpl. intro. refl.
  intros a p w. intro Hrec.
  simpl. intro Hv. case Hv. intros H1 H2. simpl Vmap.
  gen (Hrec H2). intro H. apply Vcons_eq_intro; auto.
Qed.

Implicit Arguments Vmap_proj1 [A P n v].

(***********************************************************************)
(** equality of vmap's *)

Lemma Vmap_eq : forall (A B : Type) (f g : A->B) n (v : vector A n),
  Vforall (fun a => f a = g a) v -> Vmap f v = Vmap g v.

Proof.
  induction v; simpl; intros. refl. destruct H. apply Vcons_eq_intro; auto.
Qed.

Implicit Arguments Vmap_eq [A B f g n v].

Lemma Vmap_eq_ext : forall (A B : Type) (f g : A->B),
  (forall a, f a = g a) ->
  forall n (v : vector A n), Vmap f v = Vmap g v.

Proof. induction v; intros; simpl. refl. apply Vcons_eq_intro; auto. Qed.

Lemma Vmap_id : forall (A : Type) n (v : vector A n),
  Vmap (fun x => x) v = v.

Proof. induction v. refl. simpl. apply Vcons_eq_intro; auto. Qed.

Lemma Vmap_eq_id : forall (A : Type) (f : A->A) n (v : vector A n),
  Vforall (fun a => f a = a) v -> Vmap f v = v.

Proof. intros. rewrite <- Vmap_id. apply Vmap_eq. hyp. Qed.

Lemma Vmap_eq_ext_id : forall (A : Type) (f : A->A), (forall a, f a = a) ->
  forall n (v : vector A n), Vmap f v = v.

Proof. intros. rewrite <- Vmap_id. apply Vmap_eq_ext. hyp. Qed.

(***********************************************************************)
(** Vforall <-> lforall  *)

Require Import ListForall.

Lemma lforall_Vforall : forall (A : Type) (l : list A) (p : A -> Prop),
  lforall p l -> Vforall p (vec_of_list l).

Proof.
  intros. gen H. induction l. trivial. 
  intros lforall. red in lforall. destruct lforall as [pa lforall].
  red. simpl. split. trivial. 
  unfold Vforall in IHl. apply IHl; trivial.
Qed.

Lemma Vforall_lforall : forall (A : Type) n (v : vector A n)
  (p : A -> Prop), Vforall p v -> lforall p (list_of_vec v).

Proof.
  intros. gen H. induction v. trivial. 
  intros lforall. red in lforall. destruct lforall as [pa vforall].
  red. simpl. split. trivial. 
  unfold lforall in IHv. apply IHv; trivial.
Qed.

(***********************************************************************)
(** bVforall *)

Section bVforall_sec.

  Variables (A : Type) (P : A -> Prop) (f : A -> bool)
    (f_ok : forall x, f x = true <-> P x).

  Fixpoint bVforall n (v : vector A n) : bool :=
    match v with
      | Vnil => true
      | Vcons a _ w => f a && bVforall w
    end.

  Lemma bVforall_ok : forall n (v : vector A n),
    bVforall v = true <-> Vforall P v.

  Proof. induction v; simpl. tauto. rewrite andb_eq. rewrite f_ok. tauto. Qed.

End bVforall_sec.

(***********************************************************************)
(** bVforall2 *)

Section bVforall2_sec.

  Variables (A B : Type) (P : A -> B -> bool).

  Fixpoint bVforall2n_aux n1 (v1 : vector A n1) n2 (v2 : vector B n2) : bool :=
    match v1, v2 with
      | Vnil, Vnil => true
      | Vcons x _ xs, Vcons y _ ys => P x y && bVforall2n_aux xs ys
      | _, _ => false
    end.

  Definition bVforall2n n (v1 : vector A n) (v2 : vector B n) :=
    bVforall2n_aux v1 v2.

End bVforall2_sec.

(****************************************************************************)
(** * Build a vector of [option A] of size [n] from the elements (if
they exist) of an arbitrary vector [xs] of size [p] whose positions
are given by a vector [ks] of natural numbers of size [n]. *)

Section filter.

  Variable (A : Type).

  Fixpoint vec_opt_filter n (ks : vector nat n) p (xs : vector A p) :=
    match ks in vector _ n return vector (option A) n with
      | Vnil => Vnil
      | Vcons k _ ks' =>
        Vcons (match lt_dec k p with left h => Some (Vnth xs h) | _ => None end)
          (vec_opt_filter ks' xs)
    end.

End filter.
