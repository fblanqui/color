(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-04-02
- Frederic Blanqui, 2005-01-27 and later
- Adam Koprowski and Hans Zantema, 2007-03-26
- Joerg Endrullis, 2008-06-19
- Pierre-Yves Strub, 2009-04-09
- Wang Qian & Zhang Lianyi, 2009-05-06

* Extension of the Coq library Vector
*)

Set Implicit Arguments.

From Coq Require Import Vector Program Structures.Equalities Morphisms.
From CoLoR Require Import LogicUtil NatUtil EqUtil ListUtil BoolUtil RelUtil.

Notation vector := Vector.t.
Notation Vnil := Vector.nil.
Notation Vcons := Vector.cons.
Notation Vhead := Vector.hd.
Notation Vtail := Vector.tl.
Notation Vconst := Vector.const.

Arguments Vnil {A}.
Arguments Vcons [A] _ [n] _.
Arguments Vhead [A n] _.
Arguments Vtail [A n] _.
Arguments Vconst [A] _ _.

Declare Scope vec_scope.

(***********************************************************************)
(** Notations for vectors. *)

Module VectorNotations.
  Notation " [ ] " := Vnil : vector_scope.
  Notation " [ x ] " := (Vcons x Vnil) : vector_scope.
  Notation " [ x ; .. ; y ] " := (Vcons x .. (Vcons y Vnil) ..)
    : vector_scope.
End VectorNotations.

(***********************************************************************)
(** Tactic for destructuring equalities on vectors. *)

Ltac Veqtac := repeat
  match goal with
    | H : Vcons ?x ?v = Vcons ?x ?w |- _ =>
      let h := fresh in
      (injection H; intro h; ded (inj_existT eq_nat_dec h);
        clear h; clear H)
    | H : Vcons ?x ?v = Vcons ?y ?w |- _ =>
      let h1 := fresh in let h2 := fresh in
      (injection H; intros h1 h2; ded (inj_existT eq_nat_dec h1);
        clear h1; clear H)
  end.

(***********************************************************************)
(** ** Elementary identities. *)

Section Velementary.

  Variable A : Type. Notation vec := (vector A).

  Definition Vid n : vector A n -> vector A n :=
    match n with
      | O => fun _ => Vnil
      | _ => fun v => Vcons (Vhead v) (Vtail v)
    end.

  Lemma Vid_eq : forall n (v : vector A n), v = Vid v.

  Proof. destruct v; auto. Defined.

  Lemma VSn_eq : forall n (v : vector A (S n)), v = Vcons (Vhead v) (Vtail v).

  Proof.
    intros. change (Vcons (Vhead v) (Vtail v)) with (Vid v). apply Vid_eq.
  Defined.

  Definition Vhead_tail n (v : vector A (S n)) := (Vhead v, Vtail v).

  Lemma Vcons_eq_intro : forall a1 a2 n (v1 v2 : vector A n),
    a1 = a2 -> v1 = v2 -> Vcons a1 v1 = Vcons a2 v2.

  Proof. intros. subst a1. subst v1. refl. Qed.

  Lemma Vcons_eq_elim : forall a1 a2 n (v1 v2 : vector A n),
    Vcons a1 v1 = Vcons a2 v2 -> a1 = a2 /\ v1 = v2.

  Proof. intros. Veqtac. auto. Qed.

  Lemma Vcons_eq : forall a1 a2 n (v1 v2 : vector A n),
    Vcons a1 v1 = Vcons a2 v2 <-> a1 = a2 /\ v1 = v2.

  Proof with auto.
    split; intros. 
    apply Vcons_eq_elim... 
    destruct H. apply Vcons_eq_intro...
  Qed.

  Lemma Vtail_eq : forall a n (v1 v2 : vector A n),
    v1 = v2 -> Vcons a v1 = Vcons a v2.

  Proof. intros. apply Vcons_eq_intro. refl. hyp. Qed.

End Velementary.

Arguments VSn_eq [A n] _.

(***********************************************************************)
(** Tactic for destructing non empty vectors. *)

Ltac VSntac y := let h := fresh in gen (VSn_eq y); intro h; try rewrite h.

(***********************************************************************)
(** ** First element of a vector with default value if empty. *)

Definition Vfirst A default n (v : vector A n) : A :=
  match v with
    | Vnil => default
    | Vcons x _ => x
  end.

(***********************************************************************)
(** ** Type casting function on vectors. *)

Section Vcast.

  Variable A : Type.

  Definition Vcast m (v : vector A m) n (mn : m = n) : vector A n :=
    match mn in _ = p return vector A p with
      | eq_refl => v
    end.
 
  Lemma Vcast_cons n (v : vector A n) x p (hS : S n = S p) :
    Vcast (Vcons x v) hS = Vcons x (Vcast v (eq_add_S hS)).

  Proof.
    inversion hS. rewrite (eq_unique hS (f_equal S H0)). case H0. refl.
  Qed.

  Lemma Vcast_refl n (v : vector A n) : forall H : n=n, Vcast v H = v.

  Proof. apply K_dec_type; auto with arith. Defined.

  Lemma Vcast_eq_elim : forall n (v1 v2 : vector A n) m (h : n = m),
    Vcast v1 h = Vcast v2 h -> v1 = v2.

  Proof. intros until h; case h; trivial. Qed.

  Arguments Vcast_eq_elim [n v1 v2 m h] _.

  Lemma Vcast_cast_eq :
    forall n (v : vector A n) m (h1 : n=m) p (h2 : m=p) (h3 : n=p),
      Vcast (Vcast v h1) h2 = Vcast v h3.

  Proof. intros ? ? ? [] ? []; auto using Vcast_refl. Qed.

  Lemma Vcast_cast : forall n (v : vector A n) m (h1 : n=m) p (h2 : m=p),
    Vcast (Vcast v h1) h2 = Vcast v (trans_eq h1 h2).

  Proof. intros. apply Vcast_cast_eq. Qed.

  Lemma Vcast_eq_intror : forall n1 (v1 : vector A n1) n0 (h1 : n1=n0)
    n2 (v2 : vector A n2) (h2 : n2=n0) (h : n1=n2),
    Vcast v1 h = v2 -> Vcast v1 h1 = Vcast v2 h2.

  Proof.
    intros until h1; case h1; intros; simpl; subst v2.
    rewrite Vcast_cast, Vcast_refl; refl.
  Qed.

  Lemma Vcast_eq_intro : forall n (v1 v2 : vector A n) p (e : n=p),
    v1 = v2 -> Vcast v1 e = Vcast v2 e.

  Proof. induction v1; intros. subst v2. refl. rewrite H. refl. Qed.

  Lemma Vcast_eq : forall n (v1 v2 : vector A n) p (e : n=p),
    Vcast v1 e = Vcast v2 e <-> v1 = v2.

  Proof. split; intro. apply (Vcast_eq_elim H). apply Vcast_eq_intro. hyp. Qed.

  Lemma Vcast_pi : forall n (v : vector A n) p (h1 : n=p) (h2 : n=p),
    Vcast v h1 = Vcast v h2.

  Proof.
    intros; f_equal; apply eq_proofs_unicity.
    intros x y; case (eq_nat_dec x y); tauto.
  Qed.

  Lemma Vcast_lr : forall n1 (v1 : vector A n1) n2 (v2 : vector A n2)
    (h12 : n1=n2) (h21 : n2=n1), Vcast v1 h12 = v2 -> v1 = Vcast v2 h21.

  Proof. intros; subst v2; rewrite Vcast_cast, Vcast_refl; refl. Qed.

  Lemma Vcast_rl : forall n1 (v1 : vector A n1) n2 (v2 : vector A n2)
    (h12 : n1=n2) (h21 : n2=n1), v1 = Vcast v2 h21 -> Vcast v1 h12 = v2.

  Proof. intros; sym; apply Vcast_lr with h21; hyp. Qed.

  Lemma Vcast_introrl : forall n1 (v1 : vector A n1) n2 (v2 : vector A n2)
    (h21 : n2=n1), Vcast v1 (sym_eq h21) = v2 -> v1 = Vcast v2 h21.

  Proof. intros. eapply Vcast_lr. apply H. Qed.

  Lemma Vcast_elimlr : forall n1 (v1 : vector A n1) n2 (v2 : vector A n2)
    (h12 : n1=n2), Vcast v1 h12 = v2 -> v1 = Vcast v2 (sym_eq h12).

  Proof. intros. eapply Vcast_lr. apply H. Qed.

End Vcast.

Arguments Vcast_eq_elim [A n v1 v2 m h] _.
Arguments Vcast_cons [A n v x p] _.

(***********************************************************************)
(** ** Lemma and tactic for replacing an empty vector by Vnil. *)

Definition VO_eq A (v : vector A O) : v = Vnil
  := match v with Vnil => eq_refl _ end.

Ltac VOtac := repeat
  match goal with
    | v : vector _ O |- _ => assert (v = Vnil); [apply VO_eq | subst v]
  end.

(***********************************************************************)
(** ** N-th element of a vector. *)

Section Vnth.

  Variable A : Type.

  Program Fixpoint Vnth n (v : vector A n) : forall i, i < n -> A :=
    match v with
      | Vnil => fun i ip => !
      | Vcons x v' => fun i =>
        match i with
          | 0 => fun _ => x
          | S j => fun H => Vnth v' (i:=j) _
        end
    end.
  Solve Obligations.
  Next Obligation. exact (Nat.nlt_0_r ip). Defined.
  Next Obligation. exact (NatUtil.lt_S_n H). Defined.

  Lemma Vhead_nth : forall n (v : vector A (S n)), Vhead v = Vnth v (Nat.lt_0_succ n).

  Proof. intros. VSntac v. refl. Qed.

  Lemma Vnth_eq : forall n (v : vector A n) i1 (h1 : i1<n) i2 (h2 : i2<n),
    i1 = i2 -> Vnth v h1 = Vnth v h2.

  Proof.
    induction v; intro; case i1.
    intro. absurd (0 <= 0); lia.
    intros n h1. absurd (0 <= S n); lia.
    intros. subst i2. refl.
    intros. subst i2. simpl. apply IHv. refl.
  Qed.

  Lemma Vnth_tail : forall n (v : vector A (S n)) i (h : i < n),
    Vnth (Vtail v) h = Vnth v (lt_n_S h).

  Proof. intros. VSntac v. simpl. apply Vnth_eq. refl. Qed.

  Lemma Vnth_cons_head : forall x n (v : vector A n) k (h : k < S n),
    k = 0 -> Vnth (Vcons x v) h = x.

  Proof. intros. subst k. refl. Qed.

  Lemma Vnth_cons_tail_aux : forall n i, i < S n -> i > 0 -> i-1 < n.

  Proof. lia. Qed.

  Lemma Vnth_cons_tail : forall x n (v : vector A n) i (h1:i<S n) (h2:i>0),
    Vnth (Vcons x v) h1 = Vnth v (Vnth_cons_tail_aux h1 h2).

  Proof. intros. simpl. destruct i. lia. apply Vnth_eq. lia. Qed.

  Lemma Vnth_cons : forall x n (v : vector A n) i (h1:i<S n),
    Vnth (Vcons x v) h1 = match lt_ge_dec 0 i with
                            | left h2 => Vnth v (Vnth_cons_tail_aux h1 h2)
                            | _ => x
                          end.

  Proof.
    intros. case (lt_ge_dec 0 i); intro. apply Vnth_cons_tail.
    apply Vnth_cons_head. lia.
  Qed.

  Lemma Vnth_const : forall n (a : A) i (ip : i < n), Vnth (Vconst a n) ip = a.

  Proof.
    induction n; intros. lia. destruct i. trivial. simpl. rewrite IHn. refl.
  Qed.

  Lemma Vnth_cast_aux : forall n n' k, n = n' -> k < n' -> k < n.

  Proof. lia. Qed.

  Lemma Vnth_cast : forall n (v : vector A n) n' (e : n = n') k (h : k < n'),
    Vnth (Vcast v e) h = Vnth v (Vnth_cast_aux e h).

  Proof.
    induction v as [|x p v IHv]. intros; lia. intros [|n']; try discr.
    inversion e; subst p; intros [|k] h; rewrite Vcast_refl; simpl.
    refl. rewrite (IHv n' (eq_refl n') k); apply Vnth_eq; refl.
  Qed.

  Lemma Veq_nth : forall n (v v' : vector A n), 
    (forall i (ip : i < n), Vnth v ip = Vnth v' ip) -> v = v'.

  Proof.
    induction n; intros.
    VOtac. refl.
    VSntac v. VSntac v'. apply Vcons_eq_intro.
    rewrite !Vhead_nth. apply H.
    apply IHn. intros. rewrite !Vnth_tail. apply H.
  Qed.

End Vnth.

Notation "v '[@' p ']'" := (Vnth v p) (at level 0) : vec_scope.

(***********************************************************************)
(** ** Add an element at the end of a vector. *)

Section Vadd.

  Variable A : Type.

  Fixpoint Vadd n (v : vector A n) (x : A) : vector A (S n) :=
    match v with
      | Vnil => Vcons x Vnil
      | Vcons a v' => Vcons a (Vadd v' x)
    end.

  Lemma Vnth_addl : forall k n (v : vector A n) a (H1 : k < S n) (H2 : k < n),
    Vnth (Vadd v a) H1 = Vnth v H2.

  Proof.
    intros. assert (H3 : H1 = (@le_S (S k) n H2)). apply lt_unique.
    subst H1. generalize dependent k. generalize dependent n. intro n. elim n.
    intros v k H. exfalso. apply (Nat.nlt_0_r H).
    intros n' Hrec v k H. rewrite (VSn_eq v). destruct k.
    simpl. refl.
    simpl Vadd.
    assert (H' : k < S n'). auto with arith. simpl. 
    assert (lt_S_n (le_S H) = le_S (lt_S_n H)). apply lt_unique.
    rewrite H0, Hrec. refl.
  Qed.

  Lemma Vnth_addr : forall k n (v : vector A n) a (H1 : k < S n) (H2 : k = n),
    Vnth (Vadd v a) H1 = a.

  Proof.
    intros. subst k. assert (H2 : H1 = Nat.lt_succ_diag_r n). apply lt_unique. subst H1.
    generalize dependent v. intro v. elim v.
    simpl. refl.
    intros a' p' v' Hrec. simpl. rewrite <- Hrec at -1. apply Vnth_eq. refl.
  Qed.

  Lemma Vnth_add_aux : forall i n, i < S n -> i <> n -> i < n.

  Proof. lia. Qed.

  Lemma Vnth_add : forall n (v : vector A n) x i (h : i < S n),
    Vnth (Vadd v x) h =
    match eq_nat_dec i n with
      | left _ => x
      | right n => Vnth v (Vnth_add_aux h n)
    end.

  Proof.
    induction v; intros x i hi; simpl Vadd.
    (* nil *)
    destruct (eq_nat_dec i 0). apply Vnth_cons_head. hyp. lia.
    (* cons *)
    destruct (eq_nat_dec i (S n)).
    (* i = S n *)
    subst. rewrite Vnth_cons. destruct (lt_ge_dec 0 (S n)). 2: lia.
    rewrite IHv. destruct (eq_nat_dec (S n - 1) n). refl. lia.
    (* i <> S n *)
    rename h into y. rewrite Vnth_cons. destruct (lt_ge_dec 0 i).
    rewrite IHv. destruct (eq_nat_dec (i-1) n). lia.
    rewrite Vnth_cons. destruct (lt_ge_dec 0 i). 2: lia. apply Vnth_eq. refl.
    sym. apply Vnth_cons_head. lia.
  Qed.

  Lemma Vadd_cons : forall x n (v : vector A (S n)),
    Vadd v x = Vcons (Vhead v) (Vadd (Vtail v) x).

  Proof. intro x. destruct n; intro v; rewrite (VSn_eq v) at 1; refl. Qed.

End Vadd.

(***********************************************************************)
(** ** Replace the i-th element of a vector by some value. *)

Section Vreplace.

  Variable A : Type.

  Program Fixpoint Vreplace n (v : vector A n) i (ip : i < n) (a : A)
    : vector A n :=
    match v with 
      | Vnil => !
      | Vcons h v' => 
        match i with
          | 0 => Vcons a v'
          | S i' => Vcons h (Vreplace v' (i:=i') _ a)
        end
    end.
  Next Obligation. exact (Nat.nlt_0_r ip). Defined.
  Next Obligation. exact (NatUtil.lt_S_n ip). Defined.

  Lemma Vreplace_tail : forall n i (ip : S i < S n) (v : vector A (S n)) a,
    Vreplace v ip a = Vcons (Vhead v) (Vreplace (Vtail v) (lt_S_n ip) a).

  Proof. destruct n; intros. lia. VSntac v. refl. Qed.

  Lemma Vnth_replace : forall n i (ip ip' : i < n) (v : vector A n) (a : A),
    Vnth (Vreplace v ip a) ip' = a.

  Proof.
    induction n; intros. lia.
    VSntac v. destruct i. trivial. simpl. apply IHn.
  Qed.

  Lemma Vnth_replace_neq : forall n i (ip : i < n) j (jp : j < n) 
    (v : vector A n) (a : A), i <> j -> Vnth (Vreplace v ip a) jp = Vnth v jp.

  Proof.
    induction n; intros. lia.
    VSntac v. destruct i; destruct j; trivial.
    lia. simpl. rewrite IHn. trivial. lia.
  Qed.

  Lemma Vreplace_pi : forall n (v : vector A n) i1 i2 (h1 : i1 < n)
    (h2 : i2 < n) x, i1 = i2 -> Vreplace v h1 x = Vreplace v h2 x.

  Proof.
    intros. subst i2. revert i1 h1 h2. elim v; clear v; simpl; intros.
    lia. destruct i1. refl. apply Vtail_eq. apply H.
  Qed.

  Lemma Vreplace_eq_elim : forall n (v : vector A n) i (h : i < n) x x',
    Vreplace v h x = Vreplace v h x' -> x = x'.

  Proof.
    intros. ded (f_equal (fun v => @Vnth A n v i h) H).
    rewrite !Vnth_replace in H0. hyp.
  Qed.

  Lemma Vreplace_nth_eq : forall n (v : vector A n) i (h : i < n),
    Vreplace v h (Vnth v h) = v.

  Proof.
    intros. apply Veq_nth. intro j. case (eq_nat_dec i j); intro Eij.
    rewrite <- Eij. intro hj. rewrite (Vnth_eq v h hj); auto.
    apply Vnth_replace.
    intro hj. apply Vnth_replace_neq; auto.
  Qed.

End Vreplace.

(***********************************************************************)
(** ** Concatenation of two vectors. *)

Section Vapp.

  Variable A : Type.

  Fixpoint Vapp n1 n2 (v1 : vector A n1) (v2 : vector A n2)
    : vector A (n1+n2) :=
    match v1 with
      | Vnil => v2
      | Vcons a v' => Vcons a (Vapp v' v2)
    end.

  Lemma Vapp_cons : forall a n1 n2 (v1 : vector A n1) (v2 : vector A n2),
    Vapp (Vcons a v1) v2 = Vcons a (Vapp v1 v2).

  Proof. refl. Qed.

  Lemma Vapp_nil_eq : forall n (v : vector A n) (w : vector A 0) (h : n=n+0),
    Vapp v w = Vcast v h.

  Proof.
    induction v; intros.
    VOtac; rewrite Vcast_refl; refl.
    rewrite (Vcast_cons h0), <- (IHv w); refl.
  Qed.

  Lemma Vapp_nil : forall n (v : vector A n) (w : vector A 0), 
    Vapp v w = Vcast v (plus_n_O n).

  Proof. intros. apply Vapp_nil_eq. Qed.

  Lemma Vapp_rcast_eq : forall n1 (v1 : vector A n1) n2 (v2 : vector A n2) p2
    (h1 : n2=p2) (h2 : n1+n2=n1+p2),
    Vapp v1 (Vcast v2 h1) = Vcast (Vapp v1 v2) h2.

  Proof.
    induction v1; simpl; intros.
    f_equal. apply eq_unique.
    rewrite Vcast_cons. f_equal. apply IHv1.
  Qed.

  Lemma Vapp_rcast : forall n1 (v1 : vector A n1) n2 (v2 : vector A n2) p2
    (h1 : n2=p2),
    Vapp v1 (Vcast v2 h1) = Vcast (Vapp v1 v2) (plus_reg_l_inv n1 h1).

  Proof. intros. apply Vapp_rcast_eq. Qed.

  Lemma Vapp_lcast_eq : forall n1 (v1 : vector A n1) n2 (v2 : vector A n2) p1
    (h1 : n1=p1) (h2 : n1+n2=p1+n2),
    Vapp (Vcast v1 h1) v2 = Vcast (Vapp v1 v2) h2.

  Proof.
    induction v1; intros until p1; case p1; simpl; intros; try discr.
    repeat rewrite Vcast_refl; refl.
    rewrite !Vcast_cons. simpl. f_equal. apply IHv1.
  Qed.

  Lemma Vapp_lcast :  forall n1 (v1 : vector A n1) n2 (v2 : vector A n2) p1
    (h1 : n1=p1),
    Vapp (Vcast v1 h1) v2 = Vcast (Vapp v1 v2) (plus_reg_r_inv n2 h1).

  Proof.
    intros. apply Vapp_lcast_eq.
  Qed.

  Lemma Vapp_assoc_eq : forall n1 (v1 : vector A n1) n2 (v2 : vector A n2)
    n3 (v3 : vector A n3) (h : n1+(n2+n3) = (n1+n2)+n3),
    Vapp (Vapp v1 v2) v3 = Vcast (Vapp v1 (Vapp v2 v3)) h.

  Proof.
    induction v1; intros; simpl.
    rewrite Vcast_refl. refl.
    rewrite Vcast_cons. f_equal. apply IHv1.
  Qed.

  Lemma Vapp_assoc : forall n1 (v1 : vector A n1) n2 (v2 : vector A n2)
    n3 (v3 : vector A n3),
    Vapp (Vapp v1 v2) v3 = Vcast (Vapp v1 (Vapp v2 v3)) (Nat.add_assoc n1 n2 n3).

  Proof. intros. apply Vapp_assoc_eq. Qed.

  Lemma Vapp_eq_intro : forall n1 (v1 v1' : vector A n1) n2
    (v2 v2' : vector A n2), v1 = v1' -> v2 = v2' -> Vapp v1 v2 = Vapp v1' v2'.

  Proof. intros. rewrite H, H0. refl. Qed.

  Lemma Vapp_eq : forall n1 (v1 v1' : vector A n1) n2 (v2 v2' : vector A n2),
    Vapp v1 v2 = Vapp v1' v2' <-> v1 = v1' /\ v2 = v2'.

  Proof.
    induction v1; simpl. intro. VOtac. simpl. intros. tauto.
    intro. VSntac v1'. simpl. split; intro. Veqtac. subst h.
    rewrite IHv1 in H3.
    intuition. rewrite H0. refl. destruct H0. Veqtac. subst h.
    apply Vcons_eq_intro. refl. rewrite IHv1. intuition.
  Qed.

  Lemma Vnth_app_aux : forall n1 n2 i, i < n1+n2 -> n1 <= i -> i - n1 < n2.

  Proof. lia. Qed.

  Arguments Vnth_app_aux [n1 n2 i] _ _.

  Lemma Vnth_app : forall n1 (v1 : vector A n1) n2 (v2 : vector A n2)
    i (h : i < n1+n2), Vnth (Vapp v1 v2) h =
    match le_gt_dec n1 i with
      | left p => Vnth v2 (Vnth_app_aux h p)
      | right p => Vnth v1 p
    end.

  Proof.
    induction v1; intros. simpl. apply Vnth_eq. lia.
    destruct i. refl. simpl le_gt_dec. ded (IHv1 _ v2 i (lt_S_n h0)). revert H.
    case (le_gt_dec n i); simpl; intros.
    (* case 1 *)
    trans (Vnth v2 (Vnth_app_aux (lt_S_n h0) l)). hyp.
    apply Vnth_eq. lia.
    (* case 2 *)
    trans (Vnth v1 g). hyp. apply Vnth_eq. refl.
  Qed.

  Lemma Vnth_app_cons : forall n1 (v1 : vector A n1) n2 (v2 : vector A n2)
    (h : n1 < n1 + S n2) x, Vnth (Vapp v1 (Vcons x v2)) h = x.

  Proof. induction v1; intros; simpl. refl. apply IHv1. Qed.

  Lemma Vnth_app_cons_neq : forall n1 (v1 : vector A n1) n2 (v2 : vector A n2) k
    (h : k < n1 + S n2) x x',
    k <> n1 -> Vnth (Vapp v1 (Vcons x v2)) h = Vnth (Vapp v1 (Vcons x' v2)) h.

  Proof.
    induction v1; intros.
    simpl. destruct k. cong. refl.
    rewrite !Vapp_cons. destruct k. refl. apply IHv1. lia.
  Qed.

  Lemma Vapp_cast_aux : forall n1 n2 n2', n2 = n2' -> n1+n2 = n1+n2'.

  Proof. lia. Qed.

  Lemma Vapp_cast : forall n1 (v1 : vector A n1) n2 (v2 : vector A n2)
    n2' (e : n2 = n2'),
    Vapp v1 (Vcast v2 e) = Vcast (Vapp v1 v2) (Vapp_cast_aux n1 e).

  Proof.
    induction v1; simpl; intros.
    apply Vcast_pi.
    rewrite Vcast_cons, IHv1. f_equal. apply Vcast_pi.
  Qed.

  Lemma Vadd_app_aux : forall p q, p + S q = S (p+q).

  Proof. intros p q. lia. Qed.

  Lemma Vadd_app : forall p (v : vector A p) q (w : vector A q) x,
    Vadd (Vapp v w) x = Vcast (Vapp v (Vadd w x)) (Vadd_app_aux p q).

  Proof.
    induction v; simpl; intros q w x.
    rewrite Vcast_refl. refl.
    rewrite Vcast_cons, IHv. f_equal. apply Vcast_pi.
  Qed.

End Vapp.

(***********************************************************************)
(** ** Breaking a vector into two sub-vectors. *)

Section Vbreak.

  Variable A : Type.

  Fixpoint Vbreak n1 n2 : vector A (n1+n2) -> vector A n1 * vector A n2 :=
    match n1 with
      | O => fun v => (Vnil, v)
      | S p1 => fun v =>
        let w := Vbreak p1 n2 (Vtail v) in (Vcons (Vhead v) (fst w), snd w)
    end.

  Arguments Vbreak [n1 n2] _.

  Lemma Vbreak_app : forall n1 (v1 : vector A n1) n2 (v2 : vector A n2),
    Vbreak (Vapp v1 v2) = (v1, v2).

  Proof.
    induction n1; simpl; intros. VOtac. refl. VSntac v1. simpl.
    gen (IHn1 (Vtail v1) n2 v2). intro. rewrite H0. refl.
  Qed.

  Lemma Vbreak_eq_app : forall n1 n2 (v : vector A (n1+n2)),
    v = Vapp (fst (Vbreak v)) (snd (Vbreak v)).

  Proof.
    intros n1 n2. elim n1.
    auto.
    clear n1. intros n1 Hrec. simpl. intro v. gen (Hrec (Vtail v)); intro H.
    rewrite VSn_eq at 1. rewrite H at 1. refl.
  Qed.

  Lemma Vbreak_eq_app_cast : forall n n1 n2 (H : n1+n2=n) (v : vector A n),
    v = Vcast (Vapp (fst (Vbreak (Vcast v (sym_equal H))))
      (snd (Vbreak (Vcast v (sym_equal H))))) H.

  Proof.
    intros until H; case H; simpl; intro v. rewrite <- Vbreak_eq_app; refl.
  Qed.

End Vbreak.

Arguments Vbreak [A n1 n2] _.
Arguments Vbreak_eq_app [A n1 n2] _.
Arguments Vbreak_eq_app_cast [A n n1 n2] _ _.

(***********************************************************************)
(** ** Membership predicate on vectors. *)

Section Vin.

  Variable A : Type.

  Fixpoint Vin (x : A) n (v : vector A n) : Prop :=
    match v with
      | Vnil => False
      | Vcons y w => y = x \/ Vin x w
    end.

  Lemma Vin_head : forall n (v : vector A (S n)), Vin (Vhead v) v.

  Proof. intros. VSntac v. simpl. auto. Qed.

  Lemma Vin_tail : forall n x (v : vector A (S n)), Vin x (Vtail v) -> Vin x v.

  Proof. intros. VSntac v. simpl. auto. Qed.

  Lemma Vnth_in : forall n (v : vector A n) k (h : k<n), Vin (Vnth v h) v.

  Proof.
    induction v. intros. absurd (k<0); lia.
    intro. destruct k; simpl. auto. intro. right. apply IHv.
  Qed.

  Lemma Vin_nth : forall n (v : vector A n) a, Vin a v ->
    exists i, exists ip : i < n, Vnth v ip = a.

  Proof.
    induction n; intros. 
    VOtac. destruct H.
    VSntac v. rewrite H0 in H. destruct H.
    exists 0. exists (Nat.lt_0_succ n). simpl. congruence.
    destruct (IHn (Vtail v) a H) as [j [jp v_j]].
    exists (S j). exists (lt_n_S jp). simpl.
    rewrite lt_Sn_nS. hyp.
  Qed.

  Lemma Vin_cast_intro : forall m n (H : m=n) (v : vector A m) x,
    Vin x v -> Vin x (Vcast v H).

  Proof.
    intros m n H. case H. intros. rewrite Vcast_refl. hyp.
  Qed.

  Lemma Vin_cast_elim : forall m n (H : m=n) (v : vector A m) x,
    Vin x (Vcast v H) -> Vin x v.

  Proof. intros m n H. case H. intros v x. rewrite Vcast_refl. auto. Qed.

  Arguments Vin_cast_elim [m n H v x] _.

  Lemma Vin_cast : forall m n (H : m=n) (v : vector A m) x,
    Vin x (Vcast v H) <-> Vin x v.

  Proof. intros m n H. case H. intros. rewrite Vcast_refl. tauto. Qed.

  Lemma Vin_appl : forall x n1 (v1 : vector A n1) n2 (v2 : vector A n2),
    Vin x v1 -> Vin x (Vapp v1 v2).

  Proof.
    induction v1; simpl; intros. contr. destruct H. auto.
    right. apply IHv1. hyp.
  Qed.

  Lemma Vin_appr : forall x n1 (v1 : vector A n1) n2 (v2 : vector A n2),
    Vin x v2 -> Vin x (Vapp v1 v2).

  Proof. induction v1; simpl; intros. hyp. right. apply IHv1. hyp. Qed.

  Lemma Vin_app_cons : forall x n1 (v1 : vector A n1) n2 (v2 : vector A n2),
    Vin x (Vapp v1 (Vcons x v2)).

  Proof. induction v1; intros; simpl; auto. Qed.

  Lemma Vin_app : forall x n1 (v1 : vector A n1) n2 (v2 : vector A n2),
    Vin x (Vapp v1 v2) -> Vin x v1 \/ Vin x v2.

  Proof.
    induction v1; intros; simpl in * . auto. destruct H. auto.
    assert (Vin x v1 \/ Vin x v2). apply IHv1. exact H. destruct H0; auto.
  Qed.

  Lemma Vin_elim : forall x n (v : vector A n), Vin x v ->
    exists n1 (v1 : vector A n1) n2 (v2 : vector A n2) (H : n1 + S n2 = n),
      v = Vcast (Vapp v1 (Vcons x v2)) H.

  Proof.
    induction v; simpl. contr.
    intro H. destruct H. clear IHv. subst x.
    ex 0 (@Vnil A) n. ex v (eq_refl (S n)). rewrite Vcast_refl. refl.
    assert (exists n1 (v1 : vector A n1) n2 (v2 : vector A n2)
      (H : n1 + S n2 = n), v = Vcast (Vapp v1 (Vcons x v2)) H). exact (IHv H).
    destruct H0 as [n1]. destruct H0 as [v1]. destruct H0 as [n2].
    destruct H0 as [v2].
    destruct H0 as [H1].
    exists (S n1). exists (Vcons h v1). exists n2. exists v2.
    exists (S_add_S H1). rewrite H0. clear H0. simpl.
    generalize (S_add_S H1); intros i; inversion i as [j].
    rewrite Vcast_cons. f_equal. apply Vcast_pi.
  Qed.

  Variable eq_dec : forall x y : A, {x=y}+{~x=y}.

  Lemma Vin_dec : forall x n (xs : vector A n), {Vin x xs}+{~Vin x xs}.

  Proof.
    intro x. induction xs; simpl. right. fo. destruct (eq_dec h x).
    left. fo. destruct IHxs. left. fo. right. fo.
  Qed.

End Vin.

Arguments Vin_nth [A n v a] _.
Arguments Vin_cast_elim [A m n H v x] _.
Arguments Vin_elim [A x n v] _.
Arguments Vin_app [A x n1 v1 n2 v2] _.

(***********************************************************************)
(** ** Sub-vector.

Given a vector [v] of size [n], two natural numbers [i] and [k] and a
proof [h] that [i+k<=n], then [Vsub v h] is the sub-vector of [v] of
size [k] made of the elements [v_i], ..., [v_{i+k-1}]. *)

Section Vsub.

  Variable A : Type.

  Lemma Vsub_aux1 : forall i k' n : nat, i + S k' <= n -> i < n.

  Proof. lia. Qed.

  Arguments Vsub_aux1 [i k' n] _.

  Lemma Vsub_aux2: forall i k' n : nat, i + S k' <= n -> S i + k' <= n.

  Proof. lia. Qed.

  Arguments Vsub_aux2 [i k' n] _.

  Fixpoint Vsub n (v : vector A n) i k : i+k<=n -> vector A k :=
    match k as k return i+k<=n -> vector A k with
      | 0 => fun _ => Vnil
      | S k' => fun h =>
        Vcons (Vnth v (Vsub_aux1 h)) (Vsub v (S i) k' (Vsub_aux2 h))
    end.

  Global Arguments Vsub [n] _ [i k] _.

  Lemma Vsub_nil_aux : forall i k (h:i+k<=0) (e : 0=k),
    Vsub Vnil h = Vcast Vnil e.

  Proof. destruct k; intros. rewrite Vcast_refl; refl. discr. Qed.

  Lemma Vsub_nil_aux1 : forall i k, i+k <= 0 -> 0=k.

  Proof. lia. Qed.

  Arguments Vsub_nil_aux1 [i k] _.

  Lemma Vsub_nil : forall i k (h:i+k<=0),
    Vsub Vnil h = Vcast Vnil (Vsub_nil_aux1 h).

  Proof. intros. apply Vsub_nil_aux. Qed.

  Lemma Vsub_eq_nil k n (v : vector A n) i (h : i+k <= n) (hk : k = 0) :
    Vsub v h = Vcast Vnil (eq_sym hk).

  Proof. subst k. rewrite Vcast_refl; refl. Qed.

  Lemma Vnth_sub_aux : forall n i k j, i+k<=n -> j<k -> i+j<n.

  Proof. lia. Qed.

  Arguments Vnth_sub_aux [n i k j] _ _.

  Lemma Vnth_sub : forall k n (v : vector A n) i (h : i+k<=n) j (p : j<k),
    Vnth (Vsub v h) p = Vnth v (Vnth_sub_aux h p).

  Proof.
    induction k; intros. lia. simpl. destruct j. apply Vnth_eq. lia.
    rewrite IHk. apply Vnth_eq. lia.
  Qed.

  Lemma Vsub_cons_aux : forall n i k, S i + k <= S n -> i + k <= n.

  Proof. lia. Qed.

  Lemma Vsub_cons : forall x i k n (v : vector A n) (h : S i + k <= S n),
    Vsub (Vcons x v) h = Vsub v (Vsub_cons_aux h).

  Proof.
    intros. apply Veq_nth; intros. rewrite !Vnth_sub. simpl.
    apply Vnth_eq. lia.
  Qed.

  Lemma Vsub_pi : forall n (v : vector A n) i k (h h' : i+k<=n),
    Vsub v h = Vsub v h'.

  Proof. intros. assert (h = h'). apply le_unique. subst. refl. Qed.

  Lemma Vsub_cast_aux : forall n (v : vector A n) n' (e : n=n') i k
    (h : i+k<=n') (h' : i+k<=n), Vsub (Vcast v e) h = Vsub v h'.

  Proof.
    destruct v; destruct n'; simpl; intros; try discr.
    rewrite Vcast_refl; apply Vsub_pi.
    inversion e; subst n'; rewrite Vcast_refl; apply Vsub_pi.
  Qed.

  Lemma Vsub_cast_aux1 : forall n n' i k, n=n' -> i+k<=n' -> i+k<=n.

  Proof. lia. Qed.

  Arguments Vsub_cast_aux1 [n n' i k] _ _.

  Lemma Vsub_cast : forall n (v : vector A n) n' (e : n=n') i k (h : i+k<=n')
    (h' : i+k<=n), Vsub (Vcast v e) h = Vsub v (Vsub_cast_aux1 e h).

  Proof. intros. apply Vsub_cast_aux. Qed.

  Lemma Vcast_sub_aux1 : forall n i k j, i + k <= n -> k = j -> i + j <= n.

  Proof. lia. Qed.

  Arguments Vcast_sub_aux1 [n i k j] _ _.

  Lemma Vcast_sub : forall n (v : vector A n) i k (h : i + k <= n) j
    (e : k = j), Vcast (Vsub v h) e = Vsub v (Vcast_sub_aux1 h e).

  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_cast, !Vnth_sub.
    apply Vnth_eq. auto.
  Qed.

  Lemma Vcons_nth_aux1 : forall n i k, i < n -> S i+k <= n -> i+S k <= n.

  Proof. lia. Qed.

  Lemma Vcons_nth : forall n (v : vector A n) i k (h1 : i<n)
    (h2 : S i + k <= n),
    Vcons (Vnth v h1) (Vsub v h2) = Vsub v (Vcons_nth_aux1 h1 h2).

  Proof.
    intros. apply Veq_nth; intros.
    destruct i0; simpl; repeat rewrite Vnth_sub; apply Vnth_eq; lia.
  Qed.

  Lemma Vsub_cons_intro_aux : forall n (v : vector A n) i k (h : i+k<=n)
    (h1 : i<n) (h2 : S i + pred k <= n) (e : S (pred k) = k),
    Vsub v h = Vcast (Vcons (Vnth v h1) (Vsub v h2)) e.

  Proof.
    intros. apply Veq_nth; intros. rewrite Vnth_cast.
    destruct i0; simpl; rewrite !Vnth_sub; apply Vnth_eq; lia.
  Qed.

  Lemma Vsub_cons_intro_aux1 : forall n i k, i+k<=n -> k>0 -> i<n.

  Proof. lia. Qed.

  Arguments Vsub_cons_intro_aux1 [n i k] _ _.

  Lemma Vsub_cons_intro_aux2 : forall n i k, i+k<=n -> k>0 -> S i+pred k <= n.

  Proof. lia. Qed.

  Arguments Vsub_cons_intro_aux2 [n i k] _ _.

  Lemma Vsub_cons_intro_aux3 : forall k, k>0 -> S(pred k) = k.

  Proof. lia. Qed.

  Lemma Vsub_cons_intro :  forall n (v : vector A n) i k (h : i+k<=n) (p : k>0),
    Vsub v h = Vcast (Vcons (Vnth v (Vsub_cons_intro_aux1 h p))
      (Vsub v (Vsub_cons_intro_aux2 h p))) (Vsub_cons_intro_aux3 p).

  Proof. intros. apply Vsub_cons_intro_aux. Qed.

  Lemma Veq_app_aux : forall n (v : vector A n) i
    (h1 : 0 + i <= n) (h2 : i + (n - i) <= n) (e : i + (n - i) = n),
    v = Vcast (Vapp (Vsub v h1) (Vsub v h2)) e.

  Proof.
    induction v; intros.
    (* Vnil *)
    apply Veq_nth; intros. lia.
    (* Vcons *)
    destruct i; simpl in *; [rewrite Vcast_refl | rewrite Vcast_cons];
      f_equal; rewrite !Vsub_cons.
    (* i = 0 *)
    apply Veq_nth; intros; rewrite Vnth_sub; apply Vnth_eq. refl.
    (* i > 0 *)
    apply IHv.
  Qed.

  Lemma Veq_app_aux1 : forall n i, i <= n -> 0 + i <= n.

  Proof. lia. Qed.

  Lemma Veq_app_aux2 : forall n i, i <= n -> i + (n - i) <= n.

  Proof. lia. Qed.

  Lemma Veq_app_aux3 : forall n i, i <= n -> i + (n - i) = n.

  Proof. lia. Qed.

  Lemma Veq_app : forall n (v : vector A n) i (h : i<=n),
    v = Vcast (Vapp (Vsub v (Veq_app_aux1 h)) (Vsub v (Veq_app_aux2 h)))
    (Veq_app_aux3 h).

  Proof. intros. apply Veq_app_aux. Qed.

  Lemma Veq_app_cons_aux : forall n (v : vector A n) i (h1 : 0 + i <= n)
    (h2 : i < n) (h3 : S i + (n - S i) <= n) (e : i + S (n - S i) = n),
    v = Vcast (Vapp (Vsub v h1) (Vcons (Vnth v h2) (Vsub v h3))) e.

  Proof.
    induction v; intros.
    (* Vnil *)
    apply Veq_nth; intros. lia.
    (* Vcons *)
    destruct i; simpl; rewrite Vcast_cons; f_equal; rewrite !Vsub_cons.
    (* i = 0 *)
    apply Veq_nth; intros. rewrite Vnth_cast, Vnth_sub.
    apply Vnth_eq. lia.
    (* i > 0 *)
    apply IHv.
  Qed.

  Lemma Veq_app_cons_aux1 : forall n i, i < n -> 0 + i <= n.

  Proof. lia. Qed.

  Lemma Veq_app_cons_aux2 : forall n i, i < n -> S i + (n - S i) <= n.

  Proof. lia. Qed.

  Lemma Veq_app_cons_aux3 : forall n i, i < n -> i + S (n - S i) = n.

  Proof. lia. Qed.

  Lemma Veq_app_cons : forall n (v : vector A n) i (h : i<n),
    v = Vcast (Vapp (Vsub v (Veq_app_cons_aux1 h))
      (Vcons (Vnth v h) (Vsub v (Veq_app_cons_aux2 h))))
    (Veq_app_cons_aux3 h).

  Proof. intros. apply Veq_app_cons_aux. Qed.

  Lemma Veq_sub_aux : forall n (v v' : vector A n) i (h1 : 0+i<=n)
    (h2 : i+(n-i)<=n),
    Vsub v h1 = Vsub v' h1 -> Vsub v h2 = Vsub v' h2 -> v = v'.

  Proof.
    intros. assert (e:i+(n-i)=n). lia.
    rewrite (Veq_app_aux v h1 h2 e), (Veq_app_aux v' h1 h2 e).
    apply Vcast_eq_intro. apply Vapp_eq_intro; hyp.
  Qed.

  Lemma Veq_sub : forall n (v v' : vector A n) i (h : i<=n),
    Vsub v (Veq_app_aux1 h) = Vsub v' (Veq_app_aux1 h) ->
    Vsub v (Veq_app_aux2 h) = Vsub v' (Veq_app_aux2 h) -> v = v'.

  Proof. intros. eapply Veq_sub_aux; ehyp. Qed.

  Lemma Veq_sub_cons_aux : forall n (v v' : vector A n) i (h1 : 0+i<=n)
    (h2 : i<n) (h3 : S i+(n-S i)<=n), Vsub v h1 = Vsub v' h1 ->
    Vnth v h2 = Vnth v' h2 -> Vsub v h3 = Vsub v' h3 -> v = v'.

  Proof.
    intros. assert (e:i+S(n-S i)=n). lia.
    rewrite (Veq_app_cons_aux v h1 h2 h3 e), (Veq_app_cons_aux v' h1 h2 h3 e).
    apply Vcast_eq_intro. apply Vapp_eq_intro. hyp. apply Vcons_eq_intro; hyp.
  Qed.

  Lemma Veq_sub_cons : forall n (v v' : vector A n) i (h : i<n),
    Vsub v (Veq_app_cons_aux1 h) = Vsub v' (Veq_app_cons_aux1 h) ->
    Vnth v h = Vnth v' h ->
    Vsub v (Veq_app_cons_aux2 h) = Vsub v' (Veq_app_cons_aux2 h) -> v = v'.

  Proof. intros. eapply Veq_sub_cons_aux; ehyp. Qed.

  Lemma Vsub_replace_l : forall n (v : vector A n) i (h : i<n) x j k
    (p : j+k<=n), j+k <= i -> Vsub (Vreplace v h x) p = Vsub v p.

  Proof.
    intros. apply Veq_nth; intros. rewrite !Vnth_sub, Vnth_replace_neq.
    2: lia. apply Vnth_eq. refl.
  Qed.

  Lemma Vsub_replace_r : forall n (v : vector A n) i (h : i<n) x j k
    (p : j+k<=n), j > i -> Vsub (Vreplace v h x) p = Vsub v p.

  Proof.
    intros. apply Veq_nth; intros. rewrite !Vnth_sub, Vnth_replace_neq.
    2: lia. apply Vnth_eq. refl.
  Qed.

  Lemma Vsub_app_l_aux : forall n1 n2 i, i <= n1 -> 0 + i <= n1 + n2.

  Proof. lia. Qed.

  Lemma Vsub_app_l : forall n1 (v1 : vector A n1) n2 (v2 : vector A n2)
    (h : 0+n1<=n1+n2), Vsub (Vapp v1 v2) h = v1.

  Proof.
    induction v1; simpl; intros. refl. apply Vtail_eq.
    rewrite Vsub_cons, IHv1. refl.
  Qed.

  Lemma Vsub_id : forall n (v : vector A n) (h:0+n<=n), Vsub v h = v.

  Proof.
    induction v; simpl; intros. refl. apply Vtail_eq.
    rewrite Vsub_cons, IHv. refl.
  Qed.

  Lemma Vsub_app_r : forall n1 (v1 : vector A n1) n2 (v2 : vector A n2)
    (h : n1+n2<=n1+n2), Vsub (Vapp v1 v2) h = v2.

  Proof.
    induction v1; simpl; intros. apply Vsub_id. rewrite Vsub_cons, IHv1. refl.
  Qed.

End Vsub.

Arguments Vsub [A n] _ [i k] _.
Arguments Vsub_pi [A n v i k h] _.

(***********************************************************************)
(** ** Function removing the last element of a non-empty vector. *)

Section Vremove_last.

  Variable A : Type.

  Lemma Vremove_last_aux : forall n, 0 + n <= S n.

  Proof. lia. Qed.

  Definition Vremove_last A n (v : vector A (S n)) : vector A n :=
    Vsub v (Vremove_last_aux n).

  Lemma Vnth_remove_last_intro : forall n (v : vector A (S n)) i
    (h1 : i<n) (h2 : i<S n), Vnth v h2 = Vnth (Vremove_last v) h1.

  Proof.
    intros n v i h1 h2. unfold Vremove_last. rewrite Vnth_sub. apply Vnth_eq.
    refl.
  Qed.

  Lemma Vnth_remove_last : forall n (v : vector A (S n)) i
    (h : i<n), Vnth (Vremove_last v) h = Vnth v (Nat.lt_lt_succ_r h).

  Proof. intros n v i h. sym. apply Vnth_remove_last_intro. Qed.

  Lemma Vremove_last_add : forall n (v : vector A n) x,
    Vremove_last (Vadd v x) = v.

  Proof.
    intros n v x. apply Veq_nth. intros i h.
    rewrite Vnth_remove_last, Vnth_add.
    destruct (eq_nat_dec i n). lia. apply Vnth_eq. refl.
  Qed.

End Vremove_last.

(***********************************************************************)
(** ** Last element of a vector with default value if empty. *)

Section Vlast.

  Variable A : Type.

  Fixpoint Vlast default n (v : vector A n) : A :=
    match v with
      | Vnil => default
      | Vcons x v' => Vlast x v'
    end.

  Lemma Vlast_eq : forall x y n (v : vector A (S n)), Vlast x v = Vlast y v.

  Proof. intros x y n v. VSntac v. simpl. refl. Qed.

  Lemma Vlast_nth : forall n (v : vector A (S n)) x (h : n < S n),
    Vlast x v = Vnth v h.

  Proof.
    induction n; intros v x h.
    VSntac v. simpl. generalize (Vtail v); intro w; VOtac. simpl. refl.
    VSntac v. simpl. apply IHn.
  Qed.

  Lemma Vlast_tail : forall n (v : vector A (S n)),
    Vlast (Vhead v) (Vtail v) = Vlast (Vhead v) v.

  Proof. intros n v. VSntac v. refl. Qed.

  Lemma VSn_add_default : forall x n (v : vector A (S n)),
    v = Vadd (Vremove_last v) (Vlast x v).

  Proof.
    intros x n v. apply Veq_nth. intros i h.
    destruct (lt_dec i n).
    rewrite Vnth_addl with (H2:=l), Vnth_remove_last. apply Vnth_eq. refl.
    rewrite Vnth_addr. 2: lia.
    assert (e : i=n). lia. subst i. rewrite Vlast_nth with (h:=h). refl.
  Qed.

  Lemma VSn_add : forall n (v : vector A (S n)),
    v = Vadd (Vremove_last v) (Vlast (Vhead v) v).

  Proof. intros n v. apply VSn_add_default. Qed.

End Vlast.

(***********************************************************************)
(** ** Function applying a function [f] on every element of a vector. *)

Section Vmap.

  Variables (A B : Type) (f : A->B).

  Fixpoint Vmap n (v : vector A n) : vector B n :=
    match v with
      | Vnil => Vnil
      | Vcons a v' => Vcons (f a) (Vmap v')
    end.

  Lemma Vnth_map : forall n (v : vector A n) i (H : i < n),
    Vnth (Vmap v) H = f (Vnth v H).

  Proof.
    intros n. elim n.
    intros v i H. exfalso. apply (Nat.nlt_0_r H).
    clear n. intros n Hrec v i. case i.
    intro. rewrite (VSn_eq v). simpl. refl.
    clear i. intros i Hi. rewrite (VSn_eq v). simpl.
    apply (Hrec (Vtail v) i (lt_S_n Hi)).
  Qed.

  Lemma Vin_map : forall x n (v : vector A n),
    Vin x (Vmap v) -> exists y, Vin y v /\ x = f y.

  Proof.
    induction v; simpl; intros. contr. destruct H. subst x. exists h.
    auto.
    assert (exists y, Vin y v /\ x = f y). apply IHv. hyp.
    destruct H0 as [y]. exists y. intuition.
  Qed.

  Lemma Vin_map_intro : forall x n (v : vector A n),
    Vin x v -> Vin (f x) (Vmap v).

  Proof.
    induction v; simpl; intros. contr. destruct H. subst x. auto.
    intuition.
  Qed.

  Lemma Vmap_app : forall n1 n2 (v1 : vector A n1) (v2 : vector A n2),
    Vmap (Vapp v1 v2) = Vapp (Vmap v1) (Vmap v2).

  Proof.
    intros; induction v1.
    simpl; auto.
    simpl. rewrite IHv1. refl.
  Qed.

  Lemma Vmap_cast : forall m n (H : m=n) (v : vector A m),
    Vmap (Vcast v H) = Vcast (Vmap v) H.

  Proof. intros until H. case H. intro v. rewrite !Vcast_refl. refl. Qed.

  Lemma Vmap_tail : forall n (v : vector A (S n)),
    Vmap (Vtail v) = Vtail (Vmap v).

  Proof. intros. VSntac v. refl. Qed.

  Lemma Vmap_eq_nth : forall n (v1 : vector A n) (v2 : vector B n),
    (forall i (h : i<n), f (Vnth v1 h) = Vnth v2 h) -> Vmap v1 = v2.

  Proof.
    induction n; simpl; intros. VOtac. refl.
    VSntac v1. VSntac v2. simpl. apply Vcons_eq_intro.
    rewrite !Vhead_nth. apply H.
    apply IHn. intros. rewrite !Vnth_tail. apply H.
  Qed.

End Vmap.

Arguments Vin_map [A B f x n v] _.
Arguments Vin_map_intro [A B f x n v] _.

Lemma Vmap_map : forall A B C (f:A->B) (g:B->C) n
  (v : vector A n), Vmap g (Vmap f v) = Vmap (fun x : A => g (f x)) v.

Proof.
  intros; induction v.
  simpl; refl.
  simpl Vmap at 2. simpl Vmap at 1.
  rewrite IHv. refl.
Qed.

(***********************************************************************)
(** ** Predicate saying that every element of a vector satisfies some predicate [P]. *)

Section Vforall.

  Variables (A : Type) (P : A -> Prop).

  Fixpoint Vforall n (v : vector A n) { struct v } : Prop :=
    match v with
      | Vnil => True
      | Vcons a w => P a /\ Vforall w
    end.

  Lemma Vforall_intro : forall n (v : vector A n),
    (forall x, Vin x v -> P x) -> Vforall v.

  Proof.
    induction v; simpl; intros. exact I. split.
    apply H. left. refl. apply IHv. intros. apply H. right. hyp.
  Qed.

  Lemma Vforall_nth_intro : forall n (v : vector A n),
    (forall i (ip : i < n), P (Vnth v ip)) -> Vforall v.

  Proof.
    intros. apply Vforall_intro. intros.
    destruct (Vin_nth H0) as [i [ip v_i]].
    rewrite <- v_i. apply H.
  Qed.

  Lemma Vforall_in : forall x n (v : vector A n), Vforall v -> Vin x v -> P x.

  Proof.
    induction v; simpl. contr. intros Ha Hv. destruct Ha. destruct Hv.
    rewrite <- H1. exact H. auto.
  Qed.

  Lemma Vforall_eq : forall n (v : vector A n),
    Vforall v <-> (forall x, Vin x v -> P x).

  Proof.
    split; intros. eapply Vforall_in. apply H. hyp. apply Vforall_intro. hyp.
  Qed.

  Lemma Vforall_nth : forall n (v : vector A n) i (ip : i < n), 
    Vforall v -> P (Vnth v ip).

  Proof. intros. apply Vforall_in with n v. hyp. apply Vnth_in. Qed.

  Lemma Vforall_incl : forall n1 (v1 : vector A n1) n2 (v2 : vector A n2),
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

  Lemma Vforall_app : forall p (v : vector A p) q (w : vector A q),
    Vforall (Vapp v w) <-> Vforall v /\ Vforall w.

  Proof. induction v; fo. Qed.

  (** Decidability of [Vforall]. *)

  Variable P_dec : forall x, {P x}+{~P x}.

  Lemma Vforall_dec : forall n (v : vector A n), {Vforall v}+{~Vforall v}.

  Proof.
    induction n; intros.
    VOtac. left. constructor.
    VSntac v. destruct (P_dec (Vhead v)).
    destruct (IHn (Vtail v)).
    left. simpl. split; hyp.
    right. intro V. destruct V. contr.
    right. intro V. destruct V. contr.
  Defined.

  Variables (f : A -> bool) (f_ok : forall x, f x = true <-> P x).

  Fixpoint bVforall n (v : vector A n) : bool :=
    match v with
      | Vnil => true
      | Vcons a w => f a && bVforall w
    end.

  Lemma bVforall_ok : forall n (v : vector A n),
    bVforall v = true <-> Vforall v.

  Proof. induction v; simpl. tauto. rewrite andb_eq, f_ok. tauto. Qed.

End Vforall.

Arguments Vforall_in [A P x n v] _ _.
Arguments Vforall_nth [A P n v i] _ _.

Lemma Vforall_impl : forall A (P Q : A -> Prop) n (v : vector A n),
  Vforall P v -> (forall x, Vin x v -> P x -> Q x) -> Vforall Q v.

Proof.
  intros. apply Vforall_intro. intros. apply H0. hyp.
  eapply Vforall_in with (n := n). apply H. apply H1.
Qed.

Lemma Vforall_map_elim : forall A B (f: A->B) (P : B->Prop) n (v : vector A n),
    Vforall P (Vmap f v) -> Vforall (fun a : A => P (f a)) v.

Proof. induction v; simpl; intuition. Qed.

Arguments Vforall_map_elim [A B f P n v] _.

Lemma Vforall_map_intro : forall A B (f: A->B) (P : B->Prop) n (v : vector A n),
  Vforall (fun a : A => P (f a)) v -> Vforall P (Vmap f v).

Proof. induction v; simpl; intuition. Qed.

(***********************************************************************)
(** ** Equality of [Vmap]'s. *)

Lemma Vmap_eq : forall (A B : Type) (f g : A->B) n (v : vector A n),
  Vforall (fun a => f a = g a) v -> Vmap f v = Vmap g v.

Proof.
  induction v; simpl; intros. refl. destruct H. apply Vcons_eq_intro; auto.
Qed.

Arguments Vmap_eq [A B f g n v] _.

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
(** ** Predicate saying that the elements of two vectors are pairwise in relation. *)

Section Vforall2.

  Variables (A B : Type) (R : A -> B -> Prop).

  Fixpoint Vforall2_aux n1 n2 (v1 : vector A n1) (v2 : vector B n2) : Prop :=
    match v1, v2 with
      | Vnil, Vnil => True
      | Vcons a v, Vcons b w => R a b /\ Vforall2_aux v w
      | _, _ => False
    end.

  Definition Vforall2 n (v1 : vector A n) (v2 : vector B n) :=
    Vforall2_aux v1 v2.

  Lemma Vforall2_tail : forall n (v1 : vector A (S n)) (v2 : vector B (S n)),
    Vforall2 v1 v2 -> Vforall2 (Vtail v1) (Vtail v2).

  Proof.
    intros. revert H. VSntac v1. VSntac v2. unfold Vforall2. simpl. tauto.
  Qed.

  Lemma Vforall2_elim_nth : forall n (v1 : vector A n) (v2 : vector B n) i 
    (ip : i < n), Vforall2 v1 v2 -> R (Vnth v1 ip) (Vnth v2 ip).

  Proof.
    induction v1; intros. absurd (i<0); lia. revert H. VSntac v2.
    unfold Vforall2. destruct i; simpl. tauto. intuition.
  Qed.

  Lemma Vforall2_intro_nth : forall n (v1 : vector A n) (v2 : vector B n),
    (forall i (ip : i < n), R (Vnth v1 ip) (Vnth v2 ip)) -> Vforall2 v1 v2.

  Proof.
    unfold Vforall2. induction v1; intros. VOtac. simpl. auto.
    revert H. VSntac v2. intro. split. apply (H0 0 (Nat.lt_0_succ _)).
    apply IHv1. intros. assert (S i< S n). lia. ded (H0 _ H1). simpl in H2.
    assert (ip = lt_S_n H1). apply lt_unique. rewrite H3. hyp.
  Qed.

  Lemma Vforall2_cons_eq : forall u v n (us : vector A n) (vs : vector B n),
    Vforall2 (Vcons u us) (Vcons v vs) <-> R u v /\ Vforall2 us vs.

  Proof. fo. Qed.

  Lemma Vforall2_cons_elim : forall n (u : vector A n) (v : vector B n) x y,
    Vforall2 (Vcons x u) (Vcons y v) -> Vforall2 u v.

  Proof. fo. Qed.

  Lemma Vforall2_app_elim_l n1 (v1 : vector A n1) (v1' : vector B n1)
    n2 (v2 : vector A n2) (v2' : vector B n2) :
    Vforall2 (Vapp v1 v2) (Vapp v1' v2') -> Vforall2 v1 v1'.

  Proof.
    intro h. apply Vforall2_intro_nth. intros i hi.
    assert (hi' : i < n1+n2). lia.
    assert (a1 : Vnth v1 hi = Vnth (Vapp v1 v2) hi').
    rewrite Vnth_app. destruct (Compare_dec.le_gt_dec n1 i).
    lia. apply Vnth_eq. refl.
    assert (a2 : Vnth v1' hi = Vnth (Vapp v1' v2') hi').
    rewrite Vnth_app. destruct (Compare_dec.le_gt_dec n1 i).
    lia. apply Vnth_eq. refl.
    rewrite a1, a2. apply Vforall2_elim_nth. hyp.
  Qed.

  Lemma Vforall2_app_elim_r n1 (v1 : vector A n1) (v1' : vector B n1)
    n2 (v2 : vector A n2) (v2' : vector B n2) :
    Vforall2 (Vapp v1 v2) (Vapp v1' v2') -> Vforall2 v2 v2'.

  Proof.
    intro h. apply Vforall2_intro_nth. intros i hi.
    assert (hi' : n1+i < n1+n2). lia.
    assert (a1 : Vnth v2 hi = Vnth (Vapp v1 v2) hi').
    rewrite Vnth_app. destruct (Compare_dec.le_gt_dec n1 (n1+i)).
    apply Vnth_eq. lia. lia.
    assert (a2 : Vnth v2' hi = Vnth (Vapp v1' v2') hi').
    rewrite Vnth_app. destruct (Compare_dec.le_gt_dec n1 (n1+i)).
    apply Vnth_eq. lia. lia.
    rewrite a1, a2. apply Vforall2_elim_nth. hyp.
  Qed.

  Lemma Vforall2_cast n (u : vector A n) (v : vector B n) n' (h h' : n=n') :
    Vforall2 (Vcast u h) (Vcast v h') <-> Vforall2 u v.

  Proof. subst n'. rewrite !Vcast_refl. refl. Qed.

  Lemma Vforall2_sub : forall n (v1 : vector A n) (v2 : vector B n)
    p q (h : p+q<=n), Vforall2 v1 v2 -> Vforall2 (Vsub v1 h) (Vsub v2 h).

  Proof.
    intros n v1 v2 p q h e. apply Vforall2_intro_nth; intros i hi.
    rewrite !Vnth_sub. apply Vforall2_elim_nth. hyp.
  Qed.

(** Decidability of [Vforall2]. *)

  Variable R_dec : forall x y, {R x y}+{~R x y}.

  Lemma Vforall2_aux_dec : forall n1 (v1 : vector A n1) n2 (v2 : vector B n2), 
    {Vforall2_aux v1 v2} + {~Vforall2_aux v1 v2}.

  Proof.
    induction v1; destruct v2; simpl; auto.
    destruct (IHv1 n0 v2); intuition.
    destruct (R_dec h h0); intuition.
  Defined.

  Lemma Vforall2_dec n (v : vector A n) (w : vector B n) :
   {Vforall2 v w}+{~Vforall2 v w}.

  Proof. unfold Vforall2. apply Vforall2_aux_dec. Defined.

  Variables (f : A -> B -> bool) (f_ok : forall x y, f x y = true <-> R x y).

  Fixpoint bVforall2_aux n1 n2 (v1 : vector A n1) (v2 : vector B n2) : bool :=
    match v1, v2 with
      | Vnil, Vnil => true
      | Vcons x xs, Vcons y ys => f x y && bVforall2_aux xs ys
      | _, _ => false
    end.

  Lemma bVforall2_aux_ok : forall n1 (v1 : vector A n1) n2 (v2 : vector B n2),
    bVforall2_aux v1 v2 = true <-> Vforall2_aux v1 v2.

  Proof.
    induction v1; simpl; intros.
    destruct v2. intuition. intuition.
    destruct v2. intuition.
    rewrite andb_eq, f_ok, IHv1. tauto.
  Qed.

  Definition bVforall2 n (v1 : vector A n) (v2 : vector B n) :=
    bVforall2_aux v1 v2.

  Lemma bVforall2_ok : forall n (v1 : vector A n) (v2 : vector B n),
    bVforall2 v1 v2 = true <-> Vforall2 v1 v2.

  Proof.
    intros n v1 v2. intuition.
    (* <- *)
    unfold Vforall2. apply bVforall2_aux_ok.
    unfold bVforall2 in H. hyp.
    (* -> *)
    unfold bVforall2. apply bVforall2_aux_ok.
    unfold Vforall2 in H.
    hyp.
  Qed.

End Vforall2.

Arguments Vforall2 [A B] R {n} _ _.
Arguments Vforall2_sub [A B R n v1 v2 p q] _ _.
Arguments Vforall2_elim_nth [A B R n v1 v2 i] _ _.
Arguments Vforall2_dec [A B R] _ [n] _ _.

(** Properties of [Vforall2] wrt relations. *)

Section Vforall2_rel.

  Variables (A : Type) (R : relation A).

  Global Instance Vforall2_refl :
    Reflexive R -> forall n, Reflexive (Vforall2 (n:=n) R).

  Proof. intros h n x. apply Vforall2_intro_nth. refl. Qed.

  Global Instance Vforall2_trans :
    Transitive R -> forall n, Transitive (Vforall2 (n:=n) R).

  Proof.
    intros h n x y z xy yz. apply Vforall2_intro_nth. intros i ip.
    trans (Vnth y ip); apply Vforall2_elim_nth; hyp.
  Qed.

  Global Instance Vforall2_sym :
    Symmetric R -> forall n, Symmetric (Vforall2 (n:=n) R).

  Proof.
    intros h n x y xy. apply Vforall2_intro_nth. intros i ip. sym.
    apply Vforall2_elim_nth. hyp.
  Qed.

  Global Instance Vforall2_equiv :
    Equivalence R -> forall n, Equivalence (Vforall2 (n:=n) R).

  Proof.
    constructor. apply Vforall2_refl; class. apply Vforall2_sym; class.
    apply Vforall2_trans; class.
  Qed.

End Vforall2_rel.

Section Vforall2_aux_Proper.

  Variables (A : Type) (R : relation A) (B : Type) (S : relation B)
            (F : A -> B -> Prop) (F_R : Proper (R ==> S ==> iff) F).

  Global Instance Vforall2_aux_Proper n1 n2 :
    Proper (Vforall2 R ==> Vforall2 S ==> iff)
           (Vforall2_aux F (n1:=n1) (n2:=n2)).

  Proof.
    intros u u' uu' v v' vv'; revert n1 u u' uu' n2 v v' vv'.
    induction u; simpl; intros. VOtac. simpl.
    destruct v. VOtac. tauto. VSntac v'. tauto.
    revert uu'. VSntac u'. simpl. destruct v'. VOtac. tauto.
    revert vv'. VSntac v. rewrite !Vforall2_cons_eq.
    intros [h1 h2] [h3 h4]. rewrite <- (F_R h3 h1), (IHu _ h4 _ _ _ h2). tauto.
  Qed.

End Vforall2_aux_Proper.

(** Properties of [Vforall2] wrt [Vmap]. *)

Section Vforall2_map.

  Variables (A : Type) (R : relation A) (B : Type) (S : relation B)
            (f g : A -> B).

  Lemma Vforall2_map_intro : forall n (v : vector A n),
    Vforall (fun x => S (f x) (g x)) v -> Vforall2 S (Vmap f v) (Vmap g v).

  Proof.
    induction v; simpl; intros. refl. rewrite Vforall2_cons_eq. intuition.
  Qed.

End Vforall2_map.

(***********************************************************************)
(** ** Predicate saying that some element of a vector satisfies some predicate [P]. *)

Section Vexists.

  Variables (A : Type) (P : A->Prop).

  Fixpoint Vexists n (v : vector A n) : Prop :=
    match v with
      | Vnil => False
      | Vcons a v' => P a \/ Vexists v'
    end.

  Lemma Vexists_eq : forall n (v : vector A n),
    Vexists v <-> exists x, Vin x v /\ P x.

  Proof.
    induction v; simpl; intuition. destruct H. intuition. exists h. intuition.
    destruct H1. exists x. intuition. destruct H1. intuition. subst. auto.
    right. apply H0. exists x. intuition.
  Qed.

  Variable f : A->bool.

  Fixpoint bVexists n (v : vector A n) : bool :=
    match v with
      | Vnil => false
      | Vcons a v' => f a || bVexists v'
    end.

  Lemma bVexists_ok_Vin : forall n (v : vector A n),
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

  Lemma bVexists_ok : forall n (v : vector A n),
    bVexists v = true <-> Vexists v.

  Proof.
    intros. rewrite bVexists_ok_Vin. tauto. intros. rewrite f_ok. tauto.
  Qed.

End Vexists.

(***********************************************************************)
(** ** Build a vector of size [n] from a function [gen: forall i, i<n -> A].*)

Section Vbuild.

  Variable A : Type.

  Fixpoint Vbuild n : (forall i, i<n -> A) -> vector A n :=
    match n as n return (forall i, i<n -> A) -> vector A n with
    | 0 => fun _ => Vnil
    | S p => fun gen => Vcons (gen 0 (Nat.lt_0_succ p))
                              (Vbuild (fun i ip => gen (S i) (lt_n_S ip)))
    end.

  Lemma Vbuild_nth :
    forall n gen i (ip : i < n), Vnth (Vbuild gen) ip = gen i ip.

  Proof.
    induction n; intros gen i ip.
    (* case n = 0 *)
    lia.
    (* case n = S p *)
    destruct i; simpl.
    (* case i = 0 *)
    f_equal. apply lt_unique.
    (* case i > 0 *)
    rewrite IHn. f_equal. apply lt_unique.
  Qed.

  Lemma Vbuild_in n gen x :
    Vin x (Vbuild gen) ->  exists i, exists ip : i < n, x = gen i ip.

  Proof.
    intro hx. apply Vin_nth in hx. destruct hx as [i [i_n hi]]. ex i i_n.
    rewrite <- Vbuild_nth. auto.
  Qed.

  Lemma Vbuild_head : forall n (gen : forall i, i < S n -> A),
    Vhead (Vbuild gen) = gen 0 (Nat.lt_0_succ n).

  Proof. intros n gen. rewrite Vhead_nth, Vbuild_nth. refl. Qed.

  Lemma Vbuild_tail n (gen : forall i, i < S n -> A) :
    Vtail (Vbuild gen) = Vbuild (fun i ip => gen (S i) (lt_n_S ip)).

  Proof. apply Veq_nth; intros. rewrite Vnth_tail, !Vbuild_nth. refl. Qed.

  Lemma Vin_build : forall n (gen : forall i, i < n -> A) x,
    (exists i (ip : i < n), x = gen i ip) -> Vin x (Vbuild gen).

  Proof.
    intros n gen x [i [i_n hi]]. subst x. rewrite <- Vbuild_nth. apply Vnth_in.
  Qed.

End Vbuild.

(***********************************************************************)
(** ** Iterators on vectors. *)

(** Vfold_left f a [b1 .. bn] = f .. (f (f a b1) b2) .. bn. *)

Section Vfold_left.

  Variables (A B : Type) (f : A->B->A).

  Fixpoint Vfold_left n (a:A) (v : vector B n) : A :=
    match v with
      | Vnil => a
      | Vcons b w => Vfold_left (f a b) w
    end.

  Global Instance Vfold_left_Vforall2 n (R : rel A) (S : rel B) :
    Proper (R ==> S ==> R) f
    -> Proper (R ==> Vforall2 S ==> R) (Vfold_left (n:=n)).

  Proof.
    intros hf a a' aa' v v' vv'. revert a a' aa'. induction v; simpl; intros.
    VOtac. hyp.
    revert vv'. VSntac v'. rewrite Vforall2_cons_eq. intros [h1 h2]. simpl.
    apply IHv. hyp. apply hf; hyp.
  Qed.

End Vfold_left.

(** Vfold_right f [a1 .. an] b = f a1 (f a2 .. (f an b) .. ). *)

Fixpoint Vfold_right (A B : Type) (f : A->B->B) n (v : vector A n) (b:B) : B :=
  match v with
    | Vnil => b
    | Vcons a w => f a (Vfold_right f w b)
  end.

(** Vfold_left_rev f a [b1 .. bn] = f .. (f (f a bn) bn-1) .. b1. *)

Section Vfold_left_rev.

  Variables (A B : Type) (f : A->B->A).

  Fixpoint Vfold_left_rev n (a:A) (v : vector B n) : A :=
    match v with
      | Vnil => a
      | Vcons b w => f (Vfold_left_rev a w) b
    end.

  Variables (R : relation A) (S : relation B) (f_S : Proper (R ==> S ==> R) f).

  Global Instance Vfold_left_rev_Vforall2 n :
    Proper (R ==> Vforall2 S ==> R) (Vfold_left_rev (n:=n)).

  Proof.
    intros a a' aa' v v' vv'. induction v; simpl; intros. VOtac. simpl. hyp.
    revert vv'. VSntac v'. rewrite Vforall2_cons_eq. intuition. simpl.
    apply f_S; try hyp. apply IHv; hyp.
  Qed.

End Vfold_left_rev.

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
      | Vcons xA sA, Vcons xB sB =>
        match Vfold2 sA sB with
          | Some v => F xA xB v
          | None   => None
        end
      | Vnil, Vcons _ _ => None
      | Vcons _ _, Vnil => None
    end.

End FoldOpt2.

(***********************************************************************)
(** ** Convert a vector into a list of the same length. *)

Section vec_of_list.

  Variable A : Type.

  Fixpoint vec_of_list (l : list A) : vector A (length l) :=
    match l with
      | nil => Vnil
      | cons x m => Vcons x (vec_of_list m)
    end.

  Lemma vec_of_list_cons : forall a l,
    vec_of_list (a :: l) = Vcons a (vec_of_list l).

  Proof. auto. Qed.

  Fixpoint list_of_vec n (v : vector A n) : list A :=
    match v with
      | Vnil => nil
      | Vcons x v => x :: list_of_vec v
    end.

  Lemma in_list_of_vec : forall n (v : vector A n) x,
    In x (list_of_vec v) -> Vin x v.

  Proof. induction v; simpl; intros. hyp. destruct H; auto. Qed.

  Lemma list_of_vec_in : forall n (v : vector A n) x,
    Vin x v -> In x (list_of_vec v).

  Proof.
    induction v; auto. intros. destruct H; simpl. auto. right. apply IHv. hyp.
  Qed.

  Lemma Vin_vec_of_list : forall l x, In x l <-> Vin x (vec_of_list l).

  Proof. induction l; simpl; intros. tauto. rewrite (IHl x). tauto. Qed.

  Lemma Vnth_vec_of_list : forall l d i (Hi : i < length l),
    Vnth (vec_of_list l) Hi = nth i l d.

  Proof.
    induction l. simpl. intros. lia.
    intros. rewrite vec_of_list_cons. destruct i; simpl; auto.
  Qed.

  Lemma vec_of_list_exact : forall i l (Hi : i < length(l)),
    element_at l i = Some (Vnth (vec_of_list l) Hi).

  Proof.
    induction i; intros.
    destruct l; simpl in *. contradict Hi; lia. auto.
    destruct l; simpl in *. contradict Hi; lia. apply IHi.
  Qed.

  Lemma list_of_vec_exact : forall i n (v : vector A n) (Hi : i < n),
    element_at (list_of_vec v) i = Some (Vnth v Hi).

  Proof.
    induction i; intros.
    destruct v; simpl in *. contradict Hi; lia. auto.
    destruct v; simpl in *. contradict Hi; lia. apply IHi.
  Qed.

End vec_of_list.

Arguments in_list_of_vec [A n v x] _.

(** Equivalence between [Vforall] and [lforall]. *)

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
(** ** Convert a list into a vector of options of fixed length. *)

Fixpoint vec_opt_of_list A m (l : list A) : vector (option A) m :=
  match m with
  | 0 => Vnil
  | S m' =>
    match l with
    | nil => Vconst None (S m')
    | cons x l' => Vcons (Some x) (vec_opt_of_list m' l')
    end
  end.

Lemma Vnth_vec_opt_of_list A : forall i m (l : list A) (im : i < m)
  (il : i < length l), Vnth (vec_opt_of_list m l) im = Some (ith il).

Proof.
  induction i.
  destruct m. lia. destruct l. simpl; lia. refl.
  destruct m. lia. destruct l. simpl; lia.
  simpl. intros im il. erewrite IHi. refl.
Qed.

(***********************************************************************)
(** ** Leibniz equality on [vector A n] is decidable if Leibniz equality on [A] is decidable. *)

Section eq_dec.

  Variables (A : Type) (eq_dec : forall x y : A, {x=y}+{~x=y}).

  Lemma eq_vec_dec : forall n (v1 v2 : vector A n), {v1=v2}+{~v1=v2}.

  Proof.
    induction v1; intro. VOtac. auto. VSntac v2.
    case (eq_dec h (Vhead v2)); intro.
    rewrite e. case (IHv1 (Vtail v2)); intro. rewrite e0. auto.
    right. unfold not. intro. Veqtac. auto.
    right. unfold not. intro. Veqtac. auto.
  Defined.

End eq_dec.

(***********************************************************************)
(** ** Boolean function for testing the equality of two vectors. *)

Section beq.

  Variables (A : Type) (beq : A -> A -> bool)
    (beq_ok : forall x y, beq x y = true <-> x = y).

  Fixpoint beq_vec n (v : vector A n) p (w : vector A p) :=
    match v, w with
      | Vnil, Vnil => true
      | Vcons x v', Vcons y w' => beq x y && beq_vec v' w'
      | _, _ => false
    end.

  Lemma beq_vec_refl : forall n (v : vector A n), beq_vec v v = true.

  Proof.
    induction v; simpl. refl.
    apply andb_intro. apply (beq_refl beq_ok). exact IHv.
  Qed.

  Lemma beq_vec_ok_length : forall n (v : vector A n) p (w : vector A p),
    beq_vec v w = true -> n = p.

  Proof.
    induction v; destruct w; simpl; intros; try (refl || discr).
    destruct (andb_elim H). ded (IHv _ _ H1). subst n0. refl.
  Qed.

  Arguments beq_vec_ok_length [n v p w] _.

  Lemma beq_vec_ok1_cast : forall n (v : vector A n) p (w : vector A p)
    (leq : n = p), beq_vec v w = true -> Vcast v leq = w.

  Proof.
    induction v; destruct w; simpl; intros; try discr.
    rewrite Vcast_refl; refl.
    destruct (andb_elim H). rewrite beq_ok in H0. subst h0.
    rewrite Vcast_cons; simpl. f_equal; apply IHv. hyp.
  Qed.

  Lemma beq_vec_ok1 n (v w : vector A n) : beq_vec v w = true -> v = w.

  Proof.
    intro. rewrite <- (Vcast_refl v (eq_refl n)). apply beq_vec_ok1_cast.
    hyp.
  Qed.

  Lemma beq_vec_ok2 : forall n (v w : vector A n), v = w -> beq_vec v w = true.

  Proof.
    induction v; intros. VOtac. refl. VSntac w. rewrite H0 in H. Veqtac.
    subst h. subst v. simpl. rewrite (beq_refl beq_ok). simpl.
    apply beq_vec_refl.
  Qed.

  Lemma beq_vec_ok : forall n (v w : vector A n), beq_vec v w = true <-> v = w.

  Proof. split; intro. apply beq_vec_ok1. hyp. apply beq_vec_ok2. hyp. Qed.

End beq.

Arguments beq_vec_ok_length _ _ [n v p w] _.

Section beq_in.

  Variables (A : Type) (beq : A -> A -> bool).

  Lemma beq_vec_ok_in1 : forall n (v : vector A n)
    (hyp : forall x, Vin x v -> forall y, beq x y = true <-> x = y)
    p (w : vector A p) (h : beq_vec beq v w = true),
    Vcast v (beq_vec_ok_length A beq h) = w.

  Proof.
    induction v; destruct w; intro; try discr.
    rewrite Vcast_refl; refl.
    generalize (beq_vec_ok_length A beq h1); intros e.
    simpl in h1; destruct (andb_elim h1).
    assert (ha : Vin h (Vcons h v)). simpl. auto.
    ded (hyp _ ha h0). rewrite H1 in H. subst h0. rewrite Vcast_cons.
    assert (hyp' : forall x, Vin x v -> forall y, beq x y = true <-> x=y).
    intros x hx. apply hyp. simpl. auto.
    destruct (andb_elim h1). ded (IHv hyp' _ w H2). rewrite <- H3.
    f_equal; apply Vcast_pi.
  Qed.

  Lemma beq_vec_ok_in2 : forall n (v : vector A n)
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

Arguments beq_vec_ok_in1 [A beq n v] _ [p w] _.
Arguments beq_vec_ok_in2 [A beq n v] _ [w] _.

(***********************************************************************)
(** ** Function applying a function [f] on the first element of a non-empty vector, or some default value if the vector is empty. *)

Section map_first.

  Variables (A B : Type) (default : B) (f : A->B).

  Definition Vmap_first n (v : vector A n) : B :=
    match v with
      | Vcons a _ => f a
      | _ => default
    end.

  Lemma Vmap_first_cast : forall n (v : vector A n) n' (h : n=n'),
    Vmap_first (Vcast v h) = Vmap_first v.

  Proof.
    destruct v; intros; destruct n'; try discr.
    rewrite Vcast_refl. refl.
    inversion h0. subst n'. rewrite Vcast_refl. refl.
  Qed.

End map_first.

(***********************************************************************)
(** ** Binary map function on vectors. *)

Section Vmap2.

  Variables (A B C : Type) (f: A->B->C).

  Fixpoint Vmap2 n : vector A n -> vector B n -> vector C n :=
    match n with
      | O => fun _ _ => Vnil
      | _ => fun v1 v2 =>
        Vcons (f (Vhead v1) (Vhead v2)) (Vmap2 (Vtail v1) (Vtail v2))
    end.

  Lemma Vnth_map2 : forall n (vl : vector A n) (vr : vector B n) i (ip : i < n),
    Vnth (Vmap2 vl vr) ip = f (Vnth vl ip) (Vnth vr ip).

  Proof.
    induction n; intros.
    VOtac. lia.
    VSntac vl. VSntac vr. destruct i. refl. 
    simpl. apply IHn.
  Qed.

  Variables (R : relation A) (S : relation B) (T : relation C)
            (f_mor : Proper (R ==> S ==> T) f).

  Global Instance Vmap2_proper n :
    Proper (Vforall2 R ==> Vforall2 S ==> Vforall2 T) (Vmap2 (n:=n)).

  Proof.
    intros u u' uu' v v' vv'; revert u u' uu' v v' vv'.
    induction u; simpl; intros. refl.
    revert uu'. VSntac u'. revert vv'. VSntac v. VSntac v'. simpl.
    rewrite !Vforall2_cons_eq. fo.
  Qed.

End Vmap2.

(***********************************************************************)
(** ** Vectors of [sig P]. *)

Section Vsig.

  Variables (A : Type) (P : A -> Prop).

  Fixpoint Vsig_of_forall n (v : vector A n) :
    Vforall P v -> vector (sig P) n :=
    match v in vector _ n return Vforall P v -> vector (sig P) n with
      | Vnil => fun _ => Vnil
      | Vcons a w => fun H =>
        Vcons (exist (proj1 H)) (Vsig_of_forall w (proj2 H))
    end.

  Fixpoint Vforall_of_sig (A : Type) (P : A -> Prop) n (v : vector (sig P) n) :
    Vforall P (Vmap (@proj1_sig A P) v) :=
    match v in vector _ n return Vforall P (Vmap (@proj1_sig A P) v) with
      | Vnil => I
      | Vcons a w => conj (@proj2_sig A P a) (Vforall_of_sig w)
    end.

  Lemma Vmap_proj1_sig : forall n (v : vector A n)
    (Hv : Vforall P v), v = Vmap (@proj1_sig A P) (Vsig_of_forall _ Hv).

  Proof.
    intros n v. elim v.
    simpl. intro. refl.
    intros a p w. intro Hrec.
    simpl. intro Hv. case Hv. intros H1 H2. simpl Vmap.
    gen (Hrec H2). intro H. apply Vcons_eq_intro; auto.
  Qed.

End Vsig.

Arguments Vsig_of_forall [A P n v] _.
Arguments Vmap_proj1_sig [A P n v] _.

(****************************************************************************)
(** ** Build a vector of [option A] of size [n] from the elements
(if they exist) of an arbitrary vector [xs] of size [p] whose positions
are given by a vector [ks] of natural numbers of size [n]. *)

Section Vopt_filter.

  Variable (A : Type).

  Fixpoint Vopt_filter n (ks : vector nat n) p (xs : vector A p) :=
    match ks in vector _ n return vector (option A) n with
      | Vnil => Vnil
      | Vcons k ks' =>
        Vcons (match lt_dec k p with left h => Some (Vnth xs h) | _ => None end)
          (Vopt_filter ks' xs)
    end.

  Lemma Vnth_opt_filter :
    forall p (xs : vector A p) n (ks : vector nat n) i (hi : i<n),
      Vnth (Vopt_filter ks xs) hi =
      match lt_dec (Vnth ks hi) p with
        | left h => Some (Vnth xs h)
        | _ => None
      end.

  Proof.
    intros p xs. induction ks; intros i hi. lia. simpl. destruct i as [|i].
    destruct (lt_dec h p); refl. apply IHks.
  Qed.

  Lemma Vnth_opt_filter_Some_elim :
    forall p (xs : vector A p) n (ks : vector nat n) i (hi : i<n) x,
      Vnth (Vopt_filter ks xs) hi = Some x ->
      exists h : Vnth ks hi < p, x = Vnth xs h.

  Proof.
    intros p xs. induction ks; intros i hi x. lia. rename h into k.
    simpl. destruct i as [|i]. 2: fo.
    destruct (lt_dec k p). 2: discr. intro hx; inversion hx. exists l. refl.
  Qed.

  Lemma Vnth_opt_filter_Some_intro : forall p (xs : vector A p)
    n (ks : vector nat n) i (hi : i<n) (h : Vnth ks hi < p),
    Vnth (Vopt_filter ks xs) hi = Some (Vnth xs h).

  Proof.
    intros p xs. induction ks; intros i hi. exfalso. lia. rename h into k.
    simpl. destruct i as [|i]; intro hj. 2: fo.
    destruct (lt_dec k p). 2: lia. f_equal. apply Vnth_eq. refl.
  Qed.

  Lemma Vopt_filter_cast p (xs : vector A p) p' (h : p = p') :
    forall n (ks : vector nat n),
      Vopt_filter ks (Vcast xs h) = Vopt_filter ks xs.

  Proof. subst p'. rewrite Vcast_refl. refl. Qed.

  Lemma Vopt_filter_app p (xs : vector A p) q (ys : vector A q) x :
    forall n (ks : vector nat n) i (hi : i < n),
      Vnth (Vopt_filter ks xs) hi = Some x ->
      Vnth (Vopt_filter ks (Vapp xs ys)) hi = Some x.

  Proof.
    induction ks; simpl; intros i hi. fo. destruct i.
    destruct (lt_dec h p); destruct (lt_dec h (p+q)); try (discr||lia).
    rewrite Vnth_app. destruct (le_gt_dec p h). lia.
    rewrite Vnth_eq with (h2:=g); auto.
    apply IHks.
  Qed.

  Global Instance Vopt_filter_proper R n (ks : vector nat n) p :
    Proper (Vforall2 R ==> Vforall2 (opt_r R)) (Vopt_filter ks (p:=p)).

  Proof.
    intros ts ts' tsts'. apply Vforall2_intro_nth. intros i hi.
    rewrite !Vnth_opt_filter. destruct (lt_dec (Vnth ks hi)).
    apply opt_r_Some. apply Vforall2_elim_nth. hyp. apply opt_r_None.
  Qed.

End Vopt_filter.

Arguments Vnth_opt_filter_Some_elim [A p xs n ks i hi x] _.

(** Relation between [Vopt_filter] and [Vmap]. *)

Section Vopt_filter_map.

  Variables (A B : Type) (f : A -> B).

  Definition fopt x :=
    match x with
      | Some v => Some (f v)
      | None => None
    end.

  Lemma Vopt_filter_map : forall p (xs : vector A p) n (ks : vector nat n),
    Vopt_filter ks (Vmap f xs) = Vmap fopt (Vopt_filter ks xs).

  Proof.
    intros p xs. induction ks as [|k ks]; simpl. refl.
    rewrite IHks. destruct (lt_dec k p). rewrite Vnth_map. refl. refl.
  Qed.

End Vopt_filter_map.

(** Properties of sorted filters. *)

Definition sorted n (ks : vector nat n) :=
  forall i (hi : i < n) j (hj : j < n), i < j -> Vnth ks hi < Vnth ks hj.

Lemma sorted_cons_elim n k (ks : vector nat n) :
  sorted (Vcons k ks) -> sorted ks.

Proof.
  intros h i hi j hj ij. gen (h _ (lt_n_S hi) _ (lt_n_S hj) (lt_n_S ij)).
  rewrite !Vnth_cons.
  destruct (lt_ge_dec 0 (S i)); destruct (lt_ge_dec 0 (S j)); try lia.
  rewrite Vnth_eq with (h2:=hi),
    Vnth_eq with (h1 := Vnth_cons_tail_aux (lt_n_S hj) l0) (h2:=hj); lia.
Qed.

Lemma Vnth_opt_filter_sorted_None A p (ts : vector A p) :
  forall n (ks : vector nat n), sorted ks ->
    forall i (hi : i < n), Vnth (Vopt_filter ks ts) hi = None ->
      forall j (hj : j < n), i < j -> Vnth (Vopt_filter ks ts) hj = None.

Proof.
  induction ks as [|k n ks]; intros hks i i1 i2 j j1 ij. lia.
  gen (sorted_cons_elim hks); intro ks_sorted.
  gen (hks _ i1 _ j1 ij). revert i2. simpl Vopt_filter. rewrite !Vnth_cons.
  destruct (lt_ge_dec 0 i).
  (* 0 < i *)
  intro ai. destruct (lt_ge_dec 0 j). 2: lia.
  intros _. eapply IHks. hyp. apply ai. lia.
  (* 0 >= i *)
  assert (i = 0). lia. subst i. clear g.
  destruct (lt_dec k p). discr. intros _.
  destruct (lt_ge_dec 0 j). 2: refl.
  rewrite Vnth_opt_filter.
  destruct (lt_dec (Vnth ks (Vnth_cons_tail_aux j1 l)) p). lia. refl.
Qed.

(***********************************************************************)
(** ** Extension of a relation on [A] to a relation on [vector (option A)]

so that [Vforall2_opt (n:=n) R us vs] if there are [k <= n], [xs, ys :
vector A k] such that [us = Vapp (Vmap Some xs) (Vconst None (n-k))],
[vs = Vapp (Vmap Some ys) (Vconst None (n-k))] and [Vforall2 R xs ys]. *)

Definition Vforall2_opt {n A} (R : relation A) :
  relation (vector (option A) n) :=
  fun us vs => exists i (h : i <= n),
    Vforall2 (opt R) (Vsub us (Veq_app_aux1 h)) (Vsub vs (Veq_app_aux1 h))
    /\ Vforall2 (opt_r empty_rel) (Vsub us (Veq_app_aux2 h))
                                (Vsub vs (Veq_app_aux2 h)).

Lemma Vforall2_opt_filter A p (ts us : vector A p) (R : relation A) :
  forall n (ks : vector nat n), sorted ks ->
    (forall i (ip : i < p), Vin i ks -> R (Vnth ts ip) (Vnth us ip)) ->
    Vforall2_opt R (Vopt_filter ks ts) (Vopt_filter ks us).

Proof.
  induction ks as [|k n ks IH]; intros kks_sorted tsus; simpl.
  (* Vnil *)
  ex 0 (Nat.le_refl 0). rewrite !Vsub_nil, !Vforall2_cast. split; refl.
  (* Vcons *)
  destruct (lt_dec k p).
  (* k < p *)
  gen (sorted_cons_elim kks_sorted); intro ks_sorted.
  assert (tsus' : forall i (ip:i<p), Vin i ks -> R (Vnth ts ip) (Vnth us ip)).
  intros i ip hi. apply tsus. simpl. auto.
  gen (IH ks_sorted tsus'). intros [i [i1 [i2 i3]]].
  assert (a : S i <= S n). lia. ex (S i) a. split.

  apply Vforall2_intro_nth. intros j jSi. rewrite !Vnth_sub, !Vnth_cons. simpl.
  destruct (lt_ge_dec 0 j).
  assert (b : j - 1 < i). lia. gen (Vforall2_elim_nth b i2).
  rewrite !Vnth_sub. erewrite Vnth_eq.
  erewrite Vnth_eq with (v := Vopt_filter ks us).
  apply impl_refl. lia. lia.
  apply opt_intro. apply tsus. fo.

  apply Vforall2_intro_nth. intros j hj. rewrite !Vnth_sub, !Vnth_cons.
  destruct (lt_ge_dec 0 (S i + j)). 2: lia.
  assert (b : j < n - i). lia. gen (Vforall2_elim_nth b i3).
  rewrite !Vnth_sub. erewrite Vnth_eq.
  erewrite Vnth_eq with (v := Vopt_filter ks us).
  apply impl_refl. lia. lia.
  (* k >= p *)
  assert (a : 0 <= S n). lia. ex 0 a. split.
  apply Vforall2_intro_nth. intros j hj. lia.
  apply Vforall2_intro_nth. intros j hj. rewrite !Vnth_sub, !Vnth_cons. simpl.
  destruct (lt_ge_dec 0 j). 2: apply opt_r_None. rewrite !Vnth_opt_filter.
  match goal with |- context C [lt_dec (Vnth ks ?x) p] => set (h := x) end.
  destruct (lt_dec (Vnth ks h) p). 2: apply opt_r_None. exfalso.
  unfold sorted in kks_sorted.
  assert (ai : 0 < S n). lia. assert (aj : j < S n). lia.
  gen (kks_sorted _ ai _ aj l). rewrite !Vnth_cons.
  destruct (lt_ge_dec 0 0). lia. destruct (lt_ge_dec 0 j). 2: lia.
  rewrite Vnth_eq with (h2:=h). lia. lia.
Qed.

(****************************************************************************)
(** ** First position of an element in a vector. *)

Section first_position.

  Variables (A : Type) (P : A -> Prop) (P_dec : forall y : A, {P y}+{~P y}).

  Fixpoint Vfirst_position_aux k n (ys : vector A n) :=
    match ys with
      | Vnil => None
      | Vcons y ys' =>
        match P_dec y with
          | left _ => Some k
          | _ => Vfirst_position_aux (S k) ys'
        end
    end.

  Definition Vfirst_position := Vfirst_position_aux 0.

  Lemma Vfirst_position_aux_lt : forall n (ys : vector A n) k i,
    Vfirst_position_aux k ys = Some i -> i < k+n.

  Proof.
    induction ys as [|y n ys]; intros k i; simpl. discr. destruct (P_dec y).
    intro h; inversion h; clear h; subst. lia.
    intro h. gen (IHys _ _ h). lia.
  Qed.

  Lemma Vfirst_position_lt : forall n (ys : vector A n) i,
    Vfirst_position ys = Some i -> i < n.

  Proof. intros n ys i. apply Vfirst_position_aux_lt. Qed.

  Lemma Vfirst_position_aux_ge : forall n (ys : vector A n) k i,
    Vfirst_position_aux k ys = Some i -> i >= k.

  Proof.
    induction ys as [|y n ys]; intros k i; simpl. discr.
    destruct (P_dec y). 2: firstorder auto with arith.
    intro h; inversion h; clear h; subst. refl.
  Qed.

  Lemma Vfirst_position_aux_nth : forall n (ys : vector A n) k i j (hj : j<n),
    Vfirst_position_aux k ys = Some i -> P (Vnth ys hj) -> i <= k+j.

  Proof.
    induction ys as [|y n ys]; intros k i j hj; simpl. discr.
    destruct (P_dec y).
    intro h; inversion h; clear h; subst. destruct j as [|j]; lia.
    intro h1. destruct j as [|j]; intro h2. fo.
    gen (IHys _ _ _ _ h1 h2). lia.
  Qed.

  Lemma Vfirst_position_nth : forall n (ys : vector A n) i j (hj : j<n),
    Vfirst_position ys = Some i -> P (Vnth ys hj) -> i <= j.

  Proof. intros n ys i j hj. apply Vfirst_position_aux_nth. Qed.

  Lemma Vnth_first_position_aux : forall n (ys : vector A n) k i (hi : i-k < n),
    Vfirst_position_aux k ys = Some i -> P (Vnth ys hi).

  Proof.
    induction ys as [|y n ys IH]; intros k i hi; simpl Vfirst_position_aux.
    discr.
    destruct (P_dec y).
    intro h; inversion h; clear h; subst.
    rewrite Vnth_cons. destruct (lt_ge_dec 0 (i-i)). lia. hyp.
    intro h. rewrite Vnth_cons. destruct (lt_ge_dec 0 (i-k)).
    assert (hi' : i - S k < n). lia. gen (IH _ _ hi' h); intro hx.
    rewrite Vnth_eq with (h2:=hi'). hyp. lia.
    gen (Vfirst_position_aux_ge _ _ h). lia.
  Qed.

  Lemma Vnth_first_position : forall n (ys : vector A n) i (hi : i<n),
    Vfirst_position ys = Some i -> P (Vnth ys hi).

  Proof.
    intros n ys i hi h. assert (hi' : i-0 < n). lia.
    rewrite Vnth_eq with (h2:=hi'). apply Vnth_first_position_aux. hyp. lia.
  Qed.

End first_position.

Arguments Vfirst_position_aux [A P] _ _ [n] _.
Arguments Vfirst_position [A P] _ [n] _.
Arguments Vfirst_position_lt [A P] _ [n ys i] _.
Arguments Vnth_first_position [A P] _ [n ys i hi] _.
Arguments Vfirst_position_nth [A P] _ [n ys i j hj] _ _.

Section first_position_eq.

  Variables (A : Type) (eq_dec : forall x y : A, {x=y}+{~x=y}) (x : A).

  Lemma Vfirst_position_aux_in : forall n (ys : vector A n) k i,
    Vfirst_position_aux (eq_dec x) k ys = Some i -> Vin x ys.

  Proof.
    induction ys as [|y n ys]; intros k i; simpl. discr.
    destruct (eq_dec x y); fo.
  Qed.

  Lemma Vfirst_position_in : forall n (ys : vector A n) i,
    Vfirst_position (eq_dec x) ys = Some i -> Vin x ys.

  Proof. intros n ys i. apply Vfirst_position_aux_in. Qed.
 
  Lemma Vin_first_position_aux : forall n (ys : vector A n) k,
    Vin x ys -> exists i, Vfirst_position_aux (eq_dec x) k ys = Some i.

  Proof.
    induction ys as [|y ys]; intro k; simpl. fo.
    intros [h|h]; destruct (eq_dec x y). subst y.
    exists k. refl. cong. exists k. refl. fo.
  Qed.

  Lemma Vin_first_position : forall n (ys : vector A n),
    Vin x ys -> exists i, Vfirst_position (eq_dec x) ys = Some i.

  Proof. intros n ys. apply Vin_first_position_aux. Qed.

End first_position_eq.

Arguments Vfirst_position_in [A] _ [x n ys i] _.
Arguments Vin_first_position [A] _ [x n ys] _.
