(**
CoLoR, a Coq library on rewriting and termination.

See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2012-04-05


* Alpha-equivalence
*)

Set Implicit Arguments.

Require Import Wf_nat Bool Morphisms Basics Equivalence RelUtil LogicUtil SN
  VecUtil VecOrd.
Require Export LSubs.

(****************************************************************************)
(** ** Alpha-equivalence
is defined as the smallest congruence containing the [aeq_alpha] rule.
Here, we exactly follow Curry-Feys definition (pages 59 and 91). *)

Section aeq.

  Variables (F X : Type) (E : Ens X).

  Notation Te := (@Te F X).

  Variable eq_fun_dec : forall f g : F, {f=g}+{~f=g}.
  Variable eq_var_dec : forall x y : X, {x=y}+{~x=y}.

  Variable ens_X : Ens X.

  Notation In := (Ens_In ens_X).
  Notation fv := (@fv F X ens_X).

  Variable var_notin : Ens_type ens_X -> X.

  Notation rename := (@rename F X eq_fun_dec eq_var_dec ens_X var_notin).

  Inductive aeq : relation Te :=
  | aeq_refl : forall u, aeq u u
  | aeq_sym : forall u v, aeq u v -> aeq v u
  | aeq_trans : forall u v w, aeq u v -> aeq v w -> aeq u w
  | aeq_app_l : forall u u' v, aeq u u' -> aeq (App u v) (App u' v)
  | aeq_app_r : forall u v v', aeq v v' -> aeq (App u v) (App u v')
  | aeq_lam : forall x u u', aeq u u' -> aeq (Lam x u) (Lam x u')
  | aeq_alpha : forall x u y,
    ~In y (fv u) -> aeq (Lam x u) (Lam y (rename x y u)).

  Infix "~~" := aeq (at level 70).

  (** Alternative definition of [aeq] as the equivalence closure of
  the monotone closure of [aeq_top]. *)

  Inductive aeq_top : relation Te :=
  | aeq_top_intro : forall x u y,
    ~In y (fv u) -> aeq_top (Lam x u) (Lam y (rename x y u)).

  (** Closure modulo alpha-equivalence of a relation. *)

  Section clos_aeq.

    Variable R : relation Te.

    Inductive clos_aeq : relation Te :=
    | clos_aeq_intro : forall u u', u ~~ u' ->
      forall v v', v ~~ v' -> R u' v' -> clos_aeq u v.

  (** "Alpha-transitive closure" of a relation on terms:
     [S*] is the (reflexive) transitive closure of [S U aeq]. *)

    Inductive clos_aeq_trans : relation Te :=
    | at_step : forall u v, R u v -> clos_aeq_trans u v
    | at_aeq : forall u v, u ~~ v -> clos_aeq_trans u v
    | at_trans : forall u v w, clos_aeq_trans u v ->
      clos_aeq_trans v w -> clos_aeq_trans u w.

  End clos_aeq.

End aeq.

Arguments aeq_alpha [F X] eq_fun_dec eq_var_dec ens_X var_notin [x u] y _.

(****************************************************************************)
(** ** Properties of alpha-equivalence. *)

Module Make (Export L : L_Struct).

  Module Export S := LSubs.Make L.

  Notation aeq := (@aeq F X FOrd.eq_dec XOrd.eq_dec ens_X var_notin).
  Notation aeq_alpha :=
    (@aeq_alpha F X FOrd.eq_dec XOrd.eq_dec ens_X var_notin).
  Notation aeq_top := (@aeq_top F X FOrd.eq_dec XOrd.eq_dec ens_X var_notin).
  Notation clos_aeq := (@clos_aeq F X FOrd.eq_dec XOrd.eq_dec ens_X var_notin).
  Notation clos_aeq_trans :=
    (@clos_aeq_trans F X FOrd.eq_dec XOrd.eq_dec ens_X var_notin).

  Infix "~~" := aeq (at level 70).
  Notation "R *" := (clos_aeq_trans R) (at level 35).

  Lemma aeq_equiv_mon : aeq == clos_equiv (clos_mon aeq_top).

  Proof.
    split; intros u v uv; revert u v uv.

    induction 1. refl. sym. hyp. trans v; hyp.
    clear uv. revert u u' IHuv. induction 1.
    apply e_step. apply m_app_l. hyp.
    refl. trans (App y v); hyp. sym. hyp.
    clear uv. revert v v' IHuv. induction 1.
    apply e_step. apply m_app_r. hyp.
    refl. trans (App u y); hyp. sym. hyp.
    clear uv. revert u u' IHuv. induction 1.
    apply e_step. apply m_lam. hyp.
    refl. trans (Lam x y); hyp. sym. hyp.
    apply e_step. apply m_step. apply aeq_top_intro. hyp.

    induction 1.
    revert x y H. induction 1.
    inversion H. apply aeq_alpha. hyp.
    apply aeq_app_l. hyp.
    apply aeq_app_r. hyp.
    apply aeq_lam. hyp.
    apply aeq_refl.
    apply aeq_trans with y; hyp.
    apply aeq_sym. hyp.
  Qed.

  Instance aeq_equiv : Equivalence aeq.

  Proof. rewrite aeq_equiv_mon. apply ec_equiv. Qed.

  Instance aeq_mon : Monotone aeq.

  Proof. rewrite aeq_equiv_mon. class. Qed.

  (** Term constructors are compatible with [aeq]. *)

  Instance App_aeq : Proper (aeq ==> aeq ==> aeq) App.

  Proof.
    intros u1 v1 u1v1 u2 v2 u2v2. trans (App u1 v2).
    apply aeq_app_r. hyp. apply aeq_app_l. hyp.
  Qed.

  Instance Lam_aeq : Proper (Logic.eq ==> aeq ==> aeq) Lam.

  Proof. intros x x' xx' u u' uu'. subst x'. apply aeq_lam. hyp. Qed.

  (** Basic lemmas. *)
  
  Lemma aeq_refl_eq : forall u v, u = v -> u ~~ v.

  Proof. intros u v e. subst v. apply aeq_refl. Qed.

  Lemma aeq_alpha' : forall x u y,
    x = y \/ ~In y (fv u) -> Lam x u ~~ Lam y (rename x y u).

  Proof.
    intros x u y [h|h]. subst. rewrite rename_id. refl. apply aeq_alpha. hyp.
  Qed.

  (** [fv] is compatible with [aeq]. *)

  Instance fv_aeq : Proper (aeq ==> Equal) fv.

  Proof.
    induction 1; simpl.
    refl.
    sym. hyp.
    rewrite IHaeq1, IHaeq2. refl.
    rewrite IHaeq. refl.
    rewrite IHaeq. refl.
    rewrite IHaeq. refl.
    rewrite fv_rename.
    case_eq (mem x (fv u)); [rewrite <- mem_iff|rewrite <- not_mem_iff];
      intro hx.
    rewrite remove_add. refl. set_iff. tauto.
    repeat rewrite remove_equal; auto. refl.
  Qed.

  (** [var] is compatible with [aeq]. *)

  Instance var_aeq : Proper (Logic.eq ==> aeq ==> Logic.eq ==> Logic.eq) var.

  Proof.
    intros x x' xx' u u' uu' s s' ss'. subst s'. subst x'. unfold_var.
    rewrite uu'. destruct (mem x (fvcodom (remove x (fv u')) s)).
    rewrite uu'. refl. refl.
  Qed.

  (** On variables and function symbols, alpha-equivalence is
  equivalent to equality. *)

  Lemma var_aeq_l : forall x v, Var x ~~ v -> Var x = v.

  Proof.
    intro x. cut (forall u v, u ~~ v -> (u = Var x \/ v = Var x) -> u = v). fo.
    induction 1; intro h; try (destruct h; discr). refl. fo.
    trans v. apply IHaeq1. intuition. subst. auto.
    apply IHaeq2. intuition. subst. auto.
  Qed.

  Lemma var_aeq_r : forall x v, v ~~ Var x -> v = Var x.

  Proof. intros x v h. sym. apply var_aeq_l. sym. hyp. Qed.

  Lemma fun_aeq_l : forall f v, Fun f ~~ v -> Fun f = v.

  Proof.
    intro f. cut (forall u v, u ~~ v -> (u = Fun f \/ v = Fun f) -> u = v). fo.
    induction 1; intro h; try (destruct h; discr). refl. fo.
    trans v. apply IHaeq1. intuition. subst. auto.
    apply IHaeq2. intuition. subst. auto.
  Qed.

  Lemma fun_aeq_r : forall f v, v ~~ Fun f -> v = Fun f.

  Proof. intros x v h. sym. apply fun_aeq_l. sym. hyp. Qed.

  (** Inversion lemma for alpha-equivalence on an application. *)

  Lemma app_aeq_r : forall t v1 v2, t ~~ App v1 v2 ->
    exists u1, exists u2, t = App u1 u2 /\ u1 ~~ v1 /\ u2 ~~ v2.

  Proof.
    cut (forall t u, t ~~ u -> forall v1 v2, (t = App v1 v2 \/ u = App v1 v2) ->
      exists u1, exists u2, u1 ~~ v1 /\ u2 ~~ v2
        /\ (t = App v1 v2 -> u = App u1 u2)
        /\ (u = App v1 v2 -> t = App u1 u2)).
    intros h v u1 u2 e. assert (p : v = App u1 u2 \/ App u1 u2 = App u1 u2).
    tauto. destruct (h _ _ e _ _ p) as [a [b [h1 [h2 [h3 h4]]]]].
    exists a. exists b. intuition.
    induction 1; intros u1 u2 e.
    (* refl *)
    exists u1. exists u2. fo.
    (* sym *)
    rewrite or_sym in e. destruct (IHaeq _ _ e) as [a [b [h1 [h2 [h3 h4]]]]].
    exists a. exists b. fo.
    (* trans *)
    destruct e.
    assert (p1 : u = App u1 u2 \/ v = App u1 u2). tauto.
    destruct (IHaeq1 _ _ p1) as [a [b [h1 [h2 [h3 h4]]]]].
    assert (p2 : v = App a b \/ w = App a b). tauto.
    destruct (IHaeq2 _ _ p2) as [c [d [i1 [i2 [i3 i4]]]]].
    exists c. exists d. intuition; subst; try inversion H4; try inversion H5;
    try inversion H6; subst; auto.
    trans a; hyp. trans b; hyp.
    assert (p2 : v = App u1 u2 \/ w = App u1 u2). tauto.
    destruct (IHaeq2 _ _ p2) as [a [b [h1 [h2 [h3 h4]]]]].
    assert (p1 : u = App a b \/ v = App a b). tauto.
    destruct (IHaeq1 _ _ p1) as [c [d [i1 [i2 [i3 i4]]]]].
    exists c. exists d. intuition; subst; try inversion H2; try inversion H4;
      try inversion H5; subst; auto.
    trans a; hyp. trans b; hyp.
    (* app_l *)
    destruct e as [h|h]; inversion h; subst; clear h.
    exists u'. exists u2. fo.
    exists u. exists u2. fo.
    (* app_r *)
    destruct e as [h|h]; inversion h; subst; clear h.
    exists u1. exists v'. fo.
    exists u1. exists v. fo.
    (* lam *)
    destruct e; discr.
    (* alpha *)
    destruct e; discr.
  Qed.

  Lemma app_aeq_l : forall v1 v2 t, App v1 v2 ~~ t ->
    exists u1, exists u2, t = App u1 u2 /\ u1 ~~ v1 /\ u2 ~~ v2.

  Proof. intros v1 v2 t e. apply app_aeq_r. sym. hyp. Qed.

  (** [size] is compatible with [aeq]. *)

  Instance size_aeq : Proper (aeq ==> Logic.eq) size.

  Proof.
    intro u; revert u; induction 1; simpl.
    refl.
    auto.
    trans (size v); hyp.
    rewrite IHaeq. refl.
    rewrite IHaeq. refl.
    rewrite IHaeq. refl.
    rewrite size_rename. refl.
  Qed.

  (** Every term is alpha-equivalent to a term which bound variables
  are disjoint from some given finite set (CF, Theorem 2b, page 95). *)

  Lemma aeq_notin_bv : forall xs u,
    exists v, u ~~ v /\ inter (bv v) xs [=] empty.

  Proof.
    intro xs. induction u.
    (* var *)
    exists (Var x). split. refl. simpl. rewrite inter_empty_l. refl.
    (* fun *)
    exists (Fun f). split. refl. simpl. rewrite inter_empty_l. refl.
    (* app *)
    destruct IHu1 as [v1 [h1 i1]]. destruct IHu2 as [v2 [h2 i2]].
    exists (App v1 v2). split.
    trans (App v1 u2). apply aeq_app_l. hyp. apply aeq_app_r. hyp.
    simpl. rewrite union_inter_1, i1, i2, union_empty_l. refl.
    (* lam *)
    destruct IHu as [v [h i]].
    set (uxs := union (fv v) (union (bv v) xs)).
    set (x' := var_notin uxs). exists (Lam x' (rename x x' v)).
    gen (var_notin_ok uxs). fold x'. unfold uxs. set_iff. intro n. split.
    trans (Lam x v). apply aeq_lam. hyp. apply aeq_alpha. tauto.
    simpl. rewrite bv_rename. 2: tauto. revert i. rewrite inter_sym at 1.
    repeat rewrite inter_empty. unfold not. intros i z. set_iff. intros [j|j].
    subst z. tauto. intro hz. eapply i. apply hz. hyp.
  Qed.

(****************************************************************************)
(** ** Alpha-equivalence on substitutions. *)

  Definition saeq xs s s' := forall x, In x xs -> s x ~~ s' x.

  Lemma saeq_update : forall xs x u u' s s', u ~~ u' ->
    saeq (remove x xs) s s' -> saeq xs (update x u s) (update x u' s').

  Proof.
    intros xs x u u' s s' uu' ss' y hy. unfold_update. eq_dec y x.
    hyp. apply ss'. set_iff. auto.
  Qed.

  (** For all [xs], [saeq xs] is an equivalence relation. *)

  Instance saeq_refl : forall xs, Reflexive (saeq xs).

  Proof. fo. Qed.

  Instance saeq_sym : forall xs, Symmetric (saeq xs).

  Proof. fo. Qed.

  Instance saeq_trans : forall xs, Transitive (saeq xs).

  Proof. intros xs s1 s2 s3 a b x h. trans (s2 x); fo. Qed.

  (** [saeq] is compatible with set inclusion and equality. *)

  Instance saeq_s : Proper (Subset --> Logic.eq ==> Logic.eq ==> impl) saeq.

  Proof.
    intros xs xs' e s1 s1' h1 s2 s2' h2. subst s1' s2'.
    unfold flip, impl, saeq in *. intuition.
  Qed.

  Instance saeq_e : Proper (Equal ==> Logic.eq ==> Logic.eq ==> iff) saeq.

  Proof.
    intros xs xs' e s1 s1' h1 s2 s2' h2. subst s1' s2'. unfold saeq.
    intuition. apply H. rewrite e. hyp. apply H. rewrite <- e. hyp.
  Qed.

  (** [domain] is compatible with [saeq]. *)

  Lemma domain_saeq : forall xs xs', xs [=] xs' ->
    forall s s', saeq xs s s' -> domain xs s [=] domain xs' s'.

  Proof.
    intros xs xs' e s s' ss' x. rewrite <- e. repeat rewrite In_domain.
    intuition.
    apply H1. apply var_aeq_r. rewrite <- H. apply ss'. hyp.
    apply H1. apply var_aeq_r. rewrite <- H. sym. apply ss'. hyp.
  Qed.

  (*FIXME: change order of arguments in fvcod, domain and fvcodom? *)

  Instance domain_saeq' : forall xs, Proper (saeq xs ==> Equal) (domain xs).

  Proof. intros xs s s' ss'. apply domain_saeq. refl. hyp. Qed.

  (** [fvcod] is compatible with [saeq]. *)

  Lemma fvcod_saeq : forall xs xs', xs [=] xs' ->
    forall s s', saeq xs s s' -> fvcod xs s [=] fvcod xs' s'.

  Proof.
    intros xs xs' e s s' ss' x. rewrite <- e. repeat rewrite In_fvcod.
    split; intros [y [h1 h2]]; exists y; intuition.
    rewrite <- (ss' _ h1). hyp. rewrite (ss' _ h1). hyp.
  Qed.

  Instance fvcod_saeq' : forall xs, Proper (saeq xs ==> Equal) (fvcod xs).

  Proof. intros xs s s' ss'. apply fvcod_saeq. refl. hyp. Qed.

  (** [fvcodom] is compatible with [saeq]. *)

  Lemma fvcodom_saeq : forall xs xs', xs [=] xs' ->
    forall s s', saeq xs s s' -> fvcodom xs s [=] fvcodom xs' s'.

  Proof.
    intros xs xs' e s s' ss'. unfold_fvcodom. rewrite <- e. apply fvcod_saeq.
    apply domain_saeq. refl. hyp. rewrite domain_subset. hyp.
  Qed.

  Instance fvcodom_saeq' : forall xs, Proper (saeq xs ==> Equal) (fvcodom xs).

  Proof. intros xs s s' ss'. apply fvcodom_saeq. refl. hyp. Qed.

  (** [var] is compatible with [saeq]. *)

  Lemma var_saeq : forall x x', x = x' -> forall u u', u ~~ u' -> forall s s',
    saeq (remove x (fv u)) s s' -> var x u s = var x u' s'.

  Proof.
    intros x x' xx' u u' uu' s s' ss'. subst x'. unfold_var. rewrite <- uu'.
    rewrite ss'. destruct (mem x (fvcodom (remove x (fv u)) s')).
    rewrite <- uu', ss'. refl. refl.
  Qed.

  Instance var_saeq' : forall x u, Proper (saeq (remove x (fv u)) ==> Logic.eq)
    (var x u).

  Proof. intros x u s s' ss'. eapply var_saeq. refl. refl. hyp. Qed.

  Arguments var_saeq' [x u x0 y] _.

  (** Generalization of [aeq_notin_bv] (Theorem 2b in CF) to
  substitutions: every substitution [s] is alpha-equivalent on any
  finite set [xs] to a substitution [s'] which domain is included in
  [xs] and which bound variables are disjoint from any fixed set
  [ys]. *)

  Lemma saeq_notin_bvcodom : forall ys s xs, exists s', saeq xs s s'
    /\ inter (bvcod xs s') ys [=] empty /\ dom_incl xs s'.

  Proof.
    intros ys s. apply set_induction_bis.
    (* Equal *)
    intros xs xs' e [s' [ss' [h1 h2]]]. exists s'. rewrite <- e. auto.
    (* empty *)
    exists id.
    split; try split; intro x; try rewrite bvcod_empty; set_iff; tauto.
    (* add *)
    intros x xs n [s' [ss' [h1 h2]]].
    destruct (aeq_notin_bv ys (s x)) as [u [i1 i2]]. exists (update x u s').

    split. intro y. set_iff. unfold_update. eq_dec y x.
    subst y. intros. hyp. intros [i|i]. subst y. tauto. apply ss'. hyp.

    split. rewrite inter_sym, inter_empty. intros y hy. rewrite In_bvcod.
    intros [z [j1 j2]]. revert j1 j2. set_iff. unfold_update.
    eq_dec z x.
    subst z. intros _ h'. rewrite inter_empty in i2. eapply i2. apply h'. hyp.
    intros [h3|h3] h4. subst z. tauto. rewrite inter_sym, inter_empty in h1.
    absurd (In y (bvcod xs s')). apply h1. hyp.
    rewrite In_bvcod. exists z. tauto.

    intro y. set_iff. intro hy. unfold_update. eq_dec y x.
    subst y. tauto. apply h2. tauto.
  Qed.

  (** Given a term [u], [fun s => subs s u] is compatible with [saeq
  (fv u)]. *) (*FIXME: change order of args in subs and subs1*)

  Lemma subs_saeq : forall u s s', saeq (fv u) s s' -> subs s u ~~ subs s' u.

  Proof.
    induction u; simpl; intros s s' h.
    (* var *)
    apply h. set_iff. refl.
    (* fun *)
    refl.
    (* app *)
    rewrite IHu1 with (s:=s)(s':=s'), IHu2 with (s:=s)(s':=s'). refl.
    intros x hx. apply h. apply union_subset_2. hyp.
    intros x hx. apply h. apply union_subset_1. hyp.
    (* lam *)
    rewrite (var_saeq' h). apply aeq_lam. apply IHu. intros y hy.
    unfold_update. eq_dec y x. refl. apply h. set_iff. auto.
  Qed.

  Arguments subs_saeq [u s s'] _.

  (** Given a term [u], [fun s => subs1 s u] is compatible with [saeq
  (fv u)]. *)

  Lemma subs1_saeq : forall u s s', saeq (fv u) s s' -> subs1 s u ~~ subs1 s' u.

  Proof.
    induction u; simpl; intros s s' h.
    (* var *)
    apply h. set_iff. refl.
    (* fun *)
    refl.
    (* app *)
    rewrite IHu1 with (s:=s)(s':=s'), IHu2 with (s:=s)(s':=s'). refl.
    intros x hx. apply h. apply union_subset_2. hyp.
    intros x hx. apply h. apply union_subset_1. hyp.
    (* lam *)
    apply aeq_lam. apply IHu. intros y hy. unfold_update.
    eq_dec y x. refl. apply h. set_iff. auto.
  Qed.

  Arguments subs1_saeq [u s s'] _.

(****************************************************************************)
(** ** Some meta-theorems. *)

  (** Meta-theorem saying that, for proving [subs s u ~~ subs s v], we
  can assume without lost of generality (w.l.o.g.) that the domain of
  [s] is included in [union (fv u) (fv v)]. *)

  Lemma restrict_domain_subs_aeq : forall u v,
    (forall s, (forall x, ~In x (union (fv u) (fv v)) -> s x = Var x) ->
      subs s u ~~ subs s v) -> forall s, subs s u ~~ subs s v.

  Proof.
    intros u v h s. set (s' := restrict (union (fv u) (fv v)) s).
    rewrite subs_seq with (s':=s'). rewrite subs_seq with (s:=s) (s':=s').
    apply h. intros x h'. unfold s'. unfold_restrict.
    rewrite not_mem_iff in h'. rewrite h'. refl.
    unfold s'. apply seq_restrict. apply union_subset_2.
    unfold s'. apply seq_restrict. apply union_subset_1.
  Qed.

  (** Meta-theorem saying that, for proving [subs s u ~~ subs s v], we
  can assume w.l.o.g. that the bound variables of [s] are disjoint
  from some fixed finite set [ys]. *)

  Lemma restrict_bvcodom_subs_aeq : forall ys u v,
    (forall s, dom_incl (union (fv u) (fv v)) s ->
      inter (bvcod (union (fv u) (fv v)) s) ys [=] empty ->
      subs s u ~~ subs s v) -> forall s, subs s u ~~ subs s v.

  Proof.
    intros ys u v h s.
    destruct (saeq_notin_bvcodom ys s (union (fv u) (fv v)))
      as [s' [h1 [h2 h3]]].
    rewrite subs_saeq with (s':=s'). rewrite subs_saeq with (s:=s) (s':=s').
    apply h; hyp.
    eapply saeq_s. unfold flip. apply union_subset_2. refl. refl. apply h1.
    eapply saeq_s. unfold flip. apply union_subset_1. refl. refl. apply h1.
  Qed.

  (** Meta-theorem saying that, for proving [P s -> subs s u ~~ subs s
  v], we can assume w.l.o.g. that the domain of [s] is included in
  [union (fv u) (fv v)], and the bound variables of [s] are disjoint
  from some fixed finite set [ys s], if [P] and [ys] are compatible
  with [saeq (union (fv u) (fv v))]. *)

  Lemma restrict_bvcodom_subs_aeq_prop : forall u v ys P,
    Proper (saeq (union (fv u) (fv v)) ==> Equal) ys ->
    Proper (saeq (union (fv u) (fv v)) ==> iff) P ->
    (forall s, dom_incl (union (fv u) (fv v)) s ->
      inter (bvcod (union (fv u) (fv v)) s) (ys s) [=] empty ->
      P s -> subs s u ~~ subs s v) -> forall s, P s -> subs s u ~~ subs s v.

  Proof.
    intros u v ys P hys hP h s hs.
    destruct (saeq_notin_bvcodom (ys s) s (union (fv u) (fv v)))
      as [s' [h1 [h2 h3]]].
    rewrite subs_saeq with (s':=s'). rewrite subs_saeq with (s:=s) (s':=s').
    apply h. hyp. rewrite <- h1 at 2. hyp. rewrite <- h1. hyp.
    eapply saeq_s. unfold flip. apply union_subset_2. refl. refl. apply h1.
    eapply saeq_s. unfold flip. apply union_subset_1. refl. refl. apply h1.
  Qed.

(****************************************************************************)
(** ** Substitution is compatible with alpha-equivalence
(CF, Theorem 2a, page 95, proof pages 100-103).

This is the most difficult theorem when formalizing lambda-calculus
using Curry and Feys approach. The CF paper proof has about 100 lines
and the following Coq proof has about 200 lines, but it could
certainly be shortened by defining tactics for reasoning on free
variables. *)

  Instance subs_aeq : Proper (Logic.eq ==> aeq ==> aeq) subs.

  Proof.
    intros s s' ss'. subst s'. intros u u' uu'; revert u u' uu' s.
    (* As CF, we proceed first by induction on the size of [u],
       and second by induction on [u ~~ u']. *)
    intro u; pattern u; apply (induction_ltof1 _ size); clear u.
    intros u IH u' uu'; revert u u' uu' IH. induction 1; intros IH s.
    (* refl *)
    refl.
    (* sym *)
    sym. apply IHuu'. intros w hw w' ww' s'. apply IH.
    unfold ltof. rewrite <- uu'. hyp. hyp.
    (* trans *)
    trans (subs s v).
    apply IHuu'1. intros a ha a' aa' s'. apply IH. hyp. hyp.
    apply IHuu'2. intros a ha a' aa' s'. apply IH.
    unfold ltof. rewrite uu'1. hyp. hyp.
    (* app_l *)
    simpl. apply aeq_app_l. apply IHuu'. intros a ha a' aa' s'. apply IH.
    revert ha. max. hyp.
    (* app_r *)
    simpl. apply aeq_app_r. apply IHuu'. intros a ha a' aa' s'. apply IH.
    revert ha. max. hyp.
    (* lam *)
    simpl.
    rewrite (@var_aeq _ _ (Logic.eq_refl x) _ _ uu' _ _ (Logic.eq_refl s)).
    set (x' := var x u' s). set (s' := update x (Var x') s). apply aeq_lam.
    apply IHuu'. intros v hv v' vv' l. apply IH.
    revert hv. unfold ltof. simpl. intro hv. omega. hyp.
    (* alpha *)
    eq_dec x y.
    (* x = y *)
    subst. rewrite rename_id. refl.
    (* x <> y *)
    set (u' := rename x y u).

    assert (pp' : remove x (fv u) [=] remove y (fv u')).
    unfold u'. rewrite fv_rename.
    case_eq (mem x (fv u)); [rewrite <- mem_iff|rewrite <- not_mem_iff];
      intro h. rewrite remove_add. refl. set_iff. intuition.
    repeat rewrite remove_equal; auto. refl.

    destruct (aeq_notin_bv (add (var y u' s) (add (var x u s)
      (add x (add y (union (fv u) (fvcodom (remove x (fv u)) s)))))) u)
      as [v [h1 h2]]. rewrite inter_sym in h2. revert s h2.
    apply restrict_bvcodom_subs_aeq_prop
      with (ys := fun s => singleton (var y u' s)).

    intros s s'. simpl. rewrite <- pp', union_idem. intro ss'.
    rewrite var_saeq with (x':=y) (u':=u') (s':=s'); try refl.
    rewrite <- pp'. hyp.

    intros s s'. simpl. rewrite <- pp', union_idem. intro ss'.
    rewrite fvcodom_saeq with (xs':=remove x (fv u)) (s':=s').
    rewrite var_saeq with (x':=y) (s:=s) (s':=s') (u:=u') (u':=u'); try refl.
    rewrite var_saeq with (x':=x) (s:=s) (s':=s') (u:=u) (u':=u); try refl.
    hyp. rewrite <- pp'. hyp. refl. hyp.

    intro s. simpl. set (x' := var x u s). set (y' := var y u' s).
    set (xs := add y' (add x' (add x (add y (union (fv u)
      (fvcodom (remove x (fv u)) s)))))). rewrite <- pp', union_idem.
    intros hs1 hs2 hs3.
    set (xx's := update x (Var x') s). set (yy's := update y (Var y') s).

    trans (Lam x' (subs xx's v)). apply aeq_lam. apply IH.
    unfold ltof. simpl. omega. hyp.
    unfold u'. trans (Lam y' (subs yy's (rename x y v))).

    Focus 2. apply aeq_lam. apply IH.
    unfold ltof. rewrite h1, size_rename. simpl. omega.
    apply IH. unfold ltof. rewrite h1. simpl. omega. sym. hyp.

    Focus 1. rewrite inter_sym, inter_empty in hs3. unfold xs in hs3.
    rewrite <- eqb_false_iff, eqb_sym in n.

    assert (e : rename x y v = subs1 (single x (Var y)) v).
    unfold_rename. apply subs1_no_alpha.
    rewrite fvcodom_single, beq_term_var, n.
    simpl. rewrite andb_true_r. destruct (mem x (fv v)). 2: apply inter_empty_r.
    rewrite inter_empty. intros a ha. set_iff. intro e. subst a.
    eapply hs3. apply ha. set_iff. tauto.

    assert (e1 : subs xx's v = subs1 xx's v). apply subs1_no_alpha.
    rewrite inter_empty. intros a ha. rewrite In_fvcodom.
    intros [b [i1 [i2 i3]]]. gen (hs3 _ ha). set_iff. intuition. apply H6.
    rewrite In_fvcodom. exists b. set_iff. rewrite h1.
    revert i3. unfold xx's. unfold_update. eq_dec b x.
    subst b. simpl. set_iff. tauto. intuition. revert i3. rewrite H5. simpl.
    set_iff. intro h. subst b. rewrite h1 in H4. tauto.

    assert (e2 : subs yy's (rename x y v) = subs1 yy's (rename x y v)).
    apply subs1_no_alpha. rewrite bv_rename.
    Focus 2. intro h. gen (hs3 _ h). set_iff. tauto. Focus 1.
    rewrite inter_empty. intros a ha. gen (hs3 _ ha). set_iff. intuition.
    revert H1. rewrite In_fvcodom. intros [b [i1 [i2 i3]]]. revert i2 i3.
    unfold yy's. unfold_update. eq_dec b y; simpl; set_iff. auto.
    intros i2 i3. apply H7. rewrite In_fvcodom. exists b. revert i1.
    rewrite h1 in *. rewrite fv_rename.
    destruct (mem x (fv v)); set_iff; intuition.

    rewrite e1, e2, e. unfold yy's. rewrite subs1_update_single.
    Focus 2. intro h. gen (hs3 _ h). set_iff. tauto.
    Focus 1. destruct (In_dec y' (fv (subs1 xx's v))).

    (* In y' (fv (subs1 xx's v)) *)
    rewrite <- e1, fv_subs in i. revert i. simpl. set_iff. rewrite In_domain.
    intuition.

    (* 1 *)
    case_eq (mem y (fvcodom (remove y (fv u')) s)); intro h.
    Focus 2. revert H0. unfold y'. unfold_var. rewrite h. rewrite h1 in H.
    tauto.
    assert (p0 : ~In y' (union (fv u') (fvcodom (remove y (fv u')) s))).
    unfold y'. unfold_var. rewrite h. apply var_notin_ok.
    destruct (eq_term_dec (xx's y') (Var y')). 2: tauto.
    revert e0. unfold xx's at 1. unfold LSubs.update at 1. eq_dec y' x.

    (* y' = x *)
    intro e3. inversion e3. rewrite H3, e0. apply aeq_lam. apply aeq_refl_eq.
    apply subs1_seq. intros a ha. unfold xx's. unfold_single_update.
    eq_dec a x. rewrite e3, e0. refl.
    eq_dec a y. subst a. rewrite <- h1 in ha. tauto. refl.

    (* y' <> x *)
    absurd (In y' (fv u')). intro h'. apply p0. set_iff. auto.
    unfold u'. rewrite fv_rename. rewrite <- h1 in H0. destruct (mem x (fv u)).
    set_iff. intuition. hyp.

    (* 2 *)
    change (In y' (fvcodom (fv v) xx's)) in H1. revert H1. rewrite In_fvcodom.
    intros [a [i1 [i2 i3]]]. unfold xx's, LSubs.update in i2, i3. revert i2 i3.
    eq_dec a x.

    (* a = x *)
    subst a. simpl. set_iff. intros i2 i3. rewrite <- i3. apply aeq_lam.
    apply aeq_refl_eq. apply subs1_seq. intros a ha.
    unfold xx's. unfold_single_update.
    eq_dec a x; simpl; unfold yy's. unfold_update.
    subst a. eq_dec y y. 2: tauto. rewrite i3. refl.
    eq_dec a y. subst a. rewrite h1 in H. tauto. refl.

    (* a <> x *)
    intros i2 i3. case_eq (mem y (fvcodom (remove y (fv u')) s)); intro hy.

    absurd (In y' (union (fv u') (fvcodom (remove y (fv u')) s))).
    unfold y'. unfold_var. rewrite hy. apply var_notin_ok.
    set_iff. right. rewrite In_fvcodom. exists a. set_iff. intuition.
    unfold u'. rewrite fv_rename. destruct (mem x (fv u)); rewrite h1.
    set_iff. intuition. hyp. subst a. rewrite <- h1 in i1. tauto.

    assert (p0 : y' = y). unfold y'. unfold_var. rewrite hy. refl.
    absurd (In y (fvcodom (remove y (fv u')) s)). rewrite not_mem_iff. hyp.
    rewrite In_fvcodom. exists a. set_iff. rewrite p0 in i3. intuition.
    unfold u'. rewrite fv_rename. destruct (mem x (fv u)); rewrite h1.
    set_iff. intuition. hyp. subst a. rewrite <- h1 in i1. tauto.

    (* ~In y' (fv (subs1 xx's v)) *)
    trans (Lam y' (rename x' y' (subs1 xx's v))). apply aeq_alpha. hyp.
    apply aeq_lam. unfold_rename. rewrite subs1_no_alpha.

    Focus 2. rewrite fvcodom_single, beq_term_var.
    case_eq (mem x' (fv (subs1 xx's v)) && negb (eqb y' x')).
    2: intros _; apply inter_empty_r.
    rewrite andb_true_iff, negb_true_iff, eqb_false_iff, <- mem_iff.
    intros [i1 i2]. simpl. rewrite inter_sym, inter_empty. intro a. set_iff.
    intro ha. subst a. intro h. apply bv_subs1 in h. revert h. set_iff.
    rewrite In_bvcod. intros [h|[z [j1 j2]]].
    gen (hs3 _ h). set_iff. tauto.
    revert j2. unfold xx's. eq_dec z x.
    subst z. rewrite update_eq. simpl. set_iff. auto.
    rewrite update_neq. 2: auto.
    assert (h : In z (remove x (fv u))). rewrite h1. set_iff. auto.
    intro i. rewrite inter_sym, inter_empty in hs2. eapply hs2. set_iff. refl.
    rewrite In_bvcod. exists z. auto.

    Focus 1. unfold xx's. apply aeq_refl_eq.

    destruct (In_dec x' (fv v)).
    case_eq (mem x (fvcodom (remove x (fv u)) s)); intro hx.
    absurd (In x' (union (fv u) (fvcodom (remove x (fv u)) s))).
    unfold x'. unfold_var. rewrite hx. apply var_notin_ok.
    set_iff. rewrite h1. auto.
    assert (p : x'=x). unfold x'. unfold_var. rewrite hx. refl.
    rewrite p, subs1_single_subs1. apply subs1_seq. intros a ha.
    unfold_update. eq_dec a x. refl. eq_dec a y.
    subst a. rewrite <- h1 in ha. tauto. refl. rewrite update_eq. refl.
    rewrite fvcodom_update_id, <- h1, not_mem_iff. hyp.

    eq_dec x' y'. rewrite <- e0. rewrite subs1_single_id.
    apply subs1_seq. intros a ha. unfold_update.
    eq_dec a x. refl. eq_dec a y.
    subst a. rewrite <- h1 in ha. tauto. refl.

    rewrite subs1_single_update. apply subs1_seq. intros a ha. unfold_update.
    eq_dec a x'; eq_dec a x; eq_dec a y;
      try subst a; try subst x; try subst y; auto.
    tauto. rewrite <- h1 in ha. tauto. hyp.
    intro h. case_eq (mem x (fvcodom (remove x (fv u)) s)); intro hx.
    assert (p : ~In x' (union (fv u) (fvcodom (remove x (fv u)) s))).
    unfold x'. unfold_var. rewrite hx. apply var_notin_ok.
    apply p. set_iff. right. rewrite h1. hyp.
    assert (p : x' = x). unfold x'. unfold_var. rewrite hx. refl.
    absurd (In x' (fvcodom (remove x (fv u)) s)).
    rewrite p, not_mem_iff. hyp. rewrite h1. hyp.
    intro h. gen (hs3 _ h). set_iff. tauto.
    intro h. gen (hs3 _ h). set_iff. tauto.
  Qed.

  Instance rename_aeq : Proper (Logic.eq ==> Logic.eq ==> aeq ==> aeq) rename.

  Proof.
    intros x x' xx' y y' yy' u u' uu'. subst x' y'.
    unfold_rename. rewrite uu'. refl.
  Qed.

(****************************************************************************)
(** [comp] is compatible with [saeq]. *)

  Lemma comp_saeq : forall xs s1 t1, saeq xs s1 t1 -> forall s2 t2,
    saeq (fvcod xs s1) s2 t2 -> saeq xs (comp s2 s1) (comp t2 t1).

  Proof.
    intros xs s1 t1 e1 s2 t2 e2 x hx. unfold comp. rewrite (e1 _ hx).
    apply subs_saeq. intros y hy. apply e2. rewrite In_fvcod. exists x.
    rewrite (e1 _ hx). auto.
  Qed.

(****************************************************************************)
(** ** Correctness of substitution composition modulo alpha-equivalence.

Because [subs s u] may rename some bound variables of [u] depending on
the free variables of [u] and the free variables of [s], the following
equality cannot hold syntactically. Take for instance [x<>y], [u = Lam
y (Var x)], [s1 = single x (Var y)] and [s2 = single y (Var x)]. Then,
[subs s2 (subs s1 u) = subs s2 (Lam y' (Var y)) = Lam y'' (Var x)],
while [subs (comp s1 s2) u = Lam y (Var x)] since [comp s1 s2 x = s2 y
= Var x]. And one can define [var_notin] so that [y''<>y]. *)

  Lemma subs_comp : forall u s1 s2, subs s2 (subs s1 u) ~~ subs (comp s2 s1) u.

  Proof.
    intros u s1 s2. set (A := fvcodom (fv u) s1).
    set (B := fvcodom (fv (subs s1 u)) s2).
    set (C := fvcodom (fv u) (comp s2 s1)).
    set (D := fvcodom (fvcod (fv u) s1) s2).
    set (P := union A (union B C)). set (Q := union B D).
    destruct (aeq_notin_bv P u) as [u' [uu' hu']]. rewrite uu'.
    destruct (saeq_notin_bvcodom Q s1 (fv u')) as [s1' [e1 [h1 h2]]].
    rewrite (subs_saeq e1).

    assert (a : subs s1' u' = subs1 s1' u'). apply subs1_no_alpha.
    rewrite <- e1. rewrite <- uu' at 2. fold A.
    rewrite empty_subset, union_subset_1 with (s:=A) (s':=union B C),
      <- empty_subset. hyp.

    assert (b : subs s2 (subs s1' u') = subs1 s2 (subs s1' u')).
    apply subs1_no_alpha. rewrite <- (subs_saeq e1), <- uu' at 2. fold B.
    rewrite a. rewrite empty_subset, bv_subs1, <- empty_subset. dnf.
    rewrite union_empty. split.
    rewrite empty_subset, union_subset_1 with (s:=B) (s':=union A C),
      <- empty_subset, <- union_assoc, union_sym with (s:=B), union_assoc. hyp.
    rewrite empty_subset, union_subset_1 with (s:=B) (s':=D),
      <- empty_subset. hyp.

    assert (c : subs (comp s2 s1) u' = subs1 (comp s2 s1) u').
    apply subs1_no_alpha. rewrite <- uu' at 2. fold C.
    rewrite empty_subset, union_subset_1 with (s:=C) (s':=union A B),
      <- empty_subset, union_sym with (s:=C), union_assoc. hyp.

    rewrite b, a, c, subs1_comp.

    Focus 2. rewrite <- e1. rewrite <- uu' at 2. fold A.
    rewrite empty_subset, union_subset_1 with (s:=A) (s':=union B C),
      <- empty_subset. hyp. Focus 1.

    apply subs1_saeq. intros x hx. unfold comp1, comp. rewrite (e1 _ hx).
    sym. apply aeq_refl_eq. apply subs1_no_alpha.
    assert (d : bv (s1' x) [<=] bvcod (fv u') s1').
    intros y hy. rewrite In_bvcod. exists x. auto.
    assert (e : fv (s1' x) [<=] fvcod (fv u') s1').
    intros y hy. rewrite In_fvcod. exists x. auto.
    rewrite empty_subset, d, e. rewrite <- e1 at 2. rewrite <- uu' at 2.
    fold D. rewrite union_subset_1 with (s:=D) (s':=B), union_sym,
      <- empty_subset. hyp.
  Qed.

  Lemma single_rename : forall x y u v, x = y \/ ~In y (fv u) ->
    subs (single y v) (rename x y u) ~~ subs (single x v) u.

  Proof.
    intros x y u v hy. unfold_rename. rewrite subs_comp. apply subs_saeq.
    intros d hd. unfold comp. unfold_single. unfold LSubs.update at -1.
    eq_dec d x; simpl.
    rewrite update_eq. refl.
    unfold_update. eq_dec d y. 2: refl.
    subst d. assert (n':x<>y). auto. tauto.
  Qed.

  Lemma rename2 : forall x y z u, x = y \/ ~In y (fv u) ->
    rename y z (rename x y u) ~~ rename x z u.

  Proof. intros x y z u hy. apply single_rename. hyp. Qed.

  Lemma subs_update : forall x y s u, s y = Var y ->
    subs (update x (Var y) s) u ~~ subs (update x (Var x) s) (rename x y u).

  Proof.
    intros x y s u h. unfold_rename. rewrite subs_comp. apply subs_saeq.
    intros z hz. unfold comp. unfold_single. unfold LSubs.update at -2.
    eq_dec z x; simpl.
    subst. unfold_update. eq_dec y x.
    subst. refl.
    rewrite h. refl.
    unfold_update. eq_dec z x.
    subst. tauto.
    refl.
  Qed.

(****************************************************************************)
(** ** Inversion lemma for alpha-equivalence on a lambda. *)

  Lemma lam_aeq_r : forall t x u, t ~~ Lam x u -> exists y, exists v,
    t = Lam y v /\ v ~~ rename x y u /\ (x = y \/ ~In y (fv u)).

  Proof.
    cut (forall t t', t ~~ t' -> forall x u, t = Lam x u \/ t' = Lam x u ->
      exists y, exists v, v ~~ rename x y u /\ (x=y \/ ~In y (fv u))
        /\ (t = Lam x u -> t' = Lam y v) /\ (t' = Lam x u -> t = Lam y v)).
    intros h t x u e. assert (p : t = Lam x u \/  Lam x u = Lam x u).
    auto. destruct (h _ _ e _ _ p) as [y [v i]]. exists y. exists v. tauto.
    induction 1; intros z a e.
    (* refl *)
    exists z. exists a. split. rewrite rename_id. refl. tauto.
    (* sym *)
    rewrite or_sym in e. destruct (IHaeq _ _ e) as [y [w i]].
    exists y. exists w. tauto.
    (* trans *)
    destruct e as [e|e].

    assert (p : u = Lam z a \/ v = Lam z a). auto.
    destruct (IHaeq1 _ _ p) as [x [b [i1 [i2 [i3 i4]]]]].
    assert (q : v = Lam x b \/ w = Lam x b). tauto.
    destruct (IHaeq2 _ _ q) as [y [c [j1 [j2 [j3 j4]]]]].
    exists y. exists c. repeat split.

    rewrite j1, i1. apply rename2. hyp.

    destruct i2; destruct j2.
    left. trans x; auto.
    right. rewrite H1, rename_id in i1. rewrite <- i1. hyp.
    right. rewrite <- H2. hyp.
    eq_dec z y. auto. right. intro hy. apply H2.
    rewrite i1, fv_rename. destruct (mem z (fv a)); set_iff; auto.

    tauto. intro hw. subst u w. tauto.

    assert (p : v = Lam z a \/ w = Lam z a). auto.
    destruct (IHaeq2 _ _ p) as [x [b [i1 [i2 [i3 i4]]]]].
    assert (q : u = Lam x b \/ v = Lam x b). tauto.
    destruct (IHaeq1 _ _ q) as [y [c [j1 [j2 [j3 j4]]]]].
    exists y. exists c. repeat split.

    rewrite j1, i1. apply rename2. hyp.

    destruct i2; destruct j2.
    left. trans x; auto.
    right. rewrite H1, rename_id in i1. rewrite <- i1. hyp.
    right. rewrite <- H2. hyp.
    eq_dec z y. auto. right. intro hy. apply H2.
    rewrite i1, fv_rename. destruct (mem z (fv a)); set_iff; auto.

    intro hu. subst u w. tauto. tauto.
    (* app_l *)
    destruct e; discr.
    (* app_r *)
    destruct e; discr.
    (* lam *)
    destruct e as [e|e]; inversion e; subst.
    exists z. exists u'. rewrite rename_id. intuition.
    exists z. exists u. rewrite rename_id. intuition.
    (* alpha *)
    destruct e as [e|e].
    inversion e. subst. exists y. exists (rename z y a). intuition.
    inversion e. subst. exists x. exists u. rewrite rename2, rename_id. 2: auto.
    intuition. rewrite fv_rename. case_eq (mem x (fv u));
      [rewrite <- mem_iff|rewrite <- not_mem_iff]; intro hx.
    right. set_iff. intros [h|h]. subst z. tauto. tauto.
    auto.
  Qed.

  Lemma lam_aeq_l : forall t x u, Lam x u ~~ t -> exists y, exists v,
    t = Lam y v /\ v ~~ rename x y u /\ (x = y \/ ~In y (fv u)).

  Proof. intros t x u h. apply lam_aeq_r. sym. hyp. Qed.

(****************************************************************************)
(** Inversion tactic for alpha-equivalence. *)

  Ltac inv_aeq h :=
    match type of h with
      | Var _ ~~ _ => apply var_aeq_l in h
      | _ ~~ Var _ => apply var_aeq_r in h
      | Fun _ ~~ _ => apply fun_aeq_l in h
      | _ ~~ Fun _ => apply fun_aeq_r in h
      | App _ _ ~~ _ => let u1 := fresh "u" in let u2 := fresh "u" in
        let i1 := fresh "i" in let i2 := fresh "i" in let i3 := fresh "i" in
          destruct (app_aeq_l h) as [u1 [u2 [i1 [i2 i3]]]]
      | _ ~~ App _ _ => let u1 := fresh "u" in let u2 := fresh "u" in
        let i1 := fresh "i" in let i2 := fresh "i" in let i3 := fresh "i" in
          destruct (app_aeq_r h) as [u1 [u2 [i1 [i2 i3]]]]
      | Lam _ _ ~~ _ => let x := fresh "x" in let u := fresh "u" in
        let j1 := fresh "j" in let j2 := fresh "j" in let j3 := fresh "j" in
          destruct (lam_aeq_l h) as [x [u [j1 [j2 j3]]]]
      | _ ~~ Lam _ _ => let x := fresh "x" in let u := fresh "u" in
        let j1 := fresh "j" in let j2 := fresh "j" in let j3 := fresh "j" in
          destruct (lam_aeq_r h) as [x [u [j1 [j2 j3]]]]
    end.

(****************************************************************************)
(** Compatibility with [aeq] of some basic predicates/functions. *)

  Instance not_lam_aeq : Proper (aeq ==> impl) not_lam.

  Proof.
    intros u v uv hu x a hv. subst. inv_aeq uv; subst. eapply hu. refl.
  Qed.

  Instance head_aeq : Proper (aeq ==> aeq) head.

  Proof.
    intros u v uv. revert u v uv.
    induction u; intros v uv; inv_aeq uv; subst; simpl.
    refl. refl. fo. fo.
  Qed.

(****************************************************************************)
(** ** Closure modulo alpha-equivalence of a relation. *)

  Lemma incl_clos_aeq R : R << clos_aeq R.

  Proof.
    intros u v uv. apply clos_aeq_intro with (u':=u) (v':=v).
    refl. refl. hyp.
  Qed.

  (** Alpha-closure preserves monotony. *)

  Instance clos_aeq_impl :
    Proper (same_relation ==> aeq ==> aeq ==> impl) clos_aeq.

  Proof.
    intros R R' [RR' _] u u' uu' v v' vv' h. inversion h; subst.
    eapply clos_aeq_intro.
    trans u. sym; hyp. apply H.
    trans v. sym; hyp. apply H0.
    apply RR'. hyp.
  Qed.

  Instance clos_aeq_iff :
    Proper (same_relation ==> aeq ==> aeq ==> iff) clos_aeq.

  Proof. apply Proper_inter_transp_3; class. Qed.

  Instance clos_aeq_mon R : Monotone R -> Monotone (clos_aeq R).

  Proof.
    intro h. split.
    (* app_l *)
    intros u v uv w w' ww'. inversion uv; subst.
    apply clos_aeq_intro with (u':=App u' w') (v':=App v' w').
    rewrite H. refl. rewrite H0. refl. mon.
    (* app_r *)
    intros w w' ww' u v uv. inversion uv; subst.
    apply clos_aeq_intro with (u':=App w' u') (v':=App w' v').
    rewrite H. refl. rewrite H0. refl. mon.
    (* lam *)
    intros x x' xx' u v uv. inversion uv; subst.
    apply clos_aeq_intro with (u':=Lam x' u') (v':=Lam x' v').
    rewrite H. refl. rewrite H0. refl. mon.      
  Qed.

  (** Alpha-closure is compatible with relation inclusion/equivalence. *)

  Instance clos_aeq_incl : Proper (inclusion ==> inclusion) clos_aeq.

  Proof.
    intros R S RS u v uv. inversion uv; subst.
    apply clos_aeq_intro with (u':=u') (v':=v'); fo.
  Qed.

  Instance clos_aeq_same_rel :
    Proper (same_relation ==> same_relation) clos_aeq.

  Proof. intros R S [RS SR]. split. rewrite RS. refl. rewrite SR. refl. Qed.

  (** Alpha-closure distributes overs union. *)

  Lemma clos_aeq_union : forall R S,
    clos_aeq (R U S) == clos_aeq R U clos_aeq S.

  Proof.
    intros R S. split.
    (* << *)
    induction 1.
    destruct H1 as [h|h]; [left|right];
      (eapply clos_aeq_intro; [apply H | apply H0 | hyp]).
    (* >> *)
    intros t u [h|h]. eapply clos_aeq_incl. apply incl_union_l. refl. hyp.
    eapply clos_aeq_incl. apply incl_union_r. refl. hyp.
  Qed.

  (** Alpha-closure preserves stability by substitution. *)

  Instance subs_clos_aeq : forall R, Proper (Logic.eq ==> R ==> R) subs ->
    Proper (Logic.eq ==> clos_aeq R ==> clos_aeq R) subs.

  Proof.
    intros R subs_R s s' ss' t u tu. subst s'.
    inversion tu; subst; clear tu. rewrite H, H0.
    eapply clos_aeq_intro. refl. refl. apply subs_R. refl. hyp.
  Qed.

  (* Note that the previous lemma cannot be used to prove the
  following one since [clos_subs R] is NOT stable by substitution
  since substitution composition is correct modulo alpha-equivalence
  only. *)

  Instance subs_clos_aeq_subs : forall R,
    Proper (Logic.eq ==> clos_aeq (clos_subs R) ==> clos_aeq (clos_subs R))
    subs.

  Proof.
    intros R s s' ss' t u tu. subst s'.
    inversion tu; inversion H1; subst; clear tu H1. rewrite H0, H, 2!subs_comp.
    eapply clos_aeq_intro. refl. refl. eapply subs_step. hyp.
  Qed.

  (** Alpha-closure preserves free variables. *)

  Instance fv_clos_aeq : forall R,
    Proper (R --> Subset) fv -> Proper (clos_aeq R --> Subset) fv.

  Proof.
    intros R fv_R t u tu. inversion tu; subst; clear tu.
    rewrite H, H0, <- H1. refl.
  Qed.

  Lemma fv_R_notin_fv_lam : forall R x y u v, Proper (R --> Subset) fv ->
    R (Lam x u) (Lam y v) -> y=x \/ ~In x (fv v).

  Proof.
    intros R x y u v fv_R r. rewrite notin_fv_lam, <- r. simpl. set_iff. fo.
  Qed.

  Arguments fv_R_notin_fv_lam [R x y u v] _ _.

(****************************************************************************)
(** ** Alpha-equivalence on vectors of terms. *)

  Definition vaeq := vec_ge aeq.

  Infix "~~~" := vaeq (at level 35).

  Instance vaeq_equiv n : Equivalence (@vaeq n).

  Proof.
    constructor.
    apply vec_ge_refl. intro t. refl.
    intros ts us. unfold vaeq, vec_ge. intro h. apply Vforall2n_intro.
    intros i hi. sym. apply Vforall2n_nth with (ip:=hi) in h. hyp.
    apply vec_ge_trans. intros t u v tu uv. trans u; hyp.
  Qed.

  Lemma vaeq_cons : forall u v n (us vs : Tes n),
    Vcons u us ~~~ Vcons v vs <-> u ~~ v /\ us ~~~ vs.

  Proof. fo. Qed.

  Lemma vaeq_cons_r : forall n (u v : Tes n) x y,
    Vcons x u ~~~ Vcons y v -> u ~~~ v.

  Proof. fo. Qed.

  Lemma vaeq_app_l : forall n1 (v1 v1' : Tes n1) n2 (v2 v2' : Tes n2),
    Vapp v1 v2 ~~~ Vapp v1' v2' -> v1 ~~~ v1'.

  Proof.
    intros n1 v1 v1' n2 v2 v2' h. apply Vforall2n_intro. intros i hi.
    assert (hi' : i < n1+n2). omega.
    assert (a1 : Vnth v1 hi = Vnth (Vapp v1 v2) hi').
    rewrite Vnth_app. destruct (Compare_dec.le_gt_dec n1 i).
    omega. apply Vnth_eq. refl.
    assert (a2 : Vnth v1' hi = Vnth (Vapp v1' v2') hi').
    rewrite Vnth_app. destruct (Compare_dec.le_gt_dec n1 i).
    omega. apply Vnth_eq. refl.
    rewrite a1, a2. apply Vforall2n_nth. hyp.
  Qed.

  Lemma vaeq_app_r : forall n1 (v1 v1' : Tes n1) n2 (v2 v2' : Tes n2),
    Vapp v1 v2 ~~~ Vapp v1' v2' -> v2 ~~~ v2'.

  Proof.
    intros n1 v1 v1' n2 v2 v2' h. apply Vforall2n_intro. intros i hi.
    assert (hi' : n1+i < n1+n2). omega.
    assert (a1 : Vnth v2 hi = Vnth (Vapp v1 v2) hi').
    rewrite Vnth_app. destruct (Compare_dec.le_gt_dec n1 (n1+i)).
    apply Vnth_eq. omega. omega.
    assert (a2 : Vnth v2' hi = Vnth (Vapp v1' v2') hi').
    rewrite Vnth_app. destruct (Compare_dec.le_gt_dec n1 (n1+i)).
    apply Vnth_eq. omega. omega.
    rewrite a1, a2. apply Vforall2n_nth. hyp.
  Qed.

  Lemma vaeq_cast : forall n (u v : Tes n) n' (h : n=n'),
    Vcast u h ~~~ Vcast v h <-> u ~~~ v.

  Proof. intros n u v n' h. subst n'. rewrite 2!Vcast_refl. refl. Qed.

  Instance apps_aeq : forall n, Proper (aeq ==> @vaeq n ==> aeq) (@apps n).

  Proof.
    intros n t t' tt' us us' usus'. revert n us us' usus' t t' tt'.
    induction us; simpl; intros us' usus' t t' tt'.
    VOtac. simpl. hyp.
    VSntac us'. simpl. unfold vaeq, vec_ge, Vforall2n in usus'.
    rewrite H in usus'. simpl in usus'. destruct usus' as [h1 h2].
    apply IHus. hyp. rewrite tt', h1. refl.
  Qed.

  Lemma apps_aeq_r : forall n (vs : Tes n) v t, t ~~ apps v vs ->
    exists u us, t = apps u us /\ u ~~ v /\ vaeq us vs.

  Proof.
    induction vs; simpl; intros v t a.
    (* nil *)
    exists t. exists Vnil. simpl. intuition.
    (* cons *)
    rename h into w. destruct (IHvs _ _ a) as [u [us [h1 [h2 h3]]]].
    inv_aeq h2; subst. exists u0. exists (Vcons u1 us).
    unfold vaeq, vec_ge, Vforall2n. simpl. intuition.
  Qed.

  Arguments apps_aeq_r [n vs v t0] _.

  Lemma apps_aeq_l : forall n (vs : Tes n) v t, apps v vs ~~ t ->
    exists u us, t = apps u us /\ u ~~ v /\ vaeq us vs.

  Proof. intros n vs v t e. apply apps_aeq_r. sym. hyp. Qed.

  Arguments apps_aeq_l [n vs v t0] _.

(****************************************************************************)
(** ** Properties of [clos_trans_aeq]. *)

  Section atc_props.

    Variable S : relation Te.

    (** [S*] is a quasi-ordering. *)

    Global Instance atc_preorder : PreOrder (S*).

    Proof.
      split.
      intro x. apply at_aeq. refl.
      intros x y z xy yz. apply at_trans with y; hyp.
    Qed.

    (** [S*] is compatible with alpha-equivalence if [S] so is. *)

    Section aeq.

      Variable S_aeq : Proper (aeq ==> aeq ==> iff) S.

      Instance atc_aeq_impl : Proper (aeq ==> aeq ==> impl) (S*).

      Proof.
        intros x x' xx' y y' yy' h. revert x y h x' xx' y' yy'.
        induction 1; intros x' xx' y' yy'.
        apply at_step. rewrite <- xx', <- yy'. hyp.
        apply at_aeq. rewrite <- xx', <- yy'. hyp.
        trans v. apply IHh1. hyp. refl. apply IHh2. refl. hyp.
      Qed.

      (*COQ: if removed, Coq is looping in LComp*)
      Global Instance atc_aeq : Proper (aeq ==> aeq ==> iff) (S*).

      Proof. apply Proper_inter_transp_2; class. Qed.

    End aeq.

    (** [S*] is stable by substitution if [S] so is. *)

    Section subs.

      Variable subs_S : Proper (Logic.eq ==> S ==> S) subs.

      Global Instance subs_atc : Proper (Logic.eq ==> S* ==> S*) subs.

      Proof.
        intros s s' ss' x y xy. subst s'. revert x y xy. induction 1.
        apply at_step. apply subs_S; auto.
        apply at_aeq. rewrite H. refl.
        trans (subs s v); hyp.
      Qed.

      Global Instance rename_atc :
        Proper (Logic.eq ==> Logic.eq ==> S* ==> S*) rename.

      Proof.
        intros x x' xx' y y' yy' u u' uu'. unfold_rename.
        rewrite xx', yy', uu'. refl.
      Qed.

    End subs.

    (** [S*] preserves free variables if [S] so does. *)

    Global Instance fv_atc :
      Proper (S --> Subset) fv -> Proper (S* --> Subset) fv.

    Proof.
      intros fv_S v u uv. revert u v uv. induction 1.
      apply fv_S. hyp. rewrite H. refl. trans (fv v); hyp.
    Qed.

    (** [S*] is monotone if [S] so is. *)

    Global Instance mon_atc : Monotone S -> Monotone (clos_aeq_trans S).
      (*COQ does not recognize [S*] as [clos_aeq_trans S]*)

    Proof.
      intro h. split.
      (* app_l *)
      intros u u' uu' v v' vv'. subst v'. revert u u' uu'. induction 1.
      apply at_step. mon. apply at_aeq. mon. trans (App v0 v); hyp.
      (* app_r *)
      intros u u' uu' v v' vv'. subst u'. revert v v' vv'. induction 1.
      apply at_step. mon. apply at_aeq. mon. trans (App u v); hyp.
      (* lam *)
      intros x x' xx' u u' uu'. subst x'. revert u u' uu'. induction 1.
      apply at_step. mon. apply at_aeq. mon. trans (Lam x v); hyp.
    Qed.

    Global Instance App_atc : Monotone S -> Proper (S* ==> S* ==> S*) App.

    Proof.
      intros m u u' uu' v v' vv'. trans (App u' v).
      (* app_l *)
      clear v' vv'. revert u u' uu'. induction 1.
      apply at_step. mon. apply at_aeq. mon. trans (App v0 v); hyp.
      (* app_r *)
      clear u uu'. revert v v' vv'. induction 1.
      apply at_step. mon. apply at_aeq. mon. trans (App u' v); hyp.
    Qed.

    Global Instance Lam_atc : Monotone S -> Proper (Logic.eq ==> S* ==> S*) Lam.

    Proof.
      intros m x x' xx' u u' uu'. subst x'. revert u u' uu'. induction 1.
      apply at_step. mon. apply at_aeq. mon. trans (Lam x v); hyp.
    Qed.

  End atc_props.

(****************************************************************************)
(** ** Stepwise product extension of a relation modulo alpha-equivalence. *)

  Section vaeq_prod.

    Variable R : relation Te. Infix "->R" := R (at level 70).

    Notation R_aeq := (clos_aeq R) (only parsing).
    Infix "=>R" := (clos_aeq R) (at level 70).

    (*FIXME? make @ right associative in CoLoR *)
    Definition vaeq_prod n := @vaeq n @ (@Vgt_prod _ R n @ @vaeq n).

    Infix "==>R" := vaeq_prod (at level 70).

    Lemma vaeq_prod_cons : forall u v n (us vs : Tes n),
      Vcons u us ==>R Vcons v vs
      <-> (u =>R v /\ us ~~~ vs) \/ (u ~~ v /\ us ==>R vs).

    Proof.
      intros u v n us vs. split.

      intros [x [uusx [y [xy yvvs]]]]. revert uusx yvvs xy. VSntac x. VSntac y.
      rewrite 2!vaeq_cons. intros [h1 h2] [i1 i2] h. inversion h.
      left. subst x0 y0 x'. rewrite h1, <- i1, h2, H5, i2. split.
      apply incl_clos_aeq. hyp. refl.
      right. subst x0 y0 y'. rewrite h1, H4, i1. split. refl. 
      exists (Vtail x). intuition. exists (Vtail y). intuition.

      intros [[h1 h2]|[h1 h2]].
      inversion h1; subst. exists (Vcons u' us). split.
      rewrite vaeq_cons. intuition. exists (Vcons v' us). split.
      apply Vgt_prod_cons. auto. rewrite vaeq_cons. intuition.

      destruct h2 as [us' [usus' [vs' [us'vs' vs'vs]]]].
      exists (Vcons v us'). rewrite vaeq_cons. intuition. exists (Vcons v vs').
      rewrite vaeq_cons. intuition. apply Vgt_prod_cons. right. intuition.
    Qed.

    (** [vaeq_prod] is compatible with [vaeq]. *)

    (*TODO: follows from a more general theorem on Vforall2n. *)
    Instance vaeq_prod_vaeq n :
      Proper (@vaeq n ==> @vaeq n ==> impl) (@vaeq_prod n).

    Proof.
      intros us us' usus' ws ws' wsws' [vs [usvs [xs [bvsxs xsws]]]].
      exists vs. split. trans us. sym. hyp. hyp. exists xs. intuition.
      trans ws; hyp.
    Qed.

    (** A vector of terms is strongly normalizing for [vaeq_prod] if
    every component is strongly normalizing for [R_aeq]. *)

    Lemma sn_vaeq_prod : forall n (us : Tes n),
      Vforall (SN R_aeq) us -> SN (@vaeq_prod n) us.

    Proof.
      intros n x hx.
      (* We have [SN (@Vgt_prod _ R_aeq n) x]
      since [Vforall (SN R_aeq) x]. *)
      cut (SN (@Vgt_prod _ R_aeq n) x). 2: apply Vforall_SN_gt_prod; hyp.
      (* We can therefore proceed by well-founded induction on
      [@Vgt_prod _ R_aeq n]. *)
      induction 1. apply SN_intro. intros y [x' [xx' [y' [x'y' y'y]]]].
      (* We have [x' = Vcast (Vapp x'i (Vcons a' x'j)) k0],
      [y' = Vcast (Vapp x'i (Vcons b' x'j)) k0] and [a' ->b b']. *)
      destruct (Vgt_prod_gt x'y')
        as [i [x'i [a' [j [x'j [k0 [b' [ex' [ey' a'b']]]]]]]]].
      (* Since [x ~~~ x'], we have [x = Vast (Vapp xi (Vcons a xj)) k0]. *)
      gen (Vbreak_eq_app_cast k0 x). set (k0' := Logic.eq_sym k0).
      set (p := Vbreak (Vcast x k0')). gen (VSn_eq (snd p)). intro e. rewrite e.
      set (xi := fst p). set (a := Vhead (snd p)). set (xj := Vtail (snd p)).
      intro ex. clear e.
      (* Since [y' ~~~ y], we have [y = Vast (Vapp yi (Vcons b yj)) k0]. *)
      gen (Vbreak_eq_app_cast k0 y). fold k0'.
      set (q := Vbreak (Vcast y k0')). gen (VSn_eq (snd q)). intro e. rewrite e.
      set (yi := fst q). set (b := Vhead (snd q)). set (yj := Vtail (snd q)).
      intro ey. clear e.
      (* We have i < n *)
      assert (l : i<n). omega.
      (* We now prove that [a ~~ a']. *)
      assert (aa' : a ~~ a').
      assert (s1 : a = Vnth x l). rewrite ex, Vnth_cast, Vnth_app.
      destruct (Compare_dec.le_gt_dec i i). 2: omega.
      rewrite Vnth_cons_head. refl. omega.
      assert (s2 : a' = Vnth x' l). rewrite ex', Vnth_cast, Vnth_app.
      destruct (Compare_dec.le_gt_dec i i). 2: omega.
      rewrite Vnth_cons_head. refl. omega.
      rewrite s1, s2. apply Vforall2n_nth. hyp.
      (* We now prove that [b ~~ b']. *)
      assert (bb' : b ~~ b').
      assert (t1 : b = Vnth y l). rewrite ey, Vnth_cast, Vnth_app.
      destruct (Compare_dec.le_gt_dec i i). 2: omega.
      rewrite Vnth_cons_head. refl. omega.
      assert (t2 : b' = Vnth y' l). rewrite ey', Vnth_cast, Vnth_app.
      destruct (Compare_dec.le_gt_dec i i). 2: omega.
      rewrite Vnth_cons_head. refl. omega.
      rewrite t1, t2. apply Vforall2n_nth. sym. hyp.
      (* We now prove that [y ~~~ Vcast (Vapp xi (Vcons b xj)) k0]. *)
      assert (h :  y ~~~ Vcast (Vapp xi (Vcons b xj)) k0).
      rewrite ex, ex', vaeq_cast in xx'. rewrite ey, ey', vaeq_cast in y'y.
      trans (Vcast (Vapp x'i (Vcons b x'j)) k0).
      (* left *)
      apply Vforall2n_intro. intros k hk. rewrite ey, 2!Vnth_cast, 2!Vnth_app.
      destruct (Compare_dec.le_gt_dec i k).
      rewrite 2!Vnth_cons. destruct (NatUtil.lt_ge_dec 0 (k-i)). 2: refl.
      apply Vforall2n_nth. eapply vaeq_cons_r. eapply vaeq_app_r. sym.
      apply y'y.
      apply Vforall2n_nth. eapply vaeq_app_l. sym. apply y'y.
      (* right *)
      apply Vforall2n_intro. intros k hk. rewrite 2!Vnth_cast, 2!Vnth_app.
      destruct (Compare_dec.le_gt_dec i k).
      rewrite 2!Vnth_cons. destruct (NatUtil.lt_ge_dec 0 (k-i)). 2: refl.
      apply Vforall2n_nth. eapply vaeq_cons_r. eapply vaeq_app_r. sym.
      apply xx'.
      apply Vforall2n_nth. eapply vaeq_app_l. sym. apply xx'.
      (* We now prove that
      [Vgt_prod R_aeq x (Vcast (Vapp xi (Vcons b xj)) k0)]. *)
      assert (r : Vgt_prod R_aeq x (Vcast (Vapp xi (Vcons b xj)) k0)).
      rewrite ex. apply Vgt_prod_cast. apply Vgt_prod_app. apply Vgt_prod_cons.
      left. rewrite aa', bb'. intuition. apply incl_clos_aeq. hyp.
      (* We can now end the proof. *)
      rewrite h. apply H0. hyp. apply SN_gt_prod_forall. apply H. hyp.
    Qed.

  End vaeq_prod.

End Make.
