(**
CoLoR, a Coq library on rewriting and termination.

See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2012-04-05

* Alpha-equivalence
*)

Set Implicit Arguments.

From Stdlib Require Import Wf_nat Morphisms Basics Equivalence.
From CoLoR Require Import BoolUtil RelUtil LogicUtil SN VecUtil NatUtil VecOrd.
From CoLoR Require Export LSubs.

(****************************************************************************)
(** ** Definition of alpha-equivalence

We exactly follow Curry-Feys definition (pages 59 and 91):
alpha-equivalence is defined as the smallest congruence containing the
rule [aeq_alpha] below. *)

Module Export Def.

  Section aeq.

    (** We assume given decidable sets [F] and [X] for function
    symbols and variables respectively. *)

    Variables (F X : Type)
      (eq_fun_dec : forall f g : F, {f=g}+{~f=g})
      (eq_var_dec : forall x y : X, {x=y}+{~x=y}).

    Notation Te := (@Te F X).

    (** We assume given a structure for finite sets on [X]. *)

    Variable ens_X : Ens X.

    Notation In := (Ens_In ens_X).
    Notation fv := (@fv F X ens_X).

    (** We assume that [X] is infinite. *)

    Variable var_notin : Ens_type ens_X -> X.

    Notation rename := (@rename F X eq_fun_dec eq_var_dec ens_X var_notin).

    (** Definition of alpha-equivalence. *)

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
      | clos_aeq_intro :
        forall u u' v v', u ~~ u' -> v ~~ v' -> R u' v' -> clos_aeq u v.

      (** "Alpha-transitive closure" of a relation on terms:
         [S*] is the (reflexive) transitive closure of [S U aeq]. *)

      Inductive clos_aeq_trans : relation Te :=
      | at_step : forall u v, R u v -> clos_aeq_trans u v
      | at_aeq : forall u v, u ~~ v -> clos_aeq_trans u v
      | at_trans : forall u v w, clos_aeq_trans u v ->
        clos_aeq_trans v w -> clos_aeq_trans u w.

    End clos_aeq.

    (** Alpha-equivalence on vectors of terms. *)

    Notation vaeq := (Vforall2 aeq).

    (** Component-wise extension to vectors of a relation on terms,
       modulo [vaeq]. *)

    Definition clos_vaeq {n} R := vaeq @ (Vrel1 (n:=n) R @ vaeq).

  End aeq.

  Arguments aeq_alpha [F X] eq_fun_dec eq_var_dec ens_X var_notin [x u] y _.

End Def.

(****************************************************************************)
(** ** Properties of alpha-equivalence. *)

Module Make (Export L : L_Struct).

  Module Export S := LSubs.Make L.

  (** Notations for alpha-equivalence and related definitions. *)

  Notation aeq := (@aeq F X FOrd.eq_dec XOrd.eq_dec ens_X var_notin).
  Notation aeq_alpha :=
    (@aeq_alpha F X FOrd.eq_dec XOrd.eq_dec ens_X var_notin).
  Notation aeq_top := (@aeq_top F X FOrd.eq_dec XOrd.eq_dec ens_X var_notin).
  Notation clos_aeq := (@clos_aeq F X FOrd.eq_dec XOrd.eq_dec ens_X var_notin).
  Notation clos_aeq_trans :=
    (@clos_aeq_trans F X FOrd.eq_dec XOrd.eq_dec ens_X var_notin).
  Notation clos_vaeq :=
    (@clos_vaeq F X FOrd.eq_dec XOrd.eq_dec ens_X var_notin).

  Notation vaeq := (Vforall2 aeq).
  Infix "~~" := aeq (at level 70).
  Infix "~~~" := vaeq (at level 70).
  Notation "R *" := (clos_aeq_trans R) (at level 35).

  (** [aeq] is the smallest equivalence containing the monotone
  closure of [aeq_top]. *)

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

  (** [aeq] is an equivalence relation. *)

  Global Instance aeq_equiv : Equivalence aeq.

  Proof. rewrite aeq_equiv_mon. apply ec_equiv. Qed.

  (*COQ: cannot be removed?*)
  Global Instance aeq_preorder : PreOrder aeq.

  Proof. split; class. Qed.

  (** [aeq] is monotone. *)

  Global Instance aeq_mon : Monotone aeq.

  Proof. rewrite aeq_equiv_mon. class. Qed.

  (** Term constructors are compatible with [aeq]. *)

  Global Instance App_aeq : Proper (aeq ==> aeq ==> aeq) App.

  Proof.
    intros u1 v1 u1v1 u2 v2 u2v2. trans (App u1 v2).
    apply aeq_app_r. hyp. apply aeq_app_l. hyp.
  Qed.

  Global Instance Lam_aeq : Proper (Logic.eq ==> aeq ==> aeq) Lam.

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

  Global Instance fv_aeq : Proper (aeq ==> Equal) fv.

  Proof.
    induction 1; simpl.
    refl.
    sym. hyp.
    rewrite IHaeq1, IHaeq2. refl.
    rewrite IHaeq. refl.
    rewrite IHaeq. refl.
    rewrite IHaeq. refl.
    rewrite fv_rename; unfold replace.
    case_eq (mem x (fv u)); [rewrite <- mem_iff|rewrite <- not_mem_iff];
      intro hx.
    rewrite remove_add. refl. set_iff. tauto.
    rewrite !remove_equal; auto. refl.
  Qed.

  (** [var] is compatible with [aeq]. *)

  Global Instance var_aeq : Proper (Logic.eq ==> aeq ==> Logic.eq ==> Logic.eq) var.

  Proof.
    intros x x' xx' u u' uu' s s' ss'. subst s'. subst x'. unfold Def.var; ens.
    rewrite uu'. destruct (mem x (fvcodom (remove x (fv u')) s)).
    rewrite uu'. refl. refl.
  Qed.

  (** On variables and function symbols, alpha-equivalence is
  equivalent to equality. *)

  Global Instance var_aeq_l : VarInvL aeq.

  Proof.
    split. intro x.
    cut (forall u v, u ~~ v -> (u = Var x \/ v = Var x) -> u = v). fo.
    induction 1; intro h; try (destruct h; discr). refl. fo. trans v.
    apply IHaeq1. destruct h as [h|h]. auto. subst. right. fo.
    apply IHaeq2. destruct h as [h|h]. subst. left. fo. auto.
  Qed.

  Global Instance var_aeq_r : VarInvR aeq.

  Proof. class. Qed.

  Lemma fun_aeq_l : forall f v, Fun f ~~ v -> Fun f = v.

  Proof.
    intro f. cut (forall u v, u ~~ v -> (u = Fun f \/ v = Fun f) -> u = v). fo.
    induction 1; intro h; try (destruct h; discr). refl. fo. trans v.
    apply IHaeq1. destruct h as [h|h]. auto. subst. right. fo.
    apply IHaeq2. destruct h as [h|h]. subst. left. fo. auto.
  Qed.

  Lemma fun_aeq_r : forall f v, v ~~ Fun f -> v = Fun f.

  Proof. intros x v h. sym. apply fun_aeq_l. sym. hyp. Qed.

  (** Tactic for simplifying alpha-equivalence assumptions on
  variables and function symbols. *)

  Ltac simpl_aeq := repeat
    match goal with
      | h : Var _ ~~ _ |- _ => apply var_aeq_l in h
      | h : _ ~~ Var _ |- _ => apply var_aeq_r in h
      | h : Fun _ ~~ _ |- _ => apply fun_aeq_l in h
      | h : _ ~~ Fun _ |- _ => apply fun_aeq_r in h
    end.

  (** Inversion lemma for alpha-equivalence on an application. *)

  Lemma app_aeq_r : forall t v1 v2, t ~~ App v1 v2 ->
    exists u1 u2, t = App u1 u2 /\ u1 ~~ v1 /\ u2 ~~ v2.

  Proof.
    cut (forall t u, t ~~ u -> forall v1 v2, (t = App v1 v2 \/ u = App v1 v2) ->
      exists u1 u2, u1 ~~ v1 /\ u2 ~~ v2
        /\ (t = App v1 v2 -> u = App u1 u2)
        /\ (u = App v1 v2 -> t = App u1 u2)).
    intros h v u1 u2 e. assert (p : v = App u1 u2 \/ App u1 u2 = App u1 u2).
    tauto. destruct (h _ _ e _ _ p) as [a [b [h1 [h2 [h3 h4]]]]].
    ex a b. intuition.
    induction 1; intros u1 u2 e.
    (* refl *)
    ex u1 u2. firstorder auto with crelations.
    (* sym *)
    rewrite or_sym in e. destruct (IHaeq _ _ e) as [a [b [h1 [h2 [h3 h4]]]]].
    ex a b. fo.
    (* trans *)
    destruct e.
    assert (p1 : u = App u1 u2 \/ v = App u1 u2). tauto.
    destruct (IHaeq1 _ _ p1) as [a [b [h1 [h2 [h3 h4]]]]].
    assert (p2 : v = App a b \/ w = App a b). tauto.
    destruct (IHaeq2 _ _ p2) as [c [d [i1 [i2 [i3 i4]]]]].
    ex c d. split_all; subst; try inversion H4; try inversion H5;
              try inversion H6; try inversion H2; subst; auto;
                try (trans a; hyp); try (trans b; hyp).
    assert (p2 : v = App u1 u2 \/ w = App u1 u2). tauto.
    destruct (IHaeq2 _ _ p2) as [a [b [h1 [h2 [h3 h4]]]]].
    assert (p1 : u = App a b \/ v = App a b). tauto.
    destruct (IHaeq1 _ _ p1) as [c [d [i1 [i2 [i3 i4]]]]].
    ex c d. split_all; subst; try inversion H2; try inversion H4;
              try inversion H5; subst; auto;
                try (trans a; hyp); try (trans b; hyp).
    (* app_l *)
    destruct e as [h|h]; inversion h; subst; clear h.
    ex u' u2. firstorder auto with crelations. ex u u2. firstorder auto with crelations.
    (* app_r *)
    destruct e as [h|h]; inversion h; subst; clear h.
    ex u1 v'. firstorder auto with crelations. ex u1 v. firstorder auto with crelations.
    (* lam *)
    destruct e; discr.
    (* alpha *)
    destruct e; discr.
  Qed.

  Lemma app_aeq_l : forall v1 v2 t, App v1 v2 ~~ t ->
    exists u1 u2, t = App u1 u2 /\ u1 ~~ v1 /\ u2 ~~ v2.

  Proof. intros v1 v2 t e. apply app_aeq_r. sym. hyp. Qed.

  (** [size] is compatible with [aeq]. *)

  Global Instance size_aeq : Proper (aeq ==> Logic.eq) size.

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
    ex (Var x). split. refl. simpl. rewrite inter_empty_l. refl.
    (* fun *)
    ex (Fun f). split. refl. simpl. rewrite inter_empty_l. refl.
    (* app *)
    destruct IHu1 as [v1 [h1 i1]]. destruct IHu2 as [v2 [h2 i2]].
    ex (App v1 v2). split.
    trans (App v1 u2). apply aeq_app_l. hyp. apply aeq_app_r. hyp.
    simpl. rewrite union_inter_1, i1, i2, union_empty_l. refl.
    (* lam *)
    destruct IHu as [v [h i]].
    set (uxs := union (fv v) (union (bv v) xs)).
    set (x' := var_notin uxs). ex (Lam x' (rename x x' v)).
    gen (var_notin_ok uxs). fold x'. unfold uxs. set_iff. intro n. split.
    trans (Lam x v). apply aeq_lam. hyp. apply aeq_alpha. tauto.
    simpl. rewrite bv_rename. 2: tauto. revert i. rewrite inter_sym at 1.
    rewrite !inter_empty. unfold not. intros i z. set_iff. intros [j|j].
    subst z. tauto. intro hz. eapply i. apply hz. hyp.
  Qed.

  (** Compatibility with [aeq] is preserved by [clos_trans]. *)

  Lemma clos_trans_aeq R :
    Proper (aeq ==> aeq ==> impl) R -> Proper (aeq ==> aeq ==> impl) (R!).

  Proof.
    intros R_aeq t t' tt' u u' uu' tu.
    revert t u tu t' tt' u' uu'; induction 1; intros t' tt' u' uu'.
    apply t_step. rewrite <- tt', <- uu'. hyp. trans y; firstorder auto with crelations.
  Qed.

(****************************************************************************)
(** ** Alpha-equivalence on substitutions. *)

  Notation saeq := (subs_rel aeq).

  Global Instance fvcodom_saeq xs : Proper (saeq xs ==> Equal) (fvcodom xs).

  Proof.
    intros s s' ss'. eapply fvcodom_subs_rel_Equal.
    apply fv_aeq. class. class. hyp.
  Qed.

  Global Instance var_saeq x u :
    Proper (saeq (remove x (fv u)) ==> Logic.eq) (var x u).

  Proof. eapply var_subs_rel; class. Qed.

  Arguments var_saeq [x u s s'] _ : rename.

  Lemma subs_saeq u s s' : saeq (fv u) s s' -> subs s u ~~ subs s' u.

  Proof. intro ss'. apply subs_rel_mon_preorder; class. Qed.

  Arguments subs_saeq [u s s'] _.

  Lemma subs1_saeq u s s' : saeq (fv u) s s' -> subs1 s u ~~ subs1 s' u.

  Proof. intro ss'. apply subs1_rel_mon_preorder; class. Qed.

  Arguments subs1_saeq [u s s'] _.

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
    intros xs xs' e [s' [ss' [h1 h2]]]. ex s'. rewrite <- e. auto.
    (* empty *)
    ex id.
    split; try split; intro x; try rewrite bvcod_empty; set_iff; tauto.
    (* add *)
    intros x xs n [s' [ss' [h1 h2]]].
    destruct (aeq_notin_bv ys (s x)) as [u [i1 i2]]. ex (update x u s').

    split. intro y. set_iff. unfold Def.update. eq_dec y x.
    subst y. intros. hyp. intros [i|i]. subst y. tauto. apply ss'. hyp.

    split. rewrite inter_sym, inter_empty. intros y hy. rewrite In_bvcod.
    intros [z [j1 j2]]. revert j1 j2. set_iff. unfold Def.update.
    eq_dec z x.
    subst z. intros _ h'. rewrite inter_empty in i2. eapply i2. apply h'. hyp.
    intros [h3|h3] h4. subst z. tauto. rewrite inter_sym, inter_empty in h1.
    absurd (In y (bvcod xs s')). apply h1. hyp.
    rewrite In_bvcod. ex z. tauto.

    intro y. set_iff. intro hy. unfold Def.update. eq_dec y x.
    subst y. tauto. apply h2. tauto.
  Qed.

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
    apply h. intros x h'. unfold s', Def.restrict; ens.
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
    eapply subs_rel_s. refl. unfold flip. eapply union_subset_2. refl. refl.
    apply h1.
    eapply subs_rel_s. refl. unfold flip. eapply union_subset_1. refl. refl.
    apply h1.
  Qed.

  (** Meta-theorem saying that, for proving [P s -> subs s u ~~ subs s v],
  we can assume w.l.o.g. that the domain of [s] is included in
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
    eapply subs_rel_s. refl. unfold flip. eapply union_subset_2. refl. refl.
    apply h1.
    eapply subs_rel_s. refl. unfold flip. eapply union_subset_1. refl. refl.
    apply h1.
  Qed.

(****************************************************************************)
(** ** Substitution is compatible with alpha-equivalence
(CF, Theorem 2a, page 95, proof pages 100-103).

This is the most difficult theorem when formalizing lambda-calculus
using Curry and Feys approach. The CF paper proof has about 100 lines
and the following Coq proof has about 200 lines, but it could
certainly be shortened by defining tactics for reasoning on free
variables. *)

  Global Instance subs_aeq : Proper (Logic.eq ==> aeq ==> aeq) subs.

  Proof.
    intros s s' ss'. subst s'. intros u u' uu'; revert u u' uu' s.
    (* As CF, we proceed first by induction on the size of [u],
       and second by induction on [u ~~ u']. *)
    intro u; pattern u; apply (induction_ltof1 size); clear u.
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
    revert ha. unfold ltof. simpl. max. hyp.
    (* app_r *)
    simpl. apply aeq_app_r. apply IHuu'. intros a ha a' aa' s'. apply IH.
    revert ha. unfold ltof. simpl. max. hyp.
    (* lam *)
    simpl.
    rewrite (@var_aeq _ _ (Logic.eq_refl x) _ _ uu' _ _ (Logic.eq_refl s)).
    set (x' := var x u' s). set (s' := update x (Var x') s). apply aeq_lam.
    apply IHuu'. intros v hv v' vv' l. apply IH.
    revert hv. unfold ltof. simpl. intro hv. lia. hyp.
    (* alpha *)
    eq_dec x y.
    (* x = y *)
    subst. rewrite rename_id. refl.
    (* x <> y *)
    set (u' := rename x y u).

    assert (pp' : remove x (fv u) [=] remove y (fv u')).
    unfold u'. rewrite fv_rename; unfold replace.
    case_eq (mem x (fv u)); [rewrite <- mem_iff|rewrite <- not_mem_iff];
      intro h. rewrite remove_add. refl. set_iff. intuition.
    rewrite !remove_equal; auto. refl.

    destruct (aeq_notin_bv (add (var y u' s) (add (var x u s)
      (add x (add y (union (fv u) (fvcodom (remove x (fv u)) s)))))) u)
      as [v [h1 h2]]. rewrite inter_sym in h2. revert s h2.
    apply restrict_bvcodom_subs_aeq_prop
      with (ys := fun s => singleton (var y u' s)).

    intros s s'. simpl. rewrite <- pp', union_idem. intro ss'.
    rewrite var_saeq. refl. rewrite <- pp'. hyp.

    intros s s'. simpl. rewrite <- pp', union_idem. intro ss'.
    rewrite (fvcodom_saeq ss'), (var_saeq ss').
    rewrite pp' in ss'. rewrite (var_saeq ss'). refl.

    intro s. simpl. set (x' := var x u s). set (y' := var y u' s).
    set (xs := add y' (add x' (add x (add y (union (fv u)
      (fvcodom (remove x (fv u)) s)))))). rewrite <- pp', union_idem.
    intros hs1 hs2 hs3.
    set (xx's := update x (Var x') s). set (yy's := update y (Var y') s).

    trans (Lam x' (subs xx's v)). apply aeq_lam. apply IH.
    unfold ltof. simpl. lia. hyp.
    unfold u'. trans (Lam y' (subs yy's (rename x y v))).

    2:{ apply aeq_lam. apply IH.
    unfold ltof. rewrite h1, size_rename. simpl. lia.
    apply IH. unfold ltof. rewrite h1. simpl. lia. sym. hyp. }

    rewrite inter_sym, inter_empty in hs3. unfold xs in hs3.
    rewrite <- eqb_false_iff, eqb_sym in n.

    assert (e : rename x y v = subs1 (single x (Var y)) v).
    unfold Def.rename. apply subs1_no_alpha.
    rewrite fvcodom_single, beq_term_var, n.
    simpl. rewrite andb_true_r. destruct (mem x (fv v)). 2: apply inter_empty_r.
    rewrite inter_empty. intros a ha. set_iff. intro e. subst a.
    eapply hs3. apply ha. set_iff. tauto.

    assert (e1 : subs xx's v = subs1 xx's v). apply subs1_no_alpha.
    rewrite inter_empty. intros a ha. rewrite In_fvcodom.
    intros [b [i1 [i2 i3]]]. gen (hs3 _ ha). set_iff. split_all.
    apply H5. rewrite In_fvcodom. ex b. set_iff. rewrite h1.
    revert i3. unfold xx's. unfold Def.update. eq_dec b x.
    subst b. simpl. set_iff. tauto.
    split_all. revert i3. rewrite H6. simpl.
    set_iff. intro h. subst b. rewrite h1 in H4. tauto.

    assert (e2 : subs yy's (rename x y v) = subs1 yy's (rename x y v)).
    apply subs1_no_alpha. rewrite bv_rename.
    2:{ intro h. gen (hs3 _ h). set_iff. tauto. }
    rewrite inter_empty. intros a ha. gen (hs3 _ ha). set_iff. split_all.
    revert H1. rewrite In_fvcodom. intros [b [i1 [i2 i3]]]. revert i2 i3.
    unfold yy's. unfold Def.update. eq_dec b y; simpl; set_iff. auto.
    intros i2 i3. apply H6. rewrite In_fvcodom. ex b. revert i1.
    rewrite h1 in *. rewrite fv_rename; unfold replace.
    destruct (mem x (fv v)); set_iff; split_all. subst b. cong. firstorder auto with set.

    rewrite e1, e2, e. unfold yy's. rewrite subs1_update_single.
    2:{ intro h. gen (hs3 _ h). set_iff. tauto. }
    destruct (In_dec y' (fv (subs1 xx's v))).

    (* In y' (fv (subs1 xx's v)) *)
    rewrite <- e1, fv_subs in i. revert i. simpl. set_iff. rewrite In_domain.
    split_all.

    (* 1 *)
    case_eq (mem y (fvcodom (remove y (fv u')) s)); intro h.
    2:{ revert H0. unfold y', Def.var; ens. rewrite h. rewrite h1 in H.
    tauto. }
    assert (p0 : ~In y' (union (fv u') (fvcodom (remove y (fv u')) s))).
    unfold y', Def.var; ens. rewrite h. apply var_notin_ok.
    destruct (eq_term_dec (xx's y') (Var y')). 2: tauto.
    revert e0. unfold xx's at 1. unfold Def.update at 1. eq_dec y' x.

    (* y' = x *)
    intro e3. inversion e3. rewrite H3, e0. apply aeq_lam. apply aeq_refl_eq.
    apply subs1_seq. intros a ha. unfold xx's, Def.single, Def.update.
    eq_dec a x. rewrite e3, e0. refl.
    eq_dec a y. subst a. rewrite <- h1 in ha. tauto. refl.

    (* y' <> x *)
    absurd (In y' (fv u')). intro h'. apply p0. set_iff. auto.
    unfold u'. rewrite fv_rename; unfold replace. rewrite <- h1 in H0.
    destruct (mem x (fv u)). set_iff. split_all. hyp.

    (* 2 *)
    change (In y' (fvcodom (fv v) xx's)) in H0. revert H0. rewrite In_fvcodom.
    intros [a [i1 [i2 i3]]]. unfold xx's, Def.update in i2, i3.
    revert i2 i3. eq_dec a x.

    (* a = x *)
    subst a. simpl. set_iff. intros i2 i3. rewrite <- i3. apply aeq_lam.
    apply aeq_refl_eq. apply subs1_seq. intros a ha.
    unfold xx's, Def.single, Def.update.
    eq_dec a x. refl. eq_dec a y. subst a. rewrite h1 in H. tauto. refl.

    (* a <> x *)
    intros i2 i3. case_eq (mem y (fvcodom (remove y (fv u')) s)); intro hy.

    absurd (In y' (union (fv u') (fvcodom (remove y (fv u')) s))).
    unfold y', Def.var; ens. rewrite hy. apply var_notin_ok.
    set_iff. right. rewrite In_fvcodom. ex a. set_iff. split_all.
    unfold u'. rewrite fv_rename; unfold replace.
    destruct (mem x (fv u)); rewrite h1.
    set_iff. split_all. hyp. subst a. rewrite <- h1 in i1. tauto.

    assert (p0 : y' = y). unfold y', Def.var; ens. rewrite hy. refl.
    absurd (In y (fvcodom (remove y (fv u')) s)). rewrite not_mem_iff. hyp.
    rewrite In_fvcodom. ex a. set_iff. rewrite p0 in i3. split_all.
    unfold u'. rewrite fv_rename; unfold replace.
    destruct (mem x (fv u)); rewrite h1.
    set_iff. intuition. hyp. subst a. rewrite <- h1 in i1. tauto.

    (* ~In y' (fv (subs1 xx's v)) *)
    trans (Lam y' (rename x' y' (subs1 xx's v))). apply aeq_alpha. hyp.
    apply aeq_lam. unfold Def.rename. rewrite subs1_no_alpha.

    2:{ rewrite fvcodom_single, beq_term_var.
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
    rewrite In_bvcod. ex z. auto. }

    unfold xx's. apply aeq_refl_eq.

    destruct (In_dec x' (fv v)).
    case_eq (mem x (fvcodom (remove x (fv u)) s)); intro hx.
    absurd (In x' (union (fv u) (fvcodom (remove x (fv u)) s))).
    unfold x', Def.var; ens. rewrite hx. apply var_notin_ok.
    set_iff. rewrite h1. auto.
    assert (p : x'=x). unfold x', Def.var; ens. rewrite hx. refl.
    rewrite p, subs1_single_subs1. apply subs1_seq. intros a ha.
    unfold Def.update. eq_dec a x. refl. eq_dec a y.
    subst a. rewrite <- h1 in ha. tauto. refl. rewrite update_eq. refl.
    rewrite fvcodom_update_id, <- h1, not_mem_iff. hyp.

    eq_dec x' y'. rewrite <- e0. rewrite subs1_single_id.
    apply subs1_seq. intros a ha. unfold Def.update.
    eq_dec a x. refl. eq_dec a y.
    subst a. rewrite <- h1 in ha. tauto. refl.

    rewrite subs1_single_update. apply subs1_seq. intros a ha.
    unfold Def.update. eq_dec a x'; eq_dec a x; eq_dec a y;
      try subst a; try subst x; try subst y; auto.
    tauto. rewrite <- h1 in ha. tauto. hyp.
    intro h. case_eq (mem x (fvcodom (remove x (fv u)) s)); intro hx.
    assert (p : ~In x' (union (fv u) (fvcodom (remove x (fv u)) s))).
    unfold x', Def.var; ens. rewrite hx. apply var_notin_ok.
    apply p. set_iff. right. rewrite h1. hyp.
    assert (p : x' = x). unfold x', Def.var; ens. rewrite hx. refl.
    absurd (In x' (fvcodom (remove x (fv u)) s)).
    rewrite p, not_mem_iff. hyp. rewrite h1. hyp.
    intro h. gen (hs3 _ h). set_iff. tauto.
    intro h. gen (hs3 _ h). set_iff. tauto.
  (*SLOW*)Qed.

  (** [fun u v => subs (single x u) v] is compatible with [aeq]. *)

  Global Instance subs_single_aeq :
    Proper (Logic.eq ==> aeq ==> aeq ==> aeq) subs_single.

  Proof.
    intros x x' xx' u u' uu' v v' vv'. subst x'.
    unfold Def.subs_single. rewrite <- vv'. clear v' vv'. apply subs_saeq.
    intros y _. unfold Def.single, Def.update, Def.id. eq_dec y x. hyp. refl.
  Qed.

(****************************************************************************)
(** [comp] is compatible with [saeq]. *)

  Lemma comp_saeq : forall xs s1 t1, saeq xs s1 t1 -> forall s2 t2,
    saeq (fvcod xs s1) s2 t2 -> saeq xs (comp s2 s1) (comp t2 t1).

  Proof.
    intros xs s1 t1 e1 s2 t2 e2 x hx. unfold Def.comp. rewrite (e1 _ hx).
    apply subs_saeq. intros y hy. apply e2. rewrite In_fvcod. ex x.
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

  Lemma subs_comp u s1 s2 : subs s2 (subs s1 u) ~~ subs (comp s2 s1) u.

  Proof.
    set (A := fvcodom (fv u) s1).
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

    2:{ rewrite <- e1. rewrite <- uu' at 2. fold A.
    rewrite empty_subset, union_subset_1 with (s:=A) (s':=union B C),
      <- empty_subset. hyp. }

    apply subs1_saeq. intros x hx. unfold Def.comp1, Def.comp.
    rewrite (e1 _ hx). sym. apply aeq_refl_eq. apply subs1_no_alpha.
    assert (d : bv (s1' x) [<=] bvcod (fv u') s1').
    intros y hy. rewrite In_bvcod. ex x. auto.
    assert (e : fv (s1' x) [<=] fvcod (fv u') s1').
    intros y hy. rewrite In_fvcod. ex x. auto.
    rewrite empty_subset, d, e. rewrite <- e1 at 2. rewrite <- uu' at 2.
    fold D. rewrite union_subset_1 with (s:=D) (s':=B), union_sym,
      <- empty_subset. hyp.
  Qed.

  Lemma single_rename x y u v : x = y \/ ~In y (fv u) ->
    subs (single y v) (rename x y u) ~~ subs (single x v) u.

  Proof.
    intro hy. unfold Def.rename. rewrite subs_comp. apply subs_saeq.
    intros d hd. unfold Def.comp, Def.single. unfold Def.update at -1.
    eq_dec d x; simpl.
    rewrite update_eq. refl.
    unfold Def.update. eq_dec d y. 2: refl.
    subst d. assert (n':x<>y). auto. tauto.
  Qed.

  Lemma rename2 : forall x y z u, x = y \/ ~In y (fv u) ->
    rename y z (rename x y u) ~~ rename x z u.

  Proof. intros x y z u hy. apply single_rename. hyp. Qed.

  Lemma subs_update x y s u : s y = Var y ->
    subs (update x (Var y) s) u ~~ subs (update x (Var x) s) (rename x y u).

  Proof.
    intro h. unfold Def.rename. rewrite subs_comp. apply subs_saeq.
    intros z hz. unfold Def.comp, Def.single. unfold Def.update at -2.
    eq_dec z x; simpl.
    subst. unfold Def.update. eq_dec y x.
    subst. refl.
    rewrite h. refl.
    unfold Def.update. eq_dec z x.
    subst. tauto.
    refl.
  Qed.

(****************************************************************************)
(** Given [u], [fun s => subs s u] is compatible with [subs_rel R (fv u)]. *)

  Lemma subs_rel_mon_preorder_aeq R :
    PreOrder R -> Monotone R -> Proper (aeq ==> aeq ==> impl) R ->
    forall u s s', subs_rel R (fv u) s s' -> R (subs s u) (subs s' u).

  Proof.
    intros R_refl_trans R_mon R_aeq. induction u; intros s s' h.
    (* var *)
    simpl. apply h; simpl. set_iff. refl.
    (* fun *)
    refl.
    (* app *)
    simpl. destruct R_mon.
    rewrite IHu1 with (s:=s) (s':=s'), IHu2 with (s:=s) (s':=s'). refl.
    intros x hx. apply h. simpl. apply union_subset_2. hyp.
    intros x hx. apply h. simpl. apply union_subset_1. hyp.
    (* lam *)
    rewrite subs_seq_restrict, subs_seq_restrict with (s:=s').
    set (xs := fv (Lam x u)).
    set (s1 := restrict xs s). set (s1' := restrict xs s').
    set (ys := union xs (union (fvcodom xs s1) (fvcodom xs s1'))).
    gen (var_notin_ok ys). set (z := var_notin ys). intro hz.
    rewrite aeq_alpha' with (y:=z).
    2:{ revert hz. unfold ys. unfold xs at 1. simpl. set_iff. tauto. }
    set (u' := rename x z u).

    assert (e : remove z (fv u') [=] xs).
    unfold xs, u'. rewrite fv_rename; unfold replace. simpl.
    case_eq (mem x (fv u)); intros hx a; set_iff; split_all; subst a. cong.
    revert hz. unfold ys. unfold xs at 1. simpl. set_iff. tauto.
    rewrite <- not_mem_iff in hx. contr.
    revert hz. unfold ys. unfold xs at 1. simpl. set_iff. tauto.
    
    rewrite subs_lam_no_alpha.
    2:{ rewrite e. revert hz. unfold ys. set_iff. tauto. }
    rewrite subs_lam_no_alpha.
    2:{ rewrite e. revert hz. unfold ys. set_iff. tauto. }

    clear e. mon. unfold u', Def.rename. rewrite !subs_comp. apply IHu.
    intros a ha. unfold Def.single, Def.comp. unfold Def.update at 2.
    unfold Def.update at 3. unfold Def.id. eq_dec a x.

    subst a. simpl. rewrite !update_eq. refl.
    simpl. unfold Def.update. eq_dec a z. refl.
    unfold s1, s1', Def.restrict; ens.
    assert (e : mem a xs = true).
    rewrite <- mem_iff. unfold xs. simpl. set_iff. fo.
    rewrite e. apply h. rewrite mem_iff. hyp.
  Qed.

  Global Instance subs_single_mon_preorder_aeq R :
    PreOrder R -> Monotone R -> Proper (aeq ==> aeq ==> impl) R ->
    Proper (Logic.eq ==> R ==> aeq ==> R) subs_single.

  Proof.
    intros P_qo R_mon R_aeq x x' xx' u u' uu' v v' vv'. subst x'.
    unfold Def.subs_single. rewrite <- vv'. clear v' vv'.
    apply subs_rel_mon_preorder_aeq; class.
    intros y _. unfold Def.single, Def.update, Def.id. eq_dec y x. hyp. refl.
  Qed.

(****************************************************************************)
(** ** Inversion lemma for alpha-equivalence on a lambda. *)

  Lemma lam_aeq_r : forall t x u, t ~~ Lam x u -> exists y v,
    t = Lam y v /\ v ~~ rename x y u /\ (x = y \/ ~In y (fv u)).

  Proof.
    cut (forall t t', t ~~ t' -> forall x u, t = Lam x u \/ t' = Lam x u ->
      exists y v, v ~~ rename x y u /\ (x=y \/ ~In y (fv u))
        /\ (t = Lam x u -> t' = Lam y v) /\ (t' = Lam x u -> t = Lam y v)).
    intros h t x u e. assert (p : t = Lam x u \/  Lam x u = Lam x u).
    auto. destruct (h _ _ e _ _ p) as [y [v i]]. ex y v. tauto.
    induction 1; intros z a e.
    (* refl *)
    ex z a. split. rewrite rename_id. refl. tauto.
    (* sym *)
    rewrite or_sym in e. destruct (IHaeq _ _ e) as [y [w i]]. ex y w. tauto.
    (* trans *)
    destruct e as [e|e].

    assert (p : u = Lam z a \/ v = Lam z a). auto.
    destruct (IHaeq1 _ _ p) as [x [b [i1 [i2 [i3 i4]]]]].
    assert (q : v = Lam x b \/ w = Lam x b). tauto.
    destruct (IHaeq2 _ _ q) as [y [c [j1 [j2 [j3 j4]]]]].
    ex y c. repeat split.

    rewrite j1, i1. apply rename2. hyp.

    destruct i2; destruct j2.
    left. trans x; auto.
    right. rewrite H1, rename_id in i1. rewrite <- i1. hyp.
    right. rewrite <- H2. hyp.
    eq_dec z y. auto. right. intro hy. apply H2.
    rewrite i1, fv_rename; unfold replace.
    destruct (mem z (fv a)); set_iff; auto.

    tauto. intro hw. subst u w. tauto.

    assert (p : v = Lam z a \/ w = Lam z a). auto.
    destruct (IHaeq2 _ _ p) as [x [b [i1 [i2 [i3 i4]]]]].
    assert (q : u = Lam x b \/ v = Lam x b). tauto.
    destruct (IHaeq1 _ _ q) as [y [c [j1 [j2 [j3 j4]]]]].
    ex y c. repeat split.

    rewrite j1, i1. apply rename2. hyp.

    destruct i2; destruct j2.
    left. trans x; auto.
    right. rewrite H1, rename_id in i1. rewrite <- i1. hyp.
    right. rewrite <- H2. hyp.
    eq_dec z y. auto. right. intro hy. apply H2.
    rewrite i1, fv_rename; unfold replace.
    destruct (mem z (fv a)); set_iff; auto.

    intro hu. subst u w. tauto. tauto.
    (* app_l *)
    destruct e; discr.
    (* app_r *)
    destruct e; discr.
    (* lam *)
    destruct e as [e|e]; inversion e; subst.
    ex z u'. rewrite rename_id. intuition auto with *.
    ex z u. rewrite rename_id. intuition.
    (* alpha *)
    destruct e as [e|e].
    inversion e. subst. ex y (rename z y a). split_all. refl.
    inversion e. subst. ex x u. rewrite rename2, rename_id. 2: auto.
    split_all. refl. rewrite fv_rename; unfold replace.
    case_eq (mem x (fv u));
      [rewrite <- mem_iff|rewrite <- not_mem_iff]; intro hx.
    right. set_iff. intros [h|h]. subst z. tauto. tauto.
    auto.
  Qed.

  Lemma lam_aeq_l : forall t x u, Lam x u ~~ t -> exists y v,
    t = Lam y v /\ v ~~ rename x y u /\ (x = y \/ ~In y (fv u)).

  Proof. intros t x u h. apply lam_aeq_r. sym. hyp. Qed.

  Lemma permut_rename v x y u :
    v ~~ rename x y u -> (x = y \/ ~In y (fv u)) ->
    u ~~ rename y x v /\ (x = y \/ ~In x (fv v)).

  Proof.
    intros e h. split.
    rewrite e, rename2, rename_id. refl. hyp.
    rewrite e, fv_rename; unfold replace. destruct h. auto.
    subst. auto.
    case_eq (mem x (fv u)); intro i.
    2:{ rewrite <- not_mem_iff in i. auto. }
    right. set_iff. rewrite <- mem_iff in i. split_all. subst. contr.
  Qed.

  Arguments permut_rename [v x y u] _ _.

  Ltac permut_rename h :=
    apply permut_rename in h;
    [ let h1 := fresh "i" in let h2 := fresh "i" in destruct h as [h1 h2]
    | try tauto].

(****************************************************************************)
(** Inversion tactic for alpha-equivalence. *)

  Ltac inv_aeq_0 h :=
    let u1 := fresh "u" in let u2 := fresh "u" in let x := fresh "x" in
      let i1 := fresh "i" in let i2 := fresh "i" in let i3 := fresh "i" in
        match type of h with
          | Var _ ~~ _ => apply var_aeq_l in h
          | _ ~~ Var _ => apply var_aeq_r in h
          | Fun _ ~~ _ => apply fun_aeq_l in h
          | _ ~~ Fun _ => apply fun_aeq_r in h
          | App _ _ ~~ _ => destruct (app_aeq_l h) as [u1 [u2 [i1 [i2 i3]]]]
          | _ ~~ App _ _ => destruct (app_aeq_r h) as [u1 [u2 [i1 [i2 i3]]]]
          | Lam _ _ ~~ _ => destruct (lam_aeq_l h) as [x [u1 [i1 [i2 i3]]]]
          | _ ~~ Lam _ _ => destruct (lam_aeq_r h) as [x [u1 [i1 [i2 i3]]]]
        end; simpl_aeq.

(****************************************************************************)
(** Compatibility of some basic predicates/functions with [aeq]. *)

  Global Instance not_lam_aeq : Proper (aeq ==> impl) not_lam.

  Proof.
    intros u v uv hu x a hv. subst.
    inv_aeq_0 uv; clear uv; subst. eapply hu. refl.
  Qed.

  Global Instance head_aeq : Proper (aeq ==> aeq) head.

  Proof.
    intros u v uv. revert u v uv.
    induction u; intros v uv; inv_aeq_0 uv; subst; simpl.
    refl. refl. firstorder auto with crelations. fo.
  Qed.

(****************************************************************************)
(** ** Properties of [clos_aeq]. *)

  Lemma clos_aeq_intro_refl (R : rel Te) t u : R t u -> clos_aeq R t u.

  Proof. intro tu. eapply clos_aeq_intro. refl. refl. hyp. Qed.

  Arguments clos_aeq_intro_refl [R t u] _ : rename.

  Lemma clos_aeq_inv R t u :
    clos_aeq R t u -> exists t' u', t ~~ t' /\ u ~~ u' /\ R t' u'.

  Proof. intro tu. inversion tu; clear tu; subst. ex u' v'. intuition. Qed.

  Lemma clos_aeq_eq R : clos_aeq R == aeq @ (R @ aeq).

  Proof.
    split.
    (* << *)
    intros t u tu.
    destruct (clos_aeq_inv tu) as [t' [u' [tt' [uu' t'u']]]]; clear tu.
    ex t'. intuition. ex u'. intuition auto with *.
    (* >> *)
    intros t u [t' [tt' [u' [t'u' u'u]]]]. eapply clos_aeq_intro.
    apply tt'. sym. apply u'u. hyp.
  Qed.

  Lemma incl_clos_aeq R : R << clos_aeq R.

  Proof.
    intros u v uv. apply clos_aeq_intro with (u':=u) (v':=v).
    refl. refl. hyp.
  Qed.

  (** Alpha-closure is compatible with relation inclusion/equivalence. *)

  Global Instance clos_aeq_incl : Proper (inclusion ==> inclusion) clos_aeq.

  Proof.
    intros R S RS u v uv. inversion uv; subst.
    apply clos_aeq_intro with (u':=u') (v':=v'); fo.
  Qed.

  Global Instance clos_aeq_same : Proper (same ==> same) clos_aeq.

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

  (** Alpha-closure is compatible with alpha-equivalence. *)

  Global Instance clos_aeq_aeq R : Proper (aeq ==> aeq ==> impl) (clos_aeq R).

  Proof.
    intros u u' uu' v v' vv' h. inversion h; subst.
    eapply clos_aeq_intro.
    trans u. hyp. apply H.
    trans v. hyp. apply H0.
    hyp.
  Qed.

  (** Alpha-closure preserves monotony. *)

  Global Instance clos_aeq_mon R : Monotone R -> Monotone (clos_aeq R).

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

  (** [clos_mon (clos_aeq R)] is included in [clos_aeq (clos_mon R)]. *)

  Lemma clos_mon_aeq_incl R : clos_mon (clos_aeq R) << clos_aeq (clos_mon R).

  Proof.
    apply clos_mon_min. apply clos_aeq_mon. apply monotone_clos_mon.
    apply clos_aeq_incl. intros u v uv. apply m_step. hyp.
  Qed.

  (** Alpha-closure preserves stability by substitution. *)

  Global Instance subs_clos_aeq R : Proper (Logic.eq ==> R ==> clos_aeq R) subs ->
    Proper (Logic.eq ==> clos_aeq R ==> clos_aeq R) subs.

  Proof.
    intros h s s' ss' u u' uu'. subst s'. inversion uu'; clear uu'; subst.
    rewrite H, H0. apply h. refl. hyp.
  Qed.

  (* Note that the previous lemma cannot be used to prove the
  following one since [clos_subs R] is NOT stable by substitution
  since substitution composition is correct modulo alpha-equivalence
  only. *)

  Global Instance subs_clos_aeq_subs R :
    Proper
      (Logic.eq ==> clos_aeq (clos_subs R) ==> clos_aeq (clos_subs R)) subs.

  Proof.
    intros s s' ss' t u tu. subst s'.
    inversion tu; inversion H1; subst; clear tu H1.
    (*VERY SLOW*)rewrite H0, H, 2!subs_comp.
    apply clos_aeq_intro_refl. apply subs_step. hyp.
  Qed.

  (** [clos_aeq o clos_mon] preserves stability by substitution. *)

  Global Instance subs_clos_aeq_mon R : Proper (Logic.eq ==> R ==> clos_aeq R) subs ->
    Proper (Logic.eq ==> clos_aeq (clos_mon R) ==> clos_aeq (clos_mon R)) subs.

  Proof.
    intros h s s' ss' u v uv. subst s'. revert u v uv s.
    (* We proceed by induction on the size of [u]. *)
    intro u; pattern u; apply (induction_ltof1 size); clear u.
    intros u IH v uv s. inversion uv; clear uv; subst. rewrite H, H0.
    (* We now proceed by case on [clos_mon R u' v']. *)
    inversion H1; clear H1; subst.
    (* top *)
    apply clos_mon_aeq_incl. apply m_step. apply h. refl. hyp.
    (* app_l *)
    simpl. mon. apply IH. unfold ltof. rewrite H. simpl. max.
    apply incl_clos_aeq. hyp.
    (* app_r *)
    simpl. mon. apply IH. unfold ltof. rewrite H. simpl. max.
    apply incl_clos_aeq. hyp.
    (* lam *)
    (* We rename [x] into some variable [k] not in [xs] so that [subs s]
       makes no alpha-conversion. *)
    set (xs := union (union (fv u0) (fvcodom (remove x (fv u0)) s))
                     (union (fv u'0) (fvcodom (remove x (fv u'0)) s))).
    set (k := var_notin xs).
    gen (var_notin_ok xs). fold k. unfold xs. set_iff. intro hk.
    rewrite (aeq_alpha k). 2: tauto. rewrite (@aeq_alpha x _ k). 2: tauto.
    rewrite subs_lam_no_alpha. 2: rewrite remove_fv_rename; tauto.
    rewrite subs_lam_no_alpha. 2: rewrite remove_fv_rename; tauto.
    mon. apply IH. unfold ltof. rewrite size_rename, H. simpl. lia.
    apply IH. unfold ltof. rewrite H. simpl. lia.
    apply incl_clos_aeq. hyp.
  Qed.

  (** Alpha-closure preserves free variables. *)

  Global Instance fv_clos_aeq : forall R,
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

  (** Alpha-closure preserves termination of size-decreasing relations. *)

  Lemma clos_aeq_wf_size : forall R, R << transp (ltof size) -> WF (clos_aeq R).

  Proof.
    intros R h. apply (WF_incl (transp (ltof size))).
    2: apply transp_ltof_wf.
    intros t u tu. inversion tu; clear tu; subst. unfold transp, ltof.
    rewrite H, H0. apply h. hyp.
  Qed.

(****************************************************************************)
(** ** Compatibility of [apps] with [aeq] and [vaeq]. *)

  Global Instance apps_aeq : forall n, Proper (aeq ==> vaeq ==> aeq) (@apps n).

  Proof.
    intros n t t' tt' us us' usus'. revert n us us' usus' t t' tt'.
    induction us; simpl; intros us' usus' t t' tt'.
    VOtac. simpl. hyp.
    VSntac us'. simpl. rewrite H in usus'. destruct usus' as [h1 h2].
    apply IHus. hyp. rewrite tt', h1. refl.
  Qed.

  Lemma apps_aeq_r : forall n (vs : Tes n) v t, t ~~ apps v vs ->
    exists u us, t = apps u us /\ u ~~ v /\ vaeq us vs.

  Proof.
    induction vs; simpl; intros v t a.
    (* nil *)
    ex t (@Vnil Te). simpl. intuition auto with *.
    (* cons *)
    rename h into w. destruct (IHvs _ _ a) as [u [us [h1 [h2 h3]]]].
    inv_aeq_0 h2; clear h2; subst. ex u0 (Vcons u1 us). simpl.
    rewrite Vforall2_cons_eq. intuition.
  Qed.

  Arguments apps_aeq_r [n vs v t0] _ : rename.

  Lemma apps_aeq_l : forall n (vs : Tes n) v t, apps v vs ~~ t ->
    exists u us, t = apps u us /\ u ~~ v /\ vaeq us vs.

  Proof. intros n vs v t e. apply apps_aeq_r. hyp. Qed.

  Arguments apps_aeq_l [n vs v t0] _ : rename.

(****************************************************************************)
(** Extended inversion tactic for alpha-equivalence. *)

  Ltac inv_aeq h :=
    let u := fresh "u" in let us := fresh "us" in
      let i1 := fresh "i" in let i2 := fresh "i" in let i3 := fresh "i" in
        match type of h with
          | apps _ _ ~~ _ => destruct (apps_aeq_l h) as [u [us [i1 [i2 i3]]]]
          | _ ~~ apps _ _ => destruct (apps_aeq_r h) as [u [us [i1 [i2 i3]]]]
        end || inv_aeq_0 h; simpl_aeq.

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

      Variable S_aeq : Proper (aeq ==> aeq ==> impl) S.

      Global Instance atc_aeq : Proper (aeq ==> aeq ==> impl) (S*).

      Proof.
        intros x x' xx' y y' yy' h. revert x y h x' xx' y' yy'.
        induction 1; intros x' xx' y' yy'.
        apply at_step. rewrite <- xx', <- yy'. hyp.
        apply at_aeq. rewrite <- xx', <- yy'. hyp.
        trans v. apply IHh1. hyp. refl. apply IHh2. refl. hyp.
      Qed.

      (*COQ: if removed, Coq fails in LComp*)
      Global Instance atc_aeq_iff : Proper (aeq ==> aeq ==> iff) (S*).

      Proof.
        intros x x' xx' y y' yy'. split; intro h; eapply atc_aeq.
        apply xx'. apply yy'. hyp. sym. apply xx'. sym. apply yy'. hyp.
      Qed.

      (** Inversion lemma for [clos_aeq_trans]. *)

      Lemma clos_aeq_trans_inv : forall t u,
        S* t u -> t ~~ u \/ exists v, S t v /\ S* v u.

      Proof.
        induction 1. firstorder auto with crelations. fo. destruct IHclos_aeq_trans1 as [h|[t [h1 h2]]].
        destruct IHclos_aeq_trans2 as [i|[t' [i1 i2]]].
        left. trans v; hyp.
        right. ex t'. rewrite h. auto.
        right. ex t. split. hyp. trans v; hyp.
      Qed.

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

(*REMOVE?*)
      Global Instance rename_atc :
        Proper (Logic.eq ==> Logic.eq ==> S* ==> S*) rename.

      Proof.
        intros x x' xx' y y' yy' u u' uu'. unfold Def.rename.
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

    (** A predicate is stable by [S*] if it is stable by [~~] and [S]. *)

    Global Instance proper_atc P : Proper (aeq ==> impl) P ->
      Proper (S ==> impl) P -> Proper (S* ==> impl) P.

    Proof.
      intros P_aeq P_S_aeq u v uv hu; revert u v uv hu. induction 1; intro hu.
      rewrite <- H. hyp.
      rewrite <- H. hyp.
      tauto.
    Qed.

  End atc_props.

(*FIXME: some properties are similar to clos_aeq => factorize?*)
(****************************************************************************)
(** ** Properties of [clos_vaeq]. *)

  Section clos_vaeq.

    Variable R : relation Te.
    Infix "->R" := R (at level 70).

    Notation R_aeq := (clos_aeq R) (only parsing).
    Infix "=>R" := (clos_aeq R) (at level 70).

    Infix "==>R" := (clos_vaeq R) (at level 70).

    Lemma clos_vaeq_cons : forall u v n (us vs : Tes n),
      Vcons u us ==>R Vcons v vs
      <-> (u =>R v /\ us ~~~ vs) \/ (u ~~ v /\ us ==>R vs).

    Proof.
      intros u v n us vs. split.

      intros [x [uusx [y [xy yvvs]]]]. revert uusx yvvs xy. VSntac x. VSntac y.
      rewrite !Vforall2_cons_eq. intros [h1 h2] [i1 i2] h. inversion h.
      left. subst x0 y0 x'. (*VERY SLOW*)rewrite h1, <- i1, h2, H5, i2. split.
      apply incl_clos_aeq. hyp. refl.
      right. subst x0 y0 y'. rewrite h1, H4, i1. split. refl. 
      ex (Vtail x). intuition. ex (Vtail y). intuition.

      intros [[h1 h2]|[h1 h2]].
      inversion h1; subst. ex (Vcons u' us). split.
      rewrite Vforall2_cons_eq. intuition auto with *. ex (Vcons v' us). split.
      apply Vrel1_cons_intro. auto. rewrite Vforall2_cons_eq. intuition auto with *.

      destruct h2 as [us' [usus' [vs' [us'vs' vs'vs]]]].
      ex (Vcons v us'). rewrite Vforall2_cons_eq. intuition.
      ex (Vcons v vs'). rewrite Vforall2_cons_eq. intuition auto with *.
      apply Vrel1_cons_intro. right. intuition.
    Qed.

    (** [clos_vaeq] is compatible with [vaeq]. *)

    Global Instance clos_vaeq_vaeq n :
      Proper (vaeq ==> vaeq ==> impl) (clos_vaeq (n:=n) R).

    Proof.
      intros us us' usus' ws ws' wsws' [vs [usvs [xs [bvsxs xsws]]]].
      ex vs. split. trans us; hyp. ex xs. intuition. trans ws; hyp.
    Qed.

    Lemma clos_vaeq_sub : forall n (us vs : Tes n) p q (h : p+q<=n),
      us ==>R vs -> Vsub us h ~~~ Vsub vs h \/ Vsub us h ==>R Vsub vs h.

    Proof.
      intros n us vs p q h [us' [usus' [vs' [r vsvs']]]]; symmetry in vsvs'.
      destruct (Vrel1_sub h r).
      left. rewrite (Vforall2_sub h usus'), (Vforall2_sub h vsvs'), H.
      refl.
      right. ex (Vsub us' h). split. apply Vforall2_sub. hyp.
      ex (Vsub vs' h). split. hyp. apply Vforall2_sub. hyp.
    Qed.

    Arguments clos_vaeq_sub [n us vs p q] _ _.

    (** A vector of terms is strongly normalizing for [clos_vaeq] if
    every component is strongly normalizing for [R_aeq]. *)

    Lemma sn_clos_vaeq_intro : forall n (us : Tes n),
      Vforall (SN R_aeq) us -> SN (clos_vaeq R) us.

    Proof.
      intros n x hx.
      (* We have [SN (Vrel1 R_aeq) x] since [Vforall (SN R_aeq) x]. *)
      cut (SN (Vrel1 R_aeq) x). 2: apply Vforall_SN_rel1; hyp.
      (* We can therefore proceed by well-founded induction on
      [Vrel1 R_aeq]. *)
      induction 1. apply SN_intro. intros y [x' [xx' [y' [x'y' y'y]]]].
      (* We have [x' = Vcast (Vapp x'i (Vcons a' x'j)) k0],
      [y' = Vcast (Vapp x'i (Vcons b' x'j)) k0] and [a' ->b b']. *)
      destruct (Vrel1_app_impl x'y')
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
      assert (l : i<n). lia.
      (* We now prove that [a ~~ a']. *)
      assert (aa' : a ~~ a').
      assert (s1 : a = Vnth x l). rewrite ex, Vnth_cast, Vnth_app.
      destruct (Compare_dec.le_gt_dec i i). 2: lia.
      rewrite Vnth_cons_head. refl. lia.
      assert (s2 : a' = Vnth x' l). rewrite ex', Vnth_cast, Vnth_app.
      destruct (Compare_dec.le_gt_dec i i). 2: lia.
      rewrite Vnth_cons_head. refl. lia.
      rewrite s1, s2. apply Vforall2_elim_nth. hyp.
      (* We now prove that [b ~~ b']. *)
      assert (bb' : b ~~ b').
      assert (t1 : b = Vnth y l). rewrite ey, Vnth_cast, Vnth_app.
      destruct (Compare_dec.le_gt_dec i i). 2: lia.
      rewrite Vnth_cons_head. refl. lia.
      assert (t2 : b' = Vnth y' l). rewrite ey', Vnth_cast, Vnth_app.
      destruct (Compare_dec.le_gt_dec i i). 2: lia.
      rewrite Vnth_cons_head. refl. lia.
      rewrite t1, t2. apply Vforall2_elim_nth. hyp.
      (* We now prove that [y ~~~ Vcast (Vapp xi (Vcons b xj)) k0]. *)
      assert (h :  y ~~~ Vcast (Vapp xi (Vcons b xj)) k0).
      rewrite ex, ex', Vforall2_cast in xx'.
      rewrite ey, ey', Vforall2_cast in y'y.
      trans (Vcast (Vapp x'i (Vcons b x'j)) k0).
      (* left *)
      apply Vforall2_intro_nth. intros k hk.
      rewrite ey, 2!Vnth_cast, 2!Vnth_app.
      destruct (Compare_dec.le_gt_dec i k).
      rewrite 2!Vnth_cons. destruct (NatUtil.lt_ge_dec 0 (k-i)). 2: refl.
      apply Vforall2_elim_nth. eapply Vforall2_cons_elim.
      eapply Vforall2_app_elim_r. sym. apply y'y.
      apply Vforall2_elim_nth. eapply Vforall2_app_elim_l. sym. apply y'y.
      (* right *)
      apply Vforall2_intro_nth. intros k hk. rewrite 2!Vnth_cast, 2!Vnth_app.
      destruct (Compare_dec.le_gt_dec i k).
      rewrite 2!Vnth_cons. destruct (NatUtil.lt_ge_dec 0 (k-i)). 2: refl.
      apply Vforall2_elim_nth. eapply Vforall2_cons_elim.
      eapply Vforall2_app_elim_r. sym. apply xx'.
      apply Vforall2_elim_nth. eapply Vforall2_app_elim_l. sym. apply xx'.
      (* We now prove that
      [Vrel1 R_aeq x (Vcast (Vapp xi (Vcons b xj)) k0)]. *)
      assert (r : Vrel1 R_aeq x (Vcast (Vapp xi (Vcons b xj)) k0)).
      rewrite ex. apply Vrel1_cast_intro. apply Vrel1_app_intro_l.
      apply Vrel1_cons_intro.
      left. rewrite aa', bb'. intuition. apply incl_clos_aeq. hyp.
      (* We can now end the proof. *)
      rewrite h. apply H0. hyp. apply SN_rel1_forall. apply H. hyp.
    Qed.

    Lemma sn_clos_vaeq_elim : forall n i (hi : i<n) (us : Tes n),
      SN (clos_vaeq R) us -> SN R_aeq (Vnth us hi).

    Proof.
      intros n i hi us hus. elim hus; clear us hus. intros us h1 h2.
      apply SN_intro. intros ui' uiui'.
      destruct (clos_aeq_inv uiui') as [vi [vi' [uivi [ui'vi' vivi']]]];
        clear uiui'. rewrite <- (Vnth_replace hi hi us). apply h2.

      ex (Vreplace us hi vi). split.
      apply Vforall2_intro_nth. intros j jn. destruct (eq_nat_dec j i).
      subst j. rewrite Vnth_replace. rewrite (Vnth_eq _ jn hi); auto.
      rewrite Vnth_replace_neq. refl. lia.

      ex (Vreplace us hi vi'). split.
      rewrite Vrel1_nth_iff. ex i hi. split.
      rewrite !Vnth_replace. hyp.
      intros j jn jni. rewrite !Vnth_replace_neq; auto.

      apply Vforall2_intro_nth. intros j jn. destruct (eq_nat_dec j i).
      subst j. rewrite !Vnth_replace. hyp.
      rewrite !Vnth_replace_neq; auto. refl.
    Qed.

  End clos_vaeq.

  (** [clos_vaeq] is compatible with [inclusion] and [same]. *)

  Global Instance clos_vaeq_incl n : Proper (incl ==> incl) (@clos_vaeq n).

  Proof. intros R R' RR'. unfold Def.clos_vaeq. rewrite RR'. refl. Qed.

  Global Instance clos_vaeq_same n : Proper (same ==> same) (@clos_vaeq n).

  Proof. intros R R' RR'. unfold Def.clos_vaeq. rewrite RR'. refl. Qed.

  (** [clos_vaeq] distributes over [union]. *)

  Lemma clos_vaeq_union n R S :
    @clos_vaeq n (R U S) == @clos_vaeq n R U @clos_vaeq n S.

  Proof.
    unfold Def.clos_vaeq. rewrite Vrel1_union, comp_union_l, comp_union_r. refl.
  Qed.

End Make.
