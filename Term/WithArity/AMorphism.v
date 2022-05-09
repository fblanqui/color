(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-05-07

algebra morphisms
*)

Set Implicit Arguments.

From Coq Require Import List Morphisms Setoid.
From CoLoR Require Import LogicUtil ATrs VecUtil RelUtil SN ARules SetUtil
     NatUtil.

Import List.

Section Morphism.

(***********************************************************************)
(** we assume given a morphism between two signatures S1 and S2 *)

  Variables S1 S2 : Signature.

  Variables (F : S1 -> S2) (HF : forall f, arity f = arity (F f)).

(***********************************************************************)
(** translation of terms in S1 into terms in S2 *)

  Fixpoint Ft (t : term S1) : term S2 :=
    match t with
      | Var x => Var x
      | Fun f ts => Fun (F f) (Vcast (Vmap Ft ts) (HF f))
    end.

  Definition Fv := Vmap Ft.

(***********************************************************************)
(** translation of contexts in S1 into contexts in S2 *)

  Lemma Fc_aux : forall i j n n', i+S j=n -> n=n' -> i+S j=n'.

  Proof. lia. Qed.

  Arguments Fc_aux [i j n n'] _ _.

  Fixpoint Fc (c : context S1) : context S2 :=
    match c with
      | Hole => Hole
      | @Cont _ f _ _ e v1 c' v2 =>
        Cont (F f) (Fc_aux e (HF f)) (Fv v1) (Fc c') (Fv v2)
    end.

  Lemma Ft_fill : forall t c, Ft (fill c t) = fill (Fc c) (Ft t).

  Proof.
    induction c; intros. refl. simpl. apply args_eq.
    rewrite Vmap_cast, Vmap_app. simpl. rewrite Vcast_cast, IHc. apply Vcast_pi.
  Qed.

(***********************************************************************)
(* translation of rules in S1 into rules in S2 *)
 
  Definition Fr (a : rule S1) := let (l,r) := a in mkRule (Ft l) (Ft r).

  Definition Fl := map Fr.

  Definition Frs := image Fr.

  #[global] Instance Frs_equiv : Proper (equiv ==> equiv) Frs.

  Proof. fo. Qed.

  Lemma Rules_Fl : forall R, of_list (Fl R) [=] Frs (of_list R).

  Proof.
    induction R; simpl; intros. fo. rewrite !of_cons, IHR.
    unfold Frs. rewrite image_add. refl.
  Qed.

  Lemma incl_Frs : forall R S, R [<=] S -> Frs R [<=] Frs S.

  Proof. intros. intros a' H0. do 2 destruct H0. subst. exists x. fo. Qed.

  Lemma Frs_app : forall R S a, Frs (union R S) a <-> Frs R a \/ Frs S a.

  Proof.
    intuition. do 3 destruct H; subst. left. exists x. auto. right.
    exists x. auto.
    destruct H0. destruct H. subst. exists x. intuition. left. hyp.
    destruct H0. destruct H. subst. exists x. intuition. right. hyp.
  Qed.
 
(***********************************************************************)
(* translation of substitutions in S1 into substitutions in S2 *)

  Definition Fs (s : substitution S1) x := Ft (s x).

  Lemma Ft_sub : forall s t, Ft (sub s t) = sub (Fs s) (Ft t).

  Proof.
    intros s t. pattern t. apply term_ind
    with (Q := fun n (ts : vector (term S1) n) =>
      Fv (Vmap (sub s) ts) = Vmap (sub (Fs s)) (Fv ts));
    clear t; intros.
    refl. simpl. apply args_eq. unfold Fv in H.
    rewrite H, Vmap_cast. refl.
    refl. simpl. rewrite H, H0. refl.
  Qed.

(***********************************************************************)
(** F preserves rewriting *)

  Lemma Fred : forall R t u, red R t u -> red (Frs R) (Ft t) (Ft u).

  Proof.
    intros. redtac. unfold red. subst.
    exists (Ft l). exists (Ft r). exists (Fc c). exists (Fs s). intuition.
    change (Frs R (Fr (mkRule l r))). exists (mkRule l r). intuition.
    rewrite Ft_fill, Ft_sub. refl.
    rewrite Ft_fill, Ft_sub. refl.
  Qed.

  Lemma Fhd_red : forall R t u, hd_red R t u -> hd_red (Frs R) (Ft t) (Ft u).

  Proof.
    intros. redtac. unfold hd_red. subst.
    exists (Ft l). exists (Ft r). exists (Fs s). intuition.
    change (Frs R (Fr (mkRule l r))). exists (mkRule l r). intuition.
    rewrite Ft_sub. refl. rewrite Ft_sub. refl.
  Qed.

  Lemma Fred_rtc : forall R t u, red R # t u -> red (Frs R) # (Ft t) (Ft u).

  Proof.
    induction 1; intros. apply rt_step. apply Fred. hyp.
    apply rt_refl. apply rt_trans with (Ft y); auto.
  Qed.

  Lemma Fred_mod : forall E R t u,
    red_mod E R t u -> red_mod (Frs E) (Frs R) (Ft t) (Ft u).

  Proof.
    intros. redtac. unfold red_mod. exists (Ft t0). split.
    apply Fred_rtc. hyp. apply Fred. subst. apply red_rule. hyp.
  Qed.

  Lemma Fhd_red_mod : forall E R t u,
    hd_red_mod E R t u -> hd_red_mod (Frs E) (Frs R) (Ft t) (Ft u).

  Proof.
    intros. redtac. unfold hd_red_mod. exists (Ft t0). split.
    apply Fred_rtc. hyp. apply Fhd_red. subst. apply hd_red_rule. hyp.
  Qed.

(***********************************************************************)
(** reflexion of termination *)

  Lemma Fred_WF : forall R, WF (red (Frs R)) -> WF (red R).

  Proof.
    intros R H x. geneq H x (Ft x). induction 1; intros.
    apply SN_intro; intros.
    eapply H0. subst x. apply Fred. apply H2. refl.
  Qed.

  Lemma Fred_mod_WF : forall E R,
    WF (red_mod (Frs E) (Frs R)) -> WF (red_mod E R).

  Proof.
    intros E R H x. geneq H x (Ft x). induction 1; intros.
    apply SN_intro; intros.
    eapply H0. subst x. apply Fred_mod. apply H2. refl.
  Qed.

  Lemma Fhd_red_mod_WF : forall E R,
    WF (hd_red_mod (Frs E) (Frs R)) -> WF (hd_red_mod E R).

  Proof.
    intros E R H x. geneq H x (Ft x). induction 1; intros.
    apply SN_intro; intros.
    eapply H0. subst x. apply Fhd_red_mod. apply H2. refl.
  Qed.

(***********************************************************************)
(** finite versions *)

  Import ATrs.

  Lemma Fred_WF_fin : forall R, WF (red (Fl R)) -> WF (red R).

  Proof. intro. rewrite <- !red_Rules, Rules_Fl. apply Fred_WF. Qed.

  Lemma Fred_mod_WF_fin : forall E R,
    WF (red_mod (Fl E) (Fl R)) -> WF (red_mod E R).

  Proof.
    intros E R. rewrite <- !red_mod_Rules, !Rules_Fl. apply Fred_mod_WF.
  Qed.

  Lemma Fhd_red_mod_WF_fin : forall E R,
    WF (hd_red_mod (Fl E) (Fl R)) -> WF (hd_red_mod E R).

  Proof.
    intros E R. rewrite <- !hd_red_mod_Rules, !Rules_Fl. apply Fhd_red_mod_WF.
  Qed.

End Morphism.

Arguments Ft [S1 S2 F] _ _.
Arguments Fv [S1 S2 F] _ [n] _.
Arguments Fc [S1 S2 F] _ _.
Arguments Fs [S1 S2 F] _ _ _.
Arguments Fr [S1 S2 F] _ _.
Arguments Fl [S1 S2 F] _ _.
Arguments Frs [S1 S2 F] _ _ _.

(***********************************************************************)
(** preservation of termination *)

Import ARules.

Section Preserv.

  Variables S1 S2 : Signature.
  Variables (F : S1 -> S2) (HF : forall f, arity f = arity (F f)).
  Variables (G : S2 -> S1) (HG : forall f, arity f = arity (G f)).
  Variables (E R : set (rule S1)) (E' R' : set (rule S2)).
  Variables (hyp1 : Frs HG E' [<=] E) (hyp2 : Frs HF E [<=] E').
  Variables (hyp3 : Frs HG R' [<=] R) (hyp4 : Frs HF R [<=] R').

  Lemma WF_Fred : WF (red R) -> WF (red (Frs HF R)).

  Proof.
    intro. eapply WF_incl. eapply red_incl. apply hyp4.
    eapply Fred_WF. eapply WF_incl. eapply red_incl. apply hyp3. hyp.
  Qed.

  Lemma WF_Fred_mod : WF (red_mod E R) -> WF (red_mod (Frs HF E) (Frs HF R)).

  Proof.
    intro. eapply WF_incl. eapply red_mod_incl. apply hyp2. apply hyp4.
    eapply Fred_mod_WF. eapply WF_incl. eapply red_mod_incl. apply hyp1.
    apply hyp3. hyp.
  Qed.

  Lemma WF_Fhd_red_mod :
    WF (hd_red_mod E R) -> WF (hd_red_mod (Frs HF E) (Frs HF R)).

  Proof.
    intro. eapply WF_incl. eapply hd_red_mod_incl. apply hyp2. apply hyp4.
    eapply Fhd_red_mod_WF. eapply WF_incl. eapply hd_red_mod_incl. apply hyp1.
    apply hyp3. hyp.
  Qed.

End Preserv.

(***********************************************************************)
(** epimorphism *)

Section Epi.

  Variables S1 S2 : Signature.
  Variables (F : S1 -> S2) (HF : forall f, arity f = arity (F f)).
  Variables (G : S2 -> S1) (HG : forall f, arity f = arity (G f)).
  Variable FG : forall f, F (G f) = f.

  Lemma HG_epi : forall f, arity f = arity (G f).

  Proof. intro. rewrite <- (FG f) at 1. sym. apply HF. Qed.

  Lemma Ft_epi : forall t, Ft HF (Ft HG t) = t.

  Proof.
    intro t. pattern t; apply term_ind with (Q := fun n
    (ts : vector (term S2) n) => Vmap (Ft HF) (Vmap (Ft HG) ts) = ts);
    clear t.
    (* Var *)
    refl.
    (* Fun *)
    intros. simpl. eapply fun_eq_intro with (h:=FG f).
    rewrite Vmap_cast, !Vcast_cast, H. sym. apply Vcast_refl.
    (* Vnil *)
    refl.
    (* Vcons *)
    intros. simpl. rewrite H, H0. refl.
  Qed.

  Lemma Fv_epi : forall n (ts : vector (term S2) n), Fv HF (Fv HG ts) = ts.

  Proof. induction ts; simpl; intros. refl. rewrite IHts, Ft_epi. refl. Qed.

  Lemma Fc_epi : forall c, Fc HF (Fc HG c) = c.

  Proof.
    induction c; simpl; intros. refl. eapply cont_eq_intro
    with (h1 := eq_refl i) (h2 := eq_refl j). apply FG. hyp.
    rewrite Fv_epi, Vcast_refl. refl. rewrite Fv_epi, Vcast_refl. refl.
  Qed.

  Lemma Fr_epi : forall a, Fr HF (Fr HG a) = a.

  Proof. destruct a as [l r]. simpl. rewrite !Ft_epi. refl. Qed.

  Lemma Fl_epi : forall l, Fl HF (Fl HG l) = l.

  Proof. induction l; simpl; intros. refl. rewrite Fr_epi, IHl. refl. Qed.

End Epi.

Arguments HG_epi [S1 S2 F] _ [G] _ _.

(***********************************************************************)
(** isomorphism *)

Section Iso.

  Variables S1 S2 : Signature.
  Variables (F : S1 -> S2) (HF : forall f, arity f = arity (F f)).
  Variables (G : S2 -> S1) (HG : forall f, arity f = arity (G f)).
  Variables (FG : forall f, F (G f) = f) (GF : forall f, G (F f) = f).

  Lemma Frs_epi : forall R, Frs HG (Frs HF R) [<=] R.

  Proof.
    intros R x H. do 2 destruct H. subst. do 2 destruct H. subst.
    rewrite Fr_epi. hyp. hyp.
  Qed.

  Variables E R : set (rule S1).

  Lemma WF_Fred_iso : WF (red R) <-> WF (red (Frs HF R)).

  Proof.
    split; intro. apply WF_Fred with (G:=G) (HG:=HG) (R':=Frs HF R).
    apply Frs_epi. refl. hyp.
    apply Fred_WF with (S2:=S2) (F:=F) (HF:=HF). hyp.
  Qed.

  Lemma WF_Fred_mod_iso :
    WF (red_mod E R) <-> WF (red_mod (Frs HF E) (Frs HF R)).

  Proof.
    split; intro.
    apply WF_Fred_mod with (G:=G) (HG:=HG) (R':=Frs HF R) (E':=Frs HF E).
    apply Frs_epi. refl. apply Frs_epi. refl. hyp.
    apply Fred_mod_WF with (S2:=S2) (F:=F) (HF:=HF). hyp.
  Qed.

  Lemma WF_Fhd_red_mod_iso :
    WF (hd_red_mod E R) <-> WF (hd_red_mod (Frs HF E) (Frs HF R)).

  Proof.
    split; intro.
    apply WF_Fhd_red_mod with (G:=G) (HG:=HG) (R':=Frs HF R) (E':=Frs HF E).
    apply Frs_epi. refl. apply Frs_epi. refl. hyp.
    apply Fhd_red_mod_WF with (S2:=S2) (F:=F) (HF:=HF). hyp.
  Qed.

End Iso.
