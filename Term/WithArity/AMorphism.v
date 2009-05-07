(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-05-07

algebra morphisms
*)

Set Implicit Arguments.

Require Import LogicUtil.
Require Import ATrs.
Require Import VecUtil.
Require Import List.
Require Import RelUtil.
Require Import SN.

Section Morphism.

Variable S1 S2 : Signature.

Variable F : S1 -> S2.

Variable hyp1 : forall f, arity f = arity (F f).

Fixpoint Ft (t : term S1) : term S2 :=
  match t with
    | Var x => Var x
    | Fun f ts =>
      let fix Fv n (ts : vector (term S1) n) : vector (term S2) n :=
        match ts in vector _ n return vector _ n with
          | Vnil => Vnil
          | Vcons t n' ts' => Vcons (Ft t) (Fv n' ts')
        end
        in Fun (F f) (Vcast (Fv (arity f) ts) (hyp1 f))
  end.

Definition Fv := Vmap Ft.

Lemma Ft_fun : forall f ts,
  Ft (Fun f ts) = Fun (F f) (Vcast (Fv ts) (hyp1 f)).

Proof.
intros. simpl. apply args_eq. apply Vcast_eq. refl.
Qed.

Lemma Fc_aux : forall i j n n', i+S j=n -> n=n' -> i+S j=n'.

Proof.
intros. omega.
Qed.

Implicit Arguments Fc_aux [i j n n'].

Fixpoint Fc (c : context S1) : context S2 :=
  match c with
    | Hole => Hole
    | Cont f _ _ e v1 c' v2 =>
      Cont (F f) (Fc_aux e (hyp1 f)) (Fv v1) (Fc c') (Fv v2)
  end.

Lemma Ft_fill : forall t c, Ft (fill c t) = fill (Fc c) (Ft t).

Proof.
induction c; intros. refl. simpl fill. rewrite Ft_fun. apply args_eq.
unfold Fv. rewrite Vmap_cast. rewrite Vmap_app. simpl. rewrite Vcast_cast.
rewrite IHc. apply Vcast_pi.
Qed.
 
Definition Fr (a : rule S1) := let (l,r) := a in mkRule (Ft l) (Ft r).

Notation Frs := (List.map Fr).

Definition Fs (s : substitution S1) x := Ft (s x).

Lemma Ft_sub : forall s t, Ft (sub s t) = sub (Fs s) (Ft t).

Proof.
intros s t. pattern t. apply term_ind with (Q := fun n (ts : vector (term S1) n)
  => Fv (Vmap (sub s) ts) = Vmap (sub (Fs s)) (Fv ts)); clear t; intros.
refl. rewrite Ft_fun. repeat rewrite sub_fun. rewrite Ft_fun. apply args_eq.
rewrite H. rewrite Vmap_cast. refl.
refl. simpl. rewrite H. rewrite H0. refl.
Qed.

Lemma Fred : forall R t u, red R t u -> red (Frs R) (Ft t) (Ft u).

Proof.
intros. redtac. unfold red. subst.
exists (Ft l). exists (Ft r). exists (Fc c). exists (Fs s). intuition.
change (In (Fr (mkRule l r)) (Frs R)). apply in_map. hyp.
rewrite Ft_fill. rewrite Ft_sub. refl.
rewrite Ft_fill. rewrite Ft_sub. refl.
Qed.

Lemma Fhd_red : forall R t u, hd_red R t u -> hd_red (Frs R) (Ft t) (Ft u).

Proof.
intros. redtac. unfold hd_red. subst.
exists (Ft l). exists (Ft r). exists (Fs s). intuition.
change (In (Fr (mkRule l r)) (Frs R)). apply in_map. hyp.
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

Ltac geneq H x e := generalize (refl_equal e); generalize (H e);
  clear H; generalize e at -2; intros t h; gen x; gen h; gen t.


Lemma Fred_WF : forall R, WF (red (Frs R)) -> WF (red R).

Proof.
intros R H x. geneq H x (Ft x). induction 1; intros. apply SN_intro; intros.
eapply H0. subst x. apply Fred. apply H2. refl.
Qed.

Lemma Fred_mod_WF : forall E R,
  WF (red_mod (Frs E) (Frs R)) -> WF (red_mod E R).

Proof.
intros E R H x. geneq H x (Ft x). induction 1; intros. apply SN_intro; intros.
eapply H0. subst x. apply Fred_mod. apply H2. refl.
Qed.

Lemma Fhd_red_mod_WF : forall E R,
  WF (hd_red_mod (Frs E) (Frs R)) -> WF (hd_red_mod E R).

Proof.
intros E R H x. geneq H x (Ft x). induction 1; intros. apply SN_intro; intros.
eapply H0. subst x. apply Fhd_red_mod. apply H2. refl.
Qed.

End Morphism.
