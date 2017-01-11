(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Leo Ducas, 2007-08-06

Duplicate/mark symbols to distinguish internal reductions from head reductions
*)

Set Implicit Arguments.

From CoLoR Require Import ATrs ListUtil VecUtil LogicUtil RelUtil SN.

Section S.

Variable Sig : Signature.

Notation rules := (rules Sig).

(***********************************************************************)
(** signature of symbols marked as head or internal *)

Inductive dup_symb : Type :=
| hd_symb : symbol Sig -> dup_symb
| int_symb : symbol Sig -> dup_symb.

Definition dup_ar s :=
  match s with
    | hd_symb s' => arity s'
    | int_symb s' => arity s'
  end.

Definition beq_dup_symb (f g : dup_symb) : bool :=
  match f, g with
    | hd_symb f', hd_symb g' => beq_symb f' g'
    | int_symb f', int_symb g' => beq_symb f' g'
    | _, _ => false
  end.

Lemma beq_dup_symb_ok : forall f g, beq_dup_symb f g = true <-> f = g.

Proof.
destruct f; destruct g; simpl; try rewrite beq_symb_ok; split_all; subst;
  refl || discr || inversion H; refl.
Qed.

Definition dup_sig := mkSignature dup_ar beq_dup_symb_ok.

Notation Sig' := dup_sig. Notation Fun' := (@Fun Sig').

(***********************************************************************)
(** function marking all symbols as internal *)

Fixpoint dup_int_term t :=
  match t with
    | Var x => Var x
    | Fun f v => Fun' (int_symb f) (Vmap dup_int_term v)
  end.

Lemma dup_int_term_fun : forall f v,
  dup_int_term (Fun f v) = Fun' (int_symb f) (Vmap dup_int_term v).

Proof. trivial. Qed.

(***********************************************************************)
(** function marking all symbols as internal except the head symbol *)

Definition dup_hd_term t :=
  match t with
    | Var x => Var x
    | Fun f v => Fun' (hd_symb f) (Vmap dup_int_term v)
  end.

Lemma dup_hd_term_fun : forall f v,
  dup_hd_term (Fun f v) = Fun' (hd_symb f) (Vmap dup_int_term v).

Proof. trivial. Qed.

(***********************************************************************)
(** function marking substitutions *)

Definition dup_int_subst (s : substitution Sig) n := dup_int_term (s n).

Lemma dup_int_subst_spec : forall s t,
  sub (dup_int_subst s) (dup_int_term t) = dup_int_term (sub s t).

Proof.
intros.
pattern t.
set (Q := Vforall (fun t0 =>
  sub (dup_int_subst s) (dup_int_term t0) = dup_int_term (sub s t0))).
apply term_ind with (Q:=Q).
(* Var *)
intro; unfold dup_int_subst; simpl. apply eq_refl.
(* Fun *)
intros. rewrite dup_int_term_fun. simpl.
unfold Q in H.
cut (Vmap (sub (dup_int_subst s)) (Vmap dup_int_term v) =
  Vmap dup_int_term (Vmap (sub s) v)).
intros. rewrite <- H0. auto.
rewrite !Vmap_map.
apply Vmap_eq. apply H.
(* Vnil *)
unfold Q; simpl; auto.
(* Vcons *)
unfold Q; simpl; auto.
Qed.

Lemma dup_int_subst_hd_dup : forall s f v,
  sub (dup_int_subst s) (dup_hd_term (Fun f v))
  = dup_hd_term (sub s (Fun f v)).

Proof.
intros.
rewrite dup_hd_term_fun. simpl.
cut ((Vmap (sub (dup_int_subst s)) (Vmap dup_int_term v)) =
 (Vmap dup_int_term (Vmap (sub s) v)) ).
intro. rewrite <- H. apply eq_refl.
rewrite !Vmap_map.
apply Vmap_eq_ext. 
apply dup_int_subst_spec.
Qed. 

(***********************************************************************)
(** function marking contexts *)

Fixpoint dup_int_context c :=
  match c with
    | Hole => Hole
    | @Cont _ f _ _ H v c' w => @Cont Sig' (int_symb f) _ _ H 
      (Vmap dup_int_term v) (dup_int_context c') (Vmap dup_int_term w)
  end.

Lemma dup_int_context_spec : forall c s l,
  dup_int_term (fill c (sub s l)) =
  fill (dup_int_context c) (sub (dup_int_subst s) (dup_int_term l)).

Proof.
induction c; intros.
simpl.
rewrite dup_int_subst_spec. apply eq_refl.
simpl.
cut (Vmap dup_int_term (Vcast (Vapp t (Vcons (fill c (sub s l)) t0)) e) =
  (Vcast (Vapp (Vmap dup_int_term t)
    (Vcons
      (fill (dup_int_context c) (sub (dup_int_subst s) (dup_int_term l)))
      (Vmap dup_int_term t0))) e)).
intro. rewrite H; auto.
rewrite Vmap_cast, Vmap_app.
simpl.
rewrite IHc.
auto.
Qed.

Definition dup_hd_context c :=
  match c with
    | Hole => Hole
    | @Cont _ f _ _ H v c' w => @Cont Sig' (hd_symb f) _ _ H 
      (Vmap dup_int_term v) (dup_int_context c') (Vmap dup_int_term w)
  end.

(***********************************************************************)
(** functions marking rules *)

Definition dup_int_rule r :=
  mkRule (dup_int_term (lhs r)) (dup_int_term (rhs r)).

Definition dup_hd_rule r :=
  mkRule (dup_hd_term (lhs r)) (dup_hd_term (rhs r)).

Definition dup_int_rules := map dup_int_rule.

Definition dup_hd_rules := map dup_hd_rule.

(***********************************************************************)
(** reduction properties reflected by marking *)

Section red.

Variable R : rules.

Variable hyp : forallb (@is_notvar_lhs Sig) R = true.
Variable hyp' : forallb (@is_notvar_rhs Sig) R = true.

Lemma hd_red_dup_hd_red : forall  t u, hd_red R t u -> 
  hd_red (dup_hd_rules R) (dup_hd_term t) (dup_hd_term u).

Proof.
intros. redtac. subst. unfold hd_red.
ex (dup_hd_term l) (dup_hd_term r) (dup_int_subst s).
ded (is_notvar_lhs_elim hyp lr). decomp H.
ded (is_notvar_rhs_elim hyp' lr). decomp H. subst.
rewrite !dup_int_subst_hd_dup. split_all. unfold dup_hd_rules.
change (In (dup_hd_rule (mkRule (Fun x x0) (Fun x1 x2))) (map dup_hd_rule R)).
apply in_map. hyp.
Qed.

Lemma red_dup_int_red : forall t u,
  red R t u -> red (dup_int_rules R) (dup_int_term t) (dup_int_term u).

Proof.
intros. redtac.
exists (dup_int_term l). exists (dup_int_term r).
exists (dup_int_context c). exists (dup_int_subst s).
split.
change (In (dup_int_rule (mkRule l r)) (map dup_int_rule R)).
apply in_map. auto.
rewrite <- !dup_int_context_spec.
split; subst; refl.
Qed.

Lemma int_red_dup_int_red : forall t u,
  int_red R t u -> red (dup_int_rules R) (dup_hd_term t) (dup_hd_term u).

Proof.
intros. redtac.
ex (dup_int_term l) (dup_int_term r) (dup_hd_context c) (dup_int_subst s).
destruct c. tauto.
split.
change (In (dup_int_rule (mkRule l r)) (map dup_int_rule R)).
apply in_map. auto.
subst; simpl.
split; rewrite Vmap_cast, Vmap_app;
simpl; rewrite <- dup_int_context_spec; auto.
Qed.

End red.

(***********************************************************************)
(** preservation of termination by marking *)

Section WF.

Variables E R : rules.

Variable no_lhs_var : forallb (@is_notvar_lhs Sig) R = true.
Variable no_rhs_var : forallb (@is_notvar_rhs Sig) R = true.

Lemma WF_duplicate_hd_int_red :
  WF (hd_red_mod (dup_int_rules E) (dup_hd_rules R))
  -> WF (hd_red_Mod (int_red E #) R).

Proof.
intros. set (rel := hd_red_mod (dup_int_rules E) (dup_hd_rules R)).
set (rel' := Rof rel (dup_hd_term)). apply (WF_incl rel').
unfold Basics.flip, rel', rel, hd_red_Mod, hd_red_mod. unfold inclusion; intros.
destruct H0 as [z]; exists (dup_hd_term z). destruct H0; split.
clear H1. induction H0. apply rt_step. apply int_red_dup_int_red. hyp.
apply rt_refl. eapply rt_trans. apply IHclos_refl_trans1. hyp.
apply  hd_red_dup_hd_red; auto. subst rel rel'. apply WF_inverse; auto.
Qed.

End WF.

(***********************************************************************)
(** basic functions on marked rules *)

Notation term' := (term Sig'). Notation rule' := (ATrs.rule Sig').

Definition is_int_symb (t : term') :=
  match t with
    | Fun (int_symb _) _ => true
    | _ => false
  end.

Definition is_int_symb_lhs (a : rule') := is_int_symb (lhs a).
Definition is_int_symb_rhs (a : rule') := is_int_symb (rhs a).

Definition is_hd_symb (t : term') :=
  match t with
    | Fun (hd_symb _) _ => true
    | _ => false
  end.

Definition is_hd_symb_lhs (a : rule') := is_hd_symb (lhs a).
Definition is_hd_symb_rhs (a : rule') := is_hd_symb (rhs a).

(***********************************************************************)
(** change marking of the top of a term *)

Definition mark (t : term') : term' :=
  match t with
    | Fun (int_symb f) ts => Fun' (hd_symb f) ts
    | t => t
  end.

Definition mark_rule (a : rule') : rule' :=
  let (l,r) := a in mkRule (mark l) (mark r).

Definition mark_rules := map mark_rule.

Definition unmark (t : term') : term' :=
  match t with
    | Fun (hd_symb f) ts => Fun' (int_symb f) ts
    | t => t
  end.

Definition unmark_rule (a : rule') : rule' :=
  let (l,r) := a in mkRule (unmark l) (unmark r).

Definition unmark_rules := map unmark_rule.

(***********************************************************************)
(** relation between (red R) and (int_red R) when R is_lhs_int_symb_headed *)

Section int_red.

Variable R : @ATrs.rules Sig'.

Variable int_hyp : forallb is_int_symb_lhs R = true.

Lemma dup_int_rules_int_red : forall f v t,
  red R (Fun' (hd_symb f) v) t -> int_red R (Fun' (hd_symb f) v) t.

Proof.
intros. redtac. ex l r c s. split.
destruct c. simpl in *. rewrite forallb_forall in int_hyp. ded (int_hyp _ lr).
revert H. compute. case_eq l. discr. intro f0. case_eq f0. discr.
intros. subst l. simpl in xl. discr. congruence. tauto.
Qed.

Lemma dup_int_rules_int_red_rtc_aux : forall u t, red R # u t ->
  forall f v, u = Fun' (hd_symb f) v -> 
    int_red R # u t /\ exists w, t = Fun' (hd_symb f) w.

Proof.
intros u t H.
induction H; intros.
assert (int_red R # x y).
apply rt_step.
rewrite H0.
apply dup_int_rules_int_red. subst;auto.
split. auto.
clear H.
ded (int_red_rtc_preserve_hd H1).
destruct H.
exists v. subst. auto.
do 3 destruct H; subst.
destruct H. inversion H. subst.
exists x2. apply eq_refl.

split. apply rt_refl.
exists v; auto.
ded (IHclos_refl_trans1 _ _ H1).
clear IHclos_refl_trans1.
destruct H2.
destruct H3 as [w].
ded (IHclos_refl_trans2 _ _ H3).
destruct H4. destruct H5.
split.
eapply rt_trans; eauto.
exists x0. auto.
Qed.

Lemma dup_int_rules_int_red_rtc : forall f v t,
  red R # (Fun' (hd_symb f) v) t -> int_red R # (Fun' (hd_symb f) v) t.

Proof.
intros. ded (dup_int_rules_int_red_rtc_aux H (eq_refl _)). tauto.
Qed. 

End int_red.

(***********************************************************************)
(** properties of (red (dup_int_rules R)) *)

Section red_dup.

Variable R : rules.

Notation R' := (dup_int_rules R).

Variable hyp : forallb (@is_notvar_lhs Sig') R' = true.

Lemma red_dup_int_hd_symb : forall f us v,
  red R' (Fun' (hd_symb f) us) v -> exists vs, v = Fun' (hd_symb f) vs.

Proof.
intros. redtac. destruct (in_map_elim lr). destruct H. destruct x.
inversion H0. subst. destruct c; simpl in *.
(* Hole *)
rewrite forallb_forall in hyp. ded (hyp _ lr). destruct lhs. discr.
simpl dup_int_term in xl. simpl in xl. Funeqtac. discr.
(* Cont *)
Funeqtac.
exists (Vcast (Vapp t (Vcons (fill c (sub s (dup_int_term rhs))) t0)) e).
refl.
Qed.

Lemma rtc_red_dup_int_hd_symb_aux : forall f u v, red R' # u v ->
  forall us, u = Fun' (hd_symb f) us -> exists vs, v = Fun' (hd_symb f) vs.

Proof.
induction 1; intros. eapply red_dup_int_hd_symb. subst. apply H. eauto.
destruct (IHclos_refl_trans1 _ H1). eapply IHclos_refl_trans2. apply H2.
Qed.

Lemma rtc_red_dup_int_hd_symb : forall f us v,
  red R' # (Fun' (hd_symb f) us) v -> exists vs, v = Fun' (hd_symb f) vs.

Proof. intros. eapply rtc_red_dup_int_hd_symb_aux. apply H. refl. Qed.

End red_dup.

End S.

Arguments rtc_red_dup_int_hd_symb [Sig R] _ [f us v] _.

(***********************************************************************)
(** tactics *)

Ltac mark := apply WF_duplicate_hd_int_red; [refl | refl | idtac].

(***********************************************************************)
(** signature functor *)

Module Make (S : FSIG) <: FSIG.

  Definition Sig := dup_sig S.Sig.

  Definition Fs :=
    fold_left (fun l f => hd_symb S.Sig f :: int_symb S.Sig f :: l) S.Fs nil.

  Lemma Fs_ok : forall f : Sig, In f Fs.

  Proof.
    intro. unfold Fs. rewrite (@In_fold_left _ _ _
      (fun f => hd_symb S.Sig f :: int_symb S.Sig f :: nil)). simpl.
    right. destruct f; exists s; split_all; apply S.Fs_ok. refl.
  Qed.

End Make.
