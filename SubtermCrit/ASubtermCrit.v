(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sidi Ould-Biha & Frederic Blanqui, 2010-04-06

Subterm criterion from:

Tyrolean Termination Tool: Techniques and Features
Nao Hirokawa and Aart Middeldorp
Information and Computation 205(4), pp. 474 – 511, 2007
*)

Set Implicit Arguments.

Require Import ATrs ASimpleProj RelUtil List ARelation LogicUtil NatUtil
  VecUtil InfSeq ASN SN Classical BoolUtil ListUtil ASubterm ADP.

(***********************************************************************)
(** WARNING: we use the following axiom *)

Axiom WF_IS_DP : forall Sig (M D : rules Sig), D [= dp M -> 
  ~WF (hd_red_Mod (red M #) D) -> exists f, exists g, ISModMin M D f g.

Section S.

Variable Sig : Signature.

Notation term := (term Sig). Notation terms := (vector term).
Notation rule := (rule Sig). Notation rules := (list rule).
Notation supterm := (@supterm Sig). Notation supterm_eq := (@supterm_eq Sig).

(***********************************************************************)
(** assumptions *)

Variables (pi : Sig -> nat) (Hpi : valid pi).

Notation proj := (proj Hpi).
Notation ge := (proj_ord Hpi supterm_eq).
Notation gt := (proj_ord Hpi supterm).
Notation bge := (fun x y => bsupterm_eq (proj x) (proj y)).
Notation bgt := (fun x y => bsupterm (proj x) (proj y)).

Section S1.

Variables M D : rules.

Variable hyp1 : forall l r, In (mkRule l r) D -> ge l r.

Variable hyp2 : exists l, exists r, In (mkRule l r) D /\ gt l r.

Variable hyp3 : forall l r,
  In (mkRule l r) D -> is_notvar_lhs (mkRule l r) =  true.

(***********************************************************************)
(** properties of the projected subterm ordering *)

Lemma supterm_proj : forall t u s, gt t u -> gt (sub s t) (sub s u).

Proof.
intros t u s. unfold proj_ord, transp.
case t. simpl. intro. case u. simpl. intros.
destruct H. destruct H. destruct (var_eq_fill H0). tauto.
intros. rewrite proj_sub_fun.
destruct H. destruct H. destruct (var_eq_fill H0). tauto.
intros. destruct u. rewrite proj_sub_fun.
generalize (substitution_closed_subterm s H); intros.
apply (@subterm_trans_eq1 _ _ (sub s (Var n)) _); auto. simpl.
apply subterm_eq_proj.
repeat rewrite proj_sub_fun. apply substitution_closed_subterm. auto.
Qed.

Lemma supterm_eq_proj : forall l r s,
 In (mkRule l r) D -> ge (sub s l) (sub s r).

Proof.
intros l r s Dlr. generalize (hyp1 _ _ Dlr); intro.
case_eq (beq_term (proj l) (proj r)). Focus 2.
assert (proj l <> proj r).
intro. rewrite (proj2 (beq_term_ok _ _) H1) in H0. discriminate H0.
apply subterm_strict. apply supterm_proj. apply subterm_noteq. hyp.
intro. apply H1. symmetry. hyp.
generalize (proj1 (beq_term_ok _ _) H0). clear H0; intros.
unfold proj_ord, transp. generalize (hyp3 _ _ Dlr). destruct l.
unfold is_notvar_lhs. simpl. intros. discriminate H1.
intros. destruct r. rewrite proj_sub_fun, H0. simpl. apply subterm_eq_proj.
clear H1. repeat rewrite proj_sub_fun. rewrite H0. apply subterm_eq_refl.
Qed.

Lemma hyp5 : forall t u, int_red M # t u -> red M # (proj t) (proj u).

Proof.
induction 1. 2: apply rt_refl.
Focus 2. apply (@rtc_trans _ _ _ (proj y) _); auto.
destruct H as [l H]. destruct H as [r H]. destruct H as [c H].
destruct H as [s H]. destruct H as [c_nH H]. destruct H as [Mlr H].
destruct H as [Ht Hu]. destruct c. intuition. rewrite Ht, Hu. simpl.
case (zerop (arity f)); intro Hf0.
assert (arity f <> 0). rewrite <- e. omega. absurd_arith.
repeat rewrite Vnth_cast. repeat rewrite Vnth_app.
destruct (le_gt_dec i (pi f)). repeat rewrite Vnth_cons.
destruct (lt_ge_dec 0 (pi f - i)). apply rt_refl.
apply rt_step. apply red_rule. hyp. apply rt_refl.
Qed.

(***********************************************************************)
(** main theorem *)

Lemma subterm_criterion_IS : forall f g, ~ISModMin M D f g.

Proof.
intros f g HM. destruct HM as [HisM hmin]. destruct hmin as [hmin HsT].
destruct HsT as [Rsg Rsf]. unfold ISModInfRuleApp in hmin.
unfold ISMod in HisM. destruct hyp2 as [l H0]. destruct H0 as [r H0].
destruct H0 as [Dlr Glr].

pose (f0 := fun i => proj (f i)). pose (g0 := fun i => proj ( g i)).
pose (P := fun (i x : nat) => (i <= x /\ (supterm (g0 x) (f0 (S x))))).

assert (HexP : forall i, exists j, P i j).
destruct (hmin (mkRule l r) Dlr) as [h h_def].
assert (hMj : forall j, j <= h j).
induction 0. omega. apply lt_le_S. apply (le_lt_trans _ _ _ IHj).
destruct (h_def j). auto. intro i. exists (h i). unfold P. split. apply hMj.
destruct (h_def i) as [_ Dlr_i]. destruct Dlr_i as [l' H]. destruct H as [r' H].
destruct H as [s H]. destruct H as [Elr H]. destruct H as [Egi Efi].
destruct Elr as [Elr |]; try tauto. symmetry in Elr. rewrite <- rule_eq in Elr.
simpl in Elr. destruct Elr. subst. unfold f0, g0. rewrite Efi, Egi.
apply supterm_proj. auto.

assert (ISMfg0 : ISMod (red M #) (red M # U supterm) f0 g0).
intro i. unfold f0, g0. split. apply hyp5. apply (proj1 (HisM i)).
destruct (HisM i) as [_ [l' [r' [s [Dlr' [Eg Ef]]]]]]. rewrite Eg, Ef.
destruct (supterm_eq_proj l' r' s Dlr') as [C HC].
destruct C. simpl in HC. rewrite HC. left. apply rtc_refl.
right. exists (Cont f1 e v C v0); split; auto. discr.
destruct (ISMod_union ISMfg0 HexP (@rtc_trans _ (red M))) as [f1 [g1 Hfg1]].

pose (TrS := (transp_trans (@subterm_trans Sig))).
assert (HT : supterm @ (red M !) @ supterm << (red M !) @ supterm).
intros x y Hxy. destruct Hxy as [z Hxy]. destruct Hxy as [Hxz Szy].
destruct ((commut_tc_inv (@supterm_red _ _)) _ _ Hxz) as [u Hxu].
exists u; split. exact (proj1 Hxu). apply (@subterm_trans _ _ z _); auto.
exact (proj2 Hxu).

destruct (trc_ISMod (proj1 Hfg1) (@NIS_supterm Sig) TrS) as [f2 [g2 HF]].
destruct HF as [HF1 [[k Hk] HF]]. generalize (ISOfISMod_spec HF1 HT).
set (h := ISOfISMod HF1 HT). intros ISM.
assert (Hhk : (h (S 0)) = g1 k). unfold ISOfISMod; simpl. auto.
set (h0 := fun i => h (S i)). assert (ISM0 : IS (red M !) h0). intro.
apply (ISM (S i)). destruct (IStrc ISM0) as [h1 Hh1].

destruct (proj1 ((proj2 Hfg1) k)) as [k' Hk'].

cut (subterm (proj (g k')) (g k')). intros HT0.
apply (Rsg _ _ HT0 h1). rewrite (proj2 Hh1). unfold h0. rewrite Hhk, Hk'.
auto. intuition. destruct (proj1 Hfg1 k) as [_ HT0]. rewrite Hk' in HT0.
unfold g0 in HT0. destruct (g k'). simpl in HT0. destruct HT0 as [? HT0].
simpl in HT0. destruct (var_eq_fill (proj2 HT0)). tauto. generalize HT0. simpl.
case (zerop (arity f3)); intros Hf30 HT1. destruct HT1 as [c HT1].
destruct (fun_eq_fill (proj2 HT1)) as [HT2 | HT2]. tauto.
destruct HT2 as [i [j [HT2 _]]].
assert (arity f3 <> 0). rewrite <- HT2. omega. absurd_arith.
apply subterm_fun. apply Vnth_in.
Qed.

End S1.

(***********************************************************************)
(** theorem with boolean conditions *)

Section S2.

Lemma subterm_criterion_WF : forall M D1 D2,
  (D1 ++ D2) [= dp M ->
  forallb (@is_notvar_lhs Sig) (D1 ++ D2) = true ->
  forallb (brule bge) (D1 ++ D2) = true ->
  forallb (brule bgt) D1 = true -> 
  WF (hd_red_Mod (red M #) D2) -> WF (hd_red_Mod (red M #) (D1 ++ D2)).

Proof.
intros. induction D1. simpl. hyp.
simpl. apply NNPP. intro. destruct (WF_IS_DP H H4) as [f [g H5]].
assert (H6 : forall l r : term, In (mkRule l r) (a :: D1 ++ D2) -> ge l r).
intros. generalize (proj1 (forallb_forall _ _) H1 (mkRule l r) H6).
unfold brule; simpl. apply (proj1 (bsubterm_eq_ok _ _)).
assert (H7 : exists l, exists r, In (mkRule l r) (a :: D1 ++ D2) /\ gt l r).
exists (lhs a). exists (rhs a). simpl. split.
left. apply (proj1 (rule_eq _ _)). simpl. auto.
generalize (proj1 (forallb_forall _ _) H2 a (in_eq a _)). unfold brule.
apply (proj1 (bsubterm_ok _ _)).
assert (H8 : forall l r, In (mkRule l r) (a :: D1 ++ D2) ->
 is_notvar_lhs (mkRule l r) = true).
intros. apply (proj1 (forallb_forall _ _) H0). auto.
apply (@subterm_criterion_IS M (a :: D1 ++ D2) H6 H7 H8 f g). hyp.
Qed.

Lemma subterm_criterion : forall M D,
  D [= dp M ->
  forallb (@is_notvar_lhs Sig) D = true ->
  forallb (brule bge) D = true ->
  WF (hd_red_Mod (red M #) (filter (brule (neg bgt)) D)) ->
  WF (hd_red_Mod (red M #) D).

Proof.
intros. pose (D' := filter (brule (neg bgt)) D).
pose (D0 := filter (brule bgt) D).
assert (HD : (hd_red_Mod (red M #) D) << (hd_red_Mod (red M #) (D0 ++ D'))).
apply hd_red_Mod_incl. refl. intros d Dd. apply in_or_app.
case_eq (brule (neg bgt) d). right. apply (proj2 (filter_In _ _ _)). intuition.
left. apply (proj2 (filter_In _ _ _)). split; try hyp. unfold brule in H3.
generalize (proj1 (negb_lr _ _) H3). simpl. auto.
apply (WF_incl HD). apply subterm_criterion_WF; auto.
intro; rewrite in_app; unfold D0, D'; intro T. destruct T as [T|T]; apply H;
rewrite filter_In in T; destruct T; auto.
apply (proj2 (forallb_forall _ _)). intros.
apply (proj1 (forallb_forall _ _) H0 x). destruct (in_app_or H3).
unfold D0 in H4. rewrite filter_In in H4. destruct H4. hyp.
unfold D' in H4. rewrite filter_In in H4. destruct H4. hyp.
apply (proj2 (forallb_forall _ _)). intros.
apply (proj1 (forallb_forall _ _) H1 x). destruct (in_app_or H3).
unfold D0 in H4. rewrite filter_In in H4. destruct H4. hyp.
unfold D' in H4. rewrite filter_In in H4. destruct H4. hyp.
apply (proj2 (forallb_forall _ _)). intros. unfold D0 in H3.
rewrite filter_In in H3. intuition.
Qed.

End S2.

End S.

Implicit Arguments subterm_criterion [Sig pi D].

Ltac subterm_crit p_ok := apply (subterm_criterion p_ok);
  [ check_eq || fail 10 "a left-hand side is a variable"
  | check_eq || fail 10 "error in subterm criterion application"
  | hd_red_mod].
