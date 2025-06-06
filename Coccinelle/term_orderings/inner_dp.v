
(** * Equational theory on a term algebra *)

From Stdlib Require Import List Relations Wellfounded Arith.
From CoLoR Require Import closure more_list weaved_relation term equational_theory_spec
     rwr_strategies dp rpo.

Module Make (E : EqTh).

  Import E.
  Import T.

Module Import R := rwr_strategies.Make (E).
Module Import DP := dp.MakeDP (E).

Inductive idp (R : relation term) : term -> term -> Prop :=
 | Idp : forall t1 t2, axiom (dp R) t2 t1 -> (forall s, direct_subterm s t1 -> nf (one_step R) s) ->
         idp R t2 t1.

Inductive idp_step (R : relation term) : term -> term -> Prop :=
   | IDp_step : forall f l1 l2 t3, refl_trans_clos (one_step_list (P_step R (inner R))) l2 l1 -> 
        idp R t3 (Term f l2) -> idp_step R t3 (Term f l1).

Lemma idp_criterion_aux : 
  forall R, (forall x t, ~ (R t (Var x))) -> 
  (forall s t, R s t -> forall x, In x (var_list s) -> In x (var_list t)) ->
  (forall f, {constructor R f} + {defined R f}) ->
  forall t,   Acc (idp_step R)  t -> (forall s, direct_subterm s t -> Acc (P_step R (inner R)) s) ->
              Acc (P_step R (inner R)) t.
Proof.
intros R HR RR CD.
(* a variable is accessible *)
assert (Acc_var : forall x, Acc (P_step R (inner R)) (Var x)). 
intro x; apply Acc_intro; intros s H; inversion H; subst.
inversion H1; subst.
destruct t2 as [v2 | ].
absurd (R t1 (Var v2)); trivial; apply HR.
discriminate.
(* main proof *)
intros t Acc_t; induction Acc_t as [t Acc_t IH].
intros Acc_l; destruct t as [x | f l].
apply Acc_var.
simpl in Acc_l; rewrite acc_one_step_list in Acc_l; revert IH.
induction Acc_l as [l Acc_l IHl]; intros IH'.
assert (Acc_l' : forall t, In t l -> Acc (P_step R (inner R)) t).
rewrite acc_one_step_list; apply Acc_intro; exact Acc_l.
apply Acc_intro; 
intros s H; destruct s as [x1 | f1 l1].
apply Acc_var.
inversion H as [t s Hnf H' | f' lt ls H']; clear H; subst.
(* rewrite step at the top *)
inversion H' as [t1 t2 sigma t1_R_t2 H1 H2]; clear H'.
destruct t2 as [x | g k].
absurd (R t1 (Var x)); trivial; apply HR.
simpl in H2; injection H2; clear H2; intros; subst g l.
assert (H'' : forall n t, size (apply_subst sigma t) <= n -> 
                      (exists p, subterm_at_pos t1 p = Some t) ->
                      Acc (P_step R (inner R)) (apply_subst sigma t)).
intro n; induction n as [ | n].
intros t St; absurd (1 <= 0); auto with arith; 
apply Nat.le_trans with (size (apply_subst sigma t)); trivial; apply size_ge_one.
intros [x | g h] St [p H''].


apply var_P_acc with k; trivial.
assert (H : In x (var_list (Term f k))).
apply RR with t1; trivial.
apply var_in_subterm with (Var x) p; trivial.
simpl; left; trivial.
rewrite var_list_unfold in H; trivial.
assert (Acc_h : forall t, In t h -> Acc (P_step R (inner R)) (apply_subst sigma t)).
intros t t_in_h; destruct (In_split _ _ t_in_h) as [h' [h'' K]]; subst h.
apply IHn.
apply le_S_n; refine (Nat.le_trans _ _ _ _ St); apply size_direct_subterm; trivial.
simpl; rewrite map_app; apply in_or_app; right; left; trivial.
exists (p ++ (length h' :: nil)).
generalize t1 H''; clear t1 H'' H1 t1_R_t2 IHn; induction p as [ | i p].
intros t1 H''; simpl in H''; injection H''; intros; subst; simpl.
rewrite nth_error_at_pos; trivial.
intros t1 H''; simpl; simpl in H''; destruct t1 as [ | g1 k1].
discriminate. 
destruct (nth_error k1 i) as [ti | ].
apply IHp; trivial.
discriminate.
destruct (CD g) as [Cg | Dg].
simpl; apply P_acc_subterms; trivial.
intros t t_in_map_h; rewrite in_map_iff in t_in_map_h.
destruct t_in_map_h as [t' [H''' t'_in_h]]; subst; apply Acc_h; trivial.

destruct (subterm_at_pos_dec_alt (Term f k) (Term g h)) as [[q Sub] | not_Sub].
destruct q as [ | i q].
apply IH'.
apply IDp_step with (map (apply_subst sigma) k).
left.
replace (Term f (map (apply_subst sigma) k)) with (apply_subst sigma (Term f k)); trivial.
apply Idp; trivial.
apply instance; apply Dp with t1 p; trivial.
simpl; intros t t_in_map_h; rewrite in_map_iff in t_in_map_h.
destruct t_in_map_h as [t' [H''' t'_in_h]]; subst; apply Acc_h; trivial.
simpl in Sub.
generalize (nth_error_ok_in i k); destruct (nth_error k i) as [ti | ].
intro H; destruct (H _ (eq_refl _)) as [k1 [k2 [L H']]].
apply P_acc_subterms_3 with q (apply_subst sigma ti).
apply Acc_l'.
rewrite in_map_iff; exists ti; split; trivial.
subst; apply in_or_app; right; left; trivial.
generalize (subterm_at_pos_apply_subst_apply_subst_subterm_at_pos ti q sigma).
rewrite Sub; trivial.
discriminate.
apply IH'.
apply IDp_step with (map (apply_subst sigma) k).
left.
replace (Term f (map (apply_subst sigma) k)) with (apply_subst sigma (Term f k)); trivial.
apply Idp; trivial.
apply instance; apply Dp with t1 p; trivial.
intros s s_in_h; simpl in s_in_h.
rewrite in_map_iff in s_in_h.
destruct s_in_h as [u [H2 u_in_h]]; subst.
apply Acc_h; trivial.
apply (H'' (size (Term f1 l1))).
rewrite H1; apply le_n.
exists (@nil nat); simpl; trivial.
(* rewrite step NOT at the top *)
apply IHl; trivial.
intros t H; apply Acc_t.
inversion H; subst.
apply IDp_step with l2; trivial.
apply refl_trans_clos_is_trans with l1; trivial.
right; left; assumption.

intros s H'' H'''; apply IH'; trivial.
inversion H''; subst.
apply (IDp_step R f l l2 s); trivial.
apply refl_trans_clos_is_trans with l1; trivial; right; left; assumption.
Qed.

Lemma idp_criterion : 
  forall R, (forall x t, ~ (R t (Var x))) -> 
  (forall s t, R s t -> forall x, In x (var_list s) -> In x (var_list t)) ->
  (forall f, {constructor R f} + {defined R f}) ->
   well_founded (idp_step R)  -> well_founded (P_step R (inner R)).
Proof.
intros R HR RR CD Wf t; pattern t; apply term_rec3; clear t.
intro x; apply Acc_intro; intros s H; inversion H; subst.
inversion H1; subst.
destruct t2 as [v2 | ].
absurd (R t1 (Var v2)); trivial; apply HR.
discriminate.
intros; apply idp_criterion_aux; trivial.
Qed.

Section Psi_definition.

Variable R : relation term.
Variable Rvar : (forall t x, ~ (R t (Var x))).
Variable Rreg : (forall s t, R s t -> forall x, In x (var_list s) -> In x (var_list t)).
Variable rule_list : list (term * term).
Variable Req : (forall l r, R r l <-> In (l, r) rule_list).
Variable wf_inner : well_founded (P_step R (inner R)).
Variable UIR : forall t s s', inner R t -> axiom R s t -> axiom R s' t -> s = s'.
Variable AICR : 
    forall l r sigma, R r l -> 
      (forall p g d tau, R d g -> 
                subterm_at_pos (apply_subst sigma l) p = Some (apply_subst tau g) ->
                inner R (apply_subst tau g) -> 
                    (p = nil \/ 
                    exists q, exists q', exists v, p = q ++ q' /\ subterm_at_pos l q = Some (Var v))) \/
      (exists s', P_step R (inner R) s' (apply_subst sigma l) /\ rwr R (apply_subst sigma r) s').

Lemma Rvar' : forall x t, ~ (In (Var x,t) rule_list).
Proof.
intros t x H; apply (Rvar x t); rewrite Req; trivial.
Qed.

Lemma Rreg' : (forall l r, In (l,r) rule_list -> forall x, In x (var_list r) -> In x (var_list l)).
Proof.
intros l r H.
apply Rreg; rewrite Req; trivial.
Qed.

Lemma nf_var : forall v, nf (one_step R) (Var v).
Proof.
intros v s H.
inversion H; clear H; subst.
inversion H0; clear H0; subst.
destruct t2 as [v2 | f2 l2].
absurd (R t1 (Var v2)); trivial.
discriminate.
Qed.

Inductive Psi : relation term :=
   | Psi_at_top : forall s t, axiom R s t -> (inner R) t -> Psi s t
   | Psi_in_context : 
       forall f llst, (forall s t, In (s,t) llst -> 
                           (Psi s t) \/ (s = t /\ nf (one_step R) t)) ->
       (exists s, exists t, In (s,t) llst /\ ~nf (one_step R) t) ->
       Psi (Term f (map (@fst term term) llst)) (Term f (map (@snd term term) llst)).

Lemma Psi_not_nf :
  forall t s, Psi s t -> nf (one_step R) t -> False.
Proof.
intros t; pattern t; apply term_rec3; clear t. 
intros v s P; inversion P as [ss tt H K | g ll H K]; subst.
intro H'; unfold nf in H'; apply (H' s); apply at_top; trivial.
intros f l IHl s P; inversion P as [ss tt H K | g ll H K]; clear P; subst.
intro H'; unfold nf in H'; apply (H' s); apply at_top; trivial.
destruct K as [s [t [st_in_ll P]]].
intro H'; apply P; apply (nf_one_step_subterm _ _ H').
simpl; rewrite in_map_iff; exists (s,t); split; trivial.
Qed.

Lemma Psi_unique : forall t s s', Psi s t -> Psi s' t -> s = s'.
Proof.
intros t; pattern t; apply term_rec3; clear t.
intros v s s' P P'.
assert False; [idtac | contradiction].
apply (Psi_not_nf (Var v) s); trivial.
apply nf_var.
intros f l IHl s s' P P'.
inversion P as [ss tt H K | g ll H K]; inversion P' as [ss' tt' H' K' | g' ll' H' K']; clear P P'; subst.
apply (UIR (Term f l)); trivial.

unfold inner in K; simpl in K.
destruct K' as [s' [t' [st_in_ll' P]]].
absurd (nf (one_step R) t'); trivial.
apply K; rewrite in_map_iff; exists (s',t'); split; trivial.

unfold inner in K'; simpl in K'.
destruct K as [s [t [st_in_ll' P]]].
absurd (nf (one_step R) t); trivial.
apply K'; rewrite in_map_iff; exists (s,t); split; trivial.

apply (f_equal (fun l => Term f l)).
generalize H ll' H' IHl H5; clear K K' H ll' H' IHl H5; induction ll as [ | [s t] ll].
intros _ [ | [s' t'] ll']; trivial; intros; discriminate.
intros H1 [ | [s' t'] ll']; simpl; intros H' IHl H6.
discriminate.
injection H6; clear H6; intros H6 H7; subst t'.
destruct (H1 s t (or_introl _ (eq_refl _))) as [P | [E I]];
destruct (H' s' t (or_introl _ (eq_refl _))) as [P' | [E' I']].
rewrite (IHl t (or_introl _ (eq_refl _)) s s'); trivial.
apply (f_equal (fun l => s' :: l)).
apply IHll; trivial.
intros; apply H1; right; trivial.
intros; apply H'; right; trivial.
intros u u_in_ll v v'; apply IHl; right; trivial.
subst s'; assert False; [idtac | contradiction].
apply (Psi_not_nf _ _ P I').
subst s; assert False; [idtac | contradiction].
apply (Psi_not_nf _ _ P' I).
subst s s'; apply (f_equal (fun l => t :: l)).
apply IHll; trivial.
intros; apply H1; right; trivial.
intros; apply H'; right; trivial.
intros u u_in_ll v v'; apply IHl; right; trivial.
Qed.

Lemma Psi_def :
  forall t, ~nf (one_step R) t -> {t' : term | Psi t' t}.
Proof.
assert (red_dec :=compute_red_is_correct rule_list Rreg' R Req).
assert (nf_dec := dec_nf _ _ red_dec).
assert (inner_dec := nf_dec_inner_dec _ nf_dec).
intros t; assert (Acc_t := wf_inner t); rewrite P_acc_with_subterm in Acc_t.
induction Acc_t as [t Acc_t IH].
intro t_not_nf.
destruct t as [v | f l].
absurd (nf (one_step R) (Var v)); trivial.
apply nf_var.
assert (red_dec_fl := red_dec (Term f l)).
destruct (compute_red rule_list (Term f l)) as [ | r rl].
absurd (nf (one_step R) (Term f l)); trivial.
intros s H; rewrite <- red_dec_fl in H; contradiction.
destruct (inner_dec (Term f l)) as [inner_fl | not_inner_fl].
assert (H' : one_step R r (Term f l)).
rewrite <- red_dec_fl; left; trivial.
exists r; inversion H' as [t1 t2 H'' | g k1 k2 H'']; subst.
apply Psi_at_top; trivial; apply Acc_intro; trivial.
assert False; [idtac | contradiction].
unfold inner in inner_fl; simpl in inner_fl.
generalize inner_fl; clear f Acc_t IH t_not_nf red_dec_fl H' inner_fl.
induction H''; intros nf_l.
apply (nf_l t2 (or_introl _ (eq_refl _)) t1 H).
apply IHH''; intros; apply nf_l; right; trivial.
assert (H : forall t, In t l -> ~ nf (one_step R) t -> { t' : term | Psi t' t} ).
intros t t_in_l; apply IH; right; trivial.
assert (H' : {ll : list (term * term) | map (@snd term term) ll = l /\
                                                     (forall s t, In (s,t) ll -> Psi s t \/ (s=t /\ nf (one_step R) t))}).
clear f Acc_t IH t_not_nf red_dec_fl not_inner_fl r rl.
induction l as [ | t l].
exists (@nil (term * term)); split; trivial.
intros; contradiction.
destruct IHl as [ll [H1 H2]].
intros; apply H; trivial; right; trivial.
destruct (nf_dec t) as [nf_t | not_nf_t].
exists ((t,t) :: ll); simpl; split.
subst l; trivial.
intros u v [uv_eq_tt | uv_in_ll].
injection uv_eq_tt; intros; do 2 subst.
right; split; trivial.
apply H2; trivial.
destruct (H t (or_introl _ (eq_refl _))) as [t' P]; trivial.
exists ((t',t) :: ll); simpl; split.
subst l; trivial.
intros u v [uv_eq_tt' | uv_in_ll].
injection uv_eq_tt'; intros; subst.
left; trivial.
apply H2; trivial.
destruct H' as [ll [H1 H2]].
exists (Term f (map (@fst term term) ll)).
rewrite <- H1; apply Psi_in_context; trivial.
assert (H3 : exists t, In t l /\ ~nf (one_step R) t).
unfold inner in not_inner_fl; simpl in not_inner_fl.
clear Acc_t IH t_not_nf red_dec_fl H H1 H2 r rl f.
induction l as [ | s l].
assert False; [idtac | contradiction].
apply not_inner_fl; intros; contradiction.
destruct (nf_dec s) as [nf_s | not_nf_s].
destruct IHl as [t [t_in_l H]].
intro; apply not_inner_fl.
simpl; intros u [u_eq_s | u_in_l].
subst; trivial.
apply H; trivial.
exists t; split; trivial; right; trivial.
exists s; split; trivial.
left; trivial.
destruct H3 as [t [t_in_l H4]].
destruct (H t t_in_l H4) as [t' H5].
exists t'; exists t; split; trivial.
rewrite <- H1 in t_in_l.
rewrite in_map_iff in t_in_l.
destruct t_in_l as [[u' u] [H6 H7]].
simpl in H6; subst u.
destruct (H2 _ _ H7) as [H8 | [H8  H9]].
replace t' with u'; trivial.
refine (Psi_unique  _ _ _ H8 H5).
assert False; [idtac | contradiction].
apply Psi_not_nf with t t'; trivial.
Defined.

Definition psi : forall (t : term), term.
Proof.
intros t.
assert (red_dec :=compute_red_is_correct rule_list Rreg' R Req).
assert (nf_dec := dec_nf _ _ red_dec).
destruct (nf_dec t) as [nf_t | not_nf_dec].
exact t.
destruct (Psi_def t not_nf_dec) as [t' H].
exact t'.
Defined.

Lemma psi_char : 
  forall t, (psi t = t /\ nf (one_step R) t) \/ (Psi (psi t) t).
Proof.
intros t; unfold psi.
destruct (dec_nf (one_step R) (compute_red rule_list)
                         (compute_red_is_correct rule_list Rreg' R Req) t).
left; split; trivial.
right; destruct (Psi_def t n) as [t' P]; trivial.
Qed.

Lemma psi_nf : forall t, nf (one_step R) t -> psi t = t.
Proof.
intros t nf_t; destruct (psi_char t) as [[H1 H2] | P]; trivial.
assert False; [idtac | contradiction].
apply (Psi_not_nf _ _ P nf_t).
Qed.

Lemma psi_not_nf : forall t, ~nf (one_step R) t -> Psi (psi t) t.
Proof.
intros t nf_t; destruct (psi_char t) as [[H1 H2] | P]; trivial.
absurd (nf (one_step R) t); trivial.
Qed.

Lemma Psi_psi : forall s t, Psi s t -> psi t = s.
Proof.
intros s t P; apply Psi_unique with t; trivial.
apply psi_not_nf.
intro H; apply (Psi_not_nf t s); trivial.
Qed.

Lemma Psi_in_context_bis :
   forall f l k, (exists t, In t l /\ ~nf (one_step R) t) -> k = map psi l -> Psi (Term f k) (Term f l).
Proof.
intros f l k K H; subst k.
replace (map psi l) with (map (@fst term term) (map (fun t => (psi t,t)) l)).
replace (Term f l) with (Term f (map (@snd term term) (map (fun t => (psi t,t)) l))).
apply Psi_in_context.
intros s t st_in_ll; rewrite in_map_iff in st_in_ll.
destruct st_in_ll as [t' [H t_in_l]]; injection H; clear H; intros; subst s t'.
destruct (psi_char t) as [[H1 H2] | P].
right; split; trivial.
left; trivial.
destruct K as [t [t_in_l not_nf_t]].
exists (psi t); exists t; split; trivial.
rewrite in_map_iff; exists t; split; trivial.
apply (f_equal (fun l => Term f l)).
pattern l at 2; rewrite <- map_id.
rewrite map_map; apply map_eq; intros s _; simpl; trivial.
rewrite map_map; apply map_eq; intros s _; simpl; trivial.
Qed.

Lemma psi_not_inner : forall f l, ~(inner R (Term f l)) -> psi (Term f l) = Term f (map psi l).
Proof.
intros f l not_nf_fl.
assert (red_dec :=compute_red_is_correct rule_list Rreg' R Req).
assert (nf_dec := dec_nf _ _ red_dec).
destruct (psi_char (Term f l)) as [[H1 H2] | P].
absurd (inner R (Term f l)); trivial.
intros s s_in_l; simpl in s_in_l.
apply nf_one_step_subterm with (Term f l); trivial.
apply Psi_unique with (Term f l); trivial.
apply Psi_in_context_bis; trivial.
inversion P; subst.
absurd (inner R (Term f l)); trivial.
destruct H3 as [s [t [st_in_llst not_nf_t]]].
exists t; split; trivial.
rewrite in_map_iff; exists (s,t); split; trivial.
Qed.

Lemma psi_inner_axiom : forall s t, inner R t -> axiom R s t -> psi t = s.
Proof.
intros s t H H'; destruct (psi_char t) as [[H1 H2] | P].
absurd (one_step R s t).
intro H''; apply (H2 s H'').
apply at_top; trivial.
apply Psi_unique with t; trivial.
apply Psi_at_top; trivial.
Qed.

Lemma Psi_rwr :  
  forall t s, Psi s t -> trans_clos (P_step R (inner R)) s t.
Proof.
assert (red_dec :=compute_red_is_correct rule_list Rreg' R Req).
assert (nf_dec := dec_nf _ _ red_dec).
intros t; pattern t; apply term_rec3; clear t.
intros v s P; assert False; [idtac | contradiction].
apply (Psi_not_nf (Var v) s); trivial.
apply nf_var.
intros f l IH s P; destruct (psi_char (Term f l)) as [[H1 H2] | P'].
assert False; [idtac | contradiction].
apply (Psi_not_nf (Term f l) s); trivial.
rewrite (Psi_unique _ _ _ P P').
inversion P'; clear P'; subst.
apply t_step; apply P_at_top; trivial.
rewrite H; rewrite psi_not_inner.
apply P_general_context.
destruct H3 as [s' [t [st_in_ll not_nf_t]]].
rewrite psi_not_inner in H.
injection H; clear H; intro H.
rewrite rwr_list_expand.
destruct (In_split _ _ st_in_ll) as [ll1 [ll2 H']]; subst.
exists t; exists s'; simpl.
exists (map (@snd term term) ll1).
exists (map (@snd term term) ll2).
exists (map (@fst term term) ll1).
exists (map (@fst term term) ll2).
split.
rewrite map_app; trivial.
split.
rewrite <- H; rewrite map_app; trivial.
assert (H' : forall kk, (forall u v, In (u,v) kk -> refl_trans_clos (P_step R (inner R)) u v) ->
                       refl_trans_clos (one_step_list (P_step R (inner R))) (map (@fst _ _) kk) 
                                                               (map (@snd _ _) kk)).
intros kk; induction kk as [ | [u1 v1] kk]; intros H'.
left; trivial.
simpl; rewrite refl_trans_clos_one_step_list_head_tail; split.
apply H'; left; apply eq_refl.
apply IHkk; intros; apply H'; right; assumption.
split.
apply H'; intros u v uv_in_ll1; destruct (H2 u v) as [H2' | [H2' _]].
apply in_or_app; left; trivial.
right; apply IH; trivial; rewrite in_map_iff; exists (u,v); split; trivial; apply in_or_app; left; trivial.
subst; left.
split.
apply IH.
rewrite in_map_iff; exists (s',t); split; trivial.
destruct (H2 s' t) as [H2' | [_ H2']]; trivial.
absurd (nf (one_step R) t); trivial.
apply H'; intros u v uv_in_ll2; destruct (H2 u v) as [H2' | [H2' _]].
apply in_or_app; do 2 right; trivial.
right; apply IH; trivial; rewrite in_map_iff; exists (u,v); split; trivial; apply in_or_app; do 2 right; trivial.
subst; left.
unfold inner; intro H'; apply not_nf_t; apply H'; simpl; 
rewrite in_map_iff; exists (s',t); split; trivial.
destruct H3 as [s' [t [st_in_ll not_nf_t]]].
unfold inner; intro H'; apply not_nf_t; apply H'; simpl; 
rewrite in_map_iff; exists (s',t); split; trivial.
Qed.

Lemma Psi_not_refl : forall t, Psi t t -> False.
Proof.
intro t; pattern t; apply term_rec3; clear t.
intros v P; assert False; [idtac | contradiction].
apply (Psi_not_nf (Var v) (Var v)); trivial.
apply nf_var.
intros f l IHl P; inversion P as [u v H Acc_u H3 | f' ll H K H1 H2]; clear P; subst.
apply (@cycle_not_acc _ (P_step R (inner R)) (Term f l)).
apply P_at_top; trivial.
apply wf_inner.
destruct K as [s [t [st_in_ll not_nf_t]]].
assert (s_eq_t : s = t).
clear H not_nf_t IHl; induction ll as [ | [u v] ll].
contradiction.
simpl in st_in_ll; destruct st_in_ll as [st_eq_uv | st_in_ll].
injection st_eq_uv; clear st_eq_uv; intros; subst; 
injection H2; clear H2; intros; subst; trivial.
apply IHll; trivial; injection H2; clear H2; intros; trivial.
destruct (H s t st_in_ll) as [P | [_ nf_t]].
subst s; apply (IHl t); trivial.
rewrite in_map_iff; exists (t,t); split; trivial.
apply not_nf_t; trivial.
Qed.

Lemma psi_two_cases :
  forall t, (nf (one_step R) t /\ psi t = t) \/ (~nf (one_step R) t /\ psi t <> t).
Proof.
intro t; pattern t; apply term_rec3; clear t.
intros v; left; split.
apply nf_var.
rewrite psi_nf; trivial; apply nf_var.
intros f l IH.
assert (red_dec :=compute_red_is_correct rule_list Rreg' R Req).
assert (nf_dec := dec_nf _ _ red_dec).
destruct (nf_dec (Term f l)) as [nf_fl | not_nf_fl].
left; split; trivial; rewrite psi_nf; trivial.
right; split; trivial.
intro H; destruct (psi_char (Term f l)) as [[H1 H2] | P].
apply not_nf_fl; trivial.
apply (Psi_not_refl (Term f l)); rewrite H in P; trivial.
Qed.


Lemma map_psi :
   forall f l, psi (Term f l) = Term f (map psi l) \/ 
                   (P_step R (inner R) (psi (Term f l)) (Term f (map psi l)) /\ 
                    inner R (Term f (map psi l))).
Proof.
intros f l; destruct (psi_char (Term f l)) as [[H1 H2] | P].
left; rewrite (psi_nf (Term f l)); trivial.
apply (f_equal (fun l => Term f l)).
pattern l at 1; rewrite <- map_id; apply map_eq.
intros s s_in_l; rewrite psi_nf; trivial.
apply nf_one_step_subterm with (Term f l); trivial.
inversion P as [s t H K | f' ll H K]; clear P; subst.
right; replace (Term f (map psi l)) with (Term f l).
split; trivial; apply P_at_top; trivial.
apply (f_equal (fun l => Term f l)).
pattern l at 1; rewrite <- map_id; apply map_eq.
intros s s_in_l; rewrite psi_nf; trivial.
apply K; trivial.
left; apply (f_equal (fun l => Term f l)).
rewrite map_map; apply map_eq.
intros [s t] st_in_ll; simpl.
destruct (H _ _ st_in_ll) as [H2 | [H2 nf_t]].
rewrite (Psi_psi _ _ H2); trivial.
rewrite psi_nf; trivial.
Qed.

Lemma psi_subst :
  forall sigma tau, tau = map (fun xval => (@fst variable term xval, psi (@snd variable term xval))) sigma ->
   forall t, refl_trans_clos (P_step R (inner R)) (psi (apply_subst sigma t)) (apply_subst tau t).
Proof.
intros sigma tau H;
assert (Hvar : forall v,  apply_subst tau (Var v) = psi (apply_subst sigma (Var v))).
intros v; simpl; subst tau.
assert (H3 := @find_map _ X.eq_bool _ _ psi v sigma).
destruct (find X.eq_bool v sigma) as [val | ]; rewrite H3; trivial.
rewrite psi_nf; trivial; apply nf_var.
intro t; pattern t; apply term_rec3; clear t.
intros v; rewrite Hvar; left.
intros f l IHl; simpl.
destruct (map_psi f (map (apply_subst sigma) l)) as [H1 | [H1 H1']].
rewrite H1.
assert (H2 : refl_trans_clos (one_step_list (P_step R (inner R))) (map psi (map (apply_subst sigma) l))
                                             (map (apply_subst tau) l)).
rewrite map_map; rewrite refl_trans_clos_one_step_list_refl_trans_clos_alt; trivial.
inversion H2 as [l2 | l1 l2 K2].
left.
right; apply P_general_context; trivial.
assert (H2 : refl_trans_clos (one_step_list (P_step R (inner R))) (map psi (map (apply_subst sigma) l))
                                             (map (apply_subst tau) l)).
rewrite map_map; rewrite refl_trans_clos_one_step_list_refl_trans_clos_alt; trivial.
inversion H2 as [l2 | l1 l2 K2].
right; apply t_step; trivial.
right; apply trans_clos_is_trans with (Term f (map psi (map (apply_subst sigma) l))).
apply t_step; trivial.
apply P_general_context; trivial.
Qed.

Lemma Psi_sim_inner_at_top :
  forall t s, axiom R s t ->  inner R t -> refl_trans_clos (one_step R) (psi s) (psi t).
Proof. 
intros t s H It; inversion H as [r l sigma H']; clear H; subst.
destruct (psi_char (apply_subst sigma l)) as [[_ H] | P].
(* 1/2 t -> s at top and t in normal form -> absurd *)
absurd (one_step R (apply_subst sigma r) (apply_subst sigma l)).
intro H''; apply (H _ H'').
apply at_top; apply instance; trivial.
(* 1/1 t -> s at top and psi(t) defined *)
inversion P as [u v H Acc_u H3 | f' ll H K H1 H2]; clear P; subst.
(* 1/2 t -> s at top and Psi t' t by Psi_at_top -> s = t' *)
assert (H7 : psi (apply_subst sigma l) = apply_subst sigma r).
apply (UIR (apply_subst sigma l)); trivial.
apply instance; trivial.
rewrite H7.
destruct (psi_char (apply_subst sigma r)) as [[H1 H2] | P].
rewrite H1; left; split; trivial.
right; apply trans_incl with (P_step R (inner R)).
intros s t H6; apply P_step_one_step with (inner R); trivial.
apply Psi_rwr; trivial.
(* 1/1 t -> s at top, and Psi t' t by Psi_in_context : absurd *)
destruct K as [s [t [st_in_ll not_nf_t]]].
absurd (nf (one_step R) t); trivial.
apply It; rewrite <- H2; simpl; rewrite in_map_iff; exists (s,t); split; trivial.
Qed.

Lemma Psi_sim_inner :
  forall t s, P_step R (inner R) s t ->  refl_trans_clos (one_step R) (psi s) (psi t).
Proof. 
intro t; pattern t; apply term_rec3; clear t.
intros v s H; apply False_rect.
inversion H as [t1 t2 H' | f' l1 l2 H']; clear H; subst.
apply (nf_var v s); apply at_top; trivial.
intros f l IHl s H; inversion H as [t1 t2 H' | f' l1 l2 H']; clear H; subst.
destruct (Psi_sim_inner_at_top _ _ H0 H') as [H1 | H1].
left; trivial.
right; trivial.
destruct (P_step_in_list _ _ _ _ H') as [t [s [k1 [k2 [H1 [H2 H3]]]]]].
destruct (psi_char (Term f l)) as [[K1 K2] | P].
apply False_rect.
rewrite one_step_nf_inner_step_nf in K2.
apply (K2 (Term f l2)); apply P_in_context; trivial.
apply Rvar.
inversion P as [ss tt H K | g ll H4 K]; clear P.
subst ss tt.
assert False; [idtac | contradiction].
refine (K t _ s _).
simpl; subst l; apply in_or_app; right; left; trivial.
apply P_step_one_step with (inner R); trivial.
subst g.
assert (H6 : map (fst (A:=term) (B:=term)) ll = map psi l).
rewrite <- H5; clear K H5 H.
induction ll as [ | [u v] ll]; trivial.
simpl; rewrite <- IHll.
apply (f_equal (fun t => t :: map (fst (A:=term) (B:=term)) ll)).
destruct (H4 _ _ (or_introl _ (eq_refl _))) as [H5 | [H5 H6]].
apply Psi_unique with v; trivial.
apply psi_not_nf; intro H6; apply (Psi_not_nf v u); trivial.
rewrite psi_nf; trivial.
intros; apply H4; right; trivial.
rewrite H6 in *.
clear H4 H5 H6; rename H into H4.
destruct (map_psi f l2) as [H5 | [H5 H5']].
rewrite H4; rewrite H5.
assert (t_in_k : In t (k1 ++ t :: k2)).
apply in_or_app; right; left; trivial.
rewrite <- H2 in t_in_k.
rewrite <- H4.
rewrite H2, H3; do 2 rewrite map_app; simpl.
assert (IH' := IHl _ t_in_k _ H1); inversion IH' as [x | ps pt H6].
left.
right; apply context_in; assumption.
assert (t_in_k : In t (k1 ++ t :: k2)).
apply in_or_app; right; left; trivial.
rewrite <- H2 in t_in_k.
apply refl_trans_clos_is_trans with (Term f (map psi l2)).
right; left; apply P_step_one_step with (inner R); trivial.
rewrite H2, H3, map_app, map_app; simpl.
assert (IH':= IHl _ t_in_k _ H1); inversion IH' as [x | ps pt H6].
left.
right; apply context_in; assumption.
Qed.

Lemma Psi_sim_one_step :
  forall t s, one_step R s t -> rwr R (psi s) (psi t) \/ P_step R (inner R) s t \/ exists s', rwr R s s' /\ P_step R (inner R) s' t.
Proof.
assert (W : well_founded (union _ (P_step R (inner R)) direct_subterm)).
intro t; rewrite <-P_acc_with_subterm; apply wf_inner.
intro t; pattern t; refine (well_founded_ind W _ _ t); clear t.
(* 1/1 one_step R s t *)
intros t IHt s H; inversion H as [t1 t2 H' | f' l1 l2 H']; clear H; subst.
(* 1/2 one_step at top : axiom R s (Term f l) *)
rename H' into H; inversion H as [r l sigma H']; clear H; subst.
destruct (psi_char (apply_subst sigma l)) as [[_ H] | P].
(* 1/3 t -> s at top and t in normal form -> absurd *)
absurd (one_step R (apply_subst sigma r) (apply_subst sigma l)).
intro H''; apply (H _ H'').
apply at_top; apply instance; trivial.
(* 1/2 t -> s at top and psi(t) defined *)
inversion P as [u v H Acc_u H3 | f' ll H K H1 H2]; clear P; subst.
(* 1/3 t -> s at top and Psi t' t by Psi_at_top -> s = t' *)
assert (H7 : psi (apply_subst sigma l) = apply_subst sigma r).
apply (UIR (apply_subst sigma l)); trivial.
apply instance; trivial.
rewrite H7.
destruct (psi_char (apply_subst sigma r)) as [[H1 H2] | P].
right; left; apply P_at_top; trivial; apply instance; trivial.
left; apply trans_incl with (P_step R (inner R)).
intros s t H6; apply P_step_one_step with (inner R); trivial.
apply Psi_rwr; trivial.
(* 1/2 t -> s at top, and Psi t' t by Psi_in_context *)
set (tau := map (fun xval => (@fst variable term xval, psi (@snd variable term xval))) sigma).
assert (red_dec :=compute_red_is_correct rule_list Rreg' R Req).
assert (nf_dec := dec_nf _ _ red_dec).
assert (inner_dec := nf_dec_inner_dec _ nf_dec).
destruct (AICR _ _ sigma H') as [H6 | H6].
assert (H3' : psi (apply_subst sigma l) = apply_subst tau l).
assert (H4 : forall s p, subterm_at_pos l p = Some s ->  
                      psi (apply_subst sigma s) = apply_subst tau s).
intro s; pattern s; apply term_rec3; clear s.
intros v p Sub; simpl; subst tau.
assert (H5 := @find_map _  X.eq_bool _ _ psi v sigma).
destruct (find X.eq_bool v sigma) as [val | ]; rewrite H5; trivial.
apply psi_nf; apply nf_var.
intros f k IH p Sub.
assert (H3' : forall s, In s k -> psi (apply_subst sigma s) = apply_subst tau s).
intros s s_in_k; destruct (In_split _ _ s_in_k) as [k1 [k2 H4]]; subst k.
apply (IH s s_in_k (p ++ (length k1 :: nil))).
apply subterm_in_subterm with (Term f (k1 ++ s :: k2)); trivial.
simpl; rewrite nth_error_at_pos; trivial.
destruct (inner_dec (apply_subst sigma (Term f k))) as [inner_fk | not_inner_fk].
destruct (psi_char (apply_subst sigma (Term f k))) as [[H4 H5] | P].
rewrite H4; simpl; apply (f_equal (fun l => Term f l)); apply map_eq.
intros s s_in_k; rewrite <- H3'; trivial.
apply sym_eq; apply psi_nf.
apply nf_one_step_subterm with (apply_subst sigma (Term f k)); trivial.
simpl; rewrite in_map_iff; exists s; split; trivial.
inversion P as [s t H'' _ | f'' ll' H'' K']; clear P; subst.
inversion H'' as [d g phi H3 H4 H5].
destruct (H6 p g d phi H3) as [H7 | H7].
rewrite H5.
generalize (subterm_at_pos_apply_subst_apply_subst_subterm_at_pos l p sigma).
rewrite Sub; simpl; trivial.
rewrite H5; trivial.
subst p; injection Sub; clear Sub; intro Sub; subst l.
simpl; rewrite psi_not_inner.
apply (f_equal (fun l => Term f l)).
rewrite map_map; apply map_eq; trivial.
intro H7; destruct K as [s [t [st_in_ll not_nf_t]]]; apply not_nf_t.
apply H7; simpl in H2; rewrite <- H2; simpl; rewrite in_map_iff; exists (s,t); split; trivial.
destruct H7 as [q [q' [v [H7 Sub']]]]; subst p.
destruct (subterm_in_subterm2 _ _ _ Sub) as [u [Sub'' H7]].
rewrite Sub' in Sub''; injection Sub''; clear Sub''; intro; subst u.
destruct q'; discriminate.
destruct K' as [s' [t' [st_in_ll' not_nf_t']]].
absurd (nf (one_step R) t'); trivial.
apply inner_fk; simpl; rewrite <- H4; rewrite in_map_iff; exists (s',t'); split; trivial.
simpl; rewrite psi_not_inner; trivial.
apply (f_equal (fun l => Term f l)); rewrite map_map; apply map_eq; trivial.
apply (H4 l (@nil nat)); simpl; trivial.
rewrite H1; rewrite H3'.
assert (P := psi_subst sigma tau (eq_refl _) r).
inversion P as [pr H4 H4' | pr pr' H4].
left; apply t_step; apply at_top; rewrite H4'; apply instance; trivial.
left; apply trans_clos_is_trans with (apply_subst tau r).
apply trans_incl with (P_step R (inner R)); trivial.
intros s t H''; apply P_step_one_step with (inner R); trivial.
apply t_step; apply at_top; apply instance; trivial.

right; right; rewrite H2; destruct H6 as [s' [H6 H7]]; exists s'; split; trivial.

destruct (one_step_in_list H') as [t [s [k1 [k2 [H1 [H2 H3]]]]]].
destruct (psi_char (Term f' l2)) as [[K1 K2] | P].
apply False_rect.
apply (K2 (Term f' l1)); apply in_context; trivial.
inversion P as [ss tt H K | g ll H4 K]; clear P.
subst ss tt.
apply False_rect.
refine (K t _ s H1); simpl; subst l2; apply in_or_app; right; left; trivial.
subst g.
assert (H6 : map (fst (A:=term) (B:=term)) ll = map psi l2).
rewrite <- H5; clear K H5 H.
induction ll as [ | [u v] ll]; trivial.
simpl; rewrite <- IHll.
apply (f_equal (fun t => t :: map (fst (A:=term) (B:=term)) ll)).
destruct (H4 _ _ (or_introl _ (eq_refl _))) as [H5 | [H5 H6]].
apply Psi_unique with v; trivial.
apply psi_not_nf; intro H6; apply (Psi_not_nf v u); trivial.
rewrite psi_nf; trivial.
intros; apply H4; right; trivial.
rewrite H6 in *; rewrite H5 in *.
clear H4 H5 H6; rename H into H4.
destruct (map_psi f' l1) as [H5 | [H5 H5']].
rewrite H5.
assert (t_in_k : In t (k1 ++ t :: k2)).
apply in_or_app; right; left; trivial.
rewrite <- H2 in t_in_k.
destruct (IHt t (or_intror _ t_in_k) _ H1) as [H6 | [H6 | [s' [H6 H7]]]].
left; subst l1 l2; do 2 rewrite map_app; simpl; apply context_in; trivial.
right; left; subst l1 l2; apply P_step_context_in; trivial.
do 2 right; subst l1 l2; exists (Term f' (k1 ++ s' :: k2)); split.
apply context_in; trivial.
apply P_step_context_in; trivial.
assert (t_in_k : In t (k1 ++ t :: k2)).
apply in_or_app; right; left; trivial.
rewrite <- H2 in t_in_k.
destruct (IHt t (or_intror _ t_in_k) _ H1) as [H6 | [H6 | [s' [H6 H7]]]].
left; apply trans_clos_is_trans with (Term f' (map psi l1)).
apply t_step; apply P_step_one_step with (inner R); trivial.
subst l2 l1; do 2 rewrite map_app; simpl; apply context_in; assumption.
right; left; subst l1 l2; apply P_step_context_in; trivial.
do 2 right; subst l1 l2; exists (Term f' (k1 ++ s' :: k2)); split.
apply context_in; trivial.
apply P_step_context_in; trivial.
Qed.

Definition psi_id t := (psi t, t).
Definition oo := @lex term term eq_bool (rwr R) (trans_clos (P_step R (inner R))).
Definition ooo s t := oo (psi_id s) (psi_id t).

Lemma acc_psi_acc_ooo :
  forall pt, Acc (one_step R) pt -> forall t, psi t = pt -> Acc ooo t.
Proof.
intros a Acc_a; generalize (acc_trans Acc_a); clear Acc_a; intro Acc_a. 
induction Acc_a as [a Acc_a IHa].
intros t H; subst a.
generalize Acc_a IHa; clear Acc_a IHa;
pattern t; refine (well_founded_ind (wf_trans wf_inner) _ _ t); clear t.
intros t IH Acc_psi_t Acc_t.
apply Acc_intro; intros s H.
unfold ooo, oo, psi_id in *.
unfold lex in H.
revert H;
generalize (eq_bool_ok (psi s) (psi t)); case (eq_bool (psi s) (psi t)); [intro psi_s_eq_psi_t | intro psi_s_diff_psi_t].
intro H; apply (IH s H); rewrite psi_s_eq_psi_t; trivial.
intro H; apply Acc_t with (psi s); trivial.
Qed.

Lemma acc_psi_acc : forall t, Acc (one_step R) (psi t) -> Acc (one_step R) t.
Proof.
intros t Acc_psi_t;
assert (Acc_t := acc_psi_acc_ooo _ Acc_psi_t t (eq_refl _)).
generalize Acc_psi_t; clear Acc_psi_t; induction Acc_t as [t Acc_t IH].
intros Acc_psi_t; apply Acc_intro; intros s H.
destruct (Psi_sim_one_step t s H) as [H1 | [H1 | [s' [H1 H2]]]]; unfold ooo, oo, psi_id in *.
apply IH; unfold lex.
generalize (eq_bool_ok (psi s) (psi t)); case (eq_bool (psi s) (psi t)); [intro psi_s_eq_psi_t | intro psi_s_diff_psi_t]; trivial.
absurd (Acc (rwr R) (psi t)).
apply cycle_not_acc; rewrite psi_s_eq_psi_t in H1; trivial.
rewrite <- acc_one_step; trivial.
rewrite acc_one_step; rewrite acc_one_step in Acc_psi_t.
destruct Acc_psi_t as [Acc_psi_t]; apply Acc_psi_t; trivial.

apply IH; unfold lex.
generalize (eq_bool_ok (psi s) (psi t)); case (eq_bool (psi s) (psi t)); [intro psi_s_eq_psi_t | intro psi_s_diff_psi_t]; trivial.
apply t_step; trivial.
assert (P := Psi_sim_inner _ _ H1).
inversion P as [p H2 H2'| ps pt H2]; clear P; trivial.
absurd (psi s = psi t); trivial.
assert (P := Psi_sim_inner _ _ H1).
inversion P as [p H2 H2'| ps pt H2]; clear P.
rewrite H2'; trivial.
rewrite acc_one_step; rewrite acc_one_step in Acc_psi_t.
destruct Acc_psi_t as [Acc_psi_t]; apply Acc_psi_t; trivial.

assert (Acc_s' : Acc (rwr R) s').
rewrite <- acc_one_step.
apply IH; unfold lex.
generalize (eq_bool_ok (psi s') (psi t)); case (eq_bool (psi s') (psi t)); [intro psi_s_eq_psi_t | intro psi_s_diff_psi_t]; trivial.
apply t_step; trivial.
assert (P := Psi_sim_inner _ _ H2).
inversion P as [p H3 H3'| ps' pt H3]; clear P; trivial.
absurd (psi s' = psi t); trivial.
assert (P := Psi_sim_inner _ _ H2).
inversion P as [p H3 H3'| ps' pt H3]; clear P; trivial.
rewrite H3'; trivial.
rewrite acc_one_step; rewrite acc_one_step in Acc_psi_t.
destruct Acc_psi_t as [Acc_psi_t]; apply Acc_psi_t; trivial.
rewrite acc_one_step.
destruct Acc_s' as [Acc_s']; apply Acc_s'; trivial.
Qed.

Lemma acc_inner_acc : forall t, Acc (one_step R) t.
Proof.
intro t; pattern t; refine (well_founded_ind (wf_trans wf_inner) _ _ t); clear t.
intros t IH; apply acc_psi_acc.
destruct (psi_char t) as [[H3 H4] | H3].
rewrite H3; apply Acc_intro; intros s H.
assert False; [idtac | contradiction].
apply (H4 _ H).
apply IH; apply Psi_rwr; trivial.
Qed.

Lemma wf_inner_wf : well_founded (one_step R).
Proof.
intro t; apply acc_inner_acc.
Qed.

End Psi_definition.

Lemma wf_inner_no_wf : 
  forall R : relation term,
  (forall (t : term) (x : variable), ~ R t (Var x)) ->
  (forall s t : term, R s t -> forall x : variable, In x (var_list s) -> In x (var_list t)) ->
  forall rule_list : list (term * term), (forall l r : term, R r l <-> In (l, r) rule_list) ->
  well_founded (P_step R (inner R)) ->
  non_overlapping R -> well_founded (one_step R).
Proof.
intros R Rvar Rreg rule_list Req wf_inner NO.
apply wf_inner_wf with rule_list; trivial.

intros t s s' It H H'; inversion H as [r l sigma]; inversion H' as [d g tau]; subst.
assert (H6 := NO l r g d sigma tau H0 H3).
destruct l as [v | f l].
absurd (R r (Var v)); trivial.
destruct (H6 f l (@nil nat) (eq_refl _) (sym_eq H5)) as [ _ [H7 H8]]; clear H6; subst.
apply sym_eq; rewrite <- subst_eq_vars.
intros v v_in_d; rewrite <- subst_eq_vars in H5.
apply H5; apply Rreg with d; trivial.

intros l r sigma H0; left; intros p g d tau H3 Sub Igtau.
assert (H6 := NO l r g d sigma tau H0 H3).
assert (H7 := subterm_in_instantiated_term _ _ _ Sub).
case_eq (subterm_at_pos l p).
intros u' Sub'; rewrite Sub' in H7.
destruct u' as [v | f' l'].
right; exists p; exists (@nil nat); exists v; split; trivial; rewrite app_nil_r; trivial.
destruct (H6 f' l' p Sub' (sym_eq H7)) as [p_eq_nil _]; left; trivial.
intros Sub'; rewrite Sub' in H7.
destruct H7 as [v [q [q' [H7 [v_in_l [Sub'' Sub3]]]]]].
right; exists q; exists q'; exists v; split; trivial.
Qed.

End Make.
