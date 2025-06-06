(**************************************************************************)
(*           *                                                            *)
(*     _     *   The Coccinelle Library / Evelyne Contejean               *)
(*    <o>    *          CNRS-LRI-Universite Paris Sud                     *)
(*  -/@|@\-  *                   A3PAT Project                            *)
(*  -@ | @-  *                                                            *)
(*  -\@|@/-  *      This file is distributed under the terms of the       *)
(*    -v-    *      CeCILL-C licence                                      *)
(*           *                                                            *)
(**************************************************************************)


(** * Termination of rewriting *)

From Stdlib Require Import List Relations Wellfounded Arith Recdef Setoid.
From CoLoR Require Import closure more_list weaved_relation term equational_theory_spec.
From CoLoR Require Import NatCompat.

(** ** Module Type Termin, for termination of rewriting systems. *)

Module MakeDP (E : EqTh).

  Import E.
  Import T.

Inductive dp (R : relation term) : term -> term -> Prop:= 
  | Dp : forall t1 t2 p f2 l2, R t2 t1 -> 
                subterm_at_pos t2 p = Some (Term f2 l2) -> defined R f2 -> 
                dp R (Term f2 l2) t1.

Inductive rdp_step (R1 R2 : relation term) : term -> term -> Prop :=
   | Rdp_step : forall f l1 l2 t3, refl_trans_clos (one_step_list (one_step R2)) l2 l1 -> R1 t3 (Term f l2) -> 
                              rdp_step R1 R2 t3 (Term f l1).

Lemma dp_incl : forall R1 R2, @inclusion _ R1 R2 -> @inclusion _ (dp R1) (dp R2).
Proof.
intros R1' R2' R1_in_R2 t1 t2 H.
inversion H as [t1' t2' p f2 l2 H' Subt Df2]; subst.
apply (Dp R2' t2 t2' p f2 l2); trivial.
apply R1_in_R2; trivial.
inversion Df2 as [g2 l u H1]; subst.
apply (Def R2' f2 l u).
apply R1_in_R2; trivial.
Qed.

Lemma rdp_step_incl : forall R R' R1 R2, @inclusion _ R R' -> @inclusion _ R1 R2 ->  
               @inclusion _ (rdp_step (axiom (dp R)) R1) (rdp_step (axiom (dp R')) R2).
Proof.
intros R R' R1' R2' R_in_R' R1_in_R2 t1 t2 H.
inversion H as [g k l' s'' l_R_l' Hm]; clear H; subst.
apply Rdp_step with l'.
apply refl_trans_incl with (one_step_list (one_step R1')); trivial.
do 2 intro; apply one_step_list_incl.
apply one_step_incl; assumption.
inversion Hm as [u1 u2 sigma]; clear Hm; subst.
apply instance.
apply dp_incl with R; assumption.
Qed.

Lemma rwr_subterm_rdp_rdp :
  forall R1 R2 f l1 l2 t, refl_trans_clos (one_step_list (one_step R1)) l2 l1 -> rdp_step R2 R1 t (Term f l2) -> 
      rdp_step R2 R1 t (Term f l1).
Proof.
intros R1 R2 f l1 l2 t H H'.
inversion H' as [f' l2' l3 t' K K']; clear H'; subst.
apply Rdp_step with l3; trivial.
apply refl_trans_clos_is_trans with l2; trivial.
Qed.

Lemma one_step_subterm_rdp_rdp :
  forall R1 R2 f l1 l2 t, one_step_list (one_step R1) l2 l1 -> rdp_step R2 R1 t (Term f l2) -> 
      rdp_step R2 R1 t (Term f l1).
Proof.
intros R1 R2 f l1 l2 t H H'.
apply rwr_subterm_rdp_rdp with l2; trivial.
right; left; assumption.
Qed.

Lemma one_step_subterm_acc_rdp_acc_rdp :
  forall R1 R2 f l1 l2, one_step_list (one_step R1) l2 l1 -> Acc (rdp_step R2 R1) (Term f l1) -> 
      Acc (rdp_step R2 R1) (Term f l2).
Proof.
intros R1 R2 f l1 l2 H Acc_t1; apply Acc_intro; intros t H'.
apply Acc_inv with (Term f l1); trivial.
apply one_step_subterm_rdp_rdp with l2; trivial.
Qed.

Lemma rwr_subterm_acc_rdp_acc_rdp :
  forall R1 R2 f l1 l2, refl_trans_clos (one_step_list (one_step R1)) l2 l1 -> Acc (rdp_step R2 R1) (Term f l1) -> 
      Acc (rdp_step R2 R1) (Term f l2).
Proof.
intros R1 R2 f l1 l2 H Acc_t1; apply Acc_intro; intros t H'.
apply Acc_inv with (Term f l1); trivial.
apply rwr_subterm_rdp_rdp with l2; assumption.
Qed.

Definition dp_step R := rdp_step (axiom (dp R)) R.

Lemma acc_one_step_acc_dp :
 forall R, (forall x t, ~ (R t (Var x))) -> 
    forall t, Acc (one_step R)  t -> Acc (dp_step R) t.
Proof.
intros R HR.
assert (H : forall s t, axiom (dp R) s t -> trans_clos (@union term (one_step R) direct_subterm) s t).
intros s t H'.
inversion H' as [s' t' sigma H]; clear H'; subst.
inversion H as [t1 t2 p f l H'' H3 Df]; clear H; subst.
assert (H4 := subterm_at_pos_apply_subst_apply_subst_subterm_at_pos t2 p sigma); rewrite H3 in H4.
destruct (subterm_subterm _ _ H4) as [H1 | H2].
apply t_step; left; apply at_top; rewrite <- H1; apply instance; trivial.
apply trans_clos_is_trans with (apply_subst sigma t2).
apply trans_incl with direct_subterm; trivial.
intros s t H; right; trivial.
apply t_step; left; apply at_top; apply instance; trivial.

intros t Acc_t; apply Acc_incl with (trans_clos (@union term (one_step R) direct_subterm)).
clear t Acc_t; intros s t H'; inversion H' as [f' l1 l2 H1 H2 H3]; clear H'; subst.
inversion H2 as [l | k1 k2 K2]; clear H2; subst.
apply H; assumption.
apply trans_clos_is_trans with (Term f' l2).
apply H; trivial.
apply trans_incl with (one_step R).
intros s' t' H'; left; trivial.
apply general_context; trivial.
apply acc_trans; trivial.
rewrite <- acc_with_subterm; assumption.
Qed.

Lemma dp_necessary : 
 forall R, (forall x t, ~ (R t (Var x))) -> 
    well_founded (one_step R)  -> well_founded (dp_step R).
Proof.
intros R HR Wf.
intro t; apply acc_one_step_acc_dp; trivial.
Qed.

(** Plain standard dependency pair criterion *)
Lemma dp_criterion_local : 
  forall R, (forall x t, ~ (R t (Var x))) -> 
  (forall s t, R s t -> forall x, In x (var_list s) -> In x (var_list t)) ->
  (forall f, {constructor R f} + {defined R f}) ->
  forall t,   Acc (dp_step R)  t -> (forall s, direct_subterm s t -> Acc (one_step R) s) ->
              Acc (one_step R) t.
Proof.
intros R HR RR CD.
(* main proof *)
intros t Acc_t; induction Acc_t as [t Acc_t IH].
intros Acc_l; destruct t as [x | f l].
apply Acc_var; assumption.
simpl in Acc_l; rewrite acc_one_step_list in Acc_l; revert IH.
induction Acc_l as [l Acc_l IHl]; intros IH'.
assert (Acc_l' : forall t, In t l -> Acc (one_step R) t).
rewrite acc_one_step_list; apply Acc_intro; exact Acc_l.
apply Acc_intro; 
intros s H; destruct s as [x1 | f1 l1].
apply Acc_var; assumption.
inversion H as [t1 t2 H' | f' l1' l2 H']; clear H; subst.
(* 1/2 rewrite step at the top *)
inversion H' as [t1 t2 sigma t1_R_t2 H1 H2]; clear H'.
destruct t2 as [x | g k].
absurd (R t1 (Var x)); trivial; apply HR.
simpl in H2; injection H2; clear H2; intros; subst g l.
assert (H'' : forall n t, size (apply_subst sigma t) <= n -> (exists p, subterm_at_pos t1 p = Some t) ->
                                                        Acc (one_step R) (apply_subst sigma t)).
intro n; induction n as [ | n].
intros t St; absurd (1 <= 0); auto with arith; 
apply Nat.le_trans with (size (apply_subst sigma t)); trivial; apply size_ge_one.
intros [x | g h] St [p H''].
(* 1/4 t is a variable *)
apply E.var_acc with k; trivial.
assert (H : In x (var_list (Term f k))).
apply RR with t1; trivial.
apply var_in_subterm with (Var x) p; trivial.
simpl; left; trivial.
rewrite var_list_unfold in H; trivial.
(* 1/3 t = Term g h *)
assert (Acc_h : forall t, In t h -> Acc (one_step R) (apply_subst sigma t)).
intros t t_in_h; apply IHn.
apply le_S_n; refine (Nat.le_trans _ _ _ _ St); apply size_direct_subterm; simpl.
rewrite in_map_iff; exists t; split; trivial.
destruct (In_split _ _ t_in_h) as [h' [h'' K]]; subst h.
exists (p ++ (length h' :: nil)).
apply subterm_in_subterm with (Term g (h' ++ t :: h'')).
assumption.
simpl; rewrite nth_error_at_pos; trivial.
destruct (CD g) as [Cg | Dg].
(* 1/4 g is a constructor symbol *)
simpl; apply acc_subterms; trivial.
intros t t_in_map_h; rewrite in_map_iff in t_in_map_h.
destruct t_in_map_h as [t' [H''' t'_in_h]]; subst; apply Acc_h; trivial.
(* 1/3 g is a defined symbol *)
apply IH'.
apply Rdp_step with (map (apply_subst sigma) k).
left.
replace (Term f (map (apply_subst sigma) k)) with (apply_subst sigma (Term f k)); trivial.
apply instance; apply Dp with t1 p; trivial.
intros s s_in_h; simpl in s_in_h; rewrite in_map_iff in s_in_h.
destruct s_in_h as [_s [_ssig_eq_s _s_in_h]]; subst.
apply Acc_h; trivial.
apply (H'' (size (Term f1 l1))).
rewrite H1; apply le_n.
exists (@nil nat); simpl; trivial.
(* 1/1 rewrite step NOT at the top *)
apply IHl; trivial.
intros t H; apply Acc_t; apply one_step_subterm_rdp_rdp with l1; trivial.

intros s H'' H'''; apply IH'; trivial.
apply one_step_subterm_rdp_rdp with l1; trivial.
Defined.

Lemma dp_criterion : 
  forall R, (forall x t, ~ (R t (Var x))) -> 
  (forall s t, R s t -> forall x, In x (var_list s) -> In x (var_list t)) ->
  (forall f, {constructor R f} + {defined R f}) ->
   well_founded (dp_step R)  -> well_founded (one_step R).
Proof.
intros R HR RR CD Wf t; pattern t; apply term_rec3; clear t.
intro x; apply Acc_var; trivial.
intros; apply dp_criterion_local; trivial.
Defined.


(** Standard dependency pair criterion with minimal chains *)

Definition acc_sub R t := forall s, direct_subterm s t -> Acc (one_step R) s.
Definition dp_step_min R := rest (acc_sub R) (dp_step R).

Lemma dp_criterion_min_local : 
  forall R, (forall x t, ~ (R t (Var x))) -> 
  (forall s t, R s t -> forall x, In x (var_list s) -> In x (var_list t)) ->
  (forall f, {constructor R f} + {defined R f}) ->
  forall t,   Acc (dp_step_min R)  t -> (forall s, direct_subterm s t -> Acc (one_step R) s) ->
              Acc (one_step R) t.
Proof.
intros R HR RR CD.
(* main proof *)
intros t Acc_t; induction Acc_t as [t Acc_t IH].
intros Acc_l; destruct t as [x | f l].
apply Acc_var; assumption.
simpl in Acc_l; rewrite acc_one_step_list in Acc_l; revert Acc_t IH.
induction Acc_l as [l Acc_l IHl].
revert l Acc_l IHl.
assert (Main : 
forall l (Hsub : Acc (one_step_list (one_step R)) l)
(IH2 : forall y (Hy : one_step_list (one_step R) y l)
 (Ht' : Acc (dp_step_min R) (Term f y))
 (Hsub' : forall y0, dp_step_min R y0 (Term f y) ->
       (forall s : term, direct_subterm s y0 -> Acc (one_step R) s) -> Acc (one_step R) y0),
 Acc (one_step R) (Term f y))

     (Ht : Acc (dp_step_min R) (Term f l)) 
     (IH1 : forall y, dp_step_min R y (Term f l) ->
                (forall s : term, direct_subterm s y -> Acc (one_step R) s) -> Acc (one_step R) y), 
Acc (one_step R) (Term f l)).
intros l Acc_l IH2 Acc_t IH1.
apply Acc_intro; intros s H; destruct s as [x1 | f1 l1].
apply Acc_var; assumption.
inversion H as [t1 t2 H' | f' l1' l2 H']; clear H; subst.
(* 1/2 rewrite step at the top *)
inversion H' as [t1 t2 sigma t1_R_t2 H1 H2]; clear H'.
destruct t2 as [x | g k].
absurd (R t1 (Var x)); trivial; apply HR.
simpl in H2; injection H2; clear H2; intros; subst g l.
assert (H'' : forall n t, size t <= n -> (exists p, subterm_at_pos t1 p = Some t) ->
                                                        Acc (one_step R) (apply_subst sigma t)).
intro n; induction n as [ | n].
intros t St; absurd (1 <= 0); auto with arith; 
apply Nat.le_trans with (size t); trivial; apply size_ge_one.
intros [x | g h] St [p H''].
(* 1/4 t is a variable *)
apply E.var_acc with k. 
apply (RR _ _ t1_R_t2 x).
apply var_in_subterm with (Var x) p; trivial.
left; trivial.
rewrite acc_one_step_list; assumption.
(* 1/3 t = Term g h *)
assert (Acc_h : forall t, In t h -> Acc (one_step R) (apply_subst sigma t)).
intros t t_in_h; apply IHn.
apply le_S_n; refine (Nat.le_trans _ _ _ _ St); apply size_direct_subterm; assumption.
destruct (In_split _ _ t_in_h) as [h' [h'' K]]; subst h.
exists (p ++ (length h' :: nil)).
apply subterm_in_subterm with (Term g (h' ++ t :: h'')).
assumption.
simpl; rewrite nth_error_at_pos; trivial.
destruct (CD g) as [Cg | Dg].
(* 1/4 g is a constructor symbol *)
simpl; apply acc_subterms; trivial.
intros t t_in_map_h; rewrite in_map_iff in t_in_map_h.
destruct t_in_map_h as [t' [H''' t'_in_h]]; subst; apply Acc_h; trivial.
(* 1/3 g is a defined symbol *)
apply IH1.
split.
apply Rdp_step with (map (apply_subst sigma) k).
left.
replace (Term f (map (apply_subst sigma) k)) with (apply_subst sigma (Term f k)); trivial.
apply instance; apply Dp with t1 p; trivial.
split.
intros s s_in_h; simpl in s_in_h; rewrite in_map_iff in s_in_h.
destruct s_in_h as [_s [_ssig_eq_s _s_in_h]]; subst.
apply Acc_h; trivial.
unfold acc_sub; simpl; rewrite acc_one_step_list; assumption.
intros s s_in_h; simpl in s_in_h.
rewrite in_map_iff in s_in_h.
destruct s_in_h as [u [H2 u_in_h]]; subst.
apply Acc_h; trivial.
apply (H'' (size t1)).
apply le_n.
exists (@nil nat); simpl; trivial.
(* 1/1 rewrite step NOT at the top *)
apply IH2; trivial.
apply Acc_intro; intros s [H'' [acc_sub_s  acc_l1]].
apply Acc_inv with (Term f l); trivial.
split; [idtac | split]; trivial.
apply one_step_subterm_rdp_rdp with l1; trivial.
unfold acc_sub; simpl; rewrite acc_one_step_list; assumption.
intros s  [H'' [acc_sub_s  acc_l1]] _.
apply IH1; trivial.
split; [idtac | split]; trivial.
apply one_step_subterm_rdp_rdp with l1; trivial.
unfold acc_sub; simpl; rewrite acc_one_step_list; assumption.

intros; apply (Main l).
apply Acc_intro; assumption.
intros; apply IHl; trivial.
intros; apply Acc_inv with (Term f y); assumption.
apply Acc_intro; assumption.
apply IH.
Qed.

Lemma dp_criterion_min : 
  forall R, (forall x t, ~ (R t (Var x))) -> 
  (forall s t, R s t -> forall x, In x (var_list s) -> In x (var_list t)) ->
  (forall f, {constructor R f} + {defined R f}) ->
   well_founded (dp_step_min R)  -> well_founded (one_step R).
Proof.
intros R HR RR CD Wf t; pattern t; apply term_rec3; clear t.
intro x; apply Acc_var; trivial.
intros; apply dp_criterion_min_local; trivial.
Qed.

(* Dependency pairs a la Dershowiz *)
Definition ddp R v u := dp R v u /\ (forall i p, subterm_at_pos u (i :: p) <> Some v).

Lemma ddp_is_dp : forall R t1 t2, ddp R t1 t2 -> dp R t1 t2.
Proof.
intros R t2 t1 [H _]; assumption.
Qed.

Definition ddp_step R := rdp_step (axiom (ddp R)) R.
Definition ddp_step_min R := rest (acc_sub R) (ddp_step R).

Lemma rddp_step_incl : forall R R' R1 R2, @inclusion _ R R' -> @inclusion _ R1 R2 ->  
               @inclusion _ (rdp_step (axiom (ddp R)) R1) (rdp_step (axiom (ddp R')) R2).
Proof.
intros R R' R1' R2' R_in_R' R1_in_R2 t1 t2 H.
inversion H as [g k l' s'' l_R_l' Hm]; clear H; subst.
apply Rdp_step with l'.
apply refl_trans_incl with (one_step_list (one_step R1')); trivial.
do 2 intro; apply one_step_list_incl.
apply one_step_incl; assumption.
inversion Hm as [u1 u2 sigma [H1 Sub] H2 H3]; clear Hm; subst.
apply instance.
split; [idtac | assumption].
inversion H1; clear H1; subst.
apply Dp with t2 p; trivial.
apply R_in_R'; assumption.
inversion H2; clear H2; subst.
apply Def with l t; apply R_in_R'; assumption.
Qed.

Lemma ddp_step_incl : forall R1 R2, @inclusion _ R1 R2 ->  
               @inclusion _ (ddp_step R1) (ddp_step R2).
Proof.
intros R1' R2' R1_in_R2 t1 t2 H.
apply (rddp_step_incl R1' R2' R1' R2'); trivial.
Qed.

Lemma ddp_criterion_local : 
  forall R, (forall x t, ~ (R t (Var x))) -> 
  (forall s t, R s t -> forall x, In x (var_list s) -> In x (var_list t)) ->
  (forall f, {constructor R f} + {defined R f}) ->
  forall t,   Acc (ddp_step_min R)  t -> (forall s, direct_subterm s t -> Acc (one_step R) s) ->
              Acc (one_step R) t.
Proof.
intros R HR RR CD.
intros t Acc_t IH.
apply dp_criterion_min_local; trivial.
clear IH; induction Acc_t as [t Acc_t IH].
apply Acc_intro.
intros s [H [Hs Ht]].
inversion H as [f l1 l2 t' K1 K2]; clear H; subst.
inversion K2 as [s1 t2 sigma K3]; clear K2; subst.
inversion K3 as [l r p g k1 K4 Sub Dg]; clear K3; subst.
destruct (subterm_at_pos_dec t2 (Term g k1)) as [[q Sub'] | not_Sub].
(* 1/2 (Term g k1) is a subterm of t2 *)
destruct q as [ | i q].
(* 1/3 (Term g k1) is equal to t2, impossible *)
absurd (Acc (ddp_step_min R) (Term f l2)).
(* 1/4 ~ Acc (ddp_step_min R) (Term f l2) *)
apply cycle_not_acc; split; [idtac | split; trivial].
apply Rdp_step with l2; trivial.
left.
rewrite <- H0; apply instance.
simpl in Sub'; injection Sub'; clear Sub'; intro Sub'; subst t2.
split.
apply Dp with r p; trivial.
intros i q Sub''; generalize (size_subterm_at_pos (Term g k1) i q); rewrite Sub''; apply Nat.lt_irrefl.
refine (rwr_sub_acc_sub_acc_sub R l1 l2 K1 Ht).
refine (rwr_sub_acc_sub_acc_sub R l1 l2 K1 Ht).
(* 1/3 Acc (ddp_step_min R) (Term f l2) *)
apply Acc_intro; intros u [H [Hu Hfl2]]; apply Acc_inv with (Term f l1).
apply Acc_intro; assumption.
split; [idtac | split; assumption].
apply rwr_subterm_rdp_rdp with l2; trivial.
(* 1/2 (Term g k1) is a strict subterm of t2, the dp step is not a ddp step, use the accessibilty for subterms *)
apply Acc_incl with (dp_step R).
intros s1 s2 [H _]; assumption.
apply acc_one_step_acc_dp; [apply HR | idtac].
generalize (subterm_at_pos_apply_subst_apply_subst_subterm_at_pos t2 (i :: q) sigma).
rewrite Sub'; rewrite H0; simpl subterm_at_pos.
generalize (nth_error_ok_in i l2); destruct (nth_error l2 i) as [ti | ].
(* 1/3 l2 has a subterm ti at position i *)
intros H Sub''; destruct (H _ (eq_refl _)) as [l2' [l2'' [L2 H']]]; clear H.
apply acc_subterms_3 with q ti; trivial.
apply (rwr_sub_acc_sub_acc_sub R _ _ K1 Ht); subst l2; apply in_or_app; right; left; apply eq_refl.
(* 1/2 has No subterm at position i *)
intros _ H; discriminate.
(* 1/1 (Term g k1) is NOT a subterm of t2 *)
apply IH;  split; [idtac | split; trivial].
apply Rdp_step with l2; trivial.
rewrite <- H0; apply instance.
split; [apply Dp with r p | idtac]; trivial.
Qed.

Lemma ddp_simple_criterion_local : 
  forall R, (forall x t, ~ (R t (Var x))) -> 
  (forall s t, R s t -> forall x, In x (var_list s) -> In x (var_list t)) ->
  (forall f, {constructor R f} + {defined R f}) ->
  forall t,   Acc (ddp_step R)  t -> (forall s, direct_subterm s t -> Acc (one_step R) s) ->
              Acc (one_step R) t.
Proof.
intros R HR RR CD.
intros t Acc_t IH.
apply ddp_criterion_local; trivial.
apply Acc_incl with (ddp_step R); trivial.
clear; intros s t [H _]; assumption.
Qed.

Lemma ddp_criterion : 
  forall R, (forall x t, ~ (R t (Var x))) -> 
  (forall s t, R s t -> forall x, In x (var_list s) -> In x (var_list t)) ->
  (forall f, {constructor R f} + {defined R f}) ->
   well_founded (ddp_step_min R)  -> well_founded (one_step R).
Proof.
intros R HR RR CD Wf t; pattern t; apply term_rec3; clear t.
intro x; apply Acc_var; trivial.
intros; apply ddp_criterion_local; trivial.
Qed.

Lemma acc_one_step_acc_ddp :
 forall R, (forall x t, ~ (R t (Var x))) -> 
    forall t, Acc (one_step R)  t -> Acc (ddp_step R) t.
Proof.
intros R HR t Acc_t.
apply Acc_incl with (dp_step R).
clear t Acc_t; intros t1 t2 H; inversion H; clear H; subst.
apply Rdp_step with l2; trivial.
inversion H1; clear H1; subst; apply instance.
apply ddp_is_dp; assumption.
apply acc_one_step_acc_dp; assumption.
Qed.

Lemma ddp_necessary : 
 forall R, (forall x t, ~ (R t (Var x))) -> 
    well_founded (one_step R)  -> well_founded (ddp_step R).
Proof.
intros R HR Wf.
intro t; apply acc_one_step_acc_ddp; trivial.
Qed.

(** Dependency chains on well-formed terms, for well-formed systems *)

Definition ddp_step_min_wf R := rest (fun t => acc_sub R t /\ well_formed t) (ddp_step R).

Lemma well_formed_rdp_step_inv :
  forall (R1 R2 : relation term), 
  (forall u v, R1 u v -> well_formed u /\ well_formed v) ->
  (forall s t, R1 s t -> forall x, In x (var_list s) -> In x (var_list t)) ->
  (forall u v, R2 u v -> well_formed u /\ well_formed v) ->
  (forall s t, R2 s t -> forall x, In x (var_list s) -> In x (var_list t)) ->
  forall s t, well_formed t -> rdp_step (axiom R1) R2 s t -> well_formed s.
Proof.
intros R1 R2 W1 R_reg1 W2 R_reg2 s t Wt H.
inversion H as [f l1 l2 t3 H' H'']; clear H; subst.
inversion H'' as [s' u sigma H Hs Hfl2]; clear H''; subst.
apply well_formed_apply_subst_strong.
intros x x_in_s'.
apply well_formed_remove_term with u.
rewrite Hfl2.
inversion H' as [l | k1 k2 H'']; subst.
trivial.
apply well_formed_rwr with R2 (Term f l1); trivial.
apply general_context; assumption.
rewrite var_in_term_is_sound.
apply R_reg1 with s'.
assumption.
rewrite <- var_in_term_is_sound; assumption.
destruct (W1 _ _ H) as [Ws' _]; assumption.
Qed.

Lemma well_formed_dp :
  forall (R1 : relation term), 
  (forall u v, R1 u v -> well_formed u /\ well_formed v) ->
  forall s t, dp R1 s t -> well_formed s /\  well_formed t.
Proof.
intros R1 W1 v u H.
inversion H as [u' r p g k r_R_u Sub Dg H2 H3]; clear H; subst; split.
destruct (W1 _ _ r_R_u) as [Wr _].
apply well_formed_subterm with r p; assumption.
destruct (W1 _ _ r_R_u) as [_ Wu]; assumption.
Qed.

Lemma reg_dp :
  forall (R1 : relation term), 
  (forall s t, R1 s t -> forall x, In x (var_list s) -> In x (var_list t)) ->
  forall s t, dp R1 s t -> forall x, In x (var_list s) -> In x (var_list t).
Proof.
intros R1 R1_reg v u H.
inversion H as [u' r p g k r_R_u Sub Dg H2 H3]; clear H; subst.
intros x x_in_k; apply R1_reg with r; trivial.
refine (var_in_subterm _ _ _ Sub x_in_k).
Qed.

Lemma ddp_criterion_strong_wf_local : 
  forall R, (forall x t, ~ (R t (Var x))) -> 
  (forall s t, R s t -> forall x, In x (var_list s) -> In x (var_list t)) ->
  (forall r l : term, R r l -> well_formed r /\ well_formed l) -> 
  (forall f, {constructor R f} + {defined R f}) ->
  forall t, Acc (ddp_step_min_wf R) t -> (forall s, direct_subterm s t -> Acc (one_step R) s) ->
              well_formed t -> Acc (one_step R) t.
Proof.
intros R HR RR WR CD.
(* main proof *)
intros t Acc_t Hl Wt; apply ddp_criterion_local; trivial.
revert Hl Wt; induction Acc_t as [t Acc_t IH].
intros Hl Wt; apply Acc_intro.
intros s [H [Hs Ht]]; assert (Ws : well_formed s).
apply well_formed_rdp_step_inv with (ddp R) R t; trivial.
clear Hs Ht; inversion H; clear H; subst.
intros u v H; apply well_formed_dp with R; [apply WR | apply ddp_is_dp; trivial].
intros u v H'; apply reg_dp with R; [apply RR | apply ddp_is_dp; trivial].
apply IH; trivial.
split; [idtac | split; split]; trivial.
Qed.

Lemma dp_criterion_strong_wf :
 forall R, (forall x t, ~ (R t (Var x))) -> 
 (forall s t, R s t -> forall x, In x (var_list s) -> In x (var_list t)) ->
 (forall s t, R s t -> well_formed s /\ well_formed t) ->
 (forall f, {constructor R f} + {defined R f}) ->
 forall (inject : nat -> variable) (inject_inv : variable -> nat),
 (forall n : nat, inject_inv (inject n) = n) ->
  well_founded (ddp_step_min_wf R) -> well_founded (one_step R).
Proof.
intros R HR RR WR CD inject inject_inv Hinj W.
intro t; apply acc_well_formed_acc_all with inject inject_inv; trivial; clear t.
intro t; pattern t; apply term_rec3; clear t.
intros x _; apply Acc_var; trivial.
intros; apply ddp_criterion_strong_wf_local; trivial.
simpl; intros t t_in_l; apply H; trivial.
apply (proj1 (well_formed_unfold H0)); assumption.
Qed.

(** Lifting when the underlying relation is defined as a set of pairs of terms *)

Fixpoint defined_subterms (is_def : symbol -> bool) (lhs : term) (acc: list term) (t:term) {struct t} := 
  match t with 
    | Var _ => acc 
    | Term f l => 
      let acc' := 
        if is_def f
          then 
               if eq_bool lhs t
               then t :: acc
               else 
                  if is_subterm t lhs 
                  then acc
                  else t :: acc 
           else acc 
            in
            fold_left (defined_subterms is_def lhs) l acc' 
  end.

Lemma defined_subterms_accumulates : 
  forall is_def lhs x acc  y, In y acc -> In y (defined_subterms is_def lhs acc x).
Proof.
intros is_def lhs x; induction x using term_rec3;
intros acc y y_in_acc; simpl; trivial.
apply fold_left_in_acc.
intros acc0 x y0 H1 H2; apply H;auto with *.
case (is_def f); [ | assumption].
case (eq_bool lhs (Term f l)).
right; assumption.
destruct (is_subterm (Term f l) lhs).
assumption.
right; assumption.
Qed.

Lemma defined_subterms_is_complete: 
  forall is_def lhs, 
    forall r p f l acc, 
      subterm_at_pos r p = Some (Term f l) -> 
      is_def f = true -> 
      (~exists i, exists p, subterm_at_pos lhs (i :: p) = Some (Term f l)) ->
      In (Term f l) (defined_subterms is_def lhs acc r).
Proof.
  intros is_def lhs r.
  induction r using term_rec3. 
  (* r = var *)
  intros p f l acc H f_in_def Sub; destruct p; simpl in H; discriminate.
  (* r = Term _ _ *) 
  intros [ | i p] g k acc H' g_in_def Sub. 
  simpl in H'; injection H'; clear H'; intros; subst g k; simpl.
  apply fold_left_in_acc.
  intros; apply defined_subterms_accumulates; auto.
  rewrite g_in_def.
  generalize (eq_bool_ok lhs (Term f l)); case (eq_bool lhs (Term f l)); [intro lhs_eq_fl | intro lhs_diff_fl].
  left; apply eq_refl.
  generalize (is_subterm_ok_true (Term f l) lhs).
  case (is_subterm (Term f l) lhs); [intro Sub' | intros _].
  apply False_ind.
  apply Sub.
  destruct (Sub' (eq_refl _)) as [[ | i p] Sub''].
  simpl in Sub''; absurd (lhs = Term f l); trivial; injection Sub''; intros; trivial.
  exists i; exists p; trivial.
  left; trivial.
  
  generalize (more_list.nth_error_ok_in i l).
  simpl in H'; destruct (nth_error l i) as [ti | ].
  intro h; destruct (h _ (eq_refl _)) as [l1 [l2 [h1 h2]]]; clear h; subst.
  simpl; rewrite fold_left_app; simpl.
  apply fold_left_in_acc.
  intros;  apply defined_subterms_accumulates; auto.
  apply H with p;  auto with *.
  discriminate.
Qed.

Lemma defined_subterms_unfold_gen : 
   forall is_def s lhs acc1 acc2 acc1' acc2', 
   (forall t, In t acc1 <-> In t acc1') ->
   (forall t, In t acc2 <-> In t acc2') ->
   forall t, In t (defined_subterms is_def lhs (acc1 ++ acc2) s) <->  
   (In t (defined_subterms is_def lhs acc1' s) \/ In t acc2').
Proof.
intros is_def s; pattern s; apply term_rec3; clear s.
intros v lhs acc1 acc2 acc1' acc2' I1 I2 t; simpl; split.
rewrite <- I1; rewrite <- I2; apply in_app_or.
rewrite <- I1; rewrite <- I2; apply in_or_app.
intros f l IH lhs acc1 acc2 acc1' acc2' I1 I2 t; simpl.
set (fl := Term f l) in *.
set (flacc1 :=  (if is_def f
      then
       if eq_bool lhs fl
       then fl :: acc1
       else if is_subterm fl lhs then acc1 else fl :: acc1
      else acc1)) in *.
replace (if is_def f
      then
       if eq_bool lhs fl
       then fl :: acc1 ++ acc2
       else if is_subterm fl lhs then acc1 ++ acc2 else fl :: acc1 ++ acc2
      else acc1 ++ acc2) with (flacc1 ++ acc2).
set (flacc1' :=  (if is_def f
      then
       if eq_bool lhs fl
       then fl :: acc1'
       else if is_subterm fl lhs then acc1' else fl :: acc1'
      else acc1')) in *.
assert (flI1 : forall t : term, In t flacc1 <-> In t flacc1').
intros s; unfold flacc1, flacc1'; case (is_def f).
case (eq_bool lhs fl).
simpl; rewrite I1; split; exact (fun H => H).
case (is_subterm fl lhs).
rewrite I1; split; exact (fun H => H).
simpl; rewrite I1; split; exact (fun H => H).
rewrite I1; split; exact (fun H => H).
clearbody flacc1; clearbody flacc1'; clear acc1 acc1' I1.
revert flacc1 acc2 flacc1' acc2' flI1 I2; induction l as [ | s l]; simpl; intros acc1 acc2 acc1' acc2' I1 I2.
split.
rewrite <- I1; rewrite <- I2; apply in_app_or.
rewrite <- I1; rewrite <- I2; apply in_or_app.
replace (defined_subterms is_def lhs (acc1 ++ acc2) s) with 
            (nil ++ defined_subterms is_def lhs (acc1 ++ acc2) s); [ | apply eq_refl].
rewrite (IHl (tail_prop _ IH) 
                  nil
                  (defined_subterms is_def lhs (acc1 ++ acc2) s)
                  nil
                  ((defined_subterms is_def lhs acc1' s) ++ acc2')).
replace (defined_subterms is_def lhs acc1' s) with 
            (nil ++ defined_subterms is_def lhs acc1' s); [ | apply eq_refl].
rewrite (IHl (tail_prop _ IH) 
                  nil
                  (defined_subterms is_def lhs acc1' s)
                  nil
                  (defined_subterms is_def lhs acc1' s)).
split.
intros [H1 | H2].
do 2 left; assumption.
simpl in H2; destruct (in_app_or _ _ _ H2) as [H3 | H3].
left; right; assumption.
right; assumption.
intros [[H1 | H2] | H3].
left; assumption.
right; simpl; apply in_or_app; left; assumption.
right; simpl; apply in_or_app; right; assumption.
intro; split; exact (fun H => H).
intro; split; exact (fun H => H).

intro; split; exact (fun H => H).
intro u; rewrite (IH _ (or_introl _ (eq_refl _)) lhs acc1 acc2 acc1' acc2').
split.
apply in_or_app.
apply in_app_or.
assumption.
assumption.
unfold flacc1; case (is_def f); [ | apply eq_refl].
case (eq_bool lhs fl).
apply eq_refl.
case (is_subterm fl lhs); apply eq_refl.
Qed.

Lemma defined_subterms_unfold : 
   forall is_def s lhs acc, 
   forall t, In t (defined_subterms is_def lhs acc s) <->  
   (In t (defined_subterms is_def lhs nil s) \/ In t acc).
Proof.
intros is_def s lhs acc t.
rewrite <- (defined_subterms_unfold_gen is_def s lhs nil acc nil acc).
simpl; split; exact (fun H => H).
intro; split; exact (fun H => H).
intro; split; exact (fun H => H).
Qed.


Lemma fold_left_defined_subterms_unfold : 
   forall is_def lhs l acc t, 
  In t (fold_left (defined_subterms is_def lhs) l acc) <->
  In t (fold_left (defined_subterms is_def lhs) l nil) \/ In t acc.
Proof.
intros is_def lhs l; induction l as [ | s l].
intros acc t; simpl; split; [intro H; right; exact H | intros [Abs | H]; [contradiction | exact H]].
simpl; intros acc t.
rewrite (IHl (defined_subterms is_def lhs acc s)).
rewrite (IHl (defined_subterms is_def lhs nil s)).
rewrite  defined_subterms_unfold.
intuition.
Qed.

Lemma defined_subterms_is_sound: 
  forall is_def lhs, 
    forall r g k, 
      In (Term g k) (defined_subterms is_def lhs nil r) ->
      ((is_def g = true) /\
      (exists p, subterm_at_pos r p = Some (Term g k)) /\
      (forall i q, subterm_at_pos lhs (i :: q) <> Some (Term g k))).
Proof.
  intros is_def lhs r.
  induction r using term_rec3;   intros g k gk_in_d.
  (* r = Var _ *)
  contradiction.
  (* r = Term _ _ *) 
   simpl in gk_in_d.
   rewrite fold_left_defined_subterms_unfold in gk_in_d.
   destruct gk_in_d as [gk_in_d | gk_in_d].
   assert (K : is_def g = true /\
                    (exists i, exists p : list nat, subterm_at_pos (Term f l) (i :: p) = Some (Term g k)) /\
                    (forall (i : nat) (q : list nat),
                    subterm_at_pos lhs (i :: q) <> Some (Term g k))).
   simpl subterm_at_pos at 1.
   induction l as [ | t l].
   contradiction.
   simpl in gk_in_d.
   rewrite fold_left_defined_subterms_unfold in gk_in_d.
   destruct gk_in_d as [gk_in_d | gk_in_d].
   destruct (IHl (tail_prop _ H) gk_in_d) as [Dg [[i  [p K1]] K2]]. 
   split.
   assumption.
   split.
   exists (S i); exists p; simpl; assumption.
   assumption.
   destruct (H _ (or_introl _ (eq_refl _)) _ _ gk_in_d) as  [Dg [[p K1] K2]].
   split.
   assumption.
   split.
   exists 0; exists p; simpl; assumption.
   assumption.
   destruct K as [Dg [[i  [p K1]] K2]]. 
   split.
   assumption.
   split.
   exists (i :: p); assumption.
   assumption.
   revert gk_in_d.
   case_eq (is_def f).
   case_eq (eq_bool lhs (Term f l)).
   intros lhs_eq_fl Df [gk_eq_fl | gk_in_nil]; [ | contradiction].
   injection gk_eq_fl; clear gk_eq_fl; intros; subst; split.
   assumption.
   split.
   exists nil; apply eq_refl.
   generalize (eq_bool_ok lhs (Term g k)); rewrite lhs_eq_fl; clear lhs_eq_fl; intro lhs_eq_gk; rewrite <- lhs_eq_gk.
   intros i q Sub.
   generalize (size_subterm_at_pos lhs i q); rewrite Sub.
   apply Nat.lt_irrefl.
   case_eq (is_subterm (Term f l) lhs).
   contradiction.
   intros nSub lhs_diff_fl Df [gk_eq_fl | gk_in_nil]; [ | contradiction].
   injection gk_eq_fl; clear gk_eq_fl; intros; subst; split.
   assumption.
   split.
   exists nil; apply eq_refl.
   intros i q; apply is_subterm_ok_false; assumption.
   contradiction.
Qed.

Fixpoint defined_list (l : list (term * term))  acc :=
  match l with
  | nil => acc
  | (Var _, _) :: tl => defined_list tl acc 
  | (Term f _, _) :: tl => defined_list tl (f :: acc)
  end.

Lemma defined_list_complete : 
  forall R rule_list, (forall l r, R r l <-> In (l,r) rule_list) -> 
    forall f, defined R f  -> In f (defined_list rule_list nil).
Proof.
assert (forall R rule_list, (forall l r, R r l <-> In (l,r) rule_list) -> 
    forall f acc, (defined R f \/ In f acc) -> In f (defined_list rule_list acc)).
intros R Rlist; revert R; induction Rlist as [ | [l1 r1] Rlist];
intros R Rlist_ok _f acc [[f l t H] | f_in_acc].
rewrite Rlist_ok in H; contradiction.
assumption.
rewrite Rlist_ok in H; simpl in H; destruct H as [H | H].
injection H; clear H; intros; subst.
simpl.
apply (IHRlist (fun r l => In (l,r) Rlist)).
do 2 intro; split; intro; assumption.
right; left; apply eq_refl.
destruct l1; simpl; apply (IHRlist (fun r l => In (l,r) Rlist)).
do 2 intro; split; intro; assumption.
left; constructor 1 with l t; assumption.
do 2 intro; split; intro; assumption.
left; constructor 1 with l t; assumption.
destruct l1; simpl; apply (IHRlist (fun r l => In (l,r) Rlist)).
do 2 intro; split; intro; assumption.
right; assumption.
do 2 intro; split; intro; assumption.
do 2 right; assumption.

intros R Rlist Rlist_ok f Df; apply (H _ _ Rlist_ok); left; assumption.
Defined.

Lemma defined_list_sound : 
  forall R rule_list, (forall l r, R r l <-> In (l,r) rule_list) -> 
    forall f, In f (defined_list rule_list nil) -> defined R f .
Proof.
assert (forall R rule_list, (forall l r, R r l <-> In (l,r) rule_list) -> 
    forall f acc, In f (defined_list rule_list acc) -> (defined R f \/ In f acc)).
intros R Rlist; revert R; induction Rlist as [ | [l1 r1] Rlist];
intros R Rlist_ok f acc Df.
right; assumption.
assert (Rlist_ok' : forall l r : term, In (l, r) Rlist <-> In (l, r) Rlist).
do 2 intro; split; intro; assumption.
simpl in Df; destruct l1 as [ | f1 l1].
destruct (IHRlist _ Rlist_ok' f acc Df) as [Df' | f_in_acc].
left; inversion Df' as [f' l t H]; subst; constructor 1 with l t; rewrite Rlist_ok; right; assumption.
right; assumption.
destruct (IHRlist _ Rlist_ok' f (f1 :: acc) Df) as [Df' | f_in_f1acc].
left; inversion Df' as [f' l t H]; subst; constructor 1 with l t; rewrite Rlist_ok; right; assumption.
simpl in f_in_f1acc; destruct f_in_f1acc as [f_eq_f1 | f_in_acc].
left; constructor 1 with l1 r1; rewrite Rlist_ok; left; subst f1; apply eq_refl.
right; assumption.

intros R Rlist Rlist_ok f Df; destruct (H _ _ Rlist_ok f nil Df) as [Df' | f_in_nil]; [assumption | contradiction].
Defined.

Lemma defined_dec : 
   forall R rule_list, (forall l r, R r l <-> In (l,r) rule_list) ->
   forall f, {defined R f} + { ~ defined R f}.
Proof.
intros R Rlist Rlist_ok f.
case_eq (list_exists (fun lr => match fst lr with Var _ => false | Term g _ => eq_symb_bool f g end) Rlist).
intro Df; left; rewrite list_exists_is_sound in Df.
destruct Df as [[l r] [H1 H2]]; destruct l as [ | g].
discriminate.
generalize (F.Symb.eq_bool_ok f g); simpl in H2; rewrite H2; intro; subst g.
constructor 1 with l r; rewrite Rlist_ok; assumption.
intro nDf; right; intro Df.
inversion Df as [f' l t H]; subst f'; rewrite Rlist_ok in H.
assert (nDf' := list_exists_is_complete_false _ _ nDf _ H); 
simpl in nDf'; rewrite eq_symb_bool_refl in nDf'; discriminate.
Defined.

Lemma constructor_defined_dec :  forall R rule_list, (forall l r, R r l <-> In (l,r) rule_list) ->
   forall f, {constructor R f} + {defined R f}.
Proof.
  intros R rule_list H f.
  destruct (defined_dec R rule_list H f).
  right;assumption.
  left.
  constructor.
  intros;intro abs;apply n.
  apply (Def R f l t abs).
Defined.

Definition ddp_rule is_def  (lhs rhs:term) := 
  map (fun r => (lhs,r)) (defined_subterms is_def lhs (@nil term) rhs).

Definition ddp_list is_def rule_list := 
  fold_left (fun acc (rule : term*term) => (let (lhs,rhs) := rule in (ddp_rule is_def lhs rhs))++acc)
  rule_list (@nil (term*term)).

Lemma ddp_list_is_complete : 
   forall R rule_list, (forall l r, R r l <-> In (l,r) rule_list) ->
   forall is_def,   (forall f, is_def f = true <-> defined R f) ->
   forall x y, ddp R x y -> 
   In (y,x) (ddp_list is_def rule_list).
Proof.
intros R Rlist Rlist_ok is_def is_def_ok x y [H Sub].
inversion H as [ll r p f l K Sub' Df]; clear H; subst.
rewrite Rlist_ok in K.
clear Rlist_ok; induction Rlist as [ | [l1 r1] Rlist].
contradiction.
simpl in K; destruct K as [K | K].
injection K; clear K; intros; subst; unfold ddp_list; simpl.
apply fold_left_in_acc.
intros acc [a b] z z_in_acc _; apply in_or_app; right; assumption.
apply in_or_app; left; unfold ddp_rule; rewrite in_map_iff.
exists (Term f l); split.
apply eq_refl.
apply defined_subterms_is_complete with p; trivial.
rewrite is_def_ok; assumption.
intros [i [q Sub'']]; apply (Sub i q Sub'').
unfold ddp_list; simpl.
replace (ddp_rule is_def l1 r1 ++ nil) with (nil ++ (ddp_rule is_def l1 r1 ++ nil)); [ | apply eq_refl].
rewrite fold_left_in_acc_split.
left; apply IHRlist; assumption.
Qed.

Lemma ddp_list_is_sound : 
   forall R rule_list, (forall l r, R r l <-> In (l,r) rule_list) ->
   forall is_def,   (forall f, is_def f = true <-> defined R f) ->
   forall x y, In (y,x) (ddp_list is_def rule_list) -> ddp R x y.
Proof.
assert (H' : forall Rlist is_def x y, In (y, x) (ddp_list is_def Rlist) ->
                     (exists t2, exists f2, exists l2, exists p, 
                     x = Term f2 l2 /\ In (y,t2) Rlist /\  subterm_at_pos t2 p = Some (Term f2 l2)  /\ is_def f2 = true ) /\
                     (forall i p, subterm_at_pos y (i :: p) <> Some x)).
intros Rlist is_def x y H.
induction Rlist as  [ | [l1 r1] Rlist].
contradiction.
unfold ddp_list in H; simpl in H.
rewrite app_nil_r in H.
replace (ddp_rule is_def l1 r1) with (nil ++ ddp_rule is_def l1 r1) in H; [ | apply eq_refl].
rewrite fold_left_in_acc_split in H; destruct H as [H | H].
destruct (IHRlist H) as [[t2 [f2 [ l2 [p [H1 [H2 H3]]]]]] H4].
split; [ | assumption].
exists t2; exists f2; exists l2; exists p; split.
assumption.
split; [right | ]; assumption.
clear IHRlist.
unfold ddp_rule in H.
rewrite in_map_iff in H.
destruct H as [x' [H1 H2]].
injection H1; clear H1; intros; subst.
destruct x as [x | g k].
apply False_rect.
induction r1 using term_rec3.
contradiction.
simpl in H2; rewrite fold_left_defined_subterms_unfold in H2.
destruct H2 as [H2 | H2].
induction l as [ | t l].
contradiction.
simpl in H2; rewrite fold_left_defined_subterms_unfold in H2.
destruct H2 as [H2 | H2].
apply IHl; [ | assumption].
intros u u_in_l; apply (H u); right; assumption.
apply (H _ (or_introl _ (eq_refl _))); assumption.
revert H2; case (is_def f).
case (eq_bool y (Term f l)).
intros [H1 | H2]; [discriminate | contradiction].
case (is_subterm (Term f l) y).
contradiction.
intros [H1 | H2]; [discriminate | contradiction].
contradiction.
destruct (defined_subterms_is_sound _ _ _ _ _ H2) as [Dg [[p Sub] K2]].
split; [ | assumption].
exists r1; exists g; exists k; exists p.
split.
apply eq_refl.
split.
left; apply eq_refl.
split; assumption.
intros R Rlist Rlist_ok is_def is_def_ok x y H.
destruct (H' _ _ _ _ H) as [[t2 [f2 [l2 [p [H1 [H2 [H3 H4]]]]]]] H5].
split; [ | assumption].
subst x; constructor 1 with t2 p.
rewrite Rlist_ok; assumption.
assumption.
rewrite <- is_def_ok; assumption.
Qed.

Lemma dp_criterion_lift :
  forall R rule_list, (forall l r, R r l <-> In (l,r) rule_list) ->
  (forall l r, In (l,r) rule_list -> forall v, l <> Var v) ->
  (forall l r, In (l,r) rule_list -> forall v, In v (var_list r) -> In v (var_list l)) ->
   well_founded (ddp_step_min R)  -> well_founded (one_step R).
Proof.
intros R rule_list Equiv R_var R_reg Wf;
apply ddp_criterion; trivial.
intros x t H; rewrite Equiv in H.
apply (R_var (Var x) t H x); trivial.
intros s t H; rewrite Equiv in H.
apply (R_reg t s H).
apply constructor_defined_dec with rule_list; trivial.
Qed.

(* criterion with marked symbols *)
Section Marked_DP.

Variable R : relation term.
Variable R_var : forall x t, ~R t (Var x).
Variable mark : symbol -> symbol.

Definition mark_term (t : term) : term :=
  match t with
  | Var x => Var x
  | Term f l => Term (mark f) l
  end.

Inductive mrel (P : relation term) : relation term :=
  | Mrel : forall t1 t2, P t1 t2 -> mrel P (mark_term t1) (mark_term t2).

Lemma x_to_x2_commutes_mark : 
  forall sigma f l, apply_subst sigma (mark_term (Term f l)) =  (mark_term (apply_subst sigma (Term f l))).
Proof.
intros sigma f l; simpl; trivial.
Qed.

Lemma rdp_step_rmdp_step :
  forall (dpR : relation term), 
  (forall u v, dpR v u -> dp R v u) ->
  forall s t, rdp_step (axiom dpR) R s t ->
              rdp_step (axiom (mrel dpR)) R (mark_term s) (mark_term t).
Proof.
intros dpR dpR_in_dpR s t H.

inversion H as [f l1 l2 _s H1 H2 H3 H4]; clear H; subst.
simpl; apply Rdp_step with l2; trivial.
inversion H2 as [v u sigma K1 K2 K3]; clear H2; subst; trivial.
assert (K1' := dpR_in_dpR _ _ K1); 
inversion K1' as [t1 t2 p f2 k2 H Sub Df2]; clear K1'; subst.
destruct u as [xu | fu lu].
apply False_rect; apply (R_var _ _ H).
injection K3; clear K3; intros; subst.
apply (instance (mrel dpR) (Term (mark f2) k2) (Term (mark f) lu) sigma).
apply (Mrel dpR (Term f2 k2) (Term f lu)).
assumption.
Qed.

Lemma mdp_criterion_local : 
  forall (dpR : relation term), 
  (forall u v, dpR v u -> dp R v u) ->
   forall s, Acc (rdp_step (axiom (mrel dpR)) R)  (mark_term s) -> 
             Acc (rdp_step (axiom dpR) R) s.
Proof.
intros dpR dpR_in_dpR t Acc_t.
set (t' := mark_term t) in *; 
assert (Tt := eq_refl t'); unfold t' at 2 in Tt; clearbody t'.
revert t Tt; induction Acc_t as [t' Acc_t IH].
intros t H.
apply Acc_intro; intros s H'.
apply IH with (mark_term s); [ | apply eq_refl].
subst t'; apply rdp_step_rmdp_step; trivial.
Qed.


Lemma mdp_criterion : 
  forall (dpR : relation term), 
  (forall u v, dpR v u -> dp R v u) ->
   well_founded (rdp_step (axiom (mrel dpR)) R)  ->  
   well_founded (rdp_step (axiom dpR) R).
Proof.
intros dpR dpR_in_dpR W t;
apply mdp_criterion_local; trivial.
Qed.

Lemma mdp_criterion_local_strong : 
  forall (dpR : relation term), 
  (forall u v, dpR v u -> dp R v u) ->
   forall s, Acc (rest (acc_sub R) (rdp_step (axiom (mrel dpR)) R)) (mark_term s) -> 
             Acc (rest (acc_sub R) (rdp_step (axiom dpR) R)) s.
Proof.
intros dpR dpR_in_dpR t Acc_t.
set (t' := mark_term t) in *; 
assert (Tt := eq_refl t'); unfold t' at 2 in Tt; clearbody t'.
revert t Tt; induction Acc_t as [t' Acc_t IH].
intros t H.
apply Acc_intro; intros s H'.
apply IH with (mark_term s); [ | apply eq_refl].
subst t'; destruct H' as [H' Hmin]; split.
apply rdp_step_rmdp_step; trivial.
destruct s; destruct t; assumption.
Qed.


Lemma mdp_criterion_strong : 
  forall (dpR : relation term), 
  (forall u v, dpR v u -> dp R v u) ->
   well_founded (rest (acc_sub R) (rdp_step (axiom (mrel dpR)) R))  ->  
   well_founded (rest (acc_sub R) (rdp_step (axiom dpR) R)).
Proof.
intros dpR dpR_in_dpR W t;
apply mdp_criterion_local_strong; trivial.
Qed.

Lemma TT :  (forall f, mark (mark f) = f) -> forall t, t = mark_term (mark_term t).
Proof.
intros mark_inv t; case t; [intros v; simpl | intros f l; simpl; rewrite mark_inv]; apply eq_refl.
Qed.

Lemma mrdp_step_rdp_step :
 (forall f, mark (mark f) = f) ->
  forall (dpR : relation term), 
  (forall u v, dpR v u -> dp R v u) ->
  forall s t, rdp_step (axiom (mrel dpR)) R (mark_term s) (mark_term t) ->
                 rdp_step (axiom dpR) R s t.
Proof.
intros mark_inv dpR dpR_in_dpR.
intros s t H.
inversion H as [_f l1 l2 _s H1 H2 H3 H4]; clear H; subst.
destruct t as [ | f l1']; [discriminate | injection H4; clear H4; intros; subst _f l1'].
simpl; apply Rdp_step with l2; trivial.
inversion H2 as [_v _u sigma _K1 K2 K3]; clear H2; subst; trivial.
inversion _K1 as [v u K1]; clear _K1; subst.
assert (K1' := dpR_in_dpR _ _ K1); 
inversion K1' as [t1 t2 p f2 k2 H Sub Df2]; clear K1'; subst.
destruct u as [xu | fu lu].
apply False_rect; apply (R_var _ _ H).
injection K3; clear K3; intros; subst.
assert (_K2 := f_equal mark_term K2); simpl in _K2; rewrite <- (TT mark_inv) in _K2; rewrite mark_inv in _K2.
rewrite <- _K2.
apply (instance dpR (Term f2 k2) (Term f lu) sigma).
assert (_H2 := f_equal mark H2); do 2 rewrite mark_inv in _H2.
subst f; assumption.
Qed.

Lemma mdp_reverted_criterion_local_strong : 
 (forall f, mark (mark f) = f) ->
  forall (dpR : relation term), 
  (forall u v, dpR v u -> dp R v u) ->
   forall s, Acc (rest (acc_sub R) (rdp_step (axiom dpR) R)) s ->
             Acc (rest (acc_sub R) (rdp_step (axiom (mrel dpR)) R)) (mark_term s).
Proof.
intros mark_inv dpR dpR_in_dpR t Acc_t.
induction Acc_t as [t' Acc_t IH].
apply Acc_intro; intros s H'.
rewrite (TT mark_inv); apply IH.
destruct H' as [H' Hmin]; split.
apply (mrdp_step_rdp_step mark_inv _ dpR_in_dpR); rewrite <- (TT mark_inv s); trivial.
destruct s; destruct t'; assumption.
Qed.

Lemma mdp_strong_necessary_local : 
 (forall f, mark (mark f) = f) ->
 forall (dpR : relation term), 
  (forall u v, dpR v u -> dp R v u) ->
   well_founded (rest (acc_sub R) (rdp_step (axiom dpR) R))  ->  
   well_founded (rest (acc_sub R) (rdp_step (axiom (mrel dpR)) R)).
Proof.
intros mark_inv dpR dpR_in_dpR W.
intro t; rewrite (TT mark_inv t).
apply mdp_reverted_criterion_local_strong; trivial.
Qed.

End Marked_DP.

Definition are_connected dpR R uv' uv := 
  exists sigma, exists sigma', 
  match uv, uv' with
  | (u,v), (u', v') => 
     dpR v u /\ dpR v' u' /\ 
     match (apply_subst sigma' u'), (apply_subst sigma v) with
     | Term g lu', Term f lv => 
                 f = g /\ refl_trans_clos (one_step_list (one_step R)) lu' lv
     | _, _ => False
     end
  end.

Section RU.
Variable is_def : symbol -> bool.

Fixpoint rough_unif (t1 t2 : term) {struct t1} : bool :=
  match t1, t2 with
  | (Var _), _  => true
  | _, (Var _)  => true
  | (Term f1 k1), (Term f2 k2) =>
        if orb (is_def f1) (is_def f2)
        then true
        else
          if F.Symb.eq_bool f1 f2
          then
           let rough_unif_list :=
           (fix rough_unif_list (l1 l2 : list term) {struct l1} : bool :=
            match l1, l2 with
            | nil, nil => true
            | nil, (_ :: _) => false
            | (_ :: _), nil => false
            | (t1 :: lt1), (t2 :: lt2) => 
               andb (rough_unif t1 t2) 
               (rough_unif_list lt1 lt2)
            end) in
            rough_unif_list k1 k2
          else false
  end.

Fixpoint rough_unif_list (l1 l2 : list term) {struct l1} : bool :=
            match l1, l2 with
            | nil, nil => true
            | nil, (_ :: _) => false
            | (_ :: _), nil => false
            | (t1 :: lt1), (t2 :: lt2) => 
               andb (rough_unif t1 t2) 
               (rough_unif_list lt1 lt2)
            end.

Lemma rough_unif_unfold : 
  forall t1 t2, rough_unif t1 t2 =
 match t1, t2 with
  | (Var _), _  => true
  | _, (Var _)  => true
  | (Term f1 k1), (Term f2 k2) =>
        if orb (is_def f1) (is_def f2)
        then true
        else
          if F.Symb.eq_bool f1 f2
          then rough_unif_list k1 k2
          else false
end.
Proof.
intros t1 t2; destruct t1 as [v1 | f1 k1].
apply eq_refl.
destruct t2 as [v2 | f2 k2].
apply eq_refl.
simpl; destruct (is_def f1).
apply eq_refl.
destruct (is_def f2).
apply eq_refl.
destruct (eq_symb_bool f1 f2); [simpl | apply eq_refl].
revert k2; induction k1 as [ | t1 k1]; intros [ | t2 k2]; trivial.
Qed.

Definition connect_approx u v : bool :=
  match u, v with
  | Var _, _ => false
  | _, Var _ => false
  | Term f l, Term g k =>
    if F.Symb.eq_bool f g
    then rough_unif_list l k
    else false
    end.

End RU.

Lemma rough_unif_is_ok :
  forall (R dpR : relation term) mark is_def,
  (forall x t, ~R t (Var x)) ->
  (forall f, defined R f -> is_def f = true) ->
  (forall u v, dpR v u -> dp R v u) ->
  forall u v u' v', are_connected (mrel mark dpR) R (u',v') (u,v) ->
  connect_approx is_def v u' = true.
Proof.
intros R dpR mark is_def R_var is_def_ok dpR_in_dpR _u _v _u' _v' H.
destruct H as [sigma [sigma' [_H1 [_H2 H3]]]].
inversion _H1 as [v u H1]; clear _H1; subst.
inversion _H2 as [v' u' H2]; clear _H2; subst.
assert (K1 := dpR_in_dpR _ _ H1); clear H1.
assert (K2 := dpR_in_dpR _ _ H2); clear H2.
inversion K1 as [t1 t2 p f2 l2 H Sub Df2].
inversion K2 as [t1' t2' p' f2' l2' H' Sub' Df2'].
subst; destruct u' as [x | g k].
apply False_rect; apply (R_var _ _ H').
simpl in H3; destruct H3 as [H3 H4].
simpl; rewrite <- H3.
simpl; rewrite eq_symb_bool_refl.
assert (K0 : forall k' l' sigma sigma', 
         refl_trans_clos (one_step_list (one_step R))
           (map (apply_subst sigma') k') (map (apply_subst sigma) l') ->
         rough_unif_list is_def l' k' = true).
clear -R_var is_def_ok.
intro k; pattern k; apply (list_rec3 size); clear k.
intro n; induction n as [ | n]; intros k Sk l sigma sigma' H;
destruct k as [ | s k].
destruct l as [ | t l].
apply eq_refl.
assert (L:= refl_trans_clos_one_step_list_length_eq H).
discriminate.
absurd (1 <= 0).
intro Abs; inversion Abs.
apply Nat.le_trans with (list_size size (s :: k)); trivial.
apply Nat.le_trans with (size s).
apply size_ge_one.
simpl; apply Nat.le_add_r.
destruct l as [ | t l].
apply eq_refl.
assert (L:= refl_trans_clos_one_step_list_length_eq H).
discriminate.
destruct l as [ | t l].
assert (L:= refl_trans_clos_one_step_list_length_eq H).
discriminate.
simpl in H; rewrite refl_trans_clos_one_step_list_head_tail in H.
destruct H as [H' H].
assert (Sk' : list_size size k <= n).
apply le_S_n.
apply Nat.le_trans with (list_size size (s :: k)); trivial.
simpl; refine (proj1 (Nat.add_le_mono_r 1 (size s) _) _).
apply size_ge_one.
assert (Ss : size s <= S n).
apply Nat.le_trans with (list_size size (s :: k)); trivial.
simpl; apply Nat.le_add_r.
simpl; rewrite IHn with k l sigma sigma'; trivial.
clear l k Sk Sk' H.
rewrite rough_unif_unfold.
destruct t as [x | f l].
apply eq_refl.
destruct s as [x | g k].
apply eq_refl.
simpl; simpl in H'.
inversion H'; clear H'; subst.
destruct (is_def f).
apply eq_refl.
rewrite eq_symb_bool_refl.
simpl.
rewrite size_unfold in Ss; generalize (le_S_n _ _ Ss); clear Ss; intro Ss.
rewrite IHn with k l sigma sigma'; trivial.
rewrite H2; left.
assert (Df : defined R f \/ 
            (f = g /\ refl_trans_clos (one_step_list (one_step R))
                           (map (apply_subst sigma') k) 
                           (map (apply_subst sigma) l))).
set (l' := map (apply_subst sigma) l) in *; clearbody l'.
set (k' := map (apply_subst sigma') k) in *; clearbody k'.
set (fl := Term f l') in *.
assert (Hf := eq_refl fl).
unfold fl at 2 in Hf; clearbody fl; revert Hf.
set (gk := Term g k') in *.
assert (Hg := eq_refl gk).
unfold gk at 2 in Hg; clearbody gk; revert Hg.
clear Ss; revert f g l' k'; induction H; intros f g l' k'.
inversion H; clear H; subst.
inversion H0; clear H0; subst.
destruct t2 as [v | f2 l2].
apply False_rect; apply (R_var _ _ H).
intros _ H1; simpl in H1; injection H1; clear H1; intros; subst.
left; constructor 1 with l2 t1; assumption.
intros H1 H2; injection H1; injection H2; intros; subst; subst; right; split.
apply eq_refl.
right; left; assumption.
intros H1 H2.
inversion H; clear H; subst.
inversion H3; clear H3; subst.
destruct t2 as [v | f2 l2].
apply False_rect; apply (R_var _ _ H1).
destruct (IHtrans_clos f f2 l' (map (apply_subst sigma0) l2) 
                   (eq_refl _) (eq_refl _)) as [Df | [f_eq_f2 K]].
left; assumption.
subst f2; left; constructor 1 with l2 t1; assumption.
destruct (IHtrans_clos f f0 l' l2 (eq_refl _) (eq_refl _)) as [Df | [f_eq_f0 K]].
left; assumption.
subst f0; injection H4; intros; right; split.
assumption.
subst; apply refl_trans_clos_is_trans with l2; trivial.
right; left; assumption.
destruct Df as [Df | [f_eq_g K]].
rewrite (is_def_ok f Df).
apply eq_refl.
subst g; destruct (is_def f).
apply eq_refl.
simpl; rewrite eq_symb_bool_refl.
rewrite size_unfold in Ss; generalize (le_S_n _ _ Ss); clear Ss; intro Ss.
rewrite IHn with k l sigma sigma'; trivial.
apply K0 with sigma sigma'; trivial.
Qed.

Lemma comp_comp :
  forall dpR R comp, (forall uv uv', are_connected dpR R uv uv' -> comp uv <= comp uv') ->
   forall uv uv', comp uv <> comp uv' -> 
	~ (refl_trans_clos (are_connected dpR R) uv uv' /\ refl_trans_clos (are_connected dpR R) uv' uv).
Proof.
intros dpR R comp H1 uv uv' H2 [H3 H4].
apply H2; clear H2.
destruct H3 as [a | a b H3].
apply eq_refl.
destruct H4 as [a | a b H4].
apply eq_refl.
apply Nat.le_antisymm.
clear H4; induction H3 as [a b H3 | a b c H3 H4].
apply H1; assumption.
apply Nat.le_trans with (comp b); [ apply H1 | ]; assumption.
clear H3; induction H4 as [a b H3 | a b c H3 H4].
apply H1; assumption.
apply Nat.le_trans with (comp b); [ apply H1 | ]; assumption.
Qed.

End MakeDP.
