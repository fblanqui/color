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


(** * Equational theory on a term algebra *)

From Stdlib Require Import List Relations Wellfounded Arith Setoid.
From CoLoR Require Import closure more_list weaved_relation dickson term_spec
     equational_theory_spec.

Notation " T '-[' R ']->' U " := (R U T) (at level 80) : term_scope .


(** ** A functor building a Module EqTh from a term algebra. *)
Module Make (T1 : term_spec.Term)  <: EqTh with Module T:=T1.

  Module T := T1.
  Import T.

  Inductive defined (R : relation term) : symbol -> Prop :=
  | Def : forall f l t, R t (Term f l) -> defined R f.

  Inductive constructor (R : relation term) : symbol -> Prop :=
  | Const : forall f, (forall l t, ~ (R t (Term f l))) -> constructor R f.

  Inductive module (R1 R2 : relation term) : Prop :=
  | Mod : (forall f2 s t, defined R2 f2 -> 
    R1 s t -> symb_in_term_list f2 (s :: t :: nil) = false) ->
  module R1 R2.

(** *** One step at top. *)
  Inductive axiom (R : relation term) : term -> term -> Prop :=
  | instance : forall t1 t2 sigma,
    R t1 t2 -> axiom R (apply_subst sigma t1) (apply_subst sigma t2).

(** *** One step at any position. *)
  Inductive one_step (R : relation term) : term -> term -> Prop :=
  | at_top : forall t1 t2, axiom R t1 t2 -> one_step R t1 t2
  | in_context : forall f l1 l2, one_step_list (one_step R) l1 l2 -> one_step R (Term f l1) (Term f l2).

(** *** Rewriting Theory as transitive closure of an equational step. *)
  Definition rwr (R : relation term) := trans_clos (one_step R).

Lemma one_step_one_rule :
forall R s t, one_step R t s -> exists r, exists l, R r l /\ one_step (fun r' l' => In (r',l') ((r,l) :: nil)) t s.
Proof.
intros R s; pattern s; apply term_rec3; clear s.
intros v t K; inversion K; subst.
inversion H; subst.
destruct t2 as [x2 | f2 l2].
exists t1; exists (Var x2); split; [assumption | apply at_top; apply instance; left; apply eq_refl].
discriminate.
intros f l IH t K; inversion K; subst.
inversion H; subst.
exists t1; exists t2; split; trivial.
left; apply instance; left; apply eq_refl.
destruct (one_step_in_list H1) as [u [u' [k1 [k2 [H2 [H3 H4]]]]]].
assert (u_in_l : In u l).
subst; apply in_or_app; right; left; apply eq_refl.
destruct (IH u u_in_l u' H2) as [t1 [t2 [K1 K2]]].
exists t1; exists t2; split; trivial.
apply in_context.
clear IH K H1 u_in_l; subst l l1; induction k1 as [ | a1 k1].
left; assumption.
right; apply IHk1; trivial.
Qed.

Lemma one_step_one_step : forall R s t, one_step (one_step R) s t <-> one_step R s t.
Proof.
intros R s t; split; intro H.
revert s H; pattern t; apply term_rec3; clear t.
intros v s H; inversion H as [t1 t2 K | ]; clear H; subst.
inversion K as [t1 t2 sigma H1 H2 H3]; clear K; subst.
inversion H1 as [s1 s2 K | f l1 l2 K]; clear H1; subst.
inversion K as [s1 s2 tau K1 K2 K3]; clear K; subst.
do 2 rewrite <- subst_comp_is_subst_comp; apply at_top; apply instance; assumption. 
discriminate.
intros f l IHl s H; inversion H as [t1 t2 K | g l1 l2 K1 K2 K3]; clear H; subst.
inversion K as [t1 t2 sigma H1 H2 H3]; clear K; subst.
inversion H1 as [s1 s2 K | g l1 l2 K]; clear H1; subst.
inversion K as [s1 s2 tau K1 K2 K3]; clear K; subst.
do 2 rewrite <- subst_comp_is_subst_comp; apply at_top; apply instance; assumption. 
simpl; right.
injection H3; clear H3; intros; subst.
revert sigma IHl; induction K as [t1 t2 l K | t l1 l2 K]; intros sigma IHl.
left; apply IHl; [left; apply eq_refl | left; apply instance; assumption].
right; apply (IHK sigma (tail_prop _ IHl)).
right; revert IHl; induction K1 as [t1 t2 l K | t l1 l2 K]; intros IHl.
left; apply IHl; [left; apply eq_refl | assumption].
right; apply (IHK (tail_prop _ IHl)).
left; generalize (instance _ s t nil H); do 2 rewrite empty_subst_is_id; trivial.
Qed.

Lemma R_in_rwr_R : 
  forall t1 t2 (R : term -> term -> Prop),
  R t1 t2 -> rwr R t1 t2.
Proof.
intros t1 t2 R H; apply t_step; apply at_top; 
generalize (instance R t1 t2 nil H); do 2 rewrite empty_subst_is_id; trivial.
Qed.

  Lemma no_need_of_instance' : forall (R : relation term) t1 t2, R t1 t2 -> axiom R t1 t2.
  Proof.
    intros R t1 t2 H.
    replace t1 with (apply_subst nil t1); [idtac | apply empty_subst_is_id].
    replace t2 with (apply_subst nil t2); [idtac | apply empty_subst_is_id].
    apply instance; trivial.
  Qed.

  Notation " T '-[' R '+]->' U " := (rwr R T U) (at level 80) : term_scope .

  #[global] Hint Constructors axiom one_step one_step_list trans_clos : core.

(** *** Rewriting is a congruence. *)
  Lemma context_cons :
    forall R f t1 t2 l, rwr R t1 t2 -> rwr R (Term f (t1 :: l)) (Term f (t2 :: l)).
  Proof.
    intros R f t1 t2 l H;
      induction H as [ | t1 t2 t3 Trans1 Trans2].
    left; apply in_context; left; assumption.
    apply t_trans with (Term f (t2 :: l)); trivial.
    apply in_context; left; assumption.
  Qed.

  Lemma one_step_context_in :
    forall R t1 t2 f l l', one_step R t1 t2 -> 
      one_step R (Term f (l ++ t1 :: l')) (Term f (l ++ t2 :: l')).
  Proof.
    intros R t1 t2 f l l' H; apply in_context; 
      induction l as [ | t l ]; simpl; [ apply head_step | apply tail_step ]; 
        trivial.
  Qed.

  Lemma context_in :
    forall R t1 t2, rwr R t1 t2 -> 
      forall f l l', rwr R (Term f (l ++ t1 :: l')) (Term f (l ++ t2 :: l')).
  Proof.
    intros R t1 t2 H; 
      induction H as [ t1 t2 Step 
        | t1 t2 t3 Trans1 Trans2].
    intros f l l'; apply t_step; apply one_step_context_in; trivial.
    intros f l l'; apply t_trans with (Term f (l ++ t2 :: l')).
    apply in_context; clear - Trans1; induction l; [left | right]; assumption.
    apply IHTrans2.
  Qed.

Lemma general_context :
  forall R f l1 l2, rwr_list (one_step R) l1 l2 -> rwr R (Term f l1) (Term f l2).
Proof.
intros R f l1 l2 H; induction H as [l1 l2 H | l1 l2 l3 H1 H2].
left; right; assumption.
right with (Term f l2); trivial.
right; assumption.
Qed.

(** *** Compatibility with substitutions. *)
  Lemma one_step_apply_subst :
    forall R t1 t2 sigma , one_step R t1 t2 ->
      one_step R (apply_subst sigma t1) (apply_subst sigma t2).
  Proof.
    intros R t; pattern t; apply term_rec3; clear t.
    intros x1 t2 sigma H; 
      inversion_clear H as [ t1' t2' H'|];
        inversion_clear H' as [ t1' t2' tau H''];
          do 2 (rewrite <- subst_comp_is_subst_comp); auto.
    intros f1 l1 Hrec t2 sigma H; 
      inversion_clear H as [ t1' t2' H'| f l1' l2 H''].
    inversion_clear H' as [ t1' t2' tau H'']; 
      do 2 (rewrite <- subst_comp_is_subst_comp); auto.
    simpl; apply in_context; generalize l2 H''; clear l2 H''; 
      induction l1 as [ | a1 l1].
    intros l2 H; inversion_clear H.
    intros l2' H; inversion_clear H as [ t1' a2 l H' | t' l1' l2 H'].
    simpl; apply head_step; apply Hrec; trivial; left; trivial.
    simpl; apply tail_step;  apply IHl1; trivial; intros; 
      apply Hrec; trivial; right; trivial.
  Qed.

Lemma one_step_subterm_subst :
   forall R s t sigma, 
   refl_trans_clos (union _ (one_step R) (direct_subterm)) s t ->
   refl_trans_clos (union _ (one_step R) (direct_subterm)) (apply_subst sigma s) (apply_subst sigma t).
Proof.
intros R s t sigma [s' | s' t' H].
left.
right; induction H as [t1 t2 [H | H] | t1 t2 t3 H1 H2].
do 2 left; apply one_step_apply_subst; trivial.
destruct t2 as [v2 | f2 l2].
contradiction.
simpl in H.
left; right; simpl; rewrite in_map_iff; exists t1; split; trivial.
apply trans_clos_is_trans with (apply_subst sigma t2); trivial.
destruct H1 as [H1 | H1].
do 2 left; apply one_step_apply_subst; trivial.
destruct t2 as [v2 | f2 l2].
contradiction.
simpl in H1.
left; right; simpl; rewrite in_map_iff; exists t1; split; trivial.
Qed.

  Lemma rwr_apply_subst :
    forall R t1 t2 sigma, rwr R t1 t2 -> 
      rwr R (apply_subst sigma t1) (apply_subst sigma t2).
  Proof.
    intros R t1 t2 sigma H; 
      induction H as [ | t1 t2 t3 H1 Hrec1 H2].
    apply t_step; apply one_step_apply_subst; trivial.
    apply t_trans with (apply_subst sigma t2); trivial.
    apply one_step_apply_subst; trivial.
  Qed.

(** *** Inclusion of relations and associated equational theories. *)
  Lemma rwr_inv : 
    forall A R (eq : A -> A -> Prop) (f : term -> A), 
      (forall a1 a2 a3, eq a1 a2 -> eq a2 a3 -> eq a1 a3) ->
      (forall t1 t2, one_step R t1 t2 -> eq (f t1) (f t2)) ->
      forall t1 t2, rwr R t1 t2 -> eq (f t1) (f t2).
  Proof.
    intros A R eq f eq_trans Step_inv t1 t2 H; induction H; auto.
    apply eq_trans with (f y); auto.
  Qed.

  Lemma axiom_incl :
    forall (R1 R2 : term -> term -> Prop) , 
      (forall t1 t2, R1 t1 t2 -> R2 t1 t2) ->
      forall t1 t2, axiom R1 t1 t2 -> axiom R2 t1 t2.
  Proof.
    intros R1 R2 Incl t1 t2 H; inversion H; auto.
  Qed.

  Lemma one_step_incl :
    forall (R1 R2 : term -> term -> Prop) , 
      (forall t1 t2, R1 t1 t2 -> R2 t1 t2) ->
      forall t1 t2, one_step R1 t1 t2 -> one_step R2 t1 t2.
  Proof.
    intros R1 R2 Incl t1; pattern t1; apply term_rec3; clear t1.
    intros x1 t2 H; inversion H; 
      apply at_top; apply axiom_incl with R1; trivial.
    intros f1 l1 Hrec t2 H; inversion_clear H as [| f l1' l2 H'].
    apply at_top; apply axiom_incl with R1; trivial.
    apply in_context; generalize l2 H'; clear l2 H'; 
      induction l1 as [ | a1 l1 ]; intros l2 H; inversion_clear H.
    apply head_step; apply Hrec; trivial; left; trivial.
    apply tail_step; apply IHl1; trivial; intros; apply Hrec; trivial; right; trivial.
  Qed.

  Lemma rwr_incl :
    forall (R1 R2 : term -> term -> Prop), 
      (forall t1 t2, R1 t1 t2 -> R2 t1 t2) ->
      forall t1 t2, rwr R1 t1 t2 -> rwr R2 t1 t2.
  Proof.
    intros R1 R2 Incl t1 t2 H; induction H; auto.
    apply t_step; apply one_step_incl with R1; trivial.
    apply t_trans with y; auto.
    apply one_step_incl with R1; trivial.
  Qed.

Lemma rwr_list_incl :
  forall (R1 R2 : term -> term -> Prop), 
  (forall t1 t2, R1 t1 t2 -> R2 t1 t2) ->
  forall l1 l2, rwr_list (one_step R1) l1 l2 -> rwr_list (one_step R2) l1 l2.
Proof.
intros R1 R2 Incl.
apply trans_incl.
do 2 intro; apply one_step_list_incl.
do 2 intro; apply one_step_incl; assumption.
Qed.

Lemma th_eq_closure_one_step :
  forall (R : term -> term -> Prop), 
  forall t1 t2, one_step (rwr R) t1 t2 -> rwr R t1 t2.
Proof.
intros R t1; pattern t1; apply term_rec3; clear t1.
intros x1 t2 H; inversion_clear H as [ t1' t2' H' | ];
inversion_clear H'; apply rwr_apply_subst; trivial.
intros f1 l1 Hrec t2 H; inversion_clear H as [ t1' t2' H' | f' l1' l2 H'].
inversion_clear H'; apply rwr_apply_subst; trivial.
apply general_context; generalize l2 H'; clear l2 H'.
induction l1 as [ | a1 l1 ]; intros l2 H.
inversion H.
inversion H as [ H1 a2 H3 a1_R_a2 H5 H6 | H1 H2 l2' l1_R_l2' H5 H6]; subst.
generalize (Hrec _ (or_introl _ (eq_refl _)) _ a1_R_a2).
clear; intro H; induction H as [a1 a2 H | a1 a2 a3 H1 H2].
do 2 left; assumption.
right with (a2 :: l1); trivial.
left; assumption.
generalize (IHl1 (tail_prop _ Hrec) l2' l1_R_l2').
clear; intro H; induction H as [l1 l2 H | l1 l2 l3 H1 H2].
left; right; assumption.
apply trans_clos_is_trans with (a1 :: l2); trivial.
left; right; assumption.
Qed.

  Lemma th_eq_closure :
    forall t1 t2 (R : term -> term -> Prop),
      rwr (rwr R) t1 t2 -> rwr R t1 t2.
  Proof.
    intros t1 t2 R.
    generalize (th_eq_closure_one_step R); unfold rwr.
    generalize  (trans_clos_is_trans (R := one_step R)).
    generalize (trans_clos (one_step R)); clear R.
    intros rwr_R rwr_R_trans 
      rwr_R_step H; induction H as [ | ]; auto.
    apply rwr_R_trans with y; auto.
  Qed.

Lemma rwr_at_pos :
 forall R p t sigma u v t', subterm_at_pos t p = Some (apply_subst sigma u) -> 
  rwr R u v -> t' = (replace_at_pos t (apply_subst sigma v) p) -> rwr R t t'.
Proof.
intros R p; induction p as [ | i p]; intros t sigma u v t' Sbt H H'; simpl in Sbt.
injection Sbt; clear Sbt; intros; subst; simpl.
apply th_eq_closure; apply t_step; apply at_top; apply instance; trivial.
destruct t as [x | f l].
discriminate.
subst t'; simpl; apply general_context.
revert l Sbt; induction i as [ | i]; intros [ | s l] Sbt; simpl.
discriminate.
simpl in Sbt.
generalize (IHp s sigma u v _ Sbt H (eq_refl _)).
generalize (replace_at_pos s (apply_subst sigma v) p); clear.
intros t H; induction H as [t1 t2 H | t1 t2 t3 H1 H2].
do 2 left; assumption.
right with (t2 :: l); [left | idtac]; assumption.
discriminate.
simpl in Sbt; generalize (IHi _ Sbt); clear.
intro H; induction H as [l1 l2 H | l1 l2 l3 H1 H2].
left; right; assumption.
apply trans_clos_is_trans with (s :: l2); trivial.
left; right; assumption.
Qed.

  Lemma split_rel :
    forall R1 R2 s t, one_step (union _ R1 R2) t s <->
      (one_step R1 t s \/ one_step R2 t s).
  Proof. 
    intros R1 R2 s; pattern s; apply term_rec2; clear s.
    intro n; induction n as [ | n]; intros s Size_s.
    absurd (1 <= 0); auto with arith; apply Nat.le_trans with (size s); trivial;
      apply size_ge_one.
    intros t; split; intro H.
    inversion H as [s' t' H' | f' lt ls H']; subst.
    inversion H' as [t' s' sigma H'']; subst.
    destruct H'' as [K1 | K2].
    left; apply at_top; apply instance; trivial.
    right; apply at_top; apply instance; trivial.
    assert (Size_ls : forall s, In s ls -> size s <= n). 
    intros s s_in_ls; apply le_S_n.
    apply Nat.le_trans with (size (Term f' ls)); trivial.
    apply size_direct_subterm; trivial.
    clear H Size_s; 
      assert (H'' : one_step_list (one_step R1) lt ls \/
        one_step_list (one_step R2) lt ls).
    induction H' as [t' s' l H'' | s lt' ls' H'']; subst.
    rewrite (IHn s' (Size_ls s' (or_introl _ (eq_refl _))) t') in H''.
    destruct H'' as [H1 | H2].
    left; apply head_step; trivial.
    right; apply head_step; trivial.
    destruct IHH'' as [H1 | H2].
    intros; apply Size_ls; right; trivial.
    left; apply tail_step; trivial.
    right; apply tail_step; trivial.
    destruct H'' as [H1 | H2]; [left | right]; apply in_context; trivial.
    destruct H as [H1 | H2].
    apply one_step_incl with R1; trivial.
    intros; left; trivial.
    apply one_step_incl with R2; trivial.
    intros; right; trivial.
  Qed.

  Lemma no_need_of_instance_is_modular :
    forall (R1 R2 : term -> term -> Prop), 
      (forall t1 t2, axiom R1 t1 t2 -> R1 t1 t2) ->
      (forall t1 t2, axiom R2 t1 t2 -> R2 t1 t2) ->
      (forall t1 t2, axiom (union term R1 R2) t1 t2 -> (union term R1 R2) t1 t2).
  Proof.
    intros R1 R2 H1 H2 t1 t2 H;
      inversion H as [t1' t2' sigma H']; subst;
        inversion H'; [left; apply H1 | right; apply H2];
          apply instance; trivial.
  Qed.

  Definition sym_refl R (t1 t2 : term) := R t1 t2 \/ R t2 t1 \/ t1 = t2.
  Definition th_eq R := rwr (sym_refl R).

  Notation " T '<-[' R '*]->' U " := (th_eq R T U) (at level 80) : term_scope .

  Lemma th_refl : forall R t, th_eq R t t.
  Proof.
    unfold th_eq, sym_refl.
    intros R t; apply t_step; apply at_top; rewrite <- (empty_subst_is_id t);
      apply instance; right; right; trivial.
  Qed.

  Lemma th_sym : forall R t1 t2, th_eq R t1 t2 -> th_eq R t2 t1.
  Proof.
    intro R.
    intros t1 t2 H; refine (rwr_inv term (sym_refl R) 
      (fun u1 u2 => th_eq R u2 u1) (fun t => t) _ _ _ _ _); trivial.
    unfold th_eq; intros; apply trans_clos_is_trans with a2; trivial.
    unfold th_eq; clear t1 t2 H; intros t1 t2 H; apply t_step.
    assert (axiom_sym : 
      forall t1 t2, axiom (sym_refl R) t1 t2 -> axiom (sym_refl R) t2 t1).
    clear t1 t2 H; intros t1 t2 H; inversion_clear H as [u1 u2 sigma H'].
    destruct H' as [H' | [H' | H']].
    apply instance; right; left; trivial.
    apply instance; left; trivial.
    apply instance; right; right; subst; trivial.
    generalize t2 H; clear t2 H; pattern t1; apply term_rec3; clear t1.
    intros v1 t2 H; inversion_clear H as [ H1 H2 H' | f l1 l2 H' ].
    apply at_top; apply axiom_sym; trivial.
    intros f l1 IH t2 H; inversion_clear H as [H1 H2 H' | H1 H2 l2 H'].
    apply at_top; apply axiom_sym; trivial.
    apply in_context; generalize l2 H'; clear f t2 l2 H'; 
      induction l1 as [ | t1 l1].
    intros l2 H'; inversion H'.
    intros [ | t2 l2] H'; 
      inversion_clear H' as [ H1 H2 H'' | f l1' l2' H'' ].
    apply head_step; apply IH; trivial; left; trivial.
    apply tail_step; apply IHl1; trivial; intros; apply IH; trivial; right; trivial.
  Qed.

 
(** *** Accessibility of the rewriting relation. *)
  Lemma acc_one_step : 
    forall R t, Acc (one_step R) t <-> Acc (rwr R) t.
  Proof.
    intros R t; split.
    apply acc_trans.
    apply Acc_incl; intros; left; assumption.
  Qed.

Lemma rwr_sub_acc_sub_acc_sub :
  forall R l1 l2, refl_trans_clos (one_step_list (one_step R)) l2 l1 -> 
  (forall s, In s l1 -> Acc (one_step R) s) -> (forall s, In s l2 -> Acc (one_step R) s).
Proof.
assert (H : forall R l1 l2, one_step_list (one_step R) l2 l1 -> 
  (forall s, In s l1 -> Acc (one_step R) s) -> (forall s, In s l2 -> Acc (one_step R) s)).
intros R l1 l2 H; induction H; simpl.
intros Hacc s [s_eq_t1 | s_in_l].
apply Acc_inv with t2; [apply Hacc; left; apply eq_refl | subst s; assumption ].
apply Hacc; right; assumption.
intros Hacc s [s_eq_t | s_in_l1].
apply Hacc; left; assumption.
apply IHone_step_list; [ intros; apply Hacc; right; assumption | assumption].
intros R l1 l2 K; inversion K; clear K; subst; trivial.
induction H0 as [l1 l2 H1 | l1 l2 l3 H1 H2].
apply H; assumption.
intro H3; apply H with l2; trivial.
apply IHH2; assumption.
Qed.

  Lemma acc_subterms :
    forall R, (forall x t, ~ (R t (Var x))) -> 
      forall f l, (forall t, In t l -> Acc (one_step R) t) -> constructor R f ->
        Acc (one_step R) (Term f l).
  Proof.
    intros R HR f l Acc_l Cf'; inversion Cf' as [f' Cf]; clear Cf'; subst f';
      rewrite acc_one_step_list in Acc_l.
    pattern l; refine (@Acc_ind _ (one_step_list (one_step R)) _ _ l Acc_l).
    clear l Acc_l; intros l Acc_l IH.
    apply Acc_intro.
    intros t H; inversion H as [t1 t2 H' | f' l1 l2 H']; subst.
    inversion H' as [t1 t2 sigma H'' H3 H''']; subst; destruct t2 as [x2 | f2 l2].
    absurd (R t1 (Var x2)); trivial; apply HR.
    simpl in H'''; injection H'''; clear H'''; intros; subst;
      absurd (R t1 (Term f l2)); trivial; apply Cf.
    apply IH.
    generalize l1 l H'.
    intro k; induction k as [ | s k]; intros k' K; inversion K; subst.
    apply head_step; trivial.
    apply tail_step; trivial.
  Qed.

  Lemma acc_subterms_1 :
    forall R t s, Acc (one_step R) t -> direct_subterm s t -> Acc (one_step R) s.
  Proof.
    intros R t s Acc_t; generalize s; clear s; pattern t;
      refine (@Acc_ind _ (one_step R) _ _ t Acc_t).
    clear t Acc_t; intros t Acc_t IH s H; destruct t as [ x | f l]; simpl in H.
    contradiction.
    apply Acc_intro; intros u H';
      destruct (In_split _ _ H) as [l1 [l2 H'']]; subst l;
        apply (IH (Term f (l1 ++ u :: l2))).
    apply one_step_context_in; trivial.
    simpl; apply in_or_app; right; left; trivial.
  Qed.

  Lemma acc_subterms_3 : 
    forall R p t s, Acc (one_step R) t -> subterm_at_pos t p = Some s -> 
      Acc (one_step R) s.
  Proof.
    intros R p; induction p as [ | i p]; intros t s Acc_t H; simpl in H.
    injection H; intro; subst; trivial.
    destruct t as [ x | f l].
    discriminate.
    assert (H' := nth_error_ok_in i l); destruct (nth_error l i) as [ s' | ].
    generalize (H' _ (eq_refl _)); clear H'; intro s'_in_l.
    apply (IHp s'); trivial; apply (acc_subterms_1 R (Term f l)); trivial.
    destruct s'_in_l as [l1 [l2 [_ H']]]; subst l; simpl; 
      apply in_or_app; right; left; trivial.
    discriminate.
  Qed.

  Lemma acc_with_subterm_subterms :
    forall R t, Acc (union _ (one_step R) direct_subterm) t ->
      forall s, direct_subterm s t ->
        Acc (union _ (one_step R) direct_subterm) s.
  Proof.
    intros R t Acc_t; induction Acc_t as [t Acc_t IH].
    intros s H; apply Acc_t; right; trivial.
  Qed.

  Lemma acc_with_subterm :
    forall R t, Acc (one_step R) t <-> 
      Acc (union _ (one_step R) direct_subterm) t.
  Proof.
    intros R t; split.
    intro Acc_t; induction Acc_t as [t Acc_t IH].
    generalize Acc_t IH; clear Acc_t IH; pattern t; apply term_rec2; clear t.
    intro n; induction n as [ | n]; intros t size_t Acc_t IH.
    absurd (1 <= 0); auto with arith; apply Nat.le_trans with (size t); trivial;
      apply size_ge_one.
    apply Acc_intro.
    intros u H; destruct H as [H | H].
(* 1/2 one_step R *)
    apply IH; trivial.
(* 1/1 direct_subterm *)
    apply IHn.
    apply le_S_n; apply Nat.le_trans with (size t); trivial.
    apply size_direct_subterm; trivial.
    assert (H' : Acc (one_step R) u).
    apply acc_subterms_1 with t; trivial.
    apply Acc_intro; apply Acc_t.
    inversion H'; trivial.
    intros v v_R_u.
    destruct t as [ x | f l].
    contradiction.
    destruct (In_split _ _ H) as [l' [l'' H'']]; clear H; subst l.
    apply (acc_with_subterm_subterms R (Term f (l' ++ v :: l''))).
    apply IH; apply one_step_context_in; trivial.
    simpl; apply in_or_app; right; left; trivial.
    apply Acc_incl; intros t1 t2 H; left; trivial.
  Qed.

  Lemma var_acc : 
    forall R l x sigma, In x (var_list_list l) -> 
      (forall t, In t (map (apply_subst sigma) l) -> Acc (one_step R) t) ->
      Acc (one_step R) (apply_subst sigma (Var x)).
  Proof.
    intros R l; pattern l; apply (list_rec3 size); clear l;
      intro n; induction n as [ | n]; intros [ | t l] Sl x sigma H Acc_l.
    simpl in H; contradiction.
    simpl in Sl; absurd (1 <= 0); auto with arith.
    apply Nat.le_trans with (size t).
    apply size_ge_one.
    refine (Nat.le_trans _ _ _ _ Sl); auto with arith.
    simpl in H; contradiction.
    assert (Sl' : list_size size l <= n).
    apply le_S_n; refine (Nat.le_trans _ _ _ _ Sl); simpl;
      apply (Nat.add_le_mono_r 1 (size t) (list_size size l)); apply size_ge_one.
    destruct t as [y | g k].
    simpl in H; destruct H as [y_eq_x | x_in_l].
    subst y; apply Acc_l; simpl map; left; trivial.
    apply (IHn l); trivial; intros; apply Acc_l; simpl map; right; trivial.
    assert (Sk : list_size size k <= n).
    apply le_S_n; refine (Nat.le_trans _ _ _ _ Sl); simpl; rewrite (list_size_fold size k);
    apply le_n_S; apply Nat.le_add_r.
    assert (Acc_k : forall t, In t (map (apply_subst sigma) k) -> Acc (one_step R) t).
    intros t H'; apply acc_subterms_1 with (Term g (map (apply_subst sigma) k)).
    apply Acc_l; simpl map; left; trivial.
    trivial.
    replace (var_list_list (Term g k :: l)) with (var_list (Term g k)  ++ var_list_list l) in H; trivial.
    rewrite var_list_unfold in H.
    generalize (IHn _ Sk x sigma).
    destruct (in_app_or _ _ _ H) as [x_in_k | x_in_l].
    clear H; intro H; generalize (H x_in_k); clear H; intro H; apply H.
    intros t H'; apply Acc_k; trivial.

    simpl in H; intros _; apply (IHn l); trivial.
    intros t H'; apply Acc_l; right; trivial.
  Qed.

  Fixpoint compute_head_red s rule_list {struct rule_list} : list term :=
    match rule_list with
      | nil => nil
      | (l,r) :: rule_list =>
        match matching ((l,s) :: nil) with
          | Some sigma => (apply_subst sigma r) :: compute_head_red s rule_list
          | None => compute_head_red s rule_list
        end
    end.

  Lemma compute_head_red_is_correct :
    forall rule_list, (forall l r, In (l,r) rule_list -> forall v, In v (var_list r) -> In v (var_list l)) -> 
      forall R, (forall l r, R r l <-> In (l,r) rule_list) ->
        forall t s, (In s (compute_head_red t rule_list) <-> axiom R s t).
  Proof.
    intros rule_list; induction rule_list as [ | [l r] rule_list];
      intros Reg R Equiv t s; split; intro H.
    contradiction.
    inversion H; subst.
    rewrite Equiv in H0; contradiction.
    simpl in H.
    case_eq (matching ((l,t) :: nil)).
    intros sigma mlt_eq_sigma.
    destruct (matching_correct mlt_eq_sigma) as [C1 [C2 C3]].
    assert (H' := C3 _ _ (or_introl _ (eq_refl _))).
    rewrite mlt_eq_sigma in H.
    destruct H as [H | H].
    subst; apply instance.
    rewrite Equiv; left; trivial.
    set (R' := fun r l => In (l,r) rule_list).
    apply axiom_incl with R'; trivial.
    intros l1 r1; unfold R'; rewrite Equiv; intro; right; trivial.
    rewrite <- IHrule_list; trivial.
    intros l1 r1 l1r1_in_rule_list; apply Reg; right; trivial.
    intros l1 r1; unfold R'; intuition.
    intro mlt_eq_none; rewrite mlt_eq_none in H.
    set (R' := fun r l => In (l,r) rule_list).
    apply axiom_incl with R'; trivial.
    intros l1 r1; unfold R'; rewrite Equiv; intro; right; trivial.
    rewrite <- IHrule_list; trivial.
    intros l1 r1 l1r1_in_rule_list; apply Reg; right; trivial.
    intros l1 r1; unfold R'; intuition.

    inversion H; subst.
    rewrite Equiv in H0.
    destruct H0 as [H0 | H0].
    injection H0; clear H0; intros; subst t1 t2.
    simpl.
    assert (C := @matching_correct ((l, apply_subst sigma l) :: nil)).
    assert (C' := matching_complete ((l, apply_subst sigma l) :: nil) sigma).
    destruct (matching ((l, apply_subst sigma l) :: nil)) as [tau | ].
    generalize (C _ (eq_refl _)); clear C; intros [C1 [C2 C3]].
    left.
    assert (H' : forall v, In v (var_list r) -> apply_subst tau (Var v) = apply_subst sigma (Var v)).
    intros v v_in_r;
      assert (v_in_l : In v (var_list l)).
    apply Reg with r; trivial; left; trivial.
    apply C' with l (apply_subst sigma l); trivial.
    intros p s [ps_eq_llsigma | ps_in_nil]; [idtac | contradiction].
    injection ps_eq_llsigma; intros; subst; trivial.
    left; trivial.
    generalize r H'; clear H'; intro t; pattern t; apply term_rec3; clear t.
    intros v IH; apply IH; left; trivial.
    intros f k IHl IH.
    simpl; apply (f_equal (fun ll => Term f ll)).
    apply map_eq; intros a a_in_k; apply IHl; trivial.
    destruct (In_split _ _ a_in_k) as [k1 [k2 K]]; subst.
    intros v v_in_a; apply IH.
    apply (@var_in_subterm v a (Term f (k1 ++ a :: k2)) (length k1 :: nil)); trivial.
    simpl; rewrite nth_error_at_pos; trivial.
    assert False.
    apply C'.
    intros p s [ps_eq_llsigma | ps_in_nil]; [idtac | contradiction].
    injection ps_eq_llsigma; intros; subst; trivial.
    contradiction.
    simpl.
    assert (H' : forall l r : term,
      In (l, r) rule_list ->
      forall v : variable, In v (var_list r) -> In v (var_list l)).
    intros l1 r1 lr_in_rule_list; apply Reg; right; trivial.
    destruct (matching ((l, apply_subst sigma t2) :: nil)) as [tau | ]; [right | idtac].
    set (R' := fun r l => In (l,r) rule_list).
    rewrite (IHrule_list H' R'); trivial.
    apply instance; unfold R'; trivial.
    intros l1 r1; unfold R'; split; trivial.
    set (R' := fun r l => In (l,r) rule_list).
    rewrite (IHrule_list H' R'); trivial.
    apply instance; unfold R'; trivial.
    intros l1 r1; unfold R'; split; trivial.
  Qed.

  Definition o_size t1 t2 := size t1 < size t2.

  Lemma wf_size : well_founded o_size.
  Proof.
    unfold well_founded, o_size.
    intros t; apply Acc_intro.
    generalize (size t); clear t. 
    intro n; induction n as [ | n].
    intros y Abs; absurd (size y < 0); auto with arith.
    intros y Sy; inversion Sy; subst.
    apply Acc_intro; intros x Sx; apply IHn; trivial.
    apply IHn; trivial.
  Defined.

  Lemma term_acc_subst :
    forall R t sigma, Acc (one_step R) (apply_subst sigma t) -> Acc (one_step R) t.
  Proof.
    assert (H : forall R s, Acc (one_step R) s -> 
      forall t sigma, s = (apply_subst sigma t) -> Acc (one_step R) t).
    intros R s Acc_s; induction Acc_s as [s Acc_s IH']; intros t sigma H.
    subst s.
    assert (IH : forall u tau, one_step R (apply_subst tau u) (apply_subst sigma t) ->
      Acc (one_step R) u). 
    intros u tau H; apply (IH' _ H u tau); trivial.
    clear IH'.
    apply Acc_intro.
    intros u u_R_t; apply IH with sigma.
    apply one_step_apply_subst; trivial.
    intros R t sigma H'; apply H with (apply_subst sigma t) sigma; trivial.
  Qed.

  Lemma nf_one_step_subterm:
    forall R t, nf (one_step R) t -> forall s, direct_subterm s t -> nf (one_step R) s.
  Proof.
    intros R t; pattern t; apply term_rec3; clear t.
    intros v _ s H; contradiction.
    simpl; intros f l IH Hnf s s_in_l u H.
    destruct (In_split _ _ s_in_l) as [l' [l'' H']]; subst.
    apply (Hnf (Term f (l' ++ u :: l''))).
    apply in_context; clear IH Hnf s_in_l; induction l' as [ | s' l']; simpl.
    apply head_step; trivial.
    apply tail_step; apply IHl'.
  Qed.

  Section Compute_Red.
    Variable rule_list : list (term * term).

(** *** Definition of a step of compute_red. *)
    Definition F_compute_red:
      forall t (crec : forall s, o_size s t -> list term), list term.
    Proof.
      intros t crec; destruct t as [v | f l].
      exact (compute_head_red (Var v) rule_list).
      assert (crec_l : forall t (t_in_l : In t l), list term).
      intros t t_in_l; exact (crec t (size_direct_subterm t (Term f l) t_in_l)).
      exact ((compute_head_red (Term f l) rule_list) ++
	(map (fun k => Term f k) (mapii_dep (Dep_fun l crec_l)))).
    Defined.

(** *** Definition of compute_red. *)
    Definition compute_red :  term -> list term :=
      Fix wf_size (fun t => list term) F_compute_red.

(** *** A more practical equivalent definition of compute_red. *)
    Lemma compute_red_unfold : 
      forall t : term, compute_red t = @F_compute_red t (fun y _ => compute_red y).
    Proof.
      intros t; unfold compute_red.
      refine (Fix_eq _ _ _ _ t).
      clear t; intros t F G H.
      unfold F_compute_red; destruct t as [ v | f l ]; simpl; auto.
      apply (f_equal (fun kk => compute_head_red (Term f l) rule_list ++ 
        (map (fun k => Term f k) kk))).
      apply mapii_dep_eq.
      intros t t_in_l; apply H.
    Qed.

    Lemma compute_red_is_correct :
      (forall l r, In (l,r) rule_list -> forall v, In v (var_list r) -> In v (var_list l)) -> 
      forall R, (forall l r, R r l <-> In (l,r) rule_list) ->
        forall t s, (In s (compute_red t) <-> one_step R s t).
    Proof.
      intros Reg R Equiv t; pattern t; apply term_rec3; clear t.
      intros v s; split; intro H.
      rewrite compute_red_unfold in H; simpl in H.
      apply at_top; 
        rewrite <- (compute_head_red_is_correct rule_list Reg R Equiv);
          trivial.
      inversion H; subst.
      rewrite compute_red_unfold; simpl.
      rewrite (compute_head_red_is_correct rule_list Reg R Equiv);
        trivial.
      intros f l IHl; split; intro H.
      rewrite compute_red_unfold in H; simpl in H.
      destruct (in_app_or _ _ _ H) as [H1 | H2]; clear H.
      apply at_top; 
        rewrite <- (compute_head_red_is_correct rule_list Reg R Equiv);
          trivial.
      rewrite in_map_iff in H2.
      destruct H2 as [k [H2 H3]].
      subst s; apply in_context.
      generalize IHl k H3; clear IHl k H3; induction l as [ | a l]; intros IHll k H3;
        rewrite mapii_dep_unfold in H3; simpl in H3; trivial.
      contradiction.
      destruct (in_app_or _ _ _ H3) as [H4 | H5]; clear H3.
      rewrite in_map_iff in H4.
      destruct H4 as [b [H4 H5]]; subst.
      apply head_step.
      rewrite <- (IHll a); trivial.
      left; trivial.
      rewrite in_map_iff in H5.
      destruct H5 as [l' [H5 H6]]; subst.
      apply tail_step.
      apply IHl; trivial.
      intros t t_in_l; apply IHll; right; trivial.

      inversion H; clear H; subst.
      rewrite compute_red_unfold; simpl.
      apply in_or_app; left; 
        rewrite (compute_head_red_is_correct rule_list Reg R Equiv);
          trivial.
      rewrite compute_red_unfold; simpl.
      apply in_or_app; right.
      rewrite in_map_iff; exists l1; split; trivial.
      generalize IHl; clear IHl; induction H2; intros IHl.
      rewrite mapii_dep_unfold; simpl.
      apply in_or_app; left.
      rewrite in_map_iff; exists t1; split; trivial.
      rewrite (IHl _ (or_introl _ (eq_refl _)) t1); trivial.
      rewrite mapii_dep_unfold; simpl.
      apply in_or_app; right.
      rewrite in_map_iff.
      exists l1; split; trivial.
      apply IHone_step_list; trivial.
      intros u u_in_l2; apply IHl; right; trivial.
    Qed.

  End Compute_Red.

  Lemma FB_nf_dec :
    forall R FB, (forall t s, one_step R s t <-> In s (FB t)) ->
      forall t, {nf (one_step R) t}+{~ nf (one_step R) t}.
  Proof.
    intros R FB red_dec t.
    case_eq (FB t).
    intro FBt ; left; unfold nf; intros s; rewrite (red_dec t s); rewrite FBt; contradiction.
    intros s l FBt; right; unfold nf; intro nf_t.
    apply (nf_t s); rewrite (red_dec t s); rewrite FBt; left; trivial.
  Defined.

(* ** Accessibility of substitutions *)

  Module VT : decidable_set.S with Definition A := (variable * term)%type.

    Definition A := (variable * term)%type.
    Definition eq_A := (@eq A).

    Definition eq_bool := fun vt1 vt2 =>
      match vt1, vt2 with (v1,t1), (v2,t2) => andb (X.eq_bool v1 v2) (T.eq_bool t1 t2) end.

    Lemma eq_bool_ok : forall vt1 vt2, match eq_bool vt1 vt2 with true => vt1 = vt2 | false => vt1 <> vt2 end.
    Proof.
      intros [v1 t1] [v2 t2]; generalize (X.eq_bool_ok v1 v2) (T.eq_bool_ok t1 t2).
      unfold eq_bool; case (eq_var_bool v1 v2).
      case (T1.eq_bool t1 t2).
      intros; subst; simpl; reflexivity.
      intros _ t1_diff_t2; simpl; intro vt1_eq_vt2; apply t1_diff_t2; injection vt1_eq_vt2; intros; subst; reflexivity.
      intros v1_diff_v2 _; simpl; intro vt1_eq_vt2; apply v1_diff_v2; injection vt1_eq_vt2; intros; subst; reflexivity.
    Defined.

  End VT.

  Module D := dickson.Make (VT).

  Definition rwr_subst R sigma' sigma :=
    trans_clos (D.multiset_extension_step (fun yval' xval => rwr R (snd yval') (snd xval))) sigma' sigma.

  Lemma acc_rwr_subst :
    forall R sigma, (forall x val, In (x,val) sigma -> Acc (one_step R) val) <-> Acc (rwr_subst R) sigma.
  Proof.
    intros R sigma; split.
    intro Acc_sigma; unfold rwr_subst.
    apply Acc_incl with (trans_clos (D.multiset_extension_step (fun yval' xval => rwr R (snd yval') (snd xval)))).
    intros t1 t2; trivial.
    apply acc_trans; apply D.dickson_strong.
    intros [x val] H.
    assert (Acc_rwr_val : Acc (rwr R) val).
    apply acc_trans; apply Acc_sigma with x; trivial.
    clear H; revert x; induction Acc_rwr_val as [val Acc_val IH].
    intros x; apply Acc_intro; intros [y val'] H; simpl in H.
    apply IH; trivial.

    intros Acc_sigma; induction Acc_sigma as [sigma Acc_sigma IH].
    intros y val yval_in_sigma; apply Acc_intro; intros val' H.
    destruct (In_split _ _ yval_in_sigma) as [sigma1 [sigma2 H']]; subst.
    apply (IH (sigma1 ++ (y,val') :: sigma2)) with y.
    unfold rwr_subst; apply t_step.
    refine (@D.rmv_case _ (sigma1 ++ (y, val') :: sigma2) (sigma1 ++ (y, val) :: sigma2) 
      (sigma1 ++ sigma2) ((y,val') :: nil) (y,val) _ _ _).
    unfold D.LP.EDS.eq_A.
    intros b [H' | H']; [subst; simpl; apply t_step; trivial | contradiction].
    simpl; apply D.LP.permut_sym; rewrite <- D.LP.permut_cons_inside; auto.
    unfold D.LP.EDS.eq_A; trivial.
    simpl; apply D.LP.permut_sym; rewrite <- D.LP.permut_cons_inside; auto.
    unfold D.LP.EDS.eq_A, D.LP.EDS.eq_A; trivial.
    apply in_or_app; right; left; trivial.
  Qed.

  Lemma acc_nf_subst : 
    forall R FB, (forall t s, In s (FB t) <-> one_step R s t) ->
      forall sigma, (forall x val, find eq_var_bool x sigma = Some val -> Acc (one_step R) val) ->
        {sigma' : substitution | (forall x val', In (x,val') sigma' <-> find eq_var_bool x sigma' = Some val') /\
          (forall x val, find eq_var_bool x sigma = Some val ->
            exists val', (In (x,val') sigma' /\ nf (one_step R) val' /\
              (val' = val \/ trans_clos (one_step R) val' val))) /\
          (forall x val', In (x,val') sigma' -> nf (one_step R) val') /\
          (forall x val', In (x,val') sigma' -> find eq_var_bool x sigma <> None)}.
  Proof.
    intros R FB red_dec sigma Acc_sigma.
    destruct (remove_garbage_subst sigma) as [tau [H1 [H H']]].
    assert (H'' : {sigma' : substitution | 
      (forall x val', In (x,val') sigma' <-> find eq_var_bool x sigma' = Some val') /\
      (forall x val, find eq_var_bool x tau = Some val ->
        exists val', (In (x,val') sigma' /\ nf (one_step R) val' /\
          (val' = val \/ trans_clos (one_step R) val' val))) /\
      (forall x val', In (x,val') sigma' -> nf (one_step R) val') /\
      (forall x val', In (x,val') sigma' -> find eq_var_bool x tau <> None)}).
    assert (Acc_tau : forall (x : variable) (val : term), In (x,val) tau -> Acc (one_step R) val).
    intros x val H''; apply (Acc_sigma x val); rewrite H1; apply H; trivial.

(* 1/2 *)
    clear sigma Acc_sigma H1; induction tau as [ | [x val] tau].
(* 1/3 *)
    exists (nil : substitution); repeat split; simpl.
    contradiction.
    discriminate.
    intros; discriminate.
    contradiction.
    contradiction.

(* 1/2 *)
    destruct IHtau as [sigma' [H1 [H2 [H3 K3]]]].
(* 1/5 *)
    intros y valy H4; destruct (In_split _ _ H4) as [tau1 [tau2 H5]]; subst tau.
    rewrite <- (H y valy).
    simpl; generalize (X.eq_bool_ok y x); case (eq_var_bool y x); 
      [intro y_eq_x; absurd (y = x) | intro y_diff_x]; trivial.
    subst y; apply (H' x x val valy nil tau1 tau2); trivial.
    right; apply in_or_app; right; left; trivial.
(* 1/4 *)
    intros y z valy valz tau1 tau2 tau3 H1;
      apply (H' y z valy valz ((x,val) :: tau1) tau2 tau3); subst; trivial.
(* 1/3 *)
    intros y valy H''; apply Acc_tau with y; right; trivial.
(* 1/2 *)
    destruct (acc_nf FB red_dec (Acc_tau x val (or_introl _ (eq_refl _)))) as [val' [H4 H5]].
    exists ((x,val') :: sigma'); split.
(* 1/3 *)
    intros y valy; split; intro H6.
(* 1/4 *)
    simpl in H6; destruct H6 as [H6 | H6].
    injection H6; clear H6; intros; subst; simpl.
    generalize (X.eq_bool_ok y y); case (eq_var_bool y y); [intros _ | intro y_diff_y; absurd (y = y)]; trivial.
    assert (H7 := K3 _ _ H6).
    assert (H8 := find_mem _ _ X.eq_bool_ok y tau).
    destruct (find eq_var_bool y tau) as [valy' | ]; [idtac | absurd (@None term = None); trivial].
    destruct (H8 _ (eq_refl _)) as [y' [tau1 [tau2 [H9 H10]]]]; subst y'; subst; clear H7 H8.
    generalize (H y valy') (X.eq_bool_ok y x); simpl; case (eq_var_bool y x); [intros _ y_eq_x | intros H7 y_diff_x].
    subst y; absurd (x = x); trivial; apply (H' x x val valy' nil tau1 tau2); trivial.
    rewrite <- H1; trivial.
(* 1/3 *)
    destruct (find_mem _ _ X.eq_bool_ok _ _ H6) as [y' [l1 [l2 [H7 H8]]]]; subst y'; rewrite H8.
    apply in_or_app; right; left; trivial.
    repeat split.
(* 1/4 *)
    intros y valy; simpl.
    generalize (X.eq_bool_ok y x); case (eq_var_bool y x); [intros y_eq_x H6 | intros y_diff_x H6].
    injection H6; clear H6; intros; subst y valy; exists val'; repeat split; trivial; left; trivial.
    destruct (H2 _ _ H6) as [valy' [K1 [K2 K4]]].
    exists valy'; repeat split; trivial; right; trivial.
(* 1/3 *)
    simpl; intros y valy [H6 | H6].
    injection H6; clear H6; intros; subst y valy; trivial.
    apply H3 with y; trivial.
(* 1/2 *)
    intros y valy; simpl.
    generalize (X.eq_bool_ok y x); case (eq_var_bool y x); [intros y_eq_x H6 | intros y_diff_x H6].
    discriminate.
    apply K3 with valy; trivial.
    destruct H6 as [H6 | H6]; trivial.
    injection H6; intros; subst y; absurd (x = x); trivial.

(* 1/1 *)
    destruct H'' as [sigma' [H2 [H3 [H4 H5]]]].
    exists sigma'; split; [idtac | repeat split]; trivial.
    intros x val H''; rewrite H1 in H''; apply H3; trivial.
    intros x val H''; rewrite H1; apply H5 with val; trivial.
  Defined.

  Definition non_overlapping (R : relation term) := 
    forall l1 r1 l2 r2 sigma tau, R r1 l1 -> R r2 l2 -> 
      forall f l p, subterm_at_pos l1 p = Some (Term f l) ->
        apply_subst sigma (Term f l) = apply_subst tau l2 -> p = nil /\ l1 = l2 /\ r1 = r2.

  Definition overlay (R : relation term) := 
    forall l1 r1 l2 r2 sigma tau, R r1 l1 -> R r2 l2 -> 
      forall f l p, subterm_at_pos l1 p = Some (Term f l) ->
        apply_subst sigma (Term f l) = apply_subst tau l2 -> p = nil.

  Lemma well_formed_one_step : 
    forall (R : relation term), (forall s t, R s t -> forall x, In x (var_list s) -> In x (var_list t)) ->
      (forall r l, R r l -> well_formed r /\ well_formed l) -> 
      forall s t, one_step R t s -> well_formed s -> well_formed t.
  Proof.
    intros R R_reg WR t2 t1 H.
    revert t1 H; pattern t2; apply term_rec3; clear t2.
(* 1/3 variable case *)
    intros v2 t1 H _; inversion H as [t1' t2' H' | f l1 l2 H']; clear H.
    subst t1' t2'; inversion H' as [r l sigma H'']; clear H'.
    destruct l as [v | ]; [idtac | discriminate].
    apply well_formed_apply_subst_strong.
    intros x x_in_r; apply well_formed_remove_term with (Var v).
    rewrite H0; apply eq_refl.
    rewrite var_in_term_is_sound; apply R_reg with r.
    assumption.
    rewrite <- var_in_term_is_sound; assumption.
    apply (proj1 (WR _ _  H'')).
(* 1/2 compound term *)
    intros f l2 IHl2 t1 H Wfl2.
    inversion H as [t1' t2' H' | f' l1 l2' H']; clear H.
(* 1/3 rewrite at top *)
    subst t1' t2'; inversion H' as [r l sigma H'']; clear H'.
    subst t1.
    apply well_formed_apply_subst_strong.
    intros x x_in_r; apply well_formed_remove_term with l.
    rewrite H0; assumption.
    rewrite var_in_term_is_sound; apply R_reg with r.
    assumption.
    rewrite <- var_in_term_is_sound; assumption.
    apply (proj1 (WR _ _  H'')).
(* 1/2 rewrite in context *)
    subst t1 l2' f'.
    apply well_formed_fold; split.
    destruct (well_formed_unfold Wfl2) as [Wl2 _]; clear Wfl2.
    induction H' as [t1 t2 l H | t l1 l2 H].
    intros u [u_eq_t1 | u_in_l].
    apply IHl2 with t2.
    left; reflexivity.
    subst u; assumption.
    apply Wl2; left; reflexivity.
    apply Wl2; right; assumption.
    intros u [u_eq_t | u_in_l1].
    apply Wl2; left; assumption.
    apply IHH.
    intros t2 t2_in_l2 t1 H' Wt2; apply IHl2 with t2. 
    right; assumption.
    assumption.
    assumption.
    intros; apply Wl2; right; assumption.
    assumption.
    destruct (well_formed_unfold Wfl2) as [_ Af].
    rewrite (one_step_list_length_eq H').
    assumption.
  Qed.

  Lemma well_formed_rwr : 
    forall (R : relation term), (forall s t, R s t -> forall x, In x (var_list s) -> In x (var_list t)) ->
      (forall r l, R r l -> well_formed r /\ well_formed l) -> 
      forall s t, rwr R t s -> well_formed s -> well_formed t.
  Proof.
    intros R R_reg WR s t H; induction H as [t1 t2 H | t1 t2 t3 H1 H2].
(* 1/2 only one rewrite step *)
    apply well_formed_one_step with R; trivial.
(* 1/1 transitivity *)
    intro Wt3; apply well_formed_one_step with R t2; trivial.
    apply IHH2; assumption.
  Qed.

  Fixpoint map2 (A B C : Type) (f: A -> B -> C) (l1 : list A) (l2 : list B) : list C :=
    match l1, l2 with
      | nil, _ => nil
      | _, nil => nil
      | a :: l1, b :: l2 => (f a b) :: map2 _ _ _ f l1 l2
    end.

  Fixpoint maxl  (A : Type) (l  : list (nat * A)) : nat :=
    match l with
      | nil => 0
      | (n,_) :: l => Nat.max n (maxl _ l)
    end.

  Lemma maxl_is_max : forall (A : Type) l n a, In (n,a) l -> n <= maxl A l.
  Proof.
    fix maxl_is_max 2.
    intros A l; case l; clear l.
    intros; contradiction.
    simpl; intros na1 l.
    case na1; clear na1; intros n1 a1 n a [na_eq_na1 | na_in_l].
    injection na_eq_na1; intros; subst n1.
    apply Nat.le_max_l.
    apply Nat.le_trans with (maxl A l).
    apply maxl_is_max with a; assumption.
    apply Nat.le_max_r.
  Qed.

  Fixpoint maxll  (A : Type) (ll : list (list (nat * A))) : nat :=
    match ll with
      | nil => 0
      | l :: ll => Nat.max (maxl _ l) (maxll _ ll)
    end.

  Lemma maxll_is_max : forall (A : Type) ll l, In l ll -> forall n a, In (n,a) l -> n <= maxll A ll.
    fix maxll_is_max 2.
    intros A ll; case ll; clear ll.
    intros; contradiction.
    simpl; intros l1 ll.
    intros l [l_eq_l1 | l_in_ll] n a na_in_l.
    subst l; apply Nat.le_trans with (maxl A l1).
    apply maxl_is_max with a; assumption.
    apply Nat.le_max_l.
    apply Nat.le_trans with (maxll A ll).
    apply maxll_is_max with l a; assumption.
    apply Nat.le_max_r.
  Qed.

  Section Dec_well_formed.

    Variable R : relation term.
    Variable R_reg : forall s t, R s t -> forall x, In x (var_list s) -> In x (var_list t) .
    Variable R_var : forall v t, ~ R t (Var v).
    Variable WR : forall s t, R s t -> well_formed s /\ well_formed t.

    Variable inject : nat -> variable.
    Variable inject_inv : variable -> nat.
    Variable Hinject1 : forall v, inject (inject_inv v) = v.
    Variable Hinject2 : forall n, inject_inv (inject n) = n.

    Lemma Acc_var : forall x, Acc (one_step R) (Var x).
      intro x; apply Acc_intro; 
        intros s H; inversion H as [t1 t2 H' | f' l1 l2 H']; subst.
      inversion H' as [t1 t2 sigma H'' H3 H''']; subst; destruct t2 as [x2 | f2 l2].
      absurd (R t1 (Var x2)); trivial; apply HR.
      simpl in H'''; discriminate.
    Qed.

    Lemma find_inject : forall (A B : Type) v (f : (nat * A) -> B) sigma,
      find X.eq_bool v (map (fun xt => (inject (fst xt), f xt)) sigma) =
      find Nat.eqb (inject_inv v) (map (fun xt => (fst xt, f xt)) sigma).
    Proof.
      fix find_inject 5.
      intros C B v f sigma; case sigma; clear sigma.
      apply eq_refl.
      intros p l; case p; clear p.
      intros n c; simpl.
      destruct (eq_nat_dec (inject_inv v) n) as [v_eq_n | v_diff_n].
      subst n; rewrite Hinject1.
      generalize (X.eq_bool_ok v v); case (X.eq_bool v v); [intros _ | intro v_diff_v; apply False_rect; apply v_diff_v; apply eq_refl].
      rewrite Nat.eqb_refl; apply eq_refl.
      generalize (X.eq_bool_ok v (inject n)); case (X.eq_bool v (inject n)); [intro v_eq_n | intros _].
      subst v; apply False_rect; apply v_diff_n; rewrite Hinject2; apply eq_refl.
      generalize (decidable_set.beq_nat_ok (inject_inv v) n).
      case (Nat.eqb (inject_inv v) n); [intro v_eq_n | intros _].
      apply False_rect; apply v_diff_n; assumption.
      apply find_inject.
    Qed.

    Lemma subst_aux : 
      forall (sigma : substitution), (forall x u v, In (x,u) sigma -> In (x,v) sigma -> u = v) ->
        forall x u, In (x,u) sigma -> find X.eq_bool x sigma = Some u.
    Proof.
      intros sigma H x u xu_in_sig; case_eq (find X.eq_bool x sigma); [intros x_val x_sigma | intro x_sigma].
      apply f_equal; apply (H x); trivial.
      destruct (find_mem _ _ X.eq_bool_ok _ _ x_sigma) as [x' [sig1 [sig2 [x_eq_x' H']]]].
      subst x'; rewrite H'; apply in_or_app; right; left; apply eq_refl.
      apply False_rect; refine (find_not_found X.eq_bool _ x u sigma x_sigma (eq_var_bool_refl x) xu_in_sig).
    Qed.

    Lemma decompose_term_aux : 
      forall t sigma, 
        (forall x u, In (x,u) sigma -> 
          match u with
            | Var _ => True
            | Term f l => (match F.arity f with Free n => n | _ => 2 end) <> length l
          end) ->
        (forall x u v, In (x,u) sigma -> In (x,v) sigma -> u = v) ->
        (forall x y u, In (x,u) sigma -> In (y,u) sigma -> x = y) ->
        {s : term & {tau : substitution | 
          let sigma' := tau ++ sigma in
            t = apply_subst sigma' s /\ well_formed s /\ 
            (forall x u, In (x,u) sigma' -> 
              match u with
                | Var _ => True
                | Term f l => (match F.arity f with Free n => n | _ => 2 end) <> length l
              end) /\
            (forall x u v, In (x,u) sigma' -> In (x,v) sigma' -> u = v) /\
            (forall x y u, In (x,u) sigma' -> In (y,u) sigma' -> x = y) /\
            (forall x, In x (var_list s) -> In x (map (@fst _ _) sigma'))}}.
    Proof.
      intro t; pattern t; apply term_rec3; clear t.
(* 1/2 variable case *)
      intros v sigma h1 h2 h3.
      generalize (mem_bool_ok _ _ T.eq_bool_ok (Var v) (map (@snd _ _) sigma)).
      case (mem_bool T.eq_bool (Var v) (map (@snd _ _) sigma)); [intro v_in_sig | intro v_not_in_sig].
      destruct (mem_map_set _ _ T.eq_bool_ok  _ _ _ v_in_sig) as [[x u] [v_eq_u v_in_sig']].
      simpl in v_eq_u; subst u.
      exists (Var x); exists nil; split.
      simpl; rewrite (subst_aux sigma h2 _ _ v_in_sig'); trivial.
      split.
      apply eq_refl.
      split.
      apply h1.
      split.
      apply h2.
      split.
      apply h3.
      intros z [z_eq_x | z_in_nil]; [rewrite in_map_iff; exists (x,Var v); split; trivial | contradiction].
      set (m := (S (maxl _ (map (fun xt => (inject_inv (fst xt), snd xt)) sigma)))).
      exists (Var (inject m)); exists ((inject m, Var v ) :: nil).
      split.
      simpl.
      rewrite eq_var_bool_refl; apply eq_refl.
      split.
      apply eq_refl.
      split.
      simpl; intros x u [xu_eq_mv | xu_in_sigma].
      injection xu_eq_mv; intros; subst x u; trivial.
      apply (h1 x u xu_in_sigma).
      split.
      simpl.
      intros x u u' [xu_eq_mv | xu_in_sigma] [xu'_eq_mv | xu'_in_sigma].
      injection xu_eq_mv; injection xu'_eq_mv; intros; subst; trivial.
      injection xu_eq_mv; clear xu_eq_mv; intros; subst x u.
      absurd (m < m).
      auto with arith.
      apply le_n_S.
      apply (maxl_is_max _ (map
        (fun xt : T1.variable * T1.term => (inject_inv (fst xt), snd xt))
        sigma) m u').
      rewrite in_map_iff.
      exists (inject m, u'); split; trivial.
      simpl; rewrite Hinject2; trivial.
      injection xu'_eq_mv; clear xu'_eq_mv; intros; subst x u'.
      absurd (m < m).
      auto with arith.
      apply le_n_S.
      apply (maxl_is_max _ (map
        (fun xt : T1.variable * T1.term => (inject_inv (fst xt), snd xt))
        sigma) m u).
      rewrite in_map_iff.
      exists (inject m, u); split; trivial.
      simpl; rewrite Hinject2; trivial.
      apply (h2 x); trivial.
      split.
      simpl.
      intros x y u [xu_eq_mv | xu_in_sigma] [yu_eq_mv | yu_in_sigma].
      injection xu_eq_mv; injection yu_eq_mv; intros; subst; trivial.
      injection xu_eq_mv; clear xu_eq_mv; intros; subst x u.
      apply False_rect; apply v_not_in_sig; apply in_impl_mem.
      reflexivity.
      rewrite in_map_iff; exists (y, Var v); split; trivial.
      injection yu_eq_mv; clear yu_eq_mv; intros; subst y u.
      apply False_rect; apply v_not_in_sig; apply in_impl_mem.
      reflexivity.
      rewrite in_map_iff; exists (x, Var v); split; trivial.
      apply (h3 x y u); trivial.
      intros z [z_eq_m | z_in_nil].
      left; trivial.
      contradiction.
(* 1/1 compound term f l *)
      intros f l Hl sigma h1 h2 h3.
      generalize (mem_bool_ok _ _ T.eq_bool_ok (Term f l) (map (@snd _ _) sigma)).
      case (mem_bool T.eq_bool (Term f l) (map (@snd _ _) sigma)); [intro fl_in_sig | intro fl_not_in_sig].
(* 1/2 (f l) is in (snd sigma) *)
      destruct (mem_map_set _ _ T.eq_bool_ok  _ _ _ fl_in_sig) as [[x u] [fl_eq_u fl_in_sig']].
      simpl in fl_eq_u; subst u.
      exists (Var x); exists nil; split.
      simpl; rewrite (subst_aux sigma h2 _ _ fl_in_sig'); trivial.
      split.
      apply eq_refl.
      split.
      apply h1.
      split.
      apply h2.
      split.
      apply h3.
      intros z [z_eq_x | z_in_nil]; [rewrite in_map_iff; exists (x,Term f l); split; trivial | contradiction].
      destruct (eq_nat_dec (length l) (match F.arity f with Free n => n | _ => 2 end)) as [Wf | not_Wf].
      assert (Aux :
        {ls : list T1.term & 
          {tau : T1.substitution |
            let sigma' := tau ++ sigma in
              l = map (T1.apply_subst sigma') ls /\
              (forall si, In si ls -> well_formed si) /\
              (forall (x : T1.variable) (u : T1.term),
                In (x, u) sigma' ->
                match u with
                  | T1.Var _ => True
                  | T1.Term f0 l0 =>
                    match T1.F.arity f0 with
                      | AC => 2
                      | C => 2
                      | Free n => n
                    end <> length l0
                end) /\
              (forall (x : T1.variable) (u v : T1.term),
                In (x, u) sigma' -> In (x, v) sigma' -> u = v) /\
              (forall (x y : T1.variable) (u : T1.term),
                In (x, u) sigma' -> In (y, u) sigma' -> x = y) /\
              (forall x : T1.variable, In x (T1.var_list_list ls) -> In x (map (@fst _ _) sigma'))}}).
      clear f fl_not_in_sig Wf.
      revert sigma h1 h2 h3; induction l as [ | t l]; intros sigma h1 h2 h3.
      exists nil; exists nil; repeat split; trivial.
      intros; contradiction.
      intros; contradiction.
      destruct IHl with sigma as [ls [tau [H0 [Wls [H1 [H2 [H3 H4]]]]]]]; trivial.
      apply (tail_set _ Hl).
      destruct (Hl t (or_introl _ (eq_refl _)) (tau ++ sigma) H1 H2 H3) as [s [tau' [K0 [Ws [K1 [K2 [K3 K4]]]]]]].
      exists (s :: ls); exists (tau' ++ tau); rewrite <- app_assoc; repeat split; trivial.
      simpl; apply f_equal2.
      assumption.
      rewrite H0.
      apply map_eq.
      intros u u_in_ls; rewrite <- subst_eq_vars.
      intros v v_in_u.
      simpl; rewrite (find_app X.eq_bool v tau' (tau ++ sigma)).
      generalize (mem_bool_ok _ _ X.eq_bool_ok v (map (fun st : T1.variable * T1.term => fst st) tau')).
      case (mem_bool X.eq_bool v (map (fun st : T1.variable * T1.term => fst st) tau'));
        [intro v_in_tau' | intro v_not_in_tau']; trivial. 
      case_eq (find X.eq_bool v tau'); [intros v_val v_tau' | intro v_tau'].
      case_eq (find X.eq_bool v (tau ++ sigma)); [intros v_val' v_tau | intro v_tau].
      apply (K2 v).
      apply in_or_app; right.
      destruct (find_mem _ _ X.eq_bool_ok _ _ v_tau) as [v' [tau1 [tau2 [v_eq_v' H]]]].
      subst v'; rewrite H; apply in_or_app; right; left; apply eq_refl.
      apply in_or_app; left.
      destruct (find_mem _ _ X.eq_bool_ok _ _ v_tau') as [v' [tau1 [tau2 [v_eq_v' H]]]].
      subst v'; rewrite H; apply in_or_app; right; left; apply eq_refl.
      assert (H : In v (map (@fst _ _) (tau ++ sigma))).
      apply H4.
      destruct (in_split _ _ u_in_ls) as [ls1 [ls2 H]]; rewrite H.
      rewrite var_list_list_app; apply in_or_app; right.
      simpl; apply in_or_app; left; assumption.
      rewrite in_map_iff in H; destruct H as [[v' u'] [v_eq_v' H]]; simpl in v_eq_v'; subst v'.
      apply False_rect.
      apply (find_not_found X.eq_bool v v u' (tau ++ sigma) v_tau (eq_var_bool_refl v) H).
      destruct (mem_map_set _ _ X.eq_bool_ok  _ v tau' v_in_tau') as [[v' u'] [v_eq_v' v_in_tau'']]; simpl in v_eq_v'; subst v'.
      apply False_rect.
      apply (find_not_found X.eq_bool v v u' tau' v_tau' (eq_var_bool_refl v) v_in_tau'').
      simpl; intros si [si_eq_s | si_in_ls]; [subst; assumption | apply Wls; assumption].
      simpl; intros v v_in_sls; destruct (in_app_or _ _ _ v_in_sls) as [v_in_s | v_in_ls]; clear v_in_sls.
      apply K4; assumption.
      rewrite map_app; apply in_or_app; right; apply H4; assumption.
      destruct Aux as [ls [tau [H0 [Wls [H1 [H2 [H3 H4]]]]]]].
      exists (Term f ls); exists tau; repeat split; trivial.
      simpl; apply f_equal; assumption.
      apply well_formed_fold; split.
      exact Wls.
      rewrite H0 in Wf; rewrite length_map in Wf; destruct (F.arity f); assumption.
      set (m := (S (maxl _ (map (fun xt => (inject_inv (fst xt), snd xt)) sigma)))).
      exists (Var (inject m)); exists ((inject m, Term f l ) :: nil).
      split.
      simpl; rewrite eq_var_bool_refl; apply eq_refl.
      split.
      apply eq_refl.
      split.
      simpl; intros x u [xu_eq_mv | xu_in_sigma].
      injection xu_eq_mv; intros; subst x u.
      intro L; apply not_Wf; apply sym_eq; assumption.
      apply (h1 x u xu_in_sigma).
      split.
      simpl.
      intros x u u' [xu_eq_mv | xu_in_sigma] [xu'_eq_mv | xu'_in_sigma].
      injection xu_eq_mv; injection xu'_eq_mv; intros; subst; trivial.
      injection xu_eq_mv; clear xu_eq_mv; intros; subst x u.
      absurd (m < m).
      auto with arith.
      apply le_n_S.
      apply (maxl_is_max _ (map
        (fun xt : T1.variable * T1.term => (inject_inv (fst xt), snd xt))
        sigma) m u').
      rewrite in_map_iff.
      exists (inject m, u'); split; trivial.
      simpl; rewrite Hinject2; trivial.
      injection xu'_eq_mv; clear xu'_eq_mv; intros; subst x u'.
      absurd (m < m).
      auto with arith.
      apply le_n_S.
      apply (maxl_is_max _ (map
        (fun xt : T1.variable * T1.term => (inject_inv (fst xt), snd xt))
        sigma) m u).
      rewrite in_map_iff.
      exists (inject m, u); split; trivial.
      simpl; rewrite Hinject2; trivial.
      apply (h2 x); trivial.
      split.
      simpl.
      intros x y u [xu_eq_mv | xu_in_sigma] [yu_eq_mv | yu_in_sigma].
      injection xu_eq_mv; injection yu_eq_mv; intros; subst; trivial.
      injection xu_eq_mv; clear xu_eq_mv; intros; subst x u.
      apply False_rect; apply fl_not_in_sig; apply in_impl_mem.
      reflexivity.
      rewrite in_map_iff; exists (y, Term f l); split; trivial.
      injection yu_eq_mv; clear yu_eq_mv; intros; subst y u.
      apply False_rect; apply fl_not_in_sig; apply in_impl_mem.
      reflexivity.
      rewrite in_map_iff; exists (x, Term f l); split; trivial.
      apply (h3 x y u); trivial.
      intros z [z_eq_m | z_in_nil].
      left; trivial.
      contradiction.
    Qed.

    Lemma decompose_term : 
      forall t, 
        {s : term & {sigma : substitution | 
          t = apply_subst sigma s /\ well_formed s /\ 
          (forall x u, In (x,u) sigma -> 
            match u with
              | Var _ => True
              | Term f l => (match F.arity f with Free n => n | _ => 2 end) <> length l
            end) /\
          (forall x u v, In (x,u) sigma -> In (x,v) sigma -> u = v) /\
          (forall x y u, In (x,u) sigma -> In (y,u) sigma -> x = y) /\
          (forall x, In x (var_list s) <-> In x (map (@fst _ _) sigma))}}.
    Proof.
      intro t;
        destruct (decompose_term_aux t nil) as [s [sigma [H0 [Ws [H1 [H2 [H3 H4]]]]]]].
      intros; contradiction.
      intros; contradiction.
      intros; contradiction.
      exists s; exists (subst_rest (var_list s) sigma); repeat split; trivial.
(* H0 *)
      rewrite H0; rewrite app_nil_r.
      rewrite <- subst_eq_vars; intros v v_in_s.
      rewrite subst_rest_ok; trivial.
(* H1 *)
      intros x u xu_in_rest_sig; apply (H1 x u); rewrite app_nil_r; apply (subst_rest_subst _ _ _ _ xu_in_rest_sig). 
(* H2 *)
      intros x u v xu_in_rest_sig xv_in_rest_sig; apply (H2 x u v); rewrite app_nil_r.
      apply (subst_rest_subst _ _ _ _ xu_in_rest_sig). 
      apply (subst_rest_subst _ _ _ _ xv_in_rest_sig). 
(* H3 *)
      intros x y u xu_in_rest_sig yu_in_rest_sig; apply (H3 x y u); rewrite app_nil_r.
      apply (subst_rest_subst _ _ _ _ xu_in_rest_sig). 
      apply (subst_rest_subst _ _ _ _ yu_in_rest_sig). 
(* H4 *)
      intros x_in_s; generalize (H4 _ x_in_s); rewrite app_nil_r.
      do 2 rewrite in_map_iff.
      intros [[x' u] [x_eq_x' x_in_sig]]; simpl in x_eq_x'; subst x'.
      exists (x,u); split; trivial.
      apply subst_rest_subst_rest; trivial.
      intro x_in_sig; rewrite in_map_iff in x_in_sig.
      destruct x_in_sig as [[x' u] [x_eq_x' x_in_sig]]; simpl in x_eq_x'; subst x'.
      apply subst_rest_rest with sigma u; trivial.
    Qed.

    Lemma decompose_subst_aux :
      forall s1 s2 sigma, well_formed s1 -> well_formed s2->
        (forall x u, In (x,u) sigma -> 
          match u with
            | Var _ => True
            | Term f l => (match F.arity f with Free n => n | _ => 2 end) <> length l
          end) ->
        (forall x u v, In (x,u) sigma -> In (x,v) sigma -> u = v) ->
        (forall x y u, In (x,u) sigma -> In (y,u) sigma -> x = y) ->
        (forall x, In x (var_list s1) -> In x (map (@fst _ _) sigma)) ->
        (forall x, In x (var_list s2) -> In x (map (@fst _ _) sigma)) ->
        apply_subst sigma s1 = apply_subst sigma s2 -> s1 = s2.
    Proof.
      intro s1; pattern s1; apply term_rec3; clear s1.
(* 1/2 s1 is a variable *)
      intros v1 [v2 | f2 l2] sigma W1 W2 H1 H2 H3 H41 H42 H0.
      apply f_equal; apply H3 with (apply_subst sigma (Var v1)).
      assert (v1_in_sig : In v1 (map (@fst _ _) sigma)).
      apply H41; left; apply eq_refl.
      rewrite in_map_iff in v1_in_sig; destruct v1_in_sig as [[v1' u1] [v1_eq_v1' v1_in_sig]]; simpl in v1_eq_v1'; subst v1'.
      simpl; rewrite (subst_aux _ H2 _ _ v1_in_sig); assumption.
      rewrite H0; assert (v2_in_sig : In v2 (map (@fst _ _) sigma)).
      apply H42; left; apply eq_refl.
      rewrite in_map_iff in v2_in_sig; destruct v2_in_sig as [[v2' u1] [v2_eq_v2' v2_in_sig]]; simpl in v2_eq_v2'; subst v2'.
      simpl; rewrite (subst_aux _ H2 _ _ v2_in_sig); assumption.
      assert (v1_in_sig : In v1 (map (@fst _ _) sigma)).
      apply H41; left; apply eq_refl.
      rewrite in_map_iff in v1_in_sig; destruct v1_in_sig as [[v1' u1] [v1_eq_v1' v1_in_sig]]; simpl in v1_eq_v1'; subst v1'.
      simpl in H0; rewrite (subst_aux _ H2 _ _ v1_in_sig) in H0.
      destruct u1 as [x1 | g1 k1].
      discriminate.
      apply False_rect; apply (H1 _ _ v1_in_sig).
      injection H0; clear H0; do 2 intro; subst g1 k1; rewrite length_map; apply sym_eq.
      destruct (well_formed_unfold W2) as [_ L2]; destruct (F.arity f2); assumption.
(* 1/1 s1 is a compound term *)
      intros f1 l1 Hl1 [v2 | f2 l2] sigma W1 W2 H1 H2 H3 H41 H42 H0.
      assert (v2_in_sig : In v2 (map (@fst _ _) sigma)).
      apply H42; left; apply eq_refl.
      rewrite in_map_iff in v2_in_sig; destruct v2_in_sig as [[v2' u2] [v2_eq_v2' v2_in_sig]]; simpl in v2_eq_v2'; subst v2'.
      simpl in H0; rewrite (subst_aux _ H2 _ _ v2_in_sig) in H0.
      destruct u2 as [x2 | g2 k2].
      discriminate.
      apply False_rect; apply (H1 _ _ v2_in_sig).
      injection H0; clear H0; do 2 intro; subst g2 k2; rewrite length_map; apply sym_eq.
      destruct (well_formed_unfold W1) as [_ L1]; destruct (F.arity f1); assumption.
      simpl in H0; injection H0; clear H0; intro H0; intro; subst f2; apply f_equal.
      rewrite var_list_unfold in H41, H42.
      destruct (well_formed_unfold W1) as [Wl1 _]; clear W1.
      destruct (well_formed_unfold W2) as [Wl2 _]; clear W2.
      revert l2 sigma Wl1 Wl2 H1 H2 H3 H41 H42 H0.
      induction l1 as [ | t1 l1]; intros [ | t2 l2] sigma Wl1 Wl2 H1 H2 H3 H41 H42 H0.
      apply eq_refl.
      discriminate.
      discriminate.
      simpl in H0; injection H0; clear H0; intros H0 h0.
      rewrite (Hl1 t1 (or_introl _ (eq_refl _)) t2 sigma); trivial.
      apply f_equal; rewrite (IHl1 (tail_prop _ Hl1) l2 sigma); trivial.
      intros u u_in_l1; apply Wl1; right; assumption.
      intros u u_in_l2; apply Wl2; right; assumption.
      intros v v_in_l1; apply H41; apply in_or_app; right; assumption.
      intros v v_in_l2; apply H42; apply in_or_app; right; assumption.
      apply Wl1; left; apply eq_refl.
      apply Wl2; left; apply eq_refl.
      intros v v_in_t1; apply H41; apply in_or_app; left; assumption.
      intros v v_in_t2; apply H42; apply in_or_app; left; assumption.
    Qed.

    Lemma decompose_subst :
      forall s sigma t tau, 
        well_formed s ->
        (forall x u, In (x,u) sigma -> 
          match u with
            | Var _ => True
            | Term f l => (match F.arity f with Free n => n | _ => 2 end) <> length l
          end) ->
        (forall x u v, In (x,u) sigma -> In (x,v) sigma -> u = v) ->
        (forall x y u, In (x,u) sigma -> In (y,u) sigma -> x = y) ->
        (forall x, In x (var_list s) <-> In x (map (@fst _ _) sigma)) ->
        well_formed t ->
        apply_subst tau t = apply_subst sigma s ->
        {phi : substitution | (forall v, In v (var_list t) ->
          apply_subst (subst_comp sigma phi) (Var v) = apply_subst tau (Var v)) /\
        apply_subst phi t = s /\
        (forall v, In v (map (@fst _ _) phi) <-> In v (var_list t)) /\
        well_formed_subst phi}.
    Proof.
      intros s sigma t tau Ws H1 H2 H3 H4 Wt H0;
        assert (Aux : forall v p, subterm_at_pos t p = Some (Var v) -> 
          {v_val : term | subterm_at_pos s p = Some v_val /\ apply_subst sigma v_val = apply_subst tau (Var v)}).
      revert sigma t tau Ws H1 H2 H3 H4 Wt H0.
      pattern s; apply term_rec3; clear s.
(* 1/3 variable case *)
      intros v sigma t tau Ws H1 H2 H3 H4 Wt H0; simpl in H0; revert H0.
      assert (v_in_sig : In v (map (@fst _ _) sigma)).
      rewrite <- H4; left; apply eq_refl.
      destruct (mem_map_set _ _ X.eq_bool_ok (@fst _ _) v sigma) as [[v' v_val] [v_eq_v' v_in_sig']].
      apply in_impl_mem; [reflexivity | assumption].
      simpl in v_eq_v'; subst v'.
      rewrite (subst_aux _ H2 _ _ v_in_sig').
      generalize (H1 _ _ v_in_sig'); destruct v_val as [x | f l].
      intros _; destruct t as [y | ]; [idtac | intro; discriminate].
      intros H0 x' [ | i p]; [idtac | intro; discriminate].
      intro H; injection H; clear H; intro H; subst x'.
      exists (Var v); split.
      apply eq_refl.
      rewrite H0; simpl; rewrite (subst_aux _ H2 _ _ v_in_sig'); apply eq_refl.
      intros L; destruct t as [y | g k].
      intros H0 x' [ | i p]; [idtac | intro; discriminate].
      intro H; injection H; clear H; intro H; subst x'.
      exists (Var v); split.
      apply eq_refl.
      rewrite H0; simpl; rewrite (subst_aux _ H2 _ _ v_in_sig'); apply eq_refl.
      intro H0; injection H0; clear H0; do 2 intro; subst g l.
      apply False_rect; apply L; rewrite length_map; apply sym_eq.
      destruct (well_formed_unfold Wt) as [_ L']; destruct (F.arity f); assumption.
(* 1/2 coumpound term *)
      intros f ls Hls sigma t tau Ws H1 H2 H3 H4 Wt.
      destruct t as [y | g lt].
      intros H0 x' [ | i p]; [idtac | intro; discriminate].
      intro H; injection H; clear H; intro H; subst x'.
      exists (Term f ls); split.
      apply eq_refl.
      apply sym_eq; assumption.
      intro H0; injection H0; clear H0; intros H0 H0'; subst g.
      intros x [ | i p] Sub.
      discriminate.
      simpl in Sub.
      generalize (nth_error_ok_in i lt).
      destruct (nth_error lt i) as [ti | ]; [intros H; destruct (H _ (eq_refl _)) as [lt1 [lt2 [L H']]]; clear H | discriminate].
      rewrite H' in H0; rewrite map_app in H0.
      destruct (split_map_set _ _ _ _ (sym_eq  H0)) as [ls1 [ls2 [h1 [h2 h3]]]].
      destruct ls2 as [ | si ls2].
      discriminate.
      assert (si_in_ls : In si ls).
      rewrite h1; apply in_or_app; right; left; apply eq_refl.
      destruct (Hls _ si_in_ls (subst_rest (var_list si) sigma) ti tau) with x p as [v_val [Sub' Sub'']].
      destruct (well_formed_unfold Ws) as [Wls _]; apply Wls; trivial.
      intros y u yu_in_rest_sig; apply (H1 y); apply subst_rest_subst  with (var_list si); trivial.
      intros y u v yu_in_rest_sig yv_in_rest_sig; apply (H2 y u v).
      apply (subst_rest_subst _ _ _ _ yu_in_rest_sig). 
      apply (subst_rest_subst _ _ _ _ yv_in_rest_sig). 
      intros y z u yu_in_rest_sig zu_in_rest_sig; apply (H3 y z u).
      apply (subst_rest_subst _ _ _ _ yu_in_rest_sig).
      apply (subst_rest_subst _ _ _ _ zu_in_rest_sig). 
      intros y; split.
      intro y_in_si.
      assert (y_in_sig : In y (map (@fst _ _) sigma)).
      rewrite <- H4; rewrite h1.
      rewrite var_list_unfold; rewrite var_list_list_app; apply in_or_app; right; apply in_or_app; left; assumption.
      rewrite in_map_iff in y_in_sig; destruct y_in_sig as [[y' u] [y_eq_y' y_in_sig]]; simpl in y_eq_y'; subst y'.
      rewrite in_map_iff; exists (y,u); split; trivial.
      apply subst_rest_subst_rest; trivial.
      intro y_in_rest_subst; rewrite in_map_iff in y_in_rest_subst; 
        destruct y_in_rest_subst as [[y' u] [y_eq_y' y_in_rest_subst]]; simpl in y_eq_y'; subst y'.
      apply subst_rest_rest with sigma u; trivial.
      destruct (well_formed_unfold Wt) as [Wlt _]; apply Wlt; rewrite H'; apply in_or_app; right; left; apply eq_refl.
      injection h3; clear h3; intros _ h3; rewrite <- h3.
      rewrite <- subst_eq_vars; intros z z_in_si; rewrite subst_rest_ok; trivial.
      assumption.
      exists v_val; split.
      simpl; rewrite h1; subst i; replace (length lt1) with (length ls1).
      rewrite nth_error_at_pos; assumption.
      rewrite <- (length_map (apply_subst sigma) ls1).
      rewrite <- (length_map (apply_subst tau) lt1).
      apply f_equal; assumption.
      rewrite <- Sub''; rewrite <- subst_eq_vars; intros v v_in_val.
      rewrite subst_rest_ok; trivial.
      apply var_in_subterm with v_val p; trivial.
      assert (Aux2 : forall v, mem (@eq _) v (var_list t) -> {v_val : term | 
        apply_subst sigma v_val = apply_subst tau (Var v) /\
        (forall p, subterm_at_pos t p = Some (Var v) ->
          subterm_at_pos s p = Some v_val) /\
        well_formed v_val}).
      intros v v_in_t.
      destruct (var_in_subterm2 _ _ v_in_t) as [p Sub].
      destruct (Aux v p Sub) as [v_val [Sub' H]].
      exists v_val; split; trivial.
      split.
      intros q Subq.
      destruct (Aux _ _ Subq) as [v_val' [Sub'' H']].
      rewrite Sub''; apply f_equal.
      apply decompose_subst_aux with sigma; trivial.
      apply (well_formed_subterm q Ws Sub'').
      apply (well_formed_subterm p Ws Sub').
      intros x x_in_v_val'; rewrite <- H4.
      apply var_in_subterm with v_val' q; trivial.
      intros x x_in_v_val; rewrite <- H4.
      apply var_in_subterm with v_val p; trivial.
      rewrite H; assumption.
      apply (well_formed_subterm p Ws Sub').
      clear Aux.
      revert Wt s Ws sigma tau H0 H1 H2 H3 H4 Aux2; pattern t; apply term_rec3; clear t.
(* 1/2 t is a variable *)
      intros v _ s Ws sigma tau H0 H1 H2 H3 H4 Aux2.
      destruct (Aux2 v) as [v_val [K1 [K2 K3]]].
      left; apply eq_refl.
      exists ((v,v_val) :: nil); split.
      intros z [z_eq_v | z_in_nil]; [subst z | contradiction].
      rewrite subst_comp_is_subst_comp; simpl; rewrite eq_var_bool_refl; rewrite K1; trivial.
      split.
      simpl; simpl; rewrite eq_var_bool_refl.
      assert (K2' := K2 nil (eq_refl _)); injection K2'; intros; apply sym_eq; assumption.
      split.
      intros z; split; intro H; assumption.
      unfold well_formed_subst; simpl.
      intro z; generalize (X.eq_bool_ok z v); case (X.eq_bool z v); [intro z_eq_v | intro z_diff_v]; trivial.
(* 1/1 t is coumpound term *)
      intros f lt Hlt Wt s Ws sigma tau H0 H1 H2 H3 H4 Aux2.
      destruct s as [x | g ls].
(* 1/2 s is a variable *)
      apply False_rect.
      destruct (well_formed_unfold Wt) as [_ L].
      assert (x_in_sig : In x (map (@fst _ _) sigma)).
      rewrite <- H4; left; apply eq_refl.
      rewrite in_map_iff in x_in_sig; destruct x_in_sig as [[x' u] [x_eq_x' x_in_sig]]; simpl in x_eq_x'; subst x'.
      simpl in H0; rewrite (subst_aux _ H2 _ _ x_in_sig) in H0; subst u.
      apply (H1 _ _ x_in_sig); apply sym_eq; rewrite length_map; destruct (F.arity f); assumption.
(* 1/1 s is a compound term *)
      simpl in H0; injection H0; clear H0; intros H0 h0; subst g.
      rewrite var_list_unfold in *.
      destruct (well_formed_unfold Wt) as [Wlt _]; clear Wt.
      destruct (well_formed_unfold Ws) as [Wls _]; clear Ws.
      revert Wlt ls Wls sigma H0 H1 H2 H3 H4 Aux2; induction lt as [ | t lt]; intros Wlt ls Wls sigma H0 H1 H2 H3 H4 Aux2.
      destruct ls as [ | s ls]; [idtac | discriminate].
      exists nil; repeat split.
      intros; contradiction.
      intro; assumption.
      intro; assumption.
      destruct ls as [ | s ls]; [discriminate | idtac].
      injection H0; clear H0; intros H0 h0.
(* applying the induction hypothesis in lt *)
      destruct (Hlt t (or_introl _ (eq_refl _)) (Wlt t (or_introl _ (eq_refl _)))
        s (Wls s (or_introl _ (eq_refl _))) (subst_rest (var_list s) sigma)) with tau as [phi [k1 [k2 [k3 k4]]]]; trivial.
      rewrite h0; rewrite <- subst_eq_vars; intros x x_in_s; rewrite subst_rest_ok; trivial.
      intros x u xu_in_rest_sig; apply (H1 x u); apply subst_rest_subst with (var_list s); trivial.
      intros x u v xu_in_rest_sig xv_in_rest_sig; apply (H2 x u v); apply subst_rest_subst with (var_list s); trivial.
      intros x y u xu_in_rest_sig yu_in_rest_sig; apply (H3 x y u); apply subst_rest_subst with (var_list s); trivial.
      intro x; split.
      intro x_in_s; assert (x_in_sig : In x (map (@fst _ _) sigma)).
      rewrite <- H4; simpl; apply in_or_app; left; assumption.
      rewrite in_map_iff in x_in_sig; destruct x_in_sig as [[x' u] [x_eq_x' x_in_sig]]; simpl in x_eq_x'; subst x'.
      rewrite in_map_iff; exists (x,u); split; trivial.
      apply subst_rest_subst_rest; trivial.
      intro x_in_rest_sig; rewrite in_map_iff in x_in_rest_sig; destruct x_in_rest_sig as [[x' u] [x_eq_x' x_in_rest_sig]]; simpl in x_eq_x'; subst x'.
      apply subst_rest_rest with sigma u; trivial.
      intros v v_in_t; destruct (Aux2 v) as [v_val [K1 [K2 K3]]].
      simpl; rewrite <- mem_or_app; left; assumption.
      exists v_val; split.
      rewrite <- K1; rewrite <- subst_eq_vars; intros x z_in_val.
      rewrite subst_rest_ok; trivial.
      destruct (var_in_subterm2 _ _ v_in_t) as [p Sub].
      apply var_in_subterm with v_val p; trivial.
      apply (K2 (0 :: p)); trivial.
      split; trivial.
      intros p Sub; apply (K2 (0 :: p)); trivial.
(* applying the induction hypothesis on t *)
      destruct (IHlt (tail_set _ Hlt))  with ls (subst_rest (var_list_list ls) sigma)as [Phi [K1 [K2 [K3 K4]]]]; trivial.
      intros; apply Wlt; right; trivial.
      intros; apply Wls; right; trivial.
      rewrite H0; apply map_eq.
      intros si si_in_ls; rewrite <- subst_eq_vars; intros x x_in_si; rewrite subst_rest_ok; trivial.
      destruct (in_split _ _ si_in_ls) as [ls1 [ls2 H]]; rewrite H; rewrite var_list_list_app; apply in_or_app; right;
        simpl; apply in_or_app; left; assumption.
      intros x u xu_in_rest_sig; apply (H1 x u); apply subst_rest_subst with (var_list_list ls); trivial.
      intros x u v xu_in_rest_sig xv_in_rest_sig; apply (H2 x u v); apply subst_rest_subst with (var_list_list ls); trivial.
      intros x y u xu_in_rest_sig yu_in_rest_sig; apply (H3 x y u); apply subst_rest_subst with (var_list_list ls); trivial.
      intro x; split.
      intro x_in_ls; assert (x_in_sig : In x (map (@fst _ _) sigma)).
      rewrite <- H4; simpl; apply in_or_app; right; assumption.
      rewrite in_map_iff in x_in_sig; destruct x_in_sig as [[x' u] [x_eq_x' x_in_sig]]; simpl in x_eq_x'; subst x'.
      rewrite in_map_iff; exists (x,u); split; trivial.
      apply subst_rest_subst_rest; trivial.
      intro x_in_rest_sig; rewrite in_map_iff in x_in_rest_sig; destruct x_in_rest_sig as [[x' u] [x_eq_x' x_in_rest_sig]]; simpl in x_eq_x'; subst x'.
      apply subst_rest_rest with sigma u; trivial.
      intros v v_in_lt; destruct (Aux2 v) as [v_val [K1 [K2 K3]]].
      simpl; rewrite <- mem_or_app; right; assumption.
      exists v_val; split.
      rewrite <- K1; rewrite <- subst_eq_vars; intros x z_in_val.
      rewrite subst_rest_ok; trivial.
      destruct (mem_var_list_list _ _ v_in_lt) as [ti [ti_in_lt v_in_ti]].
      destruct (var_in_subterm2 _ _ v_in_ti) as [p Sub].
      destruct (in_split _ _ ti_in_lt) as [lt1 [lt2 Ht]].
      rewrite Ht in H0; rewrite map_app in H0.
      destruct (split_map_set _ _ _ _ (sym_eq H0)) as [ls1 [ls2 [Hs [Hs1 Hs2]]]].
      destruct ls2 as [ | si ls2].
      discriminate.
      rewrite Hs; rewrite var_list_list_app; apply in_or_app; right; simpl; apply in_or_app; left.
      apply var_in_subterm with v_val p; trivial.
      subst lt ls.
      generalize (K2 ((1 + length lt1) :: p)); simpl.
      rewrite nth_error_at_pos.
      intro K2'; generalize (K2' Sub); clear K2'.
      replace (length lt1) with (length ls1).
      rewrite nth_error_at_pos; intro; assumption.
      rewrite <- (length_map (apply_subst sigma) ls1).
      rewrite Hs1; rewrite length_map; apply eq_refl.
      split; trivial.
      intros [ | i p].
      intro; discriminate.
      generalize (K2 ((S i) :: p)); simpl; trivial.
(* glueing the pieces *)
      assert (u_in_s : forall x u, find X.eq_bool x phi = Some u -> forall x0 : T1.variable, In x0 (T1.var_list u) -> In x0 (var_list s)).
      intros x u x_phi.
      intros z z_in_u.
      assert (x_in_t : In x (var_list t)).
      rewrite <- k3; rewrite in_map_iff; exists (x,u); split; trivial.
      destruct (find_mem _ _ X.eq_bool_ok _ phi x_phi) as [x' [phi1 [phi2 [x_eq_x' H]]]]; subst x'.
      rewrite H; apply in_or_app; right; left; apply eq_refl.
      rewrite <- k2.
      destruct (var_in_subterm2 _ _ (in_impl_mem (@eq _) (fun a => eq_refl a) _ _ x_in_t)) as [p Sub].
      apply var_in_subterm with u p; trivial.
      generalize (subterm_at_pos_apply_subst_apply_subst_subterm_at_pos t p phi).
      rewrite Sub; intro H; rewrite H; apply f_equal; simpl; rewrite x_phi; apply eq_refl.
      assert (v_in_ls : forall x v, find X.eq_bool x Phi = Some v -> forall x0 : T1.variable, In x0 (T1.var_list v) -> In x0 (var_list_list ls)).
      intros x v x_Phi.
      intros z z_in_v.
      assert (x_in_lt : In x (var_list_list lt)).
      rewrite <- K3; rewrite in_map_iff; exists (x,v); split; trivial.
      destruct (find_mem _ _ X.eq_bool_ok _ Phi x_Phi) as [x' [Phi1 [Phi2 [x_eq_x' H]]]]; subst x'.
      rewrite H; apply in_or_app; right; left; apply eq_refl.
      injection K2; clear K2; intro K2; rewrite <- K2.
      destruct (in_var_list_list _ _ x_in_lt) as [ti [ti_in_lt x_in_ti]].
      destruct (in_split _ _ ti_in_lt) as [lt1 [lt2 H]]; rewrite H.
      simpl; rewrite map_app; rewrite var_list_list_app; apply in_or_app; right.
      simpl; apply in_or_app; left.
      destruct (var_in_subterm2 _ _ (in_impl_mem (@eq _) (fun a => eq_refl a) _ _ x_in_ti)) as [p Sub].
      apply var_in_subterm with (apply_subst Phi (Var x)) p.
      generalize (subterm_at_pos_apply_subst_apply_subst_subterm_at_pos ti p Phi).
      rewrite Sub; intro H'; rewrite H'; apply f_equal; simpl; rewrite x_Phi; apply eq_refl.
      simpl; rewrite x_Phi; trivial.
      assert (ok : forall x u v, find X.eq_bool x phi = Some u -> find X.eq_bool x Phi = Some v -> u = v).
      intros x u v x_phi x_Phi.
      apply decompose_subst_aux with sigma; trivial.
      generalize (k4 x); rewrite x_phi; trivial.
      generalize (K4 x); rewrite x_Phi; trivial.
      intros z z_in_u; rewrite <- H4; simpl; apply in_or_app; left; apply u_in_s with x u; assumption.
      intros z z_in_v; rewrite <- H4; simpl; apply in_or_app; right; apply v_in_ls with x v; assumption.
      apply trans_eq with (apply_subst tau (Var x)).
      rewrite <- k1.
      rewrite subst_comp_is_subst_comp; simpl; rewrite x_phi.
      rewrite <- subst_eq_vars; intros z z_in_u; rewrite subst_rest_ok; trivial.
      apply u_in_s with x u; assumption.
      rewrite <- k3; rewrite in_map_iff; exists (x,u); split; trivial.
      destruct (find_mem _ _ X.eq_bool_ok _ phi x_phi) as [x' [phi1 [phi2 [x_eq_x' H]]]]; subst x'.
      rewrite H; apply in_or_app; right; left; apply eq_refl.
      rewrite <- K1.
      rewrite subst_comp_is_subst_comp; simpl; rewrite x_Phi.
      rewrite <- subst_eq_vars; intros z z_in_v; rewrite subst_rest_ok; trivial.
      apply v_in_ls with x v; assumption.
      rewrite <- K3; rewrite in_map_iff; exists (x,v); split; trivial.
      destruct (find_mem _ _ X.eq_bool_ok _ _ x_Phi) as [x' [Phi1 [Phi2 [x_eq_x' H]]]]; subst x';
        rewrite H; apply in_or_app; right; left; apply eq_refl.
(* MAIN PROOF *)
      exists (phi ++ Phi); split.
      simpl var_list_list; intros v v_in_tlt; destruct (in_app_or _ _ _ v_in_tlt) as [v_in_t | v_in_lt]; clear v_in_tlt.
      rewrite <- k1.
      do 2 rewrite subst_comp_is_subst_comp.
      simpl; rewrite find_app.
      generalize (mem_bool_ok _ _ X.eq_bool_ok v (map (fun st : T1.variable * T1.term => fst st) phi)).
      case (mem_bool X.eq_bool v (map (fun st : T1.variable * T1.term => fst st) phi)); [intro v_in_phi | intro v_not_in_phi].
      case_eq (find X.eq_bool v phi); [intros v_val v_phi | intro v_phi].
      rewrite <- subst_eq_vars; intros z z_in_v.
      rewrite subst_rest_ok; trivial.
      apply u_in_s with v v_val; trivial.
      assert (v_in_phi' : In v (map (fun st : T1.variable * T1.term => fst st) phi)).
      apply mem_impl_in with (@eq _); trivial.
      apply False_rect.
      rewrite in_map_iff in v_in_phi'; destruct v_in_phi' as [[v' v_val] [v_eq_v' v_in_phi']]; simpl in v_eq_v'; subst v'.
      apply (find_not_found X.eq_bool v v v_val phi v_phi (eq_var_bool_refl v) v_in_phi').
      apply False_rect; apply v_not_in_phi; apply in_impl_mem.
      reflexivity. 
      rewrite k3; assumption.
      assumption.
      rewrite <- K1.
      do 2 rewrite subst_comp_is_subst_comp.
      simpl; rewrite find_app.
      generalize (mem_bool_ok _ _ X.eq_bool_ok v (map (fun st : T1.variable * T1.term => fst st) phi)).
      case (mem_bool X.eq_bool v (map (fun st : T1.variable * T1.term => fst st) phi)); [intro v_in_phi | intro v_not_in_phi].
      case_eq (find X.eq_bool v phi); [intros v_val v_phi | intro v_phi].
      case_eq (find X.eq_bool v Phi); [intros v_Val v_Phi | intro v_Phi].
      rewrite (ok _ _ _ v_phi v_Phi).
      rewrite <- subst_eq_vars; intros z z_in_v.
      rewrite subst_rest_ok; trivial.
      apply v_in_ls with v v_Val; trivial.
      apply False_rect.
      rewrite <- K3 in v_in_lt.
      rewrite in_map_iff in v_in_lt; destruct v_in_lt as [[v' v_Val] [v_eq_v' v_in_Phi]]; simpl in v_eq_v'; subst v'.
      apply (find_not_found X.eq_bool v v v_Val Phi v_Phi (eq_var_bool_refl v) v_in_Phi).
      assert (v_in_phi' : In v (map (fun st : T1.variable * T1.term => fst st) phi)).
      apply mem_impl_in with (@eq _); trivial.
      rewrite in_map_iff in v_in_phi'; destruct v_in_phi' as [[v' v_val] [v_eq_v' v_in_phi']]; simpl in v_eq_v'; subst v'.
      apply False_rect; apply (find_not_found X.eq_bool v v v_val phi v_phi (eq_var_bool_refl v) v_in_phi').
      case_eq (find X.eq_bool v Phi); [intros v_Val v_Phi | intro v_Phi].
      rewrite <- subst_eq_vars; intros z z_in_v.
      rewrite subst_rest_ok; trivial.
      apply v_in_ls with v v_Val; trivial.
      apply False_rect.
      rewrite <- K3 in v_in_lt.
      rewrite in_map_iff in v_in_lt; destruct v_in_lt as [[v' v_Val] [v_eq_v' v_in_Phi]]; simpl in v_eq_v'; subst v'.
      apply (find_not_found X.eq_bool v v v_Val Phi v_Phi (eq_var_bool_refl v) v_in_Phi).
      assumption.
      split.
      simpl; apply f_equal; apply f_equal2.
      rewrite <- k2; rewrite <- subst_eq_vars; intros v v_in_t.
      simpl; rewrite find_app.
      generalize (mem_bool_ok _ _ X.eq_bool_ok v (map (fun st : T1.variable * T1.term => fst st) phi)).
      case (mem_bool X.eq_bool v (map (fun st : T1.variable * T1.term => fst st) phi)); [intro v_in_phi | intro v_not_in_phi].
      reflexivity.
      apply False_rect; apply v_not_in_phi; apply in_impl_mem; trivial.
      rewrite k3; assumption.
      injection K2; clear K2; intro K2.
      rewrite <- K2; apply map_eq.
      intros ti ti_in_lt; rewrite <- subst_eq_vars; intros v v_in_ti; simpl; rewrite find_app.
      generalize (mem_bool_ok _ _ X.eq_bool_ok v (map (fun st : T1.variable * T1.term => fst st) phi)).
      case (mem_bool X.eq_bool v (map (fun st : T1.variable * T1.term => fst st) phi)); [intro v_in_phi | intro v_not_in_phi].
      case_eq (find X.eq_bool v phi); [intros v_val v_phi | intro v_phi].
      case_eq (find X.eq_bool v Phi); [intros v_Val v_Phi | intro v_Phi].
      apply (ok _ _ _ v_phi v_Phi).
      assert (v_in_lt : In v (var_list_list lt)).
      destruct (in_split _ _ ti_in_lt) as [lt1 [lt2 H]]; rewrite H; rewrite var_list_list_app; apply in_or_app; right;
        simpl; apply in_or_app; left; assumption.
      rewrite <- K3 in v_in_lt.
      rewrite in_map_iff in v_in_lt; destruct v_in_lt as [[v' v_Val] [v_eq_v' v_in_Phi]]; simpl in v_eq_v'; subst v'.
      apply False_rect; apply (find_not_found X.eq_bool v v v_Val Phi v_Phi (eq_var_bool_refl v) v_in_Phi).
      assert (v_in_phi' : In v (map (fun st : T1.variable * T1.term => fst st) phi)).
      apply mem_impl_in with (@eq _); trivial.
      rewrite in_map_iff in v_in_phi'; destruct v_in_phi' as [[v' v_val] [v_eq_v' v_in_phi']]; simpl in v_eq_v'; subst v'.
      apply False_rect; apply (find_not_found X.eq_bool v v v_val phi v_phi (eq_var_bool_refl v) v_in_phi').
      reflexivity.
      split.
      intro v; rewrite map_app; simpl; split; intro H.
      simpl; destruct (in_app_or _ _ _ H) as [v_in_phi | v_in_Phi].
      apply in_or_app; left; rewrite <- k3; assumption.
      apply in_or_app; right; rewrite <- K3; assumption.
      destruct (in_app_or _ _ _ H) as [v_in_phi | v_in_Phi].
      apply in_or_app; left; rewrite k3; assumption.
      apply in_or_app; right; rewrite K3; assumption.
      intro v; simpl; rewrite find_app.
      case (mem_bool T1.eq_var_bool v (map (fun st : T1.variable * T1.term => fst st) phi)).
      apply (k4 v).
      apply (K4 v).
    Qed.

    Lemma rewrite_decomposed_term : 
      forall t s sigma,  
        t = apply_subst sigma s -> 
        well_formed s -> 
        (forall x u, In (x,u) sigma -> 
          match u with
            | Var _ => True
            | Term f l => (match F.arity f with Free n => n | _ => 2 end) <> length l
          end) ->
        (forall x u v, In (x,u) sigma -> In (x,v) sigma -> u = v) ->
        (forall x y u, In (x,u) sigma -> In (y,u) sigma -> x = y) ->
        (forall x, In x (var_list s) -> In x (map (@fst _ _) sigma)) ->
        forall u, one_step R u t -> 
          ((exists s', one_step R s' s /\ u = apply_subst sigma s') 
            \/
            (exists p, exists x, exists u', 
              subterm_at_pos s p = Some (Var x) /\
              one_step R u' (apply_subst sigma (Var x)) /\
              u = replace_at_pos t u' p)).
    Proof.
      intro t; pattern t; apply term_rec3; clear t.
(* 1/2 t is a variable *)
      intros v s sigma h0 Ws h1 h2 h3 h4 u H'.
      inversion H' as [t1' t2' H1 | ]; clear H'; subst.
      inversion H1 as [r l phi H2 H3 H4]; clear H1; subst.
      destruct l as [x | ]; [apply False_rect; apply (R_var _ _ H2) | discriminate].
(* 1/1 t is a compound term *)
      intros f lt Hlt s sigma h0 Ws h1 h2 h3 h4 u H'.
      inversion H' as [t1' t2' H1 | f' l1 l2' H1 H2]; clear H'; subst.
(* 1/2 rewrite step at top *)
      inversion H1 as [r l phi H2 H3 H4]; clear H1; subst.
      destruct (decompose_subst s (subst_rest (var_list s) sigma) l phi Ws) as [phi' [K1 [K2 [K3 K4]]]].
      intros x u xu_in_rest_sig; apply (h1 x u); apply subst_rest_subst with (var_list s); trivial.
      intros x u v xu_in_rest_sig xv_in_rest_sig; apply (h2 x u v); apply subst_rest_subst with (var_list s); trivial.
      intros x y u xu_in_rest_sig yu_in_rest_sig; apply (h3 x y u).
      apply subst_rest_subst with (var_list s); trivial.
      apply subst_rest_subst with (var_list s); trivial.
      intro x; split.
      intro x_in_s; assert (x_in_sig : In x (map (@fst _ _) sigma)).
      apply h4; assumption.
      rewrite in_map_iff in x_in_sig; destruct x_in_sig as [[x' u] [x_eq_x' x_in_sig]]; simpl in x_eq_x'; subst x'.
      rewrite in_map_iff; exists (x,u); split; trivial.
      apply subst_rest_subst_rest; trivial.
      intro x_in_rest_sig; rewrite in_map_iff in x_in_rest_sig; destruct x_in_rest_sig as [[x' u] [x_eq_x' x_in_rest_sig]]; simpl in x_eq_x'; subst x'.
      apply subst_rest_rest with sigma u; trivial.
      apply (proj2 (WR _ _ H2)).
      rewrite H4; rewrite h0.
      rewrite <- subst_eq_vars; intros v v_in_s; rewrite subst_rest_ok; trivial.
      left; exists (apply_subst phi' r); split.
      rewrite <- K2; apply at_top; apply instance; trivial.
      rewrite <- subst_comp_is_subst_comp; rewrite <- subst_eq_vars; intros v v_in_r.
      assert (v_in_l : In v (var_list l)).
      apply (R_reg _ _ H2); trivial.
      apply sym_eq; rewrite <- K1; trivial.
      do 2 rewrite subst_comp_is_subst_comp.
      rewrite <- subst_eq_vars; intros z z_in_v_phi'.
      rewrite subst_rest_ok; trivial.
      rewrite <- K2.
      destruct (var_in_subterm2 _ _ (in_impl_mem (@eq _) (fun a => eq_refl a) _ _ v_in_l)) as [p Sub].
      apply var_in_subterm with (apply_subst phi' (Var v)) p; trivial.
      generalize (subterm_at_pos_apply_subst_apply_subst_subterm_at_pos l p phi').
      rewrite Sub; trivial.
(* 1/1 rewrite step in subterms *)
      destruct s as [x | g ls].
(* 1/2 s is a variable *)
      right; exists nil; exists x; exists (Term f l1).
      split; trivial.
      split; trivial.
      rewrite <- h0; apply in_context; trivial.
(* 1/1 s is a compound term *)
      destruct (one_step_in_list H1) as [ti [ui [lt1 [lt2 [K [K1 K2]]]]]].
      simpl in h0; injection h0; clear h0; intro h0; intro; subst g.
      rewrite K1 in h0.
      destruct (split_map_set _ _ _ _ (sym_eq h0)) as [ls1 [ls2 [J1 [J2 J3]]]].
      destruct ls2 as [ | si ls2].
      discriminate.
      simpl in J3; injection J3; clear J3; intros J3 j3.
      destruct Hlt with ti si sigma ui as [[si' [L1 L2]] | [p [x [ui' [Sub [L1 L2]]]]]]; trivial.
      rewrite K1; apply in_or_app; right; left; reflexivity.
      apply sym_eq; assumption.
      apply (proj1 (well_formed_unfold Ws)); rewrite J1; apply in_or_app; right; left; reflexivity.
      intros x x_in_si; apply h4; rewrite J1; simpl; rewrite var_list_list_app; apply in_or_app; right;
        apply in_or_app; left; assumption.
      left; exists (Term f (ls1 ++ si' :: ls2)); split.
      apply in_context; rewrite J1.
      revert L1; clear; induction ls1 as [ | s1 ls1].
      intro; apply head_step; trivial.
      intro; apply tail_step; apply IHls1; trivial.
      simpl; apply f_equal; rewrite map_app; rewrite K2; apply sym_eq; apply f_equal2; trivial.
      simpl; apply f_equal2; trivial.
      apply sym_eq; trivial.
      right; exists ((length ls1) :: p); exists x; exists ui'; split.
      rewrite J1; simpl; rewrite nth_error_at_pos; rewrite Sub; trivial.
      split; trivial.
      rewrite K1; rewrite K2; replace (length ls1) with (length lt1).
      simpl; apply f_equal; revert L2; clear.
      induction lt1 as [ | t1 lt1]; simpl.
      intro; apply (f_equal (fun u => u :: lt2)); assumption.
      intro; apply f_equal; apply IHlt1; assumption.
      rewrite <- J2; rewrite length_map; reflexivity.
    Qed.

    Lemma R_reg_one_step :
      forall t s, (one_step R) s t -> forall x, In x (var_list s) -> In x (var_list t).
    Proof.
      intro t; pattern t; apply term_rec3; clear t.
      intros v s H; inversion H as [t1 t2 H0 H1 H2 |]; clear H; subst.
      inversion H0 as [r l sigma H H1 H2]; clear H0; subst.
      destruct l as [x | ]; [idtac | discriminate].
      apply False_rect; apply (R_var _ _ H).
      intros f l IHl s H; inversion H as [t1 t2 H0 H1 H2 | g l1 l2 H0 H1 H2]; clear H; subst.
      inversion H0 as [r l' sigma H H1 H2].
      intros x x_in_left.
      destruct (var_in_subterm2 _ _ (in_impl_mem (@eq _) (fun a => eq_refl a) _ _ x_in_left)) as [p Sub].
      generalize (subterm_in_instantiated_term _ _ _ Sub).
      case_eq (subterm_at_pos r p); [intros u' Sub' | intro Sub'].
      destruct u' as [x' | ]; [idtac | intro; discriminate].
      intro K; assert (x'_in_r : In x' (var_list r)).
      apply (var_in_subterm x' r p Sub'); left; reflexivity.
      assert (x'_in_l : In x' (var_list l')).
      apply (R_reg _ _ H); assumption.
      destruct (var_in_subterm2 _ _ (in_impl_mem (@eq _) (fun a => eq_refl a) _ _ x'_in_l)) as [q Sub''].
      apply var_in_subterm with (apply_subst sigma (Var x')) q.
      generalize (subterm_at_pos_apply_subst_apply_subst_subterm_at_pos l' q sigma).
      rewrite Sub''; trivial.
      rewrite <- K; left; reflexivity.
      intros [x' [p' [p'' [K [x'_in_r [Sub1 Sub2]]]]]].
      assert (x'_in_l : In x' (var_list l')).
      apply (R_reg _ _ H); assumption.
      destruct (var_in_subterm2 _ _ (in_impl_mem (@eq _) (fun a => eq_refl a) _ _ x'_in_l)) as [q Sub''].
      apply var_in_subterm with (apply_subst sigma (Var x')) q.
      generalize (subterm_at_pos_apply_subst_apply_subst_subterm_at_pos l' q sigma).
      rewrite Sub''; trivial.
      apply var_in_subterm with (Var x) p''; trivial.
      left; reflexivity.
      destruct (one_step_in_list H0) as [t [s [k [k' [K [K1 K2]]]]]]; subst l l1.
      intro x; do 2 rewrite var_list_unfold; do 2 rewrite var_list_list_app.
      intro x_in_ksk'; destruct (in_app_or _ _ _ x_in_ksk') as [x_in_k | x_in_sk'].
      apply in_or_app; left; assumption.
      simpl in x_in_sk'; destruct (in_app_or _ _ _ x_in_sk') as [x_in_s | in_in_k'].
      apply in_or_app; right; apply in_or_app; left.
      apply IHl with s; trivial.
      apply in_or_app; right; left; reflexivity.
      apply in_or_app; right; simpl; apply in_or_app; right; assumption.
    Qed.

    Definition collapse_subst s := 
      apply_subst (map (fun v : variable => (v, Var (inject 0))) (var_list s)) s.

    Inductive Rwf : relation term :=
      Ren : forall s s', one_step R (collapse_subst s') (collapse_subst s) -> Rwf s' s.

    Lemma find_col :
      forall vars v, In v vars ->
        find X.eq_bool v
        (map (fun v0 : T1.variable => (v0, T1.Var (inject 0))) vars) = Some (Var (inject 0)).
    Proof.
      intros vars v v_in_vars.
      case_eq (find X.eq_bool v (map (fun v0 => (v0, T1.Var (inject 0))) vars)); [intros v_val v_col | intro v_col].
      destruct (find_mem _ _ X.eq_bool_ok _ _ v_col) as [v' [col1 [col2 [v_eq_v' H]]]]; subst v'.
      assert (v_in_col : In (v,v_val) (col1 ++ (v,v_val) :: col2)).
      apply in_or_app; right; left; reflexivity.
      rewrite <- H in v_in_col; rewrite in_map_iff in v_in_col.
      destruct v_in_col as [v' [v_eq_v' v_in_col]]; injection v_eq_v'; intros; subst; simpl; trivial.
      apply False_rect; apply (find_not_found X.eq_bool v v (Var (inject 0)) _ v_col (eq_var_bool_refl v)).
      rewrite in_map_iff; exists v; split; trivial.
    Qed.

    Lemma Acc_Rwf : 
      (forall s, well_formed s -> Acc (one_step R) s) ->
      forall s, well_formed s -> Acc Rwf s.
    Proof.
      intros W s Ws.
      apply Acc_incl with (fun x0 y : T1.term => one_step R (collapse_subst x0) (collapse_subst y)).
      intros t1 t2 H; inversion H; trivial.
      apply (Wellfounded.Inverse_Image.Acc_inverse_image term term (one_step R) collapse_subst).
      apply W; unfold collapse_subst; apply well_formed_apply_subst; trivial.
      unfold well_formed_subst.
      intros v; case_eq (find X.eq_bool v (map (fun v0 => (v0, T1.Var (inject 0))) (T1.var_list s))); [intros v_val v_col | intro v_col].
      destruct (find_mem _ _ X.eq_bool_ok _ _ v_col) as [v' [col1 [col2 [v_eq_v' H]]]]; subst v'.
      assert (v_in_col : In (v,v_val) (col1 ++ (v,v_val) :: col2)).
      apply in_or_app; right; left; reflexivity.
      rewrite <- H in v_in_col; rewrite in_map_iff in v_in_col.
      destruct v_in_col as [v' [v_eq_v' v_in_col]]; injection v_eq_v'; intros; subst; simpl; trivial.
      reflexivity.
      trivial.
    Qed.

    Lemma one_step_Rwf : forall s t, one_step R t s -> Rwf t s.
    Proof.
      intros s t H; apply Ren.
      unfold collapse_subst.
      replace (T1.apply_subst
        (map (fun v : T1.variable => (v, T1.Var (inject 0))) (T1.var_list t)) t) with
      (T1.apply_subst
        (map (fun v : T1.variable => (v, T1.Var (inject 0))) (T1.var_list s)) t).
      apply one_step_apply_subst; trivial.
      rewrite <- subst_eq_vars; intros v v_in_t.
      assert (v_in_s : In v (var_list s)).
      apply R_reg_one_step with t; trivial.
      simpl.
      rewrite find_col; trivial.
      rewrite find_col; trivial.
    Qed.

    Lemma acc_decomposed_term :
      (forall s, well_formed s -> Acc (one_step R) s) ->
      forall s,   well_formed s -> 
        forall l, Acc (one_step_list (one_step R)) l -> 
          forall sigma, l = map (fun x => apply_subst sigma (Var x)) (var_list s) ->
            (forall x u, In (x,u) sigma -> Acc (one_step R) u) ->
            (forall x u, In (x,u) sigma -> 
              match u with
                | Var _ => True
                | Term f l => (match F.arity f with Free n => n | _ => 2 end) <> length l
              end) ->
            (forall x u v, In (x,u) sigma -> In (x,v) sigma -> u = v) ->
            (forall x y u, In (x,u) sigma -> In (y,u) sigma -> x = y) ->
            (forall x, In x (var_list s) -> In x (map (@fst _ _) sigma)) ->
            Acc (one_step R) (apply_subst sigma s).
    Proof.
      intros WfwfR s Ws.
      assert (Acc_s :=  Acc_Rwf WfwfR s Ws).
      induction Acc_s as [s Acc_s IHs].
      clear Acc_s; intros l Acc_l; revert s Ws IHs.
      induction Acc_l as [l Acc_l' IHl].
      assert (Acc_l : Acc (one_step_list (one_step R)) l).
      apply Acc_intro; apply Acc_l'.
      clear Acc_l'.
      intros s Ws IHs sigma H0 Acc_sigma H1 H2 H3 H4; apply Acc_intro.
      intros u H.
      destruct (rewrite_decomposed_term (apply_subst sigma s) s sigma 
        (eq_refl _) Ws H1 H2 H3 H4 u H) as [[t [J1 J2]] | J2]; clear H.
(* 1/2 rewriting in s *)
      rewrite J2; apply (IHs t) with (map (fun x => apply_subst sigma (Var x)) (var_list t)); trivial.
      apply one_step_Rwf; trivial.
      apply well_formed_rwr with R s; trivial.
      apply t_step; trivial.
      rewrite <- acc_one_step_list.
      intros v v_in_sig; rewrite in_map_iff in v_in_sig.
      destruct v_in_sig as [x [v_in_sig x_in_t]].
      rewrite <- acc_one_step_list in Acc_l.
      apply Acc_l; rewrite H0; rewrite in_map_iff; exists x; split; trivial.
      apply R_reg_one_step with t; trivial.
      intros x x_in_t; apply H4; apply R_reg_one_step with t; trivial.
(* 1/1 rewriting in sigma *)
      destruct J2 as [p [x [u' [Sub [H H']]]]].
      assert (H5 : exists y, exists s', exists sigma', 
        s' = replace_at_pos s (Var y) p /\
        (sigma' = sigma \/ (~In y (var_list s)) /\ sigma' = (y,u') :: sigma) /\
        well_formed s' /\
        u = apply_subst sigma' s' /\
        Acc (one_step_list (one_step R)) (map (fun x  => apply_subst sigma' (Var x)) (var_list s')) /\
        (forall (x : T1.variable) (u : T1.term), In (x, u) sigma' -> Acc (one_step R) u) /\
        (forall (x : T1.variable) (u : T1.term),
          In (x, u) sigma' ->
          match u with
            | T1.Var _ => True
            | T1.Term f l =>
              match T1.F.arity f with
                | AC => 2
                | C => 2
                | Free n => n
              end <> length l
          end) /\
        (forall (x : T1.variable) (u v : T1.term), In (x, u) sigma' -> In (x, v) sigma' -> u = v) /\
        (forall (x y : T1.variable) (u : T1.term), In (x, u) sigma' -> In (y, u) sigma' -> x = y) /\
        (forall x : T1.variable, In x (T1.var_list s') -> In x (map (@fst _ _) sigma')) /\
        (In (y,u') sigma')).
      generalize (mem_bool_ok _ _ T.eq_bool_ok u' (map (@snd _ _) sigma)); 
        case (mem_bool T.eq_bool u' (map (@snd _ _) sigma)); [intro u'_in_sigma | intro u'_not_in_sigma].
      assert (u'_in_sigma' : In u' (map (@snd _ _) sigma)).
      apply mem_impl_in with (@eq _); trivial.
      rewrite in_map_iff in u'_in_sigma'; destruct u'_in_sigma' as [[y u''] [u'_eq_u'' u'_in_sigma']]; simpl in u'_eq_u''; subst u''.
      exists y; exists (replace_at_pos s (Var y) p); exists sigma.
      split.
      reflexivity.
      split.
      left; reflexivity.
      split.
      apply well_formed_replace_at_pos; simpl; [trivial | reflexivity].
      split.
      rewrite subst_replace_at_pos.
      rewrite H'; apply (f_equal (fun u => replace_at_pos (apply_subst sigma s) u p)).
      simpl; case_eq (find X.eq_bool y sigma); [intros y_val y_sigma | intro y_sigma].
      apply H2 with y; trivial.
      destruct (find_mem _ _ X.eq_bool_ok _ _ y_sigma) as [y' [sig1 [sig2 [y_eq_y' K]]]]; subst y'.
      rewrite K; apply in_or_app; right; left; reflexivity.
      apply False_rect; apply (find_not_found X.eq_bool y y u' sigma y_sigma (eq_var_bool_refl y) u'_in_sigma').
      rewrite is_a_pos_exists_subterm; exists (Var x); assumption.
      split.
      rewrite <- acc_one_step_list.
      intros v v_in_sig; rewrite in_map_iff in v_in_sig.
      destruct v_in_sig as [z [v_in_sig z_in_t]].
      rewrite <- acc_one_step_list in Acc_l.
      generalize (X.eq_bool_ok z y); case (X.eq_bool z y); [intro z_eq_y | intro z_diff_y].
      subst z.
      rewrite <- v_in_sig; simpl.
      case_eq (find X.eq_bool y sigma); [intros y_val y_sigma | intro y_sigma].
      replace y_val with u'.
      apply Acc_sigma with y; trivial.
      apply (H2 y); trivial.
      destruct (find_mem _ _ X.eq_bool_ok _ _ y_sigma) as [y' [sig1 [sig2 [y'_eq_y K]]]]; subst y'.
      rewrite K; apply in_or_app; right; left; reflexivity.
      apply False_rect; apply (find_not_found X.eq_bool y y u' sigma y_sigma (eq_var_bool_refl y) u'_in_sigma').
      destruct (var_in_replace_at_pos _ _ _ _ z_in_t) as [z_in_s | z_in_y].
      apply Acc_sigma with z.
      rewrite <- v_in_sig; simpl.
      case_eq (find X.eq_bool z sigma); [intros z_val z_sigma | intro z_sigma].
      destruct (find_mem _ _ X.eq_bool_ok _ _ z_sigma) as [z' [sig1 [sig2 [z_eq_z' K]]]]; subst z.
      rewrite K; apply in_or_app; right; left; reflexivity.
      assert (z_in_sig := H4 _ z_in_s).
      rewrite in_map_iff in z_in_sig; destruct z_in_sig as [[z' z_val] [z_eq_z' z_in_sig]].
      simpl in z_eq_z'; subst z'.
      apply False_rect; apply (find_not_found X.eq_bool z z z_val sigma z_sigma (eq_var_bool_refl z) z_in_sig).
      destruct z_in_y as [z_eq_y | z_in_nil].
      absurd (z=y); trivial; apply sym_eq; trivial.
      contradiction.
      split.
      assumption.
      split.
      assumption.
      split.
      assumption.
      split.
      assumption.
      split.
      intros z z_in_t; destruct (var_in_replace_at_pos _ _ _ _ z_in_t) as [z_in_s | z_in_y].
      apply H4; trivial.
      destruct z_in_y as [z_eq_y | z_in_nil].
      subst z; rewrite in_map_iff; exists (y,u'); split; trivial.
      contradiction.
      trivial.

      set (m := (S (maxl _ (map (fun xt => (inject_inv (fst xt), snd xt)) sigma)))).
      exists (inject m).
      exists (replace_at_pos s (Var (inject m)) p).
      exists ((inject m, u') :: sigma); split.
      reflexivity.
      split.
      right; split.
      intro m_in_s; assert (m_in_sig := H4 _ m_in_s); absurd (m < m).
      apply Nat.lt_irrefl.
      rewrite in_map_iff in m_in_sig; destruct m_in_sig as [[z' t] [z_eq_z' z_in_sig]]; simpl in z_eq_z'; subst z'.
      unfold m at 2; apply le_n_S.
      apply maxl_is_max with t.
      rewrite in_map_iff; exists (inject m,t); split; simpl; trivial.
      rewrite Hinject2; trivial.
      reflexivity.
      split.
      apply well_formed_replace_at_pos; simpl; [trivial | reflexivity].
      split.
      rewrite subst_replace_at_pos.
      rewrite H'; simpl.
      rewrite eq_var_bool_refl.
      apply (f_equal (fun s => replace_at_pos s u' p)).
      rewrite <- subst_eq_vars; intros z z_in_s; simpl.
      generalize (X.eq_bool_ok z (inject m)); case (X.eq_bool z (inject m)); [intro z_eq_m | intros _; reflexivity].
      absurd (m < m).
      apply Nat.lt_irrefl.
      apply Nat.le_lt_trans with (inject_inv z).
      subst z; rewrite Hinject2; apply le_n.
      assert (z_in_sig := H4 _ z_in_s).
      rewrite in_map_iff in z_in_sig; destruct z_in_sig as [[z' t] [z_eq_z' z_in_sig]]; simpl in z_eq_z'; subst z'.
      subst m; apply le_n_S.
      apply maxl_is_max with t.
      rewrite in_map_iff; exists (z,t); split; trivial.
      rewrite is_a_pos_exists_subterm; exists (Var x); assumption.
      split.
      rewrite <- acc_one_step_list.
      intros t t_in_sigma'; rewrite in_map_iff in t_in_sigma'.
      destruct t_in_sigma' as [z [K1 K2]].
      destruct (var_in_replace_at_pos _ _ _ _ K2) as [z_in_s | z_in_m].
      rewrite <- acc_one_step_list in Acc_l.
      apply Acc_l; rewrite H0; rewrite in_map_iff; exists z; split; trivial.
      revert K1; simpl.
      generalize (X.eq_bool_ok z (inject m)); case (X.eq_bool z (inject m)); [intro z_eq_m | intros _; trivial].
      absurd (m < m).
      apply Nat.lt_irrefl.
      apply Nat.le_lt_trans with (inject_inv z).
      subst z; rewrite Hinject2; apply le_n.
      assert (z_in_sig := H4 _ z_in_s).
      rewrite in_map_iff in z_in_sig; destruct z_in_sig as [[z' t'] [z_eq_z' z_in_sig]]; simpl in z_eq_z'; subst z'.
      subst m; apply le_n_S.
      apply maxl_is_max with t'.
      rewrite in_map_iff; exists (z,t'); split; trivial.
      destruct z_in_m as [z_eq_m | z_in_nil]; [subst z | contradiction].
      revert K1; simpl.
      rewrite eq_var_bool_refl.
      intro; subst t.
      apply Acc_inv with (apply_subst sigma (Var x)).
      simpl.
      case_eq (find X.eq_bool x sigma); [intros x_val x_sigma | intro x_sigma].
      apply Acc_sigma with x.
      destruct (find_mem _ _ X.eq_bool_ok _ _  x_sigma) as [x' [sig1 [sig2 [x_eq_x' H'']]]]; subst x'.
      rewrite H''; apply in_or_app; right; left; reflexivity.
      apply WfwfR; simpl; trivial.
      reflexivity.
      assumption.
      split.
      intros y uu [yuu_eq_xu | yuu_in_sigma].
      injection yuu_eq_xu; intros; subst uu.
      apply Acc_inv with (apply_subst sigma (Var x)).
      simpl.
      case_eq (find X.eq_bool x sigma); [intros x_val x_sigma | intro x_sigma].
      apply Acc_sigma with x.
      destruct (find_mem _ _ X.eq_bool_ok _ _  x_sigma) as [x' [sig1 [sig2 [x_eq_x' H'']]]]; subst x'.
      rewrite H''; apply in_or_app; right; left; reflexivity.
      apply WfwfR; simpl; trivial.
      reflexivity.
      assumption.
      apply Acc_sigma with y; assumption.
      split.
      intros y uu [yuu_eq_xu | yuu_in_sigma].
      injection yuu_eq_xu; intros; subst y uu.
      destruct u' as [ | f k]; trivial.
      inversion H as [t1' t2' H'' | f' l1 l2' H'']; clear H; subst.
      inversion H'' as [r l tau H''']; clear H''; subst.
      destruct l as [y | g l].
      apply False_rect; apply (R_var _ _ H''').
      apply False_rect.
      revert H0; case_eq (find X.eq_bool x sigma); [intros x_val x_sigma | intro x_sigma]; [idtac | intro; discriminate].
      assert (x_in_sig : In (x,x_val) sigma).
      destruct (find_mem _ _ X.eq_bool_ok _ _ x_sigma) as [x' [sig1 [sig2 [x_eq_x' K]]]]; subst x'.
      rewrite K; apply in_or_app; right; left; reflexivity.
      intro e; generalize (H1 _ _ x_in_sig); rewrite <- e; simpl.
      rewrite length_map; intro L; apply L.
      destruct (well_formed_unfold (proj2 (WR _ _ H'''))) as [_ L']; apply sym_eq; destruct (F.arity g); assumption.
      generalize (H1 x (Term f l2')).
      replace (length k) with (length l2').
      intro K; apply K.
      rewrite H7; revert H7.
      case_eq (find X.eq_bool x sigma); [intros x_val x_sigma | intro x_sigma]; [idtac | intro; discriminate].
      intros _; destruct (find_mem _ _ X.eq_bool_ok _ _ x_sigma) as [x' [sig1 [sig2 [x_eq_x' K']]]]; subst x'.
      rewrite K'; apply in_or_app; right; left; reflexivity.
      revert H''; clear; intro H''; induction H''.
      reflexivity.
      simpl; rewrite IHH''; trivial.
      apply (H1 y); trivial.
      split.
      simpl; intros y uu vv [yuu_eq_xu | yuu_in_sigma] [yvv_eq_xu | yvv_in_sigma].
      injection yuu_eq_xu; intros; subst y uu.
      injection yvv_eq_xu; intros; subst vv; trivial.
      injection yuu_eq_xu; intros _ y_eq_m.
      absurd (m < m).
      apply Nat.lt_irrefl.
      apply Nat.le_lt_trans with (inject_inv y).
      subst y; rewrite Hinject2; apply le_n.
      subst m; apply le_n_S.
      apply maxl_is_max with vv.
      rewrite in_map_iff; exists (y, vv); split; trivial.
      injection yvv_eq_xu; intros _ y_eq_m.
      absurd (m < m).
      apply Nat.lt_irrefl.
      apply Nat.le_lt_trans with (inject_inv y).
      subst y; rewrite Hinject2; apply le_n.
      subst m; apply le_n_S.
      apply maxl_is_max with uu.
      rewrite in_map_iff; exists (y, uu); split; trivial.
      apply (H2 y); assumption.
      split.
      simpl; intros y z uu [yuu_eq_xu | yuu_in_sigma] [zuu_eq_xu | zuu_in_sigma].
      injection yuu_eq_xu; intros; subst y uu.
      injection zuu_eq_xu; intros; subst; trivial.
      injection yuu_eq_xu; intros uu_eq_u' y_eq_m.
      apply False_rect; apply u'_not_in_sigma; subst u'; apply in_impl_mem.
      reflexivity.
      rewrite in_map_iff; exists (z,uu); split; trivial.
      injection zuu_eq_xu; intros uu_eq_u' z_eq_m.
      apply False_rect; apply u'_not_in_sigma; subst u'; apply in_impl_mem.
      reflexivity.
      rewrite in_map_iff; exists (y,uu); split; trivial.
      apply (H3 y z uu); assumption.
      split.
      intros z z_in_s'; destruct (var_in_replace_at_pos _ _ _ _ z_in_s') as [z_in_s | z_in_m].
      right; apply H4; assumption.
      destruct z_in_m as [z_eq_m | z_in_nil]; [left; trivial | contradiction].
      left; reflexivity.

(* MAIN PROOF *)
      destruct H5 as [y [s' [sigma' [k0 [K0 [Ws' [K [Acc_sigma' [K1 [K2 [K3 [K4 [K5 K6]]]]]]]]]]]]].
      rewrite K.
      apply IHl with (map (fun x => apply_subst sigma' (Var x)) (var_list s')); trivial.
      assert (y_sig : apply_subst sigma' (Var y) = u').
      simpl; case_eq (find X.eq_bool y sigma'); [intros y_val y_sig | intro y_sig].
      apply (K3 y); trivial.
      destruct (find_mem _ _ X.eq_bool_ok _ _ y_sig) as [y' [sig1 [sig3 [y_eq_y' J]]]]; subst y.
      rewrite J; apply in_or_app; right; left; reflexivity.
      apply False_rect; apply (find_not_found X.eq_bool y y u' sigma' y_sig (eq_var_bool_refl y) K6).
      assert (x_sig : forall x, x<> y -> apply_subst sigma' (Var x) = apply_subst sigma (Var x)).
      intros z z_diff_y; destruct K0 as [K0 | [y_not_in_s K0]]; subst sigma'.
      reflexivity.
      simpl.
      generalize (X.eq_bool_ok z y); case (X.eq_bool z y); [intro z_eq_y | intros _; reflexivity].
      absurd (z=y); trivial.
      rewrite H0; rewrite k0.
      destruct K0 as [K0 | [y_not_in_s K0]]; subst sigma'.
      clear x_sig.
      revert H y_sig Sub.
      clear.
      revert sigma p x u' y; pattern s; apply term_rec3; clear s.
      intros v sigma p x u' y H y_sig Sub.
      destruct p as [ | ]; [injection Sub; clear Sub; intros; subst v | discriminate].
      simpl replace_at_pos; simpl var_list; simpl; simpl in y_sig; rewrite y_sig.
      left; assumption.
      intros f l IHl sigma p x u' y H y_sig Sub.
      destruct p as [ | i p].
      discriminate.
      simpl in Sub.
      revert Sub; generalize (nth_error_ok_in i l).
      destruct (nth_error l i) as [ti | ]; [idtac | intros; discriminate].
      intro H'; destruct (H' _ (eq_refl _)) as [l1 [l2 [L H'']]]; clear H'.
      intro Sub.
      subst l.
      rewrite replace_at_pos_unfold.
      rewrite replace_at_pos_list_replace_at_pos_in_subterm; trivial.
      do 2 (rewrite var_list_unfold; rewrite var_list_list_app; rewrite map_app).
      simpl var_list_list; do 2 rewrite map_app.
      set (k1 :=  (map (fun x0 : variable => apply_subst sigma (Var x0)) 
        (var_list_list l1))) in *.
      set (k2 :=  (map (fun x0 : variable => apply_subst sigma (Var x0)) 
        (var_list_list l2))) in *.
      clearbody k1 k2.
      assert (Hi : one_step_list (one_step R)
        (map (fun x0 : variable => apply_subst sigma (Var x0))
          (var_list (replace_at_pos ti (Var y) p)))
        (map (fun x0 : variable => apply_subst sigma (Var x0))
          (var_list ti))).
      apply IHl with x u'; trivial.
      apply in_or_app; right; left; reflexivity.
      set (k := map (fun x0 : variable => apply_subst sigma (Var x0)) (var_list ti)) in *.
      set (k' := map (fun x0 : variable => apply_subst sigma (Var x0))
        (var_list (replace_at_pos ti (Var y) p))) in *.
      clearbody k k'.
      induction k1 as [ | s1 k1].
      induction Hi; [left | right]; assumption.
      right; assumption.

      revert H x_sig y_sig y_not_in_s Sub.
      clear.
      revert sigma p x u' y; pattern s; apply term_rec3; clear s.
      intros v sigma p x u' y H x_sig y_sig y_not_in_s Sub.
      destruct p as [ | ]; [injection Sub; clear Sub; intros; subst v | discriminate].
      simpl replace_at_pos; simpl var_list; simpl; simpl in y_sig; rewrite y_sig.
      left; assumption.
      intros f l IHl sigma p x u' y H x_sig y_sig y_not_in_s Sub.
      destruct p as [ | i p].
      discriminate.
      simpl in Sub.
      revert Sub; generalize (nth_error_ok_in i l).
      destruct (nth_error l i) as [ti | ]; [idtac | intros; discriminate].
      intro H'; destruct (H' _ (eq_refl _)) as [l1 [l2 [L H'']]]; clear H'.
      intro Sub.
      subst l.
      rewrite replace_at_pos_unfold.
      rewrite replace_at_pos_list_replace_at_pos_in_subterm; trivial.
      do 2 (rewrite var_list_unfold; rewrite var_list_list_app; rewrite map_app).
      simpl var_list_list; do 2 rewrite map_app.
      set (k1 :=  (map (fun x0 : variable => apply_subst sigma (Var x0)) 
        (var_list_list l1))) in *.
      set (k1' := (map
        (fun x0 : variable => apply_subst ((y, u') :: sigma) (Var x0))
        (var_list_list l1))) in *.
      assert (k1_eq_k1' : k1 = k1').
      assert (y_not_in_l1 : ~In y (var_list_list l1)).
      intro y_in_l1; apply y_not_in_s.
      simpl; rewrite var_list_list_app; apply in_or_app; left; assumption.
      set (vl1 := (var_list_list l1)) in *.
      clearbody vl1.
      induction vl1 as [ | v1 vl1]; trivial.
      subst k1 k1'.
      simpl; simpl in IHvl1; rewrite <- IHvl1; clear IHvl1.
      assert (v1_sig := x_sig v1).
      simpl in v1_sig; rewrite v1_sig; clear v1_sig; trivial.
      intro v1_eq_y; apply y_not_in_l1; left; assumption.
      intro y_in_l1; apply y_not_in_l1; right; assumption.
      clearbody k1 k1'; subst k1.
      set (k2 :=  (map (fun x0 : variable => apply_subst sigma (Var x0)) 
        (var_list_list l2))) in *.
      set (k2' := (map
        (fun x0 : variable => apply_subst ((y, u') :: sigma) (Var x0))
        (var_list_list l2))) in *.
      assert (k2_eq_k2' : k2 = k2').
      assert (y_not_in_l2 : ~In y (var_list_list l2)).
      intro y_in_l2; apply y_not_in_s.
      simpl; rewrite var_list_list_app; apply in_or_app; right; apply in_or_app; right; assumption.
      set (vl2 := (var_list_list l2)) in *.
      clearbody vl2.
      induction vl2 as [ | v2 vl2]; trivial.
      subst k2 k2'.
      simpl; simpl in IHvl2; rewrite <- IHvl2; clear IHvl2.
      assert (v2_sig := x_sig v2).
      simpl in v2_sig; rewrite v2_sig; clear v2_sig; trivial.
      intro v2_eq_y; apply y_not_in_l2; left; assumption.
      intro y_in_l2; apply y_not_in_l2; right; assumption.
      clearbody k2 k2'; subst k2.
      assert (Hi : one_step_list (one_step R)
        (map (fun x0 : variable => apply_subst ((y,u') :: sigma) (Var x0))
          (var_list (replace_at_pos ti (Var y) p)))
        (map (fun x0 : variable => apply_subst sigma (Var x0))
          (var_list ti))).
      apply IHl with x; trivial.
      apply in_or_app; right; left; reflexivity.
      intro y_in_ti; apply y_not_in_s; rewrite var_list_unfold; rewrite var_list_list_app; apply in_or_app; right;
        apply in_or_app; left; assumption.
      set (k := map (fun x0 : variable => apply_subst sigma (Var x0)) (var_list ti)) in *.
      set (k' := map (fun x0 : variable => apply_subst ((y,u') :: sigma) (Var x0))
        (var_list (replace_at_pos ti (Var y) p))) in *.
      clearbody k k'.
      induction k1' as [ | s1 k1].
      induction Hi; [left | right]; assumption.
      right; assumption.

      intros s'' s''_R_s' Ws'' l'' Acc_l'' sigma'' J0 Acc_sigma'' J1 J2 J3 J4.
      apply IHs with l''; trivial.
      inversion s''_R_s' as [t' t'' J]; subst t' t''.
      subst s'; apply Ren.
      replace (collapse_subst s) with (collapse_subst (replace_at_pos s (Var y) p)); trivial.
      revert Sub.
      clear; intro Sub.
      assert (col_map : forall t, collapse_subst t = match t with
                                                       | Var _ => Var (inject 0)
                                                       | Term f l => Term f (map collapse_subst l) end).
      clear.
      intro t; pattern t; apply term_rec3; clear t.
      intros v; unfold collapse_subst; simpl.
      rewrite eq_var_bool_refl; reflexivity.
      intros f l IHl; unfold collapse_subst.
      rewrite var_list_unfold.
      simpl; apply f_equal; clear f.
      apply map_eq.
      intros t t_in_l.
      rewrite <- subst_eq_vars; intros v v_in_t'.
      simpl; rewrite find_col.
      rewrite find_col; trivial.
      destruct (in_split _ _ t_in_l) as [l1 [l2 H]]; subst l; rewrite var_list_list_app; apply in_or_app; right.
      simpl; apply in_or_app; left; trivial.
      revert p Sub; pattern s; apply term_rec3; clear s.
      intros v p Sub; destruct p as [ | i p]; [idtac | discriminate].
      injection Sub; clear Sub; intros; subst v.
      simpl; do 2 rewrite col_map; trivial.
      intros f l IH p Sub; destruct p as [ | i p].
      discriminate.
      rewrite replace_at_pos_unfold.
      do 2 rewrite col_map.
      apply f_equal.
      simpl in Sub.
      revert Sub; case_eq (nth_error l i); [intros ti H Sub| intros; discriminate].
      destruct (nth_error_ok_in _ _ H) as [l1 [l2 [L H']]].
      subst l; rewrite replace_at_pos_list_replace_at_pos_in_subterm; trivial.
      do 2 rewrite map_app; simpl.
      apply f_equal.
      apply (f_equal (fun t => t :: map collapse_subst l2)).
      apply IH; trivial.
      apply in_or_app; right; left; trivial.
    Qed.

    Lemma almost_const :
      forall f l, (forall t, In t l -> Acc (one_step R) t) ->
        (match F.arity f with Free n => n | _ => 2 end ) <> length l -> 
        Acc (one_step R) (Term f l).
    Proof.
      intros f l Acc_l; revert f.
      rewrite acc_one_step_list in Acc_l; induction Acc_l as [l Acc_l IHl].
      intros f L; apply Acc_intro.
      intros s H; inversion H as [t1 t2 H1 | g l1 l2 H2]; clear H; subst.
      inversion H1 as [r l' sigma H2].
      destruct l' as [ | g l'].
      apply False_rect; apply (R_var _ _ H2).
      apply False_rect; apply L; injection H0; clear H0; intros; subst.
      rewrite length_map.
      assert (Wf := WR _ _ H2).
      destruct (well_formed_unfold (proj2 Wf)) as [_ L'].
      apply sym_eq; destruct (F.arity f); trivial.
      apply IHl; trivial.
      replace (length l1) with (length l); trivial.
      apply sym_eq; apply rwr_list_length_eq with (one_step R).
      left; trivial.
    Qed.

    Lemma acc_well_formed_acc_all :
      (forall t, well_formed t -> Acc (one_step R) t) ->
      forall t, Acc (one_step R) t.
    Proof.
      intros WfR.
      intro t; pattern t; apply term_rec3; clear t.
      intros v; apply Acc_intro.
      intros y H; inversion H as [t1 t2 H1 | ].
      subst t1 t2.
      inversion H1 as [t1 t2 sigma]; subst.
      destruct t2 as [ | ]; [apply False_rect; apply (R_var _ _ H0) | discriminate].
      intros f l Acc_l.
      destruct (eq_nat_dec (match F.arity f with Free n => n | _ => 2 end ) (length l)) as [L | L].
      destruct (decompose_term (Term f l)) as [s [sigma [H0 [Ws [H1 [H2 [H3 H4]]]]]]].
      rewrite H0.
      destruct s as [z | g k].
      apply False_rect; revert H0; simpl.
      case_eq (find X.eq_bool z sigma); [intros z_val z_sig | intro z_sig]; [idtac | discriminate].
      intro H0; apply (H1 z (Term f l)).
      rewrite H0; destruct (find_mem _ _ X.eq_bool_ok _ _ z_sig) as [z' [sig1 [sig2 [z_eq_z' H]]]]; subst z'.
      rewrite H; apply in_or_app; right; left; trivial.
      trivial.
      apply acc_decomposed_term with (map (fun x => apply_subst sigma (Var x)) (var_list (Term g k))); trivial.
      rewrite <- acc_one_step_list.
      intros t t_in_sig.
      rewrite in_map_iff in t_in_sig; destruct t_in_sig as [x [H x_in_s]].
      destruct (var_in_subterm2 _ _ (in_impl_mem (@eq _) (fun a => eq_refl a) _ _ x_in_s)) as [p Sub].
      destruct p as [ | i p].
      discriminate.
      simpl in Sub; revert Sub; generalize (nth_error_ok_in i k).
      destruct (nth_error k i) as [ti | ].
      intros H'; destruct (H' _ (eq_refl _)) as [l1 [l2 [L' H'']]].
      intro Sub; subst t.
      apply acc_subterms_3 with p (apply_subst sigma ti).
      apply Acc_l; injection H0; clear H0; intros; subst l.
      rewrite in_map_iff; exists ti; split; trivial.
      subst k; apply in_or_app; right; left; trivial.
      generalize (subterm_at_pos_apply_subst_apply_subst_subterm_at_pos ti p sigma).
      rewrite Sub; trivial.
      intros _ H'; discriminate.
      intros x u xu_in_sig.
      assert (x_in_s : In x (var_list (Term g k))).
      rewrite H4; rewrite in_map_iff; exists (x,u); split; trivial.
      replace u with (apply_subst sigma (Var x)).
      destruct (var_in_subterm2 _ _  (in_impl_mem (@eq _) (fun a => eq_refl a) _ _ x_in_s)) as [p Sub].
      destruct p as [ | i p].
      discriminate.
      simpl in Sub; revert Sub; generalize (nth_error_ok_in i k).
      destruct (nth_error k i) as [ti | ].
      intros H'; destruct (H' _ (eq_refl _)) as [l1 [l2 [L' H'']]].
      intro Sub.
      apply acc_subterms_3 with p (apply_subst sigma ti).
      apply Acc_l; injection H0; clear H0; intros; subst l.
      rewrite in_map_iff; exists ti; split; trivial.
      subst k; apply in_or_app; right; left; trivial.
      generalize (subterm_at_pos_apply_subst_apply_subst_subterm_at_pos ti p sigma).
      rewrite Sub; trivial.
      intros _ H'; discriminate.
      simpl.
      rewrite subst_aux with sigma x u; trivial.
      intros; rewrite <- H4; trivial.
      apply almost_const; trivial.
    Qed.

  End Dec_well_formed.

Lemma are_constructors_of_R :
  forall R, (forall v t, ~ R t (Var v)) -> 
  forall  f l t', (refl_trans_clos (one_step R) t' (Term f l)) ->
  (~defined R f) ->
  exists l', t' = Term f l' /\ refl_trans_clos (one_step_list (one_step R)) l' l.
Proof.
intros R R_var f l t' H Cf.
inversion H as [u | u1 u2 K]; clear H; subst.
exists l; split; [reflexivity | left].
set (t := Term f l) in *.
assert (H := eq_refl t).
unfold t at 2 in H.
clearbody t; revert H; induction K as [u1 u2 K1 | u1 u2 u3 K1 Kn]; intros; subst.
inversion K1 as [v1 v2 K | g k1 k2 K]; clear K1; subst.
inversion K as [v1 v2 sigma H]; clear K.
destruct v2 as [x2 | f2 l2].
apply False_rect; apply (R_var _ _ H).
apply False_rect; apply Cf; injection H1; clear H1; intros; subst; constructor 1 with l2 v1; assumption.
exists k1; split; [reflexivity | right; left; assumption].
destruct (IHKn (eq_refl _)) as [l' [H1 H2]]; clear IHKn; subst.
inversion K1 as [v1 v2 K | g k1 k2 K]; clear K1; subst.
inversion K as [v1 v2 sigma H]; clear K.
destruct v2 as [x2 | f2 l2].
apply False_rect; apply (R_var _ _ H).
apply False_rect; apply Cf; injection H1; clear H1; intros; subst; constructor 1 with l2 v1; assumption.
exists k1; split; [reflexivity | apply refl_trans_clos_is_trans with l'].
right; left; assumption.
assumption.
Qed.

End Make.
