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

Set Implicit Arguments. 

From Stdlib Require Import Setoid Relations List Wellfounded.
From CoLoR Require Export TransClosure closure more_list.

Inductive one_step_list A (R : relation A) : relation (list A) :=
    | head_step : forall t1 t2 l, R t1 t2 -> one_step_list R (t1 :: l) (t2 :: l)
    | tail_step : forall t l1 l2, one_step_list R l1 l2 -> one_step_list R (t :: l1) (t :: l2).

Lemma one_step_list_incl : 
  forall A (R1 R2 : relation A), (forall a1 a2, R1 a1 a2 -> R2 a1 a2) -> 
  forall l1 l2, one_step_list R1 l1 l2 -> one_step_list R2 l1 l2.
Proof.
intros A R1 R2 R1_in_R2.
fix one_step_list_incl 1.
intros l1; case l1; clear l1.
intros l2 H; inversion H.
intros a1 l1 l2 H; inversion H as [b1 b2 l H1 | b k1 k2 Hk]; subst.
left; apply R1_in_R2; assumption.
right; apply one_step_list_incl; assumption.
Qed.

Lemma one_step_list_length_eq :
  forall A R (l1 l2 : list A), one_step_list R l1 l2 -> length l1 = length l2.
Proof.
intros A R; fix one_step_list_length_eq 1.
intros l1; case l1; clear l1.
intros l2 H; inversion H.
intros a1 l1 l2 H; inversion H as [b1 b2 l H1 | b k1 k2 Hk]; subst.
apply eq_refl.
simpl; rewrite (one_step_list_length_eq _ _ Hk); apply eq_refl.
Qed.

Lemma trans_clos_one_step_list_length_eq :
  forall A R (l1 l2 : list A), trans_clos (one_step_list R) l1 l2 -> length l1 = length l2.
Proof.
intros A R l1 l2 H; induction H as [l1 l2 H | l1 l2 l3 H1 H2].
apply one_step_list_length_eq with R; assumption.
rewrite (one_step_list_length_eq H1); assumption.
Qed.

Lemma refl_trans_clos_one_step_list_length_eq :
  forall A R (l1 l2 : list A), refl_trans_clos (one_step_list R) l1 l2 -> length l1 = length l2.
Proof.
intros A R l1 l2 H; inversion H as [l | k1 k2 K]; clear H; subst.
apply eq_refl.
apply trans_clos_one_step_list_length_eq with R; assumption.
Qed.

Lemma acc_one_step_list_1 :
  forall A R (l : list A), (forall t, In t l -> Acc R t) -> Acc (one_step_list R) l.
Proof.
fix acc_one_step_list_1 3.
intros A R l; case l; clear l.
intros _; apply Acc_intro; intros l' H; inversion H.
intros a l Acc_l.
assert (Acc_al : Acc (product_o  R (one_step_list R)) (a,l)).
apply acc_and.
apply Acc_l; left; trivial.
apply acc_one_step_list_1; intros; apply Acc_l; right; assumption.
replace (a :: l) with ((fst (a,l) :: (snd (a,l)))); trivial.
clear acc_one_step_list_1 Acc_l.
generalize (a,l) Acc_al; clear a l Acc_al; intros al Acc_al; 
induction Acc_al as [[a l] Acc_al IH]; apply Acc_intro.
intros [ | a' l'] H; inversion H; clear H; subst.
apply (IH (a',l)).
apply CaseA; trivial.
apply (IH (a,l')).
apply CaseB; trivial.
Qed.

Lemma acc_one_step_list_2 :
 forall A R (l : list A), Acc (one_step_list R) l -> (forall t, In t l -> Acc R t). 
Proof.
fix acc_one_step_list_2 4.
intros A R l Acc_l t t_in_l; apply Acc_intro; intros s H.
destruct (in_split t l t_in_l) as [l1 [l2 K]].
apply (acc_one_step_list_2 A R (l1 ++ s :: l2)).
apply Acc_inv with l; trivial.
subst l; clear Acc_l t_in_l; revert l1; fix Hone_step 1.
intros [ | a1 l1].
left; assumption.
right; apply Hone_step.
apply in_or_app; right; left; apply eq_refl.
Qed.

Lemma acc_one_step_list :
 forall A R (l : list A), (forall t, In t l -> Acc R t) <-> Acc (one_step_list R) l.
Proof.
intros A R l; split; intro H.
apply acc_one_step_list_1; assumption.
apply acc_one_step_list_2; assumption.
Qed.

Lemma one_step_in_list :
  forall A R (l l' : list A), one_step_list R l' l ->
  exists t, exists t', exists l1, exists l2, R t' t /\  l = l1 ++ t :: l2 /\ l' = l1 ++ t' :: l2.
Proof.
intros A R l l' H'; induction H'.
exists t2; exists t1; exists (@nil A); exists l; repeat split; trivial.
destruct IHH' as [u [u' [l3 [l4 [H1 [H2 H3]]]]]]; subst.
exists u; exists u'; exists (t :: l3); exists l4; repeat split; trivial.
Qed.

Lemma one_step_list_chop : 
  forall A R (k1 l1 k2 l2 : list A), length k1 = length k2 -> one_step_list R (k1 ++ l1) (k2 ++ l2) -> refl_trans_clos (one_step_list R) l1 l2.
Proof.
fix one_step_list_chop 3.
intros A R k1 l1 k2 l2 L H.
destruct k1 as [ | a k1]; destruct k2 as [ | b k2].
right; left; assumption.
discriminate.
discriminate.
simpl in H; inversion H as [t1 t2 k K | t l1' l2' K]; clear H; subst.
assert (J : l1 = l2).
simpl in L; injection L; clear L.
revert H3; clear.
revert k1 k2 l1 l2; fix l1_eq_l2 1.
intros [ | a k1] [ | b k2] l1 l2 J L.
assumption.
discriminate.
discriminate.
injection J; clear J; intros J _.
apply (l1_eq_l2 _ _ _ _ J).
 injection L; trivial.
rewrite J; left.
apply one_step_list_chop with k1 k2; trivial.
simpl in L; injection L; trivial.
Qed.

Lemma rwr_list_chop : 
  forall A R (k1 l1 k2 l2 : list A), length k1 = length k2 -> trans_clos (one_step_list R) (k1 ++ l1) (k2 ++ l2) -> refl_trans_clos (one_step_list R) l1 l2.
Proof.
intros A R k1 l1 k2 l2 L H.
set (ll1 := k1 ++ l1) in *.
assert (H1 := eq_refl ll1).
unfold ll1 at 2 in H1.
clearbody ll1.
set (ll2 := k2 ++ l2) in *.
assert (H2 := eq_refl ll2).
unfold ll2 at 2 in H2.
clearbody ll2.
revert k1 l1 k2 l2 L H1 H2.
induction H as [ll1 ll2 H | ll1 ll2 ll3 H1 H2]; intros k1 l1 k2 l2 L K1 K2.
apply one_step_list_chop with k1 k2; subst; trivial.
assert (H : exists k3, exists l3, length k1 = length k3 /\ ll2 = k3 ++ l3).
generalize (one_step_list_length_eq H1).
subst; clear.
revert ll2  l1; induction k1 as [ | a k1]; intros ll2 l1 L.
exists nil; exists ll2; split; apply eq_refl.
destruct ll2 as [ | b ll2].
discriminate.
simpl in L; injection L; clear L; intro L.
destruct (IHk1 _ _ L) as [k3 [l3 [L' H]]]; subst.
exists (b :: k3); exists l3; split; trivial.
simpl; apply f_equal; trivial.
destruct H as [k3 [l3 [L' K3]]].
apply refl_trans_clos_is_trans with l3.
apply one_step_list_chop with k1 k3; subst; trivial.
apply IHH2 with k3 k2; trivial.
rewrite <- L'; assumption.
Qed.

Lemma rwr_list_expand_strong : 
  forall A R (l l' : list A), trans_clos (one_step_list R) l' l <->
  exists t, exists t', exists l1, exists l2, exists l2', 
   l = l1 ++ t :: l2 /\ l' = l1 ++ t' :: l2' /\ trans_clos R t' t /\ refl_trans_clos (one_step_list R) l2' l2.
Proof.
intros A R l l'; split; intro H.
induction H as [l l' H | l l' l'' H H'].
destruct (one_step_in_list H) as [t [t' [l1 [l2 [H1 [H2 H3]]]]]].
exists t; exists t'; exists l1; exists l2; exists l2; split; [assumption | split; [assumption | split]].
left; assumption.
left.
destruct (one_step_in_list H) as [t [t' [l1 [l2 [H1 [H2 H3]]]]]].
destruct IHH' as [u [u' [k1 [k2 [k2' [K1 [K2 [K3 K4]]]]]]]].
rewrite K2 in H2.
destruct (in_in_split_set _ _ _ _ _ _ H2) as [[[k [J1 J2]] | [k [J1 J2]]] | [k [J1 J2]]]; subst.
exists t; exists t'; exists l1; exists (k ++ u :: k2); exists (k ++ u' :: k2'); split; [idtac | split; [idtac | split]].
rewrite <- app_assoc; apply eq_refl.
apply eq_refl.
left; assumption.
apply rwr_list_chop with (l1 ++ t :: nil) (l1 ++ t :: nil); trivial.
do 2 rewrite <- app_assoc in H'; simpl in H; do 2 rewrite <- app_assoc; simpl; trivial.
exists u; exists u'; exists k1; exists k2; exists (k ++ t' :: l2); split; [idtac | split; [idtac | split]].
apply eq_refl.
rewrite <- app_assoc; apply eq_refl.
assumption.
apply refl_trans_clos_is_trans with (k ++ t :: l2); trivial.
right; left.
revert H1; clear; intro H1; induction k as [ | a k].
left; assumption.
right; assumption.
exists u; exists t'; exists l1; exists k2; exists l2; split; [idtac | split; [idtac | split]].
apply eq_refl.
apply eq_refl.
apply trans_clos_is_trans with t; trivial.
left; assumption.
assumption.
destruct H as [t [t' [l1 [l2 [l2' [H1 [H2 [H3 H4]]]]]]]].
assert (H5 : trans_clos (one_step_list R) (l1 ++ t' :: l2) (l1 ++ t :: l2)).
clear H4; subst; induction H3 as [t1 t2 H | t1 t2 t3 H1 H2].
left; induction l1 as [ | a l1]; [left | right]; assumption.
apply trans_clos_is_trans with (l1 ++ t2 :: l2); trivial.
revert H1; clear; left; induction l1 as [ | a l1]; [left | right]; assumption.
inversion H4 as [k2 | k3 k2 H]; clear H4; subst.
assumption.
apply trans_clos_is_trans with (l1 ++ t' :: l2); trivial.
revert H.
replace (l1 ++ t' :: l2) with ((l1 ++ t' :: nil) ++ l2).
replace (l1 ++ t' :: l2') with ((l1 ++ t' :: nil) ++ l2').
generalize (l1 ++ t' :: nil); clear.
intros l; revert l2 l2'; induction l as [ | a l]; intros l2 l2' H; trivial.
generalize (IHl _ _ H); simpl; generalize (l ++ l2') (l ++ l2); clear.
intros l1 l2 H; induction H as [l1 l2 H | l1 l2 l3 H1 H2].
left; right; assumption.
apply trans_clos_is_trans with (a :: l2); trivial.
left; right; assumption.
rewrite <- app_assoc; simpl; apply eq_refl.
rewrite <- app_assoc; simpl; apply eq_refl.
Qed.

Lemma rwr_list_expand : 
  forall A R (l l' : list A), trans_clos (one_step_list R) l' l <->
  exists t, exists t', exists l1, exists l2, exists l1', exists l2', 
   l = l1 ++ t :: l2 /\ l' = l1' ++ t' :: l2' /\ 
	refl_trans_clos (one_step_list R) l1' l1 /\ trans_clos R t' t /\ refl_trans_clos (one_step_list R) l2' l2.
Proof.
intros A R l l'; split; intro H.
rewrite rwr_list_expand_strong in H.
destruct H as [t [t' [l1 [l2 [l2' [H1 [H2 [H3 H4]]]]]]]].
exists t; exists t'; exists l1; exists l2; exists l1; exists l2'.
split; [idtac | split; [idtac | split; [idtac | split]]]; try assumption.
left.
destruct H as [t [t' [l1 [l2 [l1' [l2' [H1 [H2 [H3 [H4 H5]]]]]]]]]].
destruct H3 as [k1 | k1' k1 K3].
rewrite rwr_list_expand_strong.
exists t; exists t'; exists k1; exists l2; exists l2'.
split; [idtac | split; [idtac | split]]; assumption.
apply trans_clos_is_trans with (k1' ++ t :: l2).
rewrite rwr_list_expand_strong.
exists t; exists t'; exists k1'; exists l2; exists l2'.
split; [idtac | split; [idtac | split]]; try assumption.
apply eq_refl.
subst l; revert K3; clear; intro K; induction K as [k1 k2 K | k1 k2 k3 K1 K2].
left; induction K as [a1 a2 k K | a k1 k2 K].
left; assumption.
right; assumption.
apply trans_clos_is_trans with (k2 ++ t :: l2); trivial.
left; revert K1; clear; intro K; induction K as [a1 a2 k K | a k1 k2 K].
left; assumption.
right; assumption.
Qed.

Definition rwr_list A (R : relation A) := trans_clos (one_step_list R).

Definition rwr_list_length_eq := trans_clos_one_step_list_length_eq.

Lemma rwr_list_cons : forall A (R : relation A) a1 a2 l, trans_clos R a1 a2 -> rwr_list R (a1 :: l) (a2 :: l).
Proof.
intros A R a1 a2 l H; induction H as [a1 a2 H | a1 a2 a3 H1 H2].
do 2 left; assumption.
right with (a2 :: l); trivial.
left; assumption.
Qed.

Lemma rwr_list_tail : forall A (R : relation A) a l1 l2, rwr_list R l1 l2 -> rwr_list R (a :: l1) (a :: l2).
intros A R a l1 l2 H; induction H as [l1 l2 H | l1 l2 l3 H1 H2].
left; right; assumption.
right with (a :: l2); trivial.
right; assumption.
Qed.

Lemma rwr_list_split : 
  forall A (R : relation A) a1 a2 l1 l2, trans_clos R a1 a2 -> rwr_list R l1 l2 -> rwr_list R (a1 :: l1) (a2 :: l2).
Proof.
intros A R a1 a2 l1 l2 H1 H2; apply trans_clos_is_trans with (a1 :: l2).
apply rwr_list_tail; assumption.
apply rwr_list_cons; assumption.
Qed.

Lemma one_step_list_refl_trans_clos_one_step :
  forall A R (l1 l2 : list A) s k1 k2 t, length l1 = length k1 ->
        (one_step_list R) (l1 ++ s :: l2) (k1 ++ t :: k2) ->
	refl_trans_clos R s t.
Proof.  
intros A R l1 l2 s k1 k2 t L H.
set (l := l1 ++ s :: l2) in *.
assert (H1 := eq_refl l); unfold l at 2 in H1; clearbody l.
set (k := k1 ++ t :: k2) in *.
assert (H2 := eq_refl k); unfold k at 2 in H2; clearbody k.
revert l1 l2 s k1 k2 t L H1 H2.
induction H as [u u' k H | u l k' H].
intros l1 l2 s k1 k2 t L H1 H2.
destruct l1 as [ | a1 l1]; destruct k1 as [ | b1 k1].
injection H1; injection H2; intros; subst; right; left; trivial.
discriminate.
discriminate.
injection H1; injection H2; intros K1 K2 K3 K4; subst.
injection L; clear L; intro L.
assert (s_eq_t : s = t).
revert L K3; clear.
revert l2 s k1 k2 t; induction l1 as [ | a1 l1]; intros l2 s [ | b1 k1] k2 t L H.
injection H; intros; subst; trivial.
discriminate.
discriminate.
injection L; clear L; intro L.
injection H; intros K1 K2; subst.
apply (IHl1 l2 s k1 k2 t); trivial.
subst t; left.
intros [ | a1 l1] l2 s [ | b1 k1] k2 t L H1 H2.
simpl in H1, H2; injection H1; injection H2; intros K1 K2 K3 K4; repeat subst.
left.
discriminate.
discriminate.
injection L; clear L; intro L.
injection H1; injection H2; intros K1 K2 K3 K4; subst.
apply (IHH _ _ _ _ _ _ L (eq_refl _) (eq_refl _)).
Qed.

Lemma refl_trans_clos_one_step_list_refl_trans_clos_one_step :
  forall A R (l1 l2 : list A) s k1 k2 t, length l1 = length k1 ->
	 refl_trans_clos (one_step_list R) (l1 ++ s :: l2) (k1 ++ t :: k2) ->
	refl_trans_clos R s t.
Proof.  
intros A R l1 l2 s k1 k2 t L H.
set (l := l1 ++ s :: l2) in *.
assert (H1 := eq_refl l); unfold l at 2 in H1; clearbody l.
set (k := k1 ++ t :: k2) in *.
assert (H2 := eq_refl k); unfold k at 2 in H2; clearbody k.
revert l1 l2 s k1 k2 t L H1 H2.
inversion H as [l' | l' k' H'].
subst l' k; intros l1 l2 s k1 k2 t L H1 H2.
rewrite H2 in H1; clear H2.
assert (s_eq_t : s = t).
revert k1 s t k2 l2 L H1; induction l1 as [ | a1 l1]; intros [ | b1 k1] s t k2 l2 L H1.
injection H1; intros; subst; trivial.
discriminate.
discriminate.
injection L; clear L; intro L.
injection H1; intros; subst.
apply (IHl1 _ s t k2 l2 L H0).
subst t; left.
subst l' k'; clear H.
induction H' as [l' k' H | l' ll k' H H'].
intros l1 l2 s k1 k2 t L H1 H2.
subst l' k'; apply (one_step_list_refl_trans_clos_one_step (R := R) l1 l2 s k1 k2 t); trivial.
intros l1 l2 s k1 k2 t L H1 H2.
assert (L' : length l' = length ll).
apply one_step_list_length_eq with R; trivial.
assert (H'' : exists ll1, exists ll2, exists u, length l1 = length ll1 /\ ll = ll1 ++ u :: ll2).
rewrite H1 in L'.
revert L'; clear.
revert ll l2 s; induction l1 as [ | a1 l1]; intros ll l2 s L.
destruct ll as [ | u ll].
discriminate.
exists nil; exists ll; exists u; split; trivial.
destruct ll as [ | a ll].
discriminate.
injection L; clear L; intro L.
destruct (IHl1 _ _ _ L) as [ll1 [ll2 [u [L' H]]]].
exists (a :: ll1); exists ll2; exists u; repeat split.
simpl; rewrite L'; trivial.
simpl; rewrite H; trivial.
destruct H'' as [ll1 [ll2 [u [L'' H'']]]].
apply refl_trans_clos_is_trans with u.
apply (one_step_list_refl_trans_clos_one_step (R := R) l1 l2 s ll1 ll2 u); trivial.
subst l' ll; assumption.
apply (IHH' ll1 ll2 u k1 k2 t); trivial.
rewrite <- L''; assumption.
Qed.

Lemma refl_trans_clos_one_step_list_head_tail :
  forall A R s t (l1 l2 : list A),
	 refl_trans_clos (one_step_list R) (s :: l1) (t :: l2) <-> (refl_trans_clos R s t /\ refl_trans_clos (one_step_list R) l1 l2).
Proof.
intros A R s t l1 l2; split; intro H.
inversion H as [l | l1' l2' H']; clear H; subst.
split; left.
set (k1 := s :: l1) in *; assert (H1 := eq_refl k1); unfold k1 at 2 in H1; clearbody k1.
set (k2 := t :: l2) in *; assert (H2 := eq_refl k2); unfold k2 at 2 in H2; clearbody k2.
revert s t l1 l2 H1 H2.
induction H' as [k1 k2 H | k1 k2 k3 H].
intros s t l1 l2 H1 H2; subst; inversion H; clear H; subst; split.
right; left; assumption.
left.
left.
right; left; assumption.
intros s t l1 l2 H1 H2; subst.
inversion H; clear H; subst.
destruct (IHH' t2 t l1 l2) as [H1 H2]; trivial.
split.
apply refl_trans_clos_is_trans with t2; [right; left | idtac]; assumption.
assumption.
destruct (IHH' s t l3 l2) as [H1 H2]; trivial.
split.
assumption.
apply refl_trans_clos_is_trans with l3.
right; left; assumption.
assumption.
destruct H as [H1 H2].
apply refl_trans_clos_is_trans with (s :: l2).
inversion H2 as [l | k1 k2 K2]; clear H2; subst.
left.
right; induction K2.
left; right; assumption.
apply trans_clos_is_trans with (s :: y); trivial.
left; right; assumption.
inversion H1 as [u | s' t' K1]; clear H1; subst.
left.
induction K1.
right; do 2 left; assumption.
apply refl_trans_clos_is_trans with (y :: l2); trivial.
right; do 2 left; assumption.
Qed.

Lemma refl_trans_clos_one_step_list_refl_trans_clos :
  forall A R (ll : list (A * A)), 
	(refl_trans_clos (one_step_list R) (map (@fst _ _) ll) (map (@snd _ _) ll)) <-> 
       	(forall s t, In (s,t) ll -> refl_trans_clos R s t).
Proof.
intros A R ll; induction ll as [ | [a b] ll]; split; intro H.
intros s t st_in_nil; contradiction.
left.
simpl in H; rewrite refl_trans_clos_one_step_list_head_tail in H; destruct H as [H1 H2].
simpl; intros s t [st_eq_ab | st_in_ll]; 
  [injection st_eq_ab; intros; subst; apply H1 | revert s t st_in_ll; rewrite <- IHll; assumption].
simpl; rewrite refl_trans_clos_one_step_list_head_tail; split.
apply H; left; apply eq_refl.
rewrite IHll; intros; apply H; intros; right; assumption.
Qed.

Lemma refl_trans_clos_one_step_list_refl_trans_clos_alt :
  forall A R (f g : A -> A) l, 
	(refl_trans_clos (one_step_list R) (map f l) (map g l)) <-> 
       	(forall t, In t l -> refl_trans_clos R (f t) (g t)).
Proof.
intros A R f g l; induction l as [ | a l]; split; intro H.
intros t t_in_nil; contradiction.
left.
simpl in H; rewrite refl_trans_clos_one_step_list_head_tail in H; destruct H as [H1 H2].
simpl; intros t [t_eq_a | t_in_l]; [subst; apply H1 | revert t t_in_l; rewrite <- IHl; assumption].
simpl; rewrite refl_trans_clos_one_step_list_head_tail; split.
apply H; left; apply eq_refl.
rewrite IHl; intros; apply H; intros; right; assumption.
Qed.

