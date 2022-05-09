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



(** * Permutation over lists, and finite multisets. *)

Set Implicit Arguments. 

From Coq Require Import List Relations Arith Setoid Morphisms FunInd.
From CoLoR Require Import decidable_set more_list equiv_list.

Inductive permut0 (A B : Type) (R : A -> B -> Prop) : (list A -> list B -> Prop) :=
  | Pnil : permut0 R nil nil
  | Pcons : forall a b l l1 l2, R a b -> permut0 R l (l1 ++ l2) ->
                   permut0 R (a :: l) (l1 ++ b :: l2).

Lemma permut_nil : 
  forall (A B : Type) (R : A -> B -> Prop) l, permut0 R l nil -> l = nil.
Proof.
intros A B R l P; inversion P as [ | a b l' l1 l2 a_R_b P']; trivial.
destruct l1; discriminate.
Qed.

Lemma permut_impl :
  forall (A B : Type) (R R' : A -> B -> Prop) l1 l2,
  (forall a b, R a b -> R' a b) -> permut0 R l1 l2 -> permut0 R' l1 l2.
Proof.
intros A B R R' l1; induction l1 as [ | a1 l1]; intros l2 Compat P; 
inversion P as [ | a b k k1 k2 a_R_b Q]; subst.
apply Pnil.
apply Pcons.
apply Compat; trivial.
apply IHl1; trivial.
Qed.

Lemma permut_strong :
  forall (A B : Type) (R : A -> B -> Prop) a1 a2 l1 k1 l2 k2,
  R a1 a2 -> permut0 R (l1 ++ k1) (l2 ++ k2) ->
  permut0 R (l1 ++ a1 :: k1) (l2 ++ a2 :: k2).
Proof.
intros A B R a1 a2 l1; induction l1 as [ | u1 l1];
intros k1 l2 k2 a1_R_a2 P.
apply (@Pcons _ _ R a1 a2 k1 l2 k2); trivial.
inversion P as [ | b1 b2 l k k' b1_R_b2 Q]; clear P; subst.
destruct (split_list _ _ _ _ H1) as [H' | H']; clear H1.
destruct H' as [l [H1 H2]]; subst; simpl.
assert (Q' := @Pcons _ _ R u1 b2 (l1 ++ a1 :: k1) (l2 ++ a2 :: l) k' b1_R_b2).
do 2 rewrite <- ass_app in Q'; simpl in Q'; apply Q'.
apply IHl1; trivial.
rewrite ass_app; trivial.
destruct H' as [l [H1 H2]]; subst; simpl.
destruct l as [ | u l].
simpl in H2; subst k2; rewrite <- app_nil_end.
assert (Q' := @Pcons _ _ R u1 b2 (l1 ++ a1 :: k1) (k ++ a2 :: nil) k' b1_R_b2).
do 2 rewrite <- ass_app in Q'; simpl in Q'; apply Q'.
apply IHl1; trivial.
simpl in H2; injection H2; clear H2; intros H2 b2_eq_u; subst u k'.
assert (Q' := @Pcons _ _ R u1 b2 (l1 ++ a1 :: k1) k (l ++ a2 :: k2) b1_R_b2).
rewrite <- ass_app; simpl; apply Q'.
rewrite ass_app; apply IHl1; trivial.
rewrite <- ass_app; trivial.
Qed.

Lemma permut_inv_left_strong :
  forall (A B : Type) (R : A -> B -> Prop) a l1' l1'' l2,
  permut0 R (l1' ++ a :: l1'') l2 -> exists b, exists l2', exists l2'',
   (R a b /\ l2 = l2' ++ b :: l2'' /\ permut0 R (l1' ++ l1'') (l2' ++ l2'')).
Proof.
intros A B R a l1'; generalize a; clear a; 
induction l1' as [ | a1 l1']; intros a l1'' l2 P.
inversion P as [ | a' b l' l2' l2'' a_R_b Q H]; clear P; subst.
exists b; exists l2'; exists l2''; repeat split; trivial.
inversion P as [ | a1' b l' l2' l2'' a1_R_b Q H]; clear P; subst.
destruct (IHl1' _ _ _ Q) as [b' [k2' [k2'' [a_R_b' [H Q']]]]]; clear Q.
destruct (split_list _ _ _ _ H) as [H' | H']; clear H.
destruct H' as [[ | b'' l] [H1 H2]]; simpl in *; subst.
exists b'; exists (k2' ++ b :: nil); exists k2''; repeat split; trivial.
rewrite <- app_nil_end; rewrite <- ass_app; simpl; trivial.
rewrite <- ass_app; simpl; apply Pcons; trivial.
injection H2; clear H2; intros; subst.
exists b''; exists k2'; exists (l ++ b :: l2''); repeat split; trivial.
rewrite <- ass_app; simpl; trivial.
rewrite ass_app; apply Pcons; trivial; rewrite <- ass_app; trivial.
destruct H' as [l [H1 H2]]; subst.
exists b'; exists (l2' ++ b :: l); exists k2''; repeat split; trivial.
rewrite <- ass_app; simpl; trivial.
rewrite <- ass_app.
do 2 rewrite <- app_comm_cons; apply Pcons; trivial; rewrite ass_app; trivial.
Qed.
  
Lemma permut_inv_right :
  forall (A : Type) (R : relation A) b l1 l2,
  permut0 R l1 (b :: l2) -> exists a, exists l1', exists l1'',
   (R a b /\ l1 = l1' ++ a :: l1'' /\ permut0 R (l1' ++ l1'') l2).
Proof.
intros A R b l1; generalize b; clear b; 
induction l1 as [ | a1 l1]; intros b l2 P;
inversion P as [ | a b' l' l1' l2' a_R_b' Q H]; subst.
destruct l1' as [ | a1' l1']; injection H1; clear H1; intros; subst.
exists a1; exists (@nil A); exists l1; repeat split; trivial.
simpl in Q; destruct (IHl1 _ _ Q) as [a [k1' [k1'' [a_R_b [H Q']]]]]; subst.
exists a; exists (a1 :: k1'); exists k1''; repeat split; trivial.
simpl; apply (@Pcons _ _ R a1 b' (k1' ++ k1'') l1' l2'); trivial.
Qed.

Lemma permut_inv_right_strong :
  forall (A B : Type) (R : A -> B -> Prop) b l1 l2' l2'',
  permut0 R l1 (l2' ++ b :: l2'') -> exists a, exists l1', exists l1'',
   (R a b /\ l1 = l1' ++ a :: l1'' /\ permut0 R (l1' ++ l1'') (l2' ++ l2'')).
Proof.
intros A B R b l1; generalize b; clear b; 
induction l1 as [ | a1 l1]; intros b l2' l2'' P;
inversion P as [ | a b' l' l1' k2 a_R_b' Q H]; subst.
destruct l2'; discriminate.
destruct (in_in_split_set _ _ _ _ _ _ H1) as [[H2' | H2'] | H2']; clear H1.
destruct H2' as [l [H2 H3]]; subst.
rewrite <- ass_app in Q; simpl in Q; 
destruct (IHl1 b _ _ Q) as [a [l1' [l1'' [a_R_b [H Q']]]]]; subst.
exists a; exists (a1 :: l1'); exists l1''; repeat split; trivial.
simpl; rewrite ass_app; apply Pcons; trivial.
rewrite <- ass_app; trivial.
destruct H2' as [l [H2 H3]]; subst.
rewrite ass_app in Q.
destruct (IHl1 b _ _ Q) as [a [k1' [k1'' [a_R_b [H Q']]]]]; subst.
exists a; exists (a1 :: k1'); exists k1''; repeat split; trivial.
rewrite <- ass_app; simpl; apply Pcons; trivial.
rewrite ass_app; trivial.
destruct H2' as [b'_eq_b [H2 H3]]; subst.
exists a1; exists (@nil A); exists l1; repeat split; trivial.
Qed.

Lemma permut_rev :
  forall (A B : Type) (R : A -> B -> Prop) l1 l2, permut0 R l1 l2 ->
  permut0 (fun b a => R a b) l2 l1.
Proof.
intros A B R l1; induction l1 as [ | a1 l1]; intros l2 P;
inversion P as [ | a b l1' l2' l2'' a_R_b Q]; subst.
apply Pnil.
apply (@permut_strong B A (fun b a => R a b) b a1 l2' l2'' (@nil _) l1); trivial.
simpl; apply IHl1; trivial.
Qed.

(** Permutation is compatible with length. *)
Lemma permut_length :
  forall (A : Type) (R : relation A) l1 l2, permut0 R l1 l2 -> length l1 = length l2.
Proof.
intros A R l; induction l as [ | a l]; intros l' P; inversion P; trivial.
subst.
rewrite length_app; simpl; rewrite plus_comm; simpl; rewrite plus_comm.
rewrite <- length_app; rewrite (IHl (l1 ++ l2)); trivial.
Qed.

Lemma permut_refl : 
   forall (A : Type) (R : relation A) l, 
  (forall a, In a l -> R a a) -> permut0 R l l.
Proof.
intros A R l refl_R; induction l as [ | a l].
apply Pnil.
apply (@Pcons _ _ R a a l nil l).
apply refl_R; left; trivial.
simpl; apply IHl; intros; apply refl_R; right; trivial.
Qed.

Lemma permut_sym :
  forall (A : Type) (R : relation A) l1 l2,
   (forall a b, In a l1 -> In b l2 -> R a b -> R b a) ->
   permut0 R l1 l2 -> permut0 R l2 l1.
Proof.
intros A R l1; induction l1 as [ | a1 l1]; intros l2 sym_R P;
inversion P as [ | a b l1' l2' l2'' a_R_b Q]; subst.
apply Pnil.
apply (permut_strong (R := R) b a1 l2' l2'' (@nil A) l1).
apply sym_R; trivial; [left | apply in_or_app; right; left]; trivial.
simpl; apply IHl1; trivial.
intros; apply sym_R; trivial; [right | apply in_insert]; trivial.
Qed.

Lemma permut_trans :
  forall (A : Type) (R : relation A) l1 l2 l3,
   (forall a b c, In a l1 -> In b l2 -> In c l3 -> R a b -> R b c -> R a c) ->
   permut0 R l1 l2 -> permut0 R l2 l3 -> permut0 R l1 l3.
Proof.
intros A R l1 l2; generalize l1; clear l1; 
induction l2 as [ | a2 l2]; intros l1 l3 trans_R P1 P2.
inversion_clear P2; trivial.
destruct (permut_inv_right P1) as [a1 [l1' [l1'' [a1_R_a2 [H Q1]]]]]; subst l1.
inversion P2 as [ | a2' a3 l2' l3' l3'' a2_R_a3 Q2]; subst.
apply permut_strong.
apply trans_R with a2; trivial.
apply in_or_app; right; left; trivial.
left; trivial.
apply in_or_app; right; left; trivial.
apply IHl2; trivial.
intros a b c; intros; apply trans_R with b; trivial.
apply in_insert; trivial.
right; trivial.
apply in_insert; trivial.
Qed.

Lemma permut_cons_inside :
  forall (A B : Type) (R : A -> B -> Prop) a b l l1 l2, 
  (forall a1 b1 a2 b2, In a1 (a :: l) -> In b1 (l1 ++ b :: l2) ->
                   In a2 (a :: l) -> In b2 (l1 ++ b :: l2) ->
                   R a1 b1 -> R a2 b1 -> R a2 b2 -> R a1 b2) ->
  R a b -> permut0 R (a :: l) (l1 ++ b :: l2) -> permut0 R l (l1 ++ l2).
Proof.
intros A B R a b l l1 l2 trans_R a_R_b P;
destruct (permut_inv_right_strong (R := R) _ _ _ P) as [a' [l1' [l1'' [a'_R_b [H P']]]]].
destruct l1' as [ | a1' l1']; injection H; clear H; intros; subst; trivial.
inversion P' as [ | a'' b' l' k1' k2' a''_R_b' P'']; subst.
apply permut_strong; trivial.
apply trans_R with b a1'; trivial.
right; apply in_or_app; right; left; trivial.
apply in_or_app; right; left; trivial.
left; trivial.
apply in_insert; rewrite <- H1; apply in_or_app; right; left; trivial.
Qed.

Lemma permut_add_inside :
   forall (A B : Type) (R : A -> B -> Prop) a b l1 l1' l2 l2', 
  (forall a1 b1 a2 b2, In a1 (l1 ++ a :: l1') -> In b1 (l2 ++ b :: l2') ->
                   In a2 (l1 ++ a :: l1') -> In b2 (l2 ++ b :: l2') ->
                   R a1 b1 -> R a2 b1 -> R a2 b2 -> R a1 b2) ->
  R a b -> permut0 R (l1 ++ a :: l1') (l2 ++ b :: l2') -> permut0 R (l1 ++ l1') (l2 ++ l2').
Proof.
intros A B R a b l1 l1' l2 l2' trans_R a_R_b P.
destruct (permut_inv_left_strong (R := R) _ _ _ P) as [b' [k2 [k2' [a_R_b' [H P']]]]].
destruct (in_in_split_set _ _ _ _ _ _ H) as [[H' | H'] | H']; clear H.
destruct H' as [l [H1 H2]]; subst.
rewrite ass_app in P'.
destruct (permut_inv_right_strong (R := R) _ _ _ P') as [a' [k1' [k1'' [a'_R_b' [H P'']]]]].
rewrite H; rewrite <- ass_app; simpl; apply permut_strong.
apply trans_R with b a; trivial.
apply in_insert; rewrite H; apply in_or_app; right; left; trivial.
apply in_or_app; right; left; trivial.
apply in_or_app; right; left; trivial.
apply in_or_app; left; apply in_or_app; right; left; trivial.
rewrite ass_app; trivial.
destruct H' as [l [H1 H2]]; subst.
rewrite <- ass_app in P'; simpl in P'.
destruct (permut_inv_right_strong (R := R) _ _ _ P') as [a' [k1' [k1'' [a'_R_b' [H P'']]]]].
rewrite H; rewrite ass_app; simpl; apply permut_strong.
apply trans_R with b a; trivial.
apply in_insert; rewrite H; apply in_or_app; right; left; trivial.
apply in_or_app; right; left; trivial.
apply in_or_app; right; left; trivial.
apply in_or_app; right; right; apply in_or_app; right; left; trivial.
rewrite <- ass_app; trivial.
destruct H' as [H1 [H2 H3]]; subst; trivial.
Qed.

Lemma exists_dec : 
  forall (A : Type) (P : A -> Prop) (l : list A),
  (forall a, In a l -> {P a}+{~P a}) ->
  {a | In a l /\ P a}+{~exists a, In a l /\ P a}.
Proof.
intros A P l P_dec; induction l as [ | a l].
right; intros [a [a_in_nil _]]; absurd (In a nil); auto.
destruct (P_dec a) as [Pa | not_Pa].
left; trivial.
left; exists a; split; trivial; left; trivial.
destruct IHl as [Ok | Ko].
intros; apply P_dec; right; trivial.
destruct Ok as [b [b_in_l P_b]].
left; exists b; split; trivial; right; trivial.
right; intros [b [[b_eq_a | b_in_l] Pb]].
subst; apply not_Pa; trivial.
apply Ko; exists b; split; trivial.
Defined.

Fixpoint split_all (A : Type) (l : list A) : list (A * (list A * list A)) :=
  match l with
  | nil => @nil _
  | a :: l =>
    (a,(@nil _, l)) :: 
    (map (fun bl' => match bl' with (b,(l',l'')) => (b, (a :: l',l'')) end) (split_all l))
    end.


Lemma split_all_is_sound :
  forall (A : Type) (l  : list A) b l' l'', In (b,(l',l'')) (split_all l) <-> l = l' ++ b :: l''.
Proof.
intros A l; induction l as [ | a l]; intros b l' l''.
split; intro H.
contradiction.
destruct l'; discriminate.
simpl; split; intro H.
rewrite in_map_iff in H; destruct H as [ H | H ].
injection H; intros; subst; trivial.
destruct H as [[c [k' k'']] [H H']].
injection H; intros; subst.
simpl; apply (f_equal (fun l => a :: l)).
rewrite <- (IHl b k' l''); trivial.
rewrite in_map_iff; destruct l' as [ | a' l'];
simpl in H; injection H; intros; subst.
left; trivial.
right; exists (b,(l',l'')); split; trivial.
rewrite (IHl b l' l''); trivial.
Qed.

Lemma permut_dec :
  forall (A B : Type) (R : A -> B -> Prop),
          forall l1 l2, (forall a1 a2, In a1 l1 -> In a2 l2 -> {R a1 a2}+{~R a1 a2}) ->
         {permut0 R l1 l2}+{~permut0 R l1 l2}.
Proof.
intros A B R l1; induction l1 as [ | a1 l1]; intros l2 R_dec.
revert R_dec. destruct l2 as [ | a2 l2].
left; apply Pnil.
right; intro P; inversion P.
assert (P_dec : forall a : B * (list B * list B),
  In a (split_all l2) ->
  {(fun bll' : B * (list B * list B) =>
    let (b, y) := bll' in let (l, l') := y in R a1 b /\ permut0 R l1 (l ++ l'))
     a} +
  {~
   (fun bll' : B * (list B * list B) =>
    let (b, y) := bll' in let (l, l') := y in R a1 b /\ permut0 R l1 (l ++ l'))
     a}).
intros [b [l l']] H; rewrite split_all_is_sound in H.
destruct (R_dec a1 b) as [a1_R_b | not_a1_R_b].
left; trivial.
subst l2; apply in_or_app; right; left; trivial.
destruct (IHl1 (l ++ l')) as [P | not_P].
intros; apply R_dec.
right; trivial.
subst l2; apply in_insert; trivial.
left; split; trivial.
right; intros [_ P]; apply not_P; trivial.
right; intros [a1_R_b _]; apply not_a1_R_b; trivial.

assert (H := list_exists_rest_is_sound 
                       (fun bll' =>
                           match bll' with
                           | (b,(l,l')) => R a1 b /\ permut0 R l1 (l ++ l')
                           end) (split_all l2) P_dec).
destruct (list_exists_rest
      (fun bll' : B * (list B * list B) =>
       let (b, y) := bll' in
       let (l, l') := y in R a1 b /\ permut0 R l1 (l ++ l')) (split_all l2) P_dec).
left.
destruct ((proj1 H) (eq_refl _)) as [[b [l l']] [H' [a1_R_b P]]].
rewrite split_all_is_sound in H'; subst l2; apply Pcons; trivial.
right; intro P; inversion P; subst.
assert (false = true).
rewrite H; exists (b,(l0,l3)); split; trivial.
rewrite split_all_is_sound; trivial.
split; trivial.
discriminate.
Defined.

Lemma permut_map :
  forall (A B A' B': Type) (R : A -> B -> Prop) (R' : A' -> B' -> Prop) (f1 : A -> A') (f2 : B -> B') 
  l1 l2, (forall a b, In a l1 -> In b l2 -> R a b -> R' (f1 a) (f2 b)) ->
  permut0 R l1 l2 -> permut0 R' (map f1 l1) (map f2 l2).
Proof.
intros A B A' B' R R' f1 f2 l1; induction l1 as [ | a1 l1]; 
intros l2 Compat P; inversion P as [ | a' b l1' l2' l2'' a_R_b P' H]; subst.
simpl; apply Pnil.
rewrite map_app; simpl; apply Pcons.
apply Compat; trivial.
left; trivial.
apply in_or_app; right; left; trivial.
rewrite <- map_app; apply IHl1; trivial.
intros a b' a_in_l1 b'_in_l2; apply Compat.
right; trivial.
apply in_insert; trivial.
Qed.

Lemma permut_length_1:
  forall (A B : Type) (R : A -> B -> Prop) a b, permut0 R (a :: nil) (b :: nil)  -> R a b.
Proof.
intros A B R a b P; inversion P as [ | a' b' l' l1' l2' a_R_b' P' H1 H']; subst.
destruct l1' as [ | a1' [ | b1' l1']].
injection H'; intros; subst; trivial.
discriminate.
discriminate.
Qed.

Lemma permut_length_2 :
 forall (A B : Type) (R : A -> B -> Prop) a1 b1 a2 b2, 
    permut0 R (a1 :: b1 :: nil) (a2 :: b2 :: nil) ->
    (R a1 a2 /\ R b1 b2) \/ (R a1 b2 /\ R b1 a2).
Proof.
intros A B R a1 b1 a2 b2 P;
inversion P as [ | a b l l1 l2 a_R_b P' H1 H']; subst. 
destruct l1 as [ | c1 l1].
destruct l2 as [ | c2 [ | d2 l2]].
discriminate.
injection H'; intros; subst.
left; split; trivial.
apply (permut_length_1 P').
discriminate.
destruct l1 as [ | d1 l1].
destruct l2 as [ | c2 l2].
injection H'; intros; subst.
right; split; trivial.
apply (permut_length_1 P').
discriminate.
destruct l1; discriminate.
Qed.

Lemma permut_size :
  forall (A B : Type) (R : A -> B -> Prop) size size' l1 l2, 
  (forall a a', In a l1 -> In a' l2 -> R a a' -> size a = size' a') ->
  permut0 R l1 l2 -> list_size size l1 = list_size size' l2.
Proof.
intros A B R size size' l1; induction l1 as [ | a1 l1 ]; intros l2 E P;
inversion P as [ | a b l1' l2' l2'' a_R_b P']; subst; trivial.
rewrite list_size_app; simpl.
rewrite (E a1 b); trivial.
rewrite (IHl1 (l2' ++ l2'')); trivial.
rewrite list_size_app; simpl.
rewrite plus_comm.
rewrite <- plus_assoc.
apply (f_equal (fun n => list_size size' l2' + n)).
apply plus_comm.
intros a a' a_in_la a_in_l'; apply E; trivial.
right; trivial.
apply in_insert; trivial.
left; trivial.
apply in_or_app; right; left; trivial.
Qed.

Lemma in_permut_in :
   forall (A : Type) l1 l2, permut0 (@eq A) l1 l2 -> (forall a, In a l1 <-> In a l2).
Proof. 
assert (H : forall (A : Type) l1 l2, permut0 (@eq A) l1 l2 -> forall a, In a l2 -> In a l1).
intros A l1 l2 P a a_in_l2;
destruct (In_split _ _ a_in_l2) as [l2' [l2'' H]]; subst.
destruct (permut_inv_right_strong (R := @eq A) _ _ _ P) 
  as [a' [l1' [l1'' [a_eq_a' [H _]]]]]; subst.
apply in_or_app; right; left; trivial.
intros A l1 l2 P a; split; apply H; trivial.
apply permut_sym; trivial; intros; subst; trivial.
Qed.

(** Permutation is compatible with append. *)
Lemma permut_app :
  forall (A B : Type) (R : A -> B -> Prop) l1 l1' l2 l2',
   permut0 R l1 l2 -> permut0 R l1' l2' -> permut0 R (l1 ++ l1') (l2 ++ l2').
Proof.
intros A B R l1; induction l1 as [ | a1 l1];
intros l1' l2 l2' P P'.
inversion_clear P; trivial.
inversion P as [ | a b l1'' l2'' l2''' a_R_b Q]; subst.
simpl; rewrite <- ass_app; simpl; apply Pcons; trivial.
rewrite ass_app; apply IHl1; trivial.
Qed.

Lemma permut_swapp :
  forall (A B : Type) (R : A -> B -> Prop) l1 l1' l2 l2',
   permut0 R l1 l2 -> permut0 R l1' l2' -> permut0 R (l1 ++ l1') (l2' ++ l2).
Proof.
intros A B R l1; induction l1 as [ | a1 l1];
intros l1' l2 l2' P P'.
inversion_clear P; rewrite <- app_nil_end; trivial.
inversion P as [ | a b l1'' l2'' l2''' a_R_b Q]; subst.
simpl; rewrite ass_app; apply Pcons; trivial.
rewrite <- ass_app; apply IHl1; trivial.
Qed.

Lemma permut_app1 :
  forall (A : Type) (R : relation A), Equivalence R ->
  forall l l1 l2, permut0 R l1 l2 <-> permut0 R (l ++ l1) (l ++ l2).
Proof.
intros A R E l l1 l2; split; intro P.
(* -> case *)
induction l as [ | u l]; trivial.
simpl; apply (@Pcons _ _ R u u (l ++ l1) (@nil A) (l ++ l2)); trivial.
reflexivity.
(* <- case *)
induction l as [ | u l]; trivial.
apply IHl.
apply (@permut_cons_inside A A R u u (l ++ l1) (@nil _) (l ++ l2)); trivial.
intros a1 b1 a2 b2 _ _ _ _ a1_R_b1 a2_R_b1 a2_R_b2.
transitivity b1; trivial.
transitivity a2; trivial.
symmetry; trivial.
reflexivity.
Qed.

Lemma permut_app2 :
  forall (A : Type) (R : relation A), Equivalence R ->
  forall l l1 l2, permut0 R l1 l2 <-> permut0 R (l1 ++ l) (l2 ++ l).
Proof.
intros A R E l l1 l2; split; intro P.
(* -> case *)
induction l as [ | u l].
do 2 rewrite <- app_nil_end; trivial.
apply permut_strong; trivial.
reflexivity.

(* <- case *)
induction l as [ | u l].
do 2 rewrite <- app_nil_end in P; trivial.
apply IHl.
apply (@permut_add_inside A A R u u); trivial.
intros a1 b1 a2 b2 _ _ _ _ a1_R_b1 a2_R_b1 a2_R_b2;
transitivity b1; trivial.
transitivity a2; trivial.
symmetry; trivial.
reflexivity.
Qed.

Lemma permut_list_exists :
  forall  (A B : Type) (R : A -> B -> Prop) f f',  (forall t t', R t t' -> f t = f' t') ->
  forall l l', permut0 R l l' -> list_exists f l = list_exists f' l'.
Proof.
intros A B R f f' E l; induction l as [ | a l]; simpl; intros l' P;
inversion P as [ | a' b l1 l2' l2'' a_R_b Q]; subst; simpl; trivial.
rewrite list_exists_app; simpl.
rewrite (E _ _ a_R_b).
destruct (f' b); simpl.
destruct (list_exists f' l2'); simpl; trivial.
rewrite <- list_exists_app; apply IHl; trivial.
Qed.

Lemma permut_list_forall_exists :
  forall (A B A' B': Type) (R : A -> B -> Prop) (R' : A' -> B' -> Prop) f f',  
  (forall ta ta' tb tb', R ta tb -> R' ta' tb' -> f ta ta' = f' tb tb') ->
  forall la la' lb lb',  permut0 R la lb -> permut0 R' la' lb' -> 
  list_forall (fun t1 => list_exists (fun t2 => f t1 t2) la') la = 
  list_forall (fun t1 => list_exists (fun t2 => f' t1 t2) lb') lb. 
Proof.
intros A B A' B' R R' f f' E la; induction la as [ | a la];
intros la' lb lb' P P';
inversion P as [ | a' b k1 k2' k2'' a_R_b Q]; subst; simpl; trivial.
rewrite list_forall_app; simpl.
rewrite (IHla la' (k2' ++ k2'') lb' Q P').
rewrite list_forall_app; simpl.
assert (E' : forall (t : A') (t' : B'), R' t t' -> f a t = f' b t'). 
intros; apply E; trivial.
rewrite (@permut_list_exists _ _ R' (fun t2 : A' => f a t2) (fun t2 : B' => f' b t2) E' _ _ P').
destruct (list_exists (fun t2 : B' => f' b t2) lb'); simpl; trivial.
destruct (list_forall (fun t1 : B => list_exists (fun t2 : B' => f' t1 t2) lb') k2'); simpl; trivial.
Qed.




Section Srel. 
  Variable A : Type.
  Variable eq_A : relation A.
  Variable eq_proof : Equivalence eq_A.
  Lemma mem_permut0_mem :
    forall  l1 l2 (a:A), permut0 eq_A l1 l2 -> (mem eq_A a l1 <-> mem eq_A a l2).
  Proof. 
    intros l1 l2 a H.
    assert (forall l1 l2 e, permut0 eq_A l1 l2 -> mem eq_A e l1 -> mem eq_A e l2).
    clear - eq_proof.
    intro l1; induction l1 as [ | a1 l1]; intros l2 e P e_mem_l1.
    contradiction.
    inversion P as [ | a' b l' l1' l2' a1_eq_b P' H1 H']; subst.
    destruct e_mem_l1 as [e_eq_a1 | e_mem_l1].
    rewrite <- mem_or_app.
    right; left; transitivity a1; trivial.
    apply mem_insert; apply IHl1; trivial.
    split; apply H0; trivial.
    apply permut_sym; trivial.
    intros a0 b _ _ a_eq_b; symmetry; trivial.
  Qed.

  
  Lemma permut0_refl : forall l, permut0 eq_A l l.
  Proof.
    intro l; apply permut_refl.
    intros a _; reflexivity.
  Qed.

  Lemma permut0_sym : forall l1 l2, permut0 eq_A l1 l2 -> permut0 eq_A l2 l1.
  Proof.
    intros l1 l2 P; apply permut_sym; trivial.
    intros a b _ _ a_eq_b; symmetry; trivial.
  Qed.

  Lemma permut0_trans : 
    forall l1 l2 l3 : list A, permut0 eq_A l1 l2 -> permut0 eq_A l2 l3 -> permut0 eq_A l1 l3.
  Proof.
  intros l1 l2 l3 P1 P2; apply permut_trans with l2; trivial.
  intros a b c _ _ _ a_eq_b b_eq_c; transitivity b; trivial.
  Qed.


  Lemma mem_morph0 : 
   forall x y : A, eq_A x y ->
   forall x0 y0 : list A, permut0 eq_A x0 y0 -> (mem eq_A x x0 <-> mem eq_A y y0).
   Proof.
    intros e1 e2 e1_eq_e2 l1 l2 P.
    rewrite (mem_permut0_mem e1 P).
    clear l1 P; assert (H : forall e1 e2, eq_A e1 e2 -> mem eq_A e1 l2 -> mem eq_A e2 l2).
    clear e1 e2 e1_eq_e2; intros e1 e2 e1_eq_e2;
    induction l2 as [ | a l]; simpl; trivial.
    intros [e1_eq_a | e1_mem_l]; [left | right; trivial].
    transitivity e1; trivial.
    symmetry; trivial.
    apply IHl; trivial.
    split; apply H; trivial.
    symmetry; trivial.
  Qed.


  Lemma cons_permut0_mem :
    forall l1 l2 e1 e2, eq_A e1 e2 -> permut0 eq_A (e1 :: l1) l2 -> mem eq_A e2 l2.
  Proof.
    intros l1 l2 e1 e2 e1_eq_e2 P.
    apply (proj1 (mem_morph0 e1_eq_e2 P)).
    left; reflexivity.
  Qed.

  
 Lemma permut0_cons :
    forall e1 e2 l1 l2, eq_A e1 e2 -> 
      (permut0 eq_A l1 l2 <-> permut0 eq_A (e1 :: l1) (e2 :: l2)).
  Proof.
    intros e1 e2 l1 l2 e1_eq_e2; split; intro P.
    apply (@Pcons _ _ eq_A e1 e2 l1 (@nil A) l2); trivial.
    replace l2 with (nil ++ l2); trivial;
    apply permut_cons_inside with e1 e2; trivial.
    intros a1 b1 a2 b2 _ _ _ _ a1_eq_b1 a2_eq_b1 a2_eq_b2;
    transitivity a2; trivial.
    transitivity b1; trivial.
    symmetry; trivial.
  Qed.

 Lemma permut0_add_inside :
    forall e1 e2 l1 l2 l3 l4,  eq_A e1 e2 -> 
      (permut0 eq_A (l1 ++ l2) (l3 ++ l4) <->
      permut0 eq_A (l1 ++ e1 :: l2) (l3 ++ e2 :: l4)).
  Proof.
  intros e1 e2 l1 l2 l3 l4 e1_eq_e2; split; intro P.
  apply permut_strong; trivial.
  apply permut_add_inside with e1 e2; trivial.
  intros a1 b1 a2 b2 _ _ _ _ a1_eq_b1 a2_eq_b1 a2_eq_b2;
  transitivity a2; trivial.
  transitivity b1; trivial.
  symmetry; trivial.
  Qed.

  Lemma permut0_cons_inside :
    forall e1 e2 l l1 l2, eq_A e1 e2 ->
      (permut0 eq_A l (l1 ++ l2) <-> permut0 eq_A (e1 :: l) (l1 ++ e2 :: l2)).
  Proof.
    intros e1 e2 l l1 l2 e1_eq_e2.  
    apply (permut0_add_inside nil l l1 l2 e1_eq_e2).
  Qed.


(** Permutation is compatible with append. *)
Lemma permut0_app1 :
  forall l l1 l2, permut0 eq_A l1 l2 <-> permut0 eq_A (l ++ l1) (l ++ l2).
Proof.
intros l l1 l2; apply permut_app1.
apply eq_proof.
Qed.

Lemma permut0_app2 :
  forall l l1 l2, permut0 eq_A l1 l2 <-> permut0 eq_A (l1 ++ l) (l2 ++ l).
Proof.
intros l l1 l2; apply permut_app2.
apply eq_proof.
Qed.


End Srel.

#[global] Instance LP (A:Type) (eq_A:relation A) (eq_proof: Equivalence eq_A) :
  Equivalence (permut0 eq_A).

Proof.
  split; intro x.
  apply permut0_refl; assumption.
  apply permut0_sym; assumption.
  apply permut0_trans; assumption.
Qed.

#[global] Instance mem_morph2 (A:Type) (eq_A:relation A) (eq_proof: Equivalence eq_A) :
  Proper (eq_A ==> permut0 eq_A ==> iff) (mem eq_A).

Proof. exact (mem_morph0 eq_proof). Qed.

#[global] Instance add_A_morph (A:Type) (eq_A:relation A) (eq_proof: Equivalence eq_A):
  Proper (eq_A ==> permut0 eq_A ==> permut0 eq_A) (List.cons (A:=A)).

Proof.
  intros e1 e2 e1_eq_e2 l1 l2 P;
  rewrite <- (@permut0_cons _ _ eq_proof e1 e2 l1 l2); trivial.
Qed.

#[global] Instance app_morph (A:Type) (eq_A:relation A) (eq_proof: Equivalence eq_A) :
  Proper (permut0 eq_A ==> permut0 eq_A ==> permut0 eq_A) (List.app (A:=A)).

Proof.
intros l1 l2 P l1' l2' P'.
apply (permut0_trans eq_proof) with (l1 ++ l2').
rewrite <- permut_app1; trivial.
rewrite <- permut_app2; trivial.
Qed.

Section SRel2.
  Variable A : Type.
  Variable eq_A : relation A.
  Variable eq_proof : Equivalence eq_A.
  Variable eq_bool : A -> A -> bool.
  Hypothesis eq_bool_ok : 
    forall t1 t2, match eq_bool t1 t2 with true => eq_A t1 t2 | false => ~eq_A t1 t2 end.

Lemma ac_syntactic_aux :
 forall (l1 l2 l3 l4 : list A),
 permut0 eq_A (l1 ++ l2) (l3 ++ l4) ->
 (exists u1, exists u2, exists u3, exists u4, 
 permut0 eq_A l1 (u1 ++ u2) /\
 permut0 eq_A l2 (u3 ++ u4) /\
 permut0 eq_A l3 (u1 ++ u3) /\
 permut0 eq_A l4 (u2 ++ u4)).
Proof.
induction l1 as [ | a1 l1]; intros l2 l3 l4 P.
exists (nil : list A); exists (nil : list A); exists l3; exists l4; simpl.
repeat split.
apply (permut0_refl eq_proof).
intuition.
apply (permut0_refl eq_proof).
apply (permut0_refl eq_proof).

simpl in P.

assert (a1_in_l3l4 := @cons_permut0_mem _ _ eq_proof _ _ _ _ (@Equivalence_Reflexive _ _ eq_proof a1) P).
rewrite <- mem_or_app in a1_in_l3l4;
destruct a1_in_l3l4 as [a1_in_l3 | a1_in_l4].
generalize (mem_split_set _ _ eq_bool_ok _ _ a1_in_l3).
intros [a1' [l3' [l3'' [a1_eq_a1' [H _]]]]]; 
simpl in a1_eq_a1'; simpl in H; subst l3.
rewrite app_ass in P; rewrite <- app_comm_cons in P;
rewrite <- permut0_cons_inside in P; trivial.
rewrite <- app_ass in P;
destruct (IHl1 l2 (l3' ++ l3'') l4 P) as [u1 [u2 [u3 [u4 [P1 [P2 [P3 P4]]]]]]].
exists (a1 :: u1); exists u2; exists u3; exists u4; repeat split; simpl; trivial.
rewrite <- permut0_cons; trivial; reflexivity.
apply (permut0_sym eq_proof).  rewrite <- permut0_cons_inside; auto.
apply (permut0_sym eq_proof). assumption.


generalize (mem_split_set _ _ eq_bool_ok _ _ a1_in_l4).
intros [a1' [l4' [l4'' [a1_eq_a1' [H _]]]]]; 
simpl in a1_eq_a1'; simpl in H; subst l4.
rewrite <- app_ass in P; 
rewrite <- permut0_cons_inside in P; trivial.
rewrite app_ass in P;
destruct (IHl1 l2 l3 (l4' ++ l4'') P) as [u1 [u2 [u3 [u4 [P1 [P2 [P3 P4]]]]]]];
exists u1; exists (a1 :: u2); exists u3; exists u4; intuition; simpl; trivial.
rewrite <- permut0_cons_inside; trivial. reflexivity.
apply permut0_sym; [constructor;auto with typeclass_instances|].
rewrite <- permut0_cons_inside; trivial.
apply permut0_sym; trivial.
Qed.


Lemma list_permut0_app_app :
 forall l1 l2, permut0 eq_A (l1 ++ l2) (l2 ++ l1).
Proof.
intros l1 l2; apply permut_swapp;apply permut0_refl;assumption.
Qed.

Lemma ac_syntactic :
 forall (l1 l2 l3 l4 : list A),
 permut0 eq_A (l2 ++ l1) (l4 ++ l3) ->
 (exists u1, exists u2, exists u3, exists u4, 
 permut0 eq_A l1 (u1 ++ u2) /\
 permut0 eq_A l2 (u3 ++ u4) /\
 permut0 eq_A l3 (u1 ++ u3) /\
 permut0 eq_A l4 (u2 ++ u4)).
Proof.
intros l1 l2 l3 l4 P; apply ac_syntactic_aux.
apply permut0_trans with (l2 ++ l1). assumption.
apply list_permut0_app_app.
apply permut0_trans with (l4 ++ l3); trivial.
apply list_permut0_app_app.
Qed.


End SRel2.




Module Type S.

  Declare Module Import EDS : decidable_set.ES.
  Notation permut := (permut0 eq_A).

(* Theorem list_permut_refl *)
 Parameter permut_refl :
    forall (l : list A), permut l l.

 (* Theorem list_permut_sym *)
 Parameter permut_sym :
    forall l1 l2 : list A, permut l1 l2 -> permut l2 l1.

(* Theorem list_permut_trans *)
  Parameter permut_trans :
    forall l1 l2 l3 : list A, permut l1 l2 -> permut l2 l3 -> permut l1 l3.

  #[global] Hint Immediate permut_refl : core.
  #[global] Hint Resolve permut_sym : core.

(* Theorem mem_permut_mem *)
 Parameter mem_permut_mem :
    forall l1 l2 e, permut l1 l2 -> (mem eq_A e l1 <-> mem eq_A e l2).

(* Theorem cons_permut_mem *)
   Parameter cons_permut_mem :
    forall l1 l2 e1 e2, eq_A e1 e2 -> permut (e1 :: l1) l2 -> mem eq_A e2 l2.

(* Theorem permut_cons *)
  Parameter permut_cons :
    forall e1 e2 l1 l2, eq_A e1 e2 -> 
      (permut l1 l2 <-> permut (e1 :: l1) (e2 :: l2)).

(* Theorem permut_add_inside *)
   Parameter permut_add_inside :
    forall e1 e2 l1 l2 l3 l4,  eq_A e1 e2 -> 
      (permut (l1 ++ l2) (l3 ++ l4) <->
      permut (l1 ++ e1 :: l2) (l3 ++ e2 :: l4)).

(* Theorem permut_cons_inside *)
  Parameter permut_cons_inside :
    forall e1 e2 l l1 l2, eq_A e1 e2 ->
      (permut l (l1 ++ l2) <-> permut (e1 :: l) (l1 ++ e2 :: l2)).

(* Theorem permut_app1 *)
 Parameter permut_app1 :
  forall l l1 l2, permut l1 l2 <-> permut (l ++ l1) (l ++ l2).

(* Theorem permut_app2 *)
Parameter permut_app2 :
  forall l l1 l2, permut l1 l2 <-> permut (l1 ++ l) (l2 ++ l).

(* Theorem list_permut_app_app *)
 Parameter list_permut_app_app :
 forall l1 l2, permut (l1 ++ l2) (l2 ++ l1).

Definition permut_bool :=
              (fix permut_bool (kk1 kk2 : list A) {struct kk1} :  bool :=  
               (match kk1 with
               | nil => match kk2 with nil => true | _ :: _=> false end
               | t1 :: k1 => 
                     match remove EDS.eq_bool t1 kk2 with 
                           None => false 
                         | Some k2 => permut_bool k1 k2 end
                         end)).

Parameter permut_bool_ok : 
forall l1 l2, match permut_bool l1 l2 with true => permut l1 l2 | false => ~permut l1 l2 end.

(* Theorem ac_syntactic *)
 Parameter ac_syntactic :
 forall (l1 l2 l3 l4 : list A),
 permut (l2 ++ l1) (l4 ++ l3) ->
 (exists u1, exists u2, exists u3, exists u4, 
 permut l1 (u1 ++ u2) /\
 permut l2 (u3 ++ u4) /\
 permut l3 (u1 ++ u3) /\
 permut l4 (u2 ++ u4)).

(*  Theorem remove_is_sound *)
Parameter remove_is_sound :
  forall x l, match remove eq_bool x l with
                | None => ~mem eq_A x l
                | Some l' => permut l (x :: l')
                end.

Parameter remove_equiv_nil_2 : forall l, remove_equiv eq_bool l nil = (l,nil).

(*  Theorem remove_equiv_is_sound *)
Parameter remove_equiv_is_sound: 
  forall l1 l2, match remove_equiv eq_bool l1 l2 with
  | (l1', l2') => exists l, permut l1 (l ++ l1') /\ permut l2 (l ++ l2') /\
                        (forall x, mem eq_A x l1' -> mem eq_A x l2' -> False)
  end.

Parameter remove_equiv_is_complete :
  forall l1 l2 l l1' l2', permut l1 (l ++ l1') -> permut l2 (l ++ l2') ->
                        (forall x, mem eq_A x l1' -> mem eq_A x l2' -> False) ->
    (permut (fst (remove_equiv eq_bool l1 l2)) l1' /\ permut (snd (remove_equiv eq_bool l1 l2)) l2').

Parameter remove_equiv_permut:
  forall l1 l1' l2 l2', permut l1 l1' -> permut l2 l2' -> 
      permut (fst (remove_equiv eq_bool l1 l2))  (fst (remove_equiv eq_bool l1' l2')) /\
          permut (snd (remove_equiv eq_bool l1 l2)) (snd (remove_equiv eq_bool l1' l2')).

#[global] Instance LP : Equivalence permut.

Proof.
  split; intro x. apply permut_refl. apply permut_sym. apply permut_trans.
Qed.

#[global] Declare Instance mem_morph2 : Proper (eq_A ==> permut ==> iff) (mem eq_A).

#[global] Declare Instance app_morph : Proper (permut ==> permut ==> permut) (@app A).

#[global] Declare Instance add_A_morph : Proper (eq_A ==> permut ==> permut) (@cons A).

End S.



(** ** Definition of permutation over lists. *)
Module Make (EDS1 : decidable_set.ES) : S with Module EDS:= EDS1. 

  Module Import EDS <: decidable_set.ES := EDS1.
  Notation permut := (permut0 eq_A).

(** ** Permutation is a equivalence relation. 
      Reflexivity. *)
  Theorem permut_refl :  forall (l : list A), permut l l.
  Proof.
  intro l; apply permut_refl.
  intros a _; reflexivity.
  Qed.

  (** Symetry. *)
  Theorem permut_sym : forall l1 l2 : list A, permut l1 l2 -> permut l2 l1.
  Proof.
  intros l1 l2 P; apply permut_sym; trivial.
  intros a b _ _ a_eq_b; symmetry; trivial.
  Qed.

  #[global] Hint Immediate permut_refl : core.
  #[global] Hint Resolve permut_sym : core.

  (** Transitivity. *)
  Theorem permut_trans :
    forall l1 l2 l3 : list A, permut l1 l2 -> permut l2 l3 -> permut l1 l3.
  Proof.
  intros l1 l2 l3 P1 P2; apply permut_trans with l2; trivial.
  intros a b c _ _ _ a_eq_b b_eq_c; transitivity b; trivial.
  Qed.

  #[global] Instance LP : Equivalence permut.

  Proof.
    split; intro x. apply permut_refl. apply permut_sym. apply permut_trans.
  Qed.

  (** ** Compatibility Properties. 
      Permutation is compatible with mem. *)
  Lemma mem_permut_mem :
    forall l1 l2 e, permut l1 l2 -> (mem eq_A e l1 <-> mem eq_A e l2).
  Proof.
    assert (forall l1 l2 e, permut l1 l2 -> mem eq_A e l1 -> mem eq_A e l2).
    intro l1; induction l1 as [ | a1 l1]; intros l2 e P e_mem_l1.
    contradiction.
    inversion P as [ | a' b l' l1' l2' a1_eq_b P' H1 H']; subst.
    destruct e_mem_l1 as [e_eq_a1 | e_mem_l1].
    rewrite <- mem_or_app.
    right; left; transitivity a1; trivial.
    apply mem_insert; apply IHl1; trivial.
    intros l1 l2 e P; split; apply H; trivial.
    apply permut_sym; trivial.
  Qed.

Lemma mem_morph : 
   forall x y : EDS1.A, EDS1.eq_A x y ->
   forall x0 y0 : list EDS1.A, permut x0 y0 -> (mem EDS1.eq_A x x0 <-> mem EDS1.eq_A y y0).
   Proof.
    intros e1 e2 e1_eq_e2 l1 l2 P.
    rewrite (mem_permut_mem e1 P).
    clear l1 P; assert (H : forall e1 e2, eq_A e1 e2 -> mem eq_A e1 l2 -> mem eq_A e2 l2).
    clear e1 e2 e1_eq_e2; intros e1 e2 e1_eq_e2;
    induction l2 as [ | a l]; simpl; trivial.
    intros [e1_eq_a | e1_mem_l]; [left | right; trivial].
    transitivity e1; trivial.
    symmetry; trivial.
    apply IHl; trivial.
    split; apply H; trivial.
    symmetry; trivial.
  Qed.


#[global] Instance mem_morph2 : Proper (eq_A ==> permut ==> iff) (mem eq_A).

Proof. exact mem_morph. Qed.

  Lemma cons_permut_mem :
    forall l1 l2 e1 e2, eq_A e1 e2 -> permut (e1 :: l1) l2 -> mem eq_A e2 l2.
  Proof.
    intros l1 l2 e1 e2 e1_eq_e2 P.
    apply (proj1 (mem_morph e1_eq_e2 P)).
    left; reflexivity.
Qed.

  (** Permutation is compatible with addition and removal of common elements *)
  
 Lemma permut_cons :
    forall e1 e2 l1 l2, eq_A e1 e2 -> 
      (permut l1 l2 <-> permut (e1 :: l1) (e2 :: l2)).
  Proof.
    intros e1 e2 l1 l2 e1_eq_e2; split; intro P.
    apply (@Pcons _ _ eq_A e1 e2 l1 (@nil A) l2); trivial.
    replace l2 with (nil ++ l2); trivial;
    apply permut_cons_inside with e1 e2; trivial.
    intros a1 b1 a2 b2 _ _ _ _ a1_eq_b1 a2_eq_b1 a2_eq_b2;
    transitivity a2; trivial.
    transitivity b1; trivial.
    symmetry; trivial.
     Qed.

  #[global] Instance add_A_morph : Proper (eq_A ==> permut ==> permut) (List.cons (A:=A)).

  Proof.
    intros e1 e2 e1_eq_e2 l1 l2 P;
      rewrite <- (@permut_cons e1 e2 l1 l2); trivial.
  Qed.

 Lemma permut_add_inside :
    forall e1 e2 l1 l2 l3 l4,  eq_A e1 e2 -> 
      (permut (l1 ++ l2) (l3 ++ l4) <->
      permut (l1 ++ e1 :: l2) (l3 ++ e2 :: l4)).
  Proof.
  intros e1 e2 l1 l2 l3 l4 e1_eq_e2; split; intro P.
  apply permut_strong; trivial.
  apply permut_add_inside with e1 e2; trivial.
  intros a1 b1 a2 b2 _ _ _ _ a1_eq_b1 a2_eq_b1 a2_eq_b2;
  transitivity a2; trivial.
  transitivity b1; trivial.
  symmetry; trivial.
  Qed.

  Lemma permut_cons_inside :
    forall e1 e2 l l1 l2, eq_A e1 e2 ->
      (permut l (l1 ++ l2) <-> permut (e1 :: l) (l1 ++ e2 :: l2)).
  Proof.
    intros e1 e2 l l1 l2 e1_eq_e2; apply (permut_add_inside nil l l1 l2 e1_eq_e2).
  Qed.


(** Permutation is compatible with append. *)
Lemma permut_app1 :
  forall l l1 l2, permut l1 l2 <-> permut (l ++ l1) (l ++ l2).
Proof.
intros l l1 l2; apply permut_app1. apply EDS.EQA.
Qed.

Lemma permut_app2 :
  forall l l1 l2, permut l1 l2 <-> permut (l1 ++ l) (l2 ++ l).
Proof.
intros l l1 l2; apply permut_app2. apply EDS.EQA.
Qed.

#[global] Instance app_morph : Proper (permut ==> permut ==> permut) (List.app (A:=A)).

Proof.
intros l1 l2 P l1' l2' P'.
apply permut_trans with (l1 ++ l2').
rewrite <- permut_app1; trivial.
rewrite <- permut_app2; trivial.
Qed.

Lemma list_permut_app_app :
 forall l1 l2, permut (l1 ++ l2) (l2 ++ l1).
Proof.
intros l1 l2; apply permut_swapp; apply permut_refl.
Qed.

Definition permut_bool :=
              (fix permut_bool (kk1 kk2 : list A) {struct kk1} :  bool :=  
               (match kk1 with
               | nil => match kk2 with nil => true | _ :: _=> false end
               | t1 :: k1 => 
                     match remove EDS1.eq_bool t1 kk2 with 
                           None => false 
                         | Some k2 => permut_bool k1 k2 end
                         end)).

Lemma permut_bool_ok : 
forall l1 l2, match permut_bool l1 l2 with true => permut l1 l2 | false => ~permut l1 l2 end.
Proof.
fix permut_bool_ok 1.
intro l1; case l1; clear l1.
intro l2; case l2; clear l2.
simpl; apply Pnil.
intros a2 l2 P; inversion P.
intros a1 l1 l2; simpl.
generalize (in_remove _ _ EDS1.eq_bool_ok a1 l2); case (remove eq_bool a1 l2).
intros k2 [a2 [l2' [l2'' [a1_eq_a2 [H H']]]]]; injection H'; clear H'; intro H'.
generalize (permut_bool_ok l1 k2); case (permut_bool l1 k2).
intro P; subst; apply Pcons; assumption.
intros not_P P'; apply not_P.
subst k2; rewrite (permut_cons_inside l1 l2' l2'' a1_eq_a2); subst l2; apply P'.
intros a1_diff_a2 P; apply a1_diff_a2.
rewrite <- (mem_permut_mem a1 P); left.
reflexivity.
Qed.

(** ** Link with AC syntactic decomposition.*)
Lemma ac_syntactic_aux :
 forall (l1 l2 l3 l4 : list A),
 permut (l1 ++ l2) (l3 ++ l4) ->
 (exists u1, exists u2, exists u3, exists u4, 
 permut l1 (u1 ++ u2) /\
 permut l2 (u3 ++ u4) /\
 permut l3 (u1 ++ u3) /\
 permut l4 (u2 ++ u4)).
Proof.
induction l1 as [ | a1 l1]; intros l2 l3 l4 P.
exists (nil : list A); exists (nil : list A); exists l3; exists l4; simpl; intuition. 

simpl in P.

assert (a1_in_l3l4 := cons_permut_mem (equiv_refl _ _ eq_proof a1) P).
rewrite <- mem_or_app in a1_in_l3l4;
destruct a1_in_l3l4 as [a1_in_l3 | a1_in_l4].
generalize (mem_split_set _ _ EDS1.eq_bool_ok _ _ a1_in_l3).
intros [a1' [l3' [l3'' [a1_eq_a1' [H _]]]]]; 
simpl in a1_eq_a1'; simpl in H; subst l3.
rewrite app_ass in P; rewrite <- app_comm_cons in P;
rewrite <- permut_cons_inside in P; trivial.
rewrite <- app_ass in P;
destruct (IHl1 l2 (l3' ++ l3'') l4 P) as [u1 [u2 [u3 [u4 [P1 [P2 [P3 P4]]]]]]].
exists (a1 :: u1); exists u2; exists u3; exists u4; repeat split; simpl; trivial.
rewrite <- permut_cons; trivial; reflexivity.
apply permut_sym; rewrite <- permut_cons_inside; auto.

generalize (mem_split_set _ _ EDS1.eq_bool_ok _ _ a1_in_l4).
intros [a1' [l4' [l4'' [a1_eq_a1' [H _]]]]]; 
simpl in a1_eq_a1'; simpl in H; subst l4.
rewrite <- app_ass in P; 
rewrite <- permut_cons_inside in P; trivial.
rewrite app_ass in P;
destruct (IHl1 l2 l3 (l4' ++ l4'') P) as [u1 [u2 [u3 [u4 [P1 [P2 [P3 P4]]]]]]];
exists u1; exists (a1 :: u2); exists u3; exists u4; intuition; simpl; trivial.
rewrite <- permut_cons_inside; trivial.
reflexivity.
apply permut_sym; 
rewrite <- permut_cons_inside; trivial;
apply permut_sym; trivial.
Qed.

Lemma ac_syntactic :
 forall (l1 l2 l3 l4 : list A),
 permut (l2 ++ l1) (l4 ++ l3) ->
 (exists u1, exists u2, exists u3, exists u4, 
 permut l1 (u1 ++ u2) /\
 permut l2 (u3 ++ u4) /\
 permut l3 (u1 ++ u3) /\
 permut l4 (u2 ++ u4)).
Proof.
intros l1 l2 l3 l4 P; apply ac_syntactic_aux.
apply permut_trans with (l2 ++ l1).
apply list_permut_app_app.
apply permut_trans with (l4 ++ l3); trivial.
apply list_permut_app_app.
Qed.

Lemma remove_is_sound :
  forall x l, match remove eq_bool x l with
                | None => ~mem eq_A x l
                | Some l' => permut l (x :: l')
                end.
Proof.
intros x l; generalize (in_remove eq_A eq_bool eq_bool_ok x l);
case (remove eq_bool x l); [ intros k [x' [l' [l'' [x_eq_x' [H1 H2]]]]] | idtac].
injection H2; clear H2; intros; subst.
apply permut_sym; rewrite <- permut_cons_inside; auto.
intro; assumption.
Qed.

Lemma remove_permut :
  forall l1 l2, permut l1 l2 -> forall a, 
  match (remove eq_bool a l1) with
  | Some l => 
        match (remove eq_bool a l2) with
        | Some l' => permut l l'
        | None => False
        end
  | None => remove eq_bool a l2 = None
  end.
Proof.
intros l1 l2 P a; generalize (remove_is_sound a l1) (remove_is_sound a l2).
case (remove eq_bool a l1); case (remove eq_bool a l2).
intros l l' P1 P2.
rewrite (@permut_cons a a l' l).
apply permut_trans with l2; trivial.
apply permut_trans with l1; trivial.
apply permut_sym; trivial.
reflexivity.
intros l P' a_not_in_l2; apply a_not_in_l2.
rewrite <- (mem_permut_mem a P).
rewrite (mem_permut_mem a P'); left; reflexivity.
intros l a_not_in_l1 P'; assert False; [idtac | contradiction].
apply a_not_in_l1.
rewrite (mem_permut_mem a P).
rewrite (mem_permut_mem a P'); left; reflexivity.
intros; apply eq_refl.
Defined.

Lemma remove_eq_eq :
  forall l a a', eq_A a a' ->  
  match (remove eq_bool a l) with
  | Some l1 => 
        match (remove eq_bool a' l) with
        | Some l2 => l1 = l2
        | None => False
        end
  | None => remove eq_bool a' l = None
  end.
Proof.
fix remove_eq_eq 1.
intros [ | b l] a a' a_eq_a'; simpl.
apply eq_refl.
case_eq (eq_bool a b); [intro a_eq_b | intro a_diff_b].
case_eq (eq_bool a' b); [intro a'_eq_b | intro a'_diff_b].
apply eq_refl.
apply False_rect.
assert (D := eq_bool_ok a' b); rewrite a'_diff_b in D; apply D.
transitivity a.
symmetry; assumption.
assert (E := eq_bool_ok a b); rewrite a_eq_b in E; assumption.
case_eq (eq_bool a' b); [intro a'_eq_b | intro a'_diff_b].
apply False_rect.
assert (D := eq_bool_ok a b); rewrite a_diff_b in D; apply D.
transitivity a'.
assumption.
assert (E := eq_bool_ok a' b); rewrite a'_eq_b in E; assumption.
generalize (remove_eq_eq l _ _ a_eq_a').
case (remove eq_bool a l); case (remove eq_bool a' l); intros; subst; trivial.
discriminate.
Defined.

Lemma remove_equiv_nil_2 :
  forall l, remove_equiv eq_bool l nil = (l,nil).
Proof.
fix remove_equiv_nil_2 1.
intros [ | a l]; simpl.
apply eq_refl.
rewrite remove_equiv_nil_2; apply eq_refl.
Qed.

Lemma remove_equiv_is_sound: 
  forall l1 l2, match remove_equiv eq_bool l1 l2 with
  | (l1', l2') => exists l, permut l1 (l ++ l1') /\ permut l2 (l ++ l2') /\
                        (forall x, mem eq_A x l1' -> mem eq_A x l2' -> False)
  end.
Proof.
intros l1 l2; 
functional induction (remove_equiv eq_bool l1 l2) 
    as [ (* Case 1 *)
         | (* Case 2 *) H1 l2 e1 l1 H2 l2' H H' 
         | (* Case 3 *) H1 l2 e1 l1 H2 H H' l1'' l2'' H''].
(* Case 1 *)
exists (@nil A); simpl; intuition.
(* Case 2 *)
case_eq (remove_equiv eq_bool l1 l2'); intros l1'' l2'' H''; rewrite H'' in H'.
revert H'; intros [l [P1 [P2 H']]].
exists (e1 :: l); simpl; split.
apply (proj1 (permut_cons l1 (l ++ l1'') (equiv_refl _ _ eq_proof e1))); assumption.
split; trivial.
apply permut_trans with (e1 :: l2').
assert (H''' := remove_is_sound e1 l2); rewrite H in H'''; trivial.
apply (proj1 (permut_cons l2' (l ++ l2'') (equiv_refl _ _ eq_proof e1))); assumption.
(* Case 3 *)
case_eq (remove_equiv eq_bool l1 l2); intros l1' l2' H'''; rewrite H''' in H''; injection H''; clear H''; intros; subst l1'' l2''.
rewrite H''' in H'; revert H'; intros [l [P1 [P2 H']]]; exists l; split.
rewrite <- permut_cons_inside; trivial.
reflexivity.
split; trivial.
intros x [x_eq_e1 | x_mem_l1'] x_mem_l2'.
assert (H'' := remove_is_sound e1 l2); rewrite H in H''.
absurd (mem eq_A e1 l2); trivial.
apply (proj1 (mem_morph x_eq_e1 (permut_refl l2))).
apply (proj2 (mem_permut_mem x P2)).
rewrite <- mem_or_app; right; trivial.
apply (H' x); trivial.
Qed.

Lemma remove_equiv_is_complete :
  forall l1 l2 l l1' l2', permut l1 (l ++ l1') -> permut l2 (l ++ l2') ->
                        (forall x, mem eq_A x l1' -> mem eq_A x l2' -> False) ->
    (permut (fst (remove_equiv eq_bool l1 l2)) l1' /\ permut (snd (remove_equiv eq_bool l1 l2)) l2').
Proof.
intros l1 l2; 
functional induction (remove_equiv eq_bool l1 l2) 
    as [ (* Case 1 *)
         | (* Case 2 *) H1 l2 e1 l1 H2 l2' H H' 
         | (* Case 3 *) H1 l2 e1 l1 H2 H H' l1'' l2'' H'']; intros l k1' k2' P1 P2 E.
(* Case 1 *)
revert P1 P2; simpl; case l; [idtac | intros a l'].
case k1'; [idtac | intros a1' k1''].
simpl; split; assumption.
intro P1; inversion P1.
intro P1; inversion P1.
(* Case 2 *)
case_eq (remove_equiv eq_bool l1 l2'); intros l1'' l2'' H''.
assert (e1_in_l_k1' : mem eq_A e1 (l ++ k1')).
rewrite <- (mem_permut_mem e1 P1); left; reflexivity.
rewrite <- mem_or_app in e1_in_l_k1'; simpl.
assert (Subcase : mem eq_A e1 l -> permut l1'' k1' /\ permut l2'' k2').
intro e1_in_l; generalize (remove_is_sound e1 l); case (remove eq_bool e1 l).
intros l' P.
assert (Q1 : permut l1 (l' ++ k1')).
rewrite (permut_cons l1 (l' ++ k1') (e1 := e1) (e2 := e1)) by reflexivity.
apply permut_trans with (l ++ k1').
exact P1.
rewrite app_comm_cons; rewrite <- permut_app2; exact P.
generalize (remove_is_sound e1 l2); rewrite H; intro P2'.
assert (Q2 : permut l2' (l' ++ k2')).
rewrite (permut_cons l2' (l' ++ k2') (e1 := e1) (e2 := e1)) by reflexivity.
apply permut_trans with l2.
apply permut_sym; assumption.
apply permut_trans with (l ++ k2').
assumption.
rewrite app_comm_cons; rewrite <- permut_app2; exact P.
generalize (H' l' k1' k2' Q1 Q2 E).
intros [PP1 PP2]; split.
rewrite H'' in PP1; assumption.
rewrite H'' in PP2; assumption.
intro Abs; apply False_rect; apply Abs; assumption.
revert e1_in_l_k1'; intros [e1_in_l | e1_in_k1'].
apply (Subcase e1_in_l).
assert (R := remove_is_sound e1 l2); rewrite H in R.
assert (e1_in_l2 : mem eq_A e1 l2).
rewrite (mem_permut_mem e1 R); left; reflexivity.
rewrite (mem_permut_mem e1 P2) in e1_in_l2.
rewrite <- mem_or_app in e1_in_l2.
revert e1_in_l2; intros [e1_in_l | e1_in_k2'].
apply (Subcase e1_in_l).
apply False_rect; apply (E _ e1_in_k1' e1_in_k2').
(* Case 3 *)
case_eq (remove_equiv eq_bool l1 l2); intros l1' l2' H'''.
assert (R := remove_is_sound e1 l2); rewrite H in R.
assert (e1_in_l_k1' : mem eq_A e1 (l ++ k1')).
rewrite <- (mem_permut_mem e1 P1); left; reflexivity.
rewrite <- mem_or_app in e1_in_l_k1'.
revert e1_in_l_k1'; intros [e1_in_l | e1_in_k1'].
apply False_rect.
apply R; rewrite (mem_permut_mem e1 P2).
rewrite <- mem_or_app; left; assumption.
simpl; generalize (remove_is_sound e1 k1'); case (remove eq_bool e1 k1').
intros k' P.
assert (Q1 : permut l1 (l ++ k')).
rewrite (permut_cons l1 (l ++ k') (e1 := e1) (e2 := e1)) by reflexivity.
apply permut_trans with (l ++ k1').
exact P1.
apply permut_trans with (l ++ e1 :: k').
rewrite <- permut_app1; assumption.
apply permut_sym; rewrite <- permut_cons_inside; [apply permut_refl | reflexivity].
assert (E' : forall x : EDS1.A, mem eq_A x k' -> mem eq_A x k2' -> False).
intros x x_in_k x_in_k2'; apply (E x); trivial.
rewrite (mem_permut_mem x P); right; assumption.
generalize (H' l k' k2' Q1 P2 E'); rewrite H''; simpl.
intros [H1 H2]; split; trivial.
apply permut_trans with (e1 :: k').
rewrite <- permut_cons by reflexivity; assumption.
apply permut_sym; assumption.
intro Abs; apply False_rect; apply Abs; assumption.
Qed.

Lemma remove_equiv_permut_1 :
  forall l1 l1', permut l1 l1' -> 
      forall l2, (permut (fst (remove_equiv eq_bool l1 l2)) (fst (remove_equiv eq_bool l1' l2)) /\
      permut (snd (remove_equiv eq_bool l1 l2)) (snd (remove_equiv eq_bool l1' l2))).
Proof.
intros l1 l1' P1 l2; 
generalize (remove_equiv_is_sound l1 l2) (remove_equiv_is_sound l1' l2).
case_eq (remove_equiv eq_bool l1 l2); intros k1 k2 H1; intros [l [Q1 [Q2 H]]].
case_eq (remove_equiv eq_bool l1' l2); intros k1' k2' H1'; intros [l' [Q1' [Q2' H']]].
simpl; assert (Q1'' : permut l1 (l' ++ k1')).
apply permut_trans with l1'; trivial.
assert (R := @remove_equiv_is_complete l1 l2 l' k1' k2' Q1'' Q2' H'); rewrite H1 in R.
revert R; intros [R1 R2]; split; trivial.
Qed.

Lemma remove_equiv_permut_2:
  forall l1 l2 l2', permut l2 l2' -> 
      (fst (remove_equiv eq_bool l1 l2) =  fst (remove_equiv eq_bool l1 l2') /\
          permut (snd (remove_equiv eq_bool l1 l2)) (snd (remove_equiv eq_bool l1 l2'))).
Proof.
fix remove_equiv_permut_2 1.
intros [ | a1 l1] l2 l2' P.
simpl; split; [apply eq_refl | trivial].
simpl; generalize (remove_permut P a1).
case_eq (remove eq_bool a1 l2); [intro k2 | idtac]; intro H2.
case_eq (remove eq_bool a1 l2'); [intro k2' | idtac]; intro H2'.
intro P'; assert (H := remove_equiv_permut_2 l1 _ _ P'); case H; intros H' H''; split; trivial.
intro; apply False_rect; trivial.
intro H2'; rewrite H2'.
assert (H := remove_equiv_permut_2 l1 _ _ P); case H; intros H' H''; split.
revert H'; case (remove_equiv eq_bool l1 l2); intros k1 k2;
case (remove_equiv eq_bool l1 l2'); intros k1' k2'; simpl; intros; subst; trivial.
revert H''; case (remove_equiv eq_bool l1 l2); intros k1 k2;
case (remove_equiv eq_bool l1 l2'); intros k1' k2'; simpl; intros; subst; trivial.
Defined.

Lemma remove_equiv_permut:
  forall l1 l1' l2 l2', permut l1 l1' -> permut l2 l2' -> 
      permut (fst (remove_equiv eq_bool l1 l2))  (fst (remove_equiv eq_bool l1' l2')) /\
          permut (snd (remove_equiv eq_bool l1 l2)) (snd (remove_equiv eq_bool l1' l2')).
Proof.
intros l1 l1' l2 l2' P1 P2.
generalize (remove_equiv_permut_1 P1 l2) (remove_equiv_permut_2 l1' P2).
case (remove_equiv eq_bool l1 l2); case (remove_equiv eq_bool l1' l2); case (remove_equiv eq_bool l1' l2');
simpl; intros u1 u2 u3 u4 u5 u6 [Q1 Q2] [Q3 Q4]; split.
subst; assumption.
apply permut_trans with u4; assumption.
Qed.

End Make.
