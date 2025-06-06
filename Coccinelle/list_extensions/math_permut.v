(** * Permutation over lists, and finite multisets. *)

Set Implicit Arguments. 

From Stdlib Require Import List Relations Multiset Arith Setoid.
From CoLoR Require Import decidable_set more_list equiv_list.
From CoLoR Require list_permut.

 Definition permut (n : nat) (f : nat -> nat) :=
  (forall i, n <= i -> f i = i) /\
  (forall i, i < n -> f i < n) /\
  (forall i j, i < n -> j < n -> f i = f j -> i = j).

Lemma adequacy :
  forall (A : Type) (R : relation A) (l1 l2 : list A),
  list_permut.permut0 R l1 l2 <-> 
  (length l1 = length l2 /\ 
   exists pi, (permut (length l1) pi) /\
   forall i, i < length l1 ->
   match (nth_error l1 i), (nth_error l2 (pi i)) with
   | (Some ai), (Some bi) => R ai bi
   | _, _ => False
   end).
Proof.
intros A R l1; pattern l1; apply list_rec2; clear l1.
intro n; induction n as [ | n]; intros l1 L1 l2; split.
intros P; inversion P; subst.
split; trivial.
exists (fun (i : nat) => i); repeat split; trivial.
intros i L; simpl in L; inversion L.
simpl in L1; inversion L1.
intros [L _]; destruct l1 as [ | a1 l1].
destruct l2 as [ | a2 l2].
apply list_permut.Pnil.
simpl in L; discriminate.
simpl in L1; inversion L1.
intros P; inversion P as [ | a1 b1 l1' l2' l2'' a1_R_b1 Q ]; subst; split; trivial.
exists (fun (i : nat) => i); repeat split; trivial.
intros i L; simpl in L; inversion L.
rewrite (list_permut.permut_length P); trivial.
simpl in L1; generalize (le_S_n _ _ L1); clear L1; intro L1.
rewrite (IHn l1' L1 (l2' ++ l2'')) in Q.
destruct Q as [ L [pi [ Q H]]].
exists (fun (i : nat) =>
             match i with
             | 0 => length l2'
             | S i => 
                 if le_lt_dec (length l2') (pi i)
                 then S (pi i)
                 else pi i
             end); split.
unfold permut in *; repeat split.
intros [ | i] L'; simpl in L'.
inversion L'.
generalize (le_S_n _ _ L'); clear L'; intro L'.
destruct Q as [Q _].
rewrite (Q i L').
destruct (le_lt_dec (length l2') i) as [ll2'_le_i | ll2'_gt_i]; trivial.
rewrite L in L'.
absurd (length l2' < length l2'); auto with arith.
apply Nat.le_lt_trans with i; trivial.
apply Nat.le_trans with (length (l2' ++ l2'')); trivial.
rewrite length_app; auto with arith.
intros [ | i] L'.
simpl; rewrite L; unfold lt; apply le_n_S; rewrite length_app; auto with arith.
simpl in L'; generalize (le_S_n _ _ L'); clear L'; intro L'.
destruct Q as [_ [Q _]].
destruct (le_lt_dec (length l2') (pi i)) as [ll2'_le_pii | ll2'_gt_pii].
simpl; unfold lt; apply le_n_S; apply Q; trivial.
simpl; apply Nat.lt_le_trans with (length l1').
apply Q; trivial.
auto with arith.
destruct Q as [_ [_ Q]].
intros [ | i] [ | j] L' L'' H'; trivial.
destruct  (le_lt_dec (length l2') (pi j)) as [ll2'_cmp_pij | ll2'_cmp_pij];
rewrite H' in ll2'_cmp_pij;
absurd (S (pi j) <= pi j); trivial; auto with arith. 
destruct  (le_lt_dec (length l2') (pi i)) as [ll2'_cmp_pii | ll2'_cmp_pii];
rewrite <- H' in ll2'_cmp_pii;
absurd (S (pi i) <= pi i); trivial; auto with arith. 
destruct  (le_lt_dec (length l2') (pi i)) as [ll2'_le_pii | ll2'_gt_pii];
destruct  (le_lt_dec (length l2') (pi j)) as [ll2'_le_pij | ll2'_gt_pij].
apply (f_equal (fun n => S n)); apply Q.
simpl in L'; apply Nat.lt_succ_r; trivial.
simpl in L''; apply Nat.lt_succ_r; trivial.
injection H'; trivial.
absurd (length l2' < length l2'); auto with arith.
apply Nat.le_lt_trans with (pi j); trivial.
rewrite <- H'; auto with arith.
absurd (length l2' < length l2'); auto with arith.
apply Nat.le_lt_trans with (pi i); trivial.
rewrite H'; auto with arith.
apply (f_equal (fun n => S n)); apply Q; trivial.
simpl in L'; apply Nat.lt_succ_r; trivial.
simpl in L''; apply Nat.lt_succ_r; trivial.
intros [ | i] L'.
simpl; rewrite nth_error_at_pos; trivial.
simpl in L'; generalize (le_S_n _ _ L'); clear L'; intro L'.
simpl; rewrite (nth_error_remove b1 l2' l2'' (pi i)); apply H; trivial.

intros [L [pi [P H]]].
destruct l1 as [ | a1 l1].
destruct l2 as [ | a2 l2].
apply list_permut.Pnil.
simpl in L; discriminate.
assert (L' : 0 < length (a1 :: l1)).
simpl; auto with arith.
generalize (H 0 L'); simpl.
assert (H' := nth_error_ok_in (pi 0) l2).
destruct (nth_error l2 (pi 0)) as [ b1 | ].
intro a1_R_b1; destruct (H' _ (eq_refl _)) as [l2' [l2'' [L'' H'']]]; clear H'.
subst l2; apply list_permut.Pcons; trivial.
rewrite IHn; [split | simpl in L1; apply le_S_n; trivial].
rewrite length_app in L; rewrite Nat.add_comm in L; simpl in L; injection L; 
intro L'''; rewrite L'''; rewrite Nat.add_comm; rewrite length_app; trivial.
exists (fun i => 
               if le_lt_dec (length l1) i
               then i
               else
                 if le_lt_dec (pi (S i)) (pi 0)  
                 then pi (S i) 
                 else (pi (S i)) -1); split.
unfold permut in *; repeat split.

intros i L'''; 
destruct (le_lt_dec (length l1) i) as [ll1_le_i | ll1_gt_i]; trivial.
absurd (i < i); auto with arith.
apply Nat.lt_le_trans with (length l1); trivial.

intros i L'''; 
destruct (le_lt_dec (length l1) i) as [ll1_le_i | _]; trivial.
assert (L'''' : S i < length (a1 :: l1)).
simpl; auto with arith.
destruct (le_lt_dec (pi (S i)) (pi 0)) as [piSi_le_pi0 | piSi_gt_pi0].
assert (piSi_lt_pi0 : pi (S i) < pi 0).
destruct (proj1 (Nat.lt_eq_cases _ _) piSi_le_pi0) as [L5 | E]; trivial.
destruct P as [_ [_ P]]. 
absurd (S i = 0).
discriminate.
apply (P (S i) 0); trivial.
apply Nat.lt_le_trans with (pi 0); trivial.
destruct P as [_ [P _]].
generalize (P 0 (Nat.lt_0_succ _)); simpl; auto with arith.
destruct P as [_ [P _]].
generalize (P (S i) L''''); destruct (pi (S i)) as [ | p]; simpl.
intros _; apply Nat.le_lt_trans with i; auto with arith.
rewrite Nat.sub_0_r; auto with arith.

intros i j Li Lj;
destruct (le_lt_dec (length l1) i) as [ll1_le_i | _];
destruct (le_lt_dec (length l1) j) as [ll1_le_j | _];
trivial.
absurd (i < i); auto with arith.
apply Nat.lt_le_trans with (length l1); trivial.
absurd (j < j); auto with arith.
apply Nat.lt_le_trans with (length l1); trivial.
destruct P as [_ [_ P]];
destruct (le_lt_dec (pi (S i)) (pi 0)) as [piSi_le_pi0 | piSi_gt_pi0];
destruct (le_lt_dec (pi (S j)) (pi 0)) as [piSj_le_pi0 | piSj_gt_pi0].
intro piSi_eq_piSj; assert (Si_eq_Sj : S i = S j).
apply (P (S i) (S j)); simpl; auto with arith.
injection Si_eq_Sj; trivial.
destruct (proj1 (Nat.lt_eq_cases _ _) piSi_le_pi0) as [L5 | E]; clear piSi_le_pi0.
destruct (pi (S j)) as [ | pj].
absurd (pi 0 < 0); auto with arith.
simpl; rewrite Nat.sub_0_r.
intro H'; rewrite H' in L5.
absurd (S pj < S pj); auto with arith.
apply Nat.le_lt_trans with (pi 0); auto with arith.
absurd (S i = 0).
discriminate.
apply (P (S i) 0); trivial.
simpl; auto with arith.
destruct (proj1 (Nat.lt_eq_cases _ _) piSj_le_pi0) as [L5 | E]; clear piSj_le_pi0.
destruct (pi (S i)) as [ | qi].
absurd (pi 0 < 0); auto with arith.
simpl; rewrite Nat.sub_0_r.
intro H'; rewrite <- H' in L5.
absurd (S qi < S qi); auto with arith.
apply Nat.le_lt_trans with (pi 0); auto with arith.
absurd (S j = 0).
discriminate.
apply (P (S j) 0); trivial.
simpl; auto with arith.
intro piSi_eq_piSj; assert (Si_eq_Sj : S i = S j).
apply (P (S i) (S j)); simpl; auto with arith.
destruct (pi (S i)) as [ | qi].
absurd (pi 0 < 0); auto with arith.
destruct (pi (S j)) as [ | pj].
absurd (pi 0 < 0); auto with arith.
simpl in piSi_eq_piSj; do 2 rewrite Nat.sub_0_r in piSi_eq_piSj; subst; trivial.
injection Si_eq_Sj; trivial.

intros i Li; 
destruct (le_lt_dec (length l1) i) as [ll1_lt_i | _].
absurd (i < i); auto with arith.
apply Nat.lt_le_trans with (length l1); trivial.
generalize (H (S i) (proj1 (Nat.succ_lt_mono _ _) Li)); simpl.
destruct (nth_error l1 i) as [ai | ]; trivial.
generalize (nth_error_ok_in (pi (S i)) (l2' ++ b1 :: l2''));
destruct (nth_error (l2' ++ b1 :: l2'') (pi (S i))) as [bi | ]; 
[idtac | contradiction].
intros H' ai_R_bi; destruct (H' _ (eq_refl _)) as [k2 [k2' [Lk2 H'']]]; clear H'.
destruct (in_in_split_set b1 bi l2' l2'' k2 k2' H'') as [[H''' | H'''] | H''']; clear H''.
destruct H''' as [l [H3 H4]]; subst.
rewrite <- app_assoc; rewrite <- Lk2; rewrite <- L''; simpl.
destruct (le_lt_dec (length k2) (length (k2 ++ bi :: l))) as [Ok | Ko].
rewrite nth_error_at_pos; trivial.
absurd (length k2 < length k2); auto with arith.
apply Nat.le_lt_trans with (length (k2 ++ bi :: l)); trivial.
rewrite length_app; auto with arith.
destruct H''' as [l [H3 H4]]; subst.
rewrite <- Lk2; rewrite <- L''; simpl.
destruct (le_lt_dec (length (l2' ++ b1 :: l)) (length l2')) as [Ko | Ok].
absurd (length l2' < length l2'); auto with arith.
apply Nat.lt_le_trans with (length (l2' ++ b1 :: l)); trivial.
rewrite length_app; rewrite Nat.add_comm; simpl; auto with arith.
rewrite (length_app l2' (b1 :: l)).
rewrite Nat.add_comm; simpl; rewrite Nat.sub_0_r; rewrite Nat.add_comm;
rewrite <- length_app.
rewrite app_assoc; rewrite nth_error_at_pos; trivial.
destruct H''' as [_ [H3 H4]]; subst;
absurd (0 = S i).
discriminate.
destruct P as [_ [_ P]].
apply P; simpl; auto with arith.
rewrite <- Lk2; rewrite L''; subst; trivial.
intro; contradiction.
Qed.

Section defs.

  (** * From lists to multisets *)

  Variable A : Type.
  Variable eqA : relation A.
  Hypothesis eqA_dec : forall x y:A, {eqA x y} + {~ eqA x y}.

  Let emptyBag := EmptyBag A.
  Let singletonBag := SingletonBag _ eqA_dec.

  (** contents of a list *)

  Fixpoint list_contents (l:list A) : multiset A :=
    match l with
      | nil => emptyBag
      | a :: l => munion (singletonBag a) (list_contents l)
    end.

  (** * [permutation]: definition and basic properties *)
  
  Definition permutation (l m:list A) :=
    meq (list_contents l) (list_contents m).
End defs.

Lemma permut_closure : forall (A : Type) eqA 
 (eqA_dec : forall a1 a2, {eqA a1 a2}+{~eqA a1 a2}), 
forall a1 a2, @permutation A eqA eqA_dec (a1 :: nil) (a2 :: nil) <-> 
(forall a, eqA a1 a <-> eqA a2 a).
Proof.
intros A eqA eqA_dec; unfold permutation, meq; simpl.
intros a1 a2; split.
intros H a; assert (Ha := H a); clear H; do 2 rewrite <- plus_n_O in Ha.
destruct (eqA_dec a1 a) as [a1_eq_a | a1_diff_a];
destruct (eqA_dec a2 a) as [a2_eq_a | a2_diff_a].
intuition.
discriminate.
discriminate.
intuition.
intros H a;
destruct (eqA_dec a1 a) as [a1_eq_a | a1_diff_a];
destruct (eqA_dec a2 a) as [a2_eq_a | a2_diff_a]; trivial.
absurd (eqA a2 a); trivial; rewrite <- (H a); trivial.
absurd (eqA a1 a); trivial; rewrite  (H a); trivial.
Qed.





