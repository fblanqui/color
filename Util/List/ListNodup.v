(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-02-16
- Stephane Le Roux, 2006-10-17

Lists without duplicated elements
*)

Set Implicit Arguments.

From CoLoR Require Import ListUtil NatUtil RelMidex LogicUtil.
From CoLoR Require ListDec BoolUtil.

Section S.

  Variable A : Type.

(***********************************************************************)
(** Predicate saying if a list has no duplicated element. *)

  Fixpoint nodup (l : list A) : Prop :=
    match l with
      | nil => True
      | a :: l' => ~In a l' /\ nodup l'
    end.

  Lemma nodup_app_elim_right :
    forall l l', nodup (l++l') -> nodup l'.

  Proof. induction l; simpl; intros. hyp. apply IHl. tauto. Qed.

  Lemma nodup_midex_incl_length : eq_midex A ->
    forall l l', nodup l -> incl l l' -> length l <= length l'.

  Proof.
    intro em. induction l; simpl; intros. apply Nat.le_0_l.
    destruct (In_elim_right em a l'). apply H0. simpl. tauto. destruct H1.
    rewrite (proj1 H1), (length_app x (a::x0)).
    assert (length l <= length (x++x0)). apply IHl.
    tauto. unfold incl in *|-* . intros. apply in_or_app. destruct (em a0 a).
    subst a0. tauto. assert (In a0 x \/ In a0 (a::x0)). apply in_app_or.
    rewrite <- (proj1 H1). apply H0. simpl. tauto. simpl in H4. intuition auto with *.
    rewrite (length_app x x0) in H2. simpl. lia. 
  Qed.

(***********************************************************************)
(** Properties of nodup. *)

  Variable eq_dec : forall x y : A, {x=y}+{~x=y}.

  Lemma nodup_unique : forall l (x:A),
    nodup l -> forall n m, l[n] = Some x -> l[m] = Some x -> n=m.

  Proof.
    intro; intro; induction l; intros; simpl in H; try discr.
    destruct n; destruct m; auto with *; simpl in *.
    rewrite <- H0 in H1; ded (element_at_in2 H1); tauto.
    rewrite <- H1 in H0; ded (element_at_in2 H0); tauto.
    destruct H; ded (IHl H2 n m H0 H1); auto.
  Qed.

  Lemma nodup_incl_length : forall l l' : list A,
    nodup l -> incl l l' -> length l <= length l'.

  Proof.
    induction l; simpl; intros. apply Nat.le_0_l.
    apply Nat.le_trans with (S (length (remove eq_dec a l'))).
    apply le_n_S. apply IHl. tauto. apply incl_remove. tauto.
    apply incl_cons_l_incl with a. hyp.
    apply NatCompat.lt_le_S. apply In_length_remove. apply incl_cons_l_in with l. hyp.
  Qed.

  Lemma nodup_last : forall (a : A) l,
    nodup l -> ~In a l -> nodup (l ++ a :: nil).

  Proof.
    induction l; simpl; intros. auto. intuition. ded (in_app_or H). destruct H5.
    auto. simpl in H5. intuition.
  Qed.

  Lemma nodup_rev : forall l : list A,
    nodup l -> nodup (rev l).

  Proof.
    induction l; simpl; intros. exact H. destruct H. apply nodup_last.
    apply IHl. exact H0. intro. apply H. apply rev_incl. exact H1.
  Qed.

  Lemma nodup_app_elim : forall l m : list A, nodup (l ++ m) ->
    nodup l /\ nodup m /\ forall x, In x l -> ~In x m.

  Proof.
    induction l; simpl; intros. intuition. destruct H. ded (IHl m H0).
    decomp H1. intuition auto with *. subst a. apply H. apply in_appr. exact H3.
    apply (H5 x); hyp.
  Qed.

  Arguments nodup_app_elim [l m] _.

  Lemma nodup_app_cons : forall l (x : A) m,
    nodup (l ++ x :: m) -> ~In x l /\ ~In x m.

  Proof.
    split. apply nodup_rev in H. rewrite rev_app_distr in H.
    apply nodup_app_elim in H. decomp H. rewrite List.in_rev.
    apply H3. rewrite <- List.in_rev. simpl. auto.
    apply nodup_app_elim in H. simpl in H. tauto.
  Qed.

  Lemma length_remove_nodup (x : A) : forall l, nodup l ->
    In x l -> length (remove eq_dec x l) = length l - 1.

  Proof.
    induction l; intros hl ha; simpl. refl. destruct (eq_dec a x).
    subst. rewrite remove_notin. lia. fo.
    simpl. rewrite IHl. destruct l. fo. simpl. lia. fo. fo.
  Qed.

  Lemma nodup_incl_length_le :
    forall l m : list A, nodup l -> l [= m -> length l <= length m.

  Proof.
    induction l; simpl; intros m l_nodup lm. lia.
    destruct l_nodup as [a_notin_l l_nodup].
    assert (am : In a m). apply lm. fo.
    destruct (in_elim am) as [m1 [m2 e]]. subst.
    assert (lm1m2 : l [= m1 ++ m2). intros x xl.
    assert (xal : In x (a :: l)). right. hyp.
    apply lm in xal. rewrite in_app in xal.
    assert (x <> a). intro. subst. contr. firstorder auto with datatypes exfalso.
    gen (IHl _ l_nodup lm1m2). rewrite !length_app. simpl. lia.
  Qed.

  Lemma nodup_remove (x : A) :
    forall l, nodup l -> nodup (remove eq_dec x l).

  Proof.
    induction l; simpl. auto. destruct (eq_dec a x). fo. simpl. fo.
    intro h. apply H. eapply incl_remove2. apply h.
  Qed.

  Lemma In_nodup_elim (x : A) : forall l, In x l -> nodup l ->
    exists l1 l2, l = l1 ++ x :: l2 /\ ~In x l1 /\ ~In x l2.

  Proof.
    induction l; simpl. tauto. intros [h|h] [h1 h2].
    subst. exists nil. ex l. auto.
    destruct (IHl h h2) as [l1 [l2 [i1 [i2 i3]]]].
    assert (i : x<>a). intro; subst. tauto.
    ex (a::l1) l2. subst. fo.
  Qed.

  Arguments In_nodup_elim [x l] _ _.

  Lemma inj_nth_nodup (x : A) l i j : nodup l ->
    i < length l -> j < length l -> nth i l x = nth j l x -> i = j.

  Proof.
    intros hl hi hj. gen (nth_In x hi). set (a := nth i l x). intros h e.
    destruct (In_nodup_elim h hl) as [l1 [l2 [n0 [n1 n2]]]].
    rewrite n0, length_app in hi, hj. simpl in hi, hj.
    destruct (lt_dec j (length l1)).
    (* j < length l1 *)
    assert (aj : a = nth j l1 x). rewrite e, n0, app_nth1; auto.
    gen (nth_In x l0). rewrite <- aj. tauto.
    (* j >= length l1 *)
    assert (aj : a = nth (j-length l1) (a::l2) x). rewrite e at 1.
    rewrite n0, app_nth2. refl. lia.
    destruct (lt_dec i (length l1)).
    (* i < length l1 *)
    assert (ai : a = nth i l1 x). unfold a. rewrite n0, app_nth1; auto.
    gen (nth_In x l0). rewrite <- ai. tauto.
    (* i >= length l1 *)
    assert (ai : a = nth (i-length l1) (a::l2) x). unfold a at 1.
    rewrite n0, app_nth2. refl. lia.
    gen aj. gen ai. simpl.
    case_eq (j - length l1).
    (* j = length l1 *)
    case_eq (i - length l1). intros; lia. intros r r1 r2 _ r3.
    assert (p : r < length l2). lia. gen (nth_In x p).
    simpl in ai. rewrite r1 in ai. rewrite <- ai. tauto.
    (* j > length l1 *)
    intros r r1. assert (p : r < length l2). lia. gen (nth_In x p).
    simpl in aj. rewrite r1 in aj. rewrite <- aj. tauto.
  Qed.

  Lemma nodup_select (f : A->Prop) (f_dec : forall x, {f x}+{~f x}) :
    forall l, nodup l -> nodup (select f_dec l).

  Proof.
    induction l; simpl. fo. destruct (f_dec a); simpl; intuition.
    apply H0. eapply incl_select. apply H2.
  Qed.

(***********************************************************************)
(** Least prefix with no duplicated element. *)

  Fixpoint greatest_nodup_prefix_aux (acc l : list A) : list A :=
    match l with
      | nil => rev acc
      | cons x l =>
        match In_dec eq_dec x acc with
          | left _ => rev acc
          | right _ => greatest_nodup_prefix_aux (x :: acc) l
        end
    end.

  Notation greatest_nodup_prefix := (greatest_nodup_prefix_aux nil).

(***********************************************************************)
(** greatest_nodup_prefix properties *)

  Lemma greatest_nodup_prefix_aux_correct : forall l acc,
    nodup acc -> nodup (greatest_nodup_prefix_aux acc l).

  Proof.
    induction l; simpl; intros. apply nodup_rev. exact H.
    case (In_dec eq_dec a acc); intro. apply nodup_rev. exact H.
    apply IHl. simpl. auto.
  Qed.

  Lemma greatest_nodup_prefix_correct : forall l,
    nodup (greatest_nodup_prefix l).

  Proof. intro. apply greatest_nodup_prefix_aux_correct. fo. Qed.

  Lemma greatest_nodup_prefix_aux_elim : forall l acc,
    exists p, greatest_nodup_prefix_aux acc l = rev acc ++ p.

  Proof.
    induction l; simpl; intros. exists nil. rewrite app_nil_r. refl.
    case (In_dec eq_dec a acc); intro. exists nil. rewrite app_nil_r. refl.
    ded (IHl (a::acc)). destruct H. rewrite H. simpl. rewrite <- app_assoc. simpl.
    exists (a::x). refl.
  Qed.

  Lemma greatest_nodup_prefix_aux_app : forall m l acc,
    nodup l -> (forall x, In x l -> ~In x acc) ->
    greatest_nodup_prefix_aux acc (l ++ m)
    = greatest_nodup_prefix_aux (rev l ++ acc) m.

  Proof.
    induction l; simpl; intros. refl. destruct H.
    case (In_dec eq_dec a acc); intro.
    absurd (In a acc). apply H0. auto. exact i.
    assert (forall x, In x l -> ~In x (a::acc)). intuition. destruct H3.
    subst a. auto. eapply H0. right. apply H2. exact H3.
    rewrite (IHl (a::acc) H1 H2). rewrite <- app_assoc. refl.
  Qed.

  Arguments greatest_nodup_prefix_aux_app _ [l acc] _ _.

  Lemma greatest_nodup_prefix_app : forall m l, nodup l ->
    greatest_nodup_prefix (l ++ m)
    = greatest_nodup_prefix_aux (rev l) m.

  Proof.
    intros. assert (rev l = rev l ++ nil). rewrite app_nil_r. reflexivity.
    rewrite H0. apply greatest_nodup_prefix_aux_app. exact H. simpl. auto.
  Qed.

  Arguments greatest_nodup_prefix_app _ [l] _.

  Lemma nodup_greatest_nodup_prefix : forall l,
    nodup l -> greatest_nodup_prefix l = l.

  Proof.
    induction l; simpl; intros. refl. destruct H.
    assert (l = l++nil). rewrite app_nil_r. reflexivity. rewrite H1.
    assert (forall x, In x l -> ~In x (a::nil)). simpl. intuition.
    subst a. auto.
    rewrite (greatest_nodup_prefix_aux_app nil H0 H2). simpl.
    rewrite rev_unit, rev_involutive, app_nil_r. refl.
  Qed.

  Lemma greatest_nodup_prefix_intro: forall l,
    l = greatest_nodup_prefix l
    \/ exists x, In x (greatest_nodup_prefix l)
                 /\ exists p, l = greatest_nodup_prefix l ++ x :: p.

  Proof.
    induction l; intros. simpl. intuition.
    assert (nodup (greatest_nodup_prefix l)).
    apply greatest_nodup_prefix_correct.
    case (In_dec eq_dec a (greatest_nodup_prefix l)); intro.
    (* In a (greatest_nodup_prefix l) *)
    right. ded (in_elim_dec eq_dec i). do 3 destruct H0. exists a.
    (* nodup (a::x) *)
    assert (nodup (a::x)). simpl. split. exact H1.
    rewrite H0 in H. ded (nodup_app_elim H). intuition. split.
    simpl. ded (greatest_nodup_prefix_aux_elim l (a::nil)). destruct H3.
    rewrite H3.
    simpl. auto.
    (* exists p, l = greatest_nodup_prefix l ++ p *)
    assert (exists p, l = greatest_nodup_prefix l ++ p). destruct IHl.
    exists nil. rewrite <- H3. rewrite app_nil_r. reflexivity.
    decomp H3. exists (x1::x2). exact H4.
    (* greatest_nodup_prefix_app (x::x0++x1) H2 *)
    decomp H3. rewrite H0 in H4. rewrite H4.
    assert (a::(x++a::x0)++x1 = (a::x)++a::x0++x1). rewrite <- app_assoc. refl.
    rewrite H3. clear H3.
    rewrite (greatest_nodup_prefix_app (a::x0++x1) H2). simpl.
    case (In_dec eq_dec a (rev x ++ a :: nil)); intros.
    rewrite distr_rev. simpl. rewrite rev_involutive. exists (x0++x1). refl.
    absurd (In a (rev x++a::nil)). exact n. apply in_appr. simpl. auto.
    (* ~In a (greatest_nodup_prefix l) *)
    destruct IHl.
    left. sym. apply nodup_greatest_nodup_prefix. simpl.
    rewrite H0. intuition.
    right. decomp H0. exists x.
    assert (nodup (a::greatest_nodup_prefix l)). simpl. intuition.
    (* greatest_nodup_prefix_app (x::x0) H0 *)
    assert (a::l = (a::greatest_nodup_prefix l)++x::x0). simpl.
    rewrite <- H1. refl.
    rewrite H3. clear H3. rewrite (greatest_nodup_prefix_app (x::x0) H0).
    simpl.
    rewrite rev_unit, rev_involutive.
    case (In_dec eq_dec x (rev (greatest_nodup_prefix l) ++ a :: nil));
      intro. split.
    apply in_cons. exact H2. exists x0. refl.
    absurd (In x (rev (greatest_nodup_prefix l) ++ a :: nil)). exact n0.
    apply in_appl. apply in_rev. exact H2.
  Qed.

  Lemma greatest_nodup_prefix_intro' : forall l,
    exists m, l = greatest_nodup_prefix l ++ m.

  Proof.
    intro. ded (greatest_nodup_prefix_intro l). destruct H.
    exists nil. rewrite <- H. rewrite app_nil_r. reflexivity.
    decomp H. exists (x::x0). exact H0.
  Qed.

  Lemma nodup_intro: forall l : list A, nodup l
    \/ exists m x p, l = m ++ x :: p /\ nodup m /\ In x m.

  Proof.
    intro. ded (greatest_nodup_prefix_intro l).
    assert (nodup (greatest_nodup_prefix l)).
    apply greatest_nodup_prefix_correct. destruct H.
    left. rewrite H. exact H0.
    right. decomp H. ex (greatest_nodup_prefix l) x x0.
    intuition.
  Qed.

  Lemma nodup_intro' : forall l : list A,
    exists m p, l = m ++ p /\ nodup m.

  Proof.
    intro. ded (nodup_intro l). destruct H.
    exists l. exists nil. rewrite app_nil_r. auto.
    decomp H. exists x. exists (x0::x1). auto.
  Qed.

(***********************************************************************)
(** Remove duplicated elements of a list. *)

  Fixpoint remdup l :=
    match l with
      | nil => nil
      | t :: q => t :: remove eq_dec t (remdup q) 
    end.

  Lemma nodup_remdup : forall l, nodup (remdup l).

  Proof.
    induction l. simpl; auto. simpl. split. unfold not. apply notin_remove.
    eapply nodup_remove; eauto.
  Qed.

  Lemma remdup_incl : forall l, remdup l [= l.

  Proof.
    induction l. simpl; unfold incl; auto.
    unfold incl; simpl. intros. destruct H.
    left; auto.
    right; apply IHl. eapply remove_In. eauto.
  Qed.

  Lemma incl_remdup : forall l, l [= remdup l.

  Proof.
    induction l. simpl; unfold incl; auto.
    unfold incl; simpl. intros. destruct (eq_dec a a0).
    auto. destruct H. auto. right. apply In_remove; auto.
  Qed.

  Lemma In_remdup x : forall l, In x (remdup l) <-> In x l.

  Proof.
    intro l. split; intro h. apply remdup_incl. hyp.
    apply incl_remdup. hyp.
  Qed.

(***********************************************************************)
(** Boolean function deciding nodup. *)

  Import ListDec BoolUtil.

  Variables (beq : A -> A -> bool)
            (beq_ok : forall x y, beq x y = true <-> x = y).

  Fixpoint bnodup (l : list A) : bool :=
    match l with
      | nil => true
      | a :: l' => negb (mem beq a l') && bnodup l'
    end.

  Lemma bnodup_ok : forall l, bnodup l = true <-> nodup l.

  Proof.
    induction l; simpl; intros. tauto.
    rewrite andb_eq. rewrite IHl. rewrite <- (mem_ok beq_ok). rewrite negb_lr.
    simpl. rewrite false_not_true. refl.
  Qed.

End S.

Arguments nodup_app_elim [A l m] _.
Arguments nodup_unique [A l x] _ [n m] _ _.
Arguments nodup_app_cons [A l x m] _.
Arguments bnodup_ok [A beq] _ _.

(***********************************************************************)
(** Properties of [nodup] involving more than one type. *)

From CoLoR Require Import FunUtil.

Lemma nodup_map_inj A B (f : A -> B) :
  injective f -> forall l, nodup l -> nodup (map f l).

Proof.
  intro f_inj. induction l; simpl. auto.
  intros [a_notin_l l_nodup]. split. 2: fo.
  intro fa_in_mapfl. destruct (in_map_elim fa_in_mapfl) as [x [x1 x2]].
  apply f_inj in x2. subst. contr.
Qed.

(***********************************************************************)
(** Tactics. *)

Ltac nodup beq_ok := rewrite <- (bnodup_ok beq_ok); check_eq.
