(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Leo Ducas, 2007-08-06

Given a list Dom, we make a bijection between element of Dom and [[0,n-1]],
and relation restricted to Dom with relation restricted to [[1,n]].
*)

Set Implicit Arguments.

From CoLoR Require Import ListUtil SCC ListExtras Path Iter AdjMat RelSub
     LogicUtil ListNodup RelUtil BoundNat.

Section S.

  Variables (A : Type) (eq_dec : forall x y : A, {x=y}+{~x=y}) (Dom : list A).

(***********************************************************************)
(** Definition of the bijection of graphs *)

  Definition rel_on_nat (R : relation A) i j :=
    match Dom[i] with
    | None => False
    | Some a =>
      match Dom[j] with
      | None => False
      | Some b => R a b
      end
    end.

  Definition rel_on_dom (S : relation nat) a b :=
    match find_first (eq a) (eq_dec a) Dom with
    | None => False
    | Some p =>
      match find_first (eq b) (eq_dec b) Dom with
      | None => False
      | Some q => S p q
      end
    end.

(***********************************************************************)
(** Basic properties *)

  Section basic_props.

    Variables (R : relation A) (S : relation nat).

    Lemma rel_on_nat_intro i j a b :
      Dom[i] = Some a -> Dom[j] = Some b -> R a b -> rel_on_nat R i j.

    Proof. intros. unfold rel_on_nat. rewrite H, H0. exact H1. Qed.

    Lemma rel_on_dom_intro i j a b :
      find_first (eq a) (eq_dec a) Dom = Some i ->
      find_first (eq b) (eq_dec b) Dom = Some j -> S i j -> rel_on_dom S a b.

    Proof. intros. unfold rel_on_dom. rewrite H, H0. exact H1. Qed.

    Lemma rel_on_nat_elim  a b : rel_on_nat R a b ->
      exists x, exists y, R x y /\ Dom [a] = Some x /\ Dom [b] = Some y.

    Proof.
      intros. unfold rel_on_nat in H.
      destruct (Dom[a]); destruct (Dom[b]); try discr; try tauto.
      exists a0; exists a1; intuition; auto.
    Qed.

    Lemma rel_on_nat_is_restricted :
      is_restricted (rel_on_nat R) (nats_decr_lt (length Dom)).

    Proof.
      unfold is_restricted; intros.
      rewrite <- !In_nats_decr_lt; ded (rel_on_nat_elim x y H).
      repeat destruct H0; destruct H1.
      ded (element_at_in2 H1).
      ded (element_at_in2 H2).
      tauto.
    Qed.

    Lemma rel_on_dom_elim x y : rel_on_dom S x y ->
      exists a, exists b, S a b /\ Dom [a] = Some x /\ Dom [b] = Some y.

    Proof.
      intros; unfold rel_on_dom in H.
      assert (exists a, find_first (eq x) (eq_dec x) Dom =Some a).
      destruct (find_first (eq x) (eq_dec x) Dom ); try tauto.
      exists n; auto. destruct H0; subst. rewrite H0 in H.
      assert (exists b,find_first (eq y) (eq_dec y) Dom =Some b).
      destruct (find_first (eq y) (eq_dec y) Dom ); try tauto.
      exists n; auto. destruct H1; subst; rewrite H1 in H.
      ded (eq_find_first_exact H1).
      ded (eq_find_first_exact H0).
      exists x0; exists x1; intuition; auto.
    Qed.

    Arguments rel_on_dom_elim [x y] _.

    Lemma rel_on_dom_elim2 x y : rel_on_dom S x y ->
      exists a, exists b, S a b
                          /\ find_first (eq x) (eq_dec x) Dom = Some a
                          /\ find_first (eq y) (eq_dec y) Dom = Some b.

    Proof.
      intros; unfold rel_on_dom in H.
      assert (exists a, find_first (eq x) (eq_dec x) Dom =Some a).
      destruct (find_first (eq x) (eq_dec x) Dom ); try tauto.
      exists n; auto. destruct H0; subst. rewrite H0 in H.
      assert (exists b,find_first (eq y) (eq_dec y) Dom =Some b).
      destruct (find_first (eq y) (eq_dec y) Dom ); try tauto.
      exists n; auto. destruct H1; subst; rewrite H1 in H.
      ded (eq_find_first_exact H1).
      ded (eq_find_first_exact H0).
      exists x0; exists x1; intuition; auto.
    Qed.

    Arguments rel_on_dom_elim2 [x y] _.

    Variable Rdec : forall x y, {R x y}+{~R x y}.

    Lemma rel_on_nat_dec x y : {rel_on_nat R x y}+{~rel_on_nat R x y}.

    Proof.
      unfold rel_on_nat. destruct (Dom[x]). destruct (Dom[y]). apply Rdec.
      tauto. tauto.
    Defined.

  End basic_props.

  Arguments rel_on_dom_elim [S x y] _.
  Arguments rel_on_dom_elim2 [S x y] _.

(***********************************************************************)
(** Bijection *)

  Section bijection.

    Variables (R : relation A) (restriction : is_restricted R Dom).

    Lemma dom_change x y : rel_on_dom (rel_on_nat R) x y <-> R x y.

    Proof.
      intros; split; intro.
      ded (rel_on_dom_elim H).
      repeat destruct H0; destruct H1.
      unfold rel_on_nat in H0.
      rewrite H1, H2 in H0; auto.

      unfold is_restricted in restriction.
      ded (restriction H); destruct H0.
      ded (eq_In_find_first eq_dec H0); ded (eq_In_find_first eq_dec H1).
      destruct H2; destruct H2; destruct H3; destruct H3.
      unfold rel_on_dom.
      rewrite H2, H3.
      unfold rel_on_nat.
      rewrite H4, H5; auto.
    Qed.

  End bijection.

(***********************************************************************)
(** composition is mapped to composition *)

  Section compose.

    Variables (R S : relation nat)
              (restriction : is_restricted R (nats_decr_lt (length Dom)))
              (restriction' : is_restricted S (nats_decr_lt (length Dom)))
              (Dom_nodup : nodup Dom).

    Lemma dom_change_compose x y:
      rel_on_dom (R @ S) x y <-> (rel_on_dom R @ rel_on_dom S) x y.

    Proof.
      intros; split; intro.
      ded (rel_on_dom_elim H).
      repeat destruct H0; destruct H1.
      unfold compose; ded (restriction H0); destruct H4.
      rewrite <- In_nats_decr_lt, (@element_at_exists A) in H5.
      destruct H5 as [z]. exists z.
      ded (element_at_in2 H1).
      ded (element_at_in2 H3).
      ded (element_at_in2 H5).
      unfold rel_on_dom.
      destruct H6; clear H9.
      destruct H7; clear H9.
      destruct H8; clear H9.
      ded (eq_In_find_first eq_dec H6); destruct H9; destruct H9.
      ded (eq_In_find_first eq_dec H7); destruct H11; destruct H11.
      ded (eq_In_find_first eq_dec H8); destruct H13; destruct H13.
      ded (nodup_unique Dom_nodup H1 H10).
      ded (nodup_unique Dom_nodup H3 H12).
      ded (nodup_unique Dom_nodup H5 H14).
      subst; rewrite H9, H11, H13; auto.

      unfold compose in H; destruct H as [z]; destruct H.
      unfold rel_on_dom in *.
      destruct (find_first (eq x) (eq_dec x)); auto with *.
      destruct (find_first (eq y) (eq_dec y)); auto with *.
      destruct (find_first (eq z) (eq_dec z)); auto with *.
      unfold compose; exists n1; auto with *.
      destruct (find_first (eq z) (eq_dec z));auto with *.
    Qed.

  End compose.

(***********************************************************************)
(** iteration mapped to iteration *)

  Section iter.

    Variables (R : relation A) (restriction : is_restricted R Dom)
              (Dom_nodup : nodup Dom).

    Lemma iter_preserve_restriction n : is_restricted (iter R n) Dom.

    Proof.
      induction n; try trivial.
      simpl; unfold is_restricted; unfold compose.
      intros; destruct H as [z]; destruct H.
      intuition.
      ded (restriction H); tauto.
      ded (IHn _ _ H0); tauto.
    Qed.

    Lemma dom_change_iter : forall n x y,
        rel_on_dom (iter (rel_on_nat R) n) x y <-> iter R n x y.

    Proof.
      induction n; intros; simpl.
      apply dom_change; auto.
      split; intros.
      rewrite dom_change_compose in H.
      unfold compose in *.
      destruct H as [z]; destruct H; exists z.
      rewrite dom_change in H; rewrite IHn in H0; auto with *.
      apply rel_on_nat_is_restricted.
      hyp.

      unfold compose in H; destruct H as [z]; destruct H.
      rewrite dom_change_compose.
      unfold compose; exists z; split.
      rewrite dom_change;  hyp.
      rewrite IHn; hyp.
      apply rel_on_nat_is_restricted.
      hyp.
    Qed.

    Lemma dom_change_tc x y : rel_on_dom (rel_on_nat R !) x y <-> R! x y.

    Proof.
      split; intros.

      ded (rel_on_dom_elim2 H); do 3 destruct H0.
      ded (tc_iter H0); unfold Iter in *; unfold Iter_ge in *.
      destruct H2 as [n]. destruct H2; destruct H1.
      eapply (iter_tc R n); rewrite <- dom_change_iter.
      unfold rel_on_dom; rewrite H1, H4; trivial.

      ded (tc_iter H); unfold Iter in *; unfold Iter_ge in *.
      destruct H0 as [n]; destruct H0.
      rewrite <- dom_change_iter in H1.
      unfold rel_on_dom in *.
      destruct (find_first (eq x) (eq_dec x) Dom); auto with *.
      destruct (find_first (eq y) (eq_dec y) Dom); auto with *.
      ded (iter_tc (rel_on_nat R) n); auto.
    Qed.

  End iter.

(***********************************************************************)
(** intersection mapped to intersection *)

  Section intersection.

    Variables R S : relation nat.

    Lemma dom_change_inter x y : rel_on_dom (intersection R S) x y
      <-> rel_on_dom R x y /\ rel_on_dom S x y.

    Proof.
      split; intros;
        unfold rel_on_dom in *;
        destruct (find_first (eq x) (eq_dec x) Dom); auto with *;
          destruct (find_first (eq y) (eq_dec y) Dom); auto with *.
    Qed.

  End intersection.

(***********************************************************************)
(** transposition mapped to transposition *)

  Section transpose.

    Variable R : relation nat.

    Lemma dom_change_transp x y :
      rel_on_dom (transp R) x y <-> transp (rel_on_dom R) x y.

    Proof.
      split; intros; unfold transp in *;
        unfold rel_on_dom in *;
        destruct (find_first (eq x) (eq_dec x) Dom); auto with *;
          destruct (find_first (eq y) (eq_dec y) Dom); auto with *.
    Qed.

  End transpose.

(***********************************************************************)
(** SCC mapped to SCC *)

  Section domSCC.

    Variables (R : relation A) (restriction : is_restricted R Dom)
              (Dom_nodup : nodup Dom).

    Lemma dom_change_SCC x y :
      rel_on_dom (SCC (rel_on_nat R)) x y <-> SCC  R x y.

    Proof.
      split; intros; unfold SCC in *.
      change (R! x y /\ transp (R!) x y).
      change (rel_on_dom (intersection (rel_on_nat R !) 
                                       (transp (rel_on_nat R !))) x y) in H.
      rewrite dom_change_inter in H.
      destruct H; rewrite dom_change_transp in H0.
      unfold transp in *.
      rewrite dom_change_tc in *; auto with *.

      change (R! x y /\ transp (R!) x y) in H.
      change (rel_on_dom
                (intersection (rel_on_nat R !) (transp (rel_on_nat R !))) x y).
      rewrite dom_change_inter.
      destruct H; rewrite dom_change_transp.
      unfold transp in *.
      rewrite dom_change_tc; auto with *; rewrite dom_change_tc; auto with *.
    Qed.

  End domSCC.

End S.
