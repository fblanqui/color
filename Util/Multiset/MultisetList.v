(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2004-09-06

This file provides an implementation of finite multisets using list
representation.
*)

Set Implicit Arguments.

From Coq Require Import Permutation PermutSetoid Lia Multiset.
From CoLoR Require Import LogicUtil RelExtras MultisetCore ListExtras.

Module MultisetList (ES : Eqset_dec) <: MultisetCore with Module Sid := ES.

  Module Export Sid := ES.

Section Operations.

  Definition Multiset := list A.

  Definition empty : Multiset := nil.
  Definition singleton a : Multiset := a :: nil.
  Definition union := app (A:=A).
  Definition meq := permutation eqA eqA_dec.

  Definition mult := countIn eqA eqA_dec.
  Definition rem := removeElem eqA eqA_dec.
  Definition diff := removeAll eqA eqA_dec.

  Definition intersection := inter_as_diff diff.

  Definition fold_left := fun T : Type => List.fold_left (A := T) (B := A).

End Operations.

  Infix "=mul=" := meq (at level 70) : msets_scope.
  Notation "X <>mul Y" := (~meq X Y) (at level 50) : msets_scope.
  Notation "{{ x }}" := (singleton x) (at level 5) : msets_scope.
  Infix "+" := union : msets_scope.
  Infix "-" := diff : msets_scope.
  Infix "#" := intersection (at level 50, left associativity) : msets_scope.
  Infix "/" := mult : msets_scope.

  Delimit Scope msets_scope with msets.
  Open Scope msets_scope.
  Bind Scope msets_scope with Multiset.

Section ImplLemmas.

  Lemma empty_empty : forall M, (forall x, x / M = 0) -> M = empty.

  Proof.
    intros M mulM; destruct M.
    trivial.
    absurd (a / (a::M) = 0).
    simpl. destruct (eqA_dec a a); auto with sets.
    auto.
  Qed.

End ImplLemmas.

Section SpecConformation.

  Lemma mult_eqA_compat : forall M x y, x =A= y -> x / M = y / M.

  Proof.
     induction M.
     auto.
     intros; simpl.
     destruct (eqA_dec x a); destruct (eqA_dec y a); intros;
       solve [ absurd (y =A= a); eauto with sets
             | assert (x / M = y / M); auto ].
  Qed.

  Lemma mult_comp : forall l a,
    a / l = multiplicity (list_contents eqA eqA_dec l) a.

  Proof.
    induction l.
    auto.
    intro a0; simpl.
    destruct (eqA_dec a0 a); destruct (eqA_dec a a0); simpl;
    rewrite <- (IHl a0); (reflexivity || absurd (a0 =A= a); auto with sets).
  Qed.

  Lemma multeq_meq : forall M N, (forall x, x / M = x / N) -> M =mul= N.

  Proof.
    unfold meq. intros M N mult_MN x. rewrite <- !mult_comp. exact (mult_MN x).
  Qed.

  Lemma meq_multeq : forall M N, M =mul= N -> forall x, x / M = x / N.

  Proof.
    unfold meq, permutation, Multiset.meq.
    intros M N eqMN x. rewrite !mult_comp. exact (eqMN x).
  Qed.

  Lemma empty_mult : forall x, mult x empty = 0.

  Proof. auto. Qed.

  Lemma union_mult : forall M N x,
                       (x/(M + N))%msets = ((x/M)%msets + (x/N)%msets)%nat.

  Proof.
    induction M; auto.
    intros N x; simpl. destruct (eqA_dec x a); auto. rewrite IHM. auto.
  Qed.

  Lemma diff_empty_l : forall M, empty - M = empty.

  Proof.
    induction M; auto.
  Qed.

  Lemma diff_empty_r : forall M, M - empty = M.

  Proof.
    induction M; auto.
  Qed.

  Lemma mult_remove_in : forall x a M,
    x =A= a -> (x / (rem a M))%msets = ((x / M)%msets - 1)%nat.

  Proof.
    induction M.
    auto.
    intro x_a.
    simpl; destruct (eqA_dec x a0); destruct (eqA_dec a a0); 
      simpl; try solve [absurd (x =A= a); eauto with sets].
    auto with arith.
    destruct (eqA_dec x a0).
    contr.
    auto.
  Qed.

  Lemma mult_remove_not_in : forall M a x,
    ~ x =A= a -> x / (rem a M) = x / M.

  Proof.
    induction M; intros.
    auto.
    simpl; destruct (eqA_dec a0 a).
    destruct (eqA_dec x a);
      solve [absurd (x =A= a); eauto with sets | trivial].
    simpl; destruct (eqA_dec x a).
    rewrite (IHM a0 x); trivial.
    apply IHM; trivial.
  Qed.

  Lemma remove_perm_single : forall x a b M,
   x / (rem a (rem b M)) = x / (rem b (rem a M)).

  Proof.
    intros x a b M.
    case (eqA_dec x a); case (eqA_dec x b); intros x_b x_a.
     (* x=b,  x=a *)
    rewrite !mult_remove_in; trivial.
     (* x<>b, x=a *)
    rewrite mult_remove_in; trivial.
    do 2 (rewrite mult_remove_not_in; trivial).
    rewrite mult_remove_in; trivial.
     (* x=b,  x<>a *)
    rewrite mult_remove_not_in; trivial.
    do 2 (rewrite mult_remove_in; trivial).
    rewrite mult_remove_not_in; trivial.
     (* x<>b, x<>a *)
    rewrite !mult_remove_not_in; trivial.
  Qed.

  Lemma diff_mult_comp : forall x N M M',
    M =mul= M' -> x / (M - N) = x / (M' - N).

  Proof.
    induction N.
    intros; apply meq_multeq; trivial.
    intros M M' MM'.
    simpl.
    apply IHN.
    apply multeq_meq.
    intro x'.
    case (eqA_dec x' a).
    intro xa; rewrite !mult_remove_in; trivial.
    rewrite (meq_multeq MM'); trivial.
    intro xna; rewrite !mult_remove_not_in; trivial.
    apply meq_multeq; trivial.
  Qed.

  Lemma diff_perm_single : forall x a b M N, 
    x / (M - (a::b::N)) = x / (M - (b::a::N)).

  Proof.
    intros x a b M N.
    simpl; apply diff_mult_comp.
    apply multeq_meq.
    intro x'; apply remove_perm_single.
  Qed.

  Lemma diff_perm : forall M N a x,
    x / ((rem a M) - N) = x / (rem a (M - N)).

  Proof.
    intros M N; gen M; clear M.
    induction N.
    auto.
    intros M b x.
    change (rem b M - (a::N)) with (M - (b::a::N)).
    rewrite diff_perm_single.
    simpl; apply IHN.
  Qed.

  Lemma diff_mult_step_eq : forall M N a x,
    x =A= a -> x / (rem a M - N) = ((x / (M - N))%msets - 1)%nat.

  Proof.
    intros M N a x x_a.
    rewrite diff_perm.
    rewrite mult_remove_in; trivial.
  Qed.

  Lemma diff_mult_step_neq : forall M N a x,
    ~ x =A= a -> x / (rem a M - N) = x / (M - N).

  Proof.
    intros M N a x x_a.
    rewrite diff_perm.
    rewrite mult_remove_not_in; trivial.
  Qed.
 
  Lemma diff_mult : forall M N x,
                      x / (M - N) = ((x / M)%msets - (x / N)%msets)%nat.

  Proof.
    induction N.
     (* induction base *)
    simpl; intros; lia.
     (* induction step *)
    intro x; simpl.
    destruct (eqA_dec x a); simpl.
     (* x = a *)
    fold rem.
    rewrite (diff_mult_step_eq M N e).
    rewrite (IHN x).
    lia.
     (* x <> a *)
    fold rem.
    rewrite (diff_mult_step_neq M N n).
    exact (IHN x).
  Qed.

  Definition intersection_mult := inter_as_diff_ok mult diff diff_mult.

  Lemma singleton_mult_in : forall x y, x =A= y -> x / {{y}} = 1.

  Proof.
    intros; compute.
    case (eqA_dec x y); [trivial | contr].
  Qed.
  
  Lemma singleton_mult_notin : forall x y, ~x =A= y -> x / {{y}} = 0.

  Proof.
    intros; compute.
    case (eqA_dec x y); [contr | trivial].
  Qed.

  Lemma rev_list_ind_type : forall P : Multiset -> Type,
    P nil -> (forall a l, P (rev l) -> P (rev (a :: l))) -> forall l, P (rev l).

  Proof.
    induction l; auto.
  Defined.

  Lemma rev_ind_type : forall P : Multiset -> Type,
    P nil -> (forall x l, P l -> P (l ++ x :: nil)) -> forall l, P l.

  Proof.
    intros.
    gen (rev_involutive l).
    intros E; rewrite <- E.
    apply (rev_list_ind_type P).
    auto.
    simpl in |- *.
    intros.
    apply (X0 a (rev l0)).
    auto.
  Defined.

  Lemma mset_ind_type : forall P : Multiset -> Type,
    P empty -> (forall M a, P M -> P (union M {{a}})) -> forall M, P M.

  Proof.
    induction M as [| x M] using rev_ind_type.
    exact X.
    exact (X0 M x IHM).
  Defined.
 
End SpecConformation.

  #[global] Hint Unfold meq 
	      empty
              singleton
              mult
              union
              diff : multisets.

  #[global] Hint Resolve mult_eqA_compat 
               meq_multeq
               multeq_meq
               empty_mult
               union_mult
               diff_mult
               intersection_mult
               singleton_mult_in
               singleton_mult_notin : multisets.

  Hint Rewrite empty_mult
               union_mult
	       diff_mult
	       intersection_mult using trivial : multisets.

End MultisetList.
