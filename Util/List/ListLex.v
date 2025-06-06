(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Solange Coupet-Grimal and William Delobel, 2006-01-09
- Adam Koprowski, 2007-06-01 added Decidability section

Definition and properties of lexicographic order on lists of elements
of a setoid. In particular, proofs that lex 'transmits' strict partial
order property, and is a lifting.
*)

From CoLoR Require Import RelExtras ListUtil AccUtil LogicUtil.
From Stdlib Require Peano_dec.

Module LexOrder (ES : Eqset).

  Section Lex.

    Variable r : relation ES.A.
    
    Inductive lex : relation (list ES.A) :=
      | lex1 : forall h h' (l l' : list ES.A),
	r h h' -> length l = length l' -> lex (h::l) (h'::l')
      | lex2 : forall (h : ES.A) (l l' : list ES.A),
	lex l l' -> lex (h::l) (h::l').
    
    Lemma lex_length : forall ss ts : list ES.A,
      lex ss ts -> length ss = length ts.

    Proof.
      induction ss as [ | s ss IHss]; intros ts Hlex.
      inversion Hlex; trivial.
      destruct ts as [ | t ts]; inversion Hlex; subst.
      simpl; auto with arith.
      simpl; gen (IHss ts H0); auto with arith.
    Qed.
    
    Lemma SPO_to_lex_SPO : forall (ss : list ES.A), 
      (forall s, In s ss ->
        (forall t u, r s t -> r t u -> r s u) /\ (r s s -> False)) ->
      (forall ts us : list ES.A, lex ss ts -> lex ts us -> lex ss us)
      /\ (lex ss ss -> False).

    Proof.
      induction ss as [ | s ss IHss]; intro Hss; split.
      intros ts us Hss_ts Hts_us; inversion Hss_ts; subst; trivial.
      intro H; inversion H.
      intros ts us Hss_ts Hts_us.
      assert (Hs : In s (s::ss)). 
      left; trivial.
      elim (Hss s Hs); intros Hss' Hss''.
      destruct ts as [ | t ts]; inversion Hss_ts; subst.
      destruct us as [ | u us]; inversion Hts_us; subst.
      constructor 1.
      apply Hss' with t; try left; trivial.
      rewrite H4; trivial.
      constructor 1; trivial.
      rewrite H4; apply lex_length; trivial.
      destruct us as [ | u us]; inversion Hts_us; subst.
      constructor 1; trivial.
      rewrite <- H5; apply lex_length; trivial.
      constructor 2.
      elim IHss. 
      intros H2 H3; apply (H2 ts); trivial.
      intros s s_in_ss; split.
      elim (Hss s); try right; trivial.
      elim (Hss s); try right; trivial.
      intro H; inversion H; subst.
      elim (Hss s); try left; trivial; intros H1 H2.
      apply H2; hyp.
      elim IHss. 
      intros H2 H3; apply H3; trivial.
      intros s' s'_in_ss; apply (Hss s'); try right; trivial.
    Qed.
  
    Lemma irrefl_to_lex_irrefl : forall (ss : list ES.A), 
      (forall s, In s ss -> r s s -> False) -> lex ss ss -> False.

    Proof.
      intro ss; induction ss as [ | h ss IHss]; intros Hss Hlex;
        inversion Hlex; subst.
      apply Hss with h; try left; trivial.
      apply IHss; trivial.
      intros s s_in_ss; apply Hss; try right; trivial.
    Qed.

    Lemma lex_lifting_aux : forall n (l : list ES.A), 
      length l = n -> Accs r l -> Restricted_acc (Accs r) lex l.

    Proof.
      intro n; induction n as [ | n IHn]; intros l Hl HAccs.
      destruct l; [constructor | inversion Hl].
      intros l' Hl' Hlex; inversion Hlex.
      destruct l as [ | h l]; [inversion Hl | idtac].
      assert (acc_h : Acc r h).
      apply HAccs; left; trivial.
      assert (Accs_l : forall (a : ES.A), In a l -> Acc r a).
      intros s s_in_l; apply HAccs; right; trivial.
      assert (Hl2 : length l = n).
      inversion Hl; trivial.
      gen (IHn l Hl2 Accs_l).
      clear Hl HAccs.
      generalize dependent l.
      induction acc_h as [h acc_h IHh].
      intros l Accs_l Hl Hacc.
      induction Hacc as [l Hacc IHl].
      constructor.
      intros l' Hl' Hlex.
      destruct l' as [ | h' l'].
      inversion Hlex.
      assert (Accs_l' : forall (a : ES.A), In a l' -> Acc r a).
      intros t Ht; apply Hl'; right; trivial.
      clear Hl'.
      inversion Hlex; subst.
      apply IHh; trivial.
      apply IHn; trivial.
      apply IHl; trivial.
      cut (length (h :: l') = length ( h :: l)).
      simpl; auto with arith.
      gen Hlex; apply lex_length.
    Qed.
    
    Section Lex_and_one_less.

      Lemma one_less2lex : forall l l', one_less r l l' -> lex l l'.

      Proof.
        intros l l' H1; inversion H1; subst. 
        generalize dependent l; induction p as [ | p]; intros l Hl H1.
        destruct l as [|h l]; inversion H1.
        subst; simpl; constructor; trivial.
        destruct l as [|h l]; inversion H1.
        subst; simpl; constructor 2; trivial.
        apply IHp; trivial.
        apply (@one_less_cons _ r l (l [p := a']) p a a'); trivial.
      Qed.

    End Lex_and_one_less.

  End Lex.

  Lemma lex_lifting : forall (r : relation ES.A) (l : list ES.A), 
    Accs r l -> Restricted_acc (Accs r) (lex r) l.

  Proof.
    intros r l; apply (lex_lifting_aux r (length l) l); trivial.
  Qed.

  Section Decidability.

    Import Peano_dec.

    Variable eqA_dec : forall a b : ES.A, {a = b} + {~a = b}.

    Lemma lex_dec : forall R l l',
      (forall a b, In a l -> In b l' -> {R a b} + {~R a b}) ->
      {lex R l l'} + {~lex R l l'}.

    Proof.
      induction l; intros.
      right. intro nil_l. inversion nil_l.
      revert X; destruct l'; intro.
      right. intro al_nil. inversion al_nil.
      destruct (X a a0); auto with datatypes.
      destruct (eq_nat_dec (length l) (length l')).
      left. constructor; trivial.
      right. intro al_nil. inversion al_nil; intuition.
      apply n. apply lex_length with R. hyp.
      destruct (eqA_dec a a0).
      rewrite e. destruct (IHl l'). intuition auto with *.
      left. constructor 2. hyp.
      right. intro ll'. inversion ll'; intuition.
      apply n. congruence.
      right. intro ll'. inversion ll'; intuition.
    Defined.

  End Decidability.

  Section Homomorphism.

    Variable R : relation ES.A.
    Variable f : ES.A -> ES.A.

    Lemma lex_homomorphic : forall l l',
      (forall x x', In x l -> In x' l' -> R x x' -> R (f x) (f x')) ->
      lex R l l' -> lex R (map f l) (map f l').

    Proof.
      induction l; intros.
      inversion H0.
      destruct l'. inversion H0.
      simpl. inversion H0.
      constructor 1. apply H; auto with datatypes.
      do 2 rewrite length_map. hyp.
      constructor 2. apply IHl.
      intros. apply H; intuition auto with *. hyp.
    Qed.

  End Homomorphism.

End LexOrder.
