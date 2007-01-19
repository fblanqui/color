(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Solange Coupet-Grimal and William Delobel, 2006-01-09

Definition and properties of lexicographic order on lists of elements
of a setoid. In particular, proofs that lex 'transmits' strict partial
order property, and is a lifting.
*)

(* $Id: LexicographicOrder.v,v 1.3 2007-01-19 17:22:40 blanqui Exp $ *)

Require Export RelExtras.
Require Export ListUtil.
Require Export WfUtil.

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
      simpl; generalize (IHss ts H0); auto with arith.
    Qed.
    
    Lemma SPO_to_lex_SPO : forall (ss : list ES.A), 
      (forall s, In s ss ->
        (forall t u, r s t -> r t u -> r s u) /\ (r s s -> False)) ->
      (forall (ts us : list ES.A),
        lex ss ts -> lex ts us -> lex ss us) /\ (lex ss ss -> False).

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
      apply H2; assumption.
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
      length l = n -> accs r l -> Restricted_acc (accs r) lex l.

    Proof.
      intro n; induction n as [ | n IHn]; intros l Hl Haccs.
      destruct l; [constructor | inversion Hl].
      intros l' Hl' Hlex; inversion Hlex.
      destruct l as [ | h l]; [inversion Hl | idtac].
      assert (acc_h : Acc r h).
      apply Haccs; left; trivial.
      assert (accs_l : forall (a : ES.A), In a l -> Acc r a).
      intros s s_in_l; apply Haccs; right; trivial.
      assert (Hl2 : length l = n).
      inversion Hl; trivial.
      generalize (IHn l Hl2 accs_l).
      clear Hl Haccs.
      generalize dependent l.
      induction acc_h as [h acc_h IHh].
      intros l accs_l Hl Hacc.
      induction Hacc as [l Hacc IHl].
      constructor.
      intros l' Hl' Hlex.
      destruct l' as [ | h' l'].
      inversion Hlex.
      assert (accs_l' : forall (a : ES.A), In a l' -> Acc r a).
      intros t Ht; apply Hl'; right; trivial.
      clear Hl'.
      inversion Hlex; subst.
      apply IHh; trivial.
      apply IHn; trivial.
      apply IHl; trivial.
      cut (length (h :: l') = length ( h :: l)).
      simpl; auto with arith.
      generalize Hlex; apply lex_length.
    Qed.
    
    Section Lex_and_one_less.

      Lemma one_less2lex : forall l l', one_less r l l' -> lex l l'.

      Proof.
        intros l l' H1; inversion H1; subst. 
        generalize dependent l; induction p as [ | p]; intros l Hl H1.
        destruct l as [|h l]; inversion Hl.
        subst; simpl; constructor; trivial.
        destruct l as [|h l]; inversion Hl.
        subst; simpl; constructor 2; trivial.
        apply IHp; trivial.
        apply (@one_less_cons _ r l (l [p := a']) p a a'); trivial.
      Qed.

    End Lex_and_one_less.

  End Lex.

  Lemma lex_lifting : forall (r : relation ES.A) (l : list ES.A), 
    accs r l -> Restricted_acc (accs r) (lex r) l.

  Proof.
    intros r l; apply (lex_lifting_aux r (length l) l); trivial.
  Qed.

End LexOrder.
