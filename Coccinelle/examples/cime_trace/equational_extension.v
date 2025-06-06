From Stdlib Require Import List Bool FunInd.
From CoLoR Require Import weaved_relation closure term_spec terminaison.
From CoLoR Require equational_theory_spec closure_extension.

Module Make  (Eqt:equational_theory_spec.EqTh).

Lemma one_step_list_same_length : 
  forall R l1 l2, one_step_list (Eqt.one_step R) l2 l1 -> length l1 = length l2.
Proof.
  intros R l1 l2 H; apply sym_eq; apply one_step_list_length_eq with (Eqt.one_step R); assumption.
Qed.

Lemma rwr_as_star : forall R t t', Eqt.rwr R t t' -> star _ (Eqt.one_step R) t t'.
Proof. 
  induction 1.
  apply star_R. assumption.

  apply star_trans with y;auto.
  right with x; [left | assumption].
Qed.

Lemma one_step_list_star_decompose_cons : 
  forall R x l l'', refl_trans_clos (one_step_list (Eqt.one_step R)) (x::l) l'' -> 
    exists x', exists l', 
      l'' = x'::l' /\ 
      refl_trans_clos (Eqt.one_step R) x x'/\
      refl_trans_clos (one_step_list (Eqt.one_step R)) l l'.
Proof.
  intros R x l l''. 
  set (l1 := x::l) in *.
  generalize (eq_refl l1); unfold l1 at 1;clearbody l1.
  intros H H0  .
  revert x l  H.
  induction H0. 
  rename x into l0.

  intros x l He;subst.
  exists x;exists l;repeat split;constructor.


  rename x into l';rename y into l.
  induction H. 
  inversion H;clear H;subst.  
  intros a b Heq;injection Heq;clear Heq;intros;subst.
  exists t2;exists l.
  repeat (assumption||constructor).
  intros a b Heq;injection Heq;clear Heq;intros;subst.
  exists t;exists l2.
  repeat (assumption||constructor).
  
  inversion H;clear H;subst;  intros;  injection H;clear H;intros;subst.
  destruct (IHtrans_clos _ _ (eq_refl _)) as [u [l'' [h1 [h2 h3]]]];clear IHtrans_clos.
  subst.
  exists u;exists l''.
  split. apply eq_refl.
  split.
  apply refl_trans_clos_is_trans with t2;  repeat (assumption||constructor).
  assumption.

  destruct (IHtrans_clos _ _ (eq_refl _)) as [u [l'' [h1 [h2 h3]]]];clear IHtrans_clos.
  subst.
  exists u;exists l''.
  split. apply eq_refl.
  split.
  assumption.
  apply refl_trans_clos_is_trans with l2;  repeat (assumption||constructor).
Qed.

Lemma one_step_list_star_decompose_nil : 
  forall R l'', refl_trans_clos (one_step_list (Eqt.one_step R)) nil l'' -> l'' = nil.
Proof.
  intros R l'' H.
  set (l:= @nil Eqt.T.term) in *.
  generalize (eq_refl l).
  unfold l at 1;clearbody l.
  induction H;intro;subst;auto.
  inversion H;clear H;subst;  inversion H0.
Qed.


Lemma one_step_list_star_l : forall  R l x y, 
  refl_trans_clos (Eqt.one_step R) x y -> 
  refl_trans_clos (one_step_list (Eqt.one_step R)) (x::l) (y::l).
Proof.
induction 1.
constructor.
constructor.
induction H.
repeat  (assumption || constructor).
constructor 2 with (y::l).
repeat  (assumption || constructor).
assumption.
Qed.

Lemma one_step_list_star_r : forall R l l' x, 
  refl_trans_clos (one_step_list (Eqt.one_step R)) l l' -> 
  refl_trans_clos (one_step_list (Eqt.one_step R)) (x::l) (x::l').
Proof.
induction 1.
constructor.
induction H.
repeat (exact H || constructor).
apply refl_trans_clos_is_trans with (x::y).
constructor.
constructor.
repeat (exact H || constructor).
assumption.
Qed.

Lemma one_step_list_refl_trans_clos : forall  R l l' x y, 
  refl_trans_clos (Eqt.one_step R) x y -> 
  refl_trans_clos (one_step_list (Eqt.one_step R)) l l' ->
  refl_trans_clos (one_step_list (Eqt.one_step R)) (x::l) (y::l').
Proof.
  intros R l l' x y H H0.

apply refl_trans_clos_is_trans with (x::l').
apply one_step_list_star_r. assumption.
apply one_step_list_star_l. assumption.
Qed.

Import Eqt.
Import T.
Import Relation_Definitions.
Lemma one_step_ind2
     : forall (R : relation term)
         (P : forall t t0 : term, one_step R t t0 -> Prop)
         (P0 : forall l l0 : list term, one_step_list (one_step R) l l0 -> Prop),
       (forall (t1 t2 : term) (a : axiom R t1 t2), P t1 t2 (at_top R t1 t2 a)) ->
       (forall (f0 : symbol) (l1 l2 : list term) (o : one_step_list (one_step R) l1 l2),
        P0 l1 l2 o -> P (Term f0 l1) (Term f0 l2) (in_context R f0 l1 l2 o)) ->
       (forall (t1 t2 : term) (l : list term) (o : one_step R t1 t2),
        P t1 t2 o -> P0 (t1 :: l) (t2 :: l) (head_step (one_step R) t1 t2 l o)) ->
       (forall (t : term) (l1 l2 : list term) (o : one_step_list (one_step R) l1 l2),
        P0 l1 l2 o -> P0 (t :: l1) (t :: l2) (tail_step t o)) ->
       forall (t t0 : term) (o : Eqt.one_step R t t0), P t t0 o
.
Proof.
  intros R P P0 H H0 H1 H2.
  fix one_step_ind2 3.
  intros t t0 [t1 t2 a|f l1 l2 o].
  apply H.
  apply H0.
  revert l1 l2 o.
  fix one_step_list_ind2 3 .
  intros l1 l2 [t1 t2 l a|t1 l1' l2' a].
  apply H1.
  apply one_step_ind2.
  apply H2.
  apply one_step_list_ind2.
Qed.

Lemma star_list : 
  forall R f l l', refl_trans_clos (one_step_list (one_step R)) l' l -> 
  refl_trans_clos (one_step R) (Term f l') (Term f l).
Proof.
  intros R f l l' H.
  induction H.
  constructor.
  constructor.
  induction H.
  constructor.
  constructor 2;assumption.
  
  constructor 2 with (Eqt.T.Term f y).
  constructor 2;assumption.
  assumption.
Qed.

Import closure_extension.

Lemma star_cons : forall R t l t' l', 
  refl_trans_clos (one_step R) t' t -> 
  refl_trans_clos (one_step_list (one_step R)) l' l -> 
  refl_trans_clos (one_step_list (one_step R)) (t'::l') (t::l).
Proof.
  intros R t l t' l' H H0.

  apply refl_trans_clos_is_trans with (t::l').
  clear H0.
  induction H.
  constructor.
  induction H.
  apply refl_trans_clos_with_R.
  constructor;assumption.

  apply refl_trans_clos_is_trans with (y::l').
  apply refl_trans_clos_with_R.
  constructor;assumption.
  assumption.

  clear H;induction H0.
  constructor.
  induction H.
  apply refl_trans_clos_with_R.
  constructor;assumption.
  apply refl_trans_clos_is_trans with (t::y).
  apply refl_trans_clos_with_R.
  constructor;assumption.
  assumption.
Qed.

Lemma cons_star : forall R t l t' l', 
  refl_trans_clos (one_step_list (one_step R)) (t'::l') (t::l) ->
  refl_trans_clos (one_step R) t' t/\
  refl_trans_clos (one_step_list (one_step R)) l' l.
Proof.
  intros R t l t' l' H.
  set (l1:= t'::l') in *; generalize (eq_refl l1);unfold l1 at 1;clearbody l1.
  set (l2:= t::l) in *; generalize (eq_refl l2);unfold l2 at 1;clearbody l2.
  revert t l t' l'.
  induction H.
  intros;do 2 subst.
  injection H0;clear H0;intros;subst.
  split;constructor.
  induction H.
  induction H.
  intros t l0 t' l' H0 H1.
  injection H0;injection H1;clear H0 H1.
  intros;repeat subst.
  split.
  constructor 2;constructor;assumption.
  constructor.
  intros tk l0 t' l' H0 H1.
  injection H0;injection H1;clear H0 H1.
  intros;repeat subst.
  split.
  constructor.
  constructor 2;constructor;assumption.
  intros t l t' l' H1 H2.
  subst.
  inversion H;subst.
  destruct (IHtrans_clos _ _ _ _ (eq_refl _) (eq_refl _)) as [h1 h2].
  clear IHtrans_clos H H0.
  split.
  inversion h1;subst;clear h1.
  constructor. constructor;assumption. 
  constructor. constructor 2 with t2; assumption. 
  assumption.
  destruct (IHtrans_clos _ _ _ _ (eq_refl _) (eq_refl _)) as [h1 h2].
  clear IHtrans_clos H H0.
  split.
  assumption.
  inversion h2;subst;clear h2.
  constructor. constructor;assumption. 
  constructor. constructor 2 with l2; assumption. 
Qed.



  Function inb (A:Type) (eq_bool: A -> A -> bool) (f:A) (l:list A) {struct l} : bool :=
    match l with 
      | nil => false 
      | g::l => orb (eq_bool g f) (inb A eq_bool f l)
    end.

  Lemma inb_equiv : 
    forall (A:Type) aeq_bool f l, (forall f g:A, f=g <-> aeq_bool f g = true) -> 
      (In f l <-> inb _ aeq_bool f l=true).
  Proof.
    intros A aeq_bool f l H.
    functional induction (inb _ aeq_bool f l).
    simpl;intuition auto with *.
    simpl.
    rewrite H.
    case (aeq_bool g f);simpl. clear;intuition.
    rewrite (IHb). intuition auto with *.
  Qed.

Section is_def.
  Variable defined_list : list symbol.
  Variables rules : relation term.
  Variables rule_list : list (term*term).
  Hypothesis rules_equiv : forall l r : term, rules r l <-> In (l, r) rule_list.
  
  Hypothesis  defined_list_equiv : 
    forall f : symbol,
      In f (defined_list) <-> defined rules f.

  Definition is_def f := 
      inb _ F.Symb.eq_bool f defined_list.

  Lemma is_def_equiv : 
    forall f : symbol,
      is_def f = true <-> defined rules f.
  Proof.
    intros f.
    unfold is_def.
    rewrite <- defined_list_equiv.
    rewrite (inb_equiv _ F.Symb.eq_bool) .
    reflexivity.
    clear;intros f g.
    generalize (F.Symb.eq_bool_ok f g).
    case (F.Symb.eq_bool f g);[tauto|intuition discriminate].
  Qed.  
End is_def.

End Make.
