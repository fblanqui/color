(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-04-25

monotone polynomials
*)

(* $Id: MonotonePolynom.v,v 1.8 2007-05-29 13:05:35 blanqui Exp $ *)

Set Implicit Arguments.

Require Export PositivePolynom.

Open Local Scope Z_scope.

Definition pmonotone n (p : poly n) := coef_pos p
  /\ forall i (H : lt i n), 0 < coef (mxi H) p.

(***********************************************************************)
(** tactics *)

Ltac montacrec :=
  match goal with
    | H:lt _ O |- _ => elimtype False; apply (lt_n_O _ H)
    | H:lt ?i (S _) |- _ =>
      destruct i;
	[(vm_compute; try refl)
          | (generalize (lt_S_n H); intro; montacrec)]
    |  _ => idtac
  end.

Ltac normalize_arity :=
  match goal with
    | H : lt _ ?a |- _ => normalize_in H a
    | _ => idtac
  end.

Ltac montac := intros; normalize_arity; montacrec.

(*Ltac postac := simpl; intuition; (idtac || trivial || omega).*)
Ltac postac := vm_compute; intuition; try discriminate.

Ltac destruct_symbol :=
  match goal with
    | f : _ |- _ => destruct f; destruct_symbol
    | _ => idtac
  end.

Ltac pmonotone :=
  intro f; unfold pmonotone, coef_pos;
    destruct_symbol; (split; [postac | montac]).

(***********************************************************************)
(** alternative definition *)

Definition pmonotone' n (p : poly n) := coef_pos p
  /\ forall i (H : lt i n), exists p1, exists c, exists p2,
    0 < c /\ p = p1 ++ (c, mxi H) :: p2.

Lemma pmonotone_imp_pmonotone' : forall n (p : poly n),
  pmonotone p -> pmonotone' p.

Proof.
intros n p (H1, H2).
split. auto.
intros i Hi. generalize (H2 i Hi). clear H2.
generalize dependent p. intro p. elim p.
 intros H1 H2.
 absurd (coef (mxi Hi) nil = 0). omega. simpl. reflexivity.
 intros (c, m) p' Hrec H1. simpl in H1. generalize H1. clear H1.
 intros (H1, H2). simpl.
 case (monom_eq_dec (mxi Hi) m); intro Hm; simpl.
  elim (Z_le_lt_eq_dec _ _ H1); clear H1. intro H1.

   (* If 0<c, it's easy to build the required elements *)
   intro H'. exists (pzero n). exists c. exists p'.
   split. assumption. simpl. subst m. reflexivity.

   (* if c=0, we must use the induction hypothesis *)
   intro Hc. subst c. subst m. simpl. intro H3.
   elim (Hrec H2 H3). clear Hrec. intros p'1 H. elim H. clear H. intros c' H.
   elim H. clear H. intros p'2 (Hc', Hp').
   exists ((0, mxi Hi) :: p'1).
   exists c'. exists p'2.
   split. assumption.
   rewrite Hp'. reflexivity.

  intro H3. elim (Hrec H2 H3). clear H2. clear H3.
  intros p'1 H. elim H. clear H. intros c' H. elim H. clear H.
  intros p'2 (Hc', Hp').
  exists ((c, m) :: p'1). exists c'. exists p'2.
  split. assumption.
  subst p'. simpl. reflexivity.
Qed.

(***********************************************************************)
(** monotony wrt evaluation *)

Lemma meval_monotone_D : forall i (vi : vec i) (mi : monom i)
  j (vj : vec j) (mj : monom j) k x y (Hx : 0 <= x) (Hy : 0 <= y), x<=y -> 
  meval (Vapp mi (Vcons k mj)) (vals (Vapp vi (Vcons (inj Hx) vj)))
  <= meval (Vapp mi (Vcons k mj)) (vals (Vapp vi (Vcons (inj Hy) vj))).

Proof.
intros. do 2 rewrite Vmap_app. simpl Vmap. do 2 rewrite meval_app.
apply Zmult_le_compat_l. simpl meval. apply Zmult_le_compat_r.
apply power_le_compat; assumption. apply pos_meval. apply pos_meval.
Qed.

Lemma coef_pos_monotone_peval_Dle : forall n (p : poly n) (H : coef_pos p),
  Vmonotone (peval_D H) Dle.

Proof.
unfold Vmonotone, Dle, peval_D. unfold Vmonotone_i, restrict. unfold monotone.
intros n p H_coef_pos i j Hij vi vj. destruct x as (x, Hx).
destruct y as (y, Hy). simpl. intro Hxy.
generalize dependent p. intro p. elim p.
 intro. simpl. omega.
 unfold coef_pos. intros (c, m) p' Hrec H_coef_pos.
 simpl in H_coef_pos. generalize H_coef_pos. clear H_coef_pos.
 intros (H_pos_c, H_coef_pos_p').
 generalize (Hrec H_coef_pos_p'). clear Hrec. clear H_coef_pos_p'. intro H.
 lazy beta iota delta [peval]. fold peval.
 apply Zplus_le_compat.
  2: apply H.
  clear H.
  apply Zmult_le_compat_l.
   2: assumption.
   rewrite (Vbreak_eq_app_cast Hij m).
   set (mi := (fst (Vbreak (n1:=i) (n2:=S j) (Vcast m (sym_equal Hij))))).
   set (mj := (snd (Vbreak (n1:=i) (n2:=S j) (Vcast m (sym_equal Hij))))).
   rewrite (VSn_eq mj).
   case Hij. simpl. repeat rewrite Vcast_refl.
   apply meval_monotone_D.
   assumption.
Qed.

Implicit Arguments coef_pos_monotone_peval_Dle [n p i j x y].

Lemma pmonotone'_imp_monotone_peval_Dlt :
  forall n (p : poly n) (H: pmonotone' p), Vmonotone (peval_D (proj1 H)) Dlt.

Proof.
unfold pmonotone', Vmonotone. intros n p (H_coef_pos_p, H_pmonotone_p) i j Hij.
generalize (H_pmonotone_p _ (i_lt_n (sym_equal Hij))).
intro H. elim H. clear H. intros p1 H. elim H. clear H. intros c H. elim H.
clear H. intros p2 (H, H'). subst p.
generalize (coef_pos_app H_coef_pos_p).
intros (H_coef_pos_p1, H').
generalize (coef_pos_cons H'). clear H'. intros (H', H_coef_pos_p2). clear H'.
unfold Vmonotone_i, Dlt, peval_D. unfold monotone, restrict.
intros vi vj. destruct x as (x, Hx). destruct y as (y, Hy). simpl.
intro Hxy. clear H_coef_pos_p.
do 2 rewrite peval_app.
apply Zplus_le_lt_compat.
 generalize (coef_pos_monotone_peval_Dle H_coef_pos_p1).
 unfold Vmonotone, Dle, peval_D. unfold Vmonotone_i, restrict. unfold monotone.
 intro H'.
 generalize (H' _ _ Hij vi vj (exist pos x Hx) (exist pos y Hy)).
 simpl. clear H'. intro H'. apply H'. omega.
 lazy beta iota delta [peval]. fold peval.
 apply Zplus_lt_le_compat.
  apply Zmult_lt_compat_l. assumption.
  do 2 rewrite meval_xi.
  do 2 rewrite Vmap_cast. case Hij. simpl.
  clear H_pmonotone_p. clear Hij. generalize dependent i. intro i. elim i.
   intro vi. rewrite (VO_eq vi). simpl. assumption.
   intros i' Hrec vi. rewrite (VSn_eq vi). simpl Vapp.
   simpl Vmap. simpl Vnth. generalize (Hrec (Vtail vi)). clear Hrec. intro H'.
   assert (H'' : i_lt_n (refl_equal (i' + S j)%nat) = lt_S_n
     (@i_lt_n (S (i' + S j)) (S i') _ (refl_equal (S (i' + S j))))).
   apply lt_unique.
   rewrite <- H''. assumption.
 generalize (coef_pos_monotone_peval_Dle H_coef_pos_p2).
 unfold Vmonotone, Dle, peval_D. unfold Vmonotone_i, restrict. unfold monotone.
 intro H'.
 generalize (H' _ _ Hij vi vj (exist pos x Hx) (exist pos y Hy)).
 simpl. clear H'. intro H'. apply H'. omega.
Qed.

Lemma pmonotone_imp_monotone_peval_Dlt : forall n (p : poly n) (H: pmonotone p),
  Vmonotone (peval_D (proj1 H)) Dlt.

Proof.
intros n p H.
generalize (pmonotone'_imp_monotone_peval_Dlt (pmonotone_imp_pmonotone' H)).
unfold Vmonotone, Dlt, Vmonotone_i, peval_D, restrict, monotone.
intros H0 i j Hij vi vj. destruct x as (x, Hx). destruct y as (y, Hy).
simpl. intro Hxy.
generalize (H0 i j Hij vi vj (exist _ x Hx) (exist _ y Hy) Hxy). clear H0.
simpl. intuition.
Qed.

Lemma pmonotone'_imp_monotone_peval_Dle :
  forall n (p : poly n) (H: pmonotone' p), Vmonotone (peval_D (proj1 H)) Dle.

Proof.
unfold pmonotone', Vmonotone. intros n p (H_coef_pos_p, H_pmonotone_p) i j Hij.
generalize (H_pmonotone_p _ (i_lt_n (sym_equal Hij))).
intro H. elim H. clear H. intros p1 H. elim H. clear H. intros c H. elim H.
clear H. intros p2 (H, H'). subst p.
generalize (coef_pos_app H_coef_pos_p).
intros (H_coef_pos_p1, H').
generalize (coef_pos_cons H'). clear H'. intros (H', H_coef_pos_p2). clear H'.
unfold Vmonotone_i, Dle, peval_D. unfold monotone, restrict.
intros vi vj. destruct x as (x, Hx). destruct y as (y, Hy). simpl.
intro Hxy. clear H_coef_pos_p.
do 2 rewrite peval_app.
apply Zplus_le_compat.
 generalize (coef_pos_monotone_peval_Dle H_coef_pos_p1).
 unfold Vmonotone, Dle, peval_D. unfold Vmonotone_i, restrict. unfold monotone.
 intro H'.
 generalize (H' _ _ Hij vi vj (exist pos x Hx) (exist pos y Hy)).
 simpl. clear H'. intro H'. apply H'. omega.
 lazy beta iota delta [peval]. fold peval.
 apply Zplus_le_compat.
  apply Zmult_le_compat_l.
  do 2 rewrite meval_xi.
  do 2 rewrite Vmap_cast. case Hij. simpl.
  clear H_pmonotone_p. clear Hij. generalize dependent i. intro i. elim i.
   intro vi. rewrite (VO_eq vi). simpl. assumption.
   intros i' Hrec vi. rewrite (VSn_eq vi). simpl Vapp.
   simpl Vmap. simpl Vnth. generalize (Hrec (Vtail vi)). clear Hrec. intro H'.
   assert (H'' : i_lt_n (refl_equal (i' + S j)%nat) = lt_S_n
     (@i_lt_n (S (i' + S j)) (S i') _ (refl_equal (S (i' + S j))))).
   apply lt_unique.
   rewrite <- H''. assumption. omega.
 generalize (coef_pos_monotone_peval_Dle H_coef_pos_p2).
 unfold Vmonotone, Dle, peval_D. unfold Vmonotone_i, restrict. unfold monotone.
 intro H'.
 generalize (H' _ _ Hij vi vj (exist pos x Hx) (exist pos y Hy)).
 simpl. clear H'. intro H'. apply H'. assumption.
Qed.

Lemma pmonotone_imp_monotone_peval_Dle : forall n (p : poly n) (H: pmonotone p),
  Vmonotone (peval_D (proj1 H)) Dle.

Proof.
intros n p H.
generalize (pmonotone'_imp_monotone_peval_Dle (pmonotone_imp_pmonotone' H)).
unfold Vmonotone, Dle, Vmonotone_i, peval_D, restrict, monotone.
intros H0 i j Hij vi vj. destruct x as (x, Hx). destruct y as (y, Hy).
simpl. intro Hxy.
generalize (H0 i j Hij vi vj (exist _ x Hx) (exist _ y Hy) Hxy). clear H0.
simpl. intuition.
Qed.
