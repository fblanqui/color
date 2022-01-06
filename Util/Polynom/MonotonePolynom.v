(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-04-25
- Adam Koprowski, 2008-05-27, 
    introduced distinction of weak/strong monotonicity

monotone polynomials
*)

Set Implicit Arguments.

From CoLoR Require Import Polynom PositivePolynom NaryFunction VecUtil
     LogicUtil ListUtil ZUtil RelUtil NatUtil BoundNat.

Local Open Scope Z_scope.

(***********************************************************************)
(** definition of weak and strong monotony conditions *)

Definition pweak_monotone n (p : poly n) := coef_pos p.

Definition pstrong_monotone n (p : poly n) := pweak_monotone p /\
  forall i (H : lt i n), 0 < coef (mxi H) p.

(***********************************************************************)
(** alternative definition of monotony conditions *)

Definition pstrong_monotone' n (p : poly n) := coef_pos p
  /\ forall i (H : lt i n), exists p1, exists c, exists p2,
    0 < c /\ p = p1 ++ (c, mxi H) :: p2.

Lemma pmonotone_imp_pmonotone' : forall n (p : poly n),
  pstrong_monotone p -> pstrong_monotone' p.

Proof.
intros n p (H1, H2).
split. auto.
intros i Hi. gen (H2 i Hi). clear H2.
generalize dependent p. intro p. elim p.
 intros H1 H2.
 absurd (coef (mxi Hi) nil = 0). lia. simpl. refl.
 intros (c, m) p' Hrec H1. simpl in H1. gen H1. clear H1.
 intros (H1, H2). simpl.
 case (monom_eq_dec (mxi Hi) m); intro Hm; simpl.
  elim (Z_le_lt_eq_dec _ _ H1); clear H1. intro H1.

   (* If 0<c, it's easy to build the required elements *)
   intro H'. exists (pzero n). exists c. exists p'.
   split. hyp. simpl. subst m. refl.

   (* if c=0, we must use the induction hypothesis *)
   intro Hc. subst c. subst m. simpl. intro H3.
   elim (Hrec H2 H3). clear Hrec. intros p'1 H. elim H. clear H. intros c' H.
   elim H. clear H. intros p'2 (Hc', Hp').
   exists ((0, mxi Hi) :: p'1).
   exists c'. exists p'2.
   split. hyp.
   rewrite Hp'. refl.

  intro H3. elim (Hrec H2 H3). clear H2. clear H3.
  intros p'1 H. elim H. clear H. intros c' H. elim H. clear H.
  intros p'2 (Hc', Hp').
  exists ((c, m) :: p'1). exists c'. exists p'2.
  split. hyp.
  subst p'. simpl. refl.
Qed.

(***********************************************************************)
(** correctness of monotony conditions *)

Lemma meval_monotone_D : forall i (vi : vec i) (mi : monom i)
  j (vj : vec j) (mj : monom j) k x y (Hx : 0 <= x) (Hy : 0 <= y), x<=y -> 
  meval (Vapp mi (Vcons k mj)) (vals (Vapp vi (Vcons (inj Hx) vj)))
  <= meval (Vapp mi (Vcons k mj)) (vals (Vapp vi (Vcons (inj Hy) vj))).

Proof.
intros. rewrite !Vmap_app. simpl Vmap. rewrite !meval_app.
apply Zmult_le_compat_l. simpl meval. apply Zmult_le_compat_r.
apply power_le_compat; hyp. apply pos_meval. apply pos_meval.
Qed.

Lemma coef_pos_monotone_peval_Dle : forall n (p : poly n) (H : coef_pos p),
  Vmonotone1 (peval_D H) Dle.

Proof.
unfold Vmonotone1, Vmonotone, Dle, peval_D, Vmonotone_i, restrict, monotone.
intros n p H_coef_pos i j Hij vi vj. destruct x as (x, Hx).
destruct y as (y, Hy). simpl. intro Hxy.
generalize dependent p. intro p. elim p.
 intro. simpl. lia.
 unfold coef_pos. intros (c, m) p' Hrec H_coef_pos.
 simpl in H_coef_pos. gen H_coef_pos. clear H_coef_pos.
 intros (H_pos_c, H_coef_pos_p').
 gen (Hrec H_coef_pos_p'). clear Hrec. clear H_coef_pos_p'. intro H.
 lazy beta iota delta [peval]. fold peval.
 apply Zplus_le_compat.
  2: apply H.
  clear H.
  apply Zmult_le_compat_l.
   2: hyp.
   rewrite (Vbreak_eq_app_cast Hij m).
   set (mi := (fst (Vbreak (n1:=i) (n2:=S j) (Vcast m (sym_equal Hij))))).
   set (mj := (snd (Vbreak (n1:=i) (n2:=S j) (Vcast m (sym_equal Hij))))).
   rewrite (VSn_eq mj).
   case Hij. simpl.
   apply meval_monotone_D.
   hyp.
Qed.

Arguments coef_pos_monotone_peval_Dle [n p] _ [i j] _ _ _ [x y] _ _.

Lemma pmonotone'_imp_monotone_peval_Dlt :
  forall n (p : poly n) (H: pstrong_monotone' p), 
    Vmonotone1 (peval_D (proj1 H)) Dlt.

Proof.
intros n p (H_coef_pos_p, H_pmonotone_p) i j Hij.
gen (H_pmonotone_p _ (i_lt_n (sym_equal Hij))).
intro H. elim H. clear H. intros p1 H. elim H. clear H. intros c H. elim H.
clear H. intros p2 (H, H'). subst p.
gen (coef_pos_app H_coef_pos_p).
intros (H_coef_pos_p1, H').
gen (coef_pos_cons H'). clear H'. intros (H', H_coef_pos_p2). clear H'.
unfold Vmonotone_i, Dlt, peval_D. unfold monotone, restrict.
intros vi vj. destruct x as (x, Hx). destruct y as (y, Hy). simpl.
intro Hxy. clear H_coef_pos_p.
rewrite !peval_app.
apply Zplus_le_lt_compat.
 gen (coef_pos_monotone_peval_Dle H_coef_pos_p1).
 unfold Vmonotone, Dle, peval_D. unfold Vmonotone_i, restrict. unfold monotone.
 intro H'.
 gen (H' _ _ Hij vi vj (exist Hx) (exist Hy)).
 simpl. clear H'. intro H'. apply H'. lia.
 lazy beta iota delta [peval]. fold peval.
 apply Zplus_lt_le_compat.
  apply Zmult_lt_compat_l. hyp.
  rewrite !meval_xi, !Vmap_cast. case Hij. simpl.
  clear H_pmonotone_p. clear Hij. generalize dependent i. intro i. elim i.
   intro vi. rewrite (VO_eq vi). simpl. hyp.
   intros i' Hrec vi. rewrite (VSn_eq vi). simpl Vapp.
   simpl Vmap. simpl Vnth. gen (Hrec (Vtail vi)). clear Hrec. intro H'.
   assert (H'' : i_lt_n (eq_refl (i' + S j)%nat) = lt_S_n
     (@i_lt_n (S (i' + S j)) (S i') _ (eq_refl (S (i' + S j))))).
   apply lt_unique.
   rewrite <- H''. hyp.
 gen (coef_pos_monotone_peval_Dle H_coef_pos_p2).
 unfold Vmonotone, Dle, peval_D. unfold Vmonotone_i, restrict. unfold monotone.
 intro H'.
 gen (H' _ _ Hij vi vj (exist Hx) (exist Hy)).
 simpl. clear H'. intro H'. apply H'. lia.
Qed.

Lemma pmonotone_imp_monotone_peval_Dlt : forall n (p : poly n) 
  (wm : pweak_monotone p) (sm : pstrong_monotone p), 
  Vmonotone1 (peval_D wm) Dlt.

Proof.
intros n p wm sm.
gen (pmonotone'_imp_monotone_peval_Dlt (pmonotone_imp_pmonotone' sm)).
unfold Vmonotone1, Vmonotone, Dlt, Vmonotone_i, peval_D, restrict, monotone.
intros H0 i j Hij vi vj. destruct x as (x, Hx). destruct y as (y, Hy).
simpl. intro Hxy.
gen (H0 i j Hij vi vj (exist Hx) (exist Hy) Hxy). clear H0.
simpl. intuition.
Qed.

(***********************************************************************)
(** boolean functions for monotony *)

Definition bpweak_monotone n (p : poly n) := bcoef_pos p.
Definition bpweak_monotone_ok n (p : poly n) := bcoef_pos_ok p.

From CoLoR Require Import BoolUtil.

Definition bpstrong_monotone n (p : poly n) :=
  bcoef_pos p && forallb (fun x => is_pos (coef (mxi (N_prf x)) p)) (L n).

Lemma bpstrong_monotone_ok : forall n (p : poly n),
  bpstrong_monotone p = true <-> pstrong_monotone p.

Proof.
induction p.
(* nil *)
unfold pstrong_monotone, bpstrong_monotone, pweak_monotone. simpl.
intuition. unfold L in H. destruct n. lia. destruct n; discr.
destruct n. refl. ded (H1 n (le_n (S n))). lia.
(* cons *)
destruct a. intuition.
(* -> *)
unfold pstrong_monotone, pweak_monotone.
unfold bpstrong_monotone, bcoef_pos in H1. Opaque coef. simpl in *. 
rewrite !andb_eq in H1. intuition. change (bcoef_pos p = true) in H4.
rewrite <- is_not_neg_ok. hyp. rewrite <- bcoef_pos_ok. hyp.
assert (In (N_ H2) (L n)). apply In_L.
rewrite forallb_forall in H3. ded (H3 _ H5).
rewrite is_pos_ok in H6. simpl in H6. lia.
(* <- *)
unfold pstrong_monotone, pweak_monotone in H1.
unfold bpstrong_monotone, bcoef_pos. simpl in *.
rewrite !andb_eq. intuition. rewrite is_not_neg_ok. hyp.
change (bcoef_pos p = true). rewrite bcoef_pos_ok. hyp.
rewrite forallb_forall.
intros [i hi].  simpl. rewrite is_pos_ok.
ded (H3 _ hi). lia. Transparent coef.
Qed.

(***********************************************************************)
(** check monotony conditions *)

Definition is_pos_monom n (cm : Z * monom n) :=
  let (c, _) := cm in is_not_neg c.

Program Definition coef_pos_check n (p : poly n) : option (coef_pos p) :=
  match forallb (@is_pos_monom n) p with
  | true => Some _
  | false => None
  end.

Next Obligation.
  unfold pweak_monotone, coef_pos.
  apply forallb_imp_lforall with (@is_pos_monom n); auto.
  destruct x. unfold is_pos_monom. 
  destruct z; compute; intros; discr.
Qed.

Program Definition pweak_monotone_check n (p : poly n)
  : option (pweak_monotone p) := coef_pos_check p.

Program Definition check_coef_gt0 n (p : poly n) (i : N n) :
  option (0 < coef (mxi i) p)%Z :=
  let c := coef (mxi i) p in
    match Z_lt_dec 0 c with
    | left _ => Some _
    | _ => None
    end.

Program Definition pstrong_monotone_check n (p : poly n) :
  option (pstrong_monotone p) :=
  match pweak_monotone_check p with
  | None => None
  | _ =>    
    match check_seq (check_coef_gt0 p) with
    | None => None
    | _ => Some _
    end
  end.

Next Obligation.
Proof with auto; try congruence || discr.
  split. 
  destruct pweak_monotone_check...
  destruct (check_seq (check_coef_gt0 p))...
  refine (fun i H => l (N_ H)).
Qed.
