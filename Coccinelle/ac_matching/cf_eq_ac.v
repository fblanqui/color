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


From Stdlib Require Import Setoid Arith List Morphisms.
From CoLoR Require Import closure more_list weaved_relation list_sort term_spec ac.

Set Implicit Arguments.

Module Type S.

Declare Module Import Ac : ac.S.

Import Ac.EqTh.T.

Parameter cf_eq_ac :
  forall t1 t2, well_formed t1 -> well_formed t2 -> 
  canonical_form t1 = canonical_form t2 -> ac t1 t2.

End S.

Module Make (Ac1 : ac.S) <: S with Module Ac := Ac1.

Module Ac := Ac1.
Import Ac1 EqTh Sort T F X LPermut.

Lemma split_cf :
  forall f, arity f = AC -> forall t u1 u2, well_formed t ->
  permut (flatten f (canonical_form t :: nil)) (u1 ++ u2) ->
   u1 = nil \/
   u2 = nil \/
   (exists t1, exists t2,
   well_formed t1 /\ well_formed t2 /\
   ac t (Term f (t1 :: t2 :: nil)) /\
   permut (flatten f (canonical_form t1 :: nil)) u1 /\ 
   permut (flatten f (canonical_form t2 :: nil)) u2).
Proof.
intros f Af t; pattern t; apply term_rec3; clear t.
(* t = Var _ *)
intros v l1 l2 _ P; simpl in P; 
destruct l1 as [ | t1 l1]; [left; trivial | idtac];
destruct l2 as [ | t2 l2]; [right; left; trivial | idtac];
generalize (list_permut.permut_length P); rewrite length_app; simpl;
rewrite Nat.add_comm; intro; discriminate.
(* t = Term g l *)
intros g l IHl l1 l2 Wt; simpl.
generalize (F.Symb.eq_bool_ok f g); case (F.Symb.eq_bool f g); [intro f_eq_g; subst g | intro f_diff_g]; intro P'.
(* f=g *)
subst; rewrite Af in P'; rewrite app_nil_r in P'.
assert (P : permut (flatten f (map canonical_form l)) (l1 ++ l2)).
rewrite <- P'; apply quick_permut.
clear P'; elim (well_formed_unfold Wt); rewrite Af; intros Wl Ll;
destruct l as [ | t1 l]; [absurd (0=2); auto with arith | idtac];
destruct l as [ | t2 l]; [absurd (1=2); auto with arith | idtac];
destruct l as [ | t3 l]; [idtac | absurd (S(S(S(length l)))=2); auto with arith];
replace (map canonical_form (t1 :: t2 :: nil)) with 
((canonical_form t1 :: nil) ++ canonical_form t2 :: nil) in P; trivial;
rewrite flatten_app in P;
assert (Wt1 := Wl t1 (or_introl _  (eq_refl t1)));
assert (Wt2 := Wl t2 (or_intror _ (or_introl _  (eq_refl t2))));
elim (ac_syntactic _ _ _ _ P); intros k1 [k2 [k3 [k4 [P2 [P1 [P3 P4]]]]]].
generalize (IHl t1 (or_introl _ (eq_refl _)) k3 k4 Wt1 P1);
intros [Hk3 | [Hk4 | [t11 [t12 [Wt11 [Wt12 [H1 [Q11 Q12]]]]]]]];
generalize (IHl t2 (or_intror _ (or_introl _ (eq_refl _))) k1 k2 Wt2 P2);
intros [Hk1 | [Hk2 | [t21 [t22 [Wt21 [Wt22 [H2 [Q21 Q22]]]]]]]].
(* k1 = nil, k3 = nil *)
subst; right; left; apply list_permut.permut_nil with term (@eq term); trivial.
(* k2 = nil, k3 = nil *)
subst; right; right; exists t1; exists t2; intuition.
unfold ac; apply th_refl.
rewrite P1; apply permut_sym; trivial.
rewrite P3; trivial.
(* k3 = nil, t2 is decomposed *)
subst; right; right; exists (Term f (t1 :: t22 :: nil)); exists t21; intuition.
apply well_formed_fold; rewrite Af; split; trivial;
intros u [u_eq_t1 | [u_eq_t2 | In_u_nil]]; subst; trivial; contradiction.
apply trans_clos_is_trans with (Term f (t1 :: (Term f (t21 :: t22 :: nil) :: nil))).
refine (context_in _ t2 (Term f (t21 :: t22 :: nil)) _ f (t1 :: nil) nil); trivial.
apply trans_clos_is_trans with (Term f (t1 :: Term f (t22 :: t21 :: nil) :: nil)).
refine (context_in _ (Term f (t21 :: t22 :: nil)) (Term f (t22 :: t21 :: nil)) _ f (t1 :: nil) nil).
apply comm; right; assumption.
apply r_assoc; trivial.
rewrite P4; rewrite <- P1; rewrite <- Q22;
rewrite <- flatten_app;
transitivity (flatten f ((canonical_form t1 :: nil) ++ canonical_form t22 :: nil)).
simpl; generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); [intros _ | intro f_diff_f; apply False_rect; apply f_diff_f; reflexivity].
rewrite Af; rewrite app_nil_r;
apply quick_permut_bis; apply permut_refl.
apply list_permut_flatten; apply list_permut_app_app.
rewrite P3; rewrite app_nil_r; trivial.
(* k1 = nil, k4 = nil *)
right; right; exists t2; exists t1; subst; intuition.
apply comm; right; trivial.
rewrite P4; rewrite P2; rewrite app_nil_r; apply permut_refl.
rewrite P1; rewrite P3; rewrite app_nil_r; apply permut_refl.
(* k2 = nil, k4 = nil *)
subst; left; apply list_permut.permut_nil with term (@eq term); trivial.
(* k4 = nil; t2 is decomposed *)
subst; right; right; exists t22; exists (Term f (t1 :: t21 :: nil)); intuition.
apply well_formed_fold; rewrite Af; split; trivial;
intros u [u_eq_t1 | [u_eq_t21 | In_u_nil]]; subst; trivial; contradiction.
unfold ac, th_eq; apply trans_clos_is_trans with (Term f (t1 :: (Term f (t21 :: t22 :: nil) :: nil))).
refine (context_in _ t2 (Term f (t21 :: t22 :: nil)) _ f (t1 :: nil) nil); trivial.
apply trans_clos_is_trans with (Term f (Term f (t1 :: t21 :: nil) :: t22 :: nil)).
apply r_assoc; trivial.
apply comm; right; trivial.
rewrite P4; rewrite <- Q22; rewrite app_nil_r; auto.
transitivity (flatten f ((canonical_form t1 :: nil) ++ canonical_form t21 :: nil)).
simpl; generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); [intros _ | intro f_diff_f; apply False_rect; apply f_diff_f; reflexivity].
rewrite Af; rewrite app_nil_r;
apply quick_permut_bis; apply permut_refl.
rewrite P3;
rewrite app_nil_r in P1; rewrite <- P1;
rewrite <- Q21;
rewrite flatten_app; apply list_permut_app_app.
(* t1 is decomposed, k1 = nil  *)
subst; right; right; exists (Term f (t12 :: t2 :: nil)); exists t11; intuition.
apply well_formed_fold; rewrite Af; split; trivial;
intros u [u_eq_t12 | [u_eq_t2 | In_u_nil]]; subst; trivial; contradiction.
unfold ac, th_eq; apply trans_clos_is_trans with (Term f (Term f (t11 :: t12 :: nil) :: t2 :: nil)).
refine (context_in _ t1 (Term f (t11 :: t12 :: nil)) _ f nil (t2 :: nil)); trivial.
apply trans_clos_is_trans with (Term f (t11 :: (Term f (t12 :: t2 :: nil)) :: nil)).
apply l_assoc; trivial.
apply comm; right; trivial.
rewrite P4; rewrite <- P2; rewrite <- Q12; 
transitivity (flatten f ((canonical_form t12 :: nil) ++ canonical_form t2 :: nil)).
simpl; generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); [intros _ | intro f_diff_f; apply False_rect; apply f_diff_f; reflexivity].
rewrite Af; rewrite app_nil_r;
apply quick_permut_bis; apply permut_refl.
rewrite flatten_app; apply list_permut_app_app.
rewrite P3; trivial.
(* t1 is decomposed, k2 = nil  *)
subst; right; right; exists t12; exists (Term f (t11 :: t2 :: nil)); intuition.
apply well_formed_fold; rewrite Af; split; trivial;
intros u [u_eq_t11 | [u_eq_t2 | In_u_nil]]; subst; trivial; contradiction.
unfold ac, th_eq; apply trans_clos_is_trans with (Term f (Term f (t11 :: t12 :: nil) :: t2 :: nil)).
refine (context_in _ t1 (Term f (t11 :: t12 :: nil)) _ f nil (t2 :: nil)); trivial.
apply trans_clos_is_trans with (Term f (Term f (t12 :: t11 :: nil) :: t2 :: nil)).
refine (context_in _ (Term f (t11 :: t12 :: nil)) (Term f (t12 :: t11 :: nil)) _ f nil (t2 :: nil)); trivial.
apply comm; right; trivial.
apply l_assoc; trivial.
rewrite P4; auto.
rewrite P3;
rewrite app_nil_r in P2; rewrite <- P2;
rewrite <- Q11;
transitivity (flatten f ((canonical_form t11 :: nil) ++ canonical_form t2 :: nil)).
simpl; generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); [intros _ | intro f_diff_f; apply False_rect; apply f_diff_f; reflexivity].
rewrite Af; rewrite app_nil_r;
apply quick_permut_bis; apply permut_refl.
rewrite flatten_app; apply list_permut_app_app.
(* t1 and t2 are decomposed *)
right; right; exists (Term f (t12 :: t22 :: nil)); exists (Term f (t11 :: t21 :: nil));
intuition.
apply well_formed_fold; rewrite Af; split; trivial;
intros u [u_eq_t12 | [u_eq_t22 | In_u_nil]]; subst; trivial; contradiction.
apply well_formed_fold; rewrite Af; split; trivial;
intros u [u_eq_t11 | [u_eq_t21 | In_u_nil]]; subst; trivial; contradiction.
apply trans_clos_is_trans with (Term f (Term f (t11 :: t12 :: nil) :: t2 :: nil)).
refine (context_in _ _ _  _ f nil (t2 :: nil)); trivial.
apply trans_clos_is_trans with (Term f (Term f (t11 :: t12 :: nil) :: (Term f (t21 :: t22 :: nil)) :: nil)).
refine (context_in _ _  _ _  f (_ :: nil) nil); trivial.
apply trans_clos_is_trans with (Term f (t11 :: (Term f (t12 :: (Term f (t21 :: t22 :: nil)) :: nil)) :: nil)).
apply l_assoc; trivial.
apply trans_clos_is_trans with (Term f (t11 :: (Term f (Term f (t12 ::  t21 :: nil) :: t22 :: nil)) :: nil)).
refine (context_in _ _ _ _ f (t11 :: nil) nil).
apply r_assoc; trivial.
apply trans_clos_is_trans with (Term f (t11 :: (Term f (Term f (t21 ::  t12 :: nil) :: t22 :: nil)) :: nil)).
refine (context_in _ _ _ _ f (t11 :: nil) nil).
refine (context_in _ _ _ _ f nil (t22 :: nil)).
apply comm; right; trivial.
apply trans_clos_is_trans with (Term f (t11 :: (Term f (t21 :: (Term f (t12 :: t22 :: nil)) :: nil)) :: nil)).
refine (context_in _ _ _ _ f (t11 :: nil) nil).
apply l_assoc; trivial.
apply trans_clos_is_trans with (Term f (Term f (t11:: t21 :: nil) :: Term f (t12 :: t22 :: nil) :: nil)).
apply r_assoc; trivial.
apply comm; right; trivial.
rewrite P4; rewrite <- Q12; rewrite <- Q22.
transitivity (flatten f (canonical_form t12 :: nil) ++ flatten f (canonical_form t22 :: nil)).
rewrite <- flatten_app;
simpl; generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); [intros _ | intro f_diff_f; apply False_rect; apply f_diff_f; reflexivity].
rewrite Af; rewrite app_nil_r;
apply quick_permut_bis; apply permut_refl.
apply list_permut_app_app.
rewrite P3; rewrite <- Q11; rewrite <- Q21.
transitivity (flatten f (canonical_form t11 :: nil) ++  flatten f (canonical_form t21 :: nil)).
rewrite <- flatten_app;
simpl; generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); [intros _ | intro f_diff_f; apply False_rect; apply f_diff_f; reflexivity].
rewrite Af; rewrite app_nil_r;
apply quick_permut_bis; apply permut_refl.
apply list_permut_app_app.
(* f <> g *)
assert ( Ll := list_permut.permut_length P'); clear P';
destruct l1 as [ | t1 l1]; [left; trivial | idtac];
destruct l2 as [ | t2 l2]; [right; left; trivial | idtac];
rewrite length_app in Ll; simpl in Ll; rewrite Nat.add_comm in Ll; simpl in Ll;
discriminate.
Qed.

Lemma syntactic_dec :
  forall n, (forall t1, size t1 <= n -> forall t2, well_formed t1 ->
                   well_formed t2 -> 
                   canonical_form t1 = canonical_form t2 -> ac t1 t2) ->
  forall f, arity f = AC -> forall a1 a2 a3 a4,
  size a1 <= n -> well_formed a1 -> 
  size a2 <= n -> well_formed a2 -> 
  well_formed a3 -> well_formed a4 ->
  forall k1 k4, 
  permut  (flatten f (canonical_form a1 :: nil)) k1 ->
  permut  (flatten f (canonical_form a2 :: nil)) k4 ->
  permut  (flatten f (canonical_form a3 :: nil)) k1->
  permut  (flatten f (canonical_form a4 :: nil)) k4 ->
  ac (Term f (a1 :: a2 :: nil)) (Term f (a3 :: a4 :: nil)).
Proof.
intros n IH f Af a1 a2 a3 a4 Sa1 Wa1 Sa2 Wa2 Wa3 Wa4 k1 k4 P1 P2 P3 P4.
apply trans_clos_is_trans with (Term f (a3 :: a2 :: nil)).
refine (context_in _ _ _ _ f nil (a2 :: nil)).
apply IH; trivial; apply flatten_cf_cf with f; trivial; 
rewrite P1; rewrite P3; auto.
refine (context_in _ _ _ _ f (a3 :: nil) nil).
apply IH; trivial; apply flatten_cf_cf with f; trivial; 
rewrite P2; rewrite P4; auto.
Qed.

Lemma commutativity :
 forall n, (forall t1, size t1 <= n -> forall t2, well_formed t1 ->
                   well_formed t2 -> 
                   canonical_form t1 = canonical_form t2 -> ac t1 t2) ->
 forall f, arity f = AC -> forall a1 a2 a3 a4,
  size a1 <= n -> well_formed a1 -> 
  size a2 <= n -> well_formed a2 ->
  well_formed a3 -> well_formed a4 ->
  forall k2 k3,
  permut (flatten f (canonical_form a1 :: nil)) k2 ->
  permut (flatten f (canonical_form a2 :: nil)) k3 ->
  permut (flatten f (canonical_form a3 :: nil)) k3 ->
  permut (flatten f (canonical_form a4 :: nil)) k2 ->
 ac (Term f (a1 :: a2 :: nil)) (Term f (a3 :: a4 :: nil)).
Proof.
intros n IH f Af a1 a2 a3 a4 Sa1 Wa1 Sa2 Wa2 Wa3 Wa4 k2 k3 P1 P2 P3 P4.
apply trans_clos_is_trans with (Term f  (a2 :: a1 :: nil)).
apply comm; right; trivial.
apply trans_clos_is_trans with (Term f (a3 :: a1 :: nil)).
refine (context_in _ _ _ _ f nil (a1 :: nil)).
apply IH; trivial; apply flatten_cf_cf with f; trivial; 
rewrite P2; rewrite P3; auto.
refine (context_in _ _ _ _ f (a3 :: nil) nil).
apply IH; trivial; apply flatten_cf_cf with f; trivial; 
rewrite P1; rewrite P4; auto.
Qed.

Lemma associativity :
 forall n, (forall t1, size t1 <= n -> forall t2, well_formed t1 ->
                   well_formed t2 -> 
                   canonical_form t1 = canonical_form t2 -> ac t1 t2) ->
 forall f, arity f = AC -> forall  a1 a2 a3 a4,
  size a1 <= n -> well_formed a1 -> 
  size a2 <= n -> well_formed a2 ->
  size a3 <= n -> well_formed a3 -> 
  size a4 <= n -> well_formed a4 ->
  forall k1 k2 k4, k1 = nil \/ k2 = nil \/ k4 = nil \/
  (permut (flatten f (canonical_form a1 :: nil)) (k1 ++ k2) ->
   permut (flatten f (canonical_form a2 :: nil)) k4 ->
   permut  (flatten f (canonical_form a3 :: nil)) k1 ->
   permut (flatten f (canonical_form a4 :: nil)) (k2 ++ k4) ->
 ac (Term f (a1 :: a2 :: nil)) (Term f (a3 :: a4 :: nil))).
Proof.
intros n IH f Af a1 a2 a3 a4 Sa1 Wa1 Sa2 Wa2 Sa3 Wa3 Sa4 Wa4 k1 k2 k4.
destruct k1 as [ | h1 k1]; [left; trivial | right];
destruct k2 as [ | h2 k2]; [left; trivial | right];
destruct k4 as [ | h4 k4]; [left; trivial | right]; intros P1 P2 P3 P4;
generalize (split_cf Af _ _ Wa1 P1);
intros [Hk1 | [Hk2 | [t1 [t2 [Wt1 [Wt2 [H1 [Q1 Q2]]]]]]]];
generalize (split_cf Af _ _ Wa4 P4);
intros [Hk2' | [Hk4 | [t2' [t4 [Wt2' [Wt4 [H2 [Q2' Q4]]]]]]]]; 
subst; try discriminate.
apply trans_clos_is_trans with (Term f ((Term f (t1 :: t2 :: nil)) :: a2 :: nil)). 
refine (context_in _ _ _ _ f nil (a2 :: nil)); trivial.
apply trans_clos_is_trans with (Term f ((Term f (t1 :: t2 :: nil)) :: t4 :: nil)).
refine (context_in _ _ _ _ f (_ :: nil) nil).
apply IH; trivial.
apply flatten_cf_cf with f; trivial.
rewrite P2; rewrite Q4; apply permut_refl.
apply trans_clos_is_trans with (Term f (t1 :: (Term f (t2 :: t4 :: nil)) :: nil)).
apply l_assoc; trivial.
assert (Wt24 : well_formed (Term f (t2 :: t4 :: nil))).
apply well_formed_fold; rewrite Af; split; trivial;
intros u [u_eq_t2 | [u_eq_t4 | In_u_nil]]; subst; trivial; contradiction.
apply trans_clos_is_trans with (Term f (a3 :: (Term f (t2 :: t4 :: nil)) :: nil)).
refine (context_in _ _ _ _ f nil (_ :: nil)).
apply th_sym; apply IH; trivial.
apply flatten_cf_cf with f; trivial.
rewrite P3; rewrite Q1; auto.
refine (context_in _ _ _ _ f (_ :: nil) nil).
apply th_sym; apply IH; trivial; apply flatten_cf_cf with f; trivial.
rewrite P4; rewrite <- Q2; rewrite <- Q4.
rewrite <- flatten_app; simpl;
simpl; generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); [intros _ | intro f_diff_f; apply False_rect; apply f_diff_f; reflexivity].
rewrite Af; rewrite app_nil_r; apply quick_permut.
Qed.

Lemma swap_left :
 forall n, (forall t1, size t1 <= n -> forall t2, well_formed t1 ->
                   well_formed t2 -> 
                   canonical_form t1 = canonical_form t2 -> ac t1 t2) ->
 forall f, arity f = AC -> forall  a1 a2 a3 a4,
  size a1 <= n -> well_formed a1 -> 
  size a2 <= n -> well_formed a2 ->
  size a3 <= n -> well_formed a3 -> 
  size a4 <= n -> well_formed a4 ->
  forall k2 k3 k4, k2 = nil \/ k3 = nil \/ k4 = nil \/
  (permut (flatten f (canonical_form a1 :: nil)) k2 ->
  permut (flatten f (canonical_form a2 :: nil)) (k3 ++ k4) ->
  permut (flatten f (canonical_form a3 :: nil)) k3 ->
  permut (flatten f (canonical_form a4 :: nil)) (k2 ++ k4) ->
  ac (Term f (a1 :: a2 :: nil)) (Term f (a3 :: a4 :: nil))).
Proof.
intros n IH f Af a1 a2 a3 a4 Sa1 Wa1 Sa2 Wa2 Sa3 Wa3 Sa4 Wa4 k2 k3 k4.
destruct k2 as [ | h2 k2]; [left; trivial | right];
destruct k3 as [ | h3 k3]; [left; trivial | right];
destruct k4 as [ | h4 k4]; [left; trivial | right]; intros P1 P2 P3 P4;
generalize (split_cf Af _ _ Wa2 P2);
intros [Hk1 | [Hk2 | [t3 [t4 [Wt3 [Wt4 [H2 [Q3 Q4]]]]]]]];
generalize (split_cf Af _ _ Wa4 P4);
intros [Hk2' | [Hk4 | [t2' [t4' [Wt2' [Wt4' [H4 [Q2' Q4']]]]]]]]; 
subst; try discriminate.
apply trans_clos_is_trans with (Term f (t2' :: a2 :: nil)).
refine (context_in _ _ _ _ f nil (_ :: nil)).
apply IH; trivial; apply flatten_cf_cf with f; trivial;
rewrite P1; rewrite Q2'; auto.
apply trans_clos_is_trans with (Term f (t2' :: (Term f (t3 :: t4 :: nil)) :: nil)).
refine (context_in _ _ _ _ f (_ :: nil) nil); trivial.
apply trans_clos_is_trans with (Term f ((Term f (t2' :: t3 :: nil)) :: t4 :: nil)).
apply r_assoc; trivial.
apply trans_clos_is_trans with (Term f ((Term f (t3 :: t2' :: nil)) :: t4 :: nil)).
refine (context_in _ _ _ _ f nil (_ :: nil)).
apply comm; trivial; right; trivial.
apply trans_clos_is_trans with (Term f (t3 :: (Term f (t2' :: t4 :: nil)) :: nil)). 
apply l_assoc; trivial.
assert (Wt24 : well_formed (Term f (t2' :: t4 :: nil))).
apply well_formed_fold; rewrite Af; split; trivial;
intros u [u_eq_t2' | [u_eq_t4 | In_u_nil]]; subst; trivial; contradiction.
apply th_sym; apply trans_clos_is_trans with (Term f (t3 :: a4 :: nil)).
refine (context_in _ _ _ _ f nil (_ :: nil)).
apply IH; trivial; apply flatten_cf_cf with f; trivial.
rewrite P3; rewrite Q3; auto.
refine (context_in _ _ _ _ f (_ :: nil) nil); trivial.
apply IH; trivial; apply flatten_cf_cf with f; trivial.
rewrite P4; rewrite <- Q2'; rewrite <- Q4;
rewrite <- flatten_app; simpl;
simpl; generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); [intros _ | intro f_diff_f; apply False_rect; apply f_diff_f; reflexivity].
rewrite Af; rewrite app_nil_r; apply quick_permut.
Qed.

Lemma swap_right :
 forall n, (forall t1, size t1 <= n -> forall t2, well_formed t1 ->
                   well_formed t2 -> 
                   canonical_form t1 = canonical_form t2 -> ac t1 t2) ->
 forall f, arity f = AC -> forall  a1 a2 a3 a4,
  size a1 <= n -> well_formed a1 -> 
  size a2 <= n -> well_formed a2 ->
  size a3 <= n -> well_formed a3 -> 
  size a4 <= n -> well_formed a4 ->
  forall k1 k2 k3, k1 = nil \/ k2 = nil \/ k3 = nil \/
  (permut (flatten f (canonical_form a1 :: nil)) (k1 ++ k2) ->
  permut (flatten f (canonical_form a2 :: nil)) k3 ->
  permut (flatten f (canonical_form a3 :: nil)) (k1 ++ k3) ->
  permut (flatten f (canonical_form a4 :: nil)) k2 ->
  ac (Term f (a1 :: a2 :: nil)) (Term f (a3 :: a4 :: nil))).
Proof.
intros n IH f Af a1 a2 a3 a4 Sa1 Wa1 Sa2 Wa2 Sa3 Wa3 Sa4 Wa4 k1 k2 k3.
destruct k1 as [ | h1 k1]; [left; trivial | right]; 
destruct k2 as [ | h2 k2]; [left; trivial | right];
destruct k3 as [ | h3 k3]; [left; trivial | right]; intros P1 P2 P3 P4;
generalize (split_cf Af _ _ Wa1 P1);
intros [Hk1 | [Hk2 | [t1 [t2 [Wt1 [Wt2 [H1 [Q1 Q2]]]]]]]];
generalize (split_cf Af _ _ Wa3 P3);
intros [Hk1' | [Hk3 | [t1' [t3 [Wt1' [Wt3 [H3 [Q1' Q3]]]]]]]]; 
subst; try discriminate.
apply trans_clos_is_trans with (Term f ((Term f (t1 :: t2 :: nil)) :: a2 :: nil)).
refine (context_in _ _ _ _ f nil (_ :: nil)); trivial.
apply trans_clos_is_trans with (Term f ((Term f (t1 :: t2 :: nil)) :: t3 :: nil)).
refine (context_in _ _ _ _ f (_ :: nil) nil).
apply IH; trivial; apply flatten_cf_cf with f; trivial;
rewrite P2; rewrite Q3; auto.
apply trans_clos_is_trans with (Term f (t1 :: (Term f (t2 :: t3 :: nil)) :: nil)).
apply l_assoc; trivial.
apply trans_clos_is_trans with (Term f (t1 :: (Term f (t3 :: t2 :: nil)) :: nil)).
refine (context_in _ _ _ _ f (_ :: nil) nil).
apply comm; right; trivial.
apply trans_clos_is_trans with (Term f ((Term f (t1 :: t3 :: nil)) :: t2 :: nil)). 
apply r_assoc; trivial.
assert (Wt13 : well_formed (Term f (t1 :: t3 :: nil))).
apply well_formed_fold; rewrite Af; split; trivial;
intros u [u_eq_t1 | [u_eq_t3 | In_u_nil]]; subst; trivial; contradiction.
apply th_sym.
apply trans_clos_is_trans with (Term f (Term f (t1 :: t3 :: nil) :: a4 :: nil)).
refine (context_in _ _ _ _ f nil (_ :: nil)).
apply IH; trivial; apply flatten_cf_cf with f; trivial.
rewrite P3; rewrite <- Q1; rewrite <- Q3.
rewrite <- flatten_app; simpl;
simpl; generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); [intros _ | intro f_diff_f; apply False_rect; apply f_diff_f; reflexivity].
rewrite Af; rewrite app_nil_r; apply quick_permut.
refine (context_in _ _ _ _ f (_ :: nil) nil).
apply IH; trivial; apply flatten_cf_cf with f; trivial.
rewrite P4; rewrite Q2; auto.
Qed.

Lemma middle_commutativity :
 forall n, (forall t1, size t1 <= n -> forall t2, well_formed t1 ->
                   well_formed t2 -> 
                   canonical_form t1 = canonical_form t2 -> ac t1 t2) ->
 forall f, arity f = AC -> forall  a1 a2 a3 a4,
  size a1 <= n -> well_formed a1 -> 
  size a2 <= n -> well_formed a2 ->
  size a3 <= n -> well_formed a3 -> 
  size a4 <= n -> well_formed a4 ->
  forall k1 k2 k3 k4, k1 = nil \/ k2 = nil \/ k3 = nil \/ k4 = nil \/
  (permut (flatten f (canonical_form a1 :: nil)) (k1 ++ k2) ->
   permut (flatten f (canonical_form a2 :: nil)) (k3 ++ k4) ->
   permut (flatten f (canonical_form a3 :: nil)) (k1 ++ k3) ->
   permut (flatten f (canonical_form a4 :: nil)) (k2 ++ k4) ->
   ac (Term f (a1 :: a2 :: nil)) (Term f (a3 :: a4 :: nil))).
Proof.
intros n IH f Af a1 a2 a3 a4 Sa1 Wa1 Sa2 Wa2 Sa3 Wa3 Sa4 Wa4 k1 k2 k3 k4.
destruct k1 as [ | h1 k1]; [left; trivial | right]; 
destruct k2 as [ | h2 k2]; [left; trivial | right];
destruct k3 as [ | h3 k3]; [left; trivial | right]; 
destruct k4 as [ | h4 k4]; [left; trivial | right]; intros P1 P2 P3 P4;
generalize (split_cf Af _ _ Wa1 P1);
intros [Hk1 | [Hk2 | [t1 [t2 [Wt1 [Wt2 [H1 [Q1 Q2]]]]]]]];
generalize (split_cf Af _ _ Wa2 P2);
intros [Hk3 | [Hk4 | [t3 [t4 [Wt3 [Wt4 [H2 [Q3 Q4]]]]]]]];
generalize (split_cf Af _ _ Wa3 P3);
intros [Hk1' | [Hk3' | [t1' [t3' [Wt1' [Wt3' [H3 [Q1' Q3']]]]]]]];
generalize (split_cf Af _ _ Wa4 P4);
intros [Hk2' | [Hk4' | [t2' [t4' [Wt2' [Wt4' [H4 [Q2' Q4']]]]]]]]; 
subst; try discriminate.
apply trans_clos_is_trans with (Term f ((Term f (t1 :: t2 :: nil)) :: a2 :: nil)). 
refine (context_in _ _ _ _ f nil (_ :: nil)); trivial.
apply trans_clos_is_trans with (Term f ((Term f (t1 :: t2 :: nil)) :: (Term f (t3 :: t4 :: nil)) :: nil)). 
refine (context_in _ _ _ _ f (_ :: nil) nil); trivial.
apply trans_clos_is_trans with (Term f (t1 :: (Term f  (t2 :: (Term f (t3 :: t4 :: nil)) :: nil)) :: nil)). 
apply l_assoc; trivial.
apply trans_clos_is_trans with (Term f (t1 :: (Term f  ((Term f (t2 :: t3 :: nil)) :: t4 :: nil)) :: nil)).
refine (context_in _ _ _ _ f (_ :: nil) nil); apply r_assoc; trivial.
apply trans_clos_is_trans with (Term f (t1 :: (Term f  ((Term f (t3 :: t2 :: nil)) :: t4 :: nil)) :: nil)).
refine (context_in _ _ _ _ f (_ :: nil) nil).
refine (context_in _ _ _ _ f nil (_ :: nil)); apply comm; right; trivial.
apply trans_clos_is_trans with (Term f (t1 :: (Term f  (t3 :: (Term f (t2 :: t4 :: nil)) :: nil)) :: nil)). 
refine (context_in _ _ _ _ f (_ :: nil) nil); apply l_assoc; trivial.
apply trans_clos_is_trans with (Term f ((Term f (t1 :: t3 :: nil)) :: (Term f (t2 :: t4 :: nil)) :: nil)). 
apply r_assoc; trivial.
apply th_sym; apply trans_clos_is_trans with (Term f ((Term f (t1 :: t3 :: nil)) :: a4 :: nil)). 
refine (context_in _ _ _ _ f nil (_ :: nil)).
assert (Wt13 : well_formed (Term f (t1 :: t3 :: nil))).
apply well_formed_fold; rewrite Af; split; trivial;
intros u [u_eq_t1 | [u_eq_t3 | In_u_nil]]; subst; trivial; contradiction.
apply IH; trivial; apply flatten_cf_cf with f; trivial;
rewrite P3; rewrite <- Q1; rewrite <- Q3.
rewrite <- flatten_app; simpl;
simpl; generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); [intros _ | intro f_diff_f; apply False_rect; apply f_diff_f; reflexivity].
rewrite Af; rewrite app_nil_r; apply quick_permut.
refine (context_in _ _ _ _ f (_ :: nil) nil).
assert (Wt24 : well_formed (Term f (t2 :: t4 :: nil))).
apply well_formed_fold; rewrite Af; split; trivial;
intros u [u_eq_t2 | [u_eq_t4 | In_u_nil]]; subst; trivial; contradiction.
apply IH; trivial; apply flatten_cf_cf with f; trivial;
rewrite P4; rewrite <- Q2; rewrite <- Q4.
rewrite <- flatten_app; simpl;
generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); [intros _ | intro f_diff_f; apply False_rect; apply f_diff_f; reflexivity].
rewrite Af; rewrite app_nil_r; apply quick_permut.
Qed.

Global Instance length_morph : Proper (permut ==> eq) (length (A:=term)).

Proof. intros a b ab. eapply list_permut.permut_length. apply ab. Qed.

Theorem cf_eq_ac :
  forall t1 t2, well_formed t1 -> well_formed t2 -> 
  canonical_form t1 = canonical_form t2 -> ac t1 t2.
Proof.
intro t1; pattern t1; apply term_rec2; clear t1; induction n as [ | n].
intros t1 St1; absurd (1 <= 0); auto with arith; 
apply Nat.le_trans with (size t1); trivial; apply size_ge_one.
intros [v1 | f1 l1] St1 [v2 | f l2] Wt1 Wt2 H;
[simpl in H; rewrite H; unfold ac; apply th_refl | discriminate | discriminate | idtac].
assert (St2 : size (Term f l2) <= S n). 
rewrite size_size; trivial; rewrite <- H; rewrite <- size_size; trivial.
simpl in H; injection H; clear H;
intros H f1_eq_f; subst f1; destruct_arity f m Af.
(* arity f = AC *)
generalize (well_formed_unfold Wt1); rewrite Af; intros [Wl1 Ll1];
generalize (well_formed_unfold Wt2); rewrite Af; intros [Wl2 Ll2];
destruct l1 as [ | a1 l1]; [absurd (0=2); auto with arith | idtac];
destruct l1 as [ | a2 l1]; [absurd (1=2); auto with arith | idtac];
destruct l1 as [ | a3 l1]; [clear Ll1 | absurd (S(S(S(length l1)))=2); auto with arith];
destruct l2 as [ | a3 l2]; [absurd (0=2); auto with arith | idtac];
destruct l2 as [ | a4 l2]; [absurd (1=2); auto with arith | idtac];
destruct l2 as [ | a5 l2]; [clear Ll2 | absurd (S(S(S(length l2)))=2); auto with arith];
assert (Wa1 := Wl1 a1 (or_introl _ (eq_refl _)));
assert (Wa2 := Wl1 a2 (or_intror _ (or_introl _ (eq_refl _))));
assert (Wa3 := Wl2 a3 (or_introl _ (eq_refl _)));
assert (Wa4 := Wl2 a4 (or_intror _ (or_introl _ (eq_refl _))));
simpl in St1; rewrite Nat.add_0_r in St1;
simpl in St2; rewrite Nat.add_0_r in St2.
assert (Sa1 : size a1 <= n).
apply Nat.le_trans with (size a1 + size a2); auto with arith.
assert (Sa2 : size a2 <= n).
apply Nat.le_trans with (size a1 + size a2); auto with arith.
assert (Sa3 : size a3 <= n).
apply Nat.le_trans with (size a3 + size a4); auto with arith.
assert (Sa4 : size a4 <= n).
apply Nat.le_trans with (size a3 + size a4); auto with arith.
elim (ac_syntactic 
(flatten f (canonical_form a1 :: nil))
(flatten f (canonical_form a2 :: nil))
(flatten f (canonical_form a3 :: nil))
(flatten f (canonical_form a4 :: nil))).
intros k1 [k2 [k3 [k4 [P1 [P2 [P3 P4]]]]]].
destruct k1 as [ | h1 k1]; destruct k4 as [ | h4 k4].
(* commutativity *)
apply commutativity with n k2 k3; trivial;
[rewrite app_nil_r in P2 | rewrite app_nil_r in P4]; trivial.
(* swap_left *)
generalize (swap_left IHn Af Sa1 Wa1 Sa2 Wa2 Sa3 Wa3 Sa4 Wa4 
k2 k3 (h4 :: k4)); 
intros [Hk2 | [Hk3 | [Hk4 | H']]]; subst.
(* absurd a1=0 *)
generalize (size_size_aux3 Af Wa1); rewrite P1; intro;
absurd (1 <= 0); auto with arith.
(* absurd a3=0 *)
generalize (size_size_aux3 Af Wa3); rewrite P3; intro;
absurd (1 <= 0); auto with arith.
discriminate.
apply H'; trivial.
(* swap_right *)
generalize (swap_right IHn Af Sa1 Wa1 Sa2 Wa2 Sa3 Wa3 Sa4 Wa4 
(h1 :: k1) k2 k3);
intros [Hk1 | [Hk2 | [Hk3 | H']]]; subst.
discriminate.
(* absurd a4=0 *)
generalize (size_size_aux3 Af Wa4); rewrite P4; intro;
absurd (1 <= 0); auto with arith.
(* absurd a2=0 *)
generalize (size_size_aux3 Af Wa2); rewrite P2; intro;
absurd (1 <= 0); auto with arith.
rewrite app_nil_r in P2; rewrite app_nil_r in P4;
apply H'; trivial.
destruct k2 as [ | h2 k2]; destruct k3 as [ | h3 k3].
(* syntactic decomposition *)
apply (syntactic_dec IHn Af Sa1 Wa1 Sa2 Wa2 Wa3 Wa4 P1 P2 P3 P4).
(* reverted associativity *)
generalize (associativity IHn Af Sa3 Wa3 Sa4 Wa4 Sa1 Wa1 Sa2 Wa2 
(h1::k1) (h3 :: k3) (h4::k4));
intros [Hk1 | [Hk3 | [Hk4 | H']]]; subst.
discriminate.
discriminate.
discriminate.
rewrite app_nil_r in P1; unfold ac; apply th_sym; apply H'; trivial.
(* associativity *)
generalize (associativity IHn Af Sa1 Wa1 Sa2 Wa2 Sa3 Wa3 Sa4 Wa4 (h1::k1) (h2 :: k2) (h4::k4)).
intros [Hk1 | [Hk2 | [Hk4 | H']]]; subst.
discriminate.
discriminate.
discriminate.
rewrite app_nil_r in P3; unfold ac; apply H'; trivial.
(* middle commutativity *)
generalize (middle_commutativity IHn Af Sa1 Wa1 Sa2 Wa2 Sa3 Wa3 Sa4 Wa4
(h1 :: k1) (h2 :: k2) (h3 :: k3) (h4 :: k4));
intros [Hk1 | [Hk2 | [Hk3 | [Hk4 | H']]]].
discriminate.
discriminate.
discriminate.
discriminate.
apply H'; trivial.
simpl map in H; refine (permut_trans (list_permut_app_app _ _) _);
refine (permut_trans _ (list_permut_app_app _ _));
do 2 rewrite <- flatten_app; 
refine (permut_trans (quick_permut _) _).
simpl app; rewrite H; apply quick_permut_bis; apply permut_refl.
(* arity f = C *)
generalize (well_formed_unfold Wt1); rewrite Af; intros [Wl1 Ll1];
generalize (well_formed_unfold Wt2); rewrite Af; intros [Wl2 Ll2];
destruct l1 as [ | a1 l1]; [absurd (0=2); auto with arith | idtac];
destruct l1 as [ | a2 l1]; [absurd (1=2); auto with arith | idtac];
destruct l1 as [ | a3 l1]; [clear Ll1 | absurd (S(S(S(length l1)))=2); auto with arith];
destruct l2 as [ | a3 l2]; [absurd (0=2); auto with arith | idtac];
destruct l2 as [ | a4 l2]; [absurd (1=2); auto with arith | idtac];
destruct l2 as [ | a5 l2]; [clear Ll2 | absurd (S(S(S(length l2)))=2); auto with arith];
assert (Wa1 := Wl1 a1 (or_introl _ (eq_refl _)));
assert (Wa2 := Wl1 a2 (or_intror _ (or_introl _ (eq_refl _))));
assert (Wa3 := Wl2 a3 (or_introl _ (eq_refl _)));
assert (Wa4 := Wl2 a4 (or_intror _ (or_introl _ (eq_refl _))));
simpl in St1; rewrite Nat.add_0_r in St1;
simpl in St2; rewrite Nat.add_0_r in St2.
assert (Sa1 : size a1 <= n).
apply Nat.le_trans with (size a1 + size a2); auto with arith.
assert (Sa2 : size a2 <= n).
apply Nat.le_trans with (size a1 + size a2); auto with arith.
assert (Sa3 : size a3 <= n).
apply Nat.le_trans with (size a3 + size a4); auto with arith.
assert (Sa4 : size a4 <= n).
apply Nat.le_trans with (size a3 + size a4); auto with arith.
elim (@list_permut.permut_length_2 _ term (@eq term) (canonical_form a1) (canonical_form a2)
(canonical_form a3) (canonical_form a4)).
intros [D1 D2]; apply trans_clos_is_trans with (Term f (a3 :: a2 :: nil)).
refine (context_in _ _ _ _ f nil (_ :: nil)).
apply IHn; trivial.
refine (context_in _ _ _ _ f (_ :: nil) nil).
apply IHn; trivial.
intros [C1 C2]; apply trans_clos_is_trans with (Term f (a2 :: a1 :: nil)).
apply comm; left; trivial.
apply trans_clos_is_trans with (Term f (a3 :: a1 :: nil)).
refine (context_in _ _ _ _ f nil (_ :: nil)).
apply IHn; trivial; apply sym_eq; trivial.
refine (context_in _ _ _ _ f (_ :: nil) nil).
apply IHn; trivial.
apply permut_trans with (quicksort (map canonical_form (a1 :: a2 :: nil)));
[ apply quick_permut |  rewrite H; apply quick_permut_bis; auto ].
(* arity f = Free m *)
unfold ac, th_eq; 
generalize (list_eq_bool_ok _ T.eq_bool_ok l1 l2); case (list_eq_bool T.eq_bool l1 l2); [intro l1_eq_l2 | intro l1_diff_l2].
subst; apply th_refl.
apply general_context;
generalize (well_formed_unfold Wt1); intros [Wl1 _];
generalize (well_formed_unfold Wt2); intros [Wl2 _].
assert (Sl1 : forall t1, In t1 l1 -> size t1 <= n).
intros t1 In_t1; apply le_S_n; apply Nat.lt_le_trans with (size (Term f l1)); trivial; 
apply size_direct_subterm; trivial.
generalize l2 H Wl2 l1_diff_l2; clear St1 Wt1 l2 Wt2 St2 H Wl2 l1_diff_l2;
induction l1 as [ | t1 l1]; intros l2 H Wl2; destruct l2 as [ | t2 l2]; simpl; trivial.
intro H'; apply False_rect; apply H'; trivial.
discriminate.
discriminate.
assert (H'' : ac t1 t2).
apply IHn.
apply Sl1; left; trivial.
apply Wl1; left; trivial.
apply Wl2; left; trivial.
inversion H; trivial.
intro H'; generalize (list_eq_bool_ok _ T.eq_bool_ok l1 l2); case (list_eq_bool T.eq_bool l1 l2); [intro l1_eq_l2 | intro l1_diff_l2].
subst l2; 
revert H''; clear; intro H; induction H as [t1 t2 H | t1 t2 t3 H1 H2].
do 2 left; assumption.
right with (t2 :: l1); trivial.
left; assumption.
apply trans_clos_is_trans with (t2 :: l1).
revert H''; clear; intro H; induction H as [t1 t2 H | t1 t2 t3 H1 H2].
do 2 left; assumption.
right with (t2 :: l1); trivial.
left; assumption.
clear H''; assert (H'' : trans_clos (one_step_list (one_step (sym_refl ac_one_step_at_top))) l1 l2).
apply IHl1; trivial.
intros; apply Wl1; right; trivial.
intros; apply Sl1; right; trivial.
inversion H; trivial.
intros; apply Wl2; right; trivial.
revert H''; clear; intro H; induction H as [l1 l2 H | l1 l2 l3 H1 H2].
left; right; assumption.
right with (t2 :: l2); trivial.
right; assumption.
Qed.

End Make.





