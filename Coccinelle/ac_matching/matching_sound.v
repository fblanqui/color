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


From Stdlib Require Import Arith List.
From CoLoR Require Import more_list list_sort term_spec ac cf_eq_ac matching
     matching_well_founded matching_well_formed.

Module Type S.

Declare Module WFMMatching : matching_well_formed.S.
Import WFMMatching WFMatching Matching Cf_eq_ac Ac EqTh T.

(* Parameter add_a_subterm
Parameter add_a_subterm_subst *)
Parameter solve_is_sound :
  forall pb sigma, well_formed_pb pb ->
  forall pb', In pb' (solve pb) -> is_sol pb' sigma -> is_sol pb sigma.

End S.

Module Make (WFMMatching1 : matching_well_formed.S) :
 S with Module WFMMatching := WFMMatching1.

Module WFMMatching := WFMMatching1.

Import WFMMatching1 WFMMatching WFMatching Matching Cf_eq_ac Ac EqTh T F X Sort LPermut.

Lemma add_a_subterm :
 forall f l l' t, arity f = AC -> (well_formed_cf (Term f (l ++ t :: l'))) ->
 permut (flatten f (build f (l ++ l') :: t :: nil)) (l ++ t :: l').
Proof.
intros f l l' t Af W.
assert (Al_t : match t with | Var _ => True | Term g ll => f <> g end).
apply (well_formed_cf_alien Af W); apply in_or_app; right; left; trivial.
replace (build f (l ++ l') :: t :: nil) with ((build f (l ++ l') :: nil) ++ (t :: nil)); trivial.
rewrite flatten_app; replace (flatten f (t :: nil)) with (t :: nil).
rewrite <- permut_add_inside.
rewrite app_nil_r; 
apply flatten_build_inside with t; trivial.
reflexivity.
simpl; destruct t as [ v | g ll].
reflexivity.
generalize (F.Symb.eq_bool_ok f g); case (F.Symb.eq_bool f g); [intro f_eq_g; apply False_rect; apply Al_t; assumption | reflexivity].
Qed.

Lemma add_a_subterm_subst :
 forall f l1 l2' l2'' t sigma, arity f = AC ->
  well_formed_cf (Term f (l2' ++ t :: l2'')) ->
   apply_cf_subst sigma (build f l1) = build f (l2' ++ l2'') ->
  permut (flatten f (t :: (map (apply_cf_subst sigma) l1))) (l2' ++ t :: l2'').
Proof.
intros f l1 l2' l2'' t sigma Af Wt2 t1_sigma.
assert (Al_t : match t with | Var _ => True | Term g ll => f <> g end).
apply (well_formed_cf_alien Af Wt2); apply in_or_app; right; left; trivial.
simpl; destruct t as [ v | g ll].
rewrite <- permut_cons_inside.
refine (permut_trans (flatten_apply_cf_subst sigma l1 Af) _);
rewrite t1_sigma; apply flatten_build_inside with (Var v); trivial.
reflexivity.
generalize (F.Symb.eq_bool_ok f g); case (F.Symb.eq_bool f g).
intro f_eq_g; apply False_rect; apply Al_t; assumption.
intros _; rewrite <- permut_cons_inside.
refine (permut_trans (flatten_apply_cf_subst sigma l1 Af) _);
rewrite t1_sigma; apply flatten_build_inside with (Term g ll); trivial.
reflexivity.
Qed.

Lemma solve_is_sound :
  forall pb sigma, well_formed_pb pb ->
  forall pb', In pb' (solve pb) -> is_sol pb' sigma -> is_sol pb sigma.
Proof.
intros pb; assert (R := add_new_var_to_rough_sol pb);
unfold is_sol, solve, well_formed_pb in R; 
unfold is_sol, solve, well_formed_pb; 
intros sigma [W1 [W2 [W3 [W4 [W5 W6]]]]] pb' In_pb';
assert (U_pb : forall pb', pb' = pb -> unsolved_part pb' = unsolved_part pb).
intros; subst; trivial.
destruct (unsolved_part pb) as [ | [[v1 | f1 l1] t2] l]; 
generalize (U_pb pb (eq_refl _)); clear U_pb; intro U_pb.
(* unsolved_part pb = nil *)
contradiction.
(* unsolved_part pb =  (v1,t2) :: _ *)
revert In_pb'; case_eq (find X.eq_bool v1 (solved_part pb)); [intros t1 F | intro F].
(* v1 has already a plain value t1, and t1 is equal or not to t2 *)
generalize (T.eq_bool_ok t1 t2); case (T.eq_bool t1 t2); [intro t1_eq_t2; subst t2 | contradiction].
intros [pb'_eq_ | pb'_in_nil]; [subst pb' | contradiction].
intros [sigma' [[H1 [H2 H3]] H4]]; exists sigma'; unfold is_rough_sol; do 2 (split; trivial).
rewrite U_pb; intros s t [st_eq | In_st]; [idtac | apply H1; trivial];
injection st_eq; intros; subst; generalize (H3 v1); simpl solved_part; rewrite F; trivial.
intuition.

generalize (W3 v1); 
case_eq (find X.eq_bool v1 (partly_solved_part pb)); [intros p1 F' | intro F'].

(* v1 has not a plain value, but it has a partial value p1 *)
(* the partial value p1 is compatible or not with t2 *)
destruct t2 as [ v2 | f2 l2].
contradiction.
generalize (F.Symb.eq_bool_ok (head_symb p1) f2); case (F.Symb.eq_bool (head_symb p1) f2); [intro f1_eq_f2 | contradiction];
rewrite f1_eq_f2; destruct_arity f2 n2 Af2; [ idtac | contradiction | contradiction].
intros _; generalize (in_remove _ _ T.eq_bool_ok (closed_term p1) l2);
destruct (remove T.eq_bool (closed_term p1) l2) as [ l2''' |]; [idtac | contradiction].
intros [cp1 [l2' [l2'' [ H' [l2_eq l2'''_eq]]]]].
injection l2'''_eq; clear l2'''_eq; intro; subst l2'''.
intros [pb'_eq_ | pb'_in_nil]; [subst pb' | contradiction].
intros [sigma' [[H1 [H2 H3]] H4]]; exists sigma'; unfold is_rough_sol; 
split; [split | idtac]; trivial.
rewrite U_pb; intros s t [st_eq | In_st]; [idtac | apply H1; subst; right; trivial];
injection st_eq; intros; subst;
generalize (H2 v1); simpl partly_solved_part; rewrite F'; intro H; rewrite H;
apply (f_equal (fun l => Term (head_symb p1) l)); apply sort_is_unique.
apply quick_sorted.
apply well_formed_cf_sorted with (head_symb p1); trivial;
refine (proj2 _ (A:= well_formed_cf (Var v1))); apply W1; left; trivial.
apply quick_permut_bis;
rewrite (H1 (Var (new_var p1)) (build (head_symb p1) (l2' ++ l2''))); [idtac | left; trivial];
apply add_a_subterm; trivial;
refine (proj2 _ (A:= well_formed_cf (Var v1))); apply W1; left; trivial.
split; trivial.

(* v1 has no value at all, neither plain nor partial *)
intros _ [pb'_eq | pb'_in_nil]; [subst pb' | contradiction].
intros [sigma' [[H1 [H2 H3]] H4]]; exists sigma'; unfold is_rough_sol; 
split; [split; [idtac | split] | idtac].
rewrite U_pb; intros s t [st_eq | In_st]; [idtac | apply H1; trivial].
injection st_eq; intros; subst; generalize (H3 v1); simpl.
generalize (X.eq_bool_ok v1 v1); case (X.eq_bool v1 v1); [intros; assumption | intro v1_diff_v1; apply False_rect; apply v1_diff_v1; reflexivity].
apply H2.
intro v; generalize (H3 v); simpl; 
generalize (X.eq_bool_ok v v1); case (X.eq_bool v v1); [intros v_eq_v1; subst; rewrite F; trivial | intros _; trivial].
apply H4.

(* unsolved_part pb = (Term f1 l1, t2) :: _ *)
(* t2 is compatible or not with (Term f1 l1) *)
destruct t2 as [ v2 | f2 l2 ].
contradiction.
revert In_pb'; generalize (F.Symb.eq_bool_ok f1 f2); case (F.Symb.eq_bool f1 f2); [intro f1_eq_f2 | intros _; contradiction].
subst f2; destruct_arity f1 n1 Af1.
(* arity f1 = AC *)
destruct (le_gt_dec (length l1) (length l2)) as [_ | _]; [idtac | contradiction].
unfold ac_elementary_solve in *.
assert (W_t1 :  well_formed_cf (Term f1 l1)).
refine (proj1 _ (B:= (well_formed_cf (Term f1 l2)))); apply W1; left; trivial.
assert (W_t2 : well_formed_cf (Term f1 l2)).
apply (proj2 (A:= (well_formed_cf (Term f1 l1)))); apply W1; left; trivial. 
destruct l1 as [ | t1 l1].
(* l1 = nil *)
absurd (2 <= @length term nil); auto with arith;
apply well_formed_cf_length with f1; trivial.
(* l1 = t1 :: _ *)
destruct t1 as [v1 | g1 ll1].
(* l1 = t1 :: _  and t1 is a variable v1 *)
generalize (W2 v1); 
case_eq (find X.eq_bool v1 (solved_part pb)); [intros s1 F | intro F].
(* l1 = t1 :: _, t1 is a variable v1  and v1 has a plain value s1 *)
intro W_s1; unfold ac_elementary_solve_term_var_with_val_term in *.
generalize (in_remove _ _ T.eq_bool_ok s1 l2);
destruct (remove T.eq_bool s1 l2) as [ l2''' |].
(* l1 = t1 :: _, t1 is a variable v1, v1 has a plain value s1 and s1 occurs in l2 *)
intros [cp1 [l2' [l2'' [ H' [l2_eq l2'''_eq]]]]].
injection l2'''_eq; clear l2'''_eq; intro; subst l2'''.
intros [pb'_eq_ | pb'_in_nil]; [subst | contradiction].
intros [sigma' [[H1 [H2 H3]] H4]]; exists sigma'; unfold is_rough_sol; 
split; [split; [idtac | split] | idtac]; trivial.
rewrite U_pb; intros s t [st_eq | In_st]; [idtac | subst; apply H1; right; trivial];
injection st_eq; intros; subst. 
replace (apply_cf_subst sigma' (Term f1 (Var v1 :: l1))) with
(Term f1 (quicksort (flatten f1 (cp1 :: map (apply_cf_subst sigma') l1)))).
apply (f_equal (fun l => Term f1 l)).
apply sort_is_unique.
apply quick_sorted.
apply well_formed_cf_sorted with f1; trivial.
apply quick_permut_bis.
apply add_a_subterm_subst; trivial; apply H1; left; trivial.
generalize (H3 v1); simpl; rewrite F; rewrite Af1; intro H3_v1; rewrite H3_v1; trivial.
(* l1 = t1 :: _, t1 is a variable v1, v1 has a plain value s1 and s1 does not occur in l2 *)
intros _; destruct s1 as [| g1 ll1].
contradiction.
generalize (F.Symb.eq_bool_ok f1 g1); case (F.Symb.eq_bool f1 g1);  [intro f1_eq_g1 | contradiction].
assert (S_ll1 : is_sorted ll1).
apply well_formed_cf_sorted with g1; subst; trivial.
assert (S_l2 : is_sorted l2).
apply well_formed_cf_sorted with f1; trivial.
generalize (in_remove_list S_ll1 S_l2); unfold EDS.A, DOS.A in *;
destruct (remove_list ll1 l2) as [l2' | ]; [idtac | contradiction ].
unfold EDS.A, DOS.A in *; destruct (le_gt_dec (length l1) (length l2')) as [L_l1_l2' |]; [idtac | contradiction].
intros P [pb'_eq_ | pb'_in_nil]; [subst | contradiction].
intros [sigma' [[H1 [H2 H3]] H4]]; exists sigma'; unfold is_rough_sol;
split; [split; [idtac | split] | idtac]; trivial.
rewrite U_pb; intros s t [st_eq | In_st]; [idtac | subst; apply H1; right; trivial];
injection st_eq; intros; subst;
replace (apply_cf_subst sigma' (Term g1 (Var v1 :: l1))) with
(Term g1 (quicksort (flatten g1 ((Term g1 ll1) :: map (apply_cf_subst sigma') l1)))).
apply (f_equal (fun l => Term g1 l)).
apply sort_is_unique.
apply quick_sorted.
apply well_formed_cf_sorted with g1; trivial.
apply quick_permut_bis;
simpl; generalize (F.Symb.eq_bool_ok g1 g1); case (F.Symb.eq_bool g1 g1); 
[intros _ | intros g1_diff_g1; absurd (g1 = g1); trivial].
transitivity (ll1 ++ l2'); trivial.
rewrite <- permut_app1.
rewrite (flatten_apply_cf_subst sigma' l1 Af1);
rewrite (H1 (build g1 l1) (build g1 l2')); [idtac | left; trivial]; apply flatten_build; trivial.
intros t In_t; apply well_formed_cf_alien with l2; trivial;
rewrite <- (list_permut.in_permut_in P); apply in_or_app; right; trivial.
generalize (H3 v1); simpl; rewrite F; rewrite Af1; intro H3_v1; rewrite H3_v1; trivial.

intros _; generalize (W3 v1);
case_eq (find X.eq_bool v1 (partly_solved_part pb)); [intros p1 F' | intro F'].
(* l1 = t1 :: _, t1 is a variable v1 and v1 has a partial value p1 *)
unfold ac_elementary_solve_term_var_with_part_val_term in *.
generalize (F.Symb.eq_bool_ok f1 (head_symb p1));
case (F.Symb.eq_bool f1 (head_symb p1)); [intro f1_eq_hd_p1 | intro f1_diff_hd_p1].
(* l1 = t1 :: _, t1 is a variable v1, v1 has a partial value p1 and the head of p1 is f1 *)
generalize (in_remove _ _ T.eq_bool_ok (closed_term p1) l2);
destruct (remove T.eq_bool (closed_term p1) l2) as [l2''' | ]; [idtac | contradiction].
rewrite <- f1_eq_hd_p1; rewrite Af1.
intros [cp1 [l2' [l2'' [ H' [l2_eq l2'''_eq]]]]].
injection l2'''_eq; clear l2'''_eq; intro l2'''_eq.
intros _ [pb'_eq_ | pb'_in_nil]; [subst pb' | contradiction].
intros [sigma' [[H1 [H2 H3]] H4]]; exists sigma'; unfold is_rough_sol; 
split; [split; [idtac | split] | idtac]; trivial.
rewrite U_pb; intros s t [st_eq | In_st]; [idtac | subst; apply H1; right; trivial];
injection st_eq; intros; subst s t; clear st_eq.
assert (v1_sigma'_eq : apply_cf_subst sigma' (Var v1) = 
Term f1 (quicksort (flatten f1 (apply_cf_subst sigma' (Var (new_var p1)) :: 
                                                 closed_term p1 :: nil)))).
generalize (H2 v1); simpl; rewrite F'; subst f1; trivial.
assert (l1_sigma'_eq := 
             (H1 (build f1 (Var (new_var p1) :: l1))  (build f1 l2''') (or_introl _ (eq_refl _)))).

replace (apply_cf_subst sigma' (Term f1 (Var v1 :: l1))) with 
         (Term f1 (quicksort (flatten f1 (((apply_cf_subst sigma' (Var v1)) :: nil) ++ 
                                                                  map (apply_cf_subst sigma') l1))));
[ idtac | simpl; rewrite Af1; trivial];
apply (f_equal (fun l => Term f1 l)).
apply sort_is_unique.
apply quick_sorted.
apply well_formed_cf_sorted with f1; trivial.
replace (build f1 (Var (new_var p1) :: l1)) with 
(Term f1 (quicksort (Var (new_var p1) :: l1))) in l1_sigma'_eq.
simpl in l1_sigma'_eq; rewrite Af1 in l1_sigma'_eq.
transitivity (closed_term p1 :: l2'''); 
[idtac | subst l2; rewrite <- permut_cons_inside; auto].

assert (build_f1_l2'''_eq : build f1 l2''' = Term f1 (quicksort l2''')).
destruct l2''' as [ | u2 [ | u2' l2''']]; 
[simpl; rewrite quicksort_equation; trivial | idtac | trivial].
assert (Al_u2 : match u2 with | Var _ => True | Term g _ => f1 <> g end).
apply (well_formed_cf_alien Af1 W_t2).
subst l2; assert (u2_in_l2'_l2'' : In u2 (l2' ++ l2'')). rewrite <- l2'''_eq; left; trivial.
destruct (in_app_or _ _ _ u2_in_l2'_l2''); apply in_or_app; [left | right; right]; trivial.
simpl in l1_sigma'_eq; destruct u2 as [ | g2]; 
[discriminate | injection l1_sigma'_eq; intros; subst g2; absurd (f1 = f1); trivial].

replace (build f1 l2''') with (Term f1 (quicksort l2''')) in l1_sigma'_eq; trivial.
assert (P : permut (flatten f1 (map (apply_cf_subst sigma') (Var (new_var p1) :: l1)))
                                     l2''').
apply permut_sym; transitivity (quicksort l2''').
apply quick_permut.
injection l1_sigma'_eq; intros H''; rewrite <- H''; clear H'';
apply quick_permut_bis.
apply list_permut_flatten.
apply list_permut.permut_map with (@eq term).
intros; subst; reflexivity.
apply quick_permut_bis; auto.
apply quick_permut_bis.
transitivity (closed_term p1 :: (flatten f1 (map (apply_cf_subst sigma') (Var (new_var p1) :: l1))));
[idtac | rewrite <- permut_cons; trivial].
rewrite v1_sigma'_eq; rewrite flatten_app; 
replace (map (apply_cf_subst sigma') (Var (new_var p1) :: l1)) with
(apply_cf_subst sigma' (Var (new_var p1)) :: map (apply_cf_subst sigma') l1); trivial.
generalize (map (apply_cf_subst sigma') l1) (apply_cf_subst sigma' (Var (new_var p1)));
intros l1_sigma' t; replace (t :: l1_sigma') with ((t :: nil) ++ l1_sigma'); trivial;
rewrite flatten_app; rewrite app_comm_cons; rewrite <- permut_app2.
assert (Al_ct : match closed_term p1 with | Var _ => True | Term g _ => f1 <> g end).
generalize (W3 v1); rewrite F'; rewrite <- f1_eq_hd_p1; rewrite Af1; intuition.
pattern (quicksort (flatten f1 (t :: closed_term p1 :: nil))); unfold flatten at 1.
generalize (F.Symb.eq_bool_ok f1 f1); case (F.Symb.eq_bool f1 f1); [intros _ | intro f1_diff_f1; apply False_rect; apply f1_diff_f1; reflexivity].
rewrite app_nil_r; apply quick_permut_bis.
replace (flatten f1 (t :: closed_term p1 :: nil)) with
  (flatten f1 (t :: nil) ++ flatten f1 (closed_term p1 :: nil)).
simpl flatten at 2.
destruct (closed_term p1) as [v | g ll].
apply permut_sym; rewrite <- permut_cons_inside.
rewrite app_nil_r; reflexivity.
reflexivity.
generalize (F.Symb.eq_bool_ok f1 g); case (F.Symb.eq_bool f1 g). 
intro f1_eq_g; apply False_rect; apply Al_ct; assumption.
intros _; apply permut_sym; rewrite <- permut_cons_inside.
rewrite app_nil_r; reflexivity.
reflexivity.
rewrite <- flatten_app; reflexivity.
reflexivity.
subst l2'''; reflexivity.
rewrite build_eq_Term; trivial; simpl; 
generalize (well_formed_cf_length Af1 W_t1); simpl; trivial.

(* l1 = t1 :: _, t1 is a variable v1, v1 has a partial value p1 and the head of p1 is NOT f1 *)
intros W3_v1 In_pb'; 
pattern pb';
refine 
(prop_map_without_repetition (B:=matching_problem) _ T.eq_bool_ok _ _ _ _ pb' In_pb');
clear pb' In_pb'; intros [ | g2 ll2] In_t2; trivial.
generalize (F.Symb.eq_bool_ok g2 (head_symb p1));
case (F.Symb.eq_bool g2 (head_symb p1)); [intro g2_eq_hd_p1 | intro g2_diff_hd_p1]; trivial.
generalize (in_remove _ _ T.eq_bool_ok (closed_term p1) ll2);
destruct (remove T.eq_bool (closed_term p1) ll2) as [ll2''' | ]; trivial;
intros [cp1 [ll2' [ll2'' [ H' [ll2_eq ll2'''_eq]]]]].
injection ll2'''_eq; clear ll2'''_eq; intro ll2'''_eq;
generalize (in_remove _ _ T.eq_bool_ok (Term g2 ll2) l2);
destruct (remove T.eq_bool (Term g2 ll2) l2) as [l2''' | ]; trivial.
intros [cp1' [l2' [l2'' [ H'' [l2_eq l2'''_eq]]]]].
injection l2'''_eq; clear l2'''_eq; intro l2'''_eq;
assert (Ag2 : arity g2 = AC).
rewrite <- g2_eq_hd_p1 in W3_v1; destruct (arity g2); [trivial | contradiction | contradiction].
assert (W_g2_ll2 : well_formed_cf (Term g2 ll2)).
apply well_formed_cf_subterms with f1 l2; trivial.

intros [sigma' [[H1 [H2 H3]] H4]]; exists sigma'; unfold is_rough_sol; 
split; [split; [idtac | split] | idtac]; trivial.
rewrite U_pb; intros s t [st_eq | In_st]; [idtac | subst; apply H1; right; right; trivial];
injection st_eq; intros; subst s t; clear st_eq.
assert (v1_sigma'_eq : apply_cf_subst sigma' (Var v1) = 
Term (head_symb p1) 
     (quicksort (flatten (head_symb p1) (apply_cf_subst sigma' (Var (new_var p1)) :: 
                                                 closed_term p1 :: nil)))).
generalize (H2 v1); simpl; rewrite F'; trivial.
assert (l1_sigma'_eq := 
             (H1 (build f1 l1)  (build f1 l2''') ((or_intror _ (or_introl _ (eq_refl _)))))).

replace (apply_cf_subst sigma' (Term f1 (Var v1 :: l1)))
with (Term f1 (quicksort (flatten f1 (((apply_cf_subst sigma' (Var v1)) :: nil) ++ map (apply_cf_subst sigma') l1))));
[ idtac | simpl; rewrite Af1; trivial];
apply (f_equal (fun l => Term f1 l)).
apply sort_is_unique.
apply quick_sorted.
apply well_formed_cf_sorted with f1; trivial.
apply quick_permut_bis; rewrite flatten_app.
transitivity
    (flatten f1 (apply_cf_subst sigma' (Var v1) :: nil) ++ 
    (flatten f1 (build f1 l2''' :: nil))). 
rewrite <- permut_app1; rewrite <- l1_sigma'_eq; 
apply flatten_apply_cf_subst; trivial.
transitivity (flatten f1 (apply_cf_subst sigma' (Var v1) :: nil) ++ l2''').
rewrite <- permut_app1; apply flatten_build; trivial;
intros t In_t; apply (well_formed_cf_alien Af1 W_t2); subst l2 l2''';
generalize (in_app_or _ _ _ In_t); clear In_t; intros [In_t | In_t];
apply in_or_app; [left | right; right]; trivial.
subst l2 l2''' cp1'.
replace (l2' ++ Term g2 ll2 :: l2'') with ((l2' ++ Term g2 ll2 :: nil) ++ l2'').
rewrite <- app_ass; rewrite <- permut_app2.
refine (permut_trans _ (list_permut_app_app _ _));
rewrite <- permut_app2.
assert (new_var_p1_sigma'_eq :=
  (H1 (Var (new_var p1))  (build g2 ll2''') (or_introl _ (eq_refl _)))).
rewrite v1_sigma'_eq; rewrite new_var_p1_sigma'_eq; rewrite <- g2_eq_hd_p1;
transitivity
(Term g2
        (quicksort
           (flatten g2 (build g2 ll2''' :: closed_term p1 :: nil)))
      :: nil).
simpl; generalize (F.Symb.eq_bool_ok f1 g2); case (F.Symb.eq_bool f1 g2); [intros f1_eq_g2 | intros _]; 
[absurd (f1 = g2); subst; trivial | auto].
replace ll2 with (quicksort (flatten g2 (build g2 ll2''' :: closed_term p1 :: nil))); auto;
apply sort_is_unique.
apply quick_sorted.
apply well_formed_cf_sorted with g2; trivial.
apply quick_permut_bis; 
replace  (build g2 ll2''' :: closed_term p1 :: nil) with  
((build g2 ll2''' :: nil) ++ (closed_term p1 :: nil)); trivial;
rewrite flatten_app.
transitivity (ll2''' ++ flatten g2 (closed_term p1 :: nil)).
rewrite <- permut_app2; apply flatten_build; trivial.
intros t In_t; apply well_formed_cf_alien with ll2; trivial;
subst ll2 ll2'''; generalize (in_app_or _ _ _ In_t); clear In_t; intros [In_t | In_t];
apply in_or_app; [left | right; right]; trivial.
replace (flatten g2 (closed_term p1 :: nil)) with (closed_term p1 :: nil).
subst ll2 ll2'''; simpl; rewrite <- permut_add_inside.
rewrite app_nil_r; auto.
subst; reflexivity.
simpl; destruct (arity (head_symb p1)) as [ | | ]; [idtac | contradiction | contradiction].
generalize (well_formed_cf_alien Ag2 W_g2_ll2 cp1); subst.
destruct (closed_term p1) as [ | g1]; trivial.
intro H;
generalize (F.Symb.eq_bool_ok (head_symb p1) g1); case (F.Symb.eq_bool (head_symb p1) g1); [intros g2_eq_g1 | intros _]. 
absurd (head_symb p1 = g1); trivial.
apply H; apply in_or_app; right; trivial.
left; trivial.
reflexivity.
rewrite app_ass; simpl; trivial.

(* l1 = t1 :: _, t1 is a variable v1, v1 has no value, neither plain nor partial *)
intros _; unfold ac_elementary_solve_term_var_without_val_term in *.
intro In_pb';
pattern pb';
refine 
(prop_map12_without_repetition (B:=matching_problem) _ T.eq_bool_ok _ _ _ _ pb' In_pb').
clear pb' In_pb';
intros t2 In_t2; generalize (in_remove _ _ T.eq_bool_ok t2 l2);
destruct (remove T.eq_bool t2 l2) as [l2''' | ]; trivial; 
intros [cp1' [l2' [l2'' [ H'' [l2_eq l2'''_eq]]]]].
injection l2'''_eq; clear l2'''_eq; intro l2'''_eq;
assert (Common : 
(exists sigma' : substitution,
   is_rough_sol
     (mk_pb (existential_vars pb) ((build f1 l1, build f1 l2''') :: l)
        ((v1, t2) :: solved_part pb) (partly_solved_part pb)) sigma' /\
   (forall v : variable,
    In v
      (existential_vars
         (mk_pb (existential_vars pb) ((build f1 l1, build f1 l2''') :: l)
            ((v1, t2) :: solved_part pb) (partly_solved_part pb))) \/
    apply_cf_subst sigma (Var v) = apply_cf_subst sigma' (Var v))) ->
exists sigma' : substitution,
  is_rough_sol pb sigma' /\
  (forall v : variable,
   In v (existential_vars pb) \/
   apply_cf_subst sigma (Var v) = apply_cf_subst sigma' (Var v))).
intros [sigma' [[H1 [H2 H3]] H4]]; exists sigma'; unfold is_rough_sol; 
split; [split; [idtac | split] | idtac]; trivial.
rewrite U_pb; intros s t [st_eq | In_st]; [idtac | subst; apply H1; right; trivial];
injection st_eq; intros; subst s t; clear st_eq.
assert (v1_sigma'_eq : apply_cf_subst sigma' (Var v1) = t2).
generalize (H3 v1); simpl.
generalize (X.eq_bool_ok v1 v1); case (X.eq_bool v1 v1); [ intros _ | intro v1_diff_v1]; [idtac | absurd (v1 = v1)] ; trivial.
assert (l1_sigma'_eq := H1 (build f1 l1)  (build f1 l2''') (or_introl _ (eq_refl _))).
replace (apply_cf_subst sigma' (Term f1 (Var v1 :: l1)))
with (Term f1 (quicksort (flatten f1 ((t2 :: nil) ++ map (apply_cf_subst sigma') l1))));
[ idtac | rewrite <- v1_sigma'_eq; simpl; rewrite Af1; trivial];
apply (f_equal (fun l => Term f1 l));
apply sort_is_unique;
[ apply quick_sorted | apply (well_formed_cf_sorted Af1 W_t2) | idtac];
apply quick_permut_bis; rewrite flatten_app; 
assert (Ft2 : flatten f1 (t2 :: nil) = t2 :: nil).
generalize (well_formed_cf_alien Af1 W_t2 _ In_t2); intro; 
destruct t2 as [ | g2]; trivial; simpl;
generalize (F.Symb.eq_bool_ok f1 g2); case (F.Symb.eq_bool f1 g2); [intro f1_eq_g2 | intros _]; [absurd (f1 = g2); trivial | auto].
rewrite Ft2; subst l2; simpl; rewrite <- permut_cons_inside. 
rewrite (flatten_apply_cf_subst sigma' l1 Af1); rewrite l1_sigma'_eq;
subst; apply flatten_build; trivial;
intros t In_t; apply (well_formed_cf_alien Af1 W_t2);
generalize (in_app_or _ _ _ In_t); clear In_t; intros [In_t | In_t];
apply in_or_app; [left | right; right]; trivial.
subst; reflexivity.

intro v; generalize (H3 v); simpl.
generalize (X.eq_bool_ok v  v1); case (X.eq_bool v v1); [intro v_eq_v1 | intros _; trivial].
subst v1; rewrite F; intros _; exact I.
unfold EDS.A, DOS.A in *; destruct (le_gt_dec (length l2) (length l1 + 1)) as [_ | _]; trivial;
split; trivial; clear Common.

intros [sigma' [[H1 [H2 H3]] H4]];
exists ((fresh_var pb, apply_cf_subst sigma (Var (fresh_var pb))) :: sigma'); split.
apply R; [intuition | idtac].
split; [idtac | split] ; trivial.
rewrite U_pb; intros s t [st_eq | In_st]; [idtac | subst; apply H1; right; trivial];
injection st_eq; intros; subst s t; clear st_eq.
simpl; rewrite Af1; apply (f_equal (fun l => Term f1 l));
apply sort_is_unique; [ apply quick_sorted |  apply (well_formed_cf_sorted Af1 W_t2) | idtac];
apply quick_permut_bis; 
generalize (H2 v1); unfold partly_solved_part; simpl find;
generalize (X.eq_bool_ok v1 v1); case (X.eq_bool v1 v1); [ intros _ | intro v1_diff_v1]; [idtac | absurd (v1 = v1)] ; trivial.
intro H2_v1; fold (apply_cf_subst sigma' (Var v1)); rewrite H2_v1; clear H2_v1;
simpl head_symb; simpl new_var; simpl closed_term;
generalize (F.Symb.eq_bool_ok f1 f1); case (F.Symb.eq_bool f1 f1); [intros _ | intro f1_diff_f1; apply False_rect; apply f1_diff_f1; reflexivity].
transitivity
   (flatten f1 (apply_cf_subst sigma' (Var (fresh_var pb)) :: t2 :: nil) ++
      flatten f1 (map (apply_cf_subst sigma') l1));
[rewrite <- permut_app2; apply quick_permut_bis; auto | idtac].
replace (apply_cf_subst sigma' (Var (fresh_var pb)) :: t2 :: nil) with
((apply_cf_subst sigma' (Var (fresh_var pb)) :: nil) ++ (t2 :: nil)); trivial.
subst l2 l2''' cp1'; rewrite <- (add_a_subterm _ _ _ _ Af1 W_t2);
replace (build f1 (l2' ++ l2'') :: t2 :: nil) with ((build f1 (l2' ++ l2'') :: nil) ++ (t2 :: nil)); trivial.
do 2 rewrite flatten_app; replace (flatten f1 (t2 :: nil)) with (t2 :: nil); 
[idtac | destruct t2 as [ | g2]; simpl; trivial; 
            generalize (F.Symb.eq_bool_ok f1 g2); case (F.Symb.eq_bool f1 g2); [intros f1_eq_g2 | intros _]; trivial; 
            absurd (f1 = g2); trivial; apply (well_formed_cf_alien Af1 W_t2 _ In_t2)].
rewrite app_ass; rewrite <- app_comm_cons.
rewrite <- permut_add_inside.
rewrite <- app_ass; do 2 rewrite app_nil_r.
apply permut_sym; 
rewrite <- (H1 (build f1 (Var (fresh_var pb) :: l1))  (build f1 (l2' ++ l2'')) (or_introl _ (eq_refl _))).
rewrite build_eq_Term; [idtac | generalize (well_formed_cf_length Af1 W_t1); simpl; trivial].
simpl; rewrite Af1; 
generalize (F.Symb.eq_bool_ok f1 f1); case (F.Symb.eq_bool f1 f1); [intros _ | intro f1_diff_f1; apply False_rect; apply f1_diff_f1; reflexivity].
rewrite app_nil_r; apply quick_permut_bis.
transitivity (flatten f1 (map (apply_cf_subst sigma') (Var (fresh_var pb) :: l1))).
apply list_permut_flatten.
apply list_permut.permut_map with (@eq term).
intros; subst; reflexivity.
apply quick_permut_bis; auto. 
simpl; destruct (find X.eq_bool (fresh_var pb) sigma') as [ [ | g ] | ].
intros; apply permut_refl.
case (F.Symb.eq_bool f1 g).
intros; rewrite app_nil_r; apply permut_refl.
intros; apply permut_refl.
apply permut_refl.
reflexivity.

intros v; generalize (H2 v); simpl partly_solved_part; simpl find.
generalize (X.eq_bool_ok v v1); case (X.eq_bool v v1); [intros v_eq_v1; subst; rewrite F'; trivial | intros _; trivial].
intros v; generalize (H4 v); simpl existential_vars.
intros [[v_eq | In_v] | v_sigma_eq].
right; rewrite v_eq; simpl.
generalize (X.eq_bool_ok v v); case (X.eq_bool v v); [ intros _ | intro v_diff_v]; [idtac | absurd (v = v)] ; trivial.
left; trivial.
right; simpl; generalize (X.eq_bool_ok v (fresh_var pb)); case (X.eq_bool v (fresh_var pb)).
intro v_eq; rewrite <- v_eq; reflexivity.
intros _; assumption.

(* l1 = t1 :: _, t1 is a complex term (Term g1 ll1) *)
unfold ac_elementary_solve_term_term_term in *.
intro In_pb';
pattern pb';
refine 
(prop_map_without_repetition (B:=matching_problem) _ T.eq_bool_ok _ _ _ _ pb' In_pb');
clear pb' In_pb'; intros [ | g2 ll2] In_t2; trivial;
generalize (F.Symb.eq_bool_ok g1 g2); case (F.Symb.eq_bool g1 g2); [intro g1_eq_g2 | intro g1_diff_g2]; trivial.
generalize (in_remove _ _ T.eq_bool_ok (Term g2 ll2) l2);
destruct (remove T.eq_bool (Term g2 ll2) l2) as [l2''' | ]; trivial;
intros [cp1' [l2' [l2'' [ H'' [l2_eq l2'''_eq]]]]].
injection l2'''_eq; clear l2'''_eq; intro l2'''_eq;
intros [sigma' [[H1 [H2 H3]] H4]]; exists sigma'; 
split; [split; [idtac | split] | idtac]; trivial.
rewrite U_pb; intros s t [st_eq | In_st].
injection st_eq; intros; subst.
replace (apply_cf_subst sigma' (Term f1 (Term g2 ll1 :: l1))) with
(Term f1 (quicksort (flatten f1 (apply_cf_subst sigma' (Term g2 ll1) :: nil) ++
                                flatten f1 (map (apply_cf_subst sigma') l1)))); 
[idtac | rewrite <- flatten_app; simpl; rewrite Af1; trivial].
apply (f_equal (fun l => Term f1 l)).
apply sort_is_unique; 
[apply quick_sorted | apply well_formed_cf_sorted with f1; trivial | idtac].
apply quick_permut_bis.
rewrite (H1 _ _ (or_introl _ (eq_refl _))); rewrite <- flatten_app;
rewrite <- app_comm_cons; simpl (app (A:=term) nil); cbv beta.
apply add_a_subterm_subst; trivial. 
apply H1; right; left; trivial.
apply H1; right; right; trivial.

(* arity f1 = C *)
destruct l1 as [ | u1 [ | u2 [ | u3 l1]]]; [contradiction | contradiction | idtac | contradiction].
destruct l2 as [ | v1 [ | v2 [ | v3 l2]]]; [contradiction | contradiction | idtac | contradiction].
intros [pb'_eq_ | [pb'_eq_ | pb'_in_nil]]; [subst pb'; simpl unsolved_part | subst pb'; simpl unsolved_part | contradiction].
intros [sigma' [[H1 [H2 H3]] H4]]; exists sigma'; 
split; [split; [idtac | split] | idtac]; trivial;
rewrite U_pb; intros s t [st_eq | In_st].
injection st_eq; intros; subst; simpl; rewrite Af1;
rewrite (H1 _ _ (or_introl _ (eq_refl _)));
rewrite (H1 _ _ (or_intror _ (or_introl _ (eq_refl _))));
apply (f_equal (fun l => Term f1 l));
assert (W_t2 := proj2 (W1 _ _ (or_introl _ (eq_refl _))));
simpl in W_t2; rewrite Af1 in W_t2; 
apply sort_is_unique; [apply quick_sorted | intuition | apply quick_permut_bis; auto].
apply H1; right; right; trivial.

intros [sigma' [[H1 [H2 H3]] H4]]; exists sigma'; 
split; [split; [idtac | split] | idtac]; trivial;
rewrite U_pb; intros s t [st_eq | In_st].
injection st_eq; intros; subst; simpl; rewrite Af1;
rewrite (H1 _ _ (or_introl _ (eq_refl _)));
rewrite (H1 _ _ (or_intror _ (or_introl _ (eq_refl _))));
apply (f_equal (fun l => Term f1 l));
assert (W_t2 := proj2 (W1 _ _ (or_introl _ (eq_refl _))));
simpl in W_t2; rewrite Af1 in W_t2; 
apply sort_is_unique; [apply quick_sorted | intuition | idtac].
apply quick_permut_bis.
apply (@list_permut.Pcons _ term (@eq term) v2 v2 (v1 :: nil) (v1 :: nil) nil); auto.
apply H1; right; right; trivial.

(* arity f1 = Free n1 *)
intros In_pb' [sigma' [[H1 [H2 H3]] H4]]; exists sigma';
split; [split; [idtac | split] | idtac].
assert 
(In_t1t2 : forall t1 t2 l1 l2 l, In (t1,t2) l ->
       match 
       fold_left2
          (fun (current_list_of_eqs : list (term * term)) (t1 t2 : term) =>
                (t1, t2) :: current_list_of_eqs) l l1 l2
           with
           | Some new_list_of_equations =>
               In (t1,t2) new_list_of_equations
           | None => True
           end).
clear  l l1 l2 R W1 U_pb In_pb'; 
intros t1 t2; induction l1 as [ | a1 l1]; intros l2 l In_l; destruct l2; simpl; trivial;
apply IHl1; right; trivial.
rewrite U_pb;  intros s t [st_eq | In_st].
(* in the original unsolved part *)
injection st_eq; clear st_eq;
intros; subst; simpl; rewrite Af1; apply (f_equal (fun l => Term f1 l)).
assert (L12 : length l1 = length l2).
apply trans_eq with n1; [idtac | apply sym_eq];
generalize (W1 (Term f1 l1) (Term f1 l2) (or_introl _ (eq_refl _)));
intros [[_ W_t1] [_ W_t2]]; [rewrite Af1 in W_t1 | rewrite Af1 in W_t2]; trivial.
generalize l l2 In_pb' L12 H1; clear U_pb R W1 W2 W3 l l2 In_pb' L12 H1.
induction l1 as [ | t1 l1]; destruct l2 as [ | t2 l2].
intros [In_pb' | In_pb'] _; [idtac | contradiction]; trivial.
intros _ L12; simpl in L12; discriminate.
intros _ L12; simpl in L12; discriminate.
intros In_pb' L12 H1; simpl in L12; generalize (eq_add_S _ _ L12); clear L12; intro L12.
generalize (IHl1 _ _ In_pb' L12); clear IHl1; intro IHl1; 
generalize (In_t1t2 _ _ l1 l2 ((t1,t2) :: l) (or_introl _ (eq_refl _))); clear In_t1t2;
intro In_t1t2.
simpl in In_pb';
destruct (fold_left2
               (fun (current_list_of_eqs : list (term * term)) (t1 t2 : term) =>
                (t1, t2) :: current_list_of_eqs) ((t1,t2) :: l) l1 l2) as [new_list_of_equations | ];
[idtac | contradiction].
generalize In_pb'; clear In_pb'; intros [pb'_eq | In_pb']; [idtac | contradiction].
simpl; rewrite (IHl1 H1); revert pb'_eq; intros; subst; rewrite (H1 _ _ In_t1t2); trivial.
(* in the decomposed unsolved part *)
rewrite (H1 s t); trivial.
generalize (In_t1t2 _ _ l1 l2 _ In_st).
destruct (fold_left2
               (fun (current_list_of_eqs : list (term * term)) (t1 t2 : term) =>
                (t1, t2) :: current_list_of_eqs) l l1 l2);
[idtac | contradiction].
generalize In_pb'; clear In_pb'; intros [pb'_eq | In_pb']; [idtac | contradiction].
subst; simpl; trivial.

destruct (fold_left2
               (fun (current_list_of_eqs : list (term * term)) (t1 t2 : term) =>
                (t1, t2) :: current_list_of_eqs) l l1 l2);
[idtac | contradiction].
generalize In_pb'; clear In_pb'; intros [pb'_eq | In_pb']; [idtac | contradiction].
intro v; subst; apply H2; trivial.

destruct (fold_left2
               (fun (current_list_of_eqs : list (term * term)) (t1 t2 : term) =>
                (t1, t2) :: current_list_of_eqs) l l1 l2);
[idtac | contradiction].
generalize In_pb'; clear In_pb'; intros [pb'_eq | In_pb']; [idtac | contradiction].
intro v; subst; apply H3; trivial.

destruct (fold_left2
               (fun (current_list_of_eqs : list (term * term)) (t1 t2 : term) =>
                (t1, t2) :: current_list_of_eqs) l l1 l2);
[idtac | contradiction].
generalize In_pb'; clear In_pb'; intros [pb'_eq | In_pb']; [idtac | contradiction].
intro v; subst; apply H4; trivial.

Qed.

End Make.



