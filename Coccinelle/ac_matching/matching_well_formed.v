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
     matching_well_founded.

Module Type S.

Declare Module Import WFMatching : matching_well_founded.S.
Import Matching.
Import Cf_eq_ac.
Import Ac.
Import EqTh.
Import T.

Parameter well_formed_solve :
 forall pb, well_formed_pb pb -> forall pb', In pb' (solve pb) -> well_formed_pb pb'.

End S.

Module Make (WFMatching1 : matching_well_founded.S) : 
  S with Module WFMatching := WFMatching1.

Module WFMatching := WFMatching1.

Import WFMatching1.
Import Matching.
Import Cf_eq_ac.
Import Ac.
Import EqTh.
Import T.
Import F.
Import X.
Import Sort.
Import LPermut.

Theorem well_formed_solve :
 forall pb, well_formed_pb pb -> forall pb', In pb' (solve pb) -> well_formed_pb pb'.
Proof.
unfold solve, well_formed_pb; intros pb [W1 [W2 [W3 [W4 [W5 W6]]]]] pb' In_pb';
assert (Fresh_var_spec :~ (occurs_in_term_list (fresh_var pb)
    (map (fun p : term * term => let (t1, _) := p in t1) (unsolved_part pb)))).
intro; apply (fresh_var_spec pb); left; trivial.
unfold occurs_in_pb in W6; destruct (unsolved_part pb) as [ | [[v1 | f1 l1] t2] l].
(* unsolved_part pb = nil *)
contradiction.
(* unsolved_part pb =  (v1,t2) :: _ *)
revert In_pb'; case_eq (find X.eq_bool v1 (solved_part pb)); [intros t1 F | intros F].
(* v1 has falready a plain value t1, and t1 is equal or not to t2 *)
generalize (T.eq_bool_ok t1 t2); case (T.eq_bool t1 t2); [intros t1_eq_t2 | intros _; contradiction].
intros [pb'_eq_ | pb'_in_nil]; [subst; split | contradiction].
(* W1 *) intros; apply W1; right; trivial.
repeat split.
(* W2 *) intros; apply W2; right; trivial.
(* W3 *) intros; apply W3; right; trivial.
(* W4 *) intros; apply W4; right; trivial.
(* W5 *) intros; apply W5; right; trivial.
(* W6 *) intros v p H; generalize (W6 v p H); intros [[H1 | H1'] | [H2 | H3]].
right; right; rewrite H1; simpl; rewrite F; trivial.
left; trivial.
right; left; trivial.
right; right; trivial.

case_eq (find X.eq_bool v1 (partly_solved_part pb)); [intros p1 F' | intro F'].
(* v1 has not a plain value, but it has a partial value p1 *)
(* the partial value p1 is compatible or not with t2 *)
destruct t2 as [ v2 | f2 l2].
contradiction.
generalize (F.Symb.eq_bool_ok (head_symb p1) f2);
case (F.Symb.eq_bool (head_symb p1) f2); [intro f1_eq_f2 | contradiction].
generalize (W3 v1); rewrite F'; rewrite f1_eq_f2.
destruct_arity f2 n2 Af2; [ idtac | contradiction | contradiction].
intros [W_p1 H_p1]; generalize (in_remove _ _ T.eq_bool_ok (closed_term p1) l2);
destruct (remove T.eq_bool (closed_term p1) l2) as [ l2''' |]; [idtac | contradiction].
intros [cp1 [l2' [l2'' [ H [l2_eq l2'''_eq]]]]].
injection l2'''_eq; clear l2'''_eq; intro; subst l2''';
intros [pb'_eq_ | pb'_in_nil]; [subst; split | contradiction].
(* W1 *) intros t1 t2 [H | In_l].
inversion H; split; simpl; trivial.
apply well_formed_cf_build_inside with (closed_term p1); trivial;
refine (proj2 (A:= well_formed_cf (Var v1)) _); apply W1; left; trivial.
apply W1; right; trivial.
repeat split.
(* W2 *) intros; apply W2; right; trivial.
(* W3 *) intros; apply W3; right; trivial.
(* W4 *) intros; apply W4; right; trivial.
(* W5 *) intros; apply W5; right; trivial.
(* W6 *) intros v p H; generalize (W6 v p H); intros [[H1 | H1'] | [H2 | H3]].
right; left; rewrite H1; simpl; rewrite F'; trivial.
left; right; trivial.
right; left; trivial.
right; right; trivial.

intros [pb'_eq_ | pb'_in_nil]; [subst; split | contradiction].
(* v1 has no value at all, neither plain nor partial *)
(* W1 *) intros; apply W1; right; trivial.
repeat split.
(* W2 *) intros v; simpl; destruct (X.eq_bool v v1); [idtac | apply W2];
refine (proj2 (A:= well_formed_cf (Var v1)) _); apply W1; left; trivial.
(* W3 *) intros; apply W3; right; trivial.
(* W4 *) intros v; simpl; generalize (X.eq_bool_ok v v1); case (X.eq_bool v v1); [intros v_eq_v1 | intros _; apply W4].
subst v; rewrite (none_nb_occ_O _ _ _ F); rewrite (none_nb_occ_O _ _ _ F');
auto with arith.
(* W5 *) intros; apply W5; right; trivial.
(* W6 *) intros v p H; generalize (W6 v p H); intros [[H1 | H1'] | [H2 | H3]].
right; right; rewrite H1; simpl; generalize (X.eq_bool_ok v1 v1); case (X.eq_bool v1 v1); 
[trivial | intro v1_diff_v1; apply False_rect; apply v1_diff_v1; reflexivity].
left; trivial.
right; left; trivial.
right; right; simpl; destruct (X.eq_bool (new_var p) v1); trivial.

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
intros [cp1 [l2' [l2'' [ H [l2_eq l2'''_eq]]]]].
injection l2'''_eq; clear l2'''_eq; intro; subst l2''';
intros [pb'_eq | pb_in_nil]; [subst pb' s1 l2; split | contradiction].
(* W1 *) 
intros t1 t2 [H | In_l].
inversion H; split.
replace l1 with (nil ++ l1); trivial; apply well_formed_cf_build_inside with (Var v1); trivial.
apply well_formed_cf_build_inside with cp1; trivial.
apply W1; right; trivial.
repeat split.
(* W2 *) intros; apply W2; right; trivial.
(* W3 *) intros; apply W3; right; trivial.
(* W4 *) intros; apply W4; right; trivial.
(* W5 *) intros; apply W5; right; trivial.
(* W6 *) intros v p H; generalize (W6 v p H); intros [[[H1 | H1'] | H1''] | [H2 | H3]].
right; right; rewrite H1; simpl; rewrite F; trivial.
left; left; destruct l1 as [ | u1 [ | u2 l1]]; [contradiction | intuition | idtac];
simpl; apply list_permut_occurs_in_term_list with (u1 :: u2 :: l1); trivial;
apply quick_permut.
left; right; trivial.
right; left; trivial.
right; right; trivial.
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
intros P [pb'_eq_ | pb'_in_nil]; [subst; split | contradiction].
(* W1 *) 
intros t1 t2 [H | In_l].
inversion H; split.
replace l1 with (nil ++ l1); trivial; apply well_formed_cf_build_inside with (Var v1); trivial.
assert (In_l2'_In_l2 : forall t, In t l2' -> In t l2).
intros t In_l2'; rewrite <- (list_permut.in_permut_in P); apply in_or_app; right; trivial.
apply well_formed_cf_build; trivial.
apply Nat.le_trans with (length l1); trivial; apply le_S_n;
replace (S (length l1)) with (length (Var v1 :: l1)); trivial;
apply well_formed_cf_length with g1; trivial.
intros t In_l2'; apply well_formed_cf_subterms with g1 l2; trivial; apply In_l2'_In_l2; trivial.
intros t In_l2'; apply well_formed_cf_alien with l2; trivial; apply In_l2'_In_l2; trivial.
apply W1; right; trivial.
repeat split.
(* W2 *) intros; apply W2; right; trivial.
(* W3 *) intros; apply W3; right; trivial.
(* W4 *) intros; apply W4; right; trivial.
(* W5 *) intros; apply W5; right; trivial.
(* W6 *) intros v p H; generalize (W6 v p H); intros [[[H1 | H1'] | H1''] | [H2 | H3]].
right; right; rewrite H1; simpl; rewrite F; trivial.
left; left; destruct l1 as [ | u1 [ | u2 l1]]; [contradiction | intuition | idtac];
simpl; apply list_permut_occurs_in_term_list with (u1 :: u2 :: l1); trivial;
apply quick_permut.
left; right; trivial.
right; left; trivial.
right; right; trivial.

intros _; generalize (W3 v1);
case_eq (find X.eq_bool v1 (partly_solved_part pb)); [intros p1 F' | intro F'].
(* l1 = t1 :: _, t1 is a variable v1 and v1 has a partial value p1 *)
unfold ac_elementary_solve_term_var_with_part_val_term in *.
generalize (F.Symb.eq_bool_ok f1 (head_symb p1));
case (F.Symb.eq_bool f1 (head_symb p1)); [intro f1_eq_hd_p1; rewrite <- f1_eq_hd_p1 | intro f1_diff_hd_p1].
(* l1 = t1 :: _, t1 is a variable v1, v1 has a partial value p1 and the head of p1 is f1 *)
generalize (in_remove _ _ T.eq_bool_ok (closed_term p1) l2);
destruct (remove T.eq_bool (closed_term p1) l2) as [l2''' | ]; [idtac | contradiction].
intros [cp1 [l2' [l2'' [ H [l2_eq l2'''_eq]]]]].
injection l2'''_eq; clear l2'''_eq; intro; subst;
intros P [pb'_eq_ | pb'_in_nil]; [subst; split | contradiction].
(* W1 *) 
intros t1 t2 [H'' | In_l].
replace t1 with (fst (t1,t2)); trivial; rewrite <- H'';
replace t2 with (snd (t1,t2)); trivial; rewrite <- H''; unfold fst, snd; split.
apply well_formed_cf_build; trivial.
simpl; auto with arith.
intros t [t_eq | In_t_l1]; [subst; simpl; trivial | idtac];
apply well_formed_cf_subterms with (head_symb p1) (Var v1 :: l1); trivial; right; trivial.
intros t [t_eq | In_t_l1]; [subst; simpl; trivial | idtac].
apply well_formed_cf_alien with (Var v1 :: l1); trivial; right; trivial.
apply well_formed_cf_build_inside with (closed_term p1); trivial.
apply W1; right; trivial.
repeat split.
(* W2 *) intros; apply W2; right; trivial.
(* W3 *) intros; apply W3; right; trivial.
(* W4 *) intros; apply W4; right; trivial.
(* W5 *) intros; apply W5; right; trivial.
(* W6 *) intros v p H''; generalize (W6 v p H''); intros [[[H1 | H1'] | H1''] | [H2 | H3]].
right; left; rewrite H1; simpl; rewrite F'; trivial.
left; left; destruct l1 as [ | u1 l1]; [contradiction | idtac].
simpl; apply list_permut_occurs_in_term_list with (Var (new_var p1) :: u1 :: l1); 
[ apply quick_permut | idtac]; right; trivial.
left; right; trivial.
right; left; trivial.
right; right; trivial.
(* l1 = t1 :: _, t1 is a variable v1, v1 has a partial value p1 and the head of p1 is NOT f1 *)
intros W3_v1 In_pb'; 
pattern pb';
refine 
(prop_map_without_repetition (B:=matching_problem) _ T.eq_bool_ok _ _ _ _ pb' In_pb');
clear pb' In_pb'; intros [ | g2 ll2] In_t2; trivial.
generalize (F.Symb.eq_bool_ok g2 (head_symb p1));
case (F.Symb.eq_bool g2 (head_symb p1)); [intro g2_eq_hd_p1 | intro g2_diff_hd_p1; trivial].
generalize (in_remove _ _ T.eq_bool_ok (closed_term p1) ll2); 
destruct (remove T.eq_bool (closed_term p1) ll2) as [ll2''' | ]; trivial.
intros [cp1 [ll2' [ll2'' [ H [ll2_eq ll2'''_eq]]]]].
injection ll2'''_eq; clear ll2'''_eq; intro; subst ll2''';
generalize (in_remove _ _ T.eq_bool_ok (Term g2 ll2) l2);
destruct (remove T.eq_bool (Term g2 ll2) l2) as [l2''' | ]; trivial.
intros [cp1' [l2' [l2'' [ H' [l2_eq l2'''_eq]]]]].
injection l2'''_eq; clear l2'''_eq; intro; subst.
split.
(* W1 *) 
intros t1 t2 [H'' | [H'' | In_l]].
inversion H''; split; simpl; trivial; subst.
apply well_formed_cf_build_inside with (closed_term p1).
destruct (arity (head_symb p1)) as [ | | n]; [trivial | contradiction | contradiction].
apply (well_formed_cf_subterms W_t2); apply in_or_app; right; left; trivial.
inversion H''; split; subst.
replace l1 with (nil ++ l1); trivial;
replace (Var v1 :: l1) with (nil ++ Var v1 :: l1) in W_t1; trivial;
apply well_formed_cf_build_inside with (Var v1); trivial.
apply well_formed_cf_build_inside with 
(Term (head_symb p1) (ll2' ++ closed_term p1 :: ll2'')); trivial.
apply W1; right; trivial.
repeat split.
(* W2 *) intros; apply W2; right; trivial.
(* W3 *) intros; apply W3; right; trivial.
(* W4 *) intros; apply W4; right; trivial.
(* W5 *) intros; apply W5; right; trivial.
(* W6 *) intros v p H''; generalize (W6 v p H''); intros [[[H1 | H1'] | H1''] | [H2 | H3]].
right; left; rewrite H1; simpl; rewrite F'; trivial.
left; right; left; destruct l1 as [ | u1 [ | u2 l1]]; [contradiction | intuition | idtac].
simpl; apply list_permut_occurs_in_term_list with (u1 :: u2 :: l1);
[ apply quick_permut | idtac]; trivial.
left; right; right; trivial.
right; left; trivial.
right; right; trivial.
(* l1 = t1 :: _, t1 is a variable v1, v1 has no value, neither plain nor partial *)
intros _; unfold ac_elementary_solve_term_var_without_val_term in *.
intro In_pb'; pattern pb';
refine 
(prop_map12_without_repetition (B:=matching_problem) _ T.eq_bool_ok _ _ _ _ pb' In_pb');
clear pb' In_pb';
intros t2 In_t2; generalize (in_remove _ _ T.eq_bool_ok t2 l2);
destruct (remove T.eq_bool t2 l2) as [l2''' | ]; trivial.
intros [cp1' [l2' [l2'' [ H' [l2_eq l2'''_eq]]]]].
injection l2'''_eq; clear l2'''_eq; intro; subst l2''';
unfold DOS.A, EDS.A in *; destruct (le_gt_dec (length l2) (length l1 + 1)) as [_ | _]; trivial.
split.
(* W1 *) 
intros t1 t3 [H'' | In_l].
inversion H''; split; simpl; trivial; subst.
replace l1 with (nil ++ l1); trivial;
replace (Var v1 :: l1) with (nil ++ Var v1 :: l1) in W_t1; trivial;
apply well_formed_cf_build_inside with (Var v1); trivial.
apply well_formed_cf_build_inside with cp1'; trivial.
apply W1; right; trivial.
repeat split.
(* W2 *) 
intro v; simpl; destruct (X.eq_bool v v1);
[ apply well_formed_cf_subterms with f1 l2; trivial | apply W2 ].
(* W3 *) intros; apply W3; right; trivial.
(* W4 *) 
intro v; simpl; generalize (X.eq_bool_ok v v1); case (X.eq_bool v v1); [intro v_eq_v1 | intros _].
subst; rewrite (none_nb_occ_O _ _ _ F); rewrite (none_nb_occ_O _ _ _ F');
auto with arith.
apply W4.
(* W5 *) intros; apply W5; right; trivial.
(* W6 *) intros v p H''; generalize (W6 v p H''); intros [[[H1 | H1'] | H1''] | [H2 | H3]].
right; right; rewrite H1; simpl.
generalize (X.eq_bool_ok v1 v1); case (X.eq_bool v1 v1); [intros _; exact I | intro v1_diff_v1; apply False_rect; apply v1_diff_v1; reflexivity].
left; left; destruct l1 as [ | u1 [ | u2 l1]]; [contradiction | intuition | idtac];
simpl; apply list_permut_occurs_in_term_list with (u1 :: u2 :: l1); trivial;
apply quick_permut.
left; right; trivial.
right; left; trivial.
right; right; simpl; destruct (X.eq_bool (new_var p) v1); trivial.
do 2 split. 
(* W1 *) 
intros t1 t3 [H'' | In_l].
inversion H''; split; simpl; trivial; subst.
replace l1 with (nil ++ l1); trivial;
replace (Var v1 :: l1) with (nil ++ Var v1 :: l1) in W_t1; trivial;
apply well_formed_cf_build_inside with (Var v1); trivial.
apply well_formed_cf_build_inside with cp1'; trivial.
apply W1; right; trivial.
repeat split.
(* W2 *) 
intro v; simpl; destruct (X.eq_bool v v1);
[ apply well_formed_cf_subterms with f1 l2; trivial | apply W2 ].
(* W3 *) intros; apply W3; right; trivial.
(* W4 *) 
intro v; simpl; generalize (X.eq_bool_ok v v1); case (X.eq_bool v v1); [intro v_eq_v1 | intros _].
subst; rewrite (none_nb_occ_O _ _ _ F); rewrite (none_nb_occ_O _ _ _ F');
auto with arith.
apply W4.
(* W5 *) intros; apply W5; right; trivial.
(* W6 *) intros v p H''; generalize (W6 v p H''); intros [[[H1 | H1'] | H1''] | [H2 | H3]].
right; right; rewrite H1; simpl.
generalize (X.eq_bool_ok v1 v1); case (X.eq_bool v1 v1); [intros _; exact I | intro v1_diff_v1; apply False_rect; apply v1_diff_v1; reflexivity].
left; left; destruct l1 as [ | u1 [ | u2 l1]]; [contradiction | intuition | idtac];
simpl; apply list_permut_occurs_in_term_list with (u1 :: u2 :: l1); trivial;
apply quick_permut.
left; right; trivial.
right; left; trivial.
right; right; simpl; destruct (X.eq_bool (new_var p) v1); trivial.
(* W1 *) 
intros t1 t3 [H'' | In_l].
replace t1 with (fst (t1,t3)); trivial; rewrite <- H''; unfold fst;
replace t3 with (snd (t1,t3)); trivial; rewrite <- H''; unfold snd; split.
apply well_formed_cf_build; trivial.
simpl; auto with arith.
intros t [t_eq | In_t_l1]; [subst t; simpl; trivial | idtac];
apply well_formed_cf_subterms with f1 (Var v1 :: l1); trivial; right; trivial.
intros t [t_eq | In_t_l1]; [subst t; simpl; trivial | idtac];
apply well_formed_cf_alien with (Var v1 :: l1); trivial; right; trivial.
subst; apply well_formed_cf_build_inside with cp1'; trivial.
apply W1; right; trivial.
repeat split.
(* W2 *) intros; apply W2; right; trivial.
(* W3 *) intro v; simpl; destruct (X.eq_bool v v1).
simpl; rewrite Af1; split.
apply well_formed_cf_subterms with f1 l2; trivial.
apply well_formed_cf_alien with l2; trivial.
apply W3.
(* W4 *) 
intro v; simpl; generalize (X.eq_bool_ok v v1); case (X.eq_bool v v1); [intro v_eq_v1 | intros _].
subst; rewrite (none_nb_occ_O _ _ _ F); rewrite (none_nb_occ_O _ _ _ F');
auto with arith.
apply W4.
(* W5 *) 
simpl; intro; apply Fresh_var_spec; left; left; subst v1; simpl; trivial.
unfold new_var; intros v' one_v' v'_eq_fresh_var_pb; apply (fresh_var_spec pb);
right; left; rewrite <- v'_eq_fresh_var_pb.
generalize (none_nb_occ_O X.eq_bool v' (partly_solved_part pb));
destruct (find X.eq_bool v' (partly_solved_part pb)); trivial;
intro H; generalize (H (eq_refl _)); clear H; intro H; rewrite H in one_v';
absurd (1 <= 0); trivial; auto with arith.
apply W5.
(* W6 *) 
simpl; intros v p H; destruct (X.eq_bool v v1).
injection H; clear H; intro H; subst p; simpl.
left; left; destruct l1 as [ | u1 l1]; simpl; [trivial | idtac];
apply list_permut_occurs_in_term_list with (Var (fresh_var pb) :: u1 :: l1);
[apply quick_permut | left; simpl; trivial].
generalize (W6 _ _ H); intros [[[H1 | H1'] | H1''] | [H2 | H3]].
right; left; simpl; 
generalize (X.eq_bool_ok (new_var p) v1); case (X.eq_bool (new_var p) v1); [ intros _ | intros new_var_p_diff_v1]; trivial;
absurd (new_var p = v1); trivial.
left; left; destruct l1 as [ | u1 l1]; simpl; [contradiction | idtac];
apply list_permut_occurs_in_term_list with (Var (fresh_var pb) :: u1 :: l1);
[apply quick_permut | right; trivial].
left; right; trivial.
right; left; simpl; destruct (X.eq_bool (new_var p) v1); trivial.
right; right; trivial.

(* l1 = t1 :: _, t1 is a complex term (Term g1 ll1) *)
unfold ac_elementary_solve_term_term_term in *.
intro In_pb'; pattern pb';
refine 
(prop_map_without_repetition (B:=matching_problem) _ T.eq_bool_ok _ _ _ _ pb' In_pb');
clear pb' In_pb'; intros [ | g2 ll2] In_t2; trivial;
destruct (F.Symb.eq_bool g1 g2); trivial.
generalize (in_remove _ _ T.eq_bool_ok (Term g2 ll2) l2);
destruct (remove T.eq_bool (Term g2 ll2) l2) as [l2''' | ]; trivial.
intros [cp1' [l2' [l2'' [ H' [l2_eq l2'''_eq]]]]].
injection l2'''_eq; clear l2'''_eq; intro; subst l2''';
split.
(* W1 *) 
intros t1 t2 [H | [H | In_l]]; [idtac | idtac | apply W1; right; trivial].
injection H; clear H; intros; subst t1 t2; split.
apply (well_formed_cf_subterms W_t1); left; trivial.
apply (well_formed_cf_subterms W_t2); subst l2 cp1'; 
apply in_or_app; right; left; trivial.
injection H; clear H; intros; subst t1 t2; split.
replace l1 with (nil ++ l1); trivial;
replace (Term g1 ll1 :: l1) with (nil ++ Term g1 ll1 :: l1) in W_t1; trivial;
apply well_formed_cf_build_inside with (Term g1 ll1); trivial.
subst; apply well_formed_cf_build_inside with (Term g2 ll2); trivial.
repeat split.
(* W2 *) intros; apply W2; right; trivial.
(* W3 *) intros; apply W3; right; trivial.
(* W4 *) intros; apply W4; right; trivial.
(* W5 *) intros; apply W5; right; trivial.
(* W6 *) intros v p H; generalize (W6 v p H); intros [[[H1 | H1'] | H1''] | [H2 | H3]].
left; left; trivial.
left; right; left; destruct l1 as [ | u1 [ | u2 l1]]; [contradiction | intuition | idtac];
simpl; apply list_permut_occurs_in_term_list with (u1 :: u2 :: l1); trivial;
apply quick_permut.
left; right; right; trivial.
right; left; trivial.
right; right; trivial.

(* arity f1 = C *)
destruct l1 as [ | u1 [ | u2 [ | u3 l1]]]; [contradiction | contradiction | idtac | contradiction].
destruct l2 as [ | v1 [ | v2 [ | v3 l2]]]; [contradiction | contradiction | idtac | contradiction].
intros [pb'_eq_ | [pb'_eq_ | pb'_in_nil]]; [subst; split | subst; split | contradiction].
(* W1 *) intros t1 t2 [H | [H | In_l]]; [idtac | idtac | apply W1; right; trivial].
injection H; clear H; intros; subst t1 t2; split.
apply well_formed_cf_subterms with f1 (u1 :: u2 :: nil); [idtac | left; trivial];
refine (proj1 _ (B:= (well_formed_cf (Term f1 (v1 :: v2 :: nil))))); apply W1; left; trivial.
apply well_formed_cf_subterms with f1 (v1 :: v2 :: nil); [idtac | left; trivial];
apply (proj2 (A:= (well_formed_cf (Term f1 (u1 :: u2 :: nil))))); apply W1; left; trivial.
injection H; clear H; intros; subst t1 t2; split.
apply well_formed_cf_subterms with f1 (u1 :: u2 :: nil); [idtac | right; left; trivial];
refine (proj1 _ (B:= (well_formed_cf (Term f1 (v1 :: v2 :: nil))))); apply W1; left; trivial.
apply well_formed_cf_subterms with f1 (v1 :: v2 :: nil); [idtac | right; left; trivial];
apply (proj2 (A:= (well_formed_cf (Term f1 (u1 :: u2 :: nil))))); apply W1; left; trivial.
repeat split.
(* W2 *) intros; apply W2; right; trivial.
(* W3 *) intros; apply W3; right; trivial.
(* W4 *) intros; apply W4; right; trivial.
(* W5 *) intros; apply W5; right; trivial.
(* W6 *) intros v p H; generalize (W6 v p H); intros [[[H1 | [H1' | H1'']] | H1'''] | [H2 | H3]].
left; left; trivial.
left; right; left; trivial.
contradiction.
left; right; right; trivial.
right; left; trivial.
right; right; trivial.

(* W1 *) intros t1 t2 [H | [H | In_l]]; [idtac | idtac | apply W1; right; trivial].
injection H; clear H; intros; subst t1 t2; split.
apply well_formed_cf_subterms with f1 (u1 :: u2 :: nil); [idtac | left; trivial];
refine (proj1 _ (B:= (well_formed_cf (Term f1 (v1 :: v2 :: nil))))); apply W1; left; trivial.
apply well_formed_cf_subterms with f1 (v1 :: v2 :: nil); [idtac | right; left; trivial];
apply (proj2 (A:= (well_formed_cf (Term f1 (u1 :: u2 :: nil))))); apply W1; left; trivial.
injection H; clear H; intros; subst t1 t2; split.
apply well_formed_cf_subterms with f1 (u1 :: u2 :: nil); [idtac | right; left; trivial];
refine (proj1 _ (B:= (well_formed_cf (Term f1 (v1 :: v2 :: nil))))); apply W1; left; trivial.
apply well_formed_cf_subterms with f1 (v1 :: v2 :: nil); [idtac | left; trivial];
apply (proj2 (A:= (well_formed_cf (Term f1 (u1 :: u2 :: nil))))); apply W1; left; trivial.
repeat split.
(* W2 *) intros; apply W2; right; trivial.
(* W3 *) intros; apply W3; right; trivial.
(* W4 *) intros; apply W4; right; trivial.
(* W5 *) intros; apply W5; right; trivial.
(* W6 *) intros v p H; generalize (W6 v p H); intros [[[H1 | [H1' | H1'']] | H1'''] | [H2 | H3]].
left; left; trivial.
left; right; left; trivial.
contradiction.
left; right; right; trivial.
right; left; trivial.
right; right; trivial.

(* arity f1 = Free n1 *)
assert (L12 : length l1 = length l2).
apply trans_eq with n1; [idtac | apply sym_eq];
generalize (W1 (Term f1 l1) (Term f1 l2) (or_introl _ (eq_refl _)));
intros [[_ W_t1] [_ W_t2]]; [rewrite Af1 in W_t1 | rewrite Af1 in W_t2]; trivial.
split.
assert (W1_l : forall t1 t2, In (t1,t2) l -> well_formed_cf t1 /\ well_formed_cf t2). 
intros; apply W1; right; trivial.
assert (W_l1 : forall t, In t l1 -> well_formed_cf t).
intros; apply well_formed_cf_subterms with f1 l1; trivial;
refine (proj1 _ (B:= (well_formed_cf (Term f1 l2)))); apply W1; left; trivial.
assert (W_l2 : forall t, In t l2 -> well_formed_cf t).
intros; apply well_formed_cf_subterms with f1 l2; trivial;
apply (proj2 (A:= (well_formed_cf (Term f1 l1)))); apply W1; left; trivial.
generalize l l2 In_pb' L12 W1_l W_l1 W_l2; simpl;
clear W1 W2 W3 W4 W5 W6 Fresh_var_spec l l2 In_pb' L12 W1_l W_l1 W_l2;
induction l1 as [ | t1 l1]; destruct l2 as [ | t2 l2].
intros [In_pb' | In_pb'] _; [idtac | contradiction]; subst pb'; simpl; trivial.
intros _ L12; simpl in L12; discriminate.
intros _ L12; simpl in L12; discriminate.
intros In_pb' L12; simpl in L12; generalize (eq_add_S _ _ L12); clear L12; intro L12;
intros W1_l W_l1 W_l2; intros; apply IHl1 with ((t1, t2) :: l) l2; trivial.
intros t4 t5 [H' | In_l].
injection H'; split; subst; [apply W_l1 | apply W_l2]; left; trivial.
apply W1_l; trivial.
intros; apply W_l1; right; trivial.
intros; apply W_l2; right; trivial.
revert In_pb';
case_eq (fold_left2
               (fun (current_list_of_eqs : list (term * term)) (t1 t2 : term) =>
                (t1, t2) :: current_list_of_eqs) l l1 l2); [intros new_list_of_equations H | intro H; contradiction].
intros [pb'_eq_ | pb'_in_nil]; [subst; repeat split | contradiction].
(* W2 *) intros; apply W2; right; trivial.
(* W3 *) intros; apply W3; right; trivial.
(* W4 *) intros; apply W4; right; trivial.
(* W5 *) intros; apply W5; right; trivial.
(* W6 *) assert (H' : forall l1 l new_list_of_equations l2, 
fold_left2 (fun cl (t1 t2 : term) => (t1, t2) :: cl) l l1 l2 = Some new_list_of_equations ->
   forall u1 u2, In (u1, u2) l -> In (u1, u2) new_list_of_equations).
clear l l1 l2 W1 W6 Fresh_var_spec L12 H new_list_of_equations.
induction l1 as [ | v1 l1].
intros l new_list_of_equations [ | v2 l2]; simpl; [idtac | intros; discriminate];
intros H; injection H; intro; subst; trivial.
intros l new_list_of_equations [| v2 l2]; simpl; [intros; discriminate | idtac].
intros; apply IHl1 with ((v1,v2) :: l) l2; trivial; right; trivial.
intros v p H''; generalize (W6 v p H''); intros [ [H1 | H1'] | [H2 | H3]].

left; simpl occurs_in_term in H1; unfold unsolved_part.
generalize l l2 L12 H H1; clear l l2 W1 W6 Fresh_var_spec L12 H H1;
induction l1 as [ | u1 l1]; [contradiction | idtac].
intros l [| u2 l2] L12 H; [discriminate | idtac]; intros [In_u1 | In_l1].
assert (In_u1_new_list : In (u1,u2) new_list_of_equations).
simpl in H; apply H' with l1 ((u1,u2) :: l) l2; trivial; left; trivial.
generalize new_list_of_equations In_u1_new_list; 
clear new_list_of_equations H'' IHl1 H In_u1_new_list;
induction new_list_of_equations as [| [w1 w2] nle]; [contradiction | idtac].
intros [u12_eq | In_u12]; [injection u12_eq; intros; subst; left; trivial | idtac].
right; apply IHnle; trivial.
apply IHl1 with ((u1,u2) :: l) l2; trivial; apply eq_add_S; trivial.

left; assert (H''' : exists u1, exists u2, occurs_in_term (new_var p) u1 /\ In (u1, u2) l).
generalize (new_var p) l H1'; clear l H1' W1 W6 Fresh_var_spec H H''; 
induction l as [ | [u1 u2] l]; [contradiction | idtac]; intros [u12_eq | In_u12].
exists u1; exists u2; intuition auto with *.
generalize (IHl In_u12); 
intros [u3 [u4 [H1 H2]]]; exists u3; exists u4; split; trivial; right; trivial.
generalize H'''; clear H'''; intros [u1 [u2 [H''' In_u12]]];
generalize (H' _ _ _ _ H _ _ In_u12); clear l W1 W6 Fresh_var_spec H H1' In_u12 H'';
induction new_list_of_equations as [ | [v1 v2] nle]; [contradiction | idtac];
intros [u12_eq | In_u12].
injection u12_eq; intros; subst; left; trivial.
right; apply IHnle; trivial.

right; left; trivial.
right; right; trivial.
Qed.

End Make.
