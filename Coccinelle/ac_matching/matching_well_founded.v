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


From Coq Require Import Arith List.
From CoLoR Require Import more_list list_sort term_spec ac cf_eq_ac matching.

Module Type S.

Declare Module Import Matching : matching.S.
Import Cf_eq_ac.
Import Ac.
Import EqTh.
Import T.

Definition pb_weight pb := 
  list_size 
    (fun t1_t2 : term * term => 
       match t1_t2 with | (t1,t2) => ac_size t1 + ac_size t2 end)
     (unsolved_part pb).
Parameter well_founded_solve :
  forall pb, well_formed_pb pb -> 
  forall pb', In pb' (solve pb) -> pb_weight pb' < pb_weight pb.

End S.

Module Make (Matching1 : matching.S) : S with Module Matching := Matching1.

Module Matching := Matching1.
Import Matching1.
Import Cf_eq_ac.
Import Ac.
Import EqTh.
Import T.
Import F.
Import X.
Import Sort.
Import LPermut.

Lemma ac_size_build_eq : 
  forall f l, arity f = AC ->
  ac_size (build f l) = (length l - 1) + list_size ac_size l.
Proof.
intros f l Af; unfold build; simpl; destruct l as [ | t1 l].
rewrite quicksort_equation; simpl; rewrite Af; trivial.
destruct l as [ | t2 l].
simpl; auto with arith.
rewrite ac_size_unfold; rewrite Af; rewrite length_quicksort;
apply (f_equal (fun n => length (t1 :: t2 :: l) -1 + n));
apply list_permut.permut_size with (@eq term).
intros; subst; trivial.
apply quick_permut_bis; auto.
Qed.

Lemma ac_size_build_lt_args : 
  forall f l1 l2 t1, arity f = AC -> well_formed_cf (Term f (l1 ++ t1 :: l2)) ->
  ac_size (build f (l1 ++ l2)) + ac_size t1 < ac_size (Term f (l1 ++ t1 :: l2)).
Proof.
intros f l1 l2 t1 Ar W; 
pattern (ac_size (Term f (l1 ++ t1 :: l2))); rewrite ac_size_unfold.
rewrite ac_size_build_eq; trivial.
do 2 rewrite length_app;
do 2 rewrite list_size_app; simpl; rewrite <- Nat.add_assoc; 
apply Nat.add_lt_le_mono.
rewrite (Nat.add_comm (length l1) (S (length l2))); simpl;
rewrite <- Nat.sub_0_r;
rewrite (Nat.add_comm (length l2));
elim W; clear W; rewrite Ar; 
intros _ W; elim W; clear W;
intros L _; rewrite length_app in L; simpl in L;
rewrite Nat.add_comm in L; simpl in L;
rewrite Nat.add_comm in L;
destruct (length l1 + length l2).
absurd (1 >= 2); trivial; unfold ge; auto with arith.
auto with arith.
rewrite <- Nat.add_assoc; apply Nat.add_le_mono_l; 
rewrite Nat.add_comm; auto with arith.
Qed.

Lemma ac_size_build_lt : 
  forall f l1 l2 t1, arity f = AC -> well_formed_cf (Term f (l1 ++ t1 :: l2)) ->
  ac_size (build f (l1 ++ l2)) < ac_size (Term f (l1 ++ t1 :: l2)).
Proof.
intros f l1 l2 t1 Ar W.
apply Nat.lt_le_trans with (ac_size (build f (l1 ++ l2)) + ac_size t1).
rewrite (plus_n_O (ac_size (build f (l1 ++ l2))));
rewrite <- Nat.add_assoc; apply Nat.add_lt_mono_l;
simpl; unfold lt; apply ac_size_ge_one;
elim (well_formed_cf_unfold _ W); intros Wl _;
apply Wl; apply in_or_app; right; left; trivial.
apply Nat.lt_le_incl; apply ac_size_build_lt_args; trivial.
Qed.

Definition pb_weight pb := 
  list_size 
    (fun t1_t2 : term * term => 
       match t1_t2 with | (t1,t2) => ac_size t1 + ac_size t2 end)
     (unsolved_part pb).

Theorem well_founded_solve : 
  forall pb, well_formed_pb pb -> 
  forall pb', In pb' (solve pb) -> pb_weight pb' < pb_weight pb.
Proof.
unfold pb_weight, solve, well_formed_pb;
 intros pb [W1 [W2 [W3 _]]] pb' In_pb';
destruct (unsolved_part pb) as [ | [[v1 | f1 l1] t2] l].
(* unsolved_part pb = nil *)
contradiction.
(* unsolved_part pb =  (v1,t2) :: _ *)
destruct (find X.eq_bool v1 (solved_part pb)) as [t1 | ].
(* v1 has already a plain value t1, and t1 is equal or not to t2 *)
destruct (T.eq_bool t1 t2); [idtac | contradiction];
inversion_clear In_pb' as [pb'_eq_ | ]; [idtac | contradiction];
subst; simpl; auto with arith.
generalize (W3 v1); 
destruct (find X.eq_bool v1 (partly_solved_part pb)) as [ p1 |].
(* v1 has not a plain value, but it has a partial value p1 *)
(* the partial value p1 is compatible or not with t2 *)
destruct t2 as [ v2 | f2 l2].
contradiction.
revert In_pb'; generalize (F.Symb.eq_bool_ok (head_symb p1) f2); 
case (F.Symb.eq_bool (head_symb p1) f2); [intros f1_eq_f2 In_pb' | contradiction].
rewrite f1_eq_f2; destruct_arity f2 n2 Af2; [ idtac | contradiction | contradiction].
intros _; assert (In_l2 := in_remove _ _ T.eq_bool_ok (closed_term p1) l2).
destruct (remove T.eq_bool (closed_term p1) l2) as [ l2''' | ]; [idtac | contradiction].
destruct In_l2 as [cp1 [l2' [l2'' [H [l2_eq l2'''_eq]]]]].
injection l2'''_eq; clear l2'''_eq; intro l2'''_eq; rewrite <- H in l2_eq; clear H; subst l2;
inversion_clear In_pb' as [pb'_eq_ | ]; [idtac | contradiction].
subst; simpl unsolved_part; 
apply list_size_tl_compat; apply Nat.add_le_lt_mono; auto with arith.
apply ac_size_build_lt;
[ rewrite Af2 | apply (proj2 (A:=well_formed_cf (Var v1))); apply W1; left] ; trivial.
inversion_clear In_pb' as [pb'_eq_ | ]; [idtac | contradiction].
(* v1 has no value at all, neither plain nor partial *)
intros _; subst; simpl unsolved_part; simpl; auto with arith.

(* unsolved_part pb = (Term f1 l1, t2) :: _ *)
(* t2 is compatible or not with (Term f1 l1) *)
destruct t2 as [ v2 | f2 l2 ].
contradiction.
revert In_pb';  generalize (F.Symb.eq_bool_ok f1 f2); 
destruct (F.Symb.eq_bool f1 f2); [intros f1_eq_f2 In_pb'; subst f2 | contradiction].
destruct_arity f1 n1 Af1.
(* arity f1 = AC *)
destruct (le_gt_dec (length l1) (length l2)) as [_ | _]; [idtac | contradiction].
unfold ac_elementary_solve in In_pb'.
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
destruct (find X.eq_bool v1 (solved_part pb)) as [s1 | ].
(* l1 = t1 :: _, t1 is a variable v1  and v1 has a plain value s1 *)
intro W_s1; unfold ac_elementary_solve_term_var_with_val_term in *.
generalize (in_remove _ _ T.eq_bool_ok s1 l2);
destruct (remove T.eq_bool s1 l2) as [ l2''' |].
(* l1 = t1 :: _, t1 is a variable v1, v1 has a plain value s1 and s1 occurs in l2 *)
intros [cp1 [l2' [l2'' [ H [l2_eq l2'''_eq]]]]].
injection l2'''_eq; clear l2'''_eq; intro l2'''_eq; rewrite <- H in l2_eq; clear H; subst l2''';
inversion_clear In_pb' as [pb'_eq_ | ]; [idtac | contradiction].
generalize (W1 (Term f1 (Var v1 :: l1))  (Term f1 l2) (or_introl _ (eq_refl _)));
intros [Wt1 Wt2];  subst; unfold unsolved_part; 
apply list_size_tl_compat; apply Nat.add_lt_mono; 
[replace (Var v1 :: l1) with (nil ++ Var v1 :: l1); trivial;
replace (build f1 l1) with (build f1 (nil ++ l1)); trivial | 
idtac]; apply ac_size_build_lt; trivial.
(* l1 = t1 :: _, t1 is a variable v1, v1 has a plain value s1 and s1 does not occur in l2 *)
intros _; destruct s1 as [| g1 ll1].
contradiction.
revert In_pb'; 
generalize (F.Symb.eq_bool_ok f1 g1); case (F.Symb.eq_bool f1 g1); [intros f1_eq_g1 In_pb'; subst g1 | intros _; contradiction].
assert (S_ll1 := well_formed_cf_sorted Af1 W_s1). 
assert (S_l2 := well_formed_cf_sorted Af1 W_t2). 
generalize (in_remove_list S_ll1 S_l2); 
destruct (remove_list ll1 l2) as [l2' | ]; [idtac | contradiction ].
unfold DOS.A in *;
destruct (le_gt_dec (length l1) (length l2')) as [L_l1_l2' |]; [idtac | contradiction].
inversion_clear In_pb' as [pb'_eq_ | ]; [idtac | contradiction].
intro P; subst; simpl unsolved_part; 
apply list_size_tl_compat; apply Nat.add_lt_le_mono.
replace (Var v1 :: l1) with (nil ++ Var v1 :: l1); trivial;
replace (build f1 l1) with (build f1 (nil ++ l1)); trivial;
apply ac_size_build_lt; trivial.
rewrite ac_size_build_eq; trivial;
rewrite ac_size_unfold; rewrite Af1; apply Nat.add_le_mono.
generalize (list_permut.permut_length P); intro H;
unfold EDS.A, DOS.A in *; rewrite <- H; rewrite length_app;
destruct (length l2'); simpl; auto with arith;
rewrite Nat.add_comm; simpl; do 2 rewrite Nat.sub_0_r; auto with arith.
assert (Dummy : forall a a' : term,
  In a (ll1 ++ l2') -> In a' l2 -> a = a' -> ac_size a = ac_size a').
intros; subst; trivial.
generalize (list_permut.permut_size ac_size ac_size Dummy P); intro H;
unfold EDS.A, DOS.A in *; rewrite <- H; rewrite list_size_app; auto with arith.
intros _; generalize (W3 v1);
destruct (find X.eq_bool v1 (partly_solved_part pb)) as [p1 | ].
(* l1 = t1 :: _, t1 is a variable v1 and v1 has a partial value p1 *)
unfold ac_elementary_solve_term_var_with_part_val_term in *.
revert In_pb'; generalize (F.Symb.eq_bool_ok f1 (head_symb p1)); 
case (F.Symb.eq_bool f1 (head_symb p1)); [intros f1_eq_hd_p1 In_pb'| intros f1_diff_hd_p1 In_pb'].
(* l1 = t1 :: _, t1 is a variable v1, v1 has a partial value p1 and the head of p1 is f1 *)
generalize (in_remove _ _ T.eq_bool_ok (closed_term p1) l2);
destruct (remove T.eq_bool (closed_term p1) l2) as [l2''' | ]; [idtac | contradiction].
destruct In_pb' as [pb'_eq_ | ]; [idtac | contradiction].
intros [cp1 [l2' [l2'' [ H [l2_eq l2'''_eq]]]]].
injection l2'''_eq; clear l2'''_eq; intro l2'''_eq; rewrite <- H in l2_eq; clear H;
subst; simpl unsolved_part; rewrite Af1; intros.
apply list_size_tl_compat; apply Nat.add_le_lt_mono.
destruct l1 as [ | s1 l1]; [simpl; auto with arith | idtac].
do 2 rewrite ac_size_unfold; rewrite Af1; rewrite length_quicksort; 
simpl; apply le_n_S; apply Nat.add_le_mono_l.
assert (H'' := @list_permut.permut_size _ term (@eq term) ac_size ac_size (quicksort (Var (new_var p1) :: s1 :: l1))
  ((Var (new_var p1) :: s1 :: l1))).
unfold EDS.A, DOS.A in *; rewrite H''.
apply le_n.
intros; subst; trivial.
apply quick_permut_bis; reflexivity.
apply ac_size_build_lt; trivial.
(* l1 = t1 :: _, t1 is a variable v1, v1 has a partial value p1 and the head of p1 is NOT f1 *)
intros W3_v1; 
pattern pb';
refine 
(prop_map_without_repetition (B:=matching_problem) _ T.eq_bool_ok _ _ _ _ pb' In_pb');
clear pb' In_pb'; intros [ | g2 ll2] In_t2; trivial;
generalize (F.Symb.eq_bool_ok g2 (head_symb p1));
case (F.Symb.eq_bool g2 (head_symb p1)); [intros g2_eq_hd_p1 | intros g2_diff_hd_p1; trivial].
generalize (in_remove _ _ T.eq_bool_ok (closed_term p1) ll2);
destruct (remove T.eq_bool (closed_term p1) ll2) as [ll2''' | ]; trivial.
intros [cp1 [ll2' [ll2'' [ H [ll2_eq ll2'''_eq]]]]].
injection ll2'''_eq; clear ll2'''_eq; intro ll2'''_eq; subst cp1 ll2''';
generalize (in_remove _ _ T.eq_bool_ok (Term g2 ll2) l2);
destruct (remove T.eq_bool (Term g2 ll2) l2) as [l2''' | ]; trivial.
intros [cp1 [l2' [l2'' [ H [l2_eq l2'''_eq]]]]].
injection l2'''_eq; clear l2'''_eq; intro; subst l2''';
simpl unsolved_part; unfold list_size; rewrite Nat.add_assoc; apply Nat.add_lt_mono_r;
replace (ac_size (Var (new_var p1))) with (ac_size (Var v1)); trivial;
rewrite (Nat.add_comm (ac_size (Var v1))); rewrite <- Nat.add_assoc;
rewrite (Nat.add_assoc (ac_size (Var v1))); rewrite Nat.add_comm;
rewrite <- Nat.add_assoc; apply Nat.add_lt_mono.
rewrite Nat.add_comm; replace (build f1 l1) with (build f1 (nil ++ l1)); trivial;
replace (Var v1 :: l1) with (nil ++ Var v1 :: l1); trivial; 
apply ac_size_build_lt_args; trivial.
apply Nat.lt_trans with (ac_size (build f1 (l2' ++ l2'')) + ac_size (Term g2 ll2)).
apply Nat.add_lt_mono_l; subst; apply ac_size_build_lt.
destruct (arity (head_symb p1)); [trivial | contradiction | contradiction].
apply (well_formed_cf_subterms W_t2); trivial.
subst. apply ac_size_build_lt_args; trivial.
(* l1 = t1 :: _, t1 is a variable v1, v1 has no value, neither plain nor partial *)
intros _; unfold ac_elementary_solve_term_var_without_val_term in *.
pattern pb';
refine 
(prop_map12_without_repetition (B:=matching_problem) _ T.eq_bool_ok _ _ _ _ pb' In_pb');
clear pb' In_pb';
intros t2 In_t2; generalize (in_remove _ _ T.eq_bool_ok t2 l2);
destruct (remove T.eq_bool t2 l2) as [l2''' | ]; trivial; 
intros [cp1 [l2' [l2'' [ H [l2_eq l2'''_eq]]]]].
injection l2'''_eq; clear l2'''_eq; intro; subst l2''';
assert (Common_ineq : 
list_size
  (fun t1_t2 : term * term =>
   let (t1, t3) := t1_t2 in ac_size t1 + ac_size t3)
  (unsolved_part
     (mk_pb (existential_vars pb) ((build f1 l1, build f1 (l2' ++ l2'')) :: l)
        ((v1, t2) :: solved_part pb) (partly_solved_part pb))) <
list_size
  (fun t1_t2 : term * term =>
   let (t1, t3) := t1_t2 in ac_size t1 + ac_size t3)
  ((Term f1 (Var v1 :: l1), Term f1 l2) :: l)).
simpl unsolved_part; apply list_size_tl_compat; apply Nat.add_le_lt_mono.
simpl; rewrite Af1; rewrite Nat.sub_0_r; rewrite (list_size_fold ac_size);
rewrite ac_size_build_eq; trivial; apply Nat.add_le_mono; auto with arith; apply Nat.le_sub_l.
subst; apply ac_size_build_lt; trivial.
unfold EDS.A, DOS.A in *; destruct (le_gt_dec (length l2) (length l1 + 1)) as [_ | _]; trivial;
split; trivial; clear Common_ineq.
simpl unsolved_part; apply list_size_tl_compat; apply Nat.add_le_lt_mono.
destruct l1 as [| t1' l1]; [simpl; auto with arith | idtac];
simpl; rewrite Af1; rewrite length_quicksort; simpl;
do 2 rewrite (list_size_fold ac_size); simpl;
assert (H' := @list_permut.permut_size _ term (@eq term) ac_size ac_size (Var (fresh_var pb) :: t1' :: l1) 
(quicksort (Var (fresh_var pb) :: t1' :: l1))).
unfold EDS.A, DOS.A in *; rewrite <- H'.
simpl; apply le_n.
intros; subst; trivial.
apply quick_permut.
subst l2; apply ac_size_build_lt; trivial.
(* l1 = t1 :: _, t1 is a complex term (Term g1 ll1) *)
unfold ac_elementary_solve_term_term_term in *.
pattern pb';
refine 
(prop_map_without_repetition (B:=matching_problem) _ T.eq_bool_ok _ _ _ _ pb' In_pb');
clear pb' In_pb'; intros [ | g2 ll2] In_t2; trivial;
destruct (F.Symb.eq_bool g1 g2); trivial.
generalize (in_remove _ _ T.eq_bool_ok (Term g2 ll2) l2);
destruct (remove T.eq_bool (Term g2 ll2) l2) as [l2''' | ]; trivial.
intros [cp1 [l2' [l2'' [ H [l2_eq l2'''_eq]]]]].
injection l2'''_eq; clear l2'''_eq; intro; subst l2''';
simpl unsolved_part; unfold list_size; do 2 rewrite Nat.add_assoc; apply Nat.add_lt_mono_r.
rewrite <- Nat.add_assoc;
rewrite (Nat.add_comm (ac_size (Term g1 ll1))); rewrite <- Nat.add_assoc;
rewrite (Nat.add_assoc (ac_size (Term g1 ll1))); rewrite Nat.add_comm;
rewrite <- Nat.add_assoc; apply Nat.add_lt_mono.
rewrite Nat.add_comm; replace (build f1 l1) with (build f1 (nil ++ l1)); trivial;
replace (Term g1 ll1 :: l1) with (nil ++ Term g1 ll1 :: l1); trivial; 
apply ac_size_build_lt_args; trivial.
subst l2 cp1; apply ac_size_build_lt_args; trivial.

(* arity f1 = C *)
destruct l1 as [ | u1 [ | u2 [ | u3 l1]]]; [contradiction | contradiction | idtac | contradiction].
destruct l2 as [ | v1 [ | v2 [ | v3 l2]]]; [contradiction | contradiction | idtac | contradiction].
inversion_clear In_pb' as [pb'_eq_ | In_pb'']; 
[idtac | inversion_clear In_pb'' as [pb''_eq_ | ]; [idtac | contradiction]];
subst; simpl unsolved_part; simpl list_size;
rewrite Af1; do 2 rewrite Nat.add_assoc; apply Nat.add_lt_mono_r; do 2 rewrite Nat.add_0_r.
do 2 rewrite Nat.add_assoc; apply Nat.add_lt_mono_r;
simpl; unfold lt; apply le_n_S; do 3 rewrite <- Nat.add_assoc;
apply Nat.add_le_mono_l; rewrite Nat.add_comm; apply Nat.add_le_mono_l;
simpl; apply le_S; apply le_n.
simpl; unfold lt; apply le_n_S; do 3 rewrite <- Nat.add_assoc; apply Nat.add_le_mono_l;
rewrite Nat.add_comm;  rewrite <- Nat.add_assoc; apply Nat.add_le_mono_l;
apply le_S; apply le_n.

(* arity f1 = Free n1 *)
assert (L12 : length l1 = length l2).
apply trans_eq with n1; [idtac | apply sym_eq];
generalize (W1 (Term f1 l1) (Term f1 l2) (or_introl _ (eq_refl _)));
intros [[_ W_t1] [_ W_t2]]; [rewrite Af1 in W_t1 | rewrite Af1 in W_t2]; trivial.
generalize l l2 In_pb' L12; clear W1 W2 W3 l l2 In_pb' L12.
induction l1 as [ | t1 l1]; destruct l2 as [ | t2 l2].
intros [In_pb' | In_pb'] _; [idtac | contradiction];
subst pb'; simpl; rewrite Af1; rewrite <- plus_n_O; simpl; auto with arith.
intros _ L12; simpl in L12; discriminate.
intros _ L12; simpl in L12; discriminate.
intros In_pb' L12; simpl in L12; generalize (eq_add_S _ _ L12); clear L12; intro L12.
generalize (IHl1 _ _ In_pb' L12).
intro H; apply Nat.lt_le_trans with 
(list_size
  (fun t1_t2 : term * term =>
   let (t1, t2) := t1_t2 in ac_size t1 + ac_size t2)
  ((Term f1 l1, Term f1 l2) :: (t1, t2) :: l)); trivial.
simpl; rewrite Af1; do 2 rewrite (list_size_fold ac_size); simpl; apply le_n_S.
rewrite Nat.add_assoc; apply Nat.add_le_mono_r.
rewrite Nat.add_comm; do 2 rewrite <- Nat.add_assoc; apply Nat.add_le_mono_l.
rewrite Nat.add_comm; rewrite <- Nat.add_assoc; apply Nat.add_le_mono_l.
simpl; rewrite Nat.add_comm; trivial.

Qed.

End Make.

