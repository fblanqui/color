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
From CoLoR Require Import more_list list_sort term_spec ac cf_eq_ac matching_sound.

Module Type S.

Declare Module Import SMatching : matching_sound.S.
Import WFMMatching WFMatching Matching Cf_eq_ac Ac EqTh T.

(* Parameter remove_a_subterm
Parameter remove_several_subterms
Parameter remove_several_subterms_bis
Parameter remove_several_subterms_bis_nil *)
Parameter solve_is_complete :
  forall pb, well_formed_pb pb -> forall sigma, is_well_formed_sol pb sigma ->
  match pb.(unsolved_part) with
  | nil => True
    | _ :: _ => exists pb', In pb' (solve pb) /\ is_well_formed_sol pb' sigma
  end.

End S.

Module Make (SMatching1 : matching_sound.S) :
 S with Module SMatching := SMatching1.
Module SMatching := SMatching1.

Import SMatching1 WFMMatching WFMatching Matching Cf_eq_ac Ac EqTh T F X Sort LPermut.

Lemma remove_a_subterm :
  forall sigma f v l1 t l2, arity f = AC -> well_formed_cf_subst sigma ->
  well_formed_cf (Term f (Var v :: l1)) ->
  well_formed_cf (Term f l2)  ->
  apply_cf_subst sigma (Var v) = t ->
  apply_cf_subst sigma (Term f (Var v :: l1)) = Term f l2 ->
  match remove T.eq_bool t l2 with 
  | None => 
        match t with
        | Var _ => False
        | Term g _ => f=g
        end
  | Some rmv =>  apply_cf_subst sigma (build f l1) = build f rmv
  end.
Proof.
intros sigma f v l1 t l2 Ar W_sigma Wt1 Wt2 v_sigma t1_sigma.
generalize (in_remove _ _ T.eq_bool_ok t l2);
destruct (remove T.eq_bool t l2) as [l2''' | ].
intros [cp1 [l2' [l2'' [ H'' [l2_eq l2'''_eq]]]]]; subst cp1.
injection l2'''_eq; clear l2'''_eq; intro; subst l2 l2''';
apply flatten_cf with f; trivial.
apply well_formed_cf_apply_subst; trivial;
apply well_formed_cf_build_cons with (Var v); trivial.
apply well_formed_cf_build_inside with t; trivial.
rewrite <- (flatten_apply_cf_subst sigma l1 Ar);
rewrite (flatten_build (l2' ++ l2'') Ar).
simpl in t1_sigma; rewrite Ar in t1_sigma;
simpl in v_sigma; rewrite v_sigma in t1_sigma.
injection t1_sigma; clear t1_sigma; intro t1_sigma.
destruct t as [ x | g ll].
rewrite (@permut_cons_inside (Var x) (Var x)) by reflexivity.
(* dummy rewrite <- t1_sigma ne marche pas *)
(* avec depliage, ca marche unfold EDS.A, TO.A; rewrite <- t1_sigma. *)
setoid_rewrite <- t1_sigma.
apply permut_sym; apply quick_permut_bis; reflexivity.
revert t1_sigma; generalize (F.Symb.eq_bool_ok f g); case (F.Symb.eq_bool f g); [intro f_eq_g | intros _].
absurd (f=g); trivial.
apply (well_formed_cf_alien Ar Wt2 (Term g ll)).
apply in_or_app; right; left; trivial.
intro t1_sigma;
rewrite (@permut_cons_inside (Term g ll) (Term g ll)) by reflexivity.
setoid_rewrite <- t1_sigma.
apply permut_sym; apply quick_permut_bis; reflexivity.
intros s s_in_l2'_l2''; 
destruct (in_app_or _ _ _ s_in_l2'_l2'') as [s_in_l2' | s_in_l2''];
apply (well_formed_cf_alien Ar Wt2); apply in_or_app; [left | right; right]; trivial.
intros t_not_in_l2; 
simpl in t1_sigma; rewrite Ar in t1_sigma;
simpl in v_sigma; rewrite v_sigma in t1_sigma;
inversion t1_sigma.
destruct t as [x | g ll].
apply t_not_in_l2; subst l2.
rewrite <- (mem_permut_mem (Var x)  (quick_permut (Var x :: flatten f (map (apply_cf_subst sigma) l1)))); left; trivial.
reflexivity.
revert H0; generalize (F.Symb.eq_bool_ok f g); case (F.Symb.eq_bool f g); [intros f_eq_g _; assumption | intros f_diff_g].
intro H; apply False_rect; apply t_not_in_l2; subst l2.
rewrite <- (mem_permut_mem (Term g ll) (quick_permut (Term g ll :: flatten f (map (apply_cf_subst sigma) l1)))).
left; reflexivity.
Qed.

Lemma remove_several_subterms :
  forall sigma f v l1 t l2, arity f = AC -> well_formed_cf_subst sigma ->
  well_formed_cf (Term f (Var v :: l1)) ->
  well_formed_cf (Term f l2) ->
  apply_cf_subst sigma (Var v) = t ->
  apply_cf_subst sigma (Term f (Var v :: l1)) = Term f l2 ->
  match t with
  | Var _ => True
  | Term g l0 => 
     if F.Symb.eq_bool f g
     then
       match remove_list l0 l2 with
       | None => False
       | Some l3 =>  
         if le_gt_dec (length l1) (length l3)
         then apply_cf_subst sigma (build f l1) = build f l3
         else False
       end
     else True
  end.
Proof.
intros sigma f v l1 t l2 Ar W_sigma Wt1 Wt2 v_sigma t1_sigma;
destruct t as [ x | g ll]; trivial.
generalize (F.Symb.eq_bool_ok f g); case (F.Symb.eq_bool f g); [intro f_eq_g; subst g | intros _; trivial].
assert (W_v : well_formed_cf (Var v)). simpl; trivial.
assert (W_v_sigma := well_formed_cf_apply_subst W_sigma _ W_v);
rewrite v_sigma in W_v_sigma.
generalize (in_remove_list (well_formed_cf_sorted Ar W_v_sigma)
                    (well_formed_cf_sorted Ar Wt2)).
destruct (remove_list ll l2) as [l2' | ].
intro P; elim (le_gt_dec (length l1) (length l2')); intro L.
assert (Al_l2' : forall t, In t l2' -> match t with Var _ => True | Term g _ => f <> g end).
intros t In_t; apply (well_formed_cf_alien Ar Wt2).
rewrite <- (list_permut.in_permut_in P).
apply in_or_app; right; trivial.
apply flatten_cf with f; trivial.
apply well_formed_cf_apply_subst; trivial; 
apply well_formed_cf_build_cons with (Var v); trivial.
apply well_formed_cf_build; trivial.
apply Nat.le_trans with (length l1); trivial.
apply le_S_n; generalize (well_formed_cf_length Ar Wt1); trivial.
intros t In_t; apply (well_formed_cf_subterms Wt2).
rewrite <- (list_permut.in_permut_in P);
apply in_or_app; right; trivial.
rewrite <- (flatten_apply_cf_subst sigma l1 Ar);
rewrite (flatten_build l2' Ar Al_l2').
rewrite (permut_app1 ll).
transitivity l2.
simpl in t1_sigma; rewrite Ar in t1_sigma.
inversion_clear t1_sigma.
simpl in v_sigma; rewrite v_sigma.
generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); [intros _ | intro f_diff_f; apply False_rect; apply f_diff_f; reflexivity].
apply quick_permut.
symmetry; trivial.
generalize (proj1 (Nat.add_lt_mono_l _ _ (length ll)) L).
rewrite <- length_app; assert (L' := list_permut.permut_length P).
setoid_rewrite L'; clear L'.
simpl in t1_sigma; rewrite Ar in t1_sigma.
inversion_clear t1_sigma; rewrite length_quicksort; 
simpl in v_sigma; rewrite v_sigma;
generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); [intros _ | intro f_diff_f; apply False_rect; apply f_diff_f; reflexivity].
rewrite length_app; intro L';
assert (L'' := (proj2 (Nat.add_lt_mono_l _ _ (length ll)) L')); clear L L'.
absurd (length l1 < length l1); auto with arith.
refine (Nat.le_lt_trans _ _ _ _ L'').
rewrite <- (length_map (apply_cf_subst sigma)).
apply length_flatten_bis; trivial.
intros t' t'_in_map_l1; rewrite in_map_iff in t'_in_map_l1;
destruct t'_in_map_l1 as [t [Wt t_sigma]].
subst; apply well_formed_cf_apply_subst; trivial.
apply (well_formed_cf_subterms Wt1); right; trivial.
intro P; apply (P (flatten f (map (apply_cf_subst sigma) l1)));
simpl in v_sigma; simpl in t1_sigma;
rewrite Ar in t1_sigma; rewrite v_sigma in t1_sigma;
inversion_clear t1_sigma.
simpl; trivial;
generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); [intros _ | intro f_diff_f; apply False_rect; apply f_diff_f; reflexivity].
apply quick_permut; auto.
Qed.

Lemma remove_several_subterms_bis :
  forall sigma f v v' l1 t l2, arity f = AC -> well_formed_cf_subst sigma ->
  well_formed_cf (Term f (Var v :: l1)) ->
  well_formed_cf (Term f l2) ->
  apply_cf_subst sigma (Var v) = 
     Term f (quicksort (flatten f (apply_cf_subst sigma (Var v') :: t :: nil))) ->
  apply_cf_subst sigma (Term f (Var v :: l1)) = Term f l2 ->
  match t with  | Var _ => True  | Term g _ => f<>g end ->
  match remove T.eq_bool t l2 with
  | None => False
  | Some l3 => apply_cf_subst sigma  (build f (Var v' :: l1)) = build f l3
  end.
Proof.
intros sigma f v v' l1 t l2 Ar W_sigma Wt1 Wt2 v_sigma t1_sigma.
generalize (in_remove _ _ T.eq_bool_ok t l2);
destruct (remove T.eq_bool t l2) as [l2''' | ].
intros [cp1' [l2' [l2'' [ H'' [l2_eq l2'''_eq]]]]] Al_t.
injection l2'''_eq; clear l2'''_eq; intro l2'''_eq;
apply flatten_cf with f; trivial.
apply well_formed_cf_apply_subst; trivial; apply well_formed_cf_build; trivial.
simpl; auto with arith.
intros s [s_eq_v' | s_in_l1]; [subst; simpl | apply (well_formed_cf_subterms Wt1); right]; trivial.
intros s [s_eq_v' | s_in_l1]; [subst; simpl | apply (well_formed_cf_alien Ar Wt1); right]; trivial.
subst l2 l2'''; apply well_formed_cf_build_inside with t; subst; trivial.

rewrite <- (flatten_apply_cf_subst sigma (Var v' :: l1) Ar);
rewrite (flatten_build l2''' Ar); subst l2 l2''' cp1'.
rewrite (@permut_cons_inside t t) by reflexivity.
pattern (Var v :: l1) in t1_sigma; simpl in t1_sigma; rewrite Ar in t1_sigma.
pattern (Var v') in v_sigma; unfold apply_cf_subst in v_sigma.
rewrite v_sigma in t1_sigma; clear v_sigma.
revert t1_sigma; generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); [intros _ t1_sigma | intro f_diff_f; apply False_rect; apply f_diff_f; reflexivity].
assert (Inj : forall l' l'', Term f l' = Term f l'' -> l' = l'').
intros l' l'' H'; injection H'; intros; subst; trivial.
setoid_rewrite <- (Inj _ _ t1_sigma); clear Inj.
apply permut_sym; apply quick_permut_bis.
transitivity
  (flatten f (apply_cf_subst sigma (Var v')  :: t :: nil) ++
   flatten f (map (apply_cf_subst sigma) l1)).
rewrite <- permut_app2; apply quick_permut_bis; auto.
replace (flatten f (map (apply_cf_subst sigma) (Var v' :: l1))) with
((flatten f (apply_cf_subst sigma (Var v') :: nil)) ++ 
        flatten f (map (apply_cf_subst sigma) l1));
[ rewrite app_comm_cons | rewrite <- flatten_app; trivial].
rewrite <- permut_app2.
replace (flatten f (apply_cf_subst sigma (Var v') :: t :: nil)) with
((flatten f (apply_cf_subst sigma (Var v') :: nil) ++ flatten f (t :: nil)));
[idtac | rewrite <- flatten_app; simpl app; trivial]. 
replace (flatten f (t :: nil)) with (t :: nil).
apply permut_sym; rewrite <- permut_cons_inside.
rewrite <- app_nil_end; auto.
reflexivity.
simpl; destruct t as [x | g ll]; trivial.
generalize (F.Symb.eq_bool_ok f g); case (F.Symb.eq_bool f g); [intro f_eq_g; absurd (f = g); trivial | intros _; trivial].
intros s s_in_l2'_l2''; 
destruct (in_app_or _ _ _ s_in_l2'_l2'') as [s_in_l2' | s_in_l2''];
apply (well_formed_cf_alien Ar Wt2); apply in_or_app; [left | right; right]; trivial.

intros Not_in Al_t;
pattern (Var v :: l1) in t1_sigma; simpl in t1_sigma; rewrite Ar in t1_sigma.
pattern (Var v') in v_sigma;
unfold apply_cf_subst in v_sigma.
rewrite v_sigma in t1_sigma; clear v_sigma.
revert t1_sigma; generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); [intros _ t1_sigma | intro f_diff_f; apply False_rect; apply f_diff_f; reflexivity].
assert (Inj : forall l' l'', Term f l' = Term f l'' -> l' = l'').
intros l' l'' H'; injection H'; intros; subst; trivial.
rewrite <- (Inj _ _ t1_sigma) in Not_in; clear Inj.
apply Not_in.
apply in_impl_mem.
reflexivity.
rewrite <- in_quick_in.
apply in_or_app; left.
rewrite <- in_quick_in.
replace (flatten f (match find eq_var_bool v' sigma with
         | Some v_sigma => v_sigma
         | None => Var v'
         end :: t :: nil)) with
(flatten f (apply_cf_subst sigma (Var v')  :: nil) ++ flatten f (t :: nil)).
apply in_or_app; right; destruct t as [x | g ll]; simpl.
left; trivial.
generalize (F.Symb.eq_bool_ok f g); case (F.Symb.eq_bool f g); [intro f_eq_g; absurd (f = g); trivial | intros _; left; trivial].
rewrite <- flatten_app; simpl app; trivial.
Qed.

Lemma remove_several_subterms_bis_nil :
  forall sigma f v v' t l2, arity f = AC -> well_formed_cf_subst sigma ->
  well_formed_cf (Term f l2) ->
  apply_cf_subst sigma (Var v) = 
     Term f (quicksort (flatten f (apply_cf_subst sigma (Var v') :: t :: nil))) ->
  apply_cf_subst sigma (Var v) = Term f l2 ->
  match t with  | Var _ => True  | Term g _ => f<>g end ->
  match remove T.eq_bool t l2 with
  | None => False
  | Some l3 => apply_cf_subst sigma (Var v') = build f l3
  end.
Proof.
intros sigma f v v' t l2 Ar W_sigma Wt2 v_sigma t1_sigma Al_t;
generalize (in_remove _ _ T.eq_bool_ok t l2);
destruct (remove T.eq_bool t l2) as [l2''' | ].
intros [cp1 [l2' [l2'' [ H' [l2_eq l2'''_eq]]]]].
injection l2'''_eq; clear l2'''_eq; intro l2'''_eq;
subst l2 l2'''; apply flatten_cf with f; trivial.
apply well_formed_cf_apply_subst; trivial; simpl; trivial.
apply well_formed_cf_build_inside with t; subst; trivial.
apply permut_trans with (l2' ++ l2'').
rewrite (@permut_cons t t).
apply permut_trans with (l2' ++ t :: l2'').
assert (H:= trans_eq (sym_eq v_sigma) t1_sigma).
assert (Inj : forall l' l'', Term f l' = Term f l'' -> l' = l'').
intros l' l'' H''; injection H''; intros; subst; trivial.
subst cp1; rewrite <- (Inj _ _ H); clear Inj.
apply permut_sym; apply quick_permut_bis.
apply permut_trans with 
(flatten f (apply_cf_subst sigma (Var v') :: nil) ++ flatten f (t :: nil)).
rewrite <- flatten_app; simpl app; apply permut_refl.
refine (permut_trans (list_permut_app_app _ _) _).
simpl; destruct t as [ x | g ll ]; [apply permut_refl | idtac].
generalize (F.Symb.eq_bool_ok f g); case (F.Symb.eq_bool f g); [intro f_eq_g; absurd (f = g); trivial | intros _; reflexivity].
apply permut_sym; rewrite <- permut_cons_inside; reflexivity.
reflexivity.
apply permut_sym; apply flatten_build_inside with t; subst cp1; trivial.

intros Not_in; apply Not_in.
assert (H := trans_eq (sym_eq v_sigma) t1_sigma).
assert (Inj : forall l' l'', Term f l' = Term f l'' -> l' = l'').
intros l' l'' H'; injection H'; intros; subst; trivial.
rewrite <- (Inj _ _ H); clear Inj.
apply in_impl_mem.
reflexivity.
rewrite <- in_quick_in.
assert (H':= flatten_app f (apply_cf_subst sigma (Var v') :: nil) (t :: nil)).
simpl in H'; simpl; rewrite  H'; apply in_or_app; right.
destruct t as [ x | g ll ]; simpl; [left; trivial | idtac].
generalize (F.Symb.eq_bool_ok f g); case (F.Symb.eq_bool f g); [intro f_eq_g; absurd (f = g); trivial | intros _; left; reflexivity].
Qed.

Lemma solve_is_complete :
  forall pb, well_formed_pb pb -> forall sigma, is_well_formed_sol pb sigma ->
  match pb.(unsolved_part) with
  | nil => True
    | _ :: _ => exists pb', In pb' (solve pb) /\ is_well_formed_sol pb' sigma
  end.
Proof.
intros pb W sigma' [sigma [S [S' W_sigma]]].
case_eq pb; intros ex [ | [t1 t2] unsolved_p] solved_p partly_solved_p Pb; simpl; trivial.
assert (R' : forall t:term, is_rough_sol pb (((fresh_var pb), t) :: sigma)).
intro t; apply add_new_var_to_rough_sol; trivial.
assert (Fresh_var := fresh_var_spec pb).
rewrite Pb in S'.
rewrite Pb in W; destruct W as [W1_pb [W2_pb [W3_pb [W4_pb [W5_pb W6_pb]]]]].
rewrite Pb in S; destruct S as [S1 [S2 S3]].
destruct (W1_pb t1 t2 (or_introl _ (eq_refl _))) as [Wt1 Wt2].
assert (t1_sigma := S1 t1 t2 (or_introl _ (eq_refl _))).
simpl unsolved_part in *; simpl solved_part in *; simpl partly_solved_part in *; simpl existential_vars in *.
unfold solve; simpl; destruct t1 as [v | f1 l1].
(* 1/2 t1 is a variable v *)
case_eq (find X.eq_bool v solved_p); [intros x_val F | intros F].
(* 1/3 t1 = v has a (complete) value *)
generalize (T.eq_bool_ok x_val t2); case (T.eq_bool x_val t2); [intro x_val_eq_t2 | intro x_val_diff_t2].

subst x_val; exists (mk_pb ex unsolved_p solved_p partly_solved_p); split.
left; trivial.
exists sigma; repeat split; trivial.
simpl; intros a b ab_in_unsolved_p; apply S1; right; trivial.
absurd (x_val = t2); trivial.
generalize (S3 v); simpl; rewrite F; simpl in t1_sigma; rewrite t1_sigma.
intro; apply sym_eq; trivial.

(* 1/2 t1 = v has no complete value *)
case_eq (find X.eq_bool v partly_solved_p); [intros pst F'| intros F'].
(* 1/3 t1 =v has no complete value, but has a partial value *)
assert (E := S2 v).
simpl partly_solved_part in E; rewrite F' in E; rewrite t1_sigma in E; rewrite E.
generalize (F.Symb.eq_bool_ok (head_symb pst) (head_symb pst));
case (F.Symb.eq_bool (head_symb pst) (head_symb pst)); [intros _ | intros h_diff_h; apply False_rect; apply h_diff_h; reflexivity]. 
generalize (W3_pb v); simpl partly_solved_part; rewrite F'.
destruct_arity (head_symb pst) n Af2; [intros [Wct Act] | contradiction | contradiction].
rewrite E in Wt2; rewrite <- t1_sigma in E.
assert (H := remove_several_subterms_bis_nil _ _ v (new_var pst) (closed_term pst) _ 
                     Af2 W_sigma Wt2 E E Act).
destruct (remove T.eq_bool (closed_term pst) 
                     (quicksort (flatten (head_symb pst)
                                        (apply_cf_subst sigma (Var (new_var pst))
                                        :: closed_term pst :: nil)))) as [l2' | ].

exists (mk_pb ex ((Var (new_var pst), build (head_symb pst) l2') :: unsolved_p) solved_p partly_solved_p);
split.
left; trivial.
exists sigma; repeat split; trivial.
simpl; intros t1 t3 [In_t1t3 | In_t1t3].
injection In_t1t3; intros; subst t1 t3; trivial.
apply S1; right; trivial.
contradiction.

(* 1/2 t1 = v has no complete value, nor a partial value *)
exists (mk_pb ex unsolved_p ((v, t2) :: solved_p) partly_solved_p); split.
left; trivial.
exists sigma; repeat split; trivial.
simpl; intros t1 t3 In_t1t3; apply S1; right; trivial.
simpl; intro v0; generalize (X.eq_bool_ok v0 v); case (X.eq_bool v0 v); [intro v0_eq_v | intro v0_diff_v].
subst v0; trivial.
apply (S3 v0).

(* 1/1 t1 = f1(l1) *)
destruct t2 as [v' | f2 l2]; [inversion t1_sigma | idtac].
generalize (F.Symb.eq_bool_ok f1 f2); case (F.Symb.eq_bool f1 f2); [intro f1_eq_f2 | intros; absurd (f1 =f2); trivial; inversion t1_sigma; trivial].
(* 1/1 t1 = f1(l1), t2 = f1(l2) *)
subst f2; destruct_arity f1 n1 Af1.
(* 1/3 f1 is AC *)
destruct (le_gt_dec (length l1) (length l2)) as [Ll2 | Ll2].
(* 1/4 length l1 <= length l2 *)
unfold ac_elementary_solve; destruct l1 as [ | t l1].
absurd (2<=0); auto with arith; apply (well_formed_cf_length Af1 Wt1).

destruct t as [v | f k].
(* 1/5 t1 = f1(v,l1), t2 = f1(l2) *)
case_eq (find X.eq_bool v solved_p); [intros pst F | intros F].
assert (v_sigma := S3 v).
simpl solved_part; simpl solved_part in v_sigma; rewrite F in v_sigma.
(* 1/6 v has a complete value *)
assert (t_sigma := remove_a_subterm _ _ _ _ _ _ Af1 W_sigma Wt1 Wt2 v_sigma t1_sigma).
unfold ac_elementary_solve_term_var_with_val_term; rewrite F.
case_eq (remove T.eq_bool pst l2); [intros l2' H | intros H]; rewrite H in t_sigma.
simpl; exists (mk_pb ex ((build f1 l1, build f1 l2') :: unsolved_p) solved_p partly_solved_p); split.
left; trivial.
exists sigma; repeat split; trivial.
intros t1 t2 [In_t1t2 | In_t1t2]; [injection In_t1t2; intros; subst t1 t2 | apply S1; right]; trivial.

destruct pst as [v' | f k]; [contradiction | subst f].
assert (t_sigma := remove_several_subterms _ _ _ _ _ _ Af1 W_sigma Wt1 Wt2 v_sigma t1_sigma).
simpl in t_sigma; revert t_sigma;
generalize (F.Symb.eq_bool_ok f1 f1); case (F.Symb.eq_bool f1 f1); [intros _ | intro f1_diff_f1; apply False_rect; apply f1_diff_f1; reflexivity].
destruct (remove_list k l2) as [k2' | ]; [idtac | contradiction].
unfold TO.A in *;
destruct (le_gt_dec (length l1) (length k2')) as [Lk2' | Lk2']; [idtac | contradiction].

simpl; exists (mk_pb ex ((build f1 l1, build f1 k2') :: unsolved_p) solved_p partly_solved_p); split.
left; trivial.
exists sigma; repeat split; trivial.
intros t1 t2 [In_t1t2 | In_t1t2]; [injection In_t1t2; intros; subst | apply S1; right]; trivial.

(* 1/5 v has no complete value *)
simpl; rewrite F.
assert (v_sigma := S2 v).
cbv zeta in v_sigma.
assert (W3_v := W3_pb v).
case_eq (find X.eq_bool v partly_solved_p); [intros pst F' | intros F']; 
rewrite F' in v_sigma; rewrite F' in W3_v.
(* 1/6 v has no complete value, but has a partial value *)
destruct_arity (head_symb pst) n Ahsp; [idtac | contradiction | contradiction].
unfold ac_elementary_solve_term_var_with_part_val_term.
destruct W3_v as [Wct Act].
generalize (F.Symb.eq_bool_ok f1 (head_symb pst));
case (F.Symb.eq_bool f1 (head_symb pst)); [intro f1_eq_hd_pst | intro f1_diff_hd_pst].
rewrite <- f1_eq_hd_pst in *.

assert (t_sigma := remove_several_subterms_bis _ _ _ _ _ _ _ Af1 W_sigma Wt1 Wt2 v_sigma t1_sigma Act). 
destruct (remove T.eq_bool (closed_term pst) l2) as [ l2' | ]; [idtac | contradiction].

exists (mk_pb ex ((build f1 (Var (new_var pst) :: l1), build f1 l2') :: unsolved_p) solved_p partly_solved_p); split.
left; trivial.
exists sigma; repeat split; trivial.
simpl; intros t1 t2 [In_t1t2 | In_t1t2]; [injection In_t1t2; intros; subst t1 t2 | apply S1; right]; trivial.

refine (exists_map_without_repetition _ T.eq_bool_ok _ _ _ _).
assert (v_sigma_in_l2 : In (apply_cf_subst sigma (Var v)) l2).
rewrite v_sigma; simpl apply_cf_subst in v_sigma; simpl apply_cf_subst in t1_sigma; 
rewrite Af1 in t1_sigma; rewrite v_sigma in t1_sigma.
revert t1_sigma; generalize (F.Symb.eq_bool_ok f1 (head_symb pst));
case (F.Symb.eq_bool f1 (head_symb pst)); [intros f1_eq_hd_pst | intros _ t1_sigma].
absurd (f1 = head_symb pst); trivial.
injection t1_sigma; clear t1_sigma; intro l1_sigma; subst l2.
rewrite <- in_quick_in; left; trivial.
exists (apply_cf_subst sigma (Var v)); split; trivial.
assert (Wv : well_formed_cf (Var v)).
simpl; trivial.
assert (W := well_formed_cf_apply_subst W_sigma (Var v) Wv).
clear Wv; rewrite v_sigma; rewrite v_sigma in W;
generalize (F.Symb.eq_bool_ok (head_symb pst) (head_symb pst));
case (F.Symb.eq_bool (head_symb pst) (head_symb pst)); [intros _ | intros h_diff_h; apply False_rect; apply h_diff_h; reflexivity]. 
assert (v'_sigma := remove_several_subterms_bis_nil _ _ _ _ _ _ Ahsp W_sigma W v_sigma v_sigma Act).
assert (t_sigma := remove_a_subterm _ _ _ _ _ _ Af1 W_sigma Wt1 Wt2 (eq_refl _) t1_sigma).
destruct (remove T.eq_bool (closed_term pst)
      (quicksort
         (flatten (head_symb pst)
            (apply_cf_subst sigma (Var (new_var pst))
             :: closed_term pst :: nil)))) as [k2 | ]; [idtac | contradiction].
rewrite <- v_sigma; destruct (remove T.eq_bool (apply_cf_subst sigma (Var v)) l2) as [l2' | ].
exists sigma; repeat split; trivial.
simpl.
intros t1 t2 [In_t1t2 | [In_t1t2 | In_t1t2]]; 
[injection In_t1t2; intros; subst t1 t2 | injection In_t1t2; intros; subst t1 t2 | apply S1; right]; trivial.
rewrite v_sigma in t_sigma; apply f1_diff_hd_pst; trivial.

(* 1/5 v has no complete value, nor a partial value *)
clear v_sigma; clear W3_v.
unfold ac_elementary_solve_term_var_without_val_term.
refine (exists_map12_without_repetition _ T.eq_bool_ok _ _ _ _).
assert (t_sigma := remove_a_subterm sigma _ _ _ _ _ Af1 W_sigma Wt1 Wt2 (eq_refl _) t1_sigma).
case_eq (apply_cf_subst sigma (Var v)); [intros v' v_sigma | intros f k v_sigma]; rewrite v_sigma in t_sigma.
(* 1/6 the actual value of v is a variable *)
exists (Var v').
assert (H := in_remove _ _ T.eq_bool_ok (Var v') l2).
case_eq (remove T.eq_bool (Var v') l2); [intros l2' H' | intros H']; 
rewrite H' in t_sigma; [rewrite H' in H; split | contradiction].
destruct H as [t [l' [l'' [v_sigma_eq_t [l2_eq H]]]]]; subst; apply in_or_app; right; left; trivial.
unfold TO.A in *; destruct (le_gt_dec (length l2) (length l1 + 1)) as [Ll2' | Ll2'].
exists sigma; repeat split; trivial.
simpl; intros t1 t2 [In_t1t2 | In_t1t2]; [injection In_t1t2; intros; subst t1 t2 | apply S1; right]; trivial.
simpl; intro v0; generalize (X.eq_bool_ok v0 v); case (X.eq_bool v0 v); [intro v0_eq_v | intro v0_diff_v].
subst v0; trivial.
apply S3.
left; exists sigma; repeat split; trivial.
simpl; intros t1 t2 [In_t1t2 | In_t1t2]; [injection In_t1t2; intros; subst t1 t2 | apply S1; right]; trivial.
simpl; intro v0; generalize (X.eq_bool_ok v0 v); case (X.eq_bool v0 v); [intro v0_eq_v | intro v0_diff_v].
subst v0; trivial.
apply S3.
(* 1/5 the actual value of v is a composite term f(k) *)
assert (H := in_remove _ _ T.eq_bool_ok (Term f k) l2).
case_eq (remove T.eq_bool (Term f k) l2); [intros l2' H' | intros H']; rewrite H' in *.
(* 1/6 the actual value of v is f(k), where f <> f1, and f(k) is in l2 *)
exists (Term f k); split.
destruct H as [t [l' [l'' [v_sigma_eq_t [l2_eq H]]]]]; subst; apply in_or_app; right; left; trivial.
rewrite H'; unfold TO.A in *; destruct (le_gt_dec (length l2) (length l1 + 1)) as [Ll2' | Ll2'].
exists sigma; repeat split; trivial.
simpl; intros t1 t2 [In_t1t2 | In_t1t2]; [injection In_t1t2; intros; subst t1 t2 | apply S1; right]; trivial.
simpl; intro v0; generalize (X.eq_bool_ok v0 v); case (X.eq_bool v0 v); [intro v0_eq_v | intro v0_diff_v].
subst v0; trivial.
apply S3.
left; exists sigma; repeat split; trivial.
simpl; intros t1 t2 [In_t1t2 | In_t1t2]; [injection In_t1t2; intros; subst t1 t2 | apply S1; right]; trivial.
simpl; intro v0; generalize (X.eq_bool_ok v0 v); case (X.eq_bool v0 v); [intro v0_eq_v | intro v0_diff_v].
subst v0; trivial.
apply S3.

(* 1/5 the actual value of v is f(k), where f = f1, and f(k) is NOT in l2, but a subterm a of k is *)
subst f; assert (W_fk : well_formed_cf (Term f1 k)).
rewrite <- v_sigma; generalize (W_sigma v); simpl.
destruct (find X.eq_bool v sigma); simpl; trivial.

destruct k as [ | a k]; simpl in W_fk; rewrite Af1 in W_fk.
destruct W_fk as [_ [W_fk _]]; inversion W_fk.
assert (a_in_l2 : In a l2).
simpl in t1_sigma; rewrite Af1 in t1_sigma; simpl in v_sigma; rewrite v_sigma in t1_sigma.
revert t1_sigma;
generalize (F.Symb.eq_bool_ok f1 f1); case (F.Symb.eq_bool f1 f1); [intros _ t1_sigma | intro f1_diff_f1; apply False_rect; apply f1_diff_f1; reflexivity].
injection t1_sigma; intros; subst l2;rewrite <- in_quick_in; left; trivial.
assert (W_sigma' : well_formed_cf_subst (((fresh_var pb), (build f1 k)) :: sigma)).
unfold well_formed_cf_subst; simpl; intros v0; 
generalize (X.eq_bool_ok v0 (fresh_var pb)); case (X.eq_bool v0 (fresh_var pb)); [intro v0_eq_fv | intro v0_diff_fv].
apply well_formed_cf_build_cons with a; simpl; trivial; rewrite Af1; trivial.
apply (W_sigma v0).
assert (v_sigma' : apply_cf_subst (((fresh_var pb), (build f1 k)) :: sigma) (Var v) =
 Term f1
   (quicksort
      (flatten f1
         (apply_cf_subst (((fresh_var pb), (build f1 k)) :: sigma)
            (Var (fresh_var pb)) :: a :: nil)))).
simpl apply_cf_subst.
generalize (X.eq_bool_ok (fresh_var pb) (fresh_var pb)); case (X.eq_bool (fresh_var pb) (fresh_var pb)); 
[intros _ | intro fv_diff_fv; apply False_rect; apply fv_diff_fv; reflexivity].
generalize (X.eq_bool_ok v (fresh_var pb)); case (X.eq_bool v (fresh_var pb)); [intro v_eq_fv | intros _].
absurd (v = fresh_var pb); trivial.
intros _; apply Fresh_var; rewrite <- v_eq_fv; subst pb; 
unfold occurs_in_pb; simpl; do 3 left; trivial.
simpl in v_sigma; rewrite v_sigma.
apply (f_equal (fun l => Term f1 l)).
apply sort_is_unique.
destruct W_fk as [_ [_ [W_fk _]]]; trivial.
apply quick_sorted.
apply permut_sym; apply quick_permut_bis.
replace (flatten f1 (build f1 k :: a :: nil)) with (flatten f1 (build f1 k :: nil) ++ flatten f1 (a :: nil));
[idtac | rewrite <- flatten_app; simpl app; trivial].
refine (permut_trans (list_permut_app_app _ _) _).
apply permut_trans with (a :: flatten f1 (build f1 k :: nil)).
simpl; destruct a as [ | g ll]; [apply permut_refl | idtac].
generalize (F.Symb.eq_bool_ok f1 g); case (F.Symb.eq_bool f1 g);  [intro f1_eq_g | reflexivity].
absurd (f1=g); trivial.
destruct W_fk as [_ [_ [_ W_fk]]]; apply (W_fk (Term g ll)); left; trivial.
rewrite <- permut_cons.
apply flatten_build_cons with a; simpl; trivial; rewrite Af1; trivial.
reflexivity.
assert (t1_sigma' : apply_cf_subst (((fresh_var pb), (build f1 k)) :: sigma) (Term f1 (Var v :: l1)) = Term f1 l2).
rewrite <- add_new_var_to_subst; trivial.
intro fv_in_t1; apply Fresh_var; rewrite Pb; unfold occurs_in_pb;
simpl unsolved_part; rewrite <- Pb; do 2 left; trivial.
assert (Aa : match a with
        | Var _ => True
        | Term g _ => f1 <> g
        end).
destruct W_fk as [_ [_ [_ W_fk]]]; apply W_fk; left; trivial.
assert (H1 := remove_several_subterms_bis
         (((fresh_var pb), (build f1 k)) :: sigma) f1 v (fresh_var pb) l1
          a l2 Af1 W_sigma' Wt1 Wt2 v_sigma' t1_sigma' Aa).
exists a; split; trivial.
destruct (remove T.eq_bool a l2) as [l2' | ]; [idtac | contradiction].
unfold TO.A in *; destruct (le_gt_dec (length l2) (length l1 + 1)) as [Ll2' | Ll2'].
absurd (length l2 < length l2); auto with arith.
rewrite Nat.add_comm in Ll2';  apply Nat.le_lt_trans with (S (length l1)); trivial.
pattern (Var v :: l1) in t1_sigma; simpl in t1_sigma; rewrite Af1 in t1_sigma.
simpl in v_sigma; rewrite v_sigma in t1_sigma.
revert t1_sigma; 
generalize (F.Symb.eq_bool_ok f1 f1); case (F.Symb.eq_bool f1 f1); [intros _ t1_sigma | intro f1_diff_f1; apply False_rect; apply f1_diff_f1; reflexivity].
injection t1_sigma; intro H2; rewrite <- H2; clear H2.
rewrite length_quicksort; simpl; apply le_n_S; rewrite length_app.
replace (S (length l1)) with (1 + length l1); trivial; apply Nat.add_le_mono.
destruct W_fk as [_ [W_fk _]]; apply le_S_n; trivial.
rewrite <- (length_map (apply_cf_subst sigma) l1).
apply length_flatten_bis; trivial.
intros t' t'_in_map_l1; rewrite in_map_iff in t'_in_map_l1; 
destruct t'_in_map_l1 as [t [Wt t_sigma]].
subst; apply well_formed_cf_apply_subst; trivial.
apply (well_formed_cf_subterms Wt1); right; trivial.

right; exists (((fresh_var pb), (build f1 k)) :: sigma).
assert (R'' := (R' (build f1 k))).
rewrite Pb in R''; destruct R'' as [R1 [R2 R3]]; 
simpl in R1; rewrite <- Pb in R1;
simpl in R2; rewrite <- Pb in R2;
simpl in R3; rewrite <- Pb in R3;
simpl; rewrite <- Pb; repeat split; trivial.
intros t1 t2 [In_t1t2 | In_t1t2]; [injection In_t1t2; intros; subst | apply R1; right]; trivial.
simpl partly_solved_part; simpl find;
intro v'; assert (R2_v' := R2 v').
generalize (X.eq_bool_ok v' v); case (X.eq_bool v' v); [intro v'_eq_v | intro v'_diff_v]; trivial.
subst v'; rewrite v_sigma'; trivial.
intro v'; assert (S'_v' := S' v').
generalize (X.eq_bool_ok v' (fresh_var pb)); case (X.eq_bool v' (fresh_var pb)); [intro v'_eq_fv | intro v'_diff_fv];
[do 2 left; subst v' | destruct S'_v' as [S'_v' | S'_v']; [left; right | right]]; trivial.

(* 1/4  t1 = f1(f k,l1), t2 = f1(l2) *)
unfold ac_elementary_solve_term_term_term.
refine (exists_map_without_repetition _ T.eq_bool_ok _ _ _ _).
exists (apply_cf_subst sigma (Term f k)).
assert (f_diff_s := well_formed_cf_alien Af1 Wt1 _ (or_introl _ (eq_refl _))).
simpl in f_diff_s.
assert (s_l0_in_l2 : In (apply_cf_subst sigma (Term f k)) l2).
generalize (S1 _ _ (or_introl _ (eq_refl _))); simpl; rewrite Af1;
generalize (F.Symb.eq_bool_ok f1 f); case (F.Symb.eq_bool f1 f); [intros f1_eq_f; absurd (f1 = f); trivial | intro f_diff_f1].
intro H; injection H; intros; subst l2.
rewrite <- in_quick_in; left; trivial.
split; [trivial | idtac].
generalize (in_remove _ _ T.eq_bool_ok (apply_cf_subst sigma (Term f k)) l2);
destruct (remove T.eq_bool (apply_cf_subst sigma (Term f k)) l2) as 
   [l2''' | ]; [idtac | intro; absurd (In (apply_cf_subst sigma (Term f k)) l2); trivial].
intros [a' [l2' [l2'' [H [l2_eq l2'''_eq]]]]]; subst a';
injection l2'''_eq; clear l2'''_eq; intro; subst l2 l2''';
simpl; generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); [intros _ | intro f_diff_f; apply False_rect; apply f_diff_f; reflexivity].
exists sigma; repeat split; trivial.
simpl unsolved_part; intros t1 t2 [In_t1t2 | [In_t1t2 | In_t1t2]].
injection In_t1t2; intros; subst.
apply flatten_cf with f1; trivial.
apply well_formed_cf_apply_subst; trivial;
apply (well_formed_cf_subterms Wt1); left; trivial.
apply (well_formed_cf_apply_subst W_sigma (Term f k)).
apply (well_formed_cf_subterms Wt1); left; trivial.
apply permut_refl.
injection In_t1t2; intros; subst.
apply flatten_cf with f1; trivial.
apply well_formed_cf_apply_subst; trivial;
apply well_formed_cf_build_cons with (Term f k); trivial.
apply well_formed_cf_build_inside with (apply_cf_subst sigma (Term f k)); trivial.
rewrite <- (flatten_apply_cf_subst sigma l1 Af1).
rewrite (flatten_build (l2' ++ l2'') Af1).
rewrite (@permut_cons_inside (apply_cf_subst sigma (Term f k))
                                              (apply_cf_subst sigma (Term f k))); [idtac | reflexivity].
simpl in t1_sigma; rewrite Af1 in t1_sigma; 
injection t1_sigma; clear t1_sigma; intro t1_sigma;
(* dummy *)
setoid_rewrite <- t1_sigma.
generalize (F.Symb.eq_bool_ok f1 f); case (F.Symb.eq_bool f1 f); [intros f1_eq_f; absurd (f1 = f); trivial | intro f_diff_f1].
apply quick_permut.
intros t t_in_l2'_l2''; 
destruct (in_app_or _ _ _ t_in_l2'_l2'') as [t_in_l2' | t_in_l2''];
apply (well_formed_cf_alien Af1 Wt2); apply in_or_app; [left | right; right]; trivial.
apply S1; right; trivial.
intro; apply H; apply in_impl_mem; trivial.

(* 1/3 length l1 > length l2 *)
absurd (length l1 > length l2); trivial;
unfold gt; apply Nat.le_ngt;
simpl in t1_sigma; rewrite Af1 in t1_sigma; inversion_clear t1_sigma;
rewrite length_quicksort;
apply length_flatten_ter; trivial.
intros; apply (well_formed_cf_subterms Wt1); trivial.

(* 1/2 arity f1 = C *)
generalize (well_formed_cf_unfold _ Wt1); rewrite Af1; intros [Wl1 [Ll1 Sl1]].
generalize (well_formed_cf_unfold _ Wt2); rewrite Af1; intros [Wl2 [Ll2 Sl2]].
destruct l1 as [ | a1 [ | b1 [ | c1 l1]]]; [absurd (0 = 2) | absurd (1 = 2) | idtac | absurd (S(S(S(length l1))) = 2); simpl in Ll1; try discriminate]; trivial.
destruct l2 as [ | a2 [ | b2 [ | c2 l2]]]; [absurd (0 = 2) | absurd (1 = 2) | idtac | absurd (S(S(S(length l2))) = 2); simpl in Ll2; try discriminate]; trivial.
simpl in t1_sigma; rewrite Af1 in t1_sigma; 
injection t1_sigma; clear t1_sigma; intro t1_sigma.
assert (P := quick_permut (apply_cf_subst sigma a1 :: apply_cf_subst sigma b1 :: nil));
rewrite t1_sigma in P.
generalize (list_permut.permut_length_2 P); clear P.
intros [[a1_sigma b1_sigma] | [a1_sigma b1_sigma]].
exists (mk_pb ex ((a1, a2) :: (b1, b2) :: unsolved_p) solved_p partly_solved_p); split.
left; trivial.
exists sigma; repeat split; trivial.
simpl; intros t1 t2 [t1t2_eq_a1a2 | [t1t2_eq_b1b2 | t1t2_in_l]]; 
[ injection t1t2_eq_a1a2; intros; subst 
| injection t1t2_eq_b1b2; intros; subst 
| apply  S1; right]; trivial.
exists (mk_pb ex ((a1, b2) :: (b1, a2) :: unsolved_p) solved_p partly_solved_p); split.
right; left; trivial.
exists sigma; repeat split; trivial.
simpl; intros t1 t2 [t1t2_eq_a1b2 | [t1t2_eq_b1a2 | t1t2_in_l]]; 
[ injection t1t2_eq_a1b2; intros; subst 
| injection t1t2_eq_b1a2; intros; subst 
| apply  S1; right]; trivial.

(* 1/1 arity f1 = Free n *)
simpl in t1_sigma; rewrite Af1 in t1_sigma.
injection t1_sigma; clear t1_sigma; intro t1_sigma.
assert (T1 : forall t1 t2, In (t1,t2) unsolved_p -> apply_cf_subst sigma t1 = t2).
intros t1 t2 t1t2_in_unsolved_p; apply S1; right; trivial. 
assert (U1 : match
      fold_left2
        (fun (current_list_of_eqs : list (term * term)) (t1 t2 : term) =>
         (t1, t2) :: current_list_of_eqs) unsolved_p l1 l2
    with
    | Some new_list_of_equations =>
       forall t1 t2, In (t1,t2) new_list_of_equations ->
          apply_cf_subst sigma t1 = t2
    | None => False
    end).
subst l2.
revert T1; generalize l1 unsolved_p.
intro l; induction l as [ | t l]; simpl.
intros unsol T1 t1 t2 t1t2_in_unsol; apply T1; trivial.
intros unsol T1; generalize (IHl ((t, apply_cf_subst sigma t) :: unsol)).
destruct (fold_left2
    (fun (current_list_of_eqs : list (term * term)) (t1 t2 : term) =>
     (t1, t2) :: current_list_of_eqs) ((t, apply_cf_subst sigma t) :: unsol)
    l (map (apply_cf_subst sigma) l)) as [l' | ].
intro IH; apply IH; intros t1 t2 [t1t2_eq_ttsigma | t1t2_in_unsol].
injection t1t2_eq_ttsigma; intros; subst; trivial.
apply T1; trivial.
intro IH; apply IH; intros t1 t2 [t1t2_eq_ttsigma | t1t2_in_unsol].
injection t1t2_eq_ttsigma; intros; subst; trivial.
apply T1; trivial.
destruct (fold_left2
        (fun (current_list_of_eqs : list (term * term)) (t1 t2 : term) =>
         (t1, t2) :: current_list_of_eqs) unsolved_p l1 l2) as [l | ].
exists (mk_pb ex l solved_p partly_solved_p); split.
left; trivial.
exists sigma; repeat split; trivial.
contradiction.
Qed.

End Make.



