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

(* Usable rules, adapted from the exam of Xavier for MPRI 2-5, 2009 *)


(** * Termination of rewriting *)

From Stdlib Require Import List Relations Wellfounded Arith Recdef Setoid.
From CoLoR Require Import closure more_list weaved_relation term_spec
     equational_theory_spec dp graph_dp terminaison interp.

Module MakeUsableDP (E : EqTh).

  Module GDp := graph_dp.MakeGDP (E).
  Import GDp.
  Import Dp.
  Import E.
  Import T.

Definition filter_top R G : relation term := 
  fun r l => R r l /\ match l with Var _ => False | Term f _ => G f end.

Definition symb_sup_gen R1 R2 : relation symbol :=
  fun f g => 
            exists r, exists l, 
            filter_top R1 (fun f' => f = f') r l /\ 
            symb_in_term g r = true /\ 
            defined R2 g.

Lemma symb_sup_gen_list : 
  forall R1 Rlist1 R2 Rlist2, (forall l r, R1 r l <-> In (l,r) Rlist1) -> (forall l r, R2 r l <-> In (l,r) Rlist2) -> 
  {Slist | forall f g, symb_sup_gen R1 R2 f g <-> In (f,g) Slist}.
Proof.
intros R1 Rlist1; revert R1.
induction Rlist1 as [ | [l r] Rlist1]; intros R1 R2 Rlist2 Rlist_ok1 Rlist_ok2.
exists nil; intros f g; split; intro H.
destruct H as [r [l [[H _] _]]]; rewrite Rlist_ok1 in H; contradiction.
contradiction.
set (R' := fun b a => R1 b a /\ In (a,b) Rlist1).
assert (Rlist_ok' : forall a b, R' b a <-> In (a,b) Rlist1).
intros a b; split; intro H.
destruct H as [_ H]; assumption.
split; [rewrite Rlist_ok1; right | ]; assumption.
destruct (IHRlist1 R' R2 Rlist2 Rlist_ok' Rlist_ok2) as [Slist Slist_ok].
destruct l as [x | f l].
exists Slist; intros f g; split.
intros [u [v [[H1 H2] [H3 H4]]]].
rewrite Rlist_ok1 in H1; simpl in H1; destruct H1 as [H1 | H1].
injection H1; intros; subst; contradiction H2.
rewrite <- Slist_ok; exists u; exists v; split; split.
rewrite Rlist_ok'; assumption.
assumption.
assumption.
destruct H4 as [g l t H4]; constructor 1 with l t.
assumption.
intro H; rewrite <- Slist_ok in H; destruct H as [u [v [[H1 H2] [H3 H4]]]].
exists u; exists v; split; split.
rewrite Rlist_ok1; right; rewrite <- Rlist_ok'; assumption.
assumption.
assumption.
destruct H4 as [g l t H4]; constructor 1 with l t.
assumption.
exists ((map (fun g => (f,g)) (filter (fun g => if defined_dec _ _ Rlist_ok2 g then true else false) (symb_list r))) ++ Slist).
intros g g'; split; intro H.
destruct H as [u [v [H1 [H2 H3]]]].
destruct H1 as [H H1].
rewrite Rlist_ok1 in H; simpl in H; destruct H as [H | H].
injection H; clear H; intros; subst; subst.
apply in_or_app; left; rewrite in_map_iff; exists g'; split; [apply eq_refl | ].
rewrite filter_In; split.
rewrite symb_list_ok; assumption.
destruct (defined_dec R2 Rlist2 Rlist_ok2 g') as [Dg' | NDg'].
apply eq_refl.
apply False_rect; apply NDg'; assumption.
apply in_or_app; right; rewrite <- Slist_ok.
exists u; exists v; split; split.
rewrite Rlist_ok'; assumption.
assumption.
assumption.
assumption.
destruct (in_app_or _ _ _ H) as [H1 | H2]; clear H.
rewrite in_map_iff in H1; destruct H1 as [g'' [H1 H2]].
injection H1; clear H1; intros; subst.
rewrite filter_In in H2; destruct H2 as [g'_in_r H2].
destruct (defined_dec R2 Rlist2 Rlist_ok2 g') as [Dg' | NDg']; [ clear H2 | discriminate H2].
exists r; exists (Term g l); split; split.
rewrite Rlist_ok1; left; apply eq_refl.
apply eq_refl.
rewrite <- symb_list_ok; assumption.
assumption.
rewrite <- Slist_ok in H2; destruct H2 as [u [v [[H1 H2]  [H3 H4]]]].
exists u; exists v; split; split.
rewrite Rlist_ok1; right; rewrite <- Rlist_ok'; assumption.
assumption.
assumption.
assumption.
Defined.

Definition symb_sup R : relation symbol :=
  fun f g => 
      exists r, exists l, 
      filter_top R (fun f' => f = f') r l /\ 
      symb_in_term g r = true /\ 
      defined R g.

Definition Usable R t : relation term :=
   filter_top R 
   (fun g => exists f, symb_in_term f t = true /\ 
                       refl_trans_clos (symb_sup R) f g).

Definition UsableRules (R C : relation term) : relation term :=
  fun u v => exists r, exists l, C r l /\ Usable R r u v.

Lemma symb_sup_list : 
  forall R Rlist, (forall l r, R r l <-> In (l,r) Rlist) -> 
  {Slist | forall f g, symb_sup R f g <-> In (f,g) Slist}.
Proof.
intros R Rlist Rlist_ok.
exact (symb_sup_gen_list R Rlist R Rlist Rlist_ok Rlist_ok).
Defined.

Lemma usable_dec : 
  forall R Rlist, (forall l r, R r l <-> In (l,r) Rlist) -> 
  forall t, {URlist | forall r l,  Usable R t r l <-> In (l,r) URlist}.
Proof.
intros R Rlist Rlist_ok t.
destruct (symb_sup_list _ _ Rlist_ok) as [Slist Slist_ok].
assert (SR_dec := refl_trans_clos_dec _ F.Symb.eq_bool_ok _ _ Slist_ok).
unfold Usable; set (SR := refl_trans_clos (symb_sup R)) in *; clearbody SR; clear Slist Slist_ok.
revert R Rlist_ok; induction Rlist as [ | [l r] Rlist]; intros R Rlist_ok.
exists nil; intros r l; split; intro H.
destruct H as [H _]; rewrite Rlist_ok in H; assumption.
contradiction.
set (R' := fun b a => R b a /\ In (a,b) Rlist).
assert (Rlist_ok' : forall a b, R' b a <-> In (a,b) Rlist).
intros a b; split; intro H.
destruct H as [_ H]; assumption.
split; [rewrite Rlist_ok; right | ]; assumption.
destruct (IHRlist _ Rlist_ok') as [URlist URlist_ok].
destruct l as [x | f l].
exists URlist; intros u v; split; intro H.
destruct H as [H1 H2]; rewrite Rlist_ok in H1; simpl in H1; destruct H1 as [H1 | H1].
injection H1; clear H1; intros; subst.
contradiction.
rewrite <- URlist_ok; split; [rewrite Rlist_ok' | ]; assumption.
rewrite <- URlist_ok in H; destruct H as [H1 H2]; split; [ rewrite Rlist_ok; right; rewrite <- Rlist_ok' | ]; assumption.
assert (split_case : {f0 : symbol | symb_in_term f0 t = true /\ SR f0 f}+{forall f0, ~(symb_in_term f0 t = true /\ SR f0 f)}).
case_eq (filter (fun g => if SR_dec g f then true else false) (symb_list t)).
intro H; right; intros g [g_in_t Sgf].
assert (g_in_nil : In g nil).
rewrite <- H; rewrite filter_In; split.
rewrite symb_list_ok; assumption.
destruct (SR_dec g f); [apply eq_refl | absurd (SR g f); assumption].
contradiction g_in_nil.
intros g k H; left; exists g.
assert (g_in_gk : In g (g :: k)).
left; apply eq_refl.
rewrite <- H in g_in_gk; rewrite filter_In in g_in_gk; destruct g_in_gk as [g_in_t Sgf]; split.
rewrite <- symb_list_ok; assumption.
destruct (SR_dec g f); [assumption | discriminate].
destruct split_case as [[g [g_in_t Sgf]] | Ko].
exists ((Term f l,r) :: URlist); intros u v; split; intro H.
destruct H as [H1 H2].
rewrite Rlist_ok in H1; simpl in H1; destruct H1 as [H1 | H1].
left; assumption.
right; rewrite <- URlist_ok; split; [rewrite Rlist_ok' | ]; assumption.
simpl in H; destruct H as [H | H].
injection H; clear H; intros; subst; split.
rewrite Rlist_ok; left; apply eq_refl.
exists g; split; assumption.
rewrite <- URlist_ok in H; destruct H as [H1 H2]; split; [ rewrite Rlist_ok; right; rewrite <- Rlist_ok' | ]; assumption.
exists URlist; intros u v; split; intro H.
destruct H as [H1 H2]; rewrite Rlist_ok in H1; simpl in H1; destruct H1 as [H1 | H1].
injection H1; clear H1; intros; subst.
destruct H2 as [g H2]; apply False_rect; apply (Ko g); assumption.
rewrite <- URlist_ok; split; [rewrite Rlist_ok' | ]; assumption.
rewrite <- URlist_ok in H; destruct H as [H1 H2]; split; [ rewrite Rlist_ok; right; rewrite <- Rlist_ok' | ]; assumption.
Defined.

Lemma usablerules_dec : 
  forall R Rlist, (forall l r, R r l <-> In (l,r) Rlist) -> 
  forall P Plist, (forall u v, P v u <-> In (u,v) Plist) ->
  {URlist | forall l r,  UsableRules R P r l <-> In (l,r) URlist}.
Proof.
intros R Rlist Rlist_ok P Plist; revert P; induction Plist as [ | [u v] Plist]; intros P Plist_ok.
exists nil; intros l r; split; intro H.
destruct H as [u [v [H _]]]; rewrite Plist_ok in H; assumption.
contradiction.
set (P' := fun b a => P b a /\ In (a,b) Plist).
assert (Plist_ok' : forall a b, P' b a <-> In (a,b) Plist).
intros a b; split; intro H.
destruct H as [_ H]; assumption.
split; [rewrite Plist_ok; right | ]; assumption.
destruct (IHPlist _ Plist_ok') as [URlist URlist_ok].
destruct (usable_dec _ _ Rlist_ok v) as [Uv Uv_ok].
exists (Uv ++ URlist); intros l r; split; intro H.
destruct H as [s [t [H1 H2]]].
rewrite Plist_ok in H1; simpl in H1; destruct H1 as [H1 | H1].
injection H1; clear H1; intros; subst.
apply in_or_app; left; rewrite <- Uv_ok; assumption.
apply in_or_app; right; rewrite <- URlist_ok; exists s; exists t; split; [ rewrite Plist_ok' | ]; assumption.
destruct (in_app_or _ _ _ H) as [H1 | H1]; clear H.
rewrite <- Uv_ok in H1.
exists v; exists u; split; [rewrite Plist_ok; left; apply eq_refl | assumption].
rewrite <- URlist_ok in H1; destruct H1 as [s [t [H1 H2]]].
exists s; exists t; split; [ rewrite Plist_ok; right; rewrite <- Plist_ok' |  ]; assumption.
Defined.

Lemma eq_term_dec2 : forall (s12 t12 : term * term), {s12 = t12}+{s12 <> t12}.
Proof.
intros [s1 s2] [t1 t2].
generalize (T.eq_bool_ok s1 t1); case (T.eq_bool s1 t1); [intro s1_eq_t1 | intro s1_diff_t1].
generalize (T.eq_bool_ok s2 t2); case (T.eq_bool s2 t2); [intro s2_eq_t2 | intro s2_diff_t2].
left; apply f_equal2; assumption.
right; intro s12_eq_t12; apply s2_diff_t2; injection s12_eq_t12; intros s2_eq_t2 _; assumption.
right; intro s12_eq_t12; apply s1_diff_t1; injection s12_eq_t12; intros _ s1_eq_t1; assumption.
Defined.

Lemma split_rules :
  forall R Rlist, (forall l r, R r l <-> In (l,r) Rlist) ->
  forall P Plist, (forall u v, P v u <-> In (u,v) Plist) ->
  (forall v t, ~ R t (Var v)) ->
  forall G, 
  (forall f, G f <-> defined (fun r l => R r l /\ ~ UsableRules R P r l) f) -> 
  (forall r l, R r l <-> (UsableRules R P r l \/ filter_top R G r l)) /\
  (forall r l, UsableRules R P r l -> forall g, symb_in_term g r = true -> ~G g).
Proof.
intros R Rlist Rlist_ok P Plist Plist_ok R_var G Gdef.
assert (Pdec := rel_dec P Plist Plist_ok).
destruct (usablerules_dec _ _ Rlist_ok _ _ Plist_ok) as [URlist URlist_ok].
split.
intros r l; split; intro H.
rewrite URlist_ok.
destruct (In_dec eq_term_dec2 (l,r) URlist) as [lr_in_U | lr_not_in_U].
left; assumption.
right; split; [assumption | destruct l as [x | f l]].
apply (R_var _ _ H).
rewrite Gdef; constructor 1 with l r; split; [ | rewrite URlist_ok]; assumption.
destruct H as [[v [u [_ [H _]]]] | [H _]]; assumption.
intros r [x | f l] [v [u [H1 [H2 H3]]]] g g_in_r Gg.
contradiction H3.
rewrite Gdef in Gg; inversion Gg as [g' k t [K1 K2]]; subst g'.
apply K2; constructor 1 with v; exists u; split.
assumption.
split; [assumption | destruct H3 as [f' [H3 H4]]; exists f'; split].
assumption.
apply refl_trans_clos_is_trans with f; trivial.
right; left; constructor 1 with r; exists (Term f l); split.
split; [assumption | apply eq_refl].
split; [ | constructor 1 with k t]; assumption.
Qed.

Lemma Gdec :
  forall R Rlist, (forall l r, R r l <-> In (l,r) Rlist) ->
  forall P Plist, (forall u v, P v u <-> In (u,v) Plist) ->
  let G := fun f => defined (fun r l => R r l /\ ~ UsableRules R P r l) f in 
  forall f, {~G f} + {G f}.
Proof.
intros R Rlist Rlist_ok P Plist Plist_ok.
assert (H : {rule_list : list (term * term) |
 (forall l r : term, R r l /\ ~ UsableRules R P r l <-> In (l, r) rule_list)}).
destruct (usablerules_dec _ _ Rlist_ok _ _ Plist_ok) as [URlist URlist_ok].
exists (filter (fun st => if In_dec eq_term_dec2 st URlist then false else true) Rlist).
intros l r; split.
intros [H1 H2]; rewrite filter_In; split.
rewrite <- Rlist_ok; assumption.
destruct (In_dec eq_term_dec2 (l,r) URlist).
apply False_rect; apply H2; rewrite URlist_ok; assumption.
apply eq_refl.
rewrite filter_In; intros [H1 H2]; split.
rewrite Rlist_ok; assumption.
destruct (In_dec eq_term_dec2 (l,r) URlist).
discriminate.
rewrite URlist_ok; assumption.
destruct H as [rule_list H].
intros G f;
destruct (defined_dec(fun r l : term => R r l /\ ~ UsableRules R P r l) _ H f) as [Df | nDf].
right; assumption.
left; assumption.
Defined.

(*
Definition pair_sup_symb (R P : relation term) g :=
  exists r, exists l, P r l /\ exists g', symb_in_term g' r = true /\ refl_trans_clos (symb_sup R) g' g.
*)
Inductive Pi pi (v1 v2 : variable) : relation term :=
  | Pi1 : Pi pi v1 v2 (Var v1) (Term pi (Var v1 :: Var v2 :: nil))
  | Pi2 : Pi pi v1 v2 (Var v2) (Term pi (Var v1 :: Var v2 :: nil)).

Definition is_primary_pi pi R := 
   forall s t, R s t -> (forall f, ((symb_in_term f s = true -> f <> pi) /\
                                             (symb_in_term f t = true -> f <> pi))).

Section Interp_definition.
Variable V0 : variable.
Variable V1 : variable.
Variable V0_diff_V1 : V0 <> V1.
Variable pi : symbol.
Variable bot : symbol.
Variable R : relation term.
Variable R_reg : forall s t, R s t -> forall x, In x (var_list s) -> In x (var_list t) .
Variable R_var : forall v t, ~ R t (Var v).
Variable Rlist : list (term * term).
Variable Rlist_ok : forall l r, R r l <-> In (l,r) Rlist.
Variable PPi : is_primary_pi pi R. 
Variable G : symbol -> Prop.
Variable P : relation term.
Variable Plist : list (term * term).
Variable Plist_ok : forall u v, P v u <-> In (u,v) Plist.
Variable Gdef' : 
  forall f, G f <-> defined (fun r l => R r l /\ ~ UsableRules R P r l) f.

Lemma Gdef : forall f, G f -> defined R f.
Proof.
intros f Gf; rewrite Gdef' in Gf; inversion Gf as [f' l t [H _]]; subst f'.
constructor 1 with l t; assumption.
Qed.

Definition R_red := compute_red Rlist.
Definition FB : forall t s, In s (R_red t) <-> one_step R s t.
apply compute_red_is_correct.
intros l r H; apply R_reg; rewrite Rlist_ok; assumption.
assumption.
Defined.

Fixpoint Comb (l : list term) : term :=
  match l with
  | nil => Term bot nil
  | t :: l => Term pi (t :: (Comb l) :: nil)
  end.

Inductive interp_call : term -> term -> Prop :=
  | Subt : forall f1 l t, In t l -> interp_call t (Term f1 l)
  | Defd : forall f2 l t, G f2 -> one_step R t (Term f2 l) -> interp_call t (Term f2 l).

Definition Interp_dom t :=
  forall p f l, subterm_at_pos t p = Some (Term f l) -> G f -> Acc (one_step R) (Term f l).

Lemma interp_dom_subterm :
  forall s t p, Interp_dom s -> subterm_at_pos s p = Some t -> Interp_dom t.
Proof.
intros s t p Is Sub q g l Sub' Dg.
apply Is with (p ++ q); trivial.
apply subterm_in_subterm with t; trivial.
Qed.

Lemma acc_one_step_interp_dom : 
	forall t, Acc (one_step R) t -> Interp_dom t.
Proof.
intros t Acc_t; rewrite acc_with_subterm in Acc_t; induction Acc_t as [t Acc_t' IH].
assert (Acc_t : Acc (union term (one_step R) direct_subterm) t).
apply Acc_intro; apply Acc_t'.
clear Acc_t'.
intros p f l K f_not_in_H.
apply acc_subterms_3 with p t; trivial.
rewrite acc_with_subterm; assumption.
Qed.

Lemma interp_well_defined : forall t, Interp_dom t -> Acc interp_call t.
Proof.
intro t; pattern t; apply term_rec3; clear t.
intros v _.
apply Acc_intro; intros t K; inversion K.
intros f l IH K.
apply Acc_intro; intros t K'; inversion K'; subst.
apply IH; trivial.
destruct (in_split _ _ H1) as [l1 [l2 K'']].
apply interp_dom_subterm with (Term f l) (length l1 :: nil); trivial.
subst l; simpl; rewrite nth_error_at_pos; apply eq_refl.
apply Acc_inv with (Term f l); trivial.
generalize (K nil f l (eq_refl _) H2).
set (s := Term f l) in *; clearbody s; clear.
intro Acc_s; rewrite acc_with_subterm in Acc_s.
induction Acc_s as [s Acc_s' IH].
assert (Acc_s : Acc (union term (one_step R) direct_subterm) s).
apply Acc_intro; apply Acc_s'.
clear Acc_s'.
apply Acc_intro; intros t K; inversion K; clear K; subst.
apply IH; right; assumption.
apply IH; left; assumption.
Qed.

Inductive Interp : term -> term -> Prop :=
  | Vcase : forall x, Interp (Var x) (Var x)
  | notGcase : forall f l l' ll , ~G f -> 
                l = (map (fun st => fst st)) ll -> l' = (map (fun st => snd st)) ll ->
                (forall s s', In (s,s') ll -> Interp s s') -> 
                Interp (Term f l) (Term f l')
  | Gcase : forall f l l' ll k' kk, G f ->
               l = (map (fun st => fst st)) ll -> l' = (map (fun st => snd st)) ll ->
               (forall s s', In (s,s') ll -> Interp s s') -> 
               R_red (Term f l) = (map (fun st => fst st)) kk -> k' = (map (fun st => snd st)) kk ->
               (forall s s', In (s,s') kk -> Interp s s') -> 
               Interp (Term f l) (Comb (Term f l' :: k')).

Lemma interp_unicity : forall t, Acc interp_call t -> forall s1 s2, Interp t s1 -> Interp t s2 -> s1 = s2.
Proof.
intros t Acc_t;
induction Acc_t as [t Acc_t IH].
destruct t as [x | f l];
intros s1 s2 H1 H2; 
inversion H1 as [ | f1 l1 l1' ll1 Cf1 Hl1 Hl1' Hll1 | f1 l1 l1' ll1 k1 kk1 Df1 Hl1 Hl1' Hll1 Hk1 Hk1' Hkk1];
inversion H2 as [ | f2 l2 l2' ll2 Cf2 Hl2 Hl2' Hll2 | f2 l2 l2' ll2 k2 kk2 Df2 Hl2 Hl2' Hll2 Hk2 Hk2' Hkk2]; subst; trivial.
(* 1/4 f not in G *)
do 2 apply f_equal.
assert (K : forall s s1 s2, In (s,s1) ll1 -> In (s,s2) ll2 -> s1 = s2).
intros s s1 s2 ss1_in_ll1 ss2_in_ll2.
assert (s_in_l : In s (map (fun st => fst st) ll1)).
rewrite in_map_iff; exists (s,s1); split; trivial.
apply IH with s.
left; assumption.
destruct (in_split _ _ s_in_l) as [kk1 [kk2 K]].
apply Hll1; assumption.
apply Hll2; assumption.
clear -Hl2 K.
revert ll2 Hl2 K.
induction ll1 as [ | [s s1] ll1]; intros [ | [s' s2] ll2] Hl2 K; trivial.
discriminate.
discriminate.
simpl in Hl2; injection Hl2; clear Hl2; intros H' s_eq_s'; subst s'.
rewrite (K s s1 s2); try (left; trivial).
rewrite IHll1 with ll2; trivial.
intros t t1 t2 tt1_in_ll1 tt2_in_ll2; apply (K t t1 t2); right; trivial.
absurd (G f); trivial.
absurd (G f); trivial.
(* 1/1 f in G *)
apply f_equal; apply f_equal2.
do 2 apply f_equal.
assert (K : forall s s1 s2, In (s,s1) ll1 -> In (s,s2) ll2 -> s1 = s2).
intros s s1 s2 ss1_in_ll1 ss2_in_ll2.
assert (s_in_l : In s (map (fun st => fst st) ll1)).
rewrite in_map_iff; exists (s,s1); split; trivial.
apply IH with s.
left; assumption.
destruct (in_split _ _ s_in_l) as [lll1 [lll2 K]].
apply Hll1; assumption.
apply Hll2; assumption.
clear -Hl2 K.
revert ll2 Hl2 K.
induction ll1 as [ | [s s1] ll1]; intros [ | [s' s2] ll2] Hl2 K; trivial.
discriminate.
discriminate.
simpl in Hl2; injection Hl2; clear Hl2; intros H' s_eq_s'; subst s'.
rewrite (K s s1 s2); try (left; trivial).
rewrite IHll1 with ll2; trivial.
intros t t1 t2 tt1_in_ll1 tt2_in_ll2; apply (K t t1 t2); right; trivial.
apply f_equal.
assert (K : forall s s1 s2, In (s,s1) kk1 -> In (s,s2) kk2 -> s1 = s2).
intros s s1 s2 ss1_in_kk1 ss2_in_kk2.
assert (s_in_l : In s (map (fun st => fst st) kk1)).
rewrite in_map_iff; exists (s,s1); split; trivial.
apply IH with s.
right; trivial.
rewrite <- FB; rewrite Hk1; assumption.
destruct (in_split _ _ s_in_l) as [kkk1 [kkk2 K]].
apply Hkk1; assumption.
apply Hkk2; assumption.
rewrite Hk1 in Hk2.
clear -Hk2 K.
revert kk2 Hk2 K.
induction kk1 as [ | [s s1] kk1]; intros [ | [s' s2] kk2] Hk2 K; trivial.
discriminate.
discriminate.
simpl in Hk2; injection Hk2; clear Hk2; intros H' s_eq_s'; subst s'.
rewrite (K s s1 s2); try (left; trivial).
rewrite IHkk1 with kk2; trivial.
intros t t1 t2 tt1_in_ll1 tt2_in_ll2; apply (K t t1 t2); right; trivial.
Qed.

Lemma interp_defined : forall t, Acc interp_call t -> {t' | Interp t t'}.
Proof.
intros t Acc_t; induction Acc_t as [t Acc_t' IH].
assert (Acc_t : Acc interp_call t).
apply Acc_intro; apply Acc_t'.
clear Acc_t'; destruct t as [x | f l].
exists (Var x); apply Vcase.
assert (Il : {ll : list (term * term) | l = map (@fst term term) ll /\ forall t t', In (t,t') ll -> Interp t t'}).
assert (IHl : forall t, In t l -> {t' : term | Interp t t'}).
intros t t_in_l.
apply IH; left; trivial.
revert IHl; clear; induction l as [ | t l]; intros IH.
exists nil; split; [apply eq_refl | intros; contradiction].
destruct (IHl (tail_set _ IH)) as [ll [H1 H2]].
destruct (IH _ (or_introl _ (eq_refl _))) as [t' H3].
exists ((t,t') :: ll); split; 
[ subst l; apply eq_refl
| intros u u' [uu'_eq_tt' | uu'_in_ll]; [injection uu'_eq_tt'; intros; subst; assumption | apply H2; assumption]].
destruct Il as [ll [H1 H2]].
destruct (Gdec _ _ Rlist_ok _ _ Plist_ok f) as [f_not_in_G | f_in_G].
(* 1/2 f not in G *)
exists (Term f (map (@snd _ _) ll)).
apply notGcase with ll; trivial.
rewrite Gdef'; assumption.
(* 1/1 f in G *)
assert (Ik : {kk : list (term * term) |  R_red  (Term f l) = map (@fst term term) kk /\ forall t t', In (t,t') kk -> Interp t t'}).
assert (IHk : forall t, In t (R_red (Term f l)) -> {t' : term | Interp t t'}).
intros t t_in_red; rewrite FB in t_in_red.
apply IH; right; trivial.
rewrite Gdef'; assumption.
revert IHk; generalize ((R_red (Term f l))); clear.
intro k; induction k as [ | t k]; intro Hk.
exists nil; split; [apply eq_refl | intros; contradiction].
destruct (IHk (tail_set _ Hk)) as [kk [H1 H2]].
destruct (Hk _ (or_introl _ (eq_refl _))) as [t' H3].
exists ((t,t') :: kk); split; 
[ subst k; apply eq_refl
| intros u u' [uu'_eq_tt' | uu'_in_ll]; [injection uu'_eq_tt'; intros; subst; assumption | apply H2; assumption]].
destruct Ik as [kk [K1 K2]].
exists (Comb (Term f (map (@snd _ _) ll) :: (map (@snd _ _) kk))).
apply Gcase with ll kk; trivial.
rewrite Gdef'; assumption.
Qed.

Lemma project_comb :  forall t l, In t l -> rwr (Pi pi V0 V1) t (Comb l).
Proof.
intros t l; induction l as [ | a l].
contradiction.
simpl; set (sigma := (V0,a) :: (V1, Comb l) :: nil).
assert (H1 : a = apply_subst sigma (Var V0)).
simpl; rewrite eq_var_bool_refl; apply eq_refl.
assert (H2 : Comb l = apply_subst sigma (Var V1)).
simpl; rewrite eq_var_bool_refl; case_eq (eq_var_bool V1 V0).
intro V1_eq_V0; apply False_rect; apply V0_diff_V1; apply sym_eq.
generalize (eq_var_bool_ok V1 V0); rewrite V1_eq_V0; intro; assumption.
intros _; apply eq_refl.
assert (H3 : Term pi (a :: Comb l :: nil) = apply_subst sigma (Term pi (Var V0 :: Var V1 :: nil))).
rewrite H1, H2; apply eq_refl.
intros [t_eq_a | t_in_l].
subst t; do 2 left.
rewrite H3, H1; apply instance; left.
apply trans_clos_is_trans with (Comb l).
apply IHl; assumption.
rewrite H3, H2; do 2 left; apply instance; right.
Qed.

Lemma interp_in_H :
  forall t, (forall g, symb_in_term g t = true -> ~G g) ->
  forall sigma sigma', (forall x, In x (var_list t) -> Interp (apply_subst sigma (Var x)) (apply_subst sigma' (Var x))) ->
  Interp (apply_subst sigma t) (apply_subst sigma' t).
Proof.
intros t; pattern t; apply term_rec3; clear t.
intros v _ sigma sigma' Isigma; apply Isigma; left; apply eq_refl.
intros f l IH fl_in_H sigma sigma' Isigma.

simpl; constructor 2 with (map (fun t => (apply_subst sigma t, apply_subst sigma' t)) l).
apply fl_in_H; simpl.
rewrite eq_symb_bool_refl; apply eq_refl.
rewrite map_map; simpl; apply eq_refl.
rewrite map_map; simpl; apply eq_refl.
intros s s' K; rewrite in_map_iff in K; destruct K as [t [K t_in_l]]; injection K; clear K; intros; subst.
apply IH. 
assumption.
intros g g_in_t; apply fl_in_H; apply symb_in_direct_subterm with t; trivial.
intros x x_in_t; apply Isigma.
destruct (In_split _ _ t_in_l) as [l1 [l2 K']].
apply var_in_subterm with t (length l1 :: nil); trivial.
subst l; simpl; rewrite nth_error_at_pos; apply eq_refl.
Qed.

Lemma rwr_interp_subst : 
  forall sigma, 
  forall t, Interp_dom (apply_subst sigma t) ->
  forall tsigma' sigma', 
  Interp (apply_subst sigma t) tsigma' ->
  (forall x, In x (var_list t) -> Interp (apply_subst sigma (Var x)) (apply_subst sigma' (Var x))) ->
  (refl_trans_clos (one_step (Pi pi V0 V1)) (apply_subst sigma' t) tsigma' /\
  match t with
  | Var _ => True
  | Term f l => ~G f ->
     match tsigma' with 
     | Var _ => False 
     | Term g k => f = g /\ refl_trans_clos (one_step_list (one_step (Pi pi V0 V1))) (map (apply_subst sigma') l) k
     end
   end).
Proof.
intros sigma t; pattern t; apply term_rec3; clear t.
(* 1/2 variable case *)
intros v Acc_t tsigma' sigma' I1 I2.
assert (Acc_t' :=  interp_well_defined _ Acc_t).
rewrite <- (interp_unicity _  Acc_t' _ _ I1 (I2 v (or_introl _ (eq_refl _)))); split; [left | exact I].
(* 1/1 compound case *)
intros f l IHl Acc_t tsigma' sigma' I1 I2.
assert (IHl' : forall t : term,
      In t l ->
      forall (tsigma' : term) (sigma' : substitution),
      Interp (apply_subst sigma t) tsigma' ->
      (forall x : variable, In x (var_list t) ->
       Interp (apply_subst sigma (Var x)) (apply_subst sigma' (Var x))) ->
      refl_trans_clos (one_step (Pi pi V0 V1)) (apply_subst sigma' t) tsigma').
intros s s_in_l ssigma'' sigma'' Issigma Isigma''.
assert (Acc_ssigma : Interp_dom (apply_subst sigma s)). 
destruct (In_split _ _ s_in_l) as [l1 [l2 H3]].
apply interp_dom_subterm with (apply_subst sigma (Term f l)) (length l1 :: nil); trivial.
subst l; simpl; rewrite map_app.
rewrite <- (length_map (apply_subst sigma) l1); simpl.
rewrite nth_error_at_pos; apply eq_refl.
apply (proj1 (IHl s s_in_l Acc_ssigma ssigma'' sigma'' Issigma Isigma'')).
inversion I1 as [ | f1 l1 l1' ll1 Cf1 Hl1 Hl1' Hll1 | f1 l1 l1' ll1 k1 kk1 Df1 Hl1 Hl1' Hll1 Hk1 Hk1' Hkk1]; clear I1; subst.
assert (H0 : refl_trans_clos (one_step_list (one_step (Pi pi V0 V1)))
   (map (apply_subst sigma') l) (map (fun st : term * term => snd st) ll1)).
clear IHl Acc_t; revert ll1 Hl1 Hll1 IHl'.
induction l as [ | a l]; intros ll1 Hl1 Hll1 IH.
destruct ll1; [left | discriminate Hl1].
destruct ll1 as [ | [a' a1] ll1]; [discriminate Hl1 | injection Hl1; clear Hl1; intros; subst].
simpl; rewrite refl_trans_clos_one_step_list_head_tail; split.
apply IH; trivial.
left; apply eq_refl.
apply Hll1; left; apply eq_refl.
intros; apply I2; simpl; apply in_or_app; left; assumption.
apply IHl; trivial.
intros; apply I2; simpl; apply in_or_app; right; assumption.
intros; apply Hll1; right; trivial.
apply (tail_prop _ IH).
inversion H0 as [k | k1 k2 K].
split.
left.
intros _; split.
apply eq_refl.
left.
split.
right; apply general_context; assumption.
intros _; split.
apply eq_refl.
right; assumption.
split; [idtac | intro f_not_in_G; absurd (G f); assumption].
apply refl_trans_clos_is_trans with (Term f (map (fun st : term * term => snd st) ll1)).
assert (refl_trans_clos (one_step_list (one_step (Pi pi V0 V1))) 
                      (map (apply_subst sigma') l)
                      (map (fun st : term * term => snd st) ll1)).
clear IHl Acc_t; revert ll1 Hl1 Hll1 IHl'; clear -I2.
induction l as [ | a l]; intros ll1 Hl1 Hll1 IH.
destruct ll1; [left | discriminate Hl1].
destruct ll1 as [ | [a' a1] ll1]; [discriminate Hl1 | injection Hl1; clear Hl1; intros; subst].
simpl; rewrite refl_trans_clos_one_step_list_head_tail; split.
apply IH; trivial.
left; apply eq_refl.
apply Hll1; left; apply eq_refl.
intros; apply I2; simpl; apply in_or_app; left; assumption.
apply IHl; trivial.
intros; apply I2; simpl; apply in_or_app; right; assumption.
intros; apply Hll1; right; trivial.
apply (tail_prop _ IH).
simpl; destruct H as [k | k1 k2 H0].
left.
right; apply general_context; assumption.
right; apply project_comb; left; apply eq_refl.
Qed.

Lemma interp_subst :
  forall l sigma, Interp_dom (apply_subst sigma l) -> 
   {sigma' |  forall x, In x (var_list l) -> Interp (apply_subst sigma (Var x)) (apply_subst sigma' (Var x)) }.
Proof.
intros l sigma Acc_ls.
assert (Acc_sigma : forall x, In x (var_list l) -> Interp_dom (apply_subst sigma (Var x))).
intros x x_in_l; assert (x_mem_l : mem (@eq _) x (var_list l)).
apply in_impl_mem; trivial.
destruct (var_in_subterm2 x l x_mem_l) as [p Sub].
apply interp_dom_subterm with (apply_subst sigma l) p; trivial.
generalize (subterm_at_pos_apply_subst_apply_subst_subterm_at_pos l p sigma).
rewrite Sub; exact (fun p => p).
set (varl := var_list l) in *; clearbody varl.
destruct (remove_garbage_subst sigma) as [tau [H1 [H2 H3]]].
assert (H4 : { tau' : list (variable * (term * term)) | 
                tau = map (fun xtt' => match xtt' with (x,(t,t')) => (x,t) end) tau' /\
                (forall x t t', In x varl -> In (x,(t,t')) tau' -> Interp t t') }).
assert (Acc_tau : forall x : variable, In x varl -> Interp_dom (apply_subst tau (Var x))).
intros; simpl; rewrite <- H1; apply Acc_sigma; assumption.
revert H2 H3 Acc_tau; clear -R_reg Rlist_ok P Plist Plist_ok Gdef'; induction tau as [ | [v vval] tau]; intros H2 H3 Acc_tau.
exists nil; split; [apply eq_refl | intros; contradiction].
destruct IHtau as [tau' [K1 K2]].
intros x xval xval_in_tau; generalize (H2 _ _ (or_intror _ xval_in_tau)); simpl.
generalize (eq_var_bool_ok x v); case (eq_var_bool x v); [intro x_eq_v | intros _; trivial].
apply False_rect.
destruct (In_split _ _ xval_in_tau) as [tau' [tau'' H4]].
apply (H3 v x vval xval nil tau' tau''); subst; trivial.
intros x y xval yval tau1 tau2 tau3 H4; apply (H3 x y xval yval ((v,vval) :: tau1) tau2 tau3); subst; trivial.
intros x x_in_l; generalize (Acc_tau x x_in_l); simpl.
assert (Acc_x : Interp_dom (Var x)).
intros [ | i p] f l Sub; discriminate.
generalize (eq_var_bool_ok x v); case (eq_var_bool x v); [intro x_eq_v | intros _; trivial].
intros _; subst x; generalize (find_mem _ _ eq_var_bool_ok v tau).
case (find eq_var_bool v tau).
intros t K; destruct (K _ (eq_refl _)) as [v' [tau1 [tau2 [K' K'']]]].
apply False_rect.
apply (H3 v v' vval t nil tau1 tau2); subst; trivial.
intros; assumption.
generalize (mem_bool_ok _ _ eq_var_bool_ok v varl); case (mem_bool eq_var_bool v varl).
intro v_mem_varl; assert (v_in_varl : In v varl).
apply mem_impl_in with (@eq _); trivial.
assert (Acc_vval :  Interp_dom vval).
generalize (Acc_tau _ v_in_varl); simpl; rewrite eq_var_bool_refl; exact (fun p => p).
destruct (interp_defined _ (interp_well_defined _ Acc_vval)) as [vval' K].
exists ((v,(vval,vval')) :: tau'); split.
simpl; rewrite K1; apply eq_refl.
intros x t t' x_in_varl [x_eq_v | xtt'_in_tau']; [injection x_eq_v; intros; subst; assumption | apply (K2 x); assumption].
intro v_not_in_varl; exists ((v,(vval,vval)) :: tau'); split.
simpl; rewrite K1; apply eq_refl.
intros x t t' x_in_varl [x_eq_v | xtt'_in_tau']; 
[ injection x_eq_v; intros; subst; apply False_rect; apply v_not_in_varl; apply in_impl_mem; trivial
| apply (K2 x); assumption].
destruct H4 as [tau' [H4 H5]].
exists (map (fun xtt' => match xtt' with (x,(t,t')) => (x,t') end) tau').
intros x x_in_varl; simpl; rewrite (H1 x).
rewrite H4.
generalize (find_map eq_var_bool (fun y : (term * term) => fst y) x tau')
                 (find_map eq_var_bool (fun y : (term * term) => snd y) x tau')
                 (find_mem _ _  eq_var_bool_ok x tau').
rewrite (map_eq (fun xval0 : variable * (term * term) => (fst xval0, fst (snd xval0)))
                               (fun xtt' : variable * (term * term) => let (x0, y) := xtt' in let (t, _) := y in (x0, t)) 
                               tau'
                               (fun xtt' _ => match xtt' with (x,(t,_)) => eq_refl (x,t) end)).
rewrite (map_eq (fun xval0 : variable * (term * term) => (fst xval0, snd (snd xval0)))
                               (fun xtt' : variable * (term * term) => let (x0, y) := xtt' in let (_, t'0) := y in (x0, t'0)) 
                               tau'
                               (fun xtt' _ => match xtt' with (x,(_,t')) => eq_refl (x,t') end)).
case (find eq_var_bool x tau').
intros [xval xval']; simpl.
intros K1 K2 K3; rewrite K1, K2.
destruct (K3 _ (eq_refl _)) as [x' [tau1 [tau2 [K4 K5]]]].
subst x'; apply (H5 x); trivial.
subst tau'; apply in_or_app; right; left; apply eq_refl.
intros K1 K2 _; rewrite K1, K2; apply Vcase.
Qed.

Lemma Hclosed : forall f g, ~G f -> symb_sup R f g -> ~G g.
Proof.
intros f g Hf H Gg; apply Hf.
rewrite Gdef' in Gg; rewrite Gdef'.
inversion Gg as [g' l t [K1 K2]]; clear Gg; subst g'.
destruct H as [v [u [[J1 J2] [J3 J4]]]].
destruct u as [x | f' k].
contradiction.
subst f'.
constructor 1 with k v; split.
assumption.
intros [x [y [H1 [H2 [f' [H3 H4]]]]]]; apply K2.
exists x; exists y; split; [ | split].
assumption.
assumption.
exists f'; split.
assumption.
apply refl_trans_clos_is_trans with f.
assumption.
right; left.
constructor 1 with v.
exists (Term f k); split; split.
assumption.
apply eq_refl.
assumption.
assumption.
Qed.

Lemma rwr_at_top_H :
  forall l r, R r l -> (match l with Var _ => False | Term g _ => ~G g end) ->
  forall sigma,  Interp_dom (apply_subst sigma r) -> Interp_dom (apply_subst sigma l) ->
  forall s' t', Interp (apply_subst sigma l) s' -> Interp (apply_subst sigma r) t' -> 
  rwr (union _ (fun r' l' => In (r',l') ((r,l) :: nil))  (Pi pi V0 V1)) t' s'.
Proof.
intros l r K K' sigma Acc_rs Acc_ls s' t' Il Ir.
destruct (interp_subst l sigma Acc_ls) as [sigma' Isigma].
assert (K'' : t' = apply_subst sigma' r).
apply interp_unicity with (apply_subst sigma r); trivial.
apply interp_well_defined; assumption.
apply interp_in_H.
destruct l as [ | f k].
contradiction.
intros g g_in_r.
destruct (Gdec _ _ Rlist_ok _ _ Plist_ok g) as [not_Gg | Gg].
rewrite Gdef'; assumption.
apply Hclosed with f; trivial.
constructor 1 with r; exists (Term f k); split.
constructor 1; trivial.
split; [ | apply Gdef].
assumption.
rewrite Gdef'; assumption.
intros x x_in_r; apply Isigma; apply R_reg with r; trivial.
subst t'; assert (K'' := proj1 (rwr_interp_subst _ _ Acc_ls _ sigma' Il Isigma)).
inversion K''; clear K''; subst.
left; left; constructor; do 2 left; apply eq_refl.
apply trans_clos_is_trans with (apply_subst sigma' l).
left; left; constructor; do 2 left; apply eq_refl.
apply trans_incl with (one_step (Pi pi V0 V1)); trivial.
refine (one_step_incl _ _ _); intros; right; assumption.
Qed.

Lemma rwr_at_top_not_H :
  forall l r, R r l -> (match l with Var _ => False | Term g _ => G g end) ->
  forall sigma, Interp_dom (apply_subst sigma l) -> Interp_dom (apply_subst sigma r) ->
  forall s' t', Interp (apply_subst sigma l) s' -> Interp (apply_subst sigma r) t' -> 
  rwr (Pi pi V0 V1) t' s'.
Proof.
intros l r K K' sigma Acc_ls Acc_rs s' t' Il Ir.
destruct l as [ | f l].
contradiction.
simpl in Il; inversion Il; clear Il; subst.
absurd (G f); assumption.
apply project_comb; right.
rewrite in_map_iff; exists (apply_subst sigma r, t'); split; trivial.
assert (rs_in_kk : In (apply_subst sigma r) (map (fun st : term * term => fst st) kk)).
rewrite <- H5; rewrite FB; left; apply (instance R r (Term f l) sigma); assumption.
rewrite in_map_iff in rs_in_kk.
destruct rs_in_kk as [[rs t''] [K1 K2]]; simpl in K1; subst.
assert (Acc_rs' : Acc interp_call (apply_subst sigma r)).
apply interp_well_defined; trivial.
rewrite (interp_unicity (apply_subst sigma r) Acc_rs' t' t''); trivial.
apply H8; assumption.
Qed.

Lemma rwr_not_H :
  forall l r, R r l -> 
  forall s t, Interp_dom s -> Interp_dom t ->
  (match s with Var _ => False | Term g _ => G g end) ->
  one_step (fun r' l' => In (r',l') ((r,l) :: nil)) t s ->
  forall s' t', Interp s s' -> Interp t t' -> 
  rwr (Pi pi V0 V1) t' s'.
Proof.
intros l r K s; pattern s; apply term_rec3; clear s.
intros; contradiction.
intros f k IH t Acc_s Acc_t K' K'' s' t' Is It.
inversion K''; clear K''; intros; subst.
(* 1/2 rewriting at top *)
inversion H; clear H; subst.
destruct H2 as [H2 | H2]; [injection H2; clear H2; intros; subst | contradiction].
apply rwr_at_top_not_H with t2 t1 sigma; trivial.
destruct t2 as [x2 | f2 l2]; simpl in K'.
apply (R_var _ _ K).
injection H0; clear H0; intros; subst; assumption.
rewrite H0; assumption.
rewrite H0; assumption.
(* 1/1 rewriting in context *)
inversion Is; clear Is.
(* 1/2 f in H *)
subst; absurd (G f); assumption.
(* 1/1 f not in H *)
subst f0 l0 s'.
assert (fl1_in_kk : In (Term f l1) (map (fun st : term * term => fst st) kk)).
rewrite <- H6, FB.
apply one_step_incl with (fun r' l' : term => In (r', l') ((r, l) :: nil)).
intros t1 t2 [t1t2_eq_rl | t1t2_in_nil]; [injection t1t2_eq_rl; intros; subst; assumption | contradiction].
apply in_context; assumption.
apply project_comb; right; subst k'; rewrite in_map_iff in fl1_in_kk.
destruct fl1_in_kk as [[fl1 t''] [fl1_eq_fl1 fl1_in_kk]].
simpl in fl1_eq_fl1; subst fl1.
rewrite in_map_iff; exists (Term f l1, t''); split; trivial.
simpl; apply (interp_unicity (Term f l1)); trivial.
apply interp_well_defined; assumption.
apply H9; trivial.
Qed.

Lemma rwr_rule_not_H :
  forall l r, R r l -> (match l with Var _ => False | Term g _ => G g end) ->
  forall s t, Interp_dom s -> Interp_dom t ->
  one_step (fun r' l' => In (r',l') ((r,l) :: nil)) t s ->
  forall s' t', Interp s s' -> Interp t t' -> 
  rwr (Pi pi V0 V1) t' s'.
Proof.
intros l r K K' s; pattern s; apply term_rec3; clear s.
intros v t _ _ K''; inversion K''; clear K''; subst.
inversion H; inversion H; subst.
destruct H5 as [H5 | H5]; [injection H5; clear H5; intros; subst | contradiction].
destruct t3 as [x3 | ]; [contradiction | discriminate].
intros f k IH t Acc_s Acc_t K'' s' t' Is It.
inversion K''; clear K''; intros; subst.
(* 1/2 rewriting at top *)
inversion H; clear H; subst.
destruct H2 as [H2 | H2]; [injection H2; clear H2; intros; subst | contradiction].
apply rwr_at_top_not_H with t2 t1 sigma; trivial.
rewrite H0; assumption.
rewrite H0; assumption.
(* 1/1 rewriting in context *)
inversion Is; clear Is.
(* 1/2 f in H *)
inversion It; clear It.
subst; apply general_context.
destruct (one_step_in_list H1) as [u [u' [l1 [l2 [K1 [K2 K3]]]]]].
destruct (split_map_set _ _ _ _ K2) as [ll1 [[ | [u1 u2] ll2] [K4 [K5 K6]]]]; clear K2.
discriminate.
destruct (split_map_set _ _ _ _ K3) as [ll3 [[ | [u3 u4] ll4] [K7 [K8 K9]]]]; clear K3.
discriminate.
simpl in K6; injection K6; clear K6; intros K10 K11; subst.
simpl in K9; injection K9; clear K9; intros K10 K11; subst.
do 2 rewrite map_app; simpl.
assert (ll1_eq_ll3 : ll1 = ll3).
assert (Aux : forall t t' t'', In (t,t') ll1 -> In (t,t'') ll3 -> t' = t'').
intros t t' t'' tt'_in_ll1 tt''_in_ll3; apply (interp_unicity t).
apply interp_well_defined.
destruct (In_split _ _ tt'_in_ll1) as [lll1 [lll2 H15]].
apply interp_dom_subterm with
            (Term f
               (map (fun st : term * term => fst st) (ll1 ++ (u, u2) :: ll2)))
            (length lll1 :: nil); trivial.
subst ll1; simpl; rewrite <- app_assoc; rewrite map_app.
rewrite <- (length_map (fun st : term * term => fst st) lll1).
simpl; rewrite nth_error_at_pos; apply eq_refl.
apply H6; apply in_or_app; left; trivial.
apply H13; apply in_or_app; left; trivial.
revert K8 Aux; clear; revert ll3; induction ll1 as [ | [a1 a2] ll1]; intros [ | [b1 b2] ll3] K8 Aux.
apply eq_refl.
discriminate.
discriminate.
simpl in K8; injection K8; clear K8; intros; subst.
rewrite (Aux a1 a2 b2 (or_introl _ (eq_refl _)) (or_introl _ (eq_refl _))); rewrite (IHll1 ll3); trivial.
intros t t' t'' H1 H2; apply (Aux t); right; assumption.
assert (ll2_eq_ll4 : ll2 = ll4).
assert (Aux : forall t t' t'', In (t,t') ll2 -> In (t,t'') ll4 -> t' = t'').
intros t t' t'' tt'_in_ll2 tt''_in_ll4; apply (interp_unicity t).
apply interp_well_defined.
destruct (In_split _ _ tt'_in_ll2) as [lll1 [lll2 H15]].
apply interp_dom_subterm with
            (Term f
               (map (fun st : term * term => fst st) (ll1 ++ (u, u2) :: ll2)))
            (length (ll1 ++ (u,u2) :: lll1) :: nil); trivial.
subst ll2; simpl; rewrite app_comm_cons; rewrite app_assoc; rewrite map_app.
rewrite <- (length_map (fun st : term * term => fst st) (ll1 ++ (u,u2) :: lll1)).
simpl; rewrite nth_error_at_pos; apply eq_refl.
apply H6; apply in_or_app; do 2 right; trivial.
apply H13; apply in_or_app; do 2 right; trivial.
revert K10 Aux; clear; revert ll4; induction ll2 as [ | [a1 a2] ll2]; intros [ | [b1 b2] ll4] K10 Aux.
apply eq_refl.
discriminate.
discriminate.
simpl in K10; injection K10; clear K10; intros; subst.
rewrite (Aux a1 a2 b2 (or_introl _ (eq_refl _)) (or_introl _ (eq_refl _))); rewrite (IHll2 ll4); trivial.
intros t t' t'' H1 H2; apply (Aux t); right; assumption.
subst ll3 ll4.
unfold rwr_list; rewrite rwr_list_expand_strong; 
exists u2; exists u4;
exists (map (fun st : term * term => snd st) ll1);
exists (map (fun st : term * term => snd st) ll2);
exists (map (fun st : term * term => snd st) ll2).
split.
apply eq_refl.
split.
apply eq_refl.
split.
apply IH with u u'.
rewrite map_app; apply in_or_app; right; left; apply eq_refl.
apply interp_dom_subterm with
            (Term f
               (map (fun st : term * term => fst st) (ll1 ++ (u, u2) :: ll2)))
            (length ll1 :: nil); trivial.
rewrite map_app.
rewrite <- (length_map (fun st : term * term => fst st) ll1).
simpl; rewrite nth_error_at_pos; apply eq_refl.
apply interp_dom_subterm with
            (Term f
               (map (fun st : term * term => fst st) (ll1 ++ (u', u4) :: ll2)))
            (length ll1 :: nil); trivial.
rewrite map_app.
rewrite <- (length_map (fun st : term * term => fst st) ll1).
simpl; rewrite nth_error_at_pos; apply eq_refl.
assumption.
apply H6; apply in_or_app; right; left; apply eq_refl.
apply H13; apply in_or_app; right; left; apply eq_refl.
left.
(* 1/2 *)
absurd (G f); assumption.
(* 1/1 f not in H *)
subst f0 l0 s'.
assert (fl1_in_kk : In (Term f l1) (map (fun st : term * term => fst st) kk)).
rewrite <- H6, FB.
apply one_step_incl with (fun r' l' : term => In (r', l') ((r, l) :: nil)).
intros t1 t2 [t1t2_eq_rl | t1t2_in_nil]; [injection t1t2_eq_rl; intros; subst; assumption | contradiction].
apply in_context; assumption.
apply project_comb; right; subst k'; rewrite in_map_iff in fl1_in_kk.
destruct fl1_in_kk as [[fl1 t''] [fl1_eq_fl1 fl1_in_kk]].
simpl in fl1_eq_fl1; subst fl1.
rewrite in_map_iff; exists (Term f l1, t''); split; trivial.
simpl; apply (interp_unicity (Term f l1)); trivial.
apply interp_well_defined; trivial.
apply H9; trivial.
Qed.

Lemma rwr_rule_H :
  forall l r, R r l -> (match l with Var _ => False | Term g _ => ~G g end) -> 
  forall s t, Interp_dom s -> Interp_dom t ->
  one_step (fun r' l' => In (r',l') ((r,l) :: nil)) t s ->
  forall s' t', Interp s s' -> Interp t t' -> 
  rwr (union _ (fun r' l' => In (r',l') ((r,l) :: nil)) (Pi pi V0 V1)) t' s'.
Proof.
intros l r K K' s; pattern s; apply term_rec3; clear s.
intros v t _ _ K''; inversion K''; clear K''; subst.
inversion H; inversion H; subst.
destruct H5 as [H5 | H5]; [injection H5; clear H5; intros; subst | contradiction].
destruct t3 as [x3 | ]; [contradiction | discriminate].
intros f k IH t Acc_s Acc_t K'' s' t' Is It.
inversion K''; clear K''; intros; subst.
(* 1/2 rewriting at top *)
inversion H; clear H; subst.
destruct H2 as [H2 | H2]; [injection H2; clear H2; intros; subst | contradiction].
apply rwr_at_top_H with sigma; trivial.
rewrite H0; assumption.
rewrite H0; assumption.
(* 1/1 rewriting in context *)
inversion Is.
(* 1/2 f in H *)
inversion It; clear Is It.
subst; apply general_context.
destruct (one_step_in_list H1) as [u [u' [l1 [l2 [K1 [K2 K3]]]]]].
destruct (split_map_set _ _ _ _ K2) as [ll1 [[ | [u1 u2] ll2] [K4 [K5 K6]]]]; clear K2.
discriminate.
destruct (split_map_set _ _ _ _ K3) as [ll3 [[ | [u3 u4] ll4] [K7 [K8 K9]]]]; clear K3.
discriminate.
simpl in K6; injection K6; clear K6; intros K10 K11; subst.
simpl in K9; injection K9; clear K9; intros K10 K11; subst.
do 2 rewrite map_app; simpl.
assert (ll1_eq_ll3 : ll1 = ll3).
assert (Aux : forall t t' t'', In (t,t') ll1 -> In (t,t'') ll3 -> t' = t'').
intros t t' t'' tt'_in_ll1 tt''_in_ll3; apply (interp_unicity t).
apply interp_well_defined.
destruct (In_split _ _ tt'_in_ll1) as [lll1 [lll2 H15]].
apply interp_dom_subterm with
            (Term f
               (map (fun st : term * term => fst st) (ll1 ++ (u, u2) :: ll2)))
            (length lll1 :: nil); trivial.
subst ll1; simpl; rewrite <- app_assoc; rewrite map_app.
rewrite <- (length_map (fun st : term * term => fst st) lll1).
simpl; rewrite nth_error_at_pos; apply eq_refl.
apply H6; apply in_or_app; left; trivial.
apply H13; apply in_or_app; left; trivial.
revert K8 Aux; clear; revert ll3; induction ll1 as [ | [a1 a2] ll1]; intros [ | [b1 b2] ll3] K8 Aux.
apply eq_refl.
discriminate.
discriminate.
simpl in K8; injection K8; clear K8; intros; subst.
rewrite (Aux a1 a2 b2 (or_introl _ (eq_refl _)) (or_introl _ (eq_refl _))); rewrite (IHll1 ll3); trivial.
intros t t' t'' H1 H2; apply (Aux t); right; assumption.
assert (ll2_eq_ll4 : ll2 = ll4).
assert (Aux : forall t t' t'', In (t,t') ll2 -> In (t,t'') ll4 -> t' = t'').
intros t t' t'' tt'_in_ll2 tt''_in_ll4; apply (interp_unicity t).
apply interp_well_defined.
destruct (In_split _ _ tt'_in_ll2) as [lll1 [lll2 H15]].
apply interp_dom_subterm with
            (Term f
               (map (fun st : term * term => fst st) (ll1 ++ (u, u2) :: ll2)))
            (length (ll1 ++ (u,u2) :: lll1) :: nil); trivial.
subst ll2; simpl; rewrite app_comm_cons; rewrite app_assoc; rewrite map_app.
rewrite <- (length_map (fun st : term * term => fst st) (ll1 ++ (u,u2) :: lll1)).
simpl; rewrite nth_error_at_pos; apply eq_refl.
apply H6; apply in_or_app; do 2 right; trivial.
apply H13; apply in_or_app; do 2 right; trivial.
revert K10 Aux; clear; revert ll4; induction ll2 as [ | [a1 a2] ll2]; intros [ | [b1 b2] ll4] K10 Aux.
apply eq_refl.
discriminate.
discriminate.
simpl in K10; injection K10; clear K10; intros; subst.
rewrite (Aux a1 a2 b2 (or_introl _ (eq_refl _)) (or_introl _ (eq_refl _))); rewrite (IHll2 ll4); trivial.
intros t t' t'' H1 H2; apply (Aux t); right; assumption.
subst ll3 ll4.
unfold rwr_list; rewrite rwr_list_expand_strong; 
exists u2; exists u4;
exists (map (fun st : term * term => snd st) ll1);
exists (map (fun st : term * term => snd st) ll2);
exists (map (fun st : term * term => snd st) ll2).
split.
apply eq_refl.
split.
apply eq_refl.
split.
apply IH with u u'.
rewrite map_app; apply in_or_app; right; left; apply eq_refl.
apply interp_dom_subterm with
            (Term f
               (map (fun st : term * term => fst st) (ll1 ++ (u, u2) :: ll2)))
            (length ll1 :: nil); trivial.
simpl; rewrite map_app.
rewrite <- (length_map (fun st : term * term => fst st) ll1).
simpl; rewrite nth_error_at_pos; apply eq_refl.
apply interp_dom_subterm with
            (Term f
               (map (fun st : term * term => fst st) (ll1 ++ (u', u4) :: ll2)))
            (length ll1 :: nil); trivial.
simpl; rewrite map_app.
rewrite <- (length_map (fun st : term * term => fst st) ll1).
simpl; rewrite nth_error_at_pos; apply eq_refl.
assumption.
apply H6; apply in_or_app; right; left; apply eq_refl.
apply H13; apply in_or_app; right; left; apply eq_refl.
left.
(* 1/2 *)
absurd (G f); assumption.
(* 1/1 f not in H *)
subst f0 l0 s'.
apply trans_incl with (one_step  (Pi pi V0 V1)).
do 2 intro; apply one_step_incl; intros; right; assumption.
apply (rwr_not_H _ _ K (Term f k) (Term f l1)); trivial.
apply in_context; assumption.
Qed.

Lemma rwr_rule_H_not_H :
  forall s t, Interp_dom s -> Interp_dom t ->
  one_step R t s ->
  forall s' t', Interp s s' -> Interp t t' -> 
  rwr (union _ (UsableRules R P) (Pi pi V0 V1)) t' s'.
Proof.
intros s t Acc_s Acc_t K s' t' Is It.
destruct (split_rules _ _ Rlist_ok _ _ Plist_ok R_var G Gdef') as [U1 U2].
assert (Erule := one_step_one_rule R _ _ K).
destruct Erule as [r [l [K1 K2]]].
destruct l as [x | f l].
apply False_rect; apply (R_var _ _ K1).
destruct (Gdec _ _ Rlist_ok _ _ Plist_ok f) as [f_in_H | f_not_in_H].
apply trans_incl with
  (one_step (union term (fun r' l' : term => In (r', l') ((r, Term f l) :: nil))
      (Pi pi V0 V1))).
intros x y; apply one_step_incl; clear x y.
intros x y [[K3 | Abs] | K3].
injection K3; clear K3; intros; subst x y; left.
rewrite U1 in K1; destruct K1 as [K1 | K1].
assumption.
destruct K1 as [_ K1]; apply False_rect; apply f_in_H;
rewrite <- Gdef'; assumption.
contradiction.
right; assumption.
rewrite <- Gdef' in f_in_H.
apply (rwr_rule_H _ _ K1 f_in_H _ _ Acc_s Acc_t K2 _ _ Is It).
apply trans_incl with (one_step (Pi pi V0 V1)).
intros x y; apply one_step_incl; clear x y.
intros x y K3; right; assumption.
rewrite <- Gdef' in f_not_in_H.
apply (rwr_rule_not_H _ _ K1 f_not_in_H _ _ Acc_s Acc_t K2 _ _ Is It).
Qed.

Lemma trans_rwr_rule_H_not_H :
  forall s t, Acc (one_step R) s ->
  trans_clos (one_step R) t s ->
  forall s' t', Interp s s' -> Interp t t' -> 
  rwr (union _ (UsableRules R P) (Pi pi V0 V1)) t' s'.
Proof.
intros s t Acc_s' K; induction K as [t1 t2 K | t1 t2 t3 K1 K2].
apply rwr_rule_H_not_H; trivial.
apply acc_one_step_interp_dom; assumption.
apply acc_one_step_interp_dom; apply Acc_inv with t2; assumption.
intros t3' t1' I3 I1.
assert (Acc_t2 : Interp_dom t2).
apply acc_one_step_interp_dom; apply Acc_incl with (trans_clos (one_step R)).
do 3 intro; left; assumption.
apply Acc_inv with t3; trivial.
apply acc_trans; assumption.
destruct (interp_defined _ (interp_well_defined _ Acc_t2)) as [t2' I2].
apply trans_clos_is_trans with t2'.
apply rwr_rule_H_not_H with t2 t1; trivial.
apply acc_one_step_interp_dom; apply Acc_incl with (trans_clos (one_step R)).
do 3 intro; left; assumption.
apply Acc_inv with t3.
apply acc_trans; assumption.
right with t2; assumption.
apply IHK2; trivial.
Qed.

Lemma interp_dom_interp_dom_1 :
  forall f l1 l2, ~G f -> acc_sub R (Term f l1) -> refl_trans_clos (one_step_list (one_step R)) l2 l1 -> Interp_dom (Term f l2).
Proof.
intros f l1 l2 f_in_H Acc_l1 K1.
intros [ | i q] g l Sub g_not_in_H.
injection Sub; clear Sub; intros; subst; apply False_rect; apply f_in_H; assumption.
simpl in Sub.
generalize (nth_error_ok_in i l2); 
destruct (nth_error l2 i) as [ai | ]; [idtac | discriminate].
intro K; destruct (K _ (eq_refl _)) as [l2' [l2'' [L K']]]; clear K.
apply acc_subterms_3 with q ai; trivial.
apply rwr_sub_acc_sub_acc_sub with l1 l2; trivial.

subst l2; apply in_or_app; right; left; apply eq_refl.
Qed.

Lemma head_P_in_H :
  forall mark,
  (forall u v, P v u -> mrel mark (dp R) v u) ->
  forall t1 t2 sigma f l, P t1 t2 -> apply_subst sigma t1 = Term f l -> ~G f.
Proof.
intros mark P_in_dpR t1 t2 sigma f l K1 K2 K3.
rewrite Gdef' in K3; inversion K3 as [f' k t [K4 K5]]; subst f'.
apply K5.
constructor 1 with t1; exists t2; split.
assumption.
split.
assumption.
exists f; split.
destruct t1 as [x | f' l'].
assert (_D := P_in_dpR _ _ K1); inversion _D as [a b D J1 J2].
inversion D; subst; discriminate.
simpl in K2; injection K2; intros; subst f'.
simpl; rewrite eq_symb_bool_refl; apply eq_refl.
left.
Qed.

Lemma interp_dom_interp_dom_2 :
  forall mark, (forall v u, P u v -> mrel mark (dp R) u v) ->
  forall s t, acc_sub R s -> acc_sub R t ->  rdp_step (axiom P) R t s -> Interp_dom s -> Interp_dom t.
Proof.
intros mark P_in_dpR s t Acc_sub_s Acc_sub_t K Is.
inversion K as [_f ls l H1 H2]; clear K; subst.
inversion H as [_t _fl sigma K1 K2 K3]; clear H; subst.
assert (_K := P_in_dpR _ _ K1).
inversion _K as [t fk K]; clear _K; subst.
destruct fk as [x | f k].
inversion K; subst; apply False_rect; apply (R_var _ _ H).
injection K3; clear K3; intros; subst.
inversion K as [u v p f2 l2 H Sub Df2]; subst.
assert (f2_in_H : ~G (mark f2)).
apply (head_P_in_H mark P_in_dpR _ _ nil (mark f2) l2 K1).
rewrite empty_subst_is_id; apply eq_refl.
intros [ | i q] g k' Sub' g_not_in_H.
simpl in Sub'; injection Sub'; clear Sub'; intros; subst; apply False_rect; apply f2_in_H; assumption.
simpl in Sub'.
generalize (nth_error_ok_in i (map (apply_subst sigma) l2)); 
destruct (nth_error (map (apply_subst sigma) l2) i) as [ai | ]; [idtac | discriminate].
intro K'; destruct (K' _ (eq_refl _)) as [l2' [l2'' [L K'']]]; clear K'.
apply acc_subterms_3 with q ai; trivial.
apply Acc_sub_t; simpl; rewrite K''; apply in_or_app; right; left; apply eq_refl.
Qed.

Lemma pi_in_H : ~G pi.
Proof.
rewrite Gdef'; intro Dpi; inversion Dpi as [f l t [H1 H2]]; subst f.
apply (proj2 (PPi t (Term pi l) H1 pi)).
simpl; rewrite eq_symb_bool_refl; apply eq_refl.
apply eq_refl.
Qed.

Lemma Q8_weak :
  forall mark,
  (forall f, ~defined R (mark f)) ->
  (forall v u, P u v -> mrel mark (dp R) u v) -> 
  forall s, Interp_dom s ->
  forall s', Interp s s' -> Acc (rdp_step (axiom P) (union _  (UsableRules R P) (Pi pi V0 V1))) s' -> 
              Acc (rest (acc_sub R) (rdp_step (axiom P) R)) s.
Proof.
intros mark mark_ok P_in_dpR.
assert (acc_rdp_var : 
         forall x, Acc (rest (acc_sub R) (rdp_step (axiom P) R)) (Var x)).
intros x; apply Acc_intro; intros s [H _].
inversion H as [f l1 l2 t3 H1 H2]; subst.

intros s Acc_s s' Is Acc_s'; revert s Acc_s Is.
induction Acc_s' as [s' Acc_s'' IH].
assert (Acc_s' : Acc (rdp_step (axiom P) (union _  (UsableRules R P) (Pi pi V0 V1))) s').
apply Acc_intro; exact Acc_s''.
clear Acc_s''.
intros s Acc_s Is.
destruct s as [x | f ls].
apply acc_rdp_var.
destruct (Gdec _ _ Rlist_ok _ _ Plist_ok f) as [f_in_H | f_not_in_H]; 
[ rewrite <- Gdef' in f_in_H
| rewrite <- Gdef' in f_not_in_H].
apply Acc_intro; intros t [K [Acc_sub_t  Acc_sub_s]].
assert (Acc_t := interp_dom_interp_dom_2 mark P_in_dpR _ _ Acc_sub_s Acc_sub_t K Acc_s).
destruct (interp_defined _ (interp_well_defined _ Acc_t)) as [t' It].
apply IH with t'; trivial.
inversion K as [_f _ls l H1 H2 H3 H4 H5]; clear K; subst.
inversion H3 as [_v _fl sigma H1 H4 H5']; clear H3; subst.
assert (_K := P_in_dpR _ _ H1).
inversion _K as [v fl K]; subst.
inversion K as [fl' r p g lv H0 Sub Dg]; clear K; subst.
inversion Is as [ | f' _ls ls' lls _ H8 H9 Ills | ]; 
[subst f' _ls s' | absurd (G f); assumption].
assert (g_in_H := head_P_in_H mark P_in_dpR _ _ sigma _ _ H1 (eq_refl _)).
inversion It as [ |  g' lt lt' llt _ H4 H5 Illt | ]; [ subst g' t' | absurd (G (mark g)); assumption].

assert (Acc_fl := interp_dom_interp_dom_1 _ _ _ f_in_H Acc_sub_s H2).
rewrite <- H5' in Acc_fl; destruct (interp_subst _ sigma Acc_fl) as [sigma' Isigma].
destruct (interp_defined _ (interp_well_defined _ Acc_fl)) as [fl' Ifl].
rewrite H5' in Ifl; inversion Ifl as [ | f' _l l' ll _ H10 H11 Ill | ]; [subst f' _l fl' | absurd (G f); assumption].
apply rwr_subterm_rdp_rdp with l'.
subst; revert Ills Ill Acc_sub_s H2; clear -R_reg Rlist_ok P Plist Plist_ok Gdef' V0_diff_V1 R_var; revert ll.
induction lls as [ | [s s'] lls]; intros [ | [u u'] ll] Ills Ill Acc_sub_s K.
left.
generalize (refl_trans_clos_one_step_list_length_eq K); intro; discriminate.
generalize (refl_trans_clos_one_step_list_length_eq K); intro; discriminate.
simpl in K; rewrite refl_trans_clos_one_step_list_head_tail in K.
destruct K as [K1 K2].
simpl; rewrite refl_trans_clos_one_step_list_head_tail; split.
assert (Acc_s : Acc (one_step R) s).
apply Acc_sub_s; left; apply eq_refl.
inversion K1; subst.
assert (Acc_s' : Acc interp_call s).
apply interp_well_defined; apply acc_one_step_interp_dom; assumption.
rewrite (interp_unicity s Acc_s' s' u').
left.
apply Ills; left; apply eq_refl.
apply Ill; left; apply eq_refl.
right; apply trans_rwr_rule_H_not_H with s u; trivial.
apply Ills; left; apply eq_refl.
apply Ill; left; apply eq_refl.
apply IHlls; trivial.
intros; apply Ills; right; assumption.
intros; apply Ill; right; assumption.
do 2 intro; apply Acc_sub_s; right; assumption.
assert (Acc_sub : acc_sub R (Term f l)).
unfold acc_sub; apply (rwr_sub_acc_sub_acc_sub R _ _ H2 Acc_sub_s).

rewrite <- H5' in Ifl.
generalize (rwr_interp_subst _ _ Acc_fl (Term f l') sigma' Ifl Isigma).
destruct fl as [x | _f _l].
apply False_rect; apply (R_var _ _ H0).
simpl in H5'; injection H5'; intros; subst f.
apply rwr_subterm_rdp_rdp with  (map (apply_subst sigma') _l).
destruct H7 as [_ H7].
generalize (H7 f_in_H); clear H7; intros [_ H7].
apply refl_trans_incl with (one_step_list (one_step (Pi pi V0 V1))); trivial.
do 2 intro; apply one_step_list_incl.
do 2 intro; apply one_step_incl.
do 3 intro; right; assumption.
assert (t'_eq_glvs' : Term (mark g) lt' = apply_subst sigma' (Term (mark g) lv)).
apply (interp_unicity _ (interp_well_defined _ Acc_t)); trivial.
apply interp_in_H.
intros g' g'_glv.
rewrite symb_in_term_unfold in g'_glv.
generalize (eq_symb_bool_ok g' (mark g)); destruct (eq_symb_bool g' (mark g)).
intro; subst g'; assumption.
simpl in g'_glv; intros _.
rewrite Gdef'.
intro Dg'; inversion Dg' as [g'' k t [K K']]; subst g''; apply K'.
exists (mark_term mark (Term g lv));
exists (mark_term mark (Term _f _l)); split; [ | split]; trivial.
exists g'; split; [ | left].
rewrite symb_in_term_unfold; simpl; rewrite g'_glv.
destruct (eq_symb_bool g' (mark g)); apply eq_refl.
intros x x_in_lv; apply Isigma.
apply (R_reg _ _ H0 x).
apply var_in_subterm with (Term g lv) p; trivial.
rewrite t'_eq_glvs'.
apply Rdp_step with (map (apply_subst sigma') _l).
left.
apply (instance P (Term (mark g) lv) (Term (mark _f) _l) sigma'); trivial.


apply Acc_intro; intros s [H _]; inversion H; clear H; subst.
inversion H4 as [_t1 _t2 sigma]; clear H4; subst.
assert (_K1 := P_in_dpR _ _ H).
inversion _K1 as [t1 t2 K1]; subst.
inversion K1; clear K1; subst.
destruct t2 as [x2 | g2 k2].
apply False_rect; apply (R_var _ _ H0).
simpl in H1; injection H1; clear H1; intros; subst.
rewrite Gdef' in f_not_in_H.
apply False_rect; apply (mark_ok g2).
inversion f_not_in_H as [g2' l t [H' _]].
constructor 1 with l t; assumption.
Qed.

Lemma Q8_strong :
  forall mark,
  (forall f, ~defined R (mark f)) ->
  (forall v u, P u v -> mrel mark (dp R) u v) -> 
  well_founded (rdp_step (axiom P) (union _  (UsableRules R P) (Pi pi V0 V1))) ->
  well_founded  (rest (acc_sub R) (rdp_step (axiom P) R)).
Proof.
intros mark mark_ok P_in_dpR Wf t.
apply Acc_intro; intros s H; apply Acc_inv with t; trivial.
destruct H as [H [_ Ht]].
inversion H as [f l1 l2 s' H1 H2 H3 H4]; clear H; subst.
inversion H2 as [_t1 _t2 sigma _H2]; clear H2; subst.
assert (_K2 := P_in_dpR _ _ _H2).
inversion _K2 as [t1 t2 K2]; clear _K2; subst.
inversion K2 as [u1 u2 p f2 k2 H Sub Df2]; subst.
destruct t2 as [x2 | g2].
apply False_rect; apply (R_var _ _ H).
simpl in H0; injection H0; clear H0; intros; subst.
assert (Acc_t : Interp_dom (Term (mark g2) l1)).
intros [ | i q] f k Sub' Gf.
simpl in Sub'; injection Sub'; clear Sub'; intros; subst.
rewrite Gdef' in Gf.
inversion Gf as [f l' t [K _]]; subst.
apply False_rect; apply (mark_ok g2); constructor 1 with l' t; assumption.
simpl in Sub'.
generalize (nth_error_ok_in i l1).
destruct (nth_error l1 i) as [ai | ]; [ | discriminate].
intro K; destruct (K _ (eq_refl _)) as [kk1 [kk2 [L K1]]]; clear K.
apply acc_subterms_3 with q ai; trivial.
apply Ht; subst l1; simpl; apply in_or_app; right; left; apply eq_refl.
destruct (interp_defined (Term (mark g2) l1)) as [t' It].
apply interp_well_defined; assumption.
apply Q8_weak with mark t'; trivial.
Qed.

End Interp_definition.

End MakeUsableDP.

