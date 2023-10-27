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


(** * Termination of rewriting *)

From Coq Require Import List Relations Wellfounded Arith Recdef Setoid.
From CoLoR Require Import closure more_list weaved_relation term equational_theory_spec
     dp.

Module MakeModDP (E : EqTh).

  Module Dp := dp.MakeDP (E).
  Import Dp.
  Import E.
  Import T.

(** Interpretation *)
Inductive interp_call R1 R2 : term -> term -> Prop :=
  | Constr : forall f1 l t, ~defined R2 f1 -> In t l -> interp_call R1 R2 t (Term f1 l)
  | Defd : forall f2 l t, defined R2 f2 -> 
            one_step (union _ R1 R2) t (Term f2 l) -> interp_call R1 R2 t (Term f2 l).

Definition Interp_dom R1 R2 t :=
  forall p f l, subterm_at_pos t p = Some (Term f l) -> defined R2 f ->
                   Acc (one_step (union _ R1  R2)) (Term f l).

Lemma interp_well_defined_1 :
  forall R1 R2 f1 l, Interp_dom R1 R2 (Term f1 l) -> 
  forall t, In t l -> Interp_dom R1 R2 t.
Proof.
intros R1 R2 f1 l H t t_in_l p f2 k H' Df2.
destruct (In_split _ _ t_in_l) as [l' [l'' H'']]; subst l.
apply (H ((length l') :: p)); trivial.
simpl; rewrite nth_error_at_pos.
trivial.
Qed.

Lemma interp_dom_subterm :
  forall R1 R2 s t p, Interp_dom R1 R2 s -> subterm_at_pos s p = Some t -> Interp_dom R1 R2 t.
Proof.
intros R1 R2 s t p Is Sub q g l Sub' Dg.
apply Is with (p ++ q); trivial.
apply subterm_in_subterm with t; trivial.
Qed.

Lemma acc_one_step_interp_dom :
  forall R1 R2 t, Acc (one_step (union _ R1 R2)) t -> Interp_dom R1 R2 t.
Proof.
intros R1 R2 t Acc_t p f l Sub _.
apply acc_subterms_3 with p t; assumption.
Qed.

Lemma interp_well_defined_2 :
  forall R1 R2 f2 l, Interp_dom R1 R2 (Term f2 l) -> defined R2 f2 ->
  forall (t : term), one_step (union _ R1 R2) t (Term f2 l) -> Interp_dom R1 R2 t.
Proof.
intros R1 R2 f2 l H Df2 t t_R_f2l p f k Sub _.
apply acc_subterms_3 with p t; trivial.
apply Acc_inv with (Term f2 l); trivial.
apply H with (@nil nat); trivial.
Qed.

Lemma interp_well_defined :
  forall R1 R2 t, Interp_dom R1 R2 t -> Acc (interp_call R1 R2) t.
Proof.
intros R1 R2 t; pattern t; apply term_rec3; clear t.
(* 1/2 variable case *)
intros v H; apply Acc_intro; intros s Call_s_t; inversion Call_s_t.
(* 1/1 compound term *)
intros f l IHl H; apply Acc_intro.
intros s Call_s_t; 
inversion Call_s_t as [f1 l' s' not_def_f s_in_l | f2 l' s' def_f s_R_fl]; subst.
(* 1/2 subterm case, top function symbol not defined *)
apply IHl; trivial.
apply interp_well_defined_1 with f l; trivial.
(* 1/1 rewriting step, top function symbol defined *)
apply Acc_inv with (Term f l); trivial.
assert (Acc_fl := H nil f l (eq_refl _) def_f).
revert Acc_fl; generalize (Term f l); clear.
intros t Acc_t; rewrite acc_with_subterm in Acc_t.
induction Acc_t as [t Acc_t' IH]. 
apply Acc_intro.
intros s Call_s_t; inversion Call_s_t as [f1 l s' not_def_f2 s_in_l | f2 l s' def_f2 s_R_fl]; subst.
(* 1/2 direct_subterm *)
apply IH; right; trivial.
(* 1/1 rewriting step *)
apply IH; left; trivial.
Qed.

Lemma interp_dom_subst :
  forall R1 R2 t sigma, Interp_dom R1 R2 (apply_subst sigma t) ->
  forall v, In v (var_list t) -> Interp_dom R1 R2 (apply_subst sigma (Var v)).
Proof.
intros R1 R2 t sigma Itsigma v v_in_t.
destruct (var_in_subterm2 v t) as [p H].
apply in_impl_mem; trivial.
generalize (subterm_at_pos_apply_subst_apply_subst_subterm_at_pos t p sigma).
rewrite H.
apply interp_dom_subterm; trivial.
Qed.

Lemma interp_dom_R1_R2 :
  forall R1 R2, module R1 R2 ->
  (forall f, {defined R2 f}+{~defined R2 f}) ->
  (forall s t, R1 s t -> forall x, In x (var_list s) -> In x (var_list t)) ->
  (forall v t, ~ R2 t (Var v)) ->
  forall (s t : term), Interp_dom R1 R2 s -> 
  one_step (union _ R1 R2) t s -> Interp_dom R1 R2 t.
Proof.
intros R1 R2 module_R1_R2 def_dec R1_reg R2_var s.
pattern s; apply term_rec2; clear s.
intro n; induction n as [ | n]; intros t Size_t.
absurd (1 <= 0); auto with arith.
apply Nat.le_trans with (size t); [apply size_ge_one | assumption].
intros s It H; inversion H as [ t1 s1 H' | f lt ls H']; clear H; subst.
(* 1/2 rewriting step at top *)
inversion H' as [d g sigma [H1 | H2]]; clear H'; subst.
(* 1/3 rewriting step at top by R1 *)
intros p f k Sub Df.
generalize (subterm_in_instantiated_term p d sigma Sub).
case_eq (subterm_at_pos d p).
(* 1/4 d has a subterm u at position p*)
intros [x | f' k'] Sub' K.
(* 1/5 u is a variable x -> x in g, ok *)
rewrite K.
assert (x_in_g := R1_reg _ _ H1 x (var_in_subterm x _ _ Sub' (or_introl _ (eq_refl _)))).
destruct (var_in_subterm2 x g) as [q Sub''].
apply in_impl_mem; trivial.
rewrite <- K; apply (It q); trivial.
generalize (subterm_at_pos_apply_subst_apply_subst_subterm_at_pos g q sigma).
rewrite Sub''; rewrite K; trivial.
(* 1/4 u is a term headed by a symbol f defined in R2 -> impossible *)
injection K; clear K; intros; subst f' k.
inversion module_R1_R2 as [M].
apply False_rect; generalize (M _ _ _ Df H1); simpl; rewrite (symb_in_subterm f _ _ Sub').
discriminate.
simpl; rewrite eq_symb_bool_refl; apply eq_refl.
(* 1/3 d has no subterm at position p *)
intros Sub' [x [q [q' [K1 [x_in_d [Sub'' Sub''']]]]]].
assert (x_in_g := R1_reg _ _ H1 x (var_in_subterm x _ _ Sub'' (or_introl _ (eq_refl _)))).
destruct (var_in_subterm2 x g) as [q'' Sub4].
apply in_impl_mem; trivial.
apply (It (q'' ++ q')); trivial.
apply subterm_in_subterm with (apply_subst sigma (Var x)); trivial.
generalize (subterm_at_pos_apply_subst_apply_subst_subterm_at_pos g q'' sigma).
rewrite Sub4; trivial.
(* 1/2 rewriting at top by R2 *)
destruct g as [v | f l].
apply False_rect; apply (R2_var _ _ H2).
simpl in It; apply (interp_well_defined_2 R1 R2 _ _ It).
apply (Def _ _ _ _ H2).
apply at_top; apply (instance (union _ R1 R2) d (Term f l) sigma); right; trivial.
(* 1/1 R1 R2 in context *)
destruct (def_dec f) as [Df | Cf].
apply interp_well_defined_2 with f ls; trivial.
right; assumption.
assert (Size_ls : forall s, In s ls -> size s <= n).
intros s s_in_ls; apply le_S_n; apply Nat.le_trans with (size (Term f ls)); trivial.
apply size_direct_subterm; trivial.

assert (Hlt : forall t, In t lt -> Interp_dom R1 R2 t).
assert (Hls : forall s, In s ls -> Interp_dom R1 R2 s).
intros; apply interp_well_defined_1 with f ls; trivial.
destruct (one_step_in_list H') as [a [b [l1 [l2 [H'' [H1 H2]]]]]]; subst ls lt.
intros t t_in_lt; destruct (in_app_or _ _ _ t_in_lt) as [t_in_l1 | [t_eq_b | t_in_l2]].
apply Hls; apply in_or_app; left; assumption.
subst t; apply IHn with a; trivial.
apply Size_ls; apply in_or_app; right; left; apply eq_refl.
apply interp_well_defined_1 with f (l1 ++ a :: l2); trivial.
apply in_or_app; right; left; apply eq_refl.
apply Hls; apply in_or_app; do 2 right; assumption.

intros [ | i p]; intros g l H Dg; simpl in H.
injection H; intros; subst; absurd (defined R2 g); trivial.
assert (H'' := nth_error_ok_in i lt).
destruct (nth_error lt i) as [ ti | ].
generalize (H'' _ (eq_refl _)); clear H'';
intros [l1 [l2 [L1 H'']]].
assert (ti_in_lt : In ti lt).
subst; apply in_or_app; right; left; trivial.
apply (Hlt _ ti_in_lt p); trivial.
discriminate.

Qed.

Lemma interp_dom_R1 :
 forall R1 R2, module R1 R2 ->
  (forall f, {defined R2 f}+{~defined R2 f}) ->
  (forall s t, R1 s t -> forall x, In x (var_list s) -> In x (var_list t)) ->
  (forall v t, ~ R2 t (Var v)) ->
  forall (s t : term), Interp_dom R1 R2 s -> 
  one_step R1 t s -> Interp_dom R1 R2 t.
Proof.
intros R1 R2 module_R1_R2 def_dec R1_reg R2_var; 
intros s t Is H; apply (interp_dom_R1_R2 R1 R2 module_R1_R2 def_dec R1_reg R2_var s); trivial.
rewrite split_rel; left; trivial.
Qed.

Lemma interp_dom_R2 :
 forall R1 R2, module R1 R2 ->
  (forall f, {defined R2 f}+{~defined R2 f}) ->
  (forall s t, R1 s t -> forall x, In x (var_list s) -> In x (var_list t)) ->
  (forall v t, ~ R2 t (Var v)) ->
  forall (s t : term), Interp_dom R1 R2 s -> 
  one_step R2 t s -> Interp_dom R1 R2 t.
Proof.
intros R1 R2 module_R1_R2 def_dec R1_reg R2_var; 
intros s t Is H; apply (interp_dom_R1_R2 R1 R2 module_R1_R2 def_dec R1_reg R2_var s); trivial.
rewrite split_rel; right; trivial.
Qed.

Lemma interp_dom_R1_R2_rwr :
 forall R1 R2, module R1 R2 ->
  (forall f, {defined R2 f}+{~defined R2 f}) ->
  (forall s t, R1 s t -> forall x, In x (var_list s) -> In x (var_list t)) ->
  (forall v t, ~ R2 t (Var v)) ->
  forall (s t : term), Interp_dom R1 R2 s -> 
  rwr (union _ R1 R2) t s -> Interp_dom R1 R2 t.
Proof.
intros R1 R2 module_R1_R2 def_dec R1_reg R2_var; 
intros s t Is H; induction H.
apply interp_dom_R1_R2 with y; trivial.
apply interp_dom_R1_R2 with y; trivial.
apply IHtrans_clos; trivial.
Qed.

Inductive Pi pi (v1 v2 : variable) : relation term :=
  | Pi1 : Pi pi v1 v2 (Var v1) (Term pi (Var v1 :: Var v2 :: nil))
  | Pi2 : Pi pi v1 v2 (Var v2) (Term pi (Var v1 :: Var v2 :: nil)).

Lemma pi_subterm :
  forall pi v1 v2 s t, axiom (Pi pi v1 v2) t s -> direct_subterm t s.
Proof.
intros pi v1 v2 s t H; inversion H as [t2' s' sigma H']; clear H; subst.
inversion H' as [pi' H1 | pi' H2]; subst; simpl.
left; trivial.
right; left; trivial.
Qed.

Definition is_primary_pi pi R := 
   forall s t, R s t -> (forall f, ((symb_in_term f s = true -> f <> pi) /\
                                             (symb_in_term f t = true -> f <> pi))).

Lemma acc_subterms_pi :
  forall pi v1 v2 R, (forall x t, ~ (R t (Var x))) -> is_primary_pi pi R ->
  forall l, (forall t, In t l -> Acc (one_step (union _ R (Pi pi v1 v2))) t) -> 
                   Acc (one_step (union _ R (Pi pi v1 v2))) (Term pi l).
Proof.
intros pi x1 x2 R R_var P l Hl;
assert (Acc_l : Acc (one_step_list (one_step (union _ R (Pi pi x1 x2)))) l).
rewrite <- acc_one_step_list; trivial.
generalize Hl; clear Hl; induction Acc_l as [l Acc_l IH].
intros Acc_l'; apply Acc_intro. 
intros t H; inversion H; clear H; subst.
inversion H0; clear H0; subst.
destruct t2 as [v2 | f2 l2].
absurd ((union _ R (Pi pi x1 x2)) t1 (Var v2)); trivial.
intros [H' | HPi].
apply (R_var _ _ H').
inversion HPi.
simpl in H; injection H; clear H; intros; subst.
destruct H2 as [H2 | Hpi].
destruct (P t1 (Term pi l2) H2 pi) as [_ F]; simpl in F.
apply False_rect; apply F.
generalize (F.Symb.eq_bool_ok pi pi); case (F.Symb.eq_bool pi pi).
trivial.
intro pi_diff_pi; absurd (pi =pi); trivial.
trivial.
assert (t1_in_ll : In (apply_subst sigma t1) (map (apply_subst sigma) l2)).
inversion Hpi; subst; simpl; [left | right; left]; trivial.
apply Acc_l'; trivial.
apply IH; trivial.
generalize l H2 Acc_l'; clear l H2 Acc_l' Acc_l IH.
intros l H; induction H.
intros Acc_l t [t_eq_t1 | t_in_l].
subst; assert (Acc_t2 := Acc_l t2 (or_introl _ (eq_refl _))).
inversion Acc_t2.
apply H0; trivial.
apply Acc_l; right; trivial.
intros Acc_l2 u [u_eq_t | u_in_l1].
subst; apply Acc_l2; left; trivial.
apply IHone_step_list; trivial.
intros; apply Acc_l2; right; trivial.
Qed.

Section Interp_definition.
Variable V0 : variable.
Variable V1 : variable.
Variable V0_diff_V1 : V0 <> V1.
Variable pi : symbol.
Variable bot : symbol.
Variable R1 : relation term.
Variable R2 : relation term.
Variable R1_reg : forall s t, R1 s t -> forall x, In x (var_list s) -> In x (var_list t) .
Variable R2_reg : forall s t, R2 s t -> forall x, In x (var_list s) -> In x (var_list t) .
Variable R1_var : forall v t, ~ R1 t (Var v).
Variable R2_var : forall v t, ~ R2 t (Var v).
Variable P2 : is_primary_pi pi R2.
Variable module_R1_R2 : module R1 R2.
Variable def_dec : forall f, {defined R2 f}+{~defined R2 f}.
Variable R1_red : term -> list term.
Variable R2_red : term -> list term.
Variable FB1 : forall t s, one_step R1 s t <-> In s (R1_red t).
Variable FB2 : forall t s, one_step R2 s t <-> In s (R2_red t).

Definition R1_R2_red t := R1_red t ++ R2_red t.

Lemma FB12 : forall s t, one_step (union _ R1 R2) s t <-> In s (R1_R2_red t).
Proof.
intros s t; split.
intro s_R_t; rewrite split_rel in s_R_t; unfold R1_R2_red;
destruct s_R_t as [s_R1_t | s_R2_t]; apply in_or_app.
left; rewrite <- FB1; trivial.
right; rewrite <- FB2; trivial.

intro s_in_l; unfold R1_R2_red in s_in_l; destruct (in_app_or _ _ _ s_in_l) as [K1 | K2].
rewrite split_rel; left; rewrite FB1; trivial.
rewrite split_rel; right; rewrite FB2; trivial.
Qed.

Fixpoint Comb (l : list term) : term :=
  match l with
  | nil => Term bot nil
  | t :: l => Term pi (t :: (Comb l) :: nil)
  end.

Inductive Interp : term -> term -> Prop :=
  | Vcase : forall x, Interp (Var x) (Var x)
  | Ccase : forall f l l' ll , ~defined R2 f -> 
                l = (map (fun st => fst st)) ll -> l' = (map (fun st => snd st)) ll ->
                (forall s s', In (s,s') ll -> Interp s s') -> 
                Interp (Term f l) (Term f l')
  | Dcase : forall f l l' ll, defined R2 f ->
                 R1_R2_red (Term f l) = (map (fun st => fst st)) ll -> l' = (map (fun st => snd st)) ll ->
                 (forall s s', In (s,s') ll -> Interp s s') -> 
                Interp (Term f l) (Comb l').

Lemma interp_unicity :
   forall t, Interp_dom R1 R2 t -> forall s1 s2, Interp t s1 -> Interp t s2 -> s1 = s2.
Proof.
intros t Ht;
assert (Acc_t :=interp_well_defined R1 R2 t Ht).
induction Acc_t as [t Acc_t IH].
destruct t as [x | f l];
intros s1 S2 H1 H2; 
inversion H1 as [ | f1 l1 l1' ll1 Cf1 Hl1 Hl1' Hll1 | f1 l1 l1' ll1 Df1 Hl1 Hl1' Hll1 ]; 
inversion H2 as [ | f2 l2 l2' ll2 Cf2 Hl2 Hl2' Hll2 | f2 l2 l2' ll2 Df2 Hl2 Hl2' Hll2 ]; subst; trivial.
apply (f_equal (fun ll => Term f (map (fun st => snd (A := term) st) ll))).
assert (H : forall s s1 s2, In (s,s1) ll1 -> In (s,s2) ll2 -> s1 = s2).
intros s s1 s2 ss1_in_ll1 ss2_in_ll2.
assert (s_in_l : In s (map (fun st => fst st) ll1)).
rewrite in_map_iff; exists (s,s1); split; trivial.
apply IH with s; trivial.
apply (Constr R1 R2 f (map (fun st => fst st) ll1) s Cf1 s_in_l).
apply (interp_well_defined_1 R1 R2 _ _ Ht _ s_in_l).
apply Hll1; trivial.
apply Hll2; trivial.
generalize ll1 ll2 Hl2 H; clear ll1 ll2 Hl2 H Hll1 Hll2 Ht Acc_t IH H2 H1.
intro ll1; induction ll1 as [ | [s s1] ll1]; intros [ | [s' s2] ll2] H' H; trivial.
discriminate.
discriminate.
simpl in H'; injection H'; clear H'; intros H' s_eq_s'; subst s'.
rewrite (H s s1 s2); try (left; trivial).
rewrite IHll1 with ll2; trivial.
intros t t1 t2 tt1_in_ll1 tt2_in_ll2; apply (H t t1 t2); right; trivial.
absurd (defined R2 f); trivial.
absurd (defined R2 f); trivial.
apply (f_equal (fun ll => Comb (map (fun st => snd (A := term) st) ll))).
assert (H : forall s s1 s2, In (s,s1) ll1 -> In (s,s2) ll2 -> s1 = s2).
intros s s1 s2 ss1_in_ll1 ss2_in_ll2.
assert (s_in_l : In s (map (fun st => fst st) ll1)).
rewrite in_map_iff; exists (s,s1); split; trivial.
apply IH with s; trivial.
apply (Defd R1 R2 f l s Df1).
rewrite <- Hl1 in s_in_l.
rewrite FB12; trivial.
apply (interp_well_defined_2 R1 R2 f l Ht Df1 s).
rewrite <- Hl1 in s_in_l.
rewrite FB12; trivial.
apply Hll1; trivial.
apply Hll2; trivial.
rewrite Hl1 in Hl2;
generalize ll1 ll2 Hl2 H; clear ll1 ll2 Hl2 H Hll1 Hll2 Ht Acc_t IH H2 H1 Hl1.
intro ll1; induction ll1 as [ | [s s1] ll1]; intros [ | [s' s2] ll2] H' H; trivial.
discriminate.
discriminate.
simpl in H'; injection H'; clear H'; intros H' s_eq_s'; subst s'.
rewrite (H s s1 s2); try (left; trivial).
rewrite IHll1 with ll2; trivial.
intros t t1 t2 tt1_in_ll1 tt2_in_ll2; apply (H t t1 t2); right; trivial.
Qed.

Lemma interp_defined : forall t, Interp_dom R1 R2 t -> {s : term | Interp t s}.
Proof.
intros t Ht;
assert (Acc_t := interp_well_defined R1 R2 t Ht).
induction Acc_t as [t Acc_t IH].
destruct t as [x | f l].
exists (Var x); apply Vcase.
destruct (def_dec f) as [Df | Cf].
assert (interp_l : forall s, In s (R1_R2_red (Term f l)) -> {u : term | Interp s u}).
intros s s_in_red_t; apply IH.
apply (Defd R1 R2 f l s Df).
rewrite FB12; trivial.
apply interp_well_defined_2 with f l; trivial.
rewrite FB12; trivial.
assert (ll : {ll : list (term * term) | R1_R2_red (Term f l) = (map (fun st => fst st)) ll /\
                                                        (forall s s', In (s,s') ll -> Interp s s')}).
generalize (R1_R2_red (Term f l)) interp_l.
intro k; induction k as [ | s k].
intros _; exists (@nil (term * term)); split; trivial; contradiction.
intros interp_sk.
destruct (interp_sk s) as [u Isu].
left; trivial.
destruct IHk as [kk [Hk Pk]].
intros; apply interp_sk; right; trivial.
exists ((s,u) :: kk); split.
simpl; rewrite Hk; trivial.
simpl; intros t t' [tt'_eq_su | tt'_in_kk].
injection tt'_eq_su; intros; subst; trivial.
apply Pk; trivial.
destruct ll as [ll [Hl Pl]].
exists (Comb (map (fun st => snd st) ll)).
apply Dcase with ll; trivial.

assert (interp_l : forall s, In s l -> {u : term | Interp s u}).
intros s s_in_l; apply IH.
apply (Constr R1 R2 f l s Cf s_in_l).
apply interp_well_defined_1 with f l; trivial.
assert (ll : {ll : list (term * term) | l = (map (fun st => fst st)) ll /\
                                                        (forall s s', In (s,s') ll -> Interp s s')}).
generalize l interp_l.
intro k; induction k as [ | s k].
intros _; exists (@nil (term * term)); split; trivial; contradiction.
intros interp_sk.
destruct (interp_sk s) as [u Isu].
left; trivial.
destruct IHk as [kk [Hk Pk]].
intros; apply interp_sk; right; trivial.
exists ((s,u) :: kk); split.
simpl; rewrite Hk; trivial.
simpl; intros t t' [tt'_eq_su | tt'_in_kk].
injection tt'_eq_su; intros; subst; trivial.
apply Pk; trivial.
destruct ll as [ll [Hl Pl]].
exists (Term f (map (fun st => snd st) ll)).
apply Ccase with ll; trivial.
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

Lemma recover_red :
  forall f l t s' t', defined R2 f -> Interp_dom R1 R2 (Term f l) -> 
  Interp (Term f l) s' -> Interp t t' -> 
  one_step (union _ R1 R2) t (Term f l) -> rwr (Pi pi V0 V1) t' s'.
Proof.
intros f l t s' t' Df Idfl Is It t_R_fl.
inversion Is as [ | f' l' l'' ll Cf Hl Hl' Hll | f' l' l'' ll _ Hl Hl' Hll]; subst.
absurd (defined R2 f); trivial.
apply project_comb.
rewrite in_map_iff; exists (t,t'); split.
apply eq_refl.
assert (t_R_fl_bis := t_R_fl); rewrite FB12 in t_R_fl_bis.
rewrite Hl in t_R_fl_bis.
rewrite in_map_iff in t_R_fl_bis.
destruct t_R_fl_bis as [[u u'] [u_eq_t H]]. 
simpl in u_eq_t; subst u.
replace t' with u'; trivial.
apply interp_unicity with t; trivial.
apply interp_well_defined_2 with f l; trivial.
apply Hll; trivial.
Qed.

Definition Interp_subst lv sigma sigma' :=
  forall v, In v lv -> Interp_dom R1 R2 (apply_subst sigma (Var v)) /\
  Interp (apply_subst sigma (Var v)) (apply_subst sigma' (Var v)).

Lemma R1_at_top_aux_1 :
 forall t sigma sigma', (forall f, symb_in_term f t = true -> ~defined R2 f) -> 
                       Interp_dom R1 R2 (apply_subst sigma t) ->
                       Interp_subst (var_list t) sigma sigma' ->
  Interp (apply_subst sigma t) (apply_subst sigma' t).
Proof.
intro t; pattern t; apply term_rec3; clear t.
intros v sigma sigma' _ Ht Hsigma; apply (proj2 (Hsigma v (or_introl _ (eq_refl _)))).
intros f l IH sigma sigma' Ct Ht Hsigma; simpl.
apply (Ccase f (map (apply_subst sigma) l)
  (map (apply_subst sigma') l)
  (map (fun t => (apply_subst sigma t, apply_subst sigma' t)) l)).
simpl; apply Ct; rewrite symb_in_term_unfold.
generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); [intros _; trivial | intros f_diff_f; absurd (f = f); trivial].
rewrite map_map; simpl; trivial.
rewrite map_map; simpl; trivial.
intros s s'; rewrite in_map_iff; intros [u [H' u_in_l]].
injection H'; intros; subst; clear H'.
assert (Cu : forall f0, symb_in_term f0 u = true -> ~ defined R2 f0).
intros g Hg; apply Ct.
rewrite symb_in_term_unfold.
generalize (F.Symb.eq_bool_ok g f); case (F.Symb.eq_bool g f); [intros g_eq_f | intros g_diff_f]; trivial.
simpl; destruct (In_split _ _ u_in_l) as [l' [l'' H1]]; subst l.
rewrite symb_in_term_list_app.
destruct (symb_in_term_list g l'); simpl; trivial.
rewrite Hg; simpl; trivial.
assert (Hu : Interp_dom R1 R2 (apply_subst sigma u)).
simpl in Ht; apply (interp_well_defined_1 R1 R2 _ _ Ht).
rewrite in_map_iff.
exists u; split; trivial.
apply (IH u u_in_l sigma sigma' Cu Hu).
intros v v_in_u; apply (Hsigma v).
rewrite var_list_unfold.
generalize l u_in_l; intro k; induction k as [ | t k].
contradiction.
intros [u_eq_t | u_in_k].
subst; simpl; apply in_or_app; left; trivial.
simpl; apply in_or_app; right; apply IHk; trivial.
Qed.

Lemma R1_at_top_aux_2 :
  forall t, (forall f, symb_in_term f t = true -> ~defined R2 f) -> 
  forall sigma, Interp_dom R1 R2 (apply_subst sigma t) ->
  {sigma' : substitution | Interp_subst (var_list t) sigma sigma'}.
Proof.
intros t Ct sigma Ht.
assert (H : forall v, In v (var_list t) -> 
               {s' : term | Interp_dom R1 R2 (apply_subst sigma (Var v)) /\
                                     Interp (apply_subst sigma (Var v)) s'}).
intros v v_in_l;
assert (H' := interp_dom_subst R1 R2 t sigma Ht v v_in_l).
destruct (interp_defined _ H') as [s' Hs']; exists s'; split; trivial.
assert (H' : forall l, (forall v, In v l -> 
           {s' : term | Interp_dom R1 R2 (apply_subst sigma (Var v)) /\
                                  Interp (apply_subst sigma (Var v)) s'}) ->
                        {l' : substitution | Interp_subst l sigma l'}).
intro l; induction l as [ | x l].
intros _; exists (nil : substitution); 
unfold Interp_subst; intros; contradiction.
intro H''; destruct IHl as [sigma' Hsigma'].
intros v v_in_l; apply H''; right; trivial.
destruct (H'' x) as [x' [Hx' Hx'']].
left; trivial.
exists ((x,x') :: sigma').
unfold Interp_subst.
intros v [v_eq_x | v_in_l].
subst v;  simpl; split; trivial.
generalize (X.eq_bool_ok x x); case (X.eq_bool x x); [intros _ | intros x_diff_x; absurd (x = x)]; trivial.
destruct (Hsigma' v v_in_l) as [H''' H'''']; split; trivial.
simpl; generalize (X.eq_bool_ok v x); case (X.eq_bool v x); [intros v_eq_x | intros v_diff_x; trivial].
subst v; simpl in Hx'; trivial.
destruct (H' _ H) as [sigma' Hsigma'].
exists sigma'; trivial.
Qed.

Lemma R1_at_top :
  forall S1, inclusion _ S1 R1 -> forall l r, S1 r l -> forall sigma, 
  Interp_dom R1 R2 (apply_subst sigma l)->
  {sigma' : substitution & {s' : term & {t' : term | 
     Interp_subst (var_list l) sigma sigma' /\
     Interp (apply_subst sigma l) s' /\
     Interp (apply_subst sigma r) t' /\
     axiom S1 t' s'} } }.
Proof.
inversion module_R1_R2 as [M].
intros S1 S1_in_R1 l r r_R1_l sigma Hl. 
assert (Cl : forall f, symb_in_term f l = true -> ~defined R2 f).
intros f f_in_l Df; generalize (M f r l Df (S1_in_R1 _ _ r_R1_l)).
replace (r :: l :: nil) with ((r :: nil) ++ (l :: nil)); trivial.
rewrite symb_in_term_list_app.
simpl; rewrite f_in_l.
destruct (symb_in_term f r); simpl; discriminate.
assert (Cr : forall f, symb_in_term f r = true -> ~defined R2 f).
intros f f_in_r Df; generalize (M f r l Df (S1_in_R1 _ _ r_R1_l)).
replace (r :: l :: nil) with ((r :: nil) ++ (l :: nil)); trivial.
rewrite symb_in_term_list_app; simpl.
rewrite f_in_r; simpl; discriminate.

destruct (R1_at_top_aux_2 l Cl sigma Hl) as [sigma' Hsigma].
exists sigma'.
destruct (interp_defined _ Hl) as [s' Hs']; exists s'.
assert (Hsigma' : Interp_subst (var_list r) sigma sigma').
intros v v_in_r; apply (Hsigma v).
apply R1_reg with r; trivial; apply S1_in_R1; trivial.
assert (Hr : Interp_dom R1 R2 (apply_subst sigma r)).
refine (interp_dom_R1 R1 R2 _ _ _ _ _ _ Hl _); trivial.
apply at_top; apply instance; apply S1_in_R1; trivial.
destruct (interp_defined _ Hr) as [t' Ht']; exists t'.
split; trivial.
split; trivial.
split; trivial.
assert (Hs'' := R1_at_top_aux_1 l sigma sigma' Cl Hl Hsigma).
rewrite (interp_unicity _ Hl _ _ Hs' Hs'').
assert (Ht'' := R1_at_top_aux_1 r sigma sigma' Cr Hr Hsigma').
rewrite (interp_unicity _ Hr _ _ Ht' Ht'').
apply instance; trivial.
Qed.

Lemma R1_at_top_dp :
  forall S1, inclusion _ S1 R1 -> forall l t r p, S1 t l ->  subterm_at_pos t p = Some r ->
  forall sigma, 
  Interp_dom R1 R2 (apply_subst sigma l)->
  {sigma' : substitution | 
      Interp_subst (var_list l) sigma sigma' /\
      Interp_dom R1 R2 (apply_subst sigma r) /\
      Interp (apply_subst sigma l) (apply_subst sigma' l) /\
      Interp (apply_subst sigma r) (apply_subst sigma' r) }.
Proof.
inversion module_R1_R2 as [M].
intros S1 S1_in_R1 l t r p t_R1_l t_p_eq_r sigma Hl. 

assert (Cl : forall f, symb_in_term f l = true -> ~defined R2 f).
intros f f_in_l Df; generalize (M f t l Df (S1_in_R1 _ _ t_R1_l)).
replace (t :: l :: nil) with ((t :: nil) ++ (l :: nil)); trivial.
rewrite symb_in_term_list_app.
simpl; rewrite f_in_l.
destruct (symb_in_term f t); simpl; discriminate.

assert (Ct : forall f, symb_in_term f t = true -> ~defined R2 f).
intros f f_in_t Df; generalize (M f t l Df (S1_in_R1 _ _ t_R1_l)).
replace (t :: l :: nil) with ((t :: nil) ++ (l :: nil)); trivial.
rewrite symb_in_term_list_app; simpl.
rewrite f_in_t; simpl; discriminate.

assert (Cr : forall f, symb_in_term f r = true -> ~defined R2 f).
intros f f_in_r; apply Ct; apply symb_in_subterm with r p; trivial.

destruct l as [v | f l].
absurd (R1 t (Var v)).
apply R1_var.
apply S1_in_R1; trivial.
assert (Cf : ~defined R2 f).
apply Cl; rewrite symb_in_term_unfold.
simpl; generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); [intros _ | intros f_diff_f; absurd (f = f)]; trivial.
assert (H' := R1_at_top _ S1_in_R1 _ _ t_R1_l sigma).
destruct (R1_at_top_aux_2 (Term f l) Cl sigma Hl) as [sigma' Hsigma].
exists sigma'.

assert (Hsigma' : Interp_subst (var_list t) sigma sigma').
intros v v_in_t; apply (Hsigma v); 
apply R1_reg with t; trivial; apply S1_in_R1; trivial.
assert (Hsigma'' : Interp_subst (var_list r) sigma sigma').
intros v v_in_r; apply (Hsigma' v).
apply var_in_subterm with r p; trivial.

assert (Ht : Interp_dom R1 R2 (apply_subst sigma t)).
refine (interp_dom_R1 _ _ _ _ _ _ _ _ Hl _); trivial.
apply at_top; apply instance; apply S1_in_R1; trivial.
assert (Hr : Interp_dom R1 R2 (apply_subst sigma r)).
generalize t r t_p_eq_r Ht; clear t r t_p_eq_r Ht t_R1_l Ct Cr H' Hsigma' Hsigma''.
induction p as [ | i p]; intros t r t_p_eq_r Ht.
simpl in t_p_eq_r; injection t_p_eq_r; intro; subst; trivial.
simpl in t_p_eq_r; destruct t as [ | g ll].
discriminate.
assert (H' := nth_error_ok_in i ll).
destruct (nth_error ll i) as [ti | ].
destruct (H' _ (eq_refl _)) as [l1 [l2 [L H'']]]; subst ll.
apply (IHp ti r); trivial.
simpl in Ht; apply (interp_well_defined_1 R1 R2 _ _ Ht).
rewrite in_map_iff.
exists  ti; split; trivial.
apply in_or_app; right; left; trivial.
discriminate.

split; trivial; split; trivial; split.
exact (R1_at_top_aux_1 (Term f l) sigma sigma' Cl Hl Hsigma).
destruct r as [v | g k].
apply (proj2 (Hsigma'' v (or_introl _ (eq_refl _)))).
exact (R1_at_top_aux_1 (Term g k) sigma sigma' Cr Hr Hsigma'').
Qed.

Lemma R1_case :
   forall (s t : term), Interp_dom R1 R2 s -> one_step R1 t s ->
   exists s', exists t', Interp s s' /\ Interp t t' /\ rwr (union _ R1 (Pi pi V0 V1)) t' s'.
Proof.
assert (R1_in_R1 : inclusion _ R1 R1).
intros t1 t2; trivial.
intro s; pattern s; apply term_rec2; clear s.
intro n; induction n as [ | n]; intros s Size_s t Is t_R_s.
absurd (1 <= 0); auto with arith; apply Nat.le_trans with (size s); trivial;
apply size_ge_one.
induction t_R_s as [t' s' t'_R_s' | f' lt ls lt_R_ls]; subst.
inversion t'_R_s' as [t3 s3 sigma t3_R_s3]; subst.
destruct (R1_at_top R1 R1_in_R1 s3 t3 t3_R_s3 sigma Is) as [sigma' [s' [t' [_ [H1 [H2 H3]]]]]].
exists s'; exists t'; split; trivial.
split; trivial.
apply t_step.
apply one_step_incl with R1.
intros t1 t2 H; left; trivial.
apply at_top; trivial.
destruct (interp_defined _ Is) as [s' Hs'].
exists s'.
assert (It : Interp_dom R1 R2 (Term f' lt)).
refine (interp_dom_R1 R1 R2 _ _ _ _ _ (Term f' lt) Is _); trivial.
apply in_context; trivial.
destruct (interp_defined _ It) as [t' Ht'].
exists t'; split; trivial.
split; trivial.
inversion Hs' as [ | f l' l'' ll Cf Hl Hl' Hll | f l' l'' ll Df Hl Hl' Hll].
inversion Ht' as [ | g k' k'' kk Cg Hk Hk' Hkk | g k' k'' kk Dg Hk Hk' Hkk].
assert (Size_ls : forall s, In s ls -> size s <= n).
intros s s_in_ls; apply le_S_n; apply Nat.le_trans with (size (Term f' ls)); trivial.
apply size_direct_subterm; trivial.
assert (Hls : forall s, In s ls -> Interp_dom R1 R2 s).
intros; apply interp_well_defined_1 with f' ls; trivial.
assert (Hlt : forall t, In t lt -> Interp_dom R1 R2 t).
intros; apply interp_well_defined_1 with f' lt; trivial.
apply general_context.
subst f g l'' l' s' k'' k' t'.
generalize ll Hl Hll kk Hk Hkk ;
clear Size_s Is Hs' It Ht' ll Hl Hll kk Hk Hkk.

induction lt_R_ls as [t s l t_R1_s | s lt ls lt_R1_ls]; subst;
intros ll Hl Hll kk Hk Hkk.
destruct ll as [ | [s' s''] ll].
discriminate.
simpl in Hl; injection Hl; clear Hl; intros; subst.
destruct kk as [ | [t' t''] kk].
discriminate.
simpl in Hk; injection Hk; clear Hk; intros; subst.
simpl; replace (map (fun st : term * term => snd st) kk) with
            (map (fun st : term * term => snd st) ll).
assert (t''_R_s'' : rwr (union term R1 (Pi pi V0 V1)) t'' s'').
assert (Size_s' : size s' <= n).
apply Size_ls; left; trivial.
assert (Is' : Interp_dom R1 R2 s').
apply Hls; left; trivial.
destruct (IHn s' Size_s' t') as [u [v [Hu [Hv H1]]]]; trivial.
rewrite (interp_unicity s' Is' s'' u); trivial.
assert (It' : Interp_dom R1 R2 t').
apply Hlt; left; trivial.
rewrite (interp_unicity t' It' t'' v); trivial.
apply Hkk; left; trivial.
apply Hll; left; trivial.
revert t''_R_s''; clear; intro H; induction H as [t1 t2 H | t1 t2 t3 H1 H2].
do 2 left; assumption.
right with (t2 :: map (fun st : term * term => snd st) ll); trivial.
left; assumption.
assert (Hkl : forall u u' u'', In (u,u') ll -> In (u,u'') kk -> u' = u'').
intros u u' u'' uu'_in_ll uu''_in_kk;
refine (interp_unicity u _ u' u'' _ _).
apply Hlt; trivial.
right; rewrite in_map_iff; exists (u,u'); split; trivial.
apply Hll; right; trivial.
apply Hkk; right; trivial.
generalize ll kk H Hkl; clear H Hkl;
intro l1; induction l1 as [ | [u u'] l1]; intros [ | [v v'] l2] H Hkl.
trivial.
discriminate.
discriminate.
simpl in H; injection H; clear H; intros H u_eq_v; subst v.
simpl; rewrite (IHl1 l2); trivial.
rewrite (Hkl u u' v'); trivial; left; trivial.
intros w w' w'' H1 H2; apply (Hkl w); right; trivial.

destruct ll as [ | [s' s''] ll].
discriminate.
simpl in Hl; injection Hl; clear Hl; intros; subst.
destruct kk as [ | [t' t''] kk].
discriminate.
simpl in Hk; injection Hk; clear Hk; intros; subst.
simpl.
assert (t''_eq_s'' : t'' = s'').
refine (interp_unicity t' _ t'' s'' _ _).
apply Hlt; left; trivial.
apply Hkk; left; trivial.
apply Hll; left; trivial.
assert (H : rwr_list (one_step (union term R1 (Pi pi V0 V1)))
                                     (map (fun st : term * term => snd st) kk)
                                     (map (fun st : term * term => snd st) ll)).
apply IHlt_R1_ls; trivial.
intros; apply Size_ls; right; trivial.
intros; apply Hls; right; trivial.
intros; apply Hlt; right; trivial.
intros; apply Hll; right; trivial.
intros; apply Hkk; right; trivial.
subst t''; revert H; clear; intro H; induction H as [l1 l2 H | l1 l2 l3 H1 H2].
left; right; assumption.
right with (s'' :: l2); trivial.
right; assumption.
absurd (defined R2 f'); trivial.
subst.
simpl in Is; apply rwr_incl with (Pi pi V0 V1).
intros t1 t2; right; trivial.
refine (recover_red f' _ _ _ _ _ Is Hs' Ht' _); trivial.
apply one_step_incl with R1.
intros t1 t2 H; left; trivial.
apply in_context; trivial.
Qed.

Lemma R2_case :
   forall (s t : term), Interp_dom R1 R2 s -> one_step R2 t s ->
   exists s', exists t', Interp s s' /\ Interp t t' /\ rwr (Pi pi V0 V1) t' s'.
Proof.
intro s; pattern s; apply term_rec2; clear s.
intro n; induction n as [ | n]; intros s Size_s t Is t_R_s.
absurd (1 <= 0); auto with arith; apply Nat.le_trans with (size s); trivial;
apply size_ge_one.
induction t_R_s as [t' s' t'_R_s' | f' lt ls lt_R_ls]; subst.
inversion t'_R_s' as [t3 s3 sigma t3_R_s3]; subst.
assert (It : Interp_dom R1 R2 (apply_subst sigma t3)).
refine (interp_dom_R2 R1 R2 _ _ _ _ _ _ Is _); trivial.
apply at_top; trivial.
destruct (interp_defined _ Is) as [s' Hs'].
destruct (interp_defined _ It) as [t' Ht'].
exists s'; exists t'; split; trivial.
split; trivial.
destruct s3 as [v | f ls].
absurd (R2 t3 (Var v)); trivial; apply R2_var.
simpl in Is; refine (recover_red f _ _ _ _ _ Is Hs' Ht' _); trivial.
apply (Def _ _ _ _ t3_R_s3).
apply one_step_incl with R2.
intros; right; trivial.
apply at_top; trivial.
destruct (def_dec f') as [Df' | Cf'].
destruct (interp_defined _ Is) as [s' Hs'].
assert (It : Interp_dom R1 R2 (Term f' lt)).
refine (interp_dom_R2 R1 R2 _ _ _ _ _ _ Is _); trivial.
apply one_step_incl with R2; trivial.
apply in_context; trivial.
destruct (interp_defined _ It) as [t' Ht'].
exists s'; exists t'; split; trivial.
split; trivial.
simpl in Is; refine (recover_red f' _ _ _ _ _ Is Hs' Ht' _); trivial.
apply one_step_incl with R2.
intros; right; trivial.
apply in_context; trivial.
assert (It : Interp_dom R1 R2 (Term f' lt)).
refine (interp_dom_R2 R1 R2 _ _ _ _ _ _ Is _); trivial.
apply one_step_incl with R2; trivial.
apply in_context; trivial.
destruct (interp_defined _ Is) as [s' Hs'].
destruct (interp_defined _ It) as [t' Ht'].
exists s'; exists t'; split; trivial.
split; trivial.
inversion Hs' as [ | f l' l'' ll Cf Hl Hl' Hll | f l' l'' ll Df Hl Hl' Hll].
inversion Ht' as [ | g k' k'' kk Cg Hk Hk' Hkk | g k' k'' kk Dg Hk Hk' Hkk].
assert (Size_ls : forall s, In s ls -> size s <= n).
intros s s_in_ls; apply le_S_n; apply Nat.le_trans with (size (Term f' ls)); trivial.
apply size_direct_subterm; trivial.
assert (Hls : forall s, In s ls -> Interp_dom R1 R2 s).
intros; apply interp_well_defined_1 with f' ls; trivial.
assert (Hlt : forall t, In t lt -> Interp_dom R1 R2 t).
intros; apply interp_well_defined_1 with f' lt; trivial.
apply general_context.
subst f g l'' l' s' k'' k' t'.
generalize ll Hl Hll kk Hk Hkk ;
clear Size_s Is Hs' It Ht' ll Hl Hll kk Hk Hkk.

induction lt_R_ls as [t s l t_R2_s | s lt ls lt_R2_ls]; subst;
intros ll Hl Hll kk Hk Hkk.
destruct ll as [ | [s' s''] ll].
discriminate.
simpl in Hl; injection Hl; clear Hl; intros; subst.
destruct kk as [ | [t' t''] kk].
discriminate.
simpl in Hk; injection Hk; clear Hk; intros; subst.
simpl; replace (map (fun st : term * term => snd st) kk) with
            (map (fun st : term * term => snd st) ll).
assert (t''_R_s'' : rwr (Pi pi V0 V1) t'' s'').
assert (Size_s' : size s' <= n).
apply Size_ls; left; trivial.
assert (Is' : Interp_dom R1 R2 s').
apply Hls; left; trivial.
destruct (IHn s' Size_s' t') as [u [v [Hu [Hv H1]]]]; trivial.
rewrite (interp_unicity s' Is' s'' u); trivial.
assert (It' : Interp_dom R1 R2 t').
apply Hlt; left; trivial.
rewrite (interp_unicity t' It' t'' v); trivial.
apply Hkk; left; trivial.
apply Hll; left; trivial.
revert t''_R_s''; clear; intro H; induction H as [t1 t2 H | t1 t2 t3 H1 H2].
do 2 left; assumption.
right with (t2 :: map (fun st : term * term => snd st) ll); trivial.
left; assumption.
assert (Hkl : forall u u' u'', In (u,u') ll -> In (u,u'') kk -> u' = u'').
intros u u' u'' uu'_in_ll uu''_in_kk;
refine (interp_unicity u _ u' u'' _ _).
apply Hlt; trivial.
right; rewrite in_map_iff; exists (u,u'); split; trivial.
apply Hll; right; trivial.
apply Hkk; right; trivial.
generalize ll kk H Hkl; clear H Hkl;
intro l1; induction l1 as [ | [u u'] l1]; intros [ | [v v'] l2] H Hkl.
trivial.
discriminate.
discriminate.
simpl in H; injection H; clear H; intros H u_eq_v; subst v.
simpl; rewrite (IHl1 l2); trivial.
rewrite (Hkl u u' v'); trivial; left; trivial.
intros w w' w'' H1 H2; apply (Hkl w); right; trivial.

destruct ll as [ | [s' s''] ll].
discriminate.
simpl in Hl; injection Hl; clear Hl; intros; subst.
destruct kk as [ | [t' t''] kk].
discriminate.
simpl in Hk; injection Hk; clear Hk; intros; subst.
simpl; assert (t''_eq_s'' : t'' = s'').
refine (interp_unicity t' _ t'' s'' _ _).
apply Hlt; left; trivial.
apply Hkk; left; trivial.
apply Hll; left; trivial.
subst t''.
assert (H : rwr_list (one_step (Pi pi V0 V1)) (map (fun st : term * term => snd st) kk)
                            (map (fun st : term * term => snd st) ll)).
apply IHlt_R2_ls; trivial.
intros; apply Size_ls; right; trivial.
intros; apply Hls; right; trivial.
intros; apply Hlt; right; trivial.
intros; apply Hll; right; trivial.
intros; apply Hkk; right; trivial.
revert H; clear; intro H; induction H as [l1 l2 H | l1 l2 l3 H1 H2].
left; right; assumption.
right with (s'' :: l2); trivial.
right; assumption.
absurd (defined R2 f'); trivial.
subst.
simpl in Is; refine (recover_red f' _ _ _ _ _ Is Hs' Ht' _); trivial.
apply one_step_incl with R2.
intros; right; trivial.
apply in_context; trivial.
Qed.

Lemma R1_R2_case_one_step :
   forall (s t : term), Interp_dom R1 R2 s -> 
   one_step (union _ R1 R2) t s ->
   exists s', exists t', Interp s s' /\ Interp t t' /\ rwr (union _ R1 (Pi pi V0 V1)) t' s'.
Proof.
intros s t Is H.
rewrite split_rel in H.
destruct H as [H1 | H2].
apply R1_case; trivial.
destruct (R2_case s t Is H2) as [s' [t' [Hs' [Ht' H']]]].
exists s'; exists t'; split; trivial.
split; trivial.
apply rwr_incl with (Pi pi V0 V1); trivial.
intros t1 t2 H''; right; trivial.
Qed.

Lemma R1_R2_case :
   forall (s t : term), Interp_dom R1 R2 s -> 
   rwr (union _ R1 R2) t s ->
   exists s', exists t', Interp s s' /\ Interp t t' /\ rwr (union _ R1 (Pi pi V0 V1)) t' s'.
Proof.
intros s t Is t_R_s; induction t_R_s; subst.
apply R1_R2_case_one_step; trivial.
destruct (IHt_R_s Is) as [s' [t' [Hs' [Ht' t'_R_s']]]].
assert (It2 : Interp_dom R1 R2 y).
apply interp_dom_R1_R2_rwr with z; trivial.
destruct (R1_R2_case_one_step y x It2 H) as [s'' [t'' [Hs'' [Ht'' t''_R_s'']]]].
exists s'; exists t''; split; trivial.
split; trivial.
apply trans_clos_is_trans with s''; trivial.
rewrite (interp_unicity _ It2 _ _ Hs'' Ht'); trivial.
Qed.

Lemma technical_lemma_1 :
  forall S1, inclusion _ S1 R1 -> 
  forall s s' t t', Interp_dom R1 R2 s -> Interp_dom R1 R2 t -> 
  Interp s s' -> Interp t t' ->
  axiom (ddp S1) t s -> axiom (ddp S1) t' s'.
Proof.
intros S1 S1_in_R1 _s s' _t t' Is It Hs' Ht' t_S1_s.
inversion t_S1_s as [t s sigma K]; clear t_S1_s; subst.
destruct K as [K Sub].
inversion K as [ s'' t'' p f l t''_S1_s'' H Df H1 H2]; clear K; subst.
destruct s as [v'' | f'' l''].
absurd (R1 t'' (Var v'')).
apply R1_var.
apply S1_in_R1; trivial.
assert (H' := R1_at_top_dp _ S1_in_R1 _ _ _ _ t''_S1_s'' H sigma).
destruct (H' Is) as [sigma' [Isigma [_ [Hs Ht]]]]; clear H'.
rewrite (interp_unicity _ Is _ _ Hs' Hs).
rewrite (interp_unicity _ It _ _ Ht' Ht).
apply instance.
split; [apply (Dp _ _ _ _ _ _ t''_S1_s'' H Df) | assumption].
Qed.

Lemma technical_lemma :
  forall S1, inclusion _ S1 R1 -> forall s s' t t', 
  Interp_dom R1 R2 s -> Interp_dom R1 R2 t -> 
  Interp s s' -> Interp t t' ->
  rdp_step (axiom (ddp S1)) (union _ R1 R2) t s -> 
  rdp_step (axiom (ddp S1)) (union _ R1 (Pi pi V0 V1)) t' s'.
Proof.
inversion module_R1_R2 as [M].
intros S1 S1_in_R1 s s' t t' Is It Hs' Ht' t_R_s.
inversion t_R_s as [f l1 l2 t'' l2_R_l1 H]; subst; clear t_R_s.
assert (Is2 : Interp_dom R1 R2 (Term f l2)).
assert (t2_R_t1 : refl_trans_clos (one_step (union _ R1 R2)) (Term f l2) (Term f l1)).
inversion l2_R_l1 as [l | l2' l1' l2_R_l1']; subst; 
  [left | right; apply general_context; assumption].
inversion t2_R_t1 as [t12 | t2 t1 t2_R_t1']; clear t2_R_t1; subst.
assumption.
apply interp_dom_R1_R2_rwr with (Term f l1); assumption.
destruct (interp_defined _ Is2) as [s'' Hs''].
inversion Hs' as [ | f' l' l'' ll1 Cf' Hl Hl' Hll1 | f' l' l'' ll1 Df Hl Hl' Hll1]; clear Hs'; subst.
(* 1/2 *)
inversion Hs'' as [ | f'' k' k'' ll2 Cf'' Hk Hk' Hll2 | f'' k' k'' ll2 Df' Hk Hk' Hll2]; subst.
(* 1/3 *)
apply (Rdp_step (axiom (ddp S1)) (union term R1 (Pi pi V0 V1)) f (map (@snd _ _) ll1) (map (@snd _ _) ll2) t'); trivial.
(* 1/4 *)
assert (Ill2 : forall s, In s (map (@fst _ _) ll2) -> Interp_dom R1 R2 s).
intros; apply (interp_well_defined_1 R1 R2 _ _ Is2); trivial.
assert (Ill1 : forall s, In s (map (@fst _ _) ll1) -> Interp_dom R1 R2 s).
intros; apply (interp_well_defined_1 R1 R2 _ _ Is); trivial.
clear Is H Is2 Hs''.
revert ll1 Ill1 Ill2 Hll1 Hll2 l2_R_l1.
induction ll2 as [ | [u u'] ll2].
intros [ | [v v'] ll1] Ill1 Ill2 Hll1 Hll2 l2_R_l1.
left.
generalize (refl_trans_clos_one_step_list_length_eq l2_R_l1); intros; discriminate.
intros [ | [v v'] ll1]; simpl; intros Ill1 Ill2 Hll1 Hll2 l2_R_l1.
generalize (refl_trans_clos_one_step_list_length_eq l2_R_l1); intros; discriminate.
rewrite refl_trans_clos_one_step_list_head_tail; split.
assert (u_R_v : refl_trans_clos (one_step (union term R1 R2)) u v).
apply refl_trans_clos_one_step_list_refl_trans_clos_one_step with nil (map (@fst _ _) ll2) nil (map (@fst _ _) ll1).
apply eq_refl.
assumption.
inversion u_R_v as [uv | uu vv u_R_v']; clear u_R_v; subst.
assert (Iv := Ill1 v (or_introl _ (eq_refl _))).
rewrite (interp_unicity _ Iv v' u' (Hll1 _ _ (or_introl _ (eq_refl _))) (Hll2 _ _ (or_introl _ (eq_refl _)))).
left.
assert (Iv := Ill1 _ (or_introl _ (eq_refl _))).
assert (Iu := Ill2 _ (or_introl _ (eq_refl _))).
destruct (R1_R2_case _ _ Iv u_R_v') as [v'' [u'' [Iv' [Iu' H]]]].
rewrite (interp_unicity _ Iv _ _ (Hll1 _ _ (or_introl _ (eq_refl _))) Iv').
rewrite (interp_unicity _ Iu _ _ (Hll2 _ _ (or_introl _ (eq_refl _))) Iu').
right; assumption.
apply (IHll2 ll1 (tail_prop _ Ill1) (tail_prop _ Ill2) (fun s s' H => Hll1 _ _ (or_intror _ H)) 
                         (fun s s' H => Hll2 _ _ (or_intror _ H))).
rewrite refl_trans_clos_one_step_list_head_tail in l2_R_l1; apply (proj2 l2_R_l1).
(* 1/3 *)
apply (technical_lemma_1 _ S1_in_R1 _ _ _ _ Is2 It Hs'' Ht' H).
(* 1/2 *)
absurd (defined R2 f); trivial.
(* 1/1*)
absurd (defined R2 f); trivial.
inversion H; clear H; subst.
destruct t2 as [v2 | f2 k2].
destruct H2 as [H2 Sub]; inversion H2; clear H2; subst.
absurd (R1 t2 (Var v2)).
apply R1_var.
apply S1_in_R1; trivial.
destruct H2 as [H2 Sub]; inversion H2; clear H2; subst.
injection H0; clear H0; intros; subst.
intro D2f; generalize (M f _ _  D2f (S1_in_R1 _ _ H)). 
simpl; destruct (symb_in_term f t2); simpl.
discriminate.
rewrite eq_symb_bool_refl; discriminate.
Qed.

Lemma acc_interp_acc :
  forall S1, inclusion _ S1 R1 -> forall s s', 
  Interp_dom R1 R2 s -> Interp s s' ->
  Acc (rdp_step (axiom (ddp S1)) (union _ R1 (Pi pi V0 V1))) s' -> Acc (rdp_step (axiom (ddp S1)) (union _ R1 R2)) s.
Proof.
intros S1 S1_in_R1 s s' Is Hs' Acc_s';
generalize s Is Hs'; clear s Is Hs';
induction Acc_s' as [s' Acc_s' IH].
intros s Is Hs'; apply Acc_intro; intros t t_R_s.
assert (It : Interp_dom R1 R2 t).
inversion t_R_s as [f l1 l2 t'' l2_R_l1 H ]; subst; clear t_R_s.
assert (Is2 : Interp_dom R1 R2 (Term f l2)).
inversion l2_R_l1 as [l | k2 k1 l2_R_l1']; clear l2_R_l1; subst.
assumption.
apply interp_dom_R1_R2_rwr with (Term f l1); trivial.
apply general_context; assumption.
inversion H as [t'' _s'' sigma K' K1 K2]; clear H; subst.
destruct K' as [K' Sub];
inversion K' as [s'' t' p f' l t''_S1_s'' H' Df H1 H2]; clear K'; subst.
rewrite <- K2 in Is2.
destruct (R1_at_top_dp _ S1_in_R1 _ _ _ _ t''_S1_s'' H' _ Is2)
               as [sigma' [_ [K _]]]; trivial.
destruct (interp_defined _ It) as [t' Ht'].
apply (IH t'); trivial.
apply (technical_lemma _ S1_in_R1 s s' t t'); trivial.
Qed.

Lemma wf_interp_acc :
  forall S1, inclusion _ S1 R1 -> 
  well_founded (rdp_step (axiom (ddp S1)) (union _ R1 (Pi pi V0 V1))) ->
  forall s, Interp_dom R1 R2 s ->   Acc (rdp_step (axiom (ddp S1)) (union _ R1 R2)) s.
Proof.
intros S1 S1_in_R1 wf s Is.
destruct (interp_defined _ Is) as [s' Hs'].
apply acc_interp_acc with s'; trivial.
Qed.

Lemma acc_interp_dom :
  forall t, Acc (one_step (union _ R1 R2)) t -> Interp_dom R1 R2 t.
Proof.
intros t Acc_t p f l Sub _.
apply acc_subterms_3 with p t; trivial.
Qed.

End Interp_definition.


Section Modular_termination.
Variable V0 : variable.
Variable V1 : variable.
Variable V0_diff_V1 : V0 <> V1.
Variable pi : symbol.
Variable bot : symbol.
Variable R1 : relation term.
Variable R2 : relation term.
Variable R3 : relation term.
Variable def_dec1 : forall f, {defined R1 f}+{~defined R1 f}.
Variable def_dec2 : forall f, {defined R2 f}+{~defined R2 f}.
Variable def_dec3 : forall f, {defined R3 f}+{~defined R3 f}.
Variable R1_red : term -> list term.
Variable R2_red : term -> list term.
Variable R3_red : term -> list term.
Variable FB1 : forall t s, one_step R1 s t <-> In s (R1_red t).
Variable FB2 : forall t s, one_step R2 s t <-> In s (R2_red t).
Variable FB3 : forall t s, one_step R3 s t <-> In s (R3_red t).
Variable module_R1_R2 : module R1 R2.
Variable module_R1_R3 : module R1 R3.
Variable R1_reg : forall s t, R1 s t -> forall x, In x (var_list s) -> In x (var_list t) .
Variable R2_reg : forall s t, R2 s t -> forall x, In x (var_list s) -> In x (var_list t) .
Variable R3_reg : forall s t, R3 s t -> forall x, In x (var_list s) -> In x (var_list t) .
Variable R1_var : forall v t, ~ R1 t (Var v).
Variable R2_var : forall v t, ~ R2 t (Var v).
Variable R3_var : forall v t, ~ R3 t (Var v).
Variable P1 : is_primary_pi pi R1.
Variable P2 : is_primary_pi pi R2.
Variable P3 : is_primary_pi pi R3.
Variable Indep2 :  forall s t f, defined R2 f -> R3 s t -> symb_in_term_list f (s :: t :: nil) = false.
Variable Indep3 : forall s t f, defined R3 f -> R2 s t -> symb_in_term_list f (s :: t :: nil) = false.
Variable W2 : well_founded (one_step (union _ (union _ R1 R2) (Pi pi V0 V1))).
Variable W3 : well_founded (rdp_step (axiom (ddp R3)) (union _ (union _ R1 R3) (Pi pi V0 V1))).

Lemma R132_reg' : 
    forall s t, union _ (union _ R1 R3) (union _ R2 (Pi pi V0 V1)) s t -> 
    forall x, In x (var_list s) -> In x (var_list t) .
Proof.
intros s t [[H1 | H3] | [H2 | HPi]].
apply (R1_reg _ _ H1).
apply (R3_reg _ _ H3).
apply (R2_reg _ _ H2).
inversion HPi as [ H1 |  H2].
intros x [x_eq_v1 | x_in_nil]; [idtac | contradiction].
subst; left; trivial.
intros x [x_eq_v1 | x_in_nil]; [idtac | contradiction].
subst; right; left; trivial.
Qed.

Lemma R123_reg' : 
    forall s t, union _ (union _ R1 R2) (union _ R3 (Pi pi V0 V1)) s t -> 
    forall x, In x (var_list s) -> In x (var_list t) .
Proof.
intros s t H; destruct H as [[H1 | H2] | [H3 | HPi]].
apply (R1_reg _ _ H1).
apply (R2_reg _ _ H2).
apply (R3_reg _ _ H3).
inversion HPi as [H1 | H2].
intros x [x_eq_v1 | x_in_nil]; [idtac | contradiction].
subst; left; trivial.
intros x [x_eq_v1 | x_in_nil]; [idtac | contradiction].
subst; right; left; trivial.
Qed.

Lemma R12_var' : forall (v : variable) (t :term), ~ (union _ (union _ R1 R2) (Pi pi V0 V1)) t (Var v).
Proof.
intros v u H; destruct H as [H12 | H].
destruct H12 as [H1 | H2].
apply (R1_var _ _ H1).
apply (R2_var _ _ H2).
inversion H.
Qed.

Lemma R123_var' : forall v t, ~ (union _ (union _ R1 R2) (union _ R3 (Pi pi V0 V1))) t (Var v).
Proof.
intros v t [[H1 | H2] | [H3 | HPi]].
apply (R1_var _ _ H1).
apply (R2_var _ _ H2).
apply (R3_var _ _ H3).
inversion HPi.
Qed.

Lemma R132_var' : forall v t, ~ (union _ (union _ R1 R3) (union _ R2 (Pi pi V0 V1))) t (Var v).
Proof.
intros v t [[H1 | H3] | [H2 | HPi]].
apply (R1_var _ _ H1).
apply (R3_var _ _ H3).
apply (R2_var _ _ H2).
inversion HPi.
Qed.

Lemma Incomp12 : forall f, defined R1 f -> defined R2 f -> False.
Proof.
inversion module_R1_R2 as [M2].
intros f D1 D2; inversion D1 as [h' l1 u1 H1]; clear D1; subst.
assert (H := M2 f u1 (Term f l1) D2 H1).
simpl in H; destruct (symb_in_term f u1).
discriminate.
revert H; simpl;
generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); [intros _; discriminate | intros f_diff_f; absurd (f=f); trivial].
Qed.

Lemma Incomp13 : forall f, defined R1 f -> defined R3 f -> False.
Proof.
inversion module_R1_R3 as [M3].
intros f D1 D3; inversion D1 as [h' l1 u1 H1]; clear D1; subst.
assert (H := M3 f u1 (Term f l1) D3 H1).
simpl in H; destruct (symb_in_term f u1).
discriminate.
revert H; simpl;
generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); [intros _; discriminate | intros f_diff_f; absurd (f=f); trivial].
Qed.

Lemma Incomp23 : forall f, defined R2 f -> defined R3 f -> False.
Proof.
intros f D2 D3; inversion D2 as [h' l2 u2 H2]; clear D2; subst.
assert (H := Indep3 u2 (Term f l2) f D3 H2).
simpl in H; destruct (symb_in_term f u2).
discriminate.
revert H; simpl;
generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); [intros _; discriminate | intros f_diff_f; absurd (f=f); trivial].
Qed.

Lemma Incomp : forall (R : relation term), is_primary_pi pi R -> ~defined R pi.
Proof.
intros R P D; inversion D as [f l u H]; subst f.
destruct (P u (Term pi l) H pi) as [_ F].
apply F; trivial.
revert F; simpl;
generalize (F.Symb.eq_bool_ok pi pi); case (F.Symb.eq_bool pi pi); [intros _ | intros pi_diff_pi; absurd (pi = pi)]; trivial.
Qed.

Definition Incomp1' := Incomp R1 P1.
Definition Incomp2' := Incomp R2 P2.
Definition Incomp3' := Incomp R3 P3.

Lemma Incomp123' :
  forall f, defined (union _ R1 R2) f -> defined (union _ R3 (Pi pi V0 V1)) f -> False.
Proof.
intros f D12f D3f';
inversion D12f as [f' l u [H1 | H2]]; clear D12f; subst;
inversion D3f' as [f'' l' u' [H3 | Hpi]]; clear D3f'; subst.
apply (Incomp13 f (Def R1 f l u H1) (Def R3 f l' u' H3)).
inversion Hpi; subst f; apply (Incomp1' (Def R1 pi l u H1)).
apply (Incomp23 f (Def R2 f l u H2) (Def R3 f l' u' H3)).
inversion Hpi; subst f; apply (Incomp2' (Def R2 pi l u H2)).
Qed.

Lemma split_dp_top :
  forall f g ls lt,
   axiom (ddp (union _ (union _ R1 R2) (union _ R3 (Pi pi V0 V1)))) (Term g lt) (Term f ls) ->
   ( (defined (union _ R1 R2) f /\ defined (union _ R1 R2) g) \/
     (defined R3 f /\ defined R3 g) \/
     (defined R3 f /\ defined (union _ R1 R2) g)).
Proof.
destruct module_R1_R2 as [M2].
destruct module_R1_R3 as [M3].
intros f g ls lt H.
inversion H as [_t _s sigma K]; clear H.
destruct K as [K Sub'];
inversion K as [s' t' p h l H' Sub Dh]; clear K; subst _s _t; subst.
destruct s' as [x' | f' ls'].
apply False_rect; apply (R123_var' _ _ H').
simpl in H1; injection H1; clear H1; intros; subst.
injection H0; clear H0; intros; subst. 
destruct H' as [H12 | [ H3 | HPi]].
inversion Dh as [h' l' u [K12 | [K3 | KPi]]]; clear Dh; subst.
left; split.
apply (Def _ _ _ _ H12).
apply (Def _ _ _ _ K12).
destruct H12 as [H1 | H2].
generalize (M3 g _ _ (Def R3 g l' u K3) H1).
simpl; rewrite (symb_in_subterm g _ _ Sub).
simpl; intro; discriminate.
simpl; generalize (F.Symb.eq_bool_ok g g); case (F.Symb.eq_bool g g); [intros _ | intros g_diff_g; absurd (g=g)]; trivial.
assert (F := Indep3 _ _ _ (Def _ _ _ _ K3) H2).
simpl in F; rewrite (symb_in_subterm g _ _ Sub) in F.
discriminate.
simpl; generalize (F.Symb.eq_bool_ok g g); case (F.Symb.eq_bool g g); [intros _ | intros g_diff_g; absurd (g=g)]; trivial.
inversion KPi; subst g l' u.
destruct H12 as [H1 | H2].
assert (H := P1 _ _ H1).
destruct (H pi) as [F _].
rewrite (symb_in_subterm pi _ _ Sub) in F.
absurd (pi=pi); trivial; apply F; trivial.
simpl; generalize (F.Symb.eq_bool_ok pi pi); case (F.Symb.eq_bool pi pi); [intros _ | intros pi_diff_pi; absurd (pi = pi)]; trivial.
assert (H := P2 _ _ H2).
destruct (H pi) as [F _].
rewrite (symb_in_subterm pi _ _ Sub) in F.
absurd (pi=pi); trivial; apply F; trivial.
simpl; generalize (F.Symb.eq_bool_ok pi pi); case (F.Symb.eq_bool pi pi); [intros _ | intros pi_diff_pi; absurd (pi = pi)]; trivial.
destruct H12 as [H1 | H2].
assert (H := P1 _ _ H1).
destruct (H pi) as [F _].
rewrite (symb_in_subterm pi _ _ Sub) in F.
absurd (pi=pi); trivial; apply F; trivial.
simpl; generalize (F.Symb.eq_bool_ok pi pi); case (F.Symb.eq_bool pi pi); [intros _ | intros pi_diff_pi; absurd (pi = pi)]; trivial.
assert (H := P2 _ _ H2).
destruct (H pi) as [F _].
rewrite (symb_in_subterm pi _ _ Sub) in F.
absurd (pi=pi); trivial; apply F; trivial.
simpl; generalize (F.Symb.eq_bool_ok pi pi); case (F.Symb.eq_bool pi pi); [intros _ | intros pi_diff_pi; absurd (pi = pi)]; trivial.

inversion Dh as [h' l' u K]; clear Dh; subst.
destruct K as [K12 | [K3 | KPi]].
destruct K12 as [K1 | K2].
right; right; split.
apply (Def _ _ _ _ H3).
apply (Def (union _ R1 R2) g l' u); left; trivial.
assert (F := Indep2 _ _ _ (Def _ _ _ _ K2) H3).
simpl in F; rewrite (symb_in_subterm g _ _ Sub) in F.
discriminate.
simpl; generalize (F.Symb.eq_bool_ok g g); case (F.Symb.eq_bool g g); [intros _ | intros g_diff_g; absurd (g=g)]; trivial.
right; left; split.
apply (Def _ _ _ _ H3).
apply (Def _ _ _ _ K3).

inversion KPi; subst g u l'.
assert (H := P3 _ _ H3).
destruct (H pi) as [F _].
rewrite (symb_in_subterm pi _ _ Sub) in F.
absurd (pi=pi); trivial; apply F; trivial.
simpl; generalize (F.Symb.eq_bool_ok pi pi); case (F.Symb.eq_bool pi pi); [intros _ | intros pi_diff_pi; absurd (pi = pi)]; trivial.
assert (H := P3 _ _ H3).
destruct (H pi) as [F _].
rewrite (symb_in_subterm pi _ _ Sub) in F.
absurd (pi=pi); trivial; apply F; trivial.
simpl; generalize (F.Symb.eq_bool_ok pi pi); case (F.Symb.eq_bool pi pi); [intros _ | intros pi_diff_pi; absurd (pi = pi)]; trivial.

inversion HPi; subst; destruct p; discriminate.
Qed.

Lemma split_rdp_step_top :
  forall R f g ls lt,
   rdp_step (axiom (ddp (union _ (union _ R1 R2) (union _ R3 (Pi pi V0 V1))))) R (Term g lt) (Term f ls) ->
   ( (defined (union _ R1 R2) f /\ defined (union _ R1 R2) g) \/
     (defined R3 f /\ defined R3 g) \/
     (defined R3 f /\ defined (union _ R1 R2) g)).
Proof.
intros R f g ls lt H; 
inversion H as [f' l1 l2 t3 H' H'']; subst.
apply (split_dp_top f g l2 lt); trivial.
Qed.

Lemma split_dp :
  forall s t,
   axiom (ddp (union _ (union _ (union _ R1 R2) R3) (Pi pi V0 V1))) s t ->
   (axiom (ddp (union _ R1 R2)) s t \/ 
   axiom (ddp R3) s t \/
   (exists t3, exists t1, exists p, exists f1, exists l1, exists sigma,
    R3 t1 t3 /\
   subterm_at_pos t1 p = Some (Term f1 l1) /\
   defined R1 f1 /\
   t = apply_subst sigma t3 /\
   s = apply_subst sigma (Term f1 l1))).
Proof.
inversion module_R1_R2 as [M2].
inversion module_R1_R3 as [M3].
intros _s _t _H; inversion _H as [s t sigma H]; clear _H; subst.
destruct H as [H Sub'];
inversion H as [s' t' p f l H' Sub Df]; clear H; subst.
destruct H' as [H123 | HPi].
destruct H123 as [H12 | H3].
inversion Df as [f' l' u K]; clear Df; subst.
destruct K as [K123 | KPi].
destruct K123 as [K12 | K3].
left; apply instance; split; [apply Dp with t' p |idtac]; trivial.
apply (Def _ _ _ _ K12).
destruct H12 as [H1 | H2].
generalize (M3 f t' _ (Def R3 f l' u K3) H1).
simpl; rewrite (symb_in_subterm f _ _ Sub).
simpl; intro; discriminate.
simpl; rewrite eq_symb_bool_refl; apply eq_refl.
assert (F := Indep3 _ _ _ (Def _ _ _ _ K3) H2).
simpl in F; destruct (symb_in_term f t).
destruct (symb_in_term f t'); discriminate.
rewrite (symb_in_subterm f _ _ Sub) in F.
discriminate.
simpl; rewrite eq_symb_bool_refl; trivial.
inversion KPi; subst f u l'.
destruct H12 as [H1 | H2].
assert (H := P1 _ _ H1).
destruct (H pi) as [F _].
rewrite (symb_in_subterm pi _ _ Sub) in F.
absurd (pi=pi); trivial; apply F; trivial.
simpl; rewrite eq_symb_bool_refl; trivial.
assert (H := P2 _ _ H2).
destruct (H pi) as [F _].
rewrite (symb_in_subterm pi _ _ Sub) in F.
absurd (pi=pi); trivial; apply F; trivial.
simpl; rewrite eq_symb_bool_refl; trivial.
destruct H12 as [H1 | H2].
assert (H := P1 _ _ H1).
destruct (H pi) as [F _].
rewrite (symb_in_subterm pi _ _ Sub) in F.
absurd (pi=pi); trivial; apply F; trivial.
simpl; rewrite eq_symb_bool_refl; trivial.
assert (H := P2 _ _ H2).
destruct (H pi) as [F _].
rewrite (symb_in_subterm pi _ _ Sub) in F.
absurd (pi=pi); trivial; apply F; trivial.
simpl; rewrite eq_symb_bool_refl; trivial.

inversion Df as [f' l' u K]; clear Df; subst.
destruct K as [K123 | KPi].
destruct K123 as [K12 | K3].
destruct K12 as [K1 | K2].
right; right; trivial.
exists t; exists t'; exists p; exists f; exists l; exists sigma; split; trivial.
split; trivial.
split.
apply (Def _ _ _ _ K1).
split; trivial.
assert (F := Indep2 _ _ _ (Def _ _ _ _ K2) H3).
simpl in F; destruct (symb_in_term f t).
destruct (symb_in_term f t'); discriminate.
rewrite (symb_in_subterm f _ _ Sub) in F.
discriminate.
simpl; rewrite eq_symb_bool_refl; trivial.
right; left; apply instance; split; [apply Dp with t' p | idtac]; trivial.
apply (Def _ _ _ _ K3).

inversion KPi; subst f u l'.
assert (H := P3 _ _ H3).
destruct (H pi) as [F _].
rewrite (symb_in_subterm pi _ _ Sub) in F.
absurd (pi=pi); trivial; apply F; trivial.
simpl; rewrite eq_symb_bool_refl; trivial.
assert (H := P3 _ _ H3).
destruct (H pi) as [F _].
rewrite (symb_in_subterm pi _ _ Sub) in F.
absurd (pi=pi); trivial; apply F; trivial.
simpl; rewrite eq_symb_bool_refl; trivial.

inversion HPi; subst; destruct p; discriminate.
Qed.

Lemma split_rdp_step :
  forall R s t,
   rdp_step (axiom (ddp (union _ (union _ (union _ R1 R2) R3) (Pi pi V0 V1)))) R s t ->
   (rdp_step (axiom (ddp (union _ R1 R2))) R s t \/
   rdp_step (axiom (ddp R3)) R s t \/
   (exists t1, exists f3, exists l2, exists p, exists f1, exists l1, exists sigma, exists l3,
   R3 t1 (Term f3 l2) /\ 
   subterm_at_pos t1 p = Some (Term f1 l1) /\
   defined R1 f1 /\
   (rwr_list (one_step R) (map (apply_subst sigma) l2) l3 \/
    map (apply_subst sigma) l2 = l3) /\
   t = Term f3 l3 /\
   s = apply_subst sigma (Term f1 l1))).
Proof.
intros R s t H.
destruct H as [f l1 l2 t3 H' H''].
destruct (split_dp _ _ H'') as [H1 | [H2 | H2]]; clear H''.
left; apply Rdp_step with l2; trivial.
right; left; apply Rdp_step with l2; trivial.
right; right.
destruct H2 as [t3' [t1 [p [f1 [l2' [sigma [K3 [Sub' [Df1 [K1 K2]]]]]]]]]].
destruct t3' as [v3 | f3 l3].
absurd (R3 t1 (Var v3)); trivial; apply R3_var.
exists t1; exists f3; exists l3; exists p; exists f1.
exists l2'; exists sigma.
exists l1; split; trivial.
split; trivial.
split; trivial.
simpl in K1; injection K1; clear K1; intros K1 f_eq_f3.
split.
subst l2.
destruct H'; [right | left]; trivial.
split; trivial.
subst f; trivial.
Qed.

Fixpoint Pi_red (t : term) : list term :=
   match t with
   | Var _ => nil
   | Term f l =>
      let Pi_red_list :=
         (fix Pi_red_list (l : list term) {struct l} : list (list term) :=
            match l with
            | nil => nil
            | t :: lt => (map (fun t' => t' :: lt) (Pi_red t)) ++
                             (map (fun l' => t :: l') (Pi_red_list lt))
            end) in
    if F.Symb.eq_bool f pi
    then 
      match l with
              | t1 :: t2 :: nil => t1 :: t2 :: map (fun l' => Term pi l') (Pi_red_list l)
              | _ =>map (fun l' => Term pi l') (Pi_red_list l)
              end
    else map (fun l' => Term f l') (Pi_red_list l)
   end.

Fixpoint Pi_red_list (l : list term) {struct l} : list (list term) :=
            match l with
            | nil => nil
            | t :: lt => (map (fun t' => t' :: lt) (Pi_red t)) ++
                             (map (fun l' => t :: l') (Pi_red_list lt))
            end.

Lemma FB_Pi : forall s t, one_step (Pi pi V0 V1) t s <-> In t (Pi_red s).
Proof.
intros s; pattern s; apply term_rec3; clear s.
intros s t; simpl; split; intro H.
inversion H; subst.
inversion H0; subst.
destruct t2 as [v2 | f2 l2].
inversion H3.
discriminate.
contradiction.

intros f l IH t; split; intro H.
inversion H; clear H; subst.
inversion H0; clear H0; subst.
destruct t2 as [v2 | f2 l2]; inversion H2; clear H2; subst f2; subst.
simpl in H; injection H; clear H; intros H f2_eq_f; subst f.
simpl Pi_red.
simpl; generalize (F.Symb.eq_bool_ok pi pi); case (F.Symb.eq_bool pi pi); [intros _; left | intros pi_diff_pi; absurd (pi = pi)]; trivial.
simpl in H; injection H; clear H; intros H f2_eq_f; subst f.
simpl Pi_red.
simpl; generalize (F.Symb.eq_bool_ok pi pi); case (F.Symb.eq_bool pi pi); [intros _; right; left | intros pi_diff_pi; absurd (pi = pi)]; trivial.

assert (H' : In l1 (Pi_red_list l)).
induction H2; simpl.
apply in_or_app; left.
rewrite in_map_iff.
exists t1; split; trivial.
rewrite <- IH; trivial; left; trivial.
apply in_or_app; right.
rewrite in_map_iff; exists l1; split; trivial.
apply IHone_step_list; trivial.
intros; apply IH; right; trivial.
simpl; generalize (F.Symb.eq_bool_ok f pi); case (F.Symb.eq_bool f pi); [intros f_eq_pi | intros f_diff_pi].
subst f; destruct l as [ | t1 [ | t2 [ | t3 l]]].
contradiction.
rewrite in_map_iff; exists l1; split; trivial.
right; right; rewrite in_map_iff; exists l1; split; trivial.
rewrite in_map_iff; exists l1; split; trivial.
rewrite in_map_iff; exists l1; split; trivial.
assert (H' : forall l', In l'
      ((fix Pi_red_list (l : list term) : list (list term) :=
          match l with
          | nil => nil (A:=list term)
          | t :: lt =>
              map (fun t' : term => t' :: lt) (Pi_red t) ++
              map (fun l' : list term => t :: l') (Pi_red_list lt)
          end) l) -> one_step_list (one_step (Pi pi V0 V1)) l' l).
intros l' H'.
assert (H'' : In l' (Pi_red_list l)).
clear IH H; induction l as [ | s l]; trivial.
generalize l' H''; clear l' H H' H''; induction l as [ | s l]; intros l' H''.
contradiction.
simpl in H''; destruct (in_app_or _ _ _ H'') as [H1 | H2].
rewrite in_map_iff in H1; destruct H1 as [t' [H1' H1]]; subst l'.
apply head_step.
rewrite IH; trivial.
left; trivial.
rewrite in_map_iff in H2; destruct H2 as [l'' [H2' H2]]; subst l'.
apply tail_step.
apply IHl; trivial.
intros; apply IH; right; trivial.


revert H; simpl.
generalize (F.Symb.eq_bool_ok f pi); case (F.Symb.eq_bool f pi); [intros f_eq_pi | intros f_diff_pi].
subst f; destruct l as [ | t1 [ | t2 [ | t3 l]]].
apply False_rect.
intro H; rewrite in_map_iff in H; destruct H as [l' [H'' H]]; subst t.
apply in_context; apply H'; trivial.
intros [t_eq_t1 | [t_eq_t2 | H]].
assert (H1sigma : t1 = apply_subst 
                                        ((V0,t1) :: (V1,t2) :: nil)
                                        (Var V0)).
simpl; generalize (X.eq_bool_ok V0 V0); case (X.eq_bool V0 V0); [intros _ | intros V0_diff_V0; absurd (V0 = V0)]; trivial.
assert (H2sigma : Term pi  (t1 :: t2 :: nil) =
                             apply_subst 
                                   ((V0,t1) :: (V1,t2) :: nil)
                                   (Term pi (Var V0 :: Var V1 :: nil))).
simpl; generalize (X.eq_bool_ok V0 V0); case (X.eq_bool V0 V0); [intros _ | intros V0_diff_V0; absurd (V0 = V0)]; trivial.
generalize (X.eq_bool_ok V1 V0); case (X.eq_bool V1 V0); [intros V1_eq_V0; absurd (V0 = V1); trivial; subst V0 | intros _]; trivial.
simpl; generalize (X.eq_bool_ok V1 V1); case (X.eq_bool V1 V1); [intros _ | intros V1_diff_V1; absurd (V1 = V1)]; trivial.
subst t; pattern t1 at 1.
rewrite H1sigma.
pattern t1 at 1.
rewrite H2sigma.
apply at_top.
apply instance.
apply Pi1.

assert (H1sigma : t2 = apply_subst 
                                        ((V0,t1) :: (V1,t2) :: nil)
                                        (Var V1)).
simpl; generalize (X.eq_bool_ok V1 V0); case (X.eq_bool V1 V0); [intros V1_eq_V0; absurd (V0 = V1); trivial; subst V0 | intros _]; trivial.
simpl; generalize (X.eq_bool_ok V1 V1); case (X.eq_bool V1 V1); [intros _ | intros V1_diff_V1; absurd (V1 = V1)]; trivial.

assert (H2sigma : Term pi  (t1 :: t2 :: nil) =
                             apply_subst 
                                   ((V0,t1) :: (V1,t2) :: nil)
                                   (Term pi (Var V0 :: Var V1 :: nil))).
simpl; generalize (X.eq_bool_ok V0 V0); case (X.eq_bool V0 V0); [intros _ | intros V0_diff_V0; absurd (V0 = V0)]; trivial.
simpl; generalize (X.eq_bool_ok V1 V0); case (X.eq_bool V1 V0); [intros V1_eq_V0; absurd (V0 = V1); trivial; subst V0 | intros _]; trivial.
simpl; generalize (X.eq_bool_ok V1 V1); case (X.eq_bool V1 V1); [intros _ | intros V1_diff_V1; absurd (V1 = V1)]; trivial.
subst t; pattern t2 at 1.
rewrite H1sigma.
pattern t2 at 1.
rewrite H2sigma.
apply at_top.
apply instance.
apply Pi2.

rewrite map_app in H; destruct (in_app_or _ _ _ H) as [H1 | H2]; clear H.
rewrite in_map_iff in H1; destruct H1 as [l' [H'' H]]; subst t.
apply in_context; apply H'; apply in_or_app; left; trivial.
simpl in H2; rewrite <- app_nil_end in H2.
rewrite in_map_iff in H2; destruct H2 as [l' [H'' H]]; subst t.
apply in_context; apply H'; apply in_or_app; right.
simpl; rewrite <- app_nil_end; trivial.

intro H; rewrite in_map_iff in H; destruct H as [l' [H'' H]]; subst t.
apply in_context; apply H'; trivial.
intro H; rewrite in_map_iff in H; destruct H as [l' [H'' H]]; subst t.
apply in_context; apply H'; trivial.
Qed.

Lemma def_dec3' : forall f : symbol, {defined (union _ R3 (Pi pi V0 V1)) f} + {~ defined (union _ R3 (Pi pi V0 V1)) f}.
Proof.
intros f; destruct (def_dec3 f) as [Df | Cf].
left; inversion Df as [f' l s H]; subst.
apply (Def (union _ R3 (Pi pi V0 V1)) f l s); left; trivial.
generalize (F.Symb.eq_bool_ok f pi); case (F.Symb.eq_bool f pi); [intros f_eq_pi | intros f_diff_pi].
subst f; left; apply (Def (union _ R3 (Pi pi V0 V1)) pi (Var V0 :: Var V1 :: nil) (Var V0)).
right; apply Pi1.
right; intro Df; inversion Df as [f' l s [H3 | Hpi]]; subst.
apply Cf; apply (Def R3 f l s); trivial.
inversion Hpi; subst f; absurd (pi = pi); trivial.
Qed.

Lemma R3_var' : forall (v : variable) (t :term), ~ (union _ R3 (Pi pi V0 V1)) t (Var v).
Proof.
intros v u [H3 | HPi].
apply (R3_var _ _ H3).
inversion HPi.
Qed.

Lemma R12_var : forall (v : variable) (t :term), ~ (union _ R1 R2) t (Var v).
Proof.
intros v u [H1 | H2].
apply (R1_var _ _ H1).
apply (R2_var _ _ H2).
Qed.

Lemma R12_reg : forall s t : term,
         union term R1 R2 s t ->
         forall x : variable, In x (var_list s) -> In x (var_list t).
Proof.
intros s t [H1 | H2] x x_in_s.
apply R1_reg with s; trivial.
apply R2_reg with s; trivial.
Qed.

Lemma module123' : module (union term R1 R2) (union term R3 (Pi pi V0 V1)).
Proof.
inversion module_R1_R2 as [M2].
inversion module_R1_R3 as [M3].
apply Mod.
intros f s t Df [H1 | H2].
inversion Df as [f' l u [H3 | HPi]]; subst.
apply M3; trivial; apply (Def R3 f l u); trivial.
inversion HPi; subst f; subst.
destruct (P1 s t H1 pi) as [Hs Ht].
simpl; destruct (symb_in_term pi s).
absurd (pi = pi); trivial; apply Hs; trivial.
destruct (symb_in_term pi t).
absurd (pi = pi); trivial; apply Ht; trivial.
trivial.
destruct (P1 s t H1 pi) as [Hs Ht].
simpl; destruct (symb_in_term pi s).
absurd (pi = pi); trivial; apply Hs; trivial.
destruct (symb_in_term pi t).
absurd (pi = pi); trivial; apply Ht; trivial.
trivial.
inversion Df as [f' l u [H3 | HPi]]; subst.
apply Indep3; trivial; apply (Def R3 f l u); trivial.
inversion HPi; subst f; subst.
destruct (P2 s t H2 pi) as [Hs Ht].
simpl; destruct (symb_in_term pi s).
absurd (pi = pi); trivial; apply Hs; trivial.
destruct (symb_in_term pi t).
absurd (pi = pi); trivial; apply Ht; trivial.
trivial.
destruct (P2 s t H2 pi) as [Hs Ht].
simpl; destruct (symb_in_term pi s).
absurd (pi = pi); trivial; apply Hs; trivial.
destruct (symb_in_term pi t).
absurd (pi = pi); trivial; apply Ht; trivial.
trivial.
Qed.

Lemma W12' : well_founded (rdp_step (axiom (ddp (union _ R1 R2))) (union _ (union _ R1 R2) (Pi pi V0 V1))).
Proof.
assert (W2' := dp_necessary _ R12_var' W2).
refine (wf_incl _ _ _ _ W2').
clear; intros s t H; inversion H; clear H; subst.
apply Rdp_step with l2; trivial.
inversion H1; clear H1; subst.
apply instance.
apply dp_incl with (union _ R1 R2).
do 3 intro; left; assumption.
apply ddp_is_dp; assumption.
Qed.

Definition T12 := 
     wf_interp_acc V0 V1 V0_diff_V1 pi bot 
                           (union _ R1 R2) (union _ R3 (Pi pi V0 V1)) R12_reg R12_var R3_var'
                           module123' def_dec3' _ _
                           (fun s t => FB12 _ _ _ _ FB1 FB2 t s) 
                           (fun s t => FB12 _ _ _ _ FB3 FB_Pi t s)
                           (union _ R1 R2) (fun s t H => H) W12'.

Lemma def_dec2' : 
   forall f : symbol, {defined (union _ R2 (Pi pi V0 V1)) f} + {~ defined (union _ R2 (Pi pi V0 V1)) f}.
Proof.
intros f; destruct (def_dec2 f) as [Df | Cf].
left; inversion Df as [f' l s H]; subst.
apply (Def (union _ R2 (Pi pi V0 V1)) f l s); left; trivial.
generalize (F.Symb.eq_bool_ok f pi); case (F.Symb.eq_bool f pi); [intros f_eq_pi | intros f_diff_pi].
subst f; left; apply (Def (union _ R2 (Pi pi V0 V1)) pi (Var V0 :: Var V1 :: nil) (Var V0)).
right; apply Pi1.
right; intro Df; inversion Df as [f' l s [H2 | Hpi]]; subst.
apply Cf; apply (Def R2 f l s); trivial.
inversion Hpi; subst f; absurd (pi = pi); trivial.
Qed.

Lemma R2_var' : forall (v : variable) (t :term), ~ (union _ R2 (Pi pi V0 V1)) t (Var v).
Proof.
intros v u [H2 | HPi].
apply (R2_var _ _ H2).
inversion HPi.
Qed.

Lemma R13_var : forall (v : variable) (t :term), ~ (union _ R1 R3) t (Var v).
Proof.
intros v u [H1 | H3].
apply (R1_var _ _ H1).
apply (R3_var _ _ H3).
Qed.

Lemma R13_reg : forall s t : term,
         union term R1 R3 s t ->
         forall x : variable, In x (var_list s) -> In x (var_list t).
Proof.
intros s t [H1 | H3] x x_in_s.
apply R1_reg with s; trivial.
apply R3_reg with s; trivial.
Qed.

Lemma module132' : module (union term R1 R3) (union term R2 (Pi pi V0 V1)).
Proof.
inversion module_R1_R3 as [M3].
inversion module_R1_R2 as [M2].
apply Mod.
intros f s t Df [H1 | H3].
inversion Df as [f' l u [H2 | HPi]]; subst.
apply M2; trivial; apply (Def R2 f l u); trivial.
inversion HPi; subst f; subst.
destruct (P1 s t H1 pi) as [Hs Ht].
simpl; destruct (symb_in_term pi s).
absurd (pi = pi); trivial; apply Hs; trivial.
destruct (symb_in_term pi t).
absurd (pi = pi); trivial; apply Ht; trivial.
trivial.
destruct (P1 s t H1 pi) as [Hs Ht].
simpl; destruct (symb_in_term pi s).
absurd (pi = pi); trivial; apply Hs; trivial.
destruct (symb_in_term pi t).
absurd (pi = pi); trivial; apply Ht; trivial.
trivial.
inversion Df as [f' l u [H2 | HPi]]; subst.
apply Indep2; trivial; apply (Def R2 f l u); trivial.
inversion HPi; subst f; subst.
destruct (P3 s t H3 pi) as [Hs Ht].
simpl; destruct (symb_in_term pi s).
absurd (pi = pi); trivial; apply Hs; trivial.
destruct (symb_in_term pi t).
absurd (pi = pi); trivial; apply Ht; trivial.
trivial.
destruct (P3 s t H3 pi) as [Hs Ht].
simpl; destruct (symb_in_term pi s).
absurd (pi = pi); trivial; apply Hs; trivial.
destruct (symb_in_term pi t).
absurd (pi = pi); trivial; apply Ht; trivial.
trivial.
Qed.

Definition T3 := 
         wf_interp_acc V0 V1 V0_diff_V1 pi bot 
                               (union _ R1 R3) (union _ R2 (Pi pi V0 V1)) 
                               R13_reg R13_var R2_var' module132' 
                               def_dec2' _ _
                               (fun s t => FB12 _ _ _ _  FB1 FB3 t s) 
                               (fun s t => FB12 _ _ _ _  FB2 FB_Pi t s) 
                               R3 (fun s t H => (or_intror _ H)) W3.

Lemma def_dec123' : 
   forall f : symbol,
     {constructor (union term (union term R1 R2) (union _ R3 (Pi pi V0 V1))) f} +
     {defined (union term (union term R1 R2) (union _ R3 (Pi pi V0 V1))) f}.
Proof.
intros f; generalize (F.Symb.eq_bool_ok f pi); case (F.Symb.eq_bool f pi); [intros f_eq_pi | intros f_diff_pi].
subst; right.
refine (Def _ pi (Var V0 :: Var V1 :: nil) (Var V0) _).
do 2 right; apply Pi1.
destruct (def_dec1 f) as [D1f | C1f].
right; inversion D1f as [f' k t H1]; subst f'.
refine (Def _ f k t _); do 2 left; trivial.
destruct (def_dec2 f) as [D2f | C2f].
right; inversion D2f as [f' k t H1]; subst f'.
refine (Def _ f k t _); do 1 left; right; trivial.
destruct (def_dec3 f) as [D3f | C3f].
right; inversion D3f as [f' k t H1]; subst f'.
refine (Def _ f k t _); right; left; trivial.
left; assert (Cf : forall k t, ~ (union _ (union _ R1 R2) (union _ R3 (Pi pi V0 V1))) t (Term f k)).
intros k t  [[H1 | H2] | [H3 | HPi]].
apply C1f; apply (Def _ _ _ _ H1).
apply C2f; apply (Def _ _ _ _ H2).
apply C3f; apply (Def _ _ _ _ H3).
inversion HPi; subst; absurd (f=f); trivial.
apply Const; trivial.
Qed.

Lemma def_dec132' : 
   forall f : symbol,
     {constructor (union term (union term R1 R3) (union _ R2 (Pi pi V0 V1))) f} +
     {defined (union term (union term R1 R3) (union _ R2 (Pi pi V0 V1))) f}.
Proof.
intros f; generalize (F.Symb.eq_bool_ok f pi); case (F.Symb.eq_bool f pi); [intros f_eq_pi | intros f_diff_pi].
subst; right.
refine (Def _ pi (Var V0 :: Var V1 :: nil) (Var V0) _).
do 2 right; apply Pi1.
destruct (def_dec1 f) as [D1f | C1f].
right; inversion D1f as [f' k t H1]; subst f'.
refine (Def _ f k t _); do 2 left; trivial.
destruct (def_dec2 f) as [D2f | C2f].
right; inversion D2f as [f' k t H1]; subst f'.
refine (Def _ f k t _); right; left; trivial.
destruct (def_dec3 f) as [D3f | C3f].
right; inversion D3f as [f' k t H1]; subst f'.
refine (Def _ f k t _); left; right; trivial.
left; assert (Cf : forall k t, ~ (union _ (union _ R1 R3) (union _ R2 (Pi pi V0 V1))) t (Term f k)).
intros k t  [[H1 | H3] | [H2 | HPi]].
apply C1f; apply (Def _ _ _ _ H1).
apply C3f; apply (Def _ _ _ _ H3).
apply C2f; apply (Def _ _ _ _ H2).
inversion HPi; subst; absurd (f=f); trivial.
apply Const; trivial.
Qed.

Lemma modular_var : forall v, 
                      Acc (ddp_step (union term (union term R1 R2) (union _ R3 (Pi pi V0 V1)))) (Var v).
Proof.
intro x; apply Acc_intro; intros s H; inversion H; subst.
Qed.

Lemma def_dec12 : 
  forall f : symbol, {defined (union _ R1 R2) f} + {~ defined (union _ R1 R2) f}.
Proof.
intro f; destruct (def_dec1 f) as [D1f | C1f].
left; inversion D1f as [f' k t H1]; subst f'.
refine (Def _ f k t _); left; trivial.
destruct (def_dec2 f) as [D2f | C2f].
left; inversion D2f as [f' k t H1]; subst f'.
refine (Def _ f k t _); right; trivial.
right; intros Df; inversion Df as [f' k t [H1 | H2]]; subst f'.
apply C1f; apply (Def _ _ _ _ H1).
apply C2f; apply (Def _ _ _ _ H2).
Qed.

Lemma Dummy :
   forall t, Acc (one_step (union term (union term R1 R2) (union term R3 (Pi pi V0 V1)))) t <->
              Acc (one_step (union term (union term R1 R3) (union term R2 (Pi pi V0 V1)))) t.
Proof.
intros t; split; apply Acc_incl;
clear t; intros t1 t2; apply one_step_incl.
clear t1 t2; intros t1 t2 [[H1 | H3] | [H2 | Hpi]].
left; left; trivial.
right; left; trivial.
left; right; trivial.
right; right; trivial.
clear t1 t2; intros t1 t2 [[H1 | H2] | [H3 | Hpi]].
left; left; trivial.
right; left; trivial.
left; right; trivial.
right; right; trivial.
Qed.

Lemma Case12 :
  forall f l, defined (union _ R1 R2) f ->
             (Interp_dom (union term R1 R2) (union term R3 (Pi pi V0 V1)) (Term f l)) ->
              Acc (ddp_step (union term (union term R1 R2) (union term R3 (Pi pi V0 V1))))
                     (Term f l).
Proof.
intros f l D12 It.
inversion D12 as [f' k u H12]; subst.
assert (Ts := T12 _ It).
assert (D12' : match Term f l with
                     | Var _ => False
                     | Term g _ => defined (union _ R1 R2) g
                     end).
trivial.
generalize (Term f l) Ts D12' It; clear f l It Ts D12' D12 H12.
intros t Acc_t; induction Acc_t as [[ v | f l] Acc_t IH]; intros D12f It.
contradiction.
(* 1/1 goal is now 
    Acc (ddp_step (union term (union term R1 R2) (union term R3 (Pi pi)))) (Term f l) *)
apply Acc_intro; intros t H.
assert (Simple_step : 
forall l
(IH : forall y : term,
     rdp_step (axiom (ddp (union term R1 R2)))
       (union term (union term R1 R2) (union term R3 (Pi pi V0 V1))) y (Term f l) ->
     match y with
     | Var _ => False
     | Term g _ => defined (union term R1 R2) g
     end ->
     Interp_dom (union term R1 R2) (union term R3 (Pi pi V0 V1)) y ->
     Acc (ddp_step (union term (union term R1 R2) (union term R3 (Pi pi V0 V1)))) y)
(It : Interp_dom (union term R1 R2) (union term R3 (Pi pi V0 V1)) (Term f l))
(t : term)
(H : axiom (ddp (union term (union term R1 R2) (union term R3 (Pi pi V0 V1)))) t (Term f l)),
Acc (ddp_step (union term (union term R1 R2) (union term R3 (Pi pi V0 V1)))) t).
(* 1/2 simple RDP step *)
clear l Acc_t IH It t H;
intros l IH It t Hm.
inversion Hm as [_t s sigma _Hm K1 K2]; subst.
destruct _Hm as [_Hm _Sub].
inversion _Hm as [_s t p g'' k'' t_R_s Sub Df'' H1 H']; clear _Hm; subst.
destruct t as [v | f' k'].
destruct p; discriminate.
destruct (split_dp_top _ _ _ _ Hm) as [D12' | [D13 | D3]]; clear Hm.
(* 1/4 the new top symbol is also defined in R1 U R2 -> dp of type {1,2}x{1,2} *)
destruct D12' as [Df Dg].
assert (t_R12_s : (union term R1 R2) (Term f' k') s).
clear k; destruct s as [ v | g k].
absurd (union term (union term R1 R2) (union term R3 (Pi pi V0 V1)) (Term f' k') (Var v)); trivial.
intros [[H1 | H2] | [H3 | Hpi]].
apply (R1_var _ _ H1).
apply (R2_var _ _ H2).
apply (R3_var _ _ H3).
inversion Hpi.
simpl in K2; injection K2; clear K2; intros H' f_eq_g; subst.
destruct t_R_s as [H12 | H3']; trivial.
destruct module123' as [M].
clear u; inversion Df as [f'' l u H12]; subst.
assert (F := M f _ _ (Def (union _ R3 (Pi pi V0 V1)) f k (Term f' k') H3') H12).
simpl in F; destruct (symb_in_term f u).
discriminate.
rewrite eq_symb_bool_refl in F; discriminate.
assert (H : rdp_step (axiom (ddp (union term R1 R2))) (union term (union term R1 R2) (union term R3 (Pi pi V0 V1))) 
                           (Term g'' (map (apply_subst sigma) k'')) 
                           (Term f l)).
apply Rdp_step with l.
left.
clear k; destruct s as [ v | g k].
absurd ((union term R1 R2) (Term f' k') (Var v)); trivial.
intros [H1 | H2].
apply (R1_var _ _ H1).
apply (R2_var _ _ H2).
simpl in K2; injection K2; clear K2; intros H' f_eq_g; subst.
refine (instance _ (Term g'' k'') (Term f k) sigma _).
split; [apply (Dp (union _ R1 R2) (Term f k) (Term f' k') p g'' k'') | idtac]; trivial.
apply IH; trivial.
(* 1/4 goal is now 
  Interp_dom (union term R1 R2) (union term R3 (Pi pi))  (Term g'' (map (apply_subst sigma) k'')) *)
assert (s_not_in_F3 : forall g : symbol, symb_in_term g s = true -> ~ defined (union term R3 (Pi pi V0 V1)) g).
intros g g_in_s D3g.
destruct module123' as [M].
assert (H'' := M g _ _ D3g t_R12_s).
change ((symb_in_term g (Term f' k') || (symb_in_term g s || false))%bool =
        false) in H''.
rewrite g_in_s in H''; destruct (symb_in_term g (Term f' k')); discriminate.
destruct s as [v | ff ll].
absurd (union term R1 R2 (Term f' k') (Var v)); trivial.
apply R12_var.

assert (f'k'_not_in_F3 : forall g : symbol, symb_in_term g (Term f' k') = true -> ~ defined (union term R3 (Pi pi V0 V1)) g). 
intros g g_in_s D3g.
destruct module123' as [M].
assert (H'' := M g _ _ D3g t_R12_s).
pattern (Term f' k') in H''; simpl symb_in_term_list in H''; cbv beta in H''.
simpl symb_in_term_list in H''; fold symb_in_term_list in H''.
simpl in g_in_s; fold symb_in_term_list in g_in_s.
rewrite g_in_s in H''; discriminate.
assert (interp_dom_var : forall v, In v (var_list (Term ff ll))
              ->  Interp_dom (union term R1 R2) (union term R3 (Pi pi V0 V1)) (apply_subst sigma (Var v))).
intros v v_in_s'.
rewrite <- K2 in It.
exact (interp_dom_subst (union term R1 R2) (union term R3 (Pi pi V0 V1)) _ sigma It v v_in_s').
intros [ | i q] h kk Sub' D3h.
simpl in Sub'; injection Sub'; clear Sub'; intros; subst.
apply False_rect.
destruct module123' as [M].
inversion Dg as [g' kk v H1 H2]; subst.
generalize (M h _ _ D3h H1); simpl.
destruct (symb_in_term h v).
discriminate.
rewrite eq_symb_bool_refl; discriminate.

generalize (subterm_in_instantiated_term _ _ _ Sub').
case_eq (subterm_at_pos (Term g'' k'') (i :: q)).
intros t Sub4 K.
assert (Sub5 := subterm_in_subterm _ _ _ Sub Sub4).
destruct t as [v | h' ll'].
assert (v_in_s : In v (var_list (Term ff ll))).
apply R12_reg with (Term f' k'); trivial.
apply var_in_subterm with  (Var v) (p ++ i :: q); trivial.
left; trivial.
apply (interp_dom_var v v_in_s nil); trivial.
rewrite K; trivial.
simpl in K; injection K; clear K; intros; subst.
absurd (defined (union term R3 (Pi pi V0 V1)) h'); trivial.
apply f'k'_not_in_F3.
rewrite (symb_in_subterm h' _ _ Sub5); trivial.
simpl; rewrite eq_symb_bool_refl; trivial.
intros _ [v [q' [q'' [H1 [v_in_g''k'' [Sub3 Sub4]]]]]].
assert (v_in_s : In v (var_list (Term ff ll))).
apply R12_reg with (Term f' k'); trivial.
apply var_in_subterm with  (Term g'' k'') p; trivial.
apply (interp_dom_var v v_in_s q''); trivial.

(* 1/3 the old top symbol is defined in R1 U R3 -> contradiction *)
destruct D13 as [D3 _].
destruct module123' as [M].
clear k u; inversion D12f as [g k u H12]; subst.
inversion D3 as [g' k''' u' H3]; subst.
assert (F := M f _ _ (Def (union _ R3 (Pi pi V0 V1)) f k''' u' (or_introl _ H3)) H12).
simpl in F; destruct (symb_in_term f u).
discriminate.
simpl in F; revert F; 
generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); [intros _ | intros f_diff_f; absurd (f =f); trivial].
intro; discriminate.

(* 1/2 the old top symbol is defined in R3 -> contradiction *)
destruct D3 as [D3 _].
destruct module123' as [M].
clear k u; inversion D12f as [g k u H12]; subst.
inversion D3 as [g' k''' u' H3]; subst.
assert (F := M f _ _ (Def (union _ R3 (Pi pi V0 V1)) f k''' u' (or_introl _ H3)) H12).
simpl in F; destruct (symb_in_term f u).
discriminate.
rewrite eq_symb_bool_refl in F; discriminate.

clear k; inversion H as [g k l' s'' l_R_l' Hm]; clear H; subst.
apply (Simple_step l'); trivial.
intros [v | g k] H D12 Iu.
contradiction.
apply IH; trivial.
inversion H as [g' k' l'' s''' l'_R_l'' Hm']; clear H; subst.
apply Rdp_step with l''; trivial.
apply refl_trans_clos_is_trans with l'; trivial.

intros [ | i p] g k Sub Dg.
simpl in Sub; injection Sub; clear Sub; intros; subst g k.
assert False; [apply (Incomp123' f); trivial | contradiction].
inversion l_R_l' as [l1 | l1 l1' l1_R_l1']; clear l_R_l'; subst.
apply (It (i :: p)); trivial.
assert (It' := interp_dom_R1_R2_rwr _ _ module123' def_dec3' R12_reg R3_var'
                        _ _ It (general_context _ f _ _ l1_R_l1')).
apply (It' (i :: p)); trivial.
Qed.

Lemma Case3 : 
  forall f l, defined R3 f ->
                  ( forall t : term,
                    In t l ->
                       Acc (one_step (union term (union term R1 R3) (union term R2 (Pi pi V0 V1)))) t) ->
    Acc (ddp_step (union term (union term R1 R3) (union term R2 (Pi pi V0 V1)))) (Term f l).
Proof.
intros f l  D3 IHl.
(* 1/1 f is defined in R3 *)
assert (H : Interp_dom (union term R1 R3) (union term R2 (Pi pi V0 V1)) (Term f l)).
intros [ | i p] g k Sub D2.
simpl in Sub; injection Sub; clear Sub; intros; subst g k.
inversion D2 as [g k u [H2 | HPi]]; subst.
apply False_rect; apply (Incomp23 f (Def R2 f k u H2) D3).
apply False_rect; inversion HPi; subst f; apply (Incomp3' D3).
simpl in Sub; assert (H := nth_error_ok_in i l);
destruct (nth_error l i) as [ti | ]; [idtac | discriminate].
destruct (H _ (eq_refl _)) as [ls1 [ls2 [L H']]]; clear H; subst l.
assert (Hti : Interp_dom (union term R1 R3) (union term R2 (Pi pi V0 V1)) ti).
apply acc_interp_dom.
apply IHl; apply in_or_app; right; left; trivial.
apply (Hti p); trivial.

assert (D3' : match Term f l with
                     | Var _ => False
                     | Term g _ => defined R3 g
                     end).
trivial.
assert (Ts := T3 _ H).
assert (IHl' : forall t, direct_subterm t (Term f l) ->
                Acc (one_step (union term (union term R1 R3) (union term R2 (Pi pi V0 V1)))) t).
simpl; trivial.
generalize (Term f l) Ts D3' IHl'; clear f l H Ts D3' IHl D3 IHl'.
intros t Acc_t; induction Acc_t as [[ v | _f l] Acc_t IH]; intros D3 IHl.
contradiction.
(* 1/1 goal is now 
    Acc (dpd_step (union term (union term R1 R3) (union term R2 (Pi pi)))) (Term _f l) *)
apply Acc_intro; intros t H.
assert (Simple_step : 
forall l
(IH : forall y : term,
     rdp_step (axiom (ddp R3)) (union term (union term R1 R3) (union term R2 (Pi pi V0 V1))) y
       (Term _f l) ->
     match y with
     | Var _ => False
     | Term g _ => defined R3 g
     end ->
     (forall t : term,
      direct_subterm t y ->
      Acc (one_step (union term (union term R1 R3) (union term R2 (Pi pi V0 V1))))
        t) ->
     Acc (ddp_step (union term (union term R1 R3) (union term R2 (Pi pi V0 V1)))) y) 
(D3 : defined R3 _f)
(IHl : forall t : term,
      direct_subterm t (Term _f l) ->
      Acc (one_step (union term (union term R1 R3) (union term R2 (Pi pi V0 V1)))) t)
(t : term)
(H : axiom (ddp (union term (union term R1 R3) (union term R2 (Pi pi V0 V1)))) t
      (Term _f l)),
Acc (ddp_step (union term (union term R1 R3) (union term R2 (Pi pi V0 V1)))) t).
(* 1/2 simpl RDP step *)
clear l Acc_t IH D3 IHl t H;
intros l IH D3 IHl t _Hm.
inversion _Hm as [_t _s sigma Hm K1 K2]; clear _Hm; subst.
destruct Hm as [Hm _Sub];
inversion Hm as [s [ v | f' k'] p g'' k'' t_R_s Sub Df'' H1 H']; clear Hm; subst.
destruct p; discriminate.
destruct _s as [ v | g k].
absurd (union term (union term R1 R3) (union term R2 (Pi pi V0 V1)) (Term f' k') (Var v)); trivial.
apply R132_var'.

assert (t_R3_s : R3 (Term f' k') (Term g k)).
simpl in K2; injection K2; clear K2; intros H' f_eq_g; subst g l.
destruct t_R_s as [[ H1 | H3] | [H2 | HPi]]; trivial.
apply False_rect; apply (Incomp13 _f (Def _ _ _ _ H1) D3).
apply False_rect; apply (Incomp23 _f (Def _ _ _ _ H2) D3).
apply False_rect; inversion HPi; subst _f; apply (Incomp3' D3).

(* 1/2 R3 (Term f' k') (Term g k) *)
assert (Hm' : axiom (ddp (union term (union term R1 R2) (union term R3 (Pi pi V0 V1))))
                           (apply_subst sigma (Term g'' k'')) (Term _f l)).
rewrite <- K2; apply instance.
split; [idtac | trivial].
refine (Dp (union term (union term R1 R2) (union term R3 (Pi pi V0 V1))) _ (Term f' k')  p  g'' k'' _ _ _); trivial.
right; left; trivial.
inversion Df'' as [h'' l'' u'' [[H1 | H3] | [H2 | Hpi]]]; subst.
apply (Def (union term (union term R1 R2) (union term R3 (Pi pi V0 V1))) g'' l'' u''); left; left; trivial.
apply (Def (union term (union term R1 R2) (union term R3 (Pi pi V0 V1))) g'' l'' u''); right; left; trivial.
apply (Def (union term (union term R1 R2) (union term R3 (Pi pi V0 V1))) g'' l'' u''); left; right; trivial.
apply (Def (union term (union term R1 R2) (union term R3 (Pi pi V0 V1))) g'' l'' u''); right; right; trivial.
destruct (split_dp_top _ _ _ _ Hm') as [D12' | DD3]; clear Hm'.
(* 1/3  symbol is also defined in R1 U R2  -> contradiction *)
destruct D12' as [Df Dg].
absurd (defined (union term R1 R2) _f); trivial.
intros D12f; inversion D12f as [f'' k''' u [H1 | H2]]; subst.
apply (Incomp13 _f (Def R1 _f k''' u H1) D3).
apply (Incomp23 _f (Def R2 _f k''' u H2) D3).
assert (D123 : match Term g'' k'' with
                       | Var _ => False
                       | Term f _ => defined R3 f \/ defined (union _ R1 R2) f
                       end).
destruct DD3 as [[_ D3'] | [_ D12]]; [left | right]; trivial.
clear DD3.
generalize (Term g'' k'') p _Sub Sub D123; clear g'' k'' p _Sub Sub Df'' D123.
intro t; pattern t; apply term_rec2; clear t.
intro n; induction n as [ | n]; intros t St p _Sub Sub D123.
absurd (1 <= 0); auto with arith; apply Nat.le_trans with (size t); trivial; apply size_ge_one.
assert (IHk'' : forall s q, subterm_at_pos t q = Some s ->
                      Acc (one_step (union term (union term R1 R3) (union term R2 (Pi pi V0 V1))))
                        (apply_subst sigma s)).
intro s; pattern s; apply term_rec2; clear s.
intro m; induction m as [ | m]; intros s Ss q Sub'.
absurd (1 <= 0); auto with arith; apply Nat.le_trans with (size s); trivial; apply size_ge_one.
destruct s as [v | g3 k3].
assert (v_in_s : In v (var_list (Term g k))).
apply R3_reg with (Term f' k'); trivial.
apply var_in_subterm with (Var v) (p ++ q).
apply subterm_in_subterm with t; trivial.
left; trivial.
destruct (var_in_subterm2 _ _ (in_impl_mem (@eq _) (fun a => eq_refl a) _ _ v_in_s)) as [q' Sub''].
destruct q' as [ | i q'].
discriminate.
assert (H'' := nth_error_ok_in i k).
simpl in Sub''; destruct (nth_error k i) as [si | ].
destruct (H'' _ (eq_refl _)) as [l1 [l2 [L1 H''']]].
apply acc_subterms_3 with q' (apply_subst sigma si).
apply IHl.
simpl in K2; injection K2; clear K2; intros; subst.
simpl; rewrite map_app; apply in_or_app; right; left; trivial.
assert (Sub3 := subterm_at_pos_apply_subst_apply_subst_subterm_at_pos 
                               si q' sigma).
rewrite Sub'' in Sub3; trivial.
discriminate.
assert (Hk3 : forall s, In s k3 -> 
                  Acc (one_step (union term (union term R1 R3) (union term R2 (Pi pi V0 V1))))
                         (apply_subst sigma s)).
intros s' s'_in_k3; 
destruct (In_split _ _ s'_in_k3) as [k3' [k3'' H]]; subst k3.
apply IHm with (q ++ (length k3' :: nil)).
apply le_S_n.
apply Nat.le_trans with (size (Term g3 (k3' ++ s' :: k3''))); trivial.
apply size_direct_subterm; trivial.
apply subterm_in_subterm with (Term g3 (k3' ++ s' :: k3'')); trivial.
simpl; rewrite nth_error_at_pos; trivial.
destruct (subterm_at_pos_dec (Term g k)  (Term g3 k3)) as [[[ | i q'] _Sub'] | not_Sub].
apply ddp_simple_criterion_local.
apply R132_var'.
apply R132_reg'.
apply def_dec132'.
apply IH; trivial.
apply Rdp_step with l.
left.
rewrite <- K2; apply instance.
assert (H''' := Dp R3 _ _ (p ++ q) g3 k3 t_R3_s).
split.
apply H'''.
apply subterm_in_subterm with t; trivial.
injection _Sub'; intros; subst; apply (Def R3 _ _ _ t_R3_s).
intros i q''; intro H3; 
simpl in _Sub'; injection _Sub'; intros; subst g3 k3;
absurd (size (Term g k) < size (Term g k)).
auto with arith.
generalize (size_subterm_at_pos (Term g k) i q'').
rewrite H3; trivial.
simpl in _Sub'; injection _Sub'; intros; subst g3 k3;
apply (Def R3 g _ _ t_R3_s).
simpl; intros s s_in_k3; rewrite in_map_iff in s_in_k3; destruct s_in_k3 as [s' [H s'_in_k3]]; subst.
apply Hk3; trivial.
simpl; intros s s_in_k3; rewrite in_map_iff in s_in_k3; destruct s_in_k3 as [s' [H s'_in_k3]]; subst.
apply Hk3; trivial.
simpl in _Sub'.
generalize (nth_error_ok_in i k); destruct (nth_error k i) as [ti | ]; [idtac | discriminate].
intros H''; destruct (H'' _ (eq_refl _)) as [l1' [l2' [L H3]]]; clear H''; subst k.
apply acc_subterms_3 with q' (apply_subst sigma ti).
apply IHl.
simpl; injection K2; clear K2; intros; subst.
rewrite in_map_iff; exists ti; split; trivial; apply in_or_app; right; left; trivial.
generalize (subterm_at_pos_apply_subst_apply_subst_subterm_at_pos ti q' sigma).
rewrite _Sub'; trivial.
destruct (def_dec132' g3) as [Cg3 | Dg3].
simpl; apply acc_subterms; trivial.
apply R132_var'.
intros s s_in_k3; rewrite in_map_iff in s_in_k3; destruct s_in_k3 as [s' [H s'_in_k3]]; subst.
apply Hk3; trivial.
destruct q as [ | i q].
simpl in Sub'; injection Sub'; clear Sub'; intros; subst t.
destruct D123 as [Dg | Dg].
(* 1/5  the new symbol is also defined in R3 -> dp of type {3}x{3} *)
assert (H : rdp_step (axiom (ddp R3)) (union term (union term R1 R3) (union term R2 (Pi pi V0 V1))) 
                           (Term g3 (map (apply_subst sigma) k3)) 
                           (Term _f l)).
apply Rdp_step with l.
left.
rewrite <- K2; refine (instance _ (Term g3 k3) _ sigma _).
simpl in K2; injection K2; clear K2; intros H' _f_eq_g; subst g l.
split.
apply (Dp R3 (Term _f k) (Term f' k') p g3 k3); trivial.
intros i p'; apply not_Sub.
apply ddp_simple_criterion_local.
apply R132_var'.
apply R132_reg'.
apply def_dec132'.
apply IH; simpl; trivial.
intros s s_in_k3; rewrite in_map_iff in s_in_k3; destruct s_in_k3 as [s' [H'' s'_in_k3]]; subst.
apply Hk3; trivial.
simpl; 
intros s s_in_k3; rewrite in_map_iff in s_in_k3; destruct s_in_k3 as [s' [H'' s'_in_k3]]; subst.
apply Hk3; trivial.
(* 1/4 the old top symbol is defined in R3, the new one in R1 U R2 -> pair of type {3}x{1} *)
apply ddp_simple_criterion_local.
apply R132_var'.
apply R132_reg'.
apply def_dec132'.
apply Acc_incl with (ddp_step (union term (union term R1 R2) (union term R3 (Pi pi V0 V1)))).
apply ddp_step_incl.
intros t1 t2 [[H1 | H3] | [H2 | HPi]].
do 2 left; trivial.
right; left; trivial.
left; right; trivial.
do 2 right; trivial.
apply (Case12 g3 (map (apply_subst sigma) k3)); trivial.
intros [ | i r] g4 k4 Sub'' Dg4.
simpl in Sub''; injection Sub''; clear Sub''; intros; subst.
apply False_rect; apply (Incomp123' g4); trivial.
simpl in Sub''.
assert (H'' := nth_error_map (apply_subst sigma) k3 i).
destruct (nth_error (map (apply_subst sigma) k3) i) as [ti | ].
assert (H''' := nth_error_ok_in i k3).
destruct (nth_error k3 i) as [si | ].
destruct (H''' _ (eq_refl _)) as [l1 [l2 [L1 H'''']]].
assert (si_in_lr : In si k3).
subst k3; apply in_or_app; right; left; trivial.
apply acc_subterms_3 with r ti; trivial.
subst; rewrite Dummy; apply IHm with (length l1 :: nil); trivial.
apply le_S_n.
apply Nat.le_trans with (size (Term g3 (l1 ++ si :: l2))); trivial.
apply size_direct_subterm; trivial.
simpl; rewrite nth_error_at_pos; trivial.
contradiction.
discriminate.
simpl; 
intros s s_in_k3; rewrite in_map_iff in s_in_k3; destruct s_in_k3 as [s' [H'' s'_in_k3]]; subst.
apply Hk3; trivial.
apply ddp_simple_criterion_local.
apply R132_var'.
apply R132_reg'.
apply def_dec132'.
apply IHn with (p ++ i :: q).
apply le_S_n.
apply Nat.le_trans with (size t); trivial.
generalize (size_subterm_at_pos t i q).
rewrite Sub'; trivial.
intros j q' Sub''; apply (not_Sub (j :: q')); trivial.
apply subterm_in_subterm with t; trivial.
destruct Dg3 as [g' l' u [[H1 | H3] | [H2 | Hpi]]].
right; apply (Def (union _ R1 R2) g' l' u); left; trivial.
left; apply (Def  R3 g' l' u); trivial.
right; apply (Def (union _ R1 R2) g' l' u); right; trivial.
apply False_rect; destruct (P3 _ _ t_R3_s g') as [F _]; apply F.
apply (symb_in_subterm g' _ p Sub).
apply (symb_in_subterm g' _ (i :: q) Sub').
simpl; generalize (F.Symb.eq_bool_ok g' g'); case (F.Symb.eq_bool g' g'); [intros _ | intros g_diff_g; absurd (g'=g')]; trivial.
inversion Hpi; subst; trivial.
simpl; 
intros s s_in_k3; rewrite in_map_iff in s_in_k3; destruct s_in_k3 as [s' [H'' s'_in_k3]]; subst.
apply Hk3; trivial.

apply acc_one_step_acc_ddp.
apply R132_var'.
apply IHk'' with (@nil nat); trivial.

inversion H as [g k l' s'' l_R_l' Hm]; clear H; subst.
apply (Simple_step l'); trivial.
intros [v | g k] H D3' Iu.
contradiction.
apply IH; trivial.
inversion H as [g' k' l'' s''' l'_R_l'' Hm']; clear H; subst.
apply Rdp_step with l''; trivial.
apply refl_trans_clos_is_trans with l'; trivial.

simpl; intros u' u'_in_l'.
assert (H : exists u, In u l /\ 
                          (refl_trans_clos (one_step (union term (union term R1 R3) (union term R2 (Pi pi V0 V1)))) u' u)).
generalize l l' l_R_l' u'_in_l'.
intro k1; induction k1 as [ | t1 k1]; intros [ | t2 k2] H u_in_k1.
contradiction.
generalize (refl_trans_clos_one_step_list_length_eq H); intro; discriminate.
contradiction.
rewrite refl_trans_clos_one_step_list_head_tail in H.
destruct H as [Ht1t2 Hk1k2].
simpl in u_in_k1; destruct u_in_k1 as [u_eq_t2 | u_in_k2].
exists t1; split.
left; trivial.
subst; assumption.
destruct (IHk1 k2 Hk1k2 u_in_k2) as [u [u_in_k1 H]].
exists u; split.
right; trivial.
assumption.
destruct H as [u [u_in_l H]].
inversion H as [u'' | u1' u1 H1]; clear H; subst.
apply IHl; simpl; trivial.
assert (Acc_u : Acc (rwr (union term (union term R1 R3) (union term R2 (Pi pi V0 V1)))) u).
rewrite <- acc_one_step.
apply IHl; trivial.
apply Acc_incl with (trans_clos (one_step
                                       (union term (union term R1 R3) (union term R2 (Pi pi V0 V1))))).
do 3 intro; left; assumption.
apply Acc_inv with u; assumption.
Qed.

Lemma modular_termination :
   well_founded (ddp_step (union _ (union _ R1 R2) (union _ R3 (Pi pi V0 V1)))).
Proof.
intros s; apply ddp_necessary; simpl; trivial.
apply R123_var'.

clear s; intro s; pattern s; apply term_rec3; clear s; trivial.
intro x; apply Acc_intro; intros s H; inversion H; subst.
inversion H0; subst.
destruct t2 as [v2 | f2 l2].
apply False_rect; apply (R123_var'  _ _ H3).
discriminate.

intros f l IHl; 
generalize (F.Symb.eq_bool_ok f pi); case (F.Symb.eq_bool f pi); [intros f_eq_pi | intros f_diff_pi].
subst f.
apply Acc_incl with (one_step (union _ (union _ (union _ R1 R2) R3) (Pi pi V0 V1))).
intros t1 t2; apply one_step_incl; clear t1 t2.
intros t1 t2 [[H1 | H2] | [H3 | Hpi]].
do 3 left; trivial.
do 2 left; right; trivial.
left; right; trivial.
right; trivial.
apply acc_subterms_pi; trivial.
intros x t [[H1 | H2] | H3].
apply (R1_var _ _ H1).
apply (R2_var _ _ H2).
apply (R3_var _ _ H3).
intros t1 t2 [[H1 | H2] | H3].
apply (P1 t1 t2 H1).
apply (P2 t1 t2 H2).
apply (P3 t1 t2 H3).
intros t t_in_ll;
apply Acc_incl with (one_step (union term (union term R1 R2) (union term R3 (Pi pi V0 V1)))).
intros t1 t2; apply one_step_incl; clear t1 t2.
intros t1 t2 [[[H1 | H2] | H3] | Hpi].
do 2 left; trivial.
left; right; trivial.
right; left; trivial.
right; right; trivial.
apply IHl; trivial.

(* 1/1 Standard dependancy pairs criterion *)
apply ddp_simple_criterion_local; simpl; trivial.
apply R123_var'.
apply R123_reg'.
apply def_dec123'.

destruct (def_dec12 f) as [D12 | C12].
apply Case12; trivial.
intros [ | i p] g k Sub D3.
simpl in Sub; injection Sub; clear Sub; intros; subst g k.
assert False; [idtac | contradiction].
apply (Incomp123' f); trivial.
simpl in Sub; assert (H := nth_error_ok_in i l);
destruct (nth_error l i) as [ti | ]; [idtac | discriminate].
destruct (H _ (eq_refl _)) as [ls1 [ls2 [L H']]]; clear H; subst l.
assert (Hti : Interp_dom (union term R1 R2) (union term R3 (Pi pi V0 V1)) ti).
apply acc_interp_dom.
apply IHl; apply in_or_app; right; left; trivial.
apply (Hti p); trivial.

destruct (def_dec3 f) as [D3' | C3].
apply Acc_incl with (ddp_step (union term (union term R1 R3) (union term R2 (Pi pi V0 V1)))).
refine (ddp_step_incl _ _ _).
intros t1 t2 [[H1 | H2] | [H3 | HPi]].
do 2 left; assumption.
right; left; assumption.
left; right; assumption.
do 2 right; assumption.

apply Case3; trivial.
intros t t_in_l; rewrite <- Dummy; apply IHl; trivial.
apply Acc_intro; intros t H.
inversion H as [g k l' s'' l_R_l' _Hm]; clear H; subst.
inversion _Hm as [_t s sigma Hm K1 K2]; clear _Hm; subst.
destruct Hm as [Hm _Sub].
inversion Hm as [_s [ v | f' k'] p g'' k'' t_R_s Sub Df'' H1 H']; subst.
destruct p; discriminate.
destruct s as [x | g k].
absurd (union term (union term R1 R2) (union term R3 (Pi pi V0 V1)) (Term f' k') (Var x)); trivial.
apply R123_var'.
simpl in K2; injection K2; clear K2; intros; subst.
apply False_rect; destruct t_R_s as [H12 | [H3 | HPi]].
apply C12; apply (Def (union _ R1 R2) f _ _ H12).
apply C3; apply (Def R3 f _ _ H3).
apply f_diff_pi; inversion HPi; subst; trivial.
Qed.

End Modular_termination.

Lemma def_dec_rules : 
   forall R rule_list, (forall l r, R r l <-> In (l,r) rule_list) ->
   forall f, {defined R f} + {~ defined R f}.
Proof.
intros R rule_list; generalize R; clear R;
induction rule_list as [ | [l r] rule_list]; intros R Equiv f.
right; intro Df; inversion Df as [f' k u H]; subst.
rewrite Equiv in H; contradiction.
set (R' := fun r l => In (l,r) rule_list).
assert (Equiv' : forall l r : term, R' r l <-> In (l, r) rule_list).
intros l1 r1; unfold R'; split; trivial.
destruct (IHrule_list R' Equiv' f) as [Df | Cf].
left; inversion Df as [f' k u H]; subst.
apply (Def R f k u).
rewrite Equiv; right; trivial.
destruct l as [v | f' k'].
right; intro Df; inversion Df as [f' k u H]; subst.
apply Cf.
rewrite Equiv in H.
destruct H as [H | H].
discriminate.
rewrite <- Equiv' in H.
apply (Def R' f k u); trivial.
generalize (F.Symb.eq_bool_ok f f'); case (F.Symb.eq_bool f f'); [intros f_eq_f' | intros f_diff_f'].
left; apply (Def R f k' r); subst; rewrite Equiv; left; trivial.
right; intro Df; inversion Df as [f'' k u H]; subst.
rewrite Equiv in H; destruct H as [H | H].
apply f_diff_f'; injection H; intros; subst; trivial.
apply Cf.
rewrite <- Equiv' in H.
apply (Def R' f k u); trivial.
Defined.

Lemma modular_termination_lift :
  forall (V0 V1 : variable), V0 <> V1 ->
  forall pi R1 R2 R3, module R1 R2 -> module R1 R3 ->

  forall rule_list1, (forall l r, R1 r l <-> In (l,r) rule_list1) ->
  (forall l r, In (l,r) rule_list1 -> forall v, l <> Var v) ->
  (forall l r, In (l,r) rule_list1 -> forall v, In v (var_list r) -> In v (var_list l)) ->
  (forall l r, In (l,r) rule_list1 -> (forall f, ((symb_in_term f r = true -> f <> pi) /\
                                                              (symb_in_term f l = true -> f <> pi)))) ->

  forall rule_list2, (forall l r, R2 r l <-> In (l,r) rule_list2) ->
  (forall l r, In (l,r) rule_list2 -> forall v, l <> Var v) ->
  (forall l r, In (l,r) rule_list2 -> forall v, In v (var_list r) -> In v (var_list l)) ->
  (forall l r, In (l,r) rule_list2 -> (forall f, ((symb_in_term f r = true -> f <> pi) /\
                                                              (symb_in_term f l = true -> f <> pi)))) ->

  forall rule_list3, (forall l r, R3 r l <-> In (l,r) rule_list3) ->
  (forall l r, In (l,r) rule_list3 -> forall v, l <> Var v) ->
  (forall l r, In (l,r) rule_list3 -> forall v, In v (var_list r) -> In v (var_list l)) ->
  (forall l r, In (l,r) rule_list3 -> (forall f, ((symb_in_term f r = true -> f <> pi) /\
                                                              (symb_in_term f l = true -> f <> pi)))) ->

  (forall s t f, defined R2 f -> R3 s t -> symb_in_term_list f (s :: t :: nil) = false) ->
  (forall s t f, defined R3 f -> R2 s t -> symb_in_term_list f (s :: t :: nil) = false) ->

  well_founded (ddp_step (union _ (union _ R1 R2) (Pi pi V0 V1))) ->
  well_founded (rdp_step (axiom (ddp R3)) (union _ (union _ R1 R3) (Pi pi V0 V1))) ->
  well_founded (ddp_step (union _ (union _ R1 R2) (union _ R3 (Pi pi V0 V1)))).
Proof.
intros V0 V1 V0_diff_V1 pi R1 R2 R3 M12 M13 
rule_list1 Equiv1 R1_var R1_reg P1
rule_list2 Equiv2 R2_var R2_reg P2
rule_list3 Equiv3 R3_var R3_reg P3
Indep2 Indep3 W12 W3.
apply (modular_termination _ _ V0_diff_V1 pi pi R1 R2 R3 
(def_dec_rules _ _ Equiv1)
(def_dec_rules _ _ Equiv2)
(def_dec_rules _ _ Equiv3) _ _ _
(fun s t => iff_sym (compute_red_is_correct _ R1_reg _ Equiv1 s t))
(fun s t => iff_sym (compute_red_is_correct _ R2_reg _ Equiv2 s t))
(fun s t => iff_sym (compute_red_is_correct _ R3_reg _ Equiv3 s t))); trivial.
intros s t H1; apply R1_reg; rewrite <- Equiv1; trivial.
intros s t H2; apply R2_reg; rewrite <- Equiv2; trivial.
intros s t H3; apply R3_reg; rewrite <- Equiv3; trivial.
intros x t H1; rewrite Equiv1 in H1; apply (R1_var _ _ H1 x); trivial.
intros x t H2; rewrite Equiv2 in H2; apply (R2_var _ _ H2 x); trivial.
intros x t H3; rewrite Equiv3 in H3; apply (R3_var _ _ H3 x); trivial.
intros s t H1; apply (P1 t s); rewrite <- Equiv1; trivial.
intros s t H2; apply (P2 t s); rewrite <- Equiv2; trivial.
intros s t H3; apply (P3 t s); rewrite <- Equiv3; trivial.
apply ddp_criterion; trivial.
apply R12_var'.
intros x t H1; rewrite Equiv1 in H1; apply (R1_var _ _ H1 x); trivial.
intros x t H2; rewrite Equiv2 in H2; apply (R2_var _ _ H2 x); trivial.
intros s t [[H1 | H2] | Hpi].
apply R1_reg; rewrite <- Equiv1; trivial.
apply R2_reg; rewrite <- Equiv2; trivial.
inversion Hpi; subst.
intros x [x_eq_v1 | x_in_nil]; [left; trivial | contradiction].
intros x [x_eq_v2 | x_in_nil]; [right; left; trivial | contradiction].
intros f; destruct (def_dec_rules _ _ Equiv1 f) as [D1 | C1].
right; inversion D1 as [f' l u H1].
subst f'; apply (Def (union _ (union _ R1 R2) (Pi pi V0 V1)) f l u); left; left; trivial.
destruct (def_dec_rules _ _ Equiv2 f) as [D2 | C2].
right; inversion D2 as [f' l u H2].
subst f'; apply (Def (union _ (union _ R1 R2) (Pi pi V0 V1)) f l u); left; right; trivial.
generalize (F.Symb.eq_bool_ok f pi); case (F.Symb.eq_bool f pi); [intros f_eq_pi | intros f_diff_pi].
subst f; right; 
apply (Def (union _ (union _ R1 R2) (Pi pi V0 V1)) pi (Var V0 :: Var V1 :: nil) (Var V0)).
right; apply Pi1.
left; apply Const; intros l u [[H1 | H2] | Hpi].
apply C1; apply (Def R1 f l u H1).
apply C2; apply (Def R2 f l u H2).
inversion Hpi; subst f; apply f_diff_pi; trivial.
refine (wf_incl _ _ _ _ W12).
intros u1 u2 [H _]; assumption.
Qed.

Inductive Empty_R : term -> term -> Prop := .

Lemma module_empty : forall R, module Empty_R R.
Proof.
intros R; apply Mod.
intros f s t _ H; case H.
Qed.

Lemma list_rules_empty : forall l r, Empty_R r l <-> In (l,r) nil.
Proof.
intros l r; split; intro H; case H.
Qed.

Lemma Empty_R_reg :
  (forall l r, In (l,r) nil -> forall v, In v (var_list r) -> In v (var_list l)).
Proof.
intros l r lr_in_nil; case lr_in_nil.
Qed.

Lemma modular_termination_indep_lift :
  forall (V0 V1 : variable), V0 <> V1 ->
  forall pi R2 R3, 

  forall rule_list2, (forall l r, R2 r l <-> In (l,r) rule_list2) ->
  (forall l r, In (l,r) rule_list2 -> forall v, l <> Var v) ->
  (forall l r, In (l,r) rule_list2 -> forall v, In v (var_list r) -> In v (var_list l)) ->
  (forall l r, In (l,r) rule_list2 -> (forall f, ((symb_in_term f r = true -> f <> pi) /\
                                                              (symb_in_term f l = true -> f <> pi)))) ->

  forall rule_list3, (forall l r, R3 r l <-> In (l,r) rule_list3) ->
  (forall l r, In (l,r) rule_list3 -> forall v, l <> Var v) ->
  (forall l r, In (l,r) rule_list3 -> forall v, In v (var_list r) -> In v (var_list l)) ->
  (forall l r, In (l,r) rule_list3 -> (forall f, ((symb_in_term f r = true -> f <> pi) /\
                                                              (symb_in_term f l = true -> f <> pi)))) ->

  (forall s t f, defined R2 f -> R3 s t -> symb_in_term_list f (s :: t :: nil) = false) ->
  (forall s t f, defined R3 f -> R2 s t -> symb_in_term_list f (s :: t :: nil) = false) ->

  well_founded (ddp_step (union _ R2 (Pi pi V0 V1))) ->
  well_founded (ddp_step (union _ R3 (Pi pi V0 V1))) ->
  well_founded (ddp_step (union _ (union _ R2 R3) (Pi pi V0 V1))).
Proof.
intros V0 V1 V0_diff_V1 pi R2 R3 
rule_list2 Equiv2 R2_var R2_reg P2
rule_list3 Equiv3 R3_var R3_reg P3
Indep2 Indep3 W12 W3.
apply wf_incl with  (ddp_step (union term (union _ Empty_R R2) (union term R3 (Pi pi V0 V1)))).
intros t1 t2; apply  ddp_step_incl; clear t1 t2.
intros t1 t2 [[H2 | H3] | Hpi].
left; right; trivial.
right; left; trivial.
do 2 right; trivial.

apply (modular_termination_lift _ _ V0_diff_V1 pi Empty_R R2 R3 
(module_empty R2) (module_empty R3)) with (@nil (term * term)) rule_list2 rule_list3; trivial.
apply list_rules_empty.
intros s t H; case H.
intros s t H; case H.
intros s t H; case H.
apply wf_incl with  (ddp_step (union term R2 (Pi pi V0 V1))); trivial.
assert (H : inclusion term (union term (union term Empty_R R2) (Pi pi V0 V1)) 
                                         (union term R2 (Pi pi V0 V1))).
intros t1 t2 [[HE | H2] | Hpi].
case HE.
left; trivial.
right; trivial.
apply ddp_step_incl; trivial.

apply wf_incl with  (rdp_step (axiom (ddp (union term R3 (Pi pi V0 V1)))) (union term R3 (Pi pi V0 V1))); trivial.
clear; intros s t H; inversion H; clear H; subst.
apply Rdp_step with l2.
refine (refl_trans_incl (one_step_list_incl _ (one_step_incl _ _ _)) H0).
clear; intros t1 t2 [[HE | H3] | Hpi].
case HE.
left; trivial.
right; trivial.
inversion H1; apply instance.
destruct H3 as [H3 Sub].
inversion H3; clear H3; subst.
split; [apply Dp with t3 p | idtac]; trivial.
left; assumption.
inversion H6; clear H6; subst.
apply (Def _ f2 l t); left; trivial.
Qed.

Lemma modular_termination_hierarch_lift :
  forall (V0 V1 : variable), V0 <> V1 ->
  forall pi R1 R3, module R1 R3 ->

  forall rule_list1, (forall l r, R1 r l <-> In (l,r) rule_list1) ->
  (forall l r, In (l,r) rule_list1 -> forall v, l <> Var v) ->
  (forall l r, In (l,r) rule_list1 -> forall v, In v (var_list r) -> In v (var_list l)) ->
  (forall l r, In (l,r) rule_list1 -> (forall f, ((symb_in_term f r = true -> f <> pi) /\
                                                              (symb_in_term f l = true -> f <> pi)))) ->

  forall rule_list3, (forall l r, R3 r l <-> In (l,r) rule_list3) ->
  (forall l r, In (l,r) rule_list3 -> forall v, l <> Var v) ->
  (forall l r, In (l,r) rule_list3 -> forall v, In v (var_list r) -> In v (var_list l)) ->
  (forall l r, In (l,r) rule_list3 -> (forall f, ((symb_in_term f r = true -> f <> pi) /\
                                                              (symb_in_term f l = true -> f <> pi)))) ->

  well_founded (ddp_step (union _ R1 (Pi pi V0 V1))) ->
  well_founded (rdp_step (axiom (ddp R3)) (union _ (union _ R1 R3) (Pi pi V0 V1))) ->
  well_founded (ddp_step (union _ (union _ R1 R3) (Pi pi V0 V1))).
Proof.
intros V0 V1 V0_diff_V1 pi R1 R3 M13 
rule_list1 Equiv1 R1_var R1_reg P1
rule_list3 Equiv3 R3_var R3_reg P3
W12 W3.
apply wf_incl with  (ddp_step (union term (union _ R1 Empty_R) (union term R3 (Pi pi V0 V1)))).
intros t1 t2; apply  ddp_step_incl; clear t1 t2.
intros t1 t2 [[H1 | H3] | Hpi].
do 2 left; trivial.
right; left; trivial.
do 2 right; trivial.

apply (modular_termination_lift _ _ V0_diff_V1 pi R1 Empty_R R3) with rule_list1 (@nil (term * term)) rule_list3; trivial.
apply Mod; intros f s t [f' l u HE]; case HE.
apply list_rules_empty.
intros s t H; case H.
intros s t H; case H.
intros s t H; case H.
intros s t f [f' l u HE]; case HE.
intros s t f _ HE; case HE.
apply wf_incl with  (ddp_step (union term R1 (Pi pi V0 V1))); trivial.
apply ddp_step_incl.
intros t1 t2 [[H1 | HE] | Hpi].
left; trivial.
case HE.
right; trivial.
Qed.

Record rwr_rel (pi : F.Symb.A) : Type :=
  mk_set 
  {
     ident : nat;
     Rel : relation term;
     rules : list (term * term);
     REquiv : (forall l r, Rel r l <-> In (l,r) rules);
     RR_var : (forall l r, In (l,r) rules -> forall v, l <> Var v);
     RR_reg : (forall l r, In (l,r) rules -> forall v, In v (var_list r) -> In v (var_list l));
     RP : (forall l r, In (l,r) rules -> (forall f, ((symb_in_term f r = true -> f <> pi) /\
                                                              (symb_in_term f l = true -> f <> pi))))
  }.

Lemma Equiv_empty : forall (l r : term), Empty_R r l <-> In (l,r) nil.
Proof.
intros l r; split; intro H; case H.
Qed.

Lemma R_var_empty : forall (l r : term), In (l,r) nil -> forall v, l <> Var v.
Proof.
intros l r H; case H.
Qed.

Lemma R_reg_empty : forall l r, In (l,r) nil -> forall v, In v (var_list r) -> In v (var_list l).
Proof.
intros l r H; case H.
Qed.

Lemma P_empty :
 forall pi, forall l r, In (l,r) nil -> (forall f, ((symb_in_term f r = true -> f <> pi) /\
                                                              (symb_in_term f l = true -> f <> pi))).
Proof.
intros pi l r H; case H.
Qed.

Definition rwr_rel_empty pi : rwr_rel pi :=
  mk_set pi 0 Empty_R nil Equiv_empty R_var_empty R_reg_empty (P_empty pi).

Lemma Equiv_comb :
  forall R1 R2 rules1 rules2, (forall l r, R1 r l <-> In (l,r) rules1) -> (forall l r, R2 r l <-> In (l,r) rules2) ->
          (forall (l r : term), (union _ R1 R2) r l <-> In (l,r) (rules1 ++ rules2)).
Proof.
intros R1 R2 rules1 rules2 Equiv1 Equiv2.
intros l r; split; intro H.
destruct H as [H | H]; apply in_or_app; [left; rewrite <- Equiv1 | right; rewrite <- Equiv2]; trivial.
destruct (in_app_or _ _ _ H) as [H' | H']; [left; rewrite Equiv1 | right; rewrite Equiv2]; trivial.
Qed.

Lemma R_var_comb :
  forall rules1 rules2, (forall l r, In (l,r) rules1 -> forall v, l <> Var v) ->
  (forall l r, In (l,r) rules2 -> forall v, l <> Var v) ->
  (forall (l r : term), In (l,r) (rules1 ++ rules2) -> forall v, l <> Var v).
Proof.
intros rules1 rules2 R1_var R2_var l r H v.
destruct (in_app_or _ _ _ H) as [H' | H']; [apply (R1_var l r H' v) | apply (R2_var l r H' v)].
Qed.

Lemma R_reg_comb :
  forall rules1 rules2, (forall l r, In (l,r) rules1 -> forall v, In v (var_list r) -> In v (var_list l)) ->
  (forall l r, In (l,r) rules2 -> forall v, In v (var_list r) -> In v (var_list l)) ->
  (forall l r, In (l,r) (rules1 ++ rules2) -> forall v, In v (var_list r) -> In v (var_list l)).  
Proof.
intros rules1 rules2 R1_reg R2_reg l r H v.
destruct (in_app_or _ _ _ H) as [H' | H']; [apply (R1_reg l r H' v) | apply (R2_reg l r H' v)].
Qed.

Lemma P_comb :
 forall pi rules1 rules2, (forall l r, In (l,r) rules1 -> (forall f, ((symb_in_term f r = true -> f <> pi) /\
                                                              (symb_in_term f l = true -> f <> pi)))) ->
(forall l r, In (l,r) rules2 -> (forall f, ((symb_in_term f r = true -> f <> pi) /\
                                                              (symb_in_term f l = true -> f <> pi)))) ->
(forall l r, In (l,r) (rules1 ++ rules2) -> (forall f, ((symb_in_term f r = true -> f <> pi) /\
                                                              (symb_in_term f l = true -> f <> pi)))).
Proof.
intros rules1 rules2 pi P1 P2 l r H f.
destruct (in_app_or _ _ _ H) as [H' | H']; [apply (P1 l r H' f) | apply (P2 l r H' f)].
Qed.

Definition rwr_rel_comb pi (R1 R2 : rwr_rel pi)  : rwr_rel pi :=
  mk_set pi (ident pi R1) (union _ (Rel pi R1) (Rel pi R2)) (rules pi R1 ++ rules pi R2)
                  (Equiv_comb _ _ _ _ (REquiv pi R1) (REquiv pi R2))
                  (R_var_comb _ _ (RR_var pi R1) (RR_var pi R2))
                  (R_reg_comb _ _ (RR_reg pi R1) (RR_reg pi R2))
                  (P_comb _ _ _ (RP pi R1) (RP pi R2)).

Lemma modular_termination_indep_list_lift :
  forall (V0 V1 : variable), V0 <> V1 -> forall pi (list_rel : list (rwr_rel pi)) R',
   (forall R1 R2 L' L'' L''', list_rel = L' ++ R1 :: L'' ++ R2 :: L''' -> ident pi R1 <> ident pi R2) ->
   well_founded (ddp_step (union _ (Rel pi R') (Pi pi V0 V1))) ->
  (forall R, In R list_rel ->   module (Rel pi R') (Rel pi R)) ->
  (forall R, In R list_rel ->   well_founded (rdp_step (axiom (ddp (Rel pi R))) (union _ (union _ (Rel pi R) (Rel pi R')) (Pi pi V0 V1)))) ->
  (forall R1 R2, In R1 list_rel -> In R2 list_rel -> ident pi R1 <> ident pi R2 ->
        (forall s t f, defined (Rel pi R1) f -> (Rel pi R2) s t -> symb_in_term_list f (s :: t :: nil) = false)) ->
    well_founded (ddp_step (fold_left (fun acc Rr => union _ (Rel pi Rr) acc)  list_rel  (union _ (Rel pi R') (Pi pi V0 V1)))).
Proof.
intros V0 V1 V0_diff_V1 pi L R' U W' ML WL IL.
assert (fold_incl : forall (L0 : list (rwr_rel pi)) (P0 P1 : term -> term -> Prop),
inclusion term P0 P1 ->
inclusion term
  (fold_left
     (fun (acc : relation term) (Rr : rwr_rel pi) =>
      union term (Rel pi Rr) acc) L0 P0)
  (fold_left
     (fun (acc : relation term) (Rr : rwr_rel pi) =>
      union term (Rel pi Rr) acc) L0 P1)).
intro L'; induction L' as [ | R'' L'']; simpl; intros P1 P2 P1_in_P2; trivial.
apply IHL''.
intros t1 t2 [H'' | H1].
left; trivial.
right; apply P1_in_P2; trivial.

assert (Gen : forall (R0 : rwr_rel pi), module (Rel pi R') (Rel pi R0) ->
                     (well_founded (rdp_step (axiom (ddp (Rel pi R0))) (union _ (union _ (Rel pi R') (Rel pi R0)) (Pi pi V0 V1)))) ->
                     (forall R2, In R2 L -> 
                          (forall s t f, defined (Rel pi R0) f -> (Rel pi R2) s t -> symb_in_term_list f (s :: t :: nil) = false)) ->
                     (forall R1, In R1 L -> 
                            (forall s t f, defined (Rel pi R1) f -> (Rel pi R0) s t -> symb_in_term_list f (s :: t :: nil) = false)) ->
                     well_founded (ddp_step (fold_left (fun acc Rr => union _ (Rel pi Rr) acc)  L  (union _ (union _ (Rel pi R') (Rel pi R0)) (Pi pi V0 V1))))).
induction L as [ | R L]; intros R0 M0 W0 I1 I2; simpl; trivial.
apply (modular_termination_hierarch_lift V0 V1 V0_diff_V1) with (rules pi R') (rules pi R0); trivial.
apply (REquiv pi R').
apply (RR_var pi R').
apply (RR_reg pi R').
apply (RP pi R').
apply (REquiv pi R0).
apply (RR_var pi R0).
apply (RR_reg pi R0).
apply (RP pi R0).

apply wf_incl with
(ddp_step
     (fold_left
        (fun (acc : relation term) (Rr : rwr_rel pi) =>
         union term (Rel pi Rr) acc) L
        (union term (union term (Rel pi R') (Rel pi (rwr_rel_comb pi R R0))) (Pi pi V0 V1)))).
apply ddp_step_incl.
apply fold_incl.
intros t1 t2 [H | [[H' | H0] | Hpi]].
left; right; left; trivial.
do 2 left; trivial.
left; do 2 right; trivial.
right; trivial.

apply IHL.
intros R1 R2 L' L'' L''' H; apply (U R1 R2 (R :: L') L'' L'''); simpl; rewrite H; trivial.
intros R1 R1_in_L; apply ML; right; trivial.
intros R1 R1_in_L; apply WL; right; trivial.
intros R1 R2 R1_in_L R2_in_L; apply IL; right; trivial.
simpl; apply Mod.
intros f s t Df H'; destruct Df as [f' l u [H | H0]].
destruct (ML R (or_introl _ (eq_refl _))) as [M'].
apply (M' f' s t (Def (Rel pi R) f' l u H)); trivial.
destruct M0 as [M0].
apply (M0 f' s t (Def (Rel pi R0) f' l u H0)); trivial.
simpl; assert (M := modular_termination_lift _ _ V0_diff_V1 pi (Rel pi R') (Rel pi R) (Rel pi R0) 
(ML _ (or_introl _ (eq_refl _))) M0
_ (REquiv pi R') (RR_var pi R') (RR_reg pi R') (RP pi R')
_ (REquiv pi R) (RR_var pi R) (RR_reg pi R) (RP pi R)
_ (REquiv pi R0) (RR_var pi R0) (RR_reg pi R0) (RP pi R0)
(I2 R (or_introl _ (eq_refl _)))
(I1 R (or_introl _ (eq_refl _)))).
apply wf_incl with (ddp_step
         (union term (union term (Rel pi R') (Rel pi R))
            (union term (Rel pi R0) (Pi pi V0 V1)))).
apply rddp_step_incl.
intros t1 t2 [H | H0].
left; right; trivial.
right; left; trivial.
intros t1 t2 [[H' | [H | H0]] | Hpi].
do 2 left; trivial.
left; right; trivial.
right; left; trivial.
do 2 right; trivial.
apply M; trivial.
apply (modular_termination_hierarch_lift V0 V1 V0_diff_V1) with (rules pi R') (rules pi R); trivial.
apply ML; left; trivial.
apply (REquiv pi R').
apply (RR_var pi R').
apply (RR_reg pi R').
apply (RP pi R').
apply (REquiv pi R).
apply (RR_var pi R).
apply (RR_reg pi R).
apply (RP pi R).
apply wf_incl with (rdp_step (axiom (ddp (Rel pi R)))
     (union term (union term (Rel pi R) (Rel pi R')) (Pi pi V0 V1))).
apply rddp_step_incl.
intros t1 t2; trivial.
intros t1 t2 [[H | H'] | Hpi].
left; right; trivial.
do 2 left; trivial.
right; trivial.
apply WL; left; trivial.
intros R2 R2_in_L.
intros s t f Df H2; simpl in Df; destruct Df as [f' l u [H | H0]]. 
apply IL with R R2; trivial.
left; trivial.
right; trivial.
destruct (In_split _ _ R2_in_L) as [L'' [L''' H']].
apply (U R R2 nil L'' L'''); simpl; subst L; trivial.
apply (Def (Rel pi R) f' l u H).
apply I1 with R2; trivial.
right; trivial. 
apply (Def (Rel pi R0) f' l u H0).
intros R1 R1_in_L.
intros s t f Df [H | H0].
apply IL with R1 R; trivial.
right; trivial.
left; trivial.
destruct (In_split _ _ R1_in_L) as [L'' [L''' H']].
intro H'''; refine (U R R1 nil L'' L''' _ _); simpl; subst; symmetry; trivial.
apply I2 with R1; trivial; right; trivial.

apply wf_incl with (ddp_step
           (fold_left
              (fun (acc : relation term) (Rr : rwr_rel pi) =>
               union term (Rel pi Rr) acc) L
              (union term (union term (Rel pi R') (Rel pi (rwr_rel_empty pi))) (Pi pi V0 V1)))).
apply rddp_step_incl.
apply fold_incl.
intros t1 t2 [H' | Hpi].
do 2 left; trivial.
right; trivial.
apply fold_incl.
intros t1 t2 [H' | Hpi].
do 2 left; trivial.
right; trivial.

apply Gen.
apply Mod; intros f s t Df; inversion Df as [f' l u H]; case H.
simpl; intro s; apply Acc_intro; intros _t H.
inversion H as [g k l' s'' l_R_l' _Hm]; clear H; subst.
inversion _Hm as [t s sigma Hm K1 K2]; clear _Hm; subst.
destruct Hm as [Hm _Sub].
inversion Hm as [s' t' p g'' k'' t_R_s Sub Df'' H1 H']; case t_R_s.
intros R2 _ s t f Df; inversion Df as [f' l u H]; case H.
intros R1 _ s t f _ H; case H.
Qed.


End MakeModDP.
