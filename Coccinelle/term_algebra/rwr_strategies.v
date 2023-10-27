
(** * strategies for rewriting in a term algebra *)

From Coq Require Import List Relations Wellfounded Arith.
From CoLoR Require Import closure decidable_set more_list weaved_relation term_spec
     equational_theory_spec dp rpo.

Module Make (E : EqTh).

  Import E.
  Import T.

Inductive P_step (R : relation term) (P : term -> Prop) : term -> term -> Prop :=
  | P_at_top : forall t s, P t -> axiom R s t -> P_step R P s t
  | P_in_context : forall f lt ls, one_step_list (P_step R P) ls lt -> P_step R P (Term f ls) (Term f lt).

Lemma P_step_one_step :
  forall R P s t, P_step R P s t -> one_step R s t.
Proof.
intros R P s t; generalize s; clear s; pattern t; apply term_rec3; clear t.
intros v s H; inversion H; subst; apply at_top; trivial.
intros f l Hl s H; 
inversion H as [t' s' Hnf H' | f' lt ls H']; 
clear H; subst.
apply at_top; trivial.
apply in_context.
generalize ls H'; clear ls H';
induction l as [ | t l]; intros ls H';
inversion H' as [t1 t2 l' H'' | t' l1 l2 H'']; clear H'; subst.
apply head_step; apply Hl; trivial; left; trivial.
apply tail_step; apply IHl; trivial; intros; apply Hl; trivial; right; trivial.
Qed.

Lemma P_context_cons :
  forall R P f t1 t2 l, trans_clos (P_step R P) t1 t2 -> 
      trans_clos (P_step R P) (Term f (t1 :: l)) (Term f (t2 :: l)).
Proof.
intros R P f t1 t2 l H;
induction H as [ | t1 t2 t3 Trans1 Trans2].
apply t_step; apply P_in_context; left; trivial.
apply t_trans with (Term f (t2 :: l)); trivial.
apply P_in_context; left; trivial.
Qed.

Lemma P_step_context_in :
  forall R P t1 t2 f l l', P_step R P t1 t2 -> 
   P_step R P (Term f (l ++ t1 :: l')) (Term f (l ++ t2 :: l')).
Proof.
intros R P t1 t2 f l l' H; apply P_in_context; 
induction l as [ | t l ]; simpl; [ left | right ]; trivial.
Qed.

Lemma P_context_in :
  forall R P t1 t2, trans_clos (P_step R P) t1 t2 -> 
  forall f l l', trans_clos (P_step R P) (Term f (l ++ t1 :: l')) (Term f (l ++ t2 :: l')).
Proof.
intros R P t1 t2 H; 
induction H as [ t1 t2 Step 
                          | t1 t2 t3 Trans1 Trans2].
intros f l l'; apply t_step; apply P_step_context_in; trivial.
intros f l l'; apply trans_clos_is_trans with (Term f (l ++ t2 :: l')); trivial.
apply t_step; apply P_step_context_in; trivial.
Qed.

Lemma P_general_context :
  forall R P f l1 l2, trans_clos (one_step_list (P_step R P)) l1 l2 -> trans_clos (P_step R P) (Term f l1) (Term f l2).
Proof.
intros R P f l1 l2 H; induction H as [l1 l2 H | l1 l2 l3 H1 H2 H3]. 
left; right; assumption.
right with (Term f l2); trivial.
right; assumption.
Qed.

Lemma nf_P_step_subterm:
  forall R P t, nf (P_step R P) t -> forall s, direct_subterm s t -> nf (P_step R P) s.
Proof.
intros R P t; pattern t; apply term_rec3; clear t.
intros v _ s H; contradiction.
simpl; intros f l IH Hnf s s_in_l u H.
destruct (In_split _ _ s_in_l) as [l' [l'' H']]; subst.
apply (Hnf (Term f (l' ++ u :: l''))).
apply P_in_context; clear IH Hnf s_in_l; induction l' as [ | s' l']; simpl.
left; trivial.
right; apply IHl'.
Qed.

Lemma P_acc_subterms :
  forall R P, (forall x t, ~ (R t (Var x))) -> 
  forall f l, (forall t, In t l -> Acc (P_step R P) t) -> constructor R f ->
                   Acc (P_step R P) (Term f l).
Proof.
intros R P HR f l Acc_l Cf'; inversion Cf' as [f' Cf]; clear Cf'; subst f'.
rewrite acc_one_step_list in Acc_l.
pattern l; refine (@Acc_ind _ (one_step_list (P_step R P)) _ _ l Acc_l).
clear l Acc_l; intros l Acc_l IH.
apply Acc_intro.
intros t H; inversion H as [t' s Hnf H' | f' l1 l2 H']; subst.
inversion H' as [t1 t2 sigma H'' H3 H''']; subst; destruct t2 as [x2 | f2 l2].
absurd (R t1 (Var x2)); trivial; apply HR.
simpl in H'''; injection H'''; clear H'''; intros; subst;
absurd (R t1 (Term f l2)); trivial; apply Cf.
apply IH.
generalize l2 l H'.
intro k; induction k as [ | s k]; intros k' K; inversion K; subst.
left; trivial.
right; trivial.
Qed.

Lemma P_acc_subterms_1 :
   forall R P t s, Acc (P_step R P) t -> direct_subterm s t -> Acc (P_step R P) s.
Proof.
intros R P t s Acc_t; generalize s; clear s; pattern t;
refine (@Acc_ind _ (P_step R P) _ _ t Acc_t).
clear t Acc_t; intros t Acc_t IH s H; destruct t as [ x | f l]; simpl in H.
contradiction.
apply Acc_intro; intros u H';
destruct (In_split _ _ H) as [l1 [l2 H'']]; subst l;
apply (IH (Term f (l1 ++ u :: l2))).
apply P_step_context_in; trivial.
simpl; apply in_or_app; right; left; trivial.
Qed.

Lemma P_acc_subterms_3 : 
   forall R P p t s, Acc (P_step R P) t -> subterm_at_pos t p = Some s ->  Acc (P_step R P) s.
Proof.
intros R P p; induction p as [ | i p]; intros t s Acc_t H; simpl in H.
injection H; intro; subst; trivial.
destruct t as [ x | f l].
discriminate.
assert (H' := nth_error_ok_in i l); destruct (nth_error l i) as [ s' | ].
generalize (H' _ (eq_refl _)); clear H'; intro s'_in_l.
apply (IHp s'); trivial; apply (P_acc_subterms_1 R P (Term f l)); trivial.
destruct s'_in_l as [l1 [l2 [_ H']]]; subst l; simpl; 
apply in_or_app; right; left; trivial.
discriminate.
Qed.

Lemma var_P_acc : 
   forall R P l x sigma, In x (var_list_list l) -> 
   (forall t, In t (map (apply_subst sigma) l) -> Acc (P_step R P) t) ->
   Acc (P_step R P) (apply_subst sigma (Var x)).
Proof.
intros R P l; pattern l; apply (list_rec3 size); clear l;
intro n; induction n as [ | n]; intros [ | t l] Sl x sigma H Acc_l.
simpl in H; contradiction.
simpl in Sl; absurd (1 <= 0); auto with arith.
apply Nat.le_trans with (size t).
apply size_ge_one.
refine (Nat.le_trans _ _ _ _ Sl); auto with arith.
simpl in H; contradiction.
assert (Sl' : list_size size l <= n).
apply le_S_n; refine (Nat.le_trans _ _ _ _ Sl); simpl;
apply (Nat.add_le_mono_r 1 (size t) (list_size size l)); apply size_ge_one.
destruct t as [y | g k].
simpl in H; destruct H as [y_eq_x | x_in_l].
subst y; apply Acc_l; simpl map; left; trivial.
apply (IHn l); trivial; intros; apply Acc_l; simpl map; right; trivial.
assert (Sk : list_size size k <= n).
apply le_S_n; refine (Nat.le_trans _ _ _ _ Sl); simpl; rewrite (list_size_fold size k);
apply le_n_S; apply Nat.le_add_r.
assert (Acc_k : forall t, In t (map (apply_subst sigma) k) -> Acc (P_step R P) t).
intros t H'; apply P_acc_subterms_1 with (Term g (map (apply_subst sigma) k)).
apply Acc_l; simpl map; left; trivial.
trivial.
replace (var_list_list (Term g k :: l)) with (var_list (Term g k)  ++ var_list_list l) in H; trivial.
rewrite var_list_unfold in H.
generalize (IHn _ Sk x sigma).
destruct (in_app_or _ _ _ H) as [x_in_k | x_in_l].
clear H; intro H; generalize (H x_in_k); clear H; intro H; apply H.
intros t H'; apply Acc_k; trivial.

simpl in H; intros _; apply (IHn l); trivial.
intros t H'; apply Acc_l; right; trivial.
Qed.

Lemma P_acc_with_subterm_subterms :
  forall R P t, Acc (union _ (P_step R P) direct_subterm) t ->
                 forall s, direct_subterm s t -> Acc (union _ (P_step R P) direct_subterm) s.
Proof.
intros R P t Acc_t; induction Acc_t as [t Acc_t IH].
intros s H; apply Acc_t; right; trivial.
Qed.

Lemma P_acc_with_subterm :
  forall R P t, Acc (P_step R P) t <->  Acc (union _ (P_step R P) direct_subterm) t.
Proof.
intros R P t; split.
intro Acc_t; induction Acc_t as [t Acc_t IH].
generalize Acc_t IH; clear Acc_t IH; pattern t; apply term_rec2; clear t.
intro n; induction n as [ | n]; intros t size_t Acc_t IH.
absurd (1 <= 0); auto with arith; apply Nat.le_trans with (size t); trivial;
apply size_ge_one.
apply Acc_intro.
intros u H; destruct H as [H | H].
(* 1/2 one_step R *)
apply IH; trivial.
(* 1/1 direct_subterm *)
apply IHn.
apply le_S_n; apply Nat.le_trans with (size t); trivial.
apply size_direct_subterm; trivial.
assert (H' : Acc (P_step R P) u).
apply P_acc_subterms_1 with t; trivial.
apply Acc_intro; apply Acc_t.
inversion H'; trivial.
intros v v_R_u.
destruct t as [ x | f l].
contradiction.
destruct (In_split _ _ H) as [l' [l'' H'']]; clear H; subst l.
apply (P_acc_with_subterm_subterms R P (Term f (l' ++ v :: l''))).
apply IH; apply P_step_context_in; trivial.
simpl; apply in_or_app; right; left; trivial.
apply Acc_incl; intros t1 t2 H; left; trivial.
Qed.

Lemma P_step_in_list :
  forall R P l l', one_step_list (P_step R P) l' l ->
  exists t, exists t', exists l1, exists l2, P_step R P t' t /\  l = l1 ++ t :: l2 /\ l' = l1 ++ t' :: l2.
Proof.
intros R P l l' H'; induction H'.
exists t2; exists t1; exists (@nil term); exists l; repeat split; trivial.
destruct IHH' as [u [u' [l3 [l4 [H1 [H2 H3]]]]]]; subst.
exists u; exists u'; exists (t :: l3); exists l4; repeat split; trivial.
Qed.

Definition inner (R : relation term) (t : term) :=
  forall s, direct_subterm s t -> nf (one_step R) s.

Lemma one_step_nf_inner_step_nf :
  forall (R : relation term), (forall t v, R t (Var v) -> False) ->
  forall t, nf (one_step R) t <-> nf (P_step R (inner R)) t.
Proof.
intros R Rvar t; split.
intros H s H'; apply (H s); apply (P_step_one_step R (inner R)); trivial.
pattern t; apply term_rec3; clear t.
intros v _ s H'; inversion H' as [t1 t2 H'' | f' l1 l2 H'']; clear H'; subst.
inversion H''; clear H''; subst.
destruct t2 as [v2 | f2 l2].
apply (Rvar t1 v2); trivial.
discriminate.
intros f l IH H s H'.
apply (H s); apply P_at_top.
intros t t_in_l; apply IH; trivial.
apply nf_P_step_subterm with (Term f l); trivial.
inversion H' as [t1 t2 H'' | f' l1 l2 H'']; clear H'; subst; trivial.
assert (H' : forall t, In t l -> nf (one_step R) t).
intros t t_in_l; apply IH; trivial.
apply nf_P_step_subterm with (Term f l); trivial.
assert False.
generalize l1 H'' H'; clear IH H l1 H'' H'; 
induction l as [ | t l]; intros l1 H'' H';
inversion H'' as [t1 t2' l' H3 | t' l1' l2' H3]; clear H''; subst.
apply (H' t (or_introl _ (eq_refl _)) t1); trivial.
apply (IHl l1'); trivial.
intros s s_in_l; apply H'; right; trivial.
contradiction.
Qed.

Lemma nf_dec_inner_dec : 
  forall R, (forall t, {nf (one_step R) t}+{~ nf (one_step R) t}) -> 
  forall t, {inner R t}+{~inner R t}.
Proof.
intros R nf_dec [v | f l].
left; intro s; simpl; contradiction.
unfold inner; simpl; induction l as [ | t l].
left; intro s; simpl; contradiction.
destruct (nf_dec t) as [nf_t | red_t].
destruct IHl as [nf_l | red_l].
left; intros s [s_eq_t | s_in_l]; [subst | apply nf_l]; trivial.
right; intro nf_tl; apply red_l; intros s s_in_l; apply nf_tl; right; trivial.
right; intro nf_tl; apply red_t; apply nf_tl; left; trivial.
Defined.


Section Context_sensitive.
Parameter mu : F.Symb.A -> list nat.

(*
Parameter mu_ok : 
forall f, forall i, In i (mu f) -> i < match F.arity f with Free n => n | _ => 2 end. 
*)

Inductive C_step (R : relation term) : term -> term -> Prop :=
  | C_at_top : forall t s, axiom R s t -> C_step R s t
  | C_in_context : 
     forall f n lt ls, C_list R n ls lt -> In n (mu f) -> C_step R (Term f ls) (Term f lt)

   with C_list (R : relation term) : nat -> list term -> list term -> Prop :=
    | C_head_step : forall t1 t2 l, C_step R t1 t2 -> C_list R 0 (t1 :: l) (t2 :: l)
    | C_tail_step : forall t l1 l2 i, C_list R i l1 l2 -> C_list R (S i) (t :: l1) (t :: l2).

Definition shifted_active_in_list shift f l (s : term) := 
exists i, In (shift + i) (mu f) /\ nth_error l i = Some s.

Definition active_in_list f l (s : term) := shifted_active_in_list 0 f l s. 

Definition active_direct_subterm s t :=
  match t with
  | Var _ => False
  | Term f l => active_in_list f l s
  end.

Definition active_subterm s t := refl_trans_clos active_direct_subterm s t.

Fixpoint active_position t p {struct p} : bool :=
match p with
| nil => true
| i :: q => 
   match t with 
   | Var _ => false
   | Term f l => 
        andb (mem_bool Nat.eqb i (mu f))
                 (match nth_error l i with
                 | None => false
                 | Some ti => active_position ti q
                 end)
   end
end.

Lemma active_is_active : 
  forall s t, active_subterm s t <-> (exists p, active_position t p = true /\ subterm_at_pos t p = Some s).
Proof.
intros s t; split.
intro H; inversion H as [u | s' t' H']; clear H.
subst; exists nil; simpl; split; apply eq_refl.
subst s' t'; rewrite trans_clos_trans_clos_alt in H'; induction H' as [x y H | x y z H1 H2].
destruct y as [v | f l].
contradiction.
destruct H as [i [K1 K2]].
exists (i :: nil); simpl; split.
generalize (mem_bool_ok _ _ beq_nat_ok i (mu f)); case (mem_bool Nat.eqb i (mu f)).
intros _; simpl; rewrite K2; apply eq_refl.
intro i_not_in_mu_f; apply False_rect; apply i_not_in_mu_f.
apply (in_impl_mem (@eq _) (fun a => eq_refl a) i (mu f) K1).
rewrite K2; apply eq_refl.
destruct z as [v | f l].
contradiction.
destruct H as [i [K1 K2]].
destruct H2 as [p [K3 K4]].
exists (i :: p); simpl; split.
generalize (mem_bool_ok _ _ beq_nat_ok i (mu f)); case (mem_bool Nat.eqb i (mu f)).
intros _; simpl; rewrite K2; assumption.
intro i_not_in_mu_f; apply False_rect; apply i_not_in_mu_f.
apply (in_impl_mem (@eq _) (fun a => eq_refl a) i (mu f) K1).
rewrite K2; assumption.
intros [p [H1 H2]].
revert s t H1 H2; induction p as [ | i p]; intros s t H1 H2.
simpl in H2; injection H2; clear H2; intros; subst; left.
destruct t as [x | f l].
discriminate.
simpl in H1; simpl in H2.
revert H1 H2; generalize (nth_error_ok_in i l); case (nth_error l i).
intros ti H; destruct (H _ (eq_refl _)) as [l1 [l2 [L H']]]; clear H.
generalize (mem_bool_ok _ _ beq_nat_ok i (mu f)); case (mem_bool Nat.eqb i (mu f)).
intro i_in_mu_f; simpl; intros H1 H2.
apply refl_trans_clos_is_trans with ti.
apply IHp; trivial.
right; left; exists i; split.
apply mem_impl_in with (@eq _); trivial.
subst l i; rewrite nth_error_at_pos; apply eq_refl.
intros; discriminate.
intros; discriminate.
Qed.

Lemma context_acc_subterms_1 :
   forall R t s, Acc (C_step R) t -> active_direct_subterm s t -> Acc (C_step R) s.
Proof.
intros R t s Acc_t; generalize s; clear s; pattern t.
refine (@Acc_ind _ (C_step R) _ _ t Acc_t).
clear t Acc_t; intros t Acc_t IH s H.
 destruct t as [ x | f l]; simpl in H.
contradiction.
apply Acc_intro; intros u H'.
destruct H as [i [H1 H2]].
destruct (nth_error_ok_in _ _ H2) as [l1 [l2 [L H'']]]; subst l.
apply (IH (Term f (l1 ++ u :: l2))).
apply C_in_context with i; trivial.
subst i; revert H'; clear; induction l1 as [ | a1 l1]; intro H.
left; assumption.
right; apply IHl1; assumption.
exists (length l1); split.
subst; trivial.
rewrite nth_error_at_pos; apply eq_refl.
Qed.

Lemma context_acc_subterms_2 :
   forall R t s, Acc (C_step R) t -> active_subterm s t -> Acc (C_step R) s.
Proof.
intros R t s Acc_t H.
inversion H as [u | s' t' H']; clear H.
assumption.
subst.
rewrite trans_clos_trans_clos_alt in H'.
induction H' as [x y | x y z].
apply context_acc_subterms_1 with y; trivial.
apply IHH'.
apply context_acc_subterms_1 with z; trivial.
Qed.

Lemma instanciated_active_subterm : 
  forall s t sigma, active_subterm s t -> active_subterm (apply_subst sigma s) (apply_subst sigma t).
Proof.
intros s t sigma H; inversion H as [u | s' t' H']; clear H.
left.
subst; rewrite trans_clos_trans_clos_alt in H'; induction H' as [x y | x y z].
right; left.
destruct y as [v | f l].
contradiction.
destruct H as [i [H1 H2]].
exists i; split; trivial.
generalize (nth_error_map (apply_subst sigma) l i); rewrite H2.
case (nth_error (map (apply_subst sigma) l) i).
intros ti Hi; rewrite Hi; apply eq_refl.
contradiction.
apply refl_trans_clos_is_trans with (apply_subst sigma y); trivial.
right; left; destruct z as [v | f l].
contradiction.
destruct H as [i [H1 H2]].
exists i; split; trivial.
generalize (nth_error_map (apply_subst sigma) l i); rewrite H2.
case (nth_error (map (apply_subst sigma) l) i).
intros ti Hi; rewrite Hi; apply eq_refl.
contradiction.
Qed.

Lemma active_position_in_instanciated_term :
  forall p t s sigma, active_position (apply_subst sigma t) p = true -> subterm_at_pos t p = Some s ->
  active_position t p = true.
Proof.
intro p; induction p as [ | i p].
intros; trivial.
intros [v | f l] s sigma; simpl.
intros; discriminate.
case (mem_bool Nat.eqb i (mu f)); [idtac | intros; discriminate].
generalize (nth_error_map (apply_subst sigma) l i).
case (nth_error (map (apply_subst sigma) l) i); [idtac | intros; discriminate]; simpl.
generalize (nth_error_ok_in i l); case (nth_error l i); [idtac | contradiction].
intros t H s' H'; destruct (H _ (eq_refl _)) as [l1 [l2 [L K]]]; clear H; subst.
apply IHp; apply in_or_app; right; left; apply eq_refl.
Qed.

Inductive cdp (R : relation term) : term -> term -> Prop:= 
  | Cdp : forall t1 t2 f2 l2, R t2 t1 -> 
                active_subterm (Term f2 l2) t2 -> 
                defined R f2 ->
                cdp R (Term f2 l2) t1.

Inductive vdp (R : relation term) : term -> term -> Prop:= 
  | Vdp : forall t1 t2 x, R t2 t1 -> 
                active_subterm (Var x) t2 -> (not (active_subterm (Var x) t1)) ->
                vdp R (Var x) t1.

Definition c_in_context R shift f ls lt := exists n, C_list R n ls lt /\ In (shift + n) (mu f).

Inductive cdp_step (R : relation term) : term -> term -> Prop :=
   | Cdp_step : 
       forall f l1 l2 t3, 
       refl_trans_clos (c_in_context R 0 f) l2 l1 -> axiom (cdp R) t3 (Term f l2) -> 
       cdp_step R t3 (Term f l1)
  | Vdp_step :
       forall f l1 l2 t3 w, 
       refl_trans_clos (c_in_context R 0 f) l2 l1 -> axiom (vdp R) t3 (Term f l2) ->
       active_subterm w t3 -> 
       cdp_step R w (Term f l1).

Lemma Context_Acc_var : 
  forall R, (forall x t, ~ (R t (Var x))) -> forall x, Acc (C_step R) (Var x).
Proof.
intros R HR x; apply Acc_intro.
intros y H; inversion H; clear H; subst.
inversion H0; clear H0; subst.
destruct t2 as [x2 | f2 l2].
apply False_rect; apply (HR _ _ H2).
discriminate.
Qed.

Fixpoint actives f n l : list term :=
match l with
| nil => nil
| t :: l => if mem_bool Nat.eqb n (mu f) then t :: (actives f (S n) l) else (actives f (S n) l) 
end.

Lemma actives_ok : 
  forall f n l s, In s (actives f n l) <-> shifted_active_in_list n f l s.
Proof.
intros f n l; revert n; induction l as [ | t l]; intros n s; simpl; split.
contradiction.
intros [[ | i] [_ H]]; discriminate.
generalize (mem_bool_ok _ _ beq_nat_ok n (mu f)).
case (mem_bool Nat.eqb n (mu f)).
intro n_in_mu_f.
simpl; intros [s_eq_t | s_in_actives].
subst s; exists 0; split; trivial.
rewrite Nat.add_comm; apply mem_impl_in with (@eq _); trivial.
rewrite IHl in s_in_actives; destruct s_in_actives as [i [H1 H2]].
exists (S i); split; trivial.
rewrite Nat.add_comm; simpl; rewrite Nat.add_comm; assumption.
intro n_not_in_mu_f.
rewrite IHl; intros [i [H1 H2]].
exists (S i); split; trivial.
rewrite Nat.add_comm; simpl; rewrite Nat.add_comm; assumption.
generalize (mem_bool_ok _ _ beq_nat_ok n (mu f)).
case (mem_bool Nat.eqb n (mu f)).
intro n_in_mu_f.
intros [[ | i] [H1 H2]].
simpl in H2; injection H2; clear H2; intro; subst s; left; apply eq_refl.
right; rewrite IHl.
exists i; split; trivial.
revert H1; rewrite Nat.add_comm; simpl; rewrite Nat.add_comm; trivial.
intro n_not_in_mu_f.
intros [[ | i] [H1 H2]].
rewrite Nat.add_comm in H1; apply False_rect; apply n_not_in_mu_f; apply in_impl_mem; trivial.
rewrite IHl; exists i; split; trivial.
revert H1; rewrite Nat.add_comm; simpl; rewrite Nat.add_comm; trivial.
Qed.

Lemma shifting_context : 
forall R f shift l', 
Acc (c_in_context R shift f) l' -> 
Acc (c_in_context R (S shift) f) (match l' with nil => nil | _ :: l => l end).
Proof.
intros R f shift l Acc_l; induction Acc_l as [l Acc_l IH].
destruct l as [ | t l].
apply Acc_intro; intros y [n [H _]]; inversion H.
apply Acc_intro; intros k H.
apply (IH (t :: k)).
unfold c_in_context in *.
destruct H as [n [H1 H2]].
exists (S n); split.
apply C_tail_step; assumption.
rewrite Nat.add_comm; simpl; rewrite Nat.add_comm; assumption.
Qed.

Lemma shifting_head :
forall R f shift l, Acc (c_in_context R shift f) l ->
mem eq shift (mu f) -> (forall t, (exists k, l = t::k) -> Acc (C_step R) t).
Proof.
intros R f shift l Acc_l; induction Acc_l as [l Acc_l IH].
destruct l as [ | t l].
intros _ t [l H]; discriminate.
intros shift_in_mu_f.
intros s [l' H].
injection H; clear H; intros; subst s l'.
apply Acc_intro; intros s H.
apply (IH (s :: l)).
exists 0; split.
left; trivial.
rewrite Nat.add_comm; simpl.
apply mem_impl_in with (@eq _); trivial.
assumption.
exists l; apply eq_refl.
Qed.

Lemma filtering : 
  forall R shift f l l1, 
    c_in_context R shift f l1 l ->
    one_step_list (C_step R) (actives f shift l1) (actives f shift l).
Proof.
intros R shift f l; revert f shift.
induction l as [ | t l]; simpl; intros f shift l1.
(* 1/4 nil *)
intros [n [H _]]; inversion H.
(* 1/2 t :: l *)
intros [n [K H]]; inversion K; clear K; subst; simpl.
generalize (mem_bool_ok _ _ beq_nat_ok shift (mu f)); case (mem_bool Nat.eqb shift (mu f)).
intro shift_in_mu_f; left; assumption.
intro shift_not_in_mu; apply False_rect; rewrite Nat.add_comm in H;
apply shift_not_in_mu; apply in_impl_mem; trivial.
generalize (mem_bool_ok _ _ beq_nat_ok shift (mu f)); case (mem_bool Nat.eqb shift (mu f)).
intros _; right; apply IHl.
exists i; split; trivial.
revert H; rewrite Nat.add_comm; simpl; rewrite Nat.add_comm; trivial.
intros _; apply IHl.
exists i; split; trivial.
revert H; rewrite Nat.add_comm; simpl; rewrite Nat.add_comm; trivial.
Qed.

Lemma acc_filtering : 
  forall R shift f l, Acc (c_in_context R shift f) l <-> Acc (one_step_list (C_step R)) (actives f shift l).
Proof.
intros R shift f l; revert f shift.
induction l as [ | t l]; simpl; split.
(* 1/4 nil -> *)
intro Acc_nil; apply Acc_intro; intros y H; inversion H.
(* 1/3 nil <- *)
intro Acc_nil; apply Acc_intro; intros y [n [H _]]; inversion H.
(* 1/2 t :: l -> *)
intro Acc_l.
apply Acc_intro.
generalize (mem_bool_ok _ _ beq_nat_ok shift (mu f)); case (mem_bool Nat.eqb shift (mu f)).
(* 1/3 shift belongs to (mu f) *)
intro shift_in_mu_f.
intros k H.
inversion H; clear H; subst.
(* 1/4 reduction at head position t1 <- t *)
rewrite <- acc_one_step_list.
simpl; intros u [u_eq_t1 | u_in_actives].
subst; apply Acc_inv with t; trivial.
apply (shifting_head _ _ _ _ Acc_l); trivial.
exists l; apply eq_refl.
revert u u_in_actives.
rewrite acc_one_step_list.
rewrite <- IHl.
revert Acc_l; clear.
apply shifting_context.
(* 1/3 reduction in the tail *)
rewrite <- acc_one_step_list.
simpl; intros u [u_eq_t1 | u_in_actives].
subst u; apply (shifting_head _ _ _ _ Acc_l); trivial.
exists l; apply eq_refl.
revert u u_in_actives; rewrite acc_one_step_list.
apply Acc_inv with (actives f (S shift) l); trivial.
rewrite <- IHl.
apply (shifting_context _ _ _ _ Acc_l).
(* 1/2 shift DOES NOT belong to (mu f) *)
intros shift_not_in_mu_f.
intros k H.
apply Acc_inv with (actives f (S shift) l); trivial.
rewrite <- IHl.
apply (shifting_context _ _ _ _ Acc_l).
(* 1/1 t :: l <-  *)
generalize (mem_bool_ok _ _ beq_nat_ok shift (mu f)); case (mem_bool Nat.eqb shift (mu f)).
(* 1/2 shift belongs to (mu f) *)
intro shift_in_mu_f.
rewrite <- acc_one_step_list.
intros Acc_tl.
assert (Acc_l := tail_prop _ Acc_tl).
rewrite acc_one_step_list in Acc_l.
rewrite <- IHl in Acc_l.
assert (Acc_t := Acc_tl _ (or_introl _ (eq_refl _))).
clear Acc_tl.
clear IHl; revert l Acc_l.
induction Acc_t as [t Acc_t IH].
intros l Acc_l.
revert t Acc_t IH; induction Acc_l as [l Acc_l IHl].
intros t Acc_t IHt.
apply Acc_intro; intros k H.
destruct H as [n [H1 H2]].
inversion H1; clear H1; subst.
(* 1/3 reduction at the head *)
apply IHt; trivial.
apply Acc_intro; assumption.
(* 1/2 reduction in the tail *)
apply IHl; trivial.
exists i; split; trivial.
revert H2; rewrite Nat.add_comm; simpl; rewrite Nat.add_comm; trivial.
(* 1/1 shift DOES NOT belong to (mu f) *)
intros shift_not_in_mu_f.
rewrite <- IHl.
clear IHl.
intro Acc_l; induction Acc_l as [l Acc_l IH].
apply Acc_intro; intros k H.
destruct H as [n [H1 H2]].
inversion H1; clear H1; subst.
apply False_rect; apply shift_not_in_mu_f.
apply in_impl_mem; trivial.
rewrite Nat.add_comm in H2; assumption.
apply IH; exists i; split; trivial.
revert H2; rewrite Nat.add_comm; simpl; rewrite Nat.add_comm; trivial.
Qed.

Lemma Acc_C_step_acc_c_in_context :
forall R f l, (forall s, active_in_list f l s -> Acc (C_step R) s) -> Acc (c_in_context R 0 f) l. 
Proof.
intros R f l Acc_l.
rewrite acc_filtering. 
rewrite <- acc_one_step_list.
intros s s_in_actives; apply Acc_l.
unfold active_in_list.
revert s s_in_actives; clear.
intros s H; rewrite <- actives_ok; assumption.
Qed.

Lemma context_acc_subterms :
  forall R, (forall x t, ~ (R t (Var x))) -> 
  forall f l, (forall t, active_in_list f l t -> Acc (C_step R) t) -> constructor R f ->
                   Acc (C_step R) (Term f l).
Proof.
intros R HR f l Acc_l Cf'; inversion Cf' as [f' Cf]; clear Cf'; subst f'.
assert (Acc_l' := Acc_C_step_acc_c_in_context _ _ _ Acc_l); clear Acc_l.
induction Acc_l' as [l Acc_l IH].
apply Acc_intro.
intros t H; inversion H as [t1 t2 H' | f' n l1 l2 H']; subst.
inversion H' as [t1 t2 sigma H'' H3 H''']; subst; destruct t2 as [x2 | f2 l2].
absurd (R t1 (Var x2)); trivial; apply HR.
simpl in H'''; injection H'''; clear H'''; intros; subst;
absurd (R t1 (Term f l2)); trivial; apply Cf.
apply IH.
exists n; split; trivial.
Qed.

Lemma active_dec : forall s t, {active_subterm s t}+{~ active_subterm s t}.
Proof.
intros s t; revert s; pattern t; apply term_rec3.
(* 1/2 variable case *)
intros v s; generalize (eq_bool_ok s (Var v)); case (eq_bool s (Var v)).
intros s_eq_v; left; subst s; left.
intros s_diff_v; right; intro A; apply s_diff_v.
inversion A; subst; trivial.
rewrite trans_clos_trans_clos_alt in H.
inversion H; clear H; subst.
inversion H0.
inversion H1.
(* compound term case (Term f l) *)
intros f l IH s.
generalize (eq_bool_ok s (Term f l)); case (eq_bool s (Term f l)).
(* 1/2 s is equal to (Term f l) *)
intro s_eq_fl; left; subst s; left.
(* 1/1 s is different from (Term f l) *)
intros s_diff_fl.
assert (H : {ti | In ti l /\ active_subterm s ti /\ active_direct_subterm ti (Term f l)}+
                  {forall ti, In ti l -> active_direct_subterm ti (Term f l) -> active_subterm s ti -> False}).
(* 1/2 main proof on l *)
clear s_diff_fl; simpl.
unfold active_in_list; generalize 0.
revert s; induction l as [ | t1 l].
(* 1/3 l is equal to nil *)
intros s n; right; intros; contradiction.
(* 1/2 l is equal to (t1 :: l) *)
intros s n; simpl.
generalize (mem_bool_ok _ _ beq_nat_ok n (mu f)); case (mem_bool Nat.eqb n (mu f)).
(* 1/3 n is in (mu f) *)
intro n_in_mu_f; destruct (IH _ (or_introl _ (eq_refl _)) s) as [A1 | not_A1].
(* 1/4 s is active in t1 *)
left; exists t1; split.
left; apply eq_refl.
split; trivial.
exists 0; split.
rewrite Nat.add_comm; apply mem_impl_in with (@eq _); trivial.
apply eq_refl.
(* 1/3 s is NOT active in t1 *)
destruct (IHl (tail_set _ IH) s (S n)) as [Ai | not_Al].
(* 1/4 there is a ti such that s is active in ti *)
destruct Ai as [ti [ti_in_l [Ai Al]]].
left; exists ti; split; [idtac | split].
right; assumption.
assumption.
destruct Al as [i [H1 H2]].
exists (S i); split; trivial.
rewrite Nat.add_comm; simpl; rewrite Nat.add_comm; trivial.
(* 1/3 there is no ti such that s is active in ti *)
right; intros ti [t1_eq_ti | ti_in_l] Al Ai.
apply not_A1; subst ti; assumption.
destruct Al as [[ | i] [H1 H2]].
injection H2; clear H2; intro; subst ti.
apply not_A1; assumption.
apply (not_Al ti ti_in_l); trivial.
exists i; split; trivial.
revert H1; rewrite Nat.add_comm; simpl; rewrite Nat.add_comm; trivial.
(* 1/2 n in NOT in (mu f) *)
intro not_mem_n_mu_f.
destruct (IHl (tail_set _ IH) s (S n)) as [Ai | not_Al].
(* 1/3 there is a ti such that s is active in ti *)
destruct Ai as [ti [ti_in_l [Ai Al]]].
left; exists ti; split; [idtac | split].
right; assumption.
assumption.
destruct Al as [i [H1 H2]].
exists (S i); split; trivial.
rewrite Nat.add_comm; simpl; rewrite Nat.add_comm; trivial.
(* 1/2 there is no ti such that s is active in ti *)
right; intros ti [t1_eq_ti | ti_in_l] Al Ai.
(* 1/3 proof of the right alternative for t1 *)
destruct Al as [[ | i] [H1 H2]].
rewrite Nat.add_comm in H1; apply not_mem_n_mu_f; apply in_impl_mem; trivial.
apply (not_Al ti); trivial.
simpl in H2; destruct (nth_error_ok_in _ _ H2) as [l1 [l2 [L H]]]; 
subst l; apply in_or_app; right; left; apply eq_refl.
exists i; split; trivial.
revert H1; rewrite Nat.add_comm; simpl; rewrite Nat.add_comm; trivial.
(* 1/2 proof of the right alternative for ti *)
apply (not_Al ti); trivial.
destruct Al as [[ | i] [H1 H2]].
apply False_rect; rewrite Nat.add_comm in H1; apply not_mem_n_mu_f; apply in_impl_mem; trivial.
simpl in H2; exists i; split; trivial.
revert H1; rewrite Nat.add_comm; simpl; rewrite Nat.add_comm; trivial.
(* 1/1 application of the main proof *)
destruct H as [[ti [ti_in_l [Ai Al]]] | H].
left; apply refl_trans_clos_is_trans with ti; trivial.
right; left; trivial.
right; intro A; inversion A as [u | x y A']; clear A.
subst; apply s_diff_fl; apply eq_refl.
rewrite trans_clos_trans_clos_alt in A'; inversion A' as [x' y' A'' | x' y' z' A1 A2]; clear A'; subst.
apply (H s); trivial.
destruct A'' as [i [H1 H2]].
simpl in H2; destruct (nth_error_ok_in _ _ H2) as [l1 [l2 [L H3]]]; 
subst l; apply in_or_app; right; left; apply eq_refl.
left.
apply (H y'); trivial.
destruct A2 as [i [H1 H2]].
simpl in H2; destruct (nth_error_ok_in _ _ H2) as [l1 [l2 [L H3]]]; 
subst l; apply in_or_app; right; left; apply eq_refl.
rewrite <- trans_clos_trans_clos_alt in A1; right; trivial.
Qed.

Lemma cdp_criterion_local : 
  forall R, (forall x t, ~ (R t (Var x))) -> 
  (forall s t, R s t -> forall x, In x (var_list s) -> In x (var_list t)) ->
  (forall f, {constructor R f} + {defined R f}) ->
  forall t,   Acc (cdp_step R) t -> (forall s, active_direct_subterm s t -> Acc (C_step R) s) ->
              Acc (C_step R) t.
Proof.
intros R HR RR CD.
(* main proof *)
intros t Acc_t; induction Acc_t as [t Acc_t IH].
intros Acc_l; destruct t as [x | f l].
apply Context_Acc_var; assumption.
simpl active_direct_subterm in Acc_l.
assert (Acc_l' := Acc_C_step_acc_c_in_context _ _ _ Acc_l).
rewrite acc_filtering in Acc_l'.
clear Acc_l; rename Acc_l' into Acc_l.
set (actives_l := actives f 0 l).
generalize (eq_refl actives_l).
unfold actives_l at 2.
clearbody actives_l.
intro H; rewrite <- H in Acc_l.
revert l H IH Acc_t.
induction Acc_l as [actives_l Acc_l IHl]; intros l AH IH Acc_t.
assert (Acc_l' : Acc (one_step_list (C_step R)) actives_l).
apply Acc_intro; assumption.
clear Acc_l; rename Acc_l' into Acc_l.
rewrite <- acc_one_step_list in Acc_l.
apply Acc_intro; 
intros s H; destruct s as [x1 | f1 l1].
apply Context_Acc_var; assumption.
inversion H as [t1 t2 H' | f' n l1' l2 H']; clear H; subst.
(* 1/2 rewrite step at the top *)
inversion H' as [t1 t2 sigma t1_R_t2 H1 H2]; clear H'.
destruct t2 as [x | g k].
absurd (R t1 (Var x)); trivial; apply HR.
simpl in H2; injection H2; clear H2; intros; subst g l.
assert (H'' : forall n t, size t <= n -> active_subterm t (apply_subst sigma t1) ->
                                                        Acc (C_step R) t).
intro n; induction n as [ | n].
intros t St; absurd (1 <= 0); auto with arith;
apply Nat.le_trans with (size t); trivial; apply size_ge_one.
intros [x | g h] St A.
(* 1/4 t is a variable *)
apply Context_Acc_var; trivial.
(* 1/3 t = Term g h *)
assert (Acc_h : forall t, In t h -> active_subterm t (apply_subst sigma t1) -> Acc (C_step R) t).
intros t t_in_h At; apply IHn; trivial.
apply le_S_n; refine (Nat.le_trans _ _ _ _ St); apply size_direct_subterm; simpl; trivial.
destruct (CD g) as [Cg | Dg].
(* 1/4 g is a constructor symbol *)
simpl; apply context_acc_subterms; trivial.
intros t t_in_h; apply Acc_h.
revert t_in_h; clear; unfold active_in_list, shifted_active_in_list; generalize 0.
induction h as [ | s h].
simpl; intros n [[ | i] [_ H]]; discriminate.
intros n [[ | i] [H1 H2]]; simpl in H2.
injection H2; clear H2; intros; left; assumption.
right; apply IHh with (S n).
exists i; split; trivial.
revert H1; rewrite Nat.add_comm; simpl; rewrite Nat.add_comm; trivial.
apply refl_trans_clos_is_trans with (Term g h); trivial.
right; left; trivial.
(* 1/3 g is a defined symbol *)
rewrite active_is_active in A.
destruct A as [p [Ap Sub]].
generalize (subterm_in_instantiated_term _ _ _ Sub).
case_eq (subterm_at_pos t1 p).
(* 1/4 almost standard case, p is a position of t1 *)
intros u Sub' H.
destruct u as [xu | g' lu].
(* 1/5 u is a variable xu *)
destruct (active_dec (Var xu) (Term f k)) as [Axu_in_k | not_Axu_in_k].
(* 1/6 xu is active in (Term f k),  *)
inversion Axu_in_k as [xu' | xu' fk' Axu_in_k']; clear Axu_in_k; subst.
rewrite trans_clos_trans_clos_alt in Axu_in_k'; inversion Axu_in_k' as [xu' fk' Axu_in_k | xu' y fk' A1 A2]; subst.
apply Acc_l.
destruct Axu_in_k as [i [K1 K2]].
rewrite actives_ok; exists i; split; trivial.
generalize (nth_error_map (apply_subst sigma) k i); rewrite K2.
case (nth_error (map (apply_subst sigma) k) i).
intros ti Hi; rewrite H; rewrite Hi; apply eq_refl.
contradiction.
apply context_acc_subterms_2 with (apply_subst sigma y).
apply Acc_l.
destruct A2 as [i [K1 K2]].
rewrite actives_ok; exists i; split; trivial.
generalize (nth_error_map (apply_subst sigma) k i); rewrite K2.
case (nth_error (map (apply_subst sigma) k) i).
intros ti Hi; rewrite Hi; apply eq_refl.
contradiction.
rewrite H; apply instanciated_active_subterm; rewrite <- trans_clos_trans_clos_alt in A1; right; assumption.
(* 1/5 xu is not active in (Term f k) *)
apply IH.
apply Vdp_step with (map (apply_subst sigma) k) (Term g h).
left.
rewrite H.
replace (Term f (map (apply_subst sigma) k)) with (apply_subst sigma (Term f k)); trivial.
apply instance; apply Vdp with t1; trivial.
rewrite active_is_active; exists p; split; trivial.
apply active_position_in_instanciated_term with (Var xu) sigma; trivial.
left.
intros s s_in_h; apply Acc_h.
destruct s_in_h as [i [K1 K2]].
destruct (nth_error_ok_in _ _ K2) as [h1 [h2 [L K3]]]; subst; apply in_or_app; right; left; apply eq_refl.
apply refl_trans_clos_is_trans with (Term g h); trivial.
right; left; trivial.
assert (Dummy : active_subterm (Term g h) (apply_subst sigma t1)).
rewrite active_is_active.
exists p; split; trivial.
assumption.
(* 1/4 us is a compound term (Term g' lu) *)
rewrite H.
apply IH.
apply Cdp_step with (map (apply_subst sigma) k).
left.
replace (Term f (map (apply_subst sigma) k)) with (apply_subst sigma (Term f k)); trivial.
apply instance.
apply Cdp with t1; trivial.
rewrite active_is_active; exists p; split; trivial.
apply active_position_in_instanciated_term with (Term g' lu) sigma; trivial.
injection H; clear H; intros; subst; assumption.
intros s As; apply Acc_h.
rewrite <- H in As; destruct As as [i [K1 K2]].
destruct (nth_error_ok_in _ _ K2) as [h1 [h2 [L K3]]]; subst; apply in_or_app; right; left; apply eq_refl.
apply refl_trans_clos_is_trans with (Term g h); trivial.
right; left; rewrite H; assumption.
assert (Dummy : active_subterm (Term g h) (apply_subst sigma t1)).
rewrite active_is_active; exists p; split; trivial.
unfold active_subterm in Dummy; assumption.
(* 1/3 special case, p is a NOT position of t1 *)
intros Sub' [v [q [q' [J1 [v_in_t1 [Sub'' J2]]]]]]; subst p.
destruct (active_dec (Var v) (Term f k)) as [Av_in_k | not_Av_in_k].
(* 1/4 v is active in (Term f k)  *)
apply context_acc_subterms_2 with (apply_subst sigma (Var v)).
inversion Av_in_k as [v' | v' fk' Av_in_k']; clear Av_in_k; subst.
rewrite trans_clos_trans_clos_alt in Av_in_k'; inversion Av_in_k' as [v' fk' Av_in_k | v' y fk' A1 A2]; subst.
apply Acc_l.
destruct Av_in_k as [i [K1 K2]].
rewrite actives_ok; exists i; split; trivial.
generalize (nth_error_map (apply_subst sigma) k i); rewrite K2.
case (nth_error (map (apply_subst sigma) k) i).
intros ti Hi; rewrite Hi; apply eq_refl.
contradiction.
apply context_acc_subterms_2 with (apply_subst sigma y).
apply Acc_l.
destruct A2 as [i [K1 K2]].
rewrite actives_ok; exists i; split; trivial.
generalize (nth_error_map (apply_subst sigma) k i); rewrite K2.
case (nth_error (map (apply_subst sigma) k) i).
intros ti Hi; rewrite Hi; apply eq_refl.
contradiction.
apply refl_trans_clos_is_trans with (apply_subst sigma (Var v)).
assert (Dummy : active_subterm (Term g h) (apply_subst sigma (Var v))).
rewrite active_is_active; exists q'; split; trivial.
generalize (subterm_at_pos_apply_subst_apply_subst_subterm_at_pos t1 q sigma).
rewrite Sub''; trivial.
revert Ap.
generalize (apply_subst sigma t1) (apply_subst sigma (Var v)); clear.
revert q'; induction q as [ | i q]; simpl.
intros q' t s A H; injection H; clear H; intros; subst; trivial.
intros q' [v | f l] s.
intros; discriminate.
case (mem_bool Nat.eqb i (mu f)); [idtac | intros; discriminate].
simpl; case (nth_error l i); [idtac | intros; discriminate].
intro t; apply IHq.
left.
assert (Dummy : active_subterm (apply_subst sigma (Var v)) (apply_subst sigma y)).
apply instanciated_active_subterm; rewrite <- trans_clos_trans_clos_alt in A1; right; assumption.
assumption.
rewrite active_is_active; exists q'; split; trivial.
assert (Sub''' : subterm_at_pos (apply_subst sigma t1) q  = Some (apply_subst sigma (Var v))).
generalize (subterm_at_pos_apply_subst_apply_subst_subterm_at_pos t1 q sigma).
rewrite Sub''; trivial.
revert Ap Sub'''.
generalize (apply_subst sigma t1) (apply_subst sigma (Var v)); clear.
revert q'; induction q as [ | i q]; simpl.
intros q' t s A H; injection H; clear H; intros; subst; trivial.
intros q' [v | f l] s.
intros; discriminate.
case (mem_bool Nat.eqb i (mu f)); [idtac | intros; discriminate].
simpl; case (nth_error l i); [idtac | intros; discriminate].
intro t; apply IHq.
(* 1/3 v is not active in (Term f k) *)
apply IH.
apply Vdp_step with (map (apply_subst sigma) k) (apply_subst sigma (Var v)).
left.
replace (Term f (map (apply_subst sigma) k)) with (apply_subst sigma (Term f k)); trivial.
apply instance; apply Vdp with t1; trivial.
rewrite active_is_active; exists q; split; trivial.
apply active_position_in_instanciated_term with (Var v) sigma; trivial.
revert Ap; generalize (apply_subst sigma t1); clear.
revert q'; induction q as [ | i q]; intro q'.
simpl; trivial.
intros [v | f l].
intros; discriminate.
simpl; case (mem_bool Nat.eqb i (mu f)); [idtac | intros; discriminate].
case (nth_error l i); [idtac | intros; discriminate].
intros t; simpl; apply IHq.
rewrite active_is_active; exists q'; split; trivial.
assert (Sub''' : subterm_at_pos (apply_subst sigma t1) q  = Some (apply_subst sigma (Var v))).
generalize (subterm_at_pos_apply_subst_apply_subst_subterm_at_pos t1 q sigma).
rewrite Sub''; trivial.
revert Ap Sub'''.
generalize (apply_subst sigma t1) (apply_subst sigma (Var v)); clear.
revert q'; induction q as [ | i q]; simpl.
intros q' t s A H; injection H; clear H; intros; subst; trivial.
intros q' [v | f l] s.
intros; discriminate.
case (mem_bool Nat.eqb i (mu f)); [idtac | intros; discriminate].
simpl; case (nth_error l i); [idtac | intros; discriminate].
intro t; apply IHq.
intros s s_in_h; apply Acc_h.
destruct s_in_h as [i [K1 K2]].
destruct (nth_error_ok_in _ _ K2) as [h1 [h2 [L K3]]]; subst; apply in_or_app; right; left; apply eq_refl.
apply refl_trans_clos_is_trans with (Term g h); trivial.
right; left; trivial.
assert (Dummy : active_subterm (Term g h) (apply_subst sigma t1)).
rewrite active_is_active.
exists (q ++ q'); split; trivial.
assumption.
(* 1/2 *)
apply (H'' (size (apply_subst sigma t1))).
apply le_n.
left.
(* 1/1 rewrite step NOT at the top *)
apply IHl with (actives f 0 l1); trivial.
apply filtering.
exists n; split; trivial.

intros s H'' H'''; apply IH; trivial.
inversion H'' as [f' l1' l2 s' K1 K2 | f' l1' l2 s' K1 K2]; subst.
apply Cdp_step with l2; [idtac | trivial].
apply refl_trans_clos_is_trans with l1.
assumption.
right; left; exists n; split; trivial.
apply Vdp_step with l2 s'; [idtac | trivial | trivial].
apply refl_trans_clos_is_trans with l1.
assumption.
right; left; exists n; split; trivial.

intros t H; apply Acc_t.
inversion H as [f' l1' l2 s' K1 K2 | f' l1' l2 s' K1 K2]; subst.
apply Cdp_step with l2; [idtac | trivial].
apply refl_trans_clos_is_trans with l1.
assumption.
right; left; exists n; split; trivial.
apply Vdp_step with l2 s'; [idtac | trivial | trivial].
apply refl_trans_clos_is_trans with l1.
assumption.
right; left; exists n; split; trivial.
Qed.

Lemma cdp_criterion : 
  forall R, (forall x t, ~ (R t (Var x))) -> 
  (forall s t, R s t -> forall x, In x (var_list s) -> In x (var_list t)) ->
  (forall f, {constructor R f} + {defined R f}) ->
  well_founded (cdp_step R) -> well_founded (C_step R).
Proof.
intros R HR RR CD Wf t; pattern t; apply term_rec3; clear t.
intro x; apply Context_Acc_var; trivial.
intros; apply cdp_criterion_local; trivial.
simpl; intros s As; apply H.
destruct As as [n [_ As]].
revert n As; clear; induction l as [ | t l]; intros [ | n] H.
discriminate.
discriminate.
injection H; intros; left; assumption.
right; apply IHl with n; trivial.
Qed.

(* http://zenon.dsic.upv.es/muterm *)
End Context_sensitive.

End Make.

