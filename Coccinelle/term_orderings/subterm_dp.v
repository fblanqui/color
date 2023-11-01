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
From CoLoR Require Import closure more_list weaved_relation term_spec
     equational_theory_spec dp.
From CoLoR Require Import NatCompat.

(** ** Module Type Termin, for termination of rewriting systems. *)

Module MakeSubDP (E : EqTh).

  Module Dp := dp.MakeDP (E).
  Import Dp.
  Import E.
  Import T.

Section Subterm.

Variable R : relation term.
Variable R_reg : forall s t, R s t -> forall x, In x (var_list s) -> In x (var_list t) .
Variable R_var : forall v t, ~ R t (Var v).
Variable CD : forall f, {constructor R f} + {defined R f}.
Variable R_red : term -> list term.
Variable FB : forall t s, one_step R s t <-> In s (R_red t).
Variable inject : nat -> variable.
Variable inject_inv : variable -> nat.
Variable Hinject1 : forall v, inject (inject_inv v) = v.
Variable Hinject2 : forall n, inject_inv (inject n) = n.

Variable cdp : term -> term -> Prop.
Variable cdp_in_dpR : forall u v, cdp v u -> ddp R v u.


Variable P : F.Symb.A -> nat.
Variable u0 : term.
Variable v0 : term.
Variable u0_diff_v0 : u0 <> v0.
Variable cdp_uv0 : cdp v0 u0.

Variable P_ok : match v0 with 
                      | Var _ => True 
                      | Term f _ => match F.arity f with Free n => P f < n | _ => P f < 2 end
                      end.

Definition projection (t : term) : term :=
  match t with
  | Var _ => t
  | Term f l =>
      match nth_error l (P f)  with
      | Some tf => tf
      | None => t
      end
   end.

Variable  uv0_strict : trans_clos (union _ (one_step R) direct_subterm) (projection v0) (projection u0).

Inductive dp' : term -> term -> Prop := 
  Dp' : forall v u, cdp v u -> (u,v) <> (u0,v0) -> dp' v u.

Inductive dp0 : term -> term -> Prop := 
  Dp0 : dp0 v0 u0.

Definition Rdp' := rdp_step (axiom dp') R.
Definition Rdp0 := rdp_step (axiom dp0) R.
Definition Rcdp := rdp_step (axiom cdp) R.
Definition R1 := compose_rel (refl_trans_clos Rdp') Rdp0.
Definition R1' := compose_rel Rdp0 (refl_trans_clos Rdp').

Lemma subst_projection :
  forall sigma f l, projection (apply_subst sigma (Term f l)) = apply_subst sigma (projection (Term f l)).
Proof.
unfold projection; intros sigma f l; simpl.
generalize (nth_error_map (apply_subst sigma) l (P f)).
case (nth_error (map (apply_subst sigma) l) (P f)).
intros ti_sigma.
case (nth_error l (P f)).
intros ti H; assumption.
contradiction.
case (nth_error l (P f)).
contradiction.
intros; apply eq_refl.
Qed.

Lemma projection_is_subterm : 
   forall t f l,  
   Rdp0 (Term f l) t -> 
   (match F.arity f with
        | AC => length l = 2
        | C => length l = 2
        | Free n => length l = n
   end) -> 
   direct_subterm (projection (Term f l)) (Term f l).
Proof.
intros s f l K L.
inversion K as [g l1 l2 t3 H1 H2]; subst.
inversion H2 as [t1 t2 sigma K1 K2 K3]; subst.
destruct t1 as [x | g1 k1].
inversion K1 as [J1 J2]; clear K K1 H2; subst.
assert (K4 := cdp_in_dpR _ _ cdp_uv0).
destruct K4 as [K4 _]; inversion K4.
inversion K1 as [J1 J2].
rewrite J1 in P_ok; injection K2; clear K2; do 2 intro; subst.
destruct (F.arity f) as [ | | n].

destruct k1 as [ | u1 [ | u2 [ | u3 l]]]; try discriminate.
simpl; destruct (P f) as [ | [ | p]]; simpl.
left; reflexivity.
right; left; reflexivity.
assert (Abs := le_S_n _ _ (le_S_n _ _ P_ok)); inversion Abs.

destruct k1 as [ | u1 [ | u2 [ | u3 l]]]; try discriminate.
simpl; destruct (P f) as [ | [ | p]]; simpl.
left; reflexivity.
right; left; reflexivity.
assert (Abs := le_S_n _ _ (le_S_n _ _ P_ok)); inversion Abs.
rewrite <- L in P_ok; generalize P_ok.
simpl; set (k := map (apply_subst sigma) k1); clearbody k; set (p := P f); clearbody p.
revert p k; fix projection_is_subterm 1.
intro p; case p; clear p.
intro l; case l; clear l.
intro Abs; inversion Abs.
intros t l _; simpl; left; reflexivity.
intros p l; case l; clear l.
intro Abs; inversion Abs.
intros t l LL; simpl; right; generalize (projection_is_subterm p l (proj2 (Nat.succ_lt_mono _ _) LL)).
case (nth_error l p).
intros s s_in_l; exact s_in_l.
intros Abs; apply False_rect; apply (Nat.lt_irrefl (size (Term f l))).
apply size_direct_subterm; assumption.
Qed.

Lemma split_dps :
  forall t1 t2, Rcdp t1 t2 <-> union _ Rdp' Rdp0 t1 t2.
Proof.
intros u1 u2; split; intro H.
inversion H as [f' l1 l2 H1 H2 H']; clear H; subst.
inversion H' as [t1 t2 sigma H'' H3 H''']; clear H'; subst.
generalize (T.eq_bool_ok t2 u0); case (T.eq_bool t2 u0); [intro t2_eq_u0 | intro t2_diff_u0].
generalize (T.eq_bool_ok t1 v0); case (T.eq_bool t1 v0); [intro t1_eq_v0 | intro t1_diff_v0].
subst t1 t2; right.
apply Rdp_step with l2; trivial.
rewrite <- H'''; apply instance; apply Dp0.
left; apply Rdp_step with l2; trivial.
rewrite <- H'''; apply instance; apply Dp'; trivial.
intro H; apply t1_diff_v0; injection H; intros; assumption.
left; apply Rdp_step with l2; trivial.
rewrite <- H'''; apply instance; apply Dp'; trivial.
intro H; apply t2_diff_u0; injection H; intros; assumption.

destruct H as [H | H].
inversion H as [f' l1 l2 H1 H2 H']; clear H; subst.
inversion H' as [t1 t2 sigma H'' H3 H''']; clear H'; subst.
inversion H'' as [v u]; clear H''; subst t1 t2.
apply Rdp_step with l2; trivial.
rewrite <- H'''; apply instance; assumption.
inversion H as [f' l1 l2 H1 H2 H']; clear H; subst.
inversion H' as [t1 t2 sigma H'' H3 H''']; clear H'; subst.
inversion H'' as [v u]; clear H''; subst t1 t2.
apply Rdp_step with l2; trivial.
rewrite <- H'''; apply instance; assumption.
Qed.

Lemma dp0_is_dp : forall t1 t2, Rdp0 t2 t1 -> Rcdp t2 t1.
Proof.
intros t1 t2 H; inversion H; subst.
apply Rdp_step with l2; trivial.
inversion H1; subst.
apply instance.
inversion H4; subst; trivial.
Qed.

Lemma dp'_is_dp : forall t1 t2, Rdp' t2 t1 -> Rcdp t2 t1.
Proof.
intros t1 t2 H; inversion H; subst.
apply Rdp_step with l2; trivial.
inversion H1; subst.
apply instance.
inversion H4; subst; trivial.
Qed.

Definition extract_dp u v s t :=
   cdp v u /\
   exists f, exists l1, exists l2, exists sigma, 
   s = apply_subst sigma v /\
   Term f l2 = apply_subst sigma u /\
   refl_trans_clos (one_step_list (one_step R)) l2 l1 /\
   Term f l1 = t.

Lemma connect_extract_dp_aux :
  forall u1 v1 s1 t1 un vn sn,
  Rcdp s1 t1 ->
  Rcdp sn s1 ->
  extract_dp u1 v1 s1 t1 -> extract_dp un vn sn s1 ->
  are_connected cdp R (un,vn) (u1,v1).
Proof.
intros u1 v1 s1 t1 un vn sn H1 Hn.
unfold extract_dp.
intros [D1 [f [l1 [l2 [sigma [K1 [J1 [L1 E1]]]]]]]] [Dn [g [k1 [k2 [tau [K2 [J2 [L2 E2]]]]]]]].
exists sigma; exists tau; subst; repeat split; trivial.
rewrite <- J2.
rewrite <- E2; split; trivial.
Qed.

Lemma connect_extract_dp :
  forall u1 v1 s1 t1 un vn sn tn,
  Rcdp s1 t1 ->
  refl_trans_clos Rcdp tn s1 ->
  Rcdp sn tn ->
  extract_dp u1 v1 s1 t1 -> extract_dp un vn sn tn ->
  trans_clos (are_connected cdp R) (un,vn) (u1,v1).
Proof.
intros u1 v1 s1 t1 un vn sn tn H1 H; revert u1 v1 t1 un vn sn H1.
inversion H as [u | tn' s1' H']; clear H.
subst u tn.
intros u1 v1 t1 un vn sn H1 Hn E1 En;
left; apply connect_extract_dp_aux with s1 t1 sn; trivial.
subst s1' tn'.
induction H' as [tn s1 H | tn t s1 H1 H2].
assert (H_save := H).
inversion H as [f l1 l2 tn' H21 H'].
inversion H' as [v2 u2 sigma2].
intros u1 v1 t1 un vn sn Dp1 Dpn E1 En.
assert (E2 : extract_dp u2 v2 tn (Term f l1)).
split.
trivial.
exists f; exists l1; exists l2; exists sigma2; repeat split; trivial.
apply sym_eq; assumption.
apply sym_eq; assumption.
rewrite H3 in En, Dpn.
rewrite H1 in E1, Dp1.
apply trans_clos_is_trans with (u2,v2); left.
subst; refine (connect_extract_dp_aux _ _ _ _ _ _ _ _ _ E2 En); trivial.
subst; refine (connect_extract_dp_aux _ _ _ _ _ _ _ _ _ E1 E2); trivial.
intros u1 v1 t1 un vn sn Dp1 Dpn E1 En.
assert (H1_save := H1).
inversion H1 as [f l1 l2 tn' K1 K2]; subst tn' t.
inversion K2 as [v u sigma].
assert (E : extract_dp u v tn (Term f l1)).
split; trivial.
exists f; exists l1; exists l2; exists sigma; repeat split; trivial.
apply sym_eq; assumption.
apply sym_eq; assumption.
apply trans_clos_is_trans with (u,v).
left; refine (connect_extract_dp_aux _ _ _ _ _ _ _ _ _ E En); trivial.
apply (IHH2 u1 v1 t1 u v tn Dp1 H1_save E1 E).
Qed.

(*
Variable connect_approx : relation (term * term).
Variable approx_dec : forall uv uv', {connect_approx uv uv'}+{~connect_approx uv uv'}.
Variable approx_is_approx : forall uv uv', ~connect_approx uv uv' -> ~ trans_clos (are_connected cdp R) uv uv'.
*)
Variable comp : term * term -> nat.
Variable comp_ok : 
  forall uv uv', are_connected cdp R uv uv' -> comp uv <= comp uv'.
Definition connect_approx uv uv' := comp uv <= comp uv'.

Lemma approx_dec: forall uv uv', {connect_approx uv uv'}+{~connect_approx uv uv'}.
Proof.
intros uv uv'; unfold connect_approx.
destruct (le_lt_dec (comp uv) (comp uv')).
left; exact l.
right; apply Nat.lt_nge; assumption.
Defined.

Lemma approx_is_approx : forall uv uv', ~connect_approx uv uv' -> ~ trans_clos (are_connected cdp R) uv uv'.
Proof.
unfold connect_approx; intros u v H.
intro H'; apply H; clear H.
induction H' as [x y H1 | x y z H1 Hn].
apply comp_ok; assumption.
apply Nat.le_trans with (comp y).
apply comp_ok; assumption.
assumption.
Qed.

Lemma between_dp0_aux1 :
  forall t1 t2 t3 t4 t5 t6,  
  Rdp0 t2 t1 ->
  refl_trans_clos Rdp' t3 t2 ->
  rdp_step (axiom dp') R t4 t3 ->
  refl_trans_clos Rdp' t5 t4 ->
  Rdp0 t6 t5 -> 
  forall u v, extract_dp u v t4 t3 -> 
      refl_trans_clos (are_connected cdp R) (u0,v0) (u,v) /\ 
      refl_trans_clos (are_connected cdp R) (u,v) (u0,v0). 
Proof.
intros t1 t2 t3 t4 t5 t6 H21 H32 H43 H54 H65 u v E.
assert (E1 : extract_dp u0 v0 t2 t1).
split; trivial.
inversion H21 as [f l1 l2 v1 Hl21 Hdp2]; subst.
inversion Hdp2 as [v2 u2 sigma2 Hdp2' K2 J2]; clear Hdp2.
inversion Hdp2'; subst v2 u2.
exists f; exists l1; exists l2; exists sigma2; repeat split; trivial.
apply sym_eq; assumption.
assert (E6 : extract_dp u0 v0 t6 t5).
split; trivial.
inversion H65 as [f l1 l2 v1 Hl21 Hdp2]; subst.
inversion Hdp2 as [v2 u2 sigma2 Hdp2' K2 J2]; clear Hdp2.
inversion Hdp2'; subst v2 u2.
exists f; exists l1; exists l2; exists sigma2; repeat split; trivial.
apply sym_eq; assumption.

split.
right; apply (connect_extract_dp u v t4 t3 u0 v0 t6 t5); trivial.
apply dp'_is_dp; trivial.
apply refl_trans_incl with (rdp_step (axiom dp') R); trivial.
intros u1 u2 H; apply dp'_is_dp; trivial.
apply dp0_is_dp; trivial.
right; apply (connect_extract_dp u0 v0 t2 t1 u v t4 t3); trivial.
apply dp0_is_dp; trivial.
apply refl_trans_incl with (rdp_step (axiom dp') R); trivial.
intros u1 u2 H; apply dp'_is_dp; trivial.
apply dp'_is_dp; trivial.
Qed.

Lemma projection_one_step_list :
forall f l1 l2, refl_trans_clos (one_step_list (one_step R)) l2 l1 ->
                   refl_trans_clos (one_step R) (projection (Term f l2)) (projection (Term f l1)).
Proof.
intros h l3 l4 H; simpl.
generalize (nth_error_ok_in (P h) l4).
case_eq (nth_error l4 (P h)).
intros s4 H4 K; destruct (K _ (eq_refl _)) as [l41 [l42 [L4 H4']]]; clear K H4.
generalize (nth_error_ok_in (P h) l3).
case_eq (nth_error l3 (P h)).
intros s3 H3 K; destruct (K _ (eq_refl _)) as [l31 [l32 [L3 H3']]]; clear K H3.
rewrite <- L4 in L3.
subst l3 l4.
apply (refl_trans_clos_one_step_list_refl_trans_clos_one_step _ _ _ _ _ _ (sym_eq L3) H).
intros H3 _.
absurd (length l41 < length l41).
apply Nat.lt_irrefl.
assert (L : length l4 = length l3).
inversion H.
trivial.
apply rwr_list_length_eq with (one_step R); assumption.
assert (L' := nth_error_none _ _ H3).
rewrite <- L4 in L'; rewrite <- L in L'; subst l4. 
apply Nat.lt_le_trans with (length (l41 ++ s4 :: l42)); trivial.
rewrite length_app; rewrite Nat.add_comm; simpl.
apply le_n_S; apply NatCompat.le_add_l.
intros H4 _.
generalize (nth_error_ok_in (P h) l3).
case_eq (nth_error l3 (P h)).
intros s3 H3 K; destruct (K _ (eq_refl _)) as [l31 [l32 [L3 H3']]]; clear K H3.
absurd (length l31 < length l31).
apply Nat.lt_irrefl.
assert (L : length l4 = length l3).
inversion H.
trivial.
apply rwr_list_length_eq with (one_step R); assumption.
assert (L' := nth_error_none _ _ H4).
rewrite <- L3 in L'; rewrite L in L'; subst l3. 
apply Nat.lt_le_trans with (length (l31 ++ s3 :: l32)); trivial.
rewrite length_app; rewrite Nat.add_comm; simpl.
apply le_n_S; apply NatCompat.le_add_l.
intros H3 _.
inversion H.
left.
right.
apply general_context; assumption.
Qed.

Lemma between_dp0_aux2 :
  (forall u v, cdp v u -> connect_approx (u0,v0) (u,v) -> connect_approx (u,v) (u0,v0) ->
  refl_trans_clos (union _ (one_step R) direct_subterm) (projection v) (projection u)) ->
  forall t1 t2 t3 t4 t5 t6,  
  Rdp0 t2 t1 ->
  refl_trans_clos Rdp' t3 t2 ->
  Rdp' t4 t3 ->
  refl_trans_clos Rdp' t5 t4 ->
  Rdp0 t6 t5 -> 
  refl_trans_clos (union _ (one_step R) direct_subterm) (projection t4) (projection t3).
Proof.
intros Hdp t1 t2 t3 t4 t5 t6 H21 H32 H43 H54 H65.
inversion H43 as [h l3 l4 v3 Hl43 Hdp4]; subst.
inversion Hdp4 as [v4 u4 sigma4 Hdp4' K4 J4]; clear Hdp4.
inversion Hdp4' as [v4' u4' Hdp4'']; subst u4' v4'.
assert (E4 : extract_dp u4 v4 t4 (Term h l3)).
unfold extract_dp; split; trivial.
exists h; exists l3; exists l4; exists sigma4; repeat split; trivial.
apply sym_eq; assumption.
apply sym_eq; assumption.
destruct (between_dp0_aux1 t1 t2 (Term h l3) t4 t5 t6 H21 H32 H43 H54 H65 _ _ E4) as [K1 K2].
apply refl_trans_clos_is_trans with (projection (Term h l4)).
rewrite <- J4.
assert (Hdp4''' := cdp_in_dpR _ _ Hdp4'').
destruct Hdp4''' as [Hdp4''' Sub4].
inversion Hdp4''' as [u4' r4 p4 g4 k4 R4 Sub4' D4]; subst.
destruct u4 as [x4 | f4 ll4].
apply False_rect; apply (R_var _ _ R4).
do 2 rewrite subst_projection.
apply one_step_subterm_subst.
clear Hdp4' H65 H54 H32 H43 H21.
inversion K1 as [[u v] | uv0 uv4 K1'].
subst u v u0 v0.
right; assumption.
subst uv0 uv4.
inversion K2 as [[u v] | uv4 uv0 K2'].
subst u v u0 v0.
right; assumption.
subst uv0 uv4.
apply Hdp.
assumption.
destruct (approx_dec (u0, v0) (Term f4 ll4, Term g4 k4)) as [C4 | notC4].
assumption.
apply False_rect; apply (approx_is_approx _ _ notC4 K1').
destruct (approx_dec (Term f4 ll4, Term g4 k4) (u0, v0)) as [C4 | notC4].
assumption.
apply False_rect; apply (approx_is_approx _ _ notC4 K2').
apply refl_trans_incl with (one_step R).
intros u1 u2 K; left; assumption.
apply projection_one_step_list; trivial.
Qed.

Lemma between_dp0_aux3 :
  (forall u v, cdp v u -> connect_approx (u0,v0) (u,v) -> connect_approx (u,v) (u0,v0) ->
  refl_trans_clos (union _ (one_step R) direct_subterm) (projection v) (projection u)) ->
  forall t1 t2 t3 t4 t5 t6,  
  Rdp0 t2 t1 ->
  refl_trans_clos Rdp' t3 t2 ->
  refl_trans_clos Rdp' t4 t3 ->
  refl_trans_clos Rdp' t5 t4 ->
  Rdp0 t6 t5 -> 
  refl_trans_clos (union _ (one_step R) direct_subterm) (projection t4) (projection t3).
Proof.
intros Hdp t1 t2 t3 t4 t5 t6 H21 H32 H43.
inversion H43 as [u | u4 u3 H43']; clear H43.
intros _ _; left.
subst u3 u4; revert t1 t2 t5 t6 H21 H32; 
induction H43' as [t4 t3 H43 | t4 t t3 H4 H3]; intros t1 t2 t5 t6 H21 H32 H54 H65.
apply between_dp0_aux2 with t1 t2 t5 t6; trivial.
apply refl_trans_clos_is_trans with (projection t).
apply between_dp0_aux2 with t1 t2 t5 t6; trivial.
apply refl_trans_clos_is_trans with t3; trivial.
right; assumption.
apply IHH3 with t1 t2 t5 t6; trivial.
apply refl_trans_clos_is_trans with t4; trivial.
right; left; assumption.
Qed.

Lemma between_dp0 :
  (forall u v, cdp v u -> connect_approx (u0,v0) (u,v) -> connect_approx (u,v) (u0,v0) ->
  refl_trans_clos (union _ (one_step R) direct_subterm) (projection v) (projection u)) ->
  forall t1 t2 t3 t4,  
  Rdp0 t2 t1 ->
  refl_trans_clos Rdp' t3 t2 ->
  Rdp0 t4 t3 -> 
  refl_trans_clos (union _ (one_step R) direct_subterm) (projection t3) (projection t2).
Proof.
intros Hdp t1 t2 t3 t4 H21 H32 H43; apply between_dp0_aux3 with t1 t2 t3 t4; trivial.
left.
left.
Qed.

Lemma dp0_decreases :
   forall t1 t2, Rdp0 t2 t1 ->
  trans_clos (union _ (one_step R) direct_subterm) (projection t2) (projection t1).
Proof.
intros t1 t2 H21.
inversion H21 as [f l1 l2 v1 Hl21 Hdp2]; subst.
inversion Hdp2 as [v2 u2 sigma2 Hdp2' K2 J2]; clear Hdp2.
inversion Hdp2'; subst v2 u2.
assert (dp_uv0 := cdp_in_dpR _ _ cdp_uv0).
destruct dp_uv0 as [dp_uv0 H2].
inversion dp_uv0 as [u0' r0 p0 g0 k0 H1 H3]; clear Hdp2' H21; subst.
destruct u0 as [x0 | f0 l0].
apply False_rect; apply (R_var _ _ H1).
assert (Sub := projection_one_step_list f _ _ Hl21).
assert (Sub' : trans_clos (union term (one_step R) direct_subterm)
  (projection (apply_subst sigma2 (Term g0 k0))) (projection (Term f l2))).
rewrite <- J2.
do 2 rewrite subst_projection.
revert uv0_strict; apply trans_incl2.
intros a1 a2 [Sub'' | Sub''].
left; apply one_step_apply_subst; assumption.
right; destruct a2 as [x2 | g2 k2].
contradiction.
simpl; rewrite in_map_iff; exists a1; split; trivial.
inversion Sub as [u H0 H5 | u1 u2 K1 K2].
subst u; simpl; rewrite <- H5; assumption.
subst u1 u2; apply trans_clos_is_trans with (projection (Term f l2)); trivial.
apply trans_incl with (one_step R); trivial.
intros u1 u2 K; left; trivial.
Qed.

Lemma sub_projection : 
 (forall u v, cdp v u -> connect_approx (u0,v0) (u,v) -> connect_approx (u,v) (u0,v0) ->
  refl_trans_clos (union _ (one_step R) direct_subterm) (projection v) (projection u)) ->
   forall t1 t2 t3, R1 t3 t2 -> R1 t2 t1 ->
      trans_clos (union term (one_step R) direct_subterm) (projection t2) (projection t1).
Proof.
intros Hdp t1 t3 t5 H53 H31.
inversion H31 as [t3' t2 t1' H32 H21]; subst t1' t3'.
inversion H53 as [t5' t4 t3' H54 H43]; subst t3' t5'.
assert (B21 := dp0_decreases _ _ H21).
assert (B32 := between_dp0 Hdp t1 t2 t3 t4 H21 H32 H43).
inversion B32 as [t | t4' t3' B32'].
rewrite H0; assumption.
apply trans_clos_is_trans with (projection t2); assumption.
Qed.

Lemma acc_R_acc_dp :
forall t, Acc (one_step R) t -> Acc Rcdp t.
Proof.
intros t Acc_t.
apply Acc_incl with (rdp_step (axiom (ddp R)) R).
intros t1 t2 K; inversion K; clear K; subst.
apply Rdp_step with l2; trivial.
inversion H0; clear H0; subst; apply instance; apply cdp_in_dpR; trivial.
apply acc_one_step_acc_ddp; trivial.
Qed.

Lemma acc_R_acc_dp_sub :
forall t, Acc (one_step R) t -> Acc (union _ Rcdp (trans_clos direct_subterm)) t.
Proof.
intros t Acc_t; apply Acc_incl with (trans_clos (union _ (one_step R) direct_subterm)).
clear t Acc_t; intros s t [H1 | H2].
inversion H1; clear H1; subst.
inversion H0; clear H0; subst.
assert (H4 := cdp_in_dpR _ _ H3); clear H3.
destruct H4 as [H4 Sub].
inversion H4; clear H4; subst.
destruct (subterm_subterm _ _ H2) as [H4 | H4]; subst; inversion H; clear H; subst.
do 3 left; rewrite <- H1; apply instance; assumption.
apply trans_clos_is_trans with (Term f l2).
apply trans_incl with (one_step R).
do 3 intro; left; assumption.
do 2 left; rewrite <- H1; apply instance; assumption.
apply trans_incl with (one_step R).
do 3 intro; left; assumption.
apply general_context; assumption.
apply trans_clos_is_trans with (apply_subst sigma t3).
apply trans_incl with direct_subterm.
do 3 intro; right; assumption.
apply instantiated_subterm; assumption.
do 3 left; rewrite <- H1; apply instance; assumption.
apply trans_clos_is_trans with (apply_subst sigma t3).
apply trans_incl with direct_subterm.
do 3 intro; right; assumption.
apply instantiated_subterm; assumption.
apply trans_clos_is_trans with (Term f l2).
do 3 left; rewrite <- H1; apply instance; assumption.
apply trans_incl with (one_step R).
do 3 intro; left; assumption.
apply general_context; assumption.
apply trans_incl with direct_subterm; trivial.
do 3 intro; right; assumption.
apply acc_trans; rewrite <- acc_with_subterm; assumption.
Qed.

Definition Rcdp_min := rest (acc_sub R) Rcdp.
Definition Rdp_min' := rest (acc_sub R) Rdp'.
Definition Rdp0_min := rest (acc_sub R) Rdp0.

Lemma dp_subterm_criterion: 
   (match v0 with 
      | Var _  => True
      | Term f l =>
        match F.arity f with
        | AC => length l = 2
        | C => length l = 2
        | Free n => length l = n
        end
   end) -> 
  (forall u v, cdp v u -> connect_approx (u0,v0) (u,v) -> connect_approx (u,v) (u0,v0) ->
  refl_trans_clos (union _ (one_step R) direct_subterm) (projection v) (projection u)) ->
  well_founded Rdp_min' -> well_founded Rcdp_min.
Proof.
intros L Hdp W' t; apply (well_founded_ind W'); clear t.
intros t IH; apply Acc_intro; intros s [H [Ms Mt]].
rewrite split_dps in H; destruct H as [H | H].
apply IH.
split; [ | split ]; assumption.
apply Acc_incl with (union _ Rdp_min' Rdp0_min).
do 2 intro; intros [K [MW1 MW2]]; rewrite split_dps in K; destruct K as [K | K]; [left | right]; split; trivial.
split; assumption.
split; assumption.
apply acc_union_weak.
apply acc_inv_im2 with term (trans_clos (union term (one_step R) direct_subterm)) projection.
intros a1 a2 a3 H32 H21 H10.
assert (B := between_dp0 Hdp).
(*  a2  <- DP0 DP'* - a2 <- DP0 DP'* - a1<- (DP0 DP'* )* - g1h1sig1 <- DP0 f1k1sig1 *)
assert (H0 : exists a0, Rdp0 a1 a0).
inversion H10 as [a | a1' b1 K10]; clear H10; subst.
exists t; assumption.
inversion K10 as [a1' b1' H10 | a1' b1 c1' J10 K0]; clear K10.
subst a1' b1'.
inversion H10 as [a1' b1 c1' K1 K10]; clear H10.
subst a1' c1'.
exists b1; destruct K1; assumption.
subst a1' c1'.
inversion J10 as [a1' b1' c1 J1 J0]; clear J10.
subst a1' c1.
exists b1'; destruct J1; assumption.
destruct H0 as [a0 H0].
inversion H21 as [a2' b2 c2' K2 K1]; clear H21.
subst a2' c2'.
assert (K1' : refl_trans_clos Rdp' b2 a1).
apply refl_trans_incl with Rdp_min'; trivial.
do 2 intro; intros [K _]; assumption.
assert (K2' := proj1 K2).
assert (B' := B _ _ _ _ H0 K1' K2').
inversion B' as [p J1 J2 | pb2 pa1 B''].
apply dp0_decreases; assumption.
subst pb2 pa1.
apply trans_clos_is_trans with (projection b2); trivial.
apply dp0_decreases; assumption.
apply acc_trans; rewrite <- acc_with_subterm.
destruct s as [v | f l].
simpl; apply Acc_var; trivial.
apply Ms; apply (projection_is_subterm t).
assumption.
inversion H as [g l1 l2 t3 H1 H2]; clear H; subst.
inversion H2 as [t1 t2 sigma]; clear H2; subst.
inversion H; clear H; subst t1 t2.
assert (H4 := cdp_in_dpR _ _ cdp_uv0).
destruct H4 as [H4 _].
inversion H4; clear IH W'; subst.
injection H0; intros; subst f2 l; rewrite length_map.
assumption.
intros b _; apply W'.
Qed.

End Subterm.

Lemma dp_subterm_criterion_gen :
      forall R : relation term,
       (forall (v : variable) (t : term), ~ R t (Var v)) ->
       forall (l0 : list (term * term))
       (cdp cdp': term -> term -> Prop),
       (forall u v : term, cdp v u -> ddp R v u) ->
       forall (P : symbol -> nat),
       (forall u v, cdp v u <-> (cdp' v u \/ In (u,v) l0)) ->
       (forall u0 v0, In (u0,v0) l0 -> u0 <> v0) ->
       (forall u0 v0, In (u0,v0) l0 -> match v0 with
       | Var _ => True
       | Term f _ =>
           match F.arity f with
           | AC => P f < 2
           | C => P f < 2
           | Free n => P f < n
           end
       end) ->
       (forall u0 v0, In (u0,v0) l0 -> trans_clos (union term (one_step R) direct_subterm) (projection P v0)
         (projection P u0)) ->
       forall comp : term * term -> nat,
       (forall uv uv' : term * term,
        are_connected cdp R uv uv' -> comp uv <= comp uv') ->
       forall n0, (forall uv0, In uv0 l0 -> comp uv0 = n0) ->
       (forall u0 v0, In (u0,v0) l0 -> match v0 with
       | Var _ => True
       | Term f l =>
           match F.arity f with
           | AC => length l = 2
           | C => length l = 2
           | Free n => length l = n
           end
       end) ->
       (forall u v : term, cdp v u -> comp (u,v) = n0 ->
        refl_trans_clos (union term (one_step R) direct_subterm)
          (projection P v) (projection P u)) ->
       well_founded (rest (acc_sub R) (rdp_step (axiom cdp') R)) -> 
       well_founded (rest (acc_sub R) (rdp_step (axiom cdp) R)).
Proof.
intros R R_var l0; induction l0 as [ | [u0 v0] l0];
intros cdp cdp' cdp_in_dpR P split_cdp l0_diff P_ok l0_decr
comp comp_ok n0 l0_in_comp_n0 Wl0 cdp_decr W'.

apply wf_incl with (rest (acc_sub R) (rdp_step (axiom cdp') R)); [ | assumption].
intros x y [H Hmin]; split; [ | assumption].
inversion H as [f l1 l2 t3 H1 H2]; clear H; subst.
constructor 1 with l2.
assumption.
inversion H2 as [t1 t2 sigma H3 H4]; clear H2; subst.
constructor 1.
rewrite split_cdp in H3; destruct H3 as [H3 | H3]; [assumption | contradiction].

apply (dp_subterm_criterion R R_var _ cdp_in_dpR P u0 v0) with comp.
apply l0_diff; left; apply eq_refl.
rewrite split_cdp; right; left; apply eq_refl.
apply P_ok with u0; left; apply eq_refl.
apply l0_decr; left; apply eq_refl.
assumption.
apply Wl0 with u0; left; apply eq_refl.
unfold connect_approx; intros u v H0 H1 H2; apply cdp_decr.
assumption.
rewrite <- (l0_in_comp_n0 _ (or_introl _ (eq_refl _))).
apply Nat.le_antisymm; assumption.

apply wf_incl with (rest (acc_sub R) (rdp_step (axiom (fun v u => cdp' v u \/ In (u, v) l0)) R)).
intros x y [H Hmin]; split; [ | assumption].
inversion H as [f l1 l2 t3 H1 H2]; clear H; subst.
constructor 1 with l2.
assumption.
inversion H2 as [t1 t2 sigma H3 H4]; clear H2; subst.
constructor 1.
inversion H3 as [u v K1 K2]; clear H3; subst.
rewrite split_cdp in K1; simpl in K1; destruct K1 as [K1 | [K1 | K1]].
left; assumption.
apply False_rect; apply K2; apply sym_eq; assumption.
right; assumption.

apply IHl0 with cdp' P comp n0.
intros u v [H | H]; apply cdp_in_dpR; rewrite split_cdp; [left | do 2 right]; assumption.
intros u v; split; intro H; assumption.
intros; apply l0_diff; right; assumption.
intros u1 v1 uv1_in_l0; apply P_ok with u1; right; assumption.
intros u1 v1 uv1_in_l0; apply l0_decr; right; assumption.
intros [u v] [u' v'] H; apply comp_ok.
destruct H as [sigma [sigma' [H1 [H2 H3]]]].
exists sigma; exists sigma'; split; [ | split].
rewrite split_cdp; destruct H1 as [H1 | H1]; [left | do 2 right]; assumption.
rewrite split_cdp; destruct H2 as [H2 | H2]; [left | do 2 right]; assumption.
assumption.
intros; apply l0_in_comp_n0; right; assumption.
intros u1 v1 uv1_in_l0; apply Wl0 with u1; right; assumption.
intros u v [H1 | H2]; apply cdp_decr; rewrite split_cdp; [left | do 2 right]; assumption.
assumption.
Qed.

Lemma dp_subterm_criterion_one_comp :
      forall R : relation term,
       (forall (v : variable) (t : term), ~ R t (Var v)) ->
       forall (l0 : list (term * term))
       (cdp cdp' : term -> term -> Prop),
       (forall u v : term, cdp v u -> ddp R v u) ->
       forall (P : symbol -> nat),
       (forall u v, cdp v u <-> (cdp' v u \/ In (u,v) l0)) ->
       (forall u0 v0, In (u0,v0) l0 -> u0 <> v0) ->
       (forall u0 v0, In (u0,v0) l0 -> match v0 with
       | Var _ => True
       | Term f _ =>
           match F.arity f with
           | AC => P f < 2
           | C => P f < 2
           | Free n => P f < n
           end
       end) ->
       (forall u0 v0, In (u0,v0) l0 -> 
           trans_clos (union term (one_step R) direct_subterm) (projection P v0) (projection P u0)) ->
       (forall u0 v0, In (u0,v0) l0 -> match v0 with
       | Var _ => True
       | Term f l =>
           match F.arity f with
           | AC => length l = 2
           | C => length l = 2
           | Free n => length l = n
           end
       end) ->
       (forall u v : term, cdp v u  ->
         refl_trans_clos (union term (one_step R) direct_subterm) (projection P v) (projection P u)) ->
       well_founded (rest (acc_sub R) (rdp_step (axiom cdp') R)) ->
       well_founded (rest (acc_sub R) (rdp_step (axiom cdp) R)).
Proof.
intros R R_var l0; induction l0 as [ | [u0 v0] l0];
intros cdp cdp' cdp_in_dpR P split_cdp l0_diff P_ok l0_decr Wl0 cdp_decr W'.

apply wf_incl with (rest (acc_sub R) (rdp_step (axiom cdp') R)); [ | assumption].
intros x y [H Hmin]; split; [ | assumption].
inversion H as [f l1 l2 t3 H1 H2]; clear H; subst.
constructor 1 with l2.
assumption.
inversion H2 as [t1 t2 sigma H3 H4]; clear H2; subst.
constructor 1.
rewrite split_cdp in H3; destruct H3 as [H3 | H3]; [assumption | contradiction].

apply (dp_subterm_criterion R R_var _ cdp_in_dpR P u0 v0) with (fun _ => 0).
apply l0_diff; left; apply eq_refl.
rewrite split_cdp; right; left; apply eq_refl.
apply P_ok with u0; left; apply eq_refl.
apply l0_decr; left; apply eq_refl.
intros; apply le_n.
apply Wl0 with u0; left; apply eq_refl.
unfold connect_approx.
 intros u v H1 _ _; apply cdp_decr; assumption.

apply wf_incl with (rest (acc_sub R) (rdp_step (axiom (fun v u => cdp' v u \/ In (u, v) l0)) R)).
intros x y [H Hmin]; split; [ | assumption].
inversion H as [f l1 l2 t3 H1 H2]; clear H; subst.
constructor 1 with l2.
assumption.
inversion H2 as [t1 t2 sigma H3 H4]; clear H2; subst.
constructor 1.
inversion H3 as [u v K1 K2]; clear H3; subst.
rewrite split_cdp in K1; simpl in K1; destruct K1 as [K1 | [K1 | K1]].
left; assumption.
apply False_rect; apply K2; apply sym_eq; assumption.
right; assumption.

apply IHl0 with cdp' P.
intros u v [H | H]; apply cdp_in_dpR; rewrite split_cdp; [left | do 2 right]; assumption.
intros u v; split; intro H; assumption.
intros; apply l0_diff; right; assumption.
intros u1 v1 uv1_in_l0; apply P_ok with u1; right; assumption.
intros u1 v1 uv1_in_l0; apply l0_decr; right; assumption.
intros u1 v1 uv1_in_l0; apply Wl0 with u1; right; assumption.
intros u v [H1 | H2]; apply cdp_decr; rewrite split_cdp; [left | do 2 right]; assumption.
assumption.
Qed.

End MakeSubDP.
