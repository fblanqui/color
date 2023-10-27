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

(** * Unit Equational theory on a term algebra *)


From Coq Require Import Arith List Relations.
From CoLoR Require Import closure more_list weaved_relation list_sort term_spec
     equational_theory ac cf_eq_ac rpo.

(** ** Module Type EqTh, an equational theory over a term algebra. *)

Module Type ACU.

Declare Module F : Signature.
Import F.

Inductive unit_theory_type : Type :=
  | LU : Symb.A -> unit_theory_type
  | RU : Symb.A -> unit_theory_type
  | U : Symb.A -> unit_theory_type
  | Nothing : unit_theory_type.

Definition is_coherent (unit_theory : Symb.A -> unit_theory_type) :=
  forall f, 
   match unit_theory f with
   | LU u => arity f = Free 2 /\ arity u = Free 0
   | RU u => arity f = Free 2 /\ arity u = Free 0
   | U u => (arity f = Free 2 \/ arity f = C \/ arity f = AC) /\ (arity u = Free 0)
   | Nothing => True
   end.

Parameter unit_theory : Symb.A -> unit_theory_type.
Parameter unit_theory_is_coherent : is_coherent unit_theory.

End ACU.

(* Set Implicit Arguments. *)

Module Make (Cf_eq_ac1 : cf_eq_ac.S) 
                     (Acu1 : ACU with Module F:=Cf_eq_ac1.Ac.EqTh.T.F). 

Module Cf_eq_ac := Cf_eq_ac1.
Import Cf_eq_ac1.
Import Ac.
Import EqTh.
Import Acu1.
Import T.
Import F.
Import X.
Import Sort.
Import LPermut.

Inductive unit_one_step_at_top : term -> term -> Prop :=
  | left_unit : forall t f u, (unit_theory f = LU u \/ unit_theory f = U u) -> 
            unit_one_step_at_top (Term f ((Term u nil) :: t :: nil)) t
  | right_unit : forall t f u, (unit_theory f = RU u \/ unit_theory f = U u) -> 
            unit_one_step_at_top (Term f (t :: (Term u nil) :: nil)) t.

Definition unit_th := th_eq unit_one_step_at_top.
Definition acu := th_eq (union term ac_one_step_at_top unit_one_step_at_top).

Lemma no_need_of_instance :
  forall t1 t2, axiom (sym_refl unit_one_step_at_top) t1 t2 -> 
                     (sym_refl unit_one_step_at_top) t1 t2.
Proof.
unfold sym_refl; intros t1 t2 H. 
inversion_clear H as [ u1 u2 sigma H'].
destruct H' as [H' | [H' | H']]; inversion_clear H'; simpl.
left; apply left_unit; trivial.
left; apply right_unit; trivial.
right; left; apply left_unit; trivial.
right; left; apply right_unit; trivial.
right; right; trivial.
Qed.

Fixpoint unit_nf (t : term) : term :=
  match t with
  | Var _ => t
  | Term f nil => Term f nil
  | Term f (t1 :: nil) => Term f ((unit_nf t1) :: nil) 
  | Term f (t1 :: t2 :: nil) => 
     match unit_theory f with
     | LU u => let ut1 := unit_nf t1 in
        if T.eq_bool ut1 (Term u nil)
        then unit_nf t2
        else Term f (ut1 :: (unit_nf t2) :: nil)
     | RU u => let ut2 := unit_nf t2 in
            if T.eq_bool ut2 (Term u nil)
            then unit_nf t1
            else Term f ((unit_nf t1) :: ut2 :: nil)
    | U u => let ut1 := unit_nf t1 in 
                   let ut2 := unit_nf t2 in
                   if T.eq_bool ut1 (Term u nil)
                   then ut2
                   else if T.eq_bool ut2 (Term u nil)
                   then ut1
                   else Term f (ut1 :: ut2 :: nil)
    | Nothing => Term f ((unit_nf t1) :: (unit_nf t2) :: nil)
     end
  | Term f l => Term f (map unit_nf l)
end.

Lemma ac_const : forall c t, ac (Term c nil) t -> t = Term c nil.
Proof.
intros c [ v | f [ | t l]] H; generalize (ac_top_eq H).
contradiction.
intros; subst; trivial.
intros _; assert (S := ac_size_eq H); 
simpl in S; injection S; clear S; intro S;
absurd (1 <= 0).
auto with arith.
pattern 0 at 2; rewrite S; apply Nat.le_trans with (size t).
apply size_ge_one.
auto with arith.
Qed.

Lemma unit_nf_nothing :
  forall f, (unit_theory f = Nothing) ->
  forall l, unit_nf (Term f l) = Term f (map unit_nf l).
Proof.
intros f UT [ | t1 [ | t2 [ | t3 l]]].
trivial.
simpl; destruct (unit_nf t1) as [ v1 | f1 [ | s1 l1]]; trivial.
simpl; destruct (unit_nf t1) as [ v1 | f1 [ | s1 l1]];
destruct (unit_nf t2) as [ v2 | f2 [ | s2 l2]]; trivial; repeat rewrite UT; trivial.
simpl; destruct (unit_nf t1) as [ v1 | f1 [ | s1 l1]];
destruct (unit_nf t2) as [ v2 | f2 [ | s2 l2]]; trivial.
Qed.

Lemma well_formed_unit_nf : forall t, well_formed t -> well_formed (unit_nf t).
Proof.
unfold well_formed; intro t; pattern t; apply term_rec3; clear t.
intros v _; simpl; trivial.
intros f l IHl Wt; generalize (well_formed_unfold Wt); clear Wt; 
intros [Wl Ar]; unfold well_formed in Wl.
assert (Wl' : forall u, In u (map unit_nf l) -> well_formed_bool u = true).
clear Ar; induction l as [ | t l].
contradiction.
intros u [u_eq | In_u].
subst; apply IHl; [idtac | apply Wl]; left; trivial.
apply IHl0; trivial; intros; [ apply IHl; trivial | apply Wl]; right; trivial.
simpl; generalize (length_map unit_nf l); intro L; rewrite <- L in Ar; clear L.
destruct l as [ | t1 [ | t2 [ | t3 l ]]]; simpl in Ar; simpl in Wl'.
simpl; destruct (arity f) as [ | | [ | n]]; try (discriminate || trivial).
simpl; destruct (arity f) as [ | | [ | n]]; try (discriminate || trivial).
injection Ar; intro; subst; rewrite Wl'; [reflexivity | left; reflexivity].
destruct (unit_theory f) as [ u | u | u | ].
generalize (T.eq_bool_ok  (unit_nf t1) (Term u nil)); case (T.eq_bool (unit_nf t1) (Term u nil)); [intro t1_eq_u | intro t1_diff_u].
apply Wl'; right; left; trivial.
apply well_formed_fold; intuition.
generalize (T.eq_bool_ok (unit_nf t2) (Term u nil)); case (T.eq_bool (unit_nf t2) (Term u nil)); [intro t2_eq_u | intro t2_diff_u].
apply Wl'; left; trivial.
apply well_formed_fold; intuition.
generalize (T.eq_bool_ok (unit_nf t1) (Term u nil)); case (T.eq_bool (unit_nf t1) (Term u nil)); [intro t1_eq_u | intro t1_diff_u].
apply Wl'; right; left; trivial.
generalize (T.eq_bool_ok  (unit_nf t2) (Term u nil)); case (T.eq_bool (unit_nf t2) (Term u nil)); [intro t2_eq_u | intro t2_diff_u].
apply Wl'; left; trivial.
apply well_formed_fold; intuition.
apply well_formed_fold; intuition.
rewrite length_map in Ar; simpl.
destruct (arity f) as [ | | n]; try discriminate.
subst n; rewrite length_map.
rewrite Nat.eqb_refl; rewrite Bool.andb_true_r.
rewrite (IHl t1); simpl.
rewrite (IHl t2); simpl.
rewrite (IHl t3); simpl.
assert (Wl'' : forall u : term, In u (map unit_nf l) -> well_formed u).
intros; apply Wl'; right; right; right; trivial.
clear t1 t2 t3 IHl Wl Wl'; revert l Wl''.
intro l; induction l as [ | t l]; simpl.
trivial. 
intro H; rewrite H.
rewrite IHl; trivial.
intros; apply H; right; trivial.
left; trivial.
do 2 right; left; trivial.
apply Wl; do 2 right; left; trivial.
right; left; trivial.
apply Wl; right; left; trivial.
left; trivial.
apply Wl; left; trivial.
Qed.

Lemma  unit_nf_is_sound : forall t, unit_th t (unit_nf t).
Proof.
unfold unit_th; intro t; pattern t; apply term_rec3; clear t.
intros v; simpl; apply th_refl.
intros f l IH; unfold th_eq; apply trans_clos_is_trans with (Term f (map unit_nf l)).
destruct l as [ | a l].
apply th_refl.
apply general_context.
revert a IH; induction l as [ | b l].
intros a IH.
assert (Ha := IH _ (or_introl _ (eq_refl _))).
apply rwr_list_cons; assumption.
intros a IH.
assert (Ha := IH _ (or_introl _ (eq_refl _))).
assert (Hl : rwr_list (one_step (sym_refl unit_one_step_at_top)) (b :: l) (map unit_nf (b :: l))).
apply IHl.
simpl; intros t [t_eq_b | t_in_l]; apply IH; right; [left | right]; assumption.
simpl; apply rwr_list_split.
apply IH; left; apply eq_refl.
apply Hl.

clear IH; destruct l as [ | t1 [ | t2 [ | t3 l ]]]; 
[apply th_refl | apply th_refl | idtac | apply th_refl].
simpl; case_eq (unit_theory f); [intros u UT | intros u UT | intros u UT | intro UT].
generalize (T.eq_bool_ok (unit_nf t1) (Term u nil)); case (T.eq_bool (unit_nf t1) (Term u nil)); [intro t1_eq_u | intro t1_diff_u].
subst; apply R_in_rwr_R; rewrite t1_eq_u; left; apply left_unit; left; trivial.
apply th_refl.
generalize (T.eq_bool_ok (unit_nf t2) (Term u nil)); case (T.eq_bool (unit_nf t2) (Term u nil)); [intro t2_eq_u | intro t2_diff_u].
subst; apply R_in_rwr_R; rewrite t2_eq_u; left; apply right_unit; left; trivial.
apply th_refl.
generalize (T.eq_bool_ok (unit_nf t1) (Term u nil)); case (T.eq_bool (unit_nf t1) (Term u nil)); [intro t1_eq_u | intro t1_diff_u].
subst; apply R_in_rwr_R; rewrite t1_eq_u; left; apply left_unit; right; trivial.
generalize (T.eq_bool_ok (unit_nf t2) (Term u nil)); case (T.eq_bool (unit_nf t2) (Term u nil)); [intro t2_eq_u | intro t2_diff_u].
subst; apply R_in_rwr_R; rewrite t2_eq_u; left; apply right_unit; right; trivial.
apply th_refl.
apply th_refl.
Qed.

Lemma one_step_unit_th_unit_nf_eq :
  forall t1 t2, one_step (sym_refl unit_one_step_at_top) t1 t2 -> unit_nf t1 = unit_nf t2.
Proof.
intro t1; pattern t1; apply term_rec3; clear t1.
intros v t2 H; inversion H as [ t1 t2' H' | ]; subst; 
inversion H' as [[v1 | f1 l1] u2 sigma H'' v1_sigma u2_sigma];
destruct H'' as [ H'' | [H'' | H'']].
inversion H''.
inversion H'' as [ u22 f u Ufu | u21 f u Ufu].
subst; simpl; rewrite v1_sigma; destruct Ufu as [Ufu | Ufu]; rewrite Ufu.
generalize (F.Symb.eq_bool_ok u u); case (F.Symb.eq_bool u u); 
[intros  _; trivial | intro u_diff_u; apply False_rect; apply u_diff_u; reflexivity].
generalize (F.Symb.eq_bool_ok u u); case (F.Symb.eq_bool u u); 
[intros  _; trivial | intro u_diff_u; apply False_rect; apply u_diff_u; reflexivity].
subst; simpl; rewrite v1_sigma; destruct Ufu as [Ufu | Ufu]; rewrite Ufu.
generalize (F.Symb.eq_bool_ok u u); case (F.Symb.eq_bool u u); 
[intros  _; trivial | intro u_diff_u; apply False_rect; apply u_diff_u; reflexivity].
simpl.
generalize (F.Symb.eq_bool_ok u u); case (F.Symb.eq_bool u u); 
[intros  _; trivial | intro u_diff_u; apply False_rect; apply u_diff_u; reflexivity].
subst; trivial.

intros f l IHl t2 H; inversion H as [t1 t2' H' | t1 t2' l2 H']; subst.
generalize (no_need_of_instance _ _ H'); clear H'; intro H'.
destruct H' as [H' | [H' | H']].
inversion H' as [t2' f' u [Ufu | Ufu] | t2' f' u [Ufu | Ufu]]; subst;
simpl; rewrite Ufu.
generalize (F.Symb.eq_bool_ok u u); case (F.Symb.eq_bool u u); 
[intros  _; trivial | intro u_diff_u; apply False_rect; apply u_diff_u; reflexivity].
generalize (F.Symb.eq_bool_ok u u); case (F.Symb.eq_bool u u); 
[intros  _; trivial | intro u_diff_u; apply False_rect; apply u_diff_u; reflexivity].
generalize (F.Symb.eq_bool_ok u u); case (F.Symb.eq_bool u u); 
[intros  _; trivial | intro u_diff_u; apply False_rect; apply u_diff_u; reflexivity].
generalize (F.Symb.eq_bool_ok u u); case (F.Symb.eq_bool u u); 
[intros  _; trivial | intro u_diff_u; apply False_rect; apply u_diff_u; reflexivity].
generalize (T.eq_bool_ok (unit_nf t2) (Term u nil)); case (T.eq_bool (unit_nf t2) (Term u nil)); [intro t2_eq_u | intro t2_diff_u].
apply sym_eq; trivial.
trivial.
generalize (Term f l) H'; clear H'; intros t H';
inversion H' as [t2' f' u [Ufu | Ufu] | t2' f' u [Ufu | Ufu]]; subst;
simpl; rewrite Ufu.
generalize (F.Symb.eq_bool_ok u u); case (F.Symb.eq_bool u u); 
[intros  _; trivial | intro u_diff_u; apply False_rect; apply u_diff_u; reflexivity].
generalize (F.Symb.eq_bool_ok u u); case (F.Symb.eq_bool u u); 
[intros  _; trivial | intro u_diff_u; apply False_rect; apply u_diff_u; reflexivity].
generalize (F.Symb.eq_bool_ok u u); case (F.Symb.eq_bool u u); 
[intros  _; trivial | intro u_diff_u; apply False_rect; apply u_diff_u; reflexivity].
generalize (F.Symb.eq_bool_ok u u); case (F.Symb.eq_bool u u); 
[intros  _; trivial | intro u_diff_u; apply False_rect; apply u_diff_u; reflexivity].
generalize (T.eq_bool_ok (unit_nf t) (Term u nil)); case (T.eq_bool (unit_nf t) (Term u nil)); [intro t_eq_u | intro t_diff_u].
trivial.
trivial.
subst; trivial.

simpl; clear H; assert (map unit_nf l = map unit_nf l2).
generalize l2 H'; clear l2 H'; induction l as [ | t l ]; intros l2 H; 
inversion H as [ t' t2 l' H' | t' l' l2' H']; subst; simpl.
rewrite (IHl t (or_introl _ (eq_refl t)) t2 H'); trivial.
apply (f_equal (fun l => unit_nf t :: l)); refine (IHl0 _ l2' H');
intros; apply IHl; trivial; right; trivial.
clear IHl H'; destruct l as [ | t1 [ | t2 [ | t3 l]]];
destruct l2 as [ | s1 [ | s2 [ | s3 l2]]]; simpl in H; try discriminate.
trivial.
simpl; rewrite H; trivial.
injection H; intros H1 H2; simpl; rewrite H1; rewrite H2; trivial.
simpl; rewrite H; trivial.
Qed.

Lemma unit_th_is_unit_nf_eq :
  forall t1 t2, unit_th t1 t2 <-> unit_nf t1 = unit_nf t2.
Proof.
intros t1 t2; split.

intro H; induction H; [ idtac | apply trans_eq with (unit_nf y); trivial];
apply one_step_unit_th_unit_nf_eq; assumption.

unfold unit_th, th_eq; intro H'; apply trans_clos_is_trans with (unit_nf t1); 
[idtac | rewrite H'; apply th_sym ]; apply unit_nf_is_sound.
Qed.

Lemma unit_nf_is_idempotent :
  forall t, unit_nf (unit_nf t) = unit_nf t.
Proof.
intro t; generalize (unit_th_is_unit_nf_eq (unit_nf t) t); 
intros [H _]; apply H;
unfold unit_th; apply th_sym;
apply unit_nf_is_sound.
Qed.

Lemma unit_for_AC :
  forall f, arity f = AC -> 
  match unit_theory f with
  | LU _ | RU _ => False
  | U _ | Nothing => True
  end.
Proof.
intros f Ar; generalize (unit_theory_is_coherent f); 
destruct (unit_theory f); trivial;
intros [ H _ ]; rewrite Ar in H; discriminate.
Qed.

Lemma unit_for_C :
  forall f, (arity f = C \/ arity f = AC) -> 
  match unit_theory f with
  | LU _ | RU _ => False
  | U _ | Nothing => True
  end.
Proof.
intros f [ Ar | Ar ]; 
generalize (unit_theory_is_coherent f); 
destruct (unit_theory f); trivial;
intros [ H _ ]; rewrite Ar in H; discriminate.
Qed.

Lemma acu_is_ac_on_unit_nf : 
  forall t1 t2, ac (unit_nf t1) (unit_nf t2) <-> acu t1 t2.
Proof.
unfold ac, acu, th_eq; intros t1 t2; split; intro H.

apply trans_clos_is_trans with (unit_nf t1).
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 H; intros t1 t2 [H | [H | H]].
left; right; trivial.
right; left; right; trivial.
right; right; trivial.
apply unit_nf_is_sound.
apply trans_clos_is_trans with (unit_nf t2).
apply rwr_incl with (sym_refl ac_one_step_at_top).
clear t1 t2 H; intros t1 t2 [H | [H | H]].
left; left; trivial.
right; left; left; trivial.
right; right; trivial.
trivial.
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 H; intros t1 t2 [H | [H | H]].
left; right; trivial.
right; left; right; trivial.
right; right; trivial.
apply th_sym; apply unit_nf_is_sound.

assert (No_need_of_inst : forall t1 t2, axiom (sym_refl (union _ ac_one_step_at_top unit_one_step_at_top)) t1 t2 ->
  sym_refl (union _ ac_one_step_at_top unit_one_step_at_top) t1 t2).
clear t1 t2 H; intros t1 t2 H; inversion_clear H as [u1 u2 sigma H'].
destruct H' as [[H | H] | [[H | H] | H]].
inversion_clear H.
simpl; left; left; apply a_axiom; trivial.
simpl; left; left; apply c_axiom; trivial.
inversion_clear H.
simpl; left; right; apply left_unit; trivial.
simpl; left; right; apply right_unit; trivial.
inversion_clear H.
simpl; right; left; left; apply a_axiom; trivial.
simpl; right; left; left; apply c_axiom; trivial.
inversion_clear H.
simpl; right; left; right; apply left_unit; trivial.
simpl; right; left; right; apply right_unit; trivial.
subst; right; right; trivial.
assert (H1 :
forall f u1 u2 u3, arity f = AC -> th_eq ac_one_step_at_top
  (unit_nf (Term f (Term f (u1 :: u2 :: nil) :: u3 :: nil)))
  (unit_nf (Term f (u1 :: Term f (u2 :: u3 :: nil) :: nil)))).
intros f u1 u2 u3 Ar; simpl.
assert (UT : forall g, g = f -> unit_theory g = unit_theory f).
intros; subst; trivial.
generalize (unit_for_AC _ Ar); destruct (unit_theory f) as [ u | u | u | ];
try contradiction;
intros _;
generalize (UT f (eq_refl _)); clear UT; intro UT.
generalize (T.eq_bool_ok (unit_nf u1) (Term u nil)); case (T.eq_bool (unit_nf u1) (Term u nil)); [intro u1_eq_u | intro u1_diff_u].
apply th_refl.
generalize (T.eq_bool_ok (unit_nf u2) (Term u nil)); case (T.eq_bool (unit_nf u2) (Term u nil)); [intro u2_eq_u | intro u2_diff_u].
generalize (T.eq_bool_ok  (unit_nf u1) (Term u nil)); case (T.eq_bool (unit_nf u1) (Term u nil)); [intro u1_eq_u |  intros _].
absurd (unit_nf u1 = Term u nil); trivial.
generalize (T.eq_bool_ok (unit_nf u3) (Term u nil)); case (T.eq_bool (unit_nf u3) (Term u nil)); [intro u3_eq_u | intro u3_diff_u].
apply th_refl.
apply th_refl.
generalize (T.eq_bool_ok (Term f (unit_nf u1 :: unit_nf u2 :: nil)) (Term u nil)); case (T.eq_bool (Term f (unit_nf u1 :: unit_nf u2 :: nil)) (Term u nil)); [ intro H' | intros _].
discriminate.
generalize (T.eq_bool_ok (unit_nf u3) (Term u nil)); case (T.eq_bool (unit_nf u3) (Term u nil)); [intro u3_eq_u | intro u3_diff_u].
generalize (T.eq_bool_ok (unit_nf u2) (Term u nil)); case (T.eq_bool (unit_nf u2) (Term u nil)); [intro u2_eq_u | intros _].
absurd (unit_nf u2 = Term u nil); trivial.
apply th_refl.
generalize (T.eq_bool_ok (Term f (unit_nf u1 :: unit_nf u2 :: nil)) (Term u nil)); case (T.eq_bool (Term f (unit_nf u1 :: unit_nf u2 :: nil)) (Term u nil)); [intro H' | intros _].
discriminate.
generalize (T.eq_bool_ok (Term f (unit_nf u2 :: unit_nf u3 :: nil)) (Term u nil)); case (T.eq_bool (Term f (unit_nf u2 :: unit_nf u3 :: nil)) (Term u nil)); [intro  H' | intros _].
discriminate.
apply l_assoc; trivial.
apply l_assoc; trivial.

assert (H2 :
forall f u1 u2, arity f = C \/ arity f = AC -> th_eq ac_one_step_at_top
  (unit_nf (Term f (u1 :: u2 :: nil)))
  (unit_nf (Term f (u2 :: u1 :: nil)))).
intros f u1 u2 Ar; simpl;
assert (UT : forall g, g = f -> unit_theory g = unit_theory f).
intros; subst; trivial.
generalize (unit_for_C _ Ar); destruct (unit_theory f) as [ u | u | u | ];
try contradiction;
intros _;
generalize (UT f (eq_refl _)); clear UT; intro UT.
generalize (T.eq_bool_ok (unit_nf u1) (Term u nil)); case (T.eq_bool (unit_nf u1) (Term u nil)); [intro u1_eq_u | intro u1_diff_u].
generalize (T.eq_bool_ok (unit_nf u2) (Term u nil)); case (T.eq_bool (unit_nf u2) (Term u nil)); [intro u2_eq_u | intro u2_diff_u].
rewrite u1_eq_u; rewrite u2_eq_u; apply th_refl.
apply th_refl.
generalize (T.eq_bool_ok (unit_nf u2) (Term u nil)); case (T.eq_bool (unit_nf u2) (Term u nil)); [intro u2_eq_u | intro u2_diff_u].
apply th_refl.
apply comm; trivial.
apply comm; trivial.

refine (rwr_inv _ (sym_refl (union _ ac_one_step_at_top unit_one_step_at_top))
(rwr (sym_refl ac_one_step_at_top)) unit_nf _ _ _ _ _); trivial.
apply trans_clos_is_trans.
clear t1 t2 H; intro t1; pattern t1; apply term_rec2; clear t1; induction n.
intros t1 S_t1; 
absurd (1 <= 0); [auto with arith | apply Nat.le_trans with (size t1)]; 
[apply size_ge_one | trivial].
intros t1 S_t1 t2 H; inversion H as [H3 H4 H' | f l1 l2 H']; clear H.
subst; induction H' as [t1 t2 sigma H'].
destruct H' as [[H | H] | [[H | H] | H]].
inversion_clear H as [ f u1 u2 u3 Af | f u1 u2 Af].
unfold th_eq in *; simpl apply_subst; apply H1; trivial.
unfold th_eq in *; simpl apply_subst; apply H2; trivial.
generalize (unit_th_is_unit_nf_eq (apply_subst sigma t1) (apply_subst sigma t2)); 
intros [H' _]; unfold unit_th in *.
rewrite H'; 
[ apply th_refl 
| left; apply at_top;
apply instance; left; trivial ].

inversion_clear H as [ f u1 u2 u3 Af | f u1 u2 Af].
apply th_sym; unfold th_eq in *; simpl apply_subst; apply H1; trivial.
apply th_sym; unfold th_eq in *; simpl apply_subst; apply H2; trivial.
apply th_sym;
generalize (unit_th_is_unit_nf_eq (apply_subst sigma t2) (apply_subst sigma t1)); 
intros [H' _]; unfold unit_th in *.
rewrite H'; 
[ apply th_refl 
| left; apply at_top;
apply instance; left; trivial ].

subst; apply th_refl.

subst; 
assert (S_l1 : forall t, In t l1 -> size t <= n). 
intros t In_t; apply Nat.lt_succ_r; 
apply Nat.lt_le_trans with (size (Term f l1)); [apply size_direct_subterm | idtac]; trivial.
assert (H : rwr_list (one_step (sym_refl ac_one_step_at_top)) (map unit_nf l1) (map unit_nf l2)).
clear S_t1; generalize l2 H'; clear l2 H';
induction l1 as [ | t1 l1]; intros l2 H;
inversion_clear H as [ t1' t2 l1'  H' | t1' l1' l2' H'].
apply rwr_list_cons; apply IHn; trivial.
apply S_l1; left; apply eq_refl.
simpl; apply rwr_list_tail; apply IHl1; trivial.
intros; apply S_l1; right; trivial.
clear S_t1; 
assert (UT : forall g, g = f -> unit_theory g = unit_theory f).
intros; subst; trivial.
generalize (rwr_list_length_eq H); do 2 rewrite length_map.
destruct l1 as [ | s1 [ | t1 [ | u1 l1]]]; destruct l2 as [ | s2 [ | t2 [ | u2 l2]]]; 
simpl; intro L; try discriminate; clear L.
apply th_refl.
simpl; inversion H' as [H3 H4 H5 H'' | H3 H4 H5 H'']; subst.
apply general_context; trivial.
inversion H''.
simpl; inversion H' as [H3 H4 H5 H'' | H3 H4 H5 H'']; subst.
assert (s1_acu_s2 := IHn s1 (S_l1 _ (or_introl _ (eq_refl _))) s2 H'').
destruct (unit_theory f) as [ u | u | u | ];
generalize (UT f (eq_refl _)); clear UT; intro UT; simpl.
generalize (T.eq_bool_ok (unit_nf s1) (Term u nil)); case (T.eq_bool (unit_nf s1) (Term u nil)); [intro s1_eq_u | intro s1_diff_u].
generalize (T.eq_bool_ok (unit_nf s2) (Term u nil)); case (T.eq_bool (unit_nf s2) (Term u nil)); [intro s2_eq_u | intro s2_diff_u].
apply th_refl.
rewrite s1_eq_u in s1_acu_s2;  rewrite (ac_const u _ s1_acu_s2) in s2_diff_u;
absurd (Term u nil = Term u nil); trivial.
generalize (T.eq_bool_ok (unit_nf s2) (Term u nil)); case (T.eq_bool (unit_nf s2) (Term u nil)); [intro s2_eq_u | intro s2_diff_u].
rewrite s2_eq_u in s1_acu_s2;  rewrite (ac_const u _ (th_sym _ _ _ s1_acu_s2)) in s1_diff_u;
absurd (Term u nil = Term u nil); trivial.
apply general_context; simpl; intuition.
generalize (T.eq_bool_ok (unit_nf t2) (Term u nil)); case (T.eq_bool (unit_nf t2) (Term u nil)); [intro t2_eq_u | intro t2_diff_u].
apply IHn; trivial; apply S_l1; left; trivial.
apply general_context; simpl; intuition.
generalize (T.eq_bool_ok (unit_nf s1) (Term u nil)); case (T.eq_bool (unit_nf s1) (Term u nil)); [intro s1_eq_u | intro s1_diff_u].
generalize (T.eq_bool_ok (unit_nf s2) (Term u nil)); case (T.eq_bool (unit_nf s2) (Term u nil)); [intro s2_eq_u | intro s2_diff_u].
apply th_refl.
rewrite s1_eq_u in s1_acu_s2;  rewrite (ac_const u _ s1_acu_s2) in s2_diff_u;
absurd (Term u nil = Term u nil); trivial.
generalize (T.eq_bool_ok (unit_nf s2) (Term u nil)); case (T.eq_bool (unit_nf s2) (Term u nil)); [intro s2_eq_u | intro s2_diff_u].
rewrite s2_eq_u in s1_acu_s2;  rewrite (ac_const u _ (th_sym _ _ _ s1_acu_s2)) in s1_diff_u;
absurd (Term u nil = Term u nil); trivial.
generalize (T.eq_bool_ok (unit_nf t2) (Term u nil)); case (T.eq_bool (unit_nf t2) (Term u nil)); [intro t2_eq_u | intro t2_diff_u].
trivial.
apply general_context; simpl; intuition.
apply general_context; simpl; intuition.
inversion H'' as [H3 H4 H5 H''' | H3 H4 H5 H''']; subst.
assert (t1_acu_t2 := IHn t1 (S_l1 _ (or_intror _ (or_introl _ (eq_refl _)))) t2 H''').
destruct (unit_theory f) as [ u | u | u | ];
generalize (UT f (eq_refl _)); clear UT; intro UT; simpl.
generalize (T.eq_bool_ok ); case (T.eq_bool (unit_nf s2) (Term u nil)); [intro s2_eq_u | intro s2_diff_u].
trivial.
apply general_context; simpl; intuition.
generalize (T.eq_bool_ok (unit_nf t1) (Term u nil)); case (T.eq_bool (unit_nf t1) (Term u nil)); [intro t1_eq_u | intro t1_diff_u].
generalize (T.eq_bool_ok (unit_nf t2) (Term u nil)); case (T.eq_bool (unit_nf t2) (Term u nil)); [intro t2_eq_u | intro t2_diff_u].
apply th_refl.
rewrite t1_eq_u in t1_acu_t2;  rewrite (ac_const u _ t1_acu_t2) in t2_diff_u;
absurd (Term u nil = Term u nil); trivial.
generalize (T.eq_bool_ok (unit_nf t2) (Term u nil)); case (T.eq_bool (unit_nf t2) (Term u nil)); [intro t2_eq_u | intro t2_diff_u].
rewrite t2_eq_u in t1_acu_t2;  rewrite (ac_const u _ (th_sym _ _ _ t1_acu_t2)) in t1_diff_u;
absurd (Term u nil = Term u nil); trivial.
apply general_context; simpl; intuition.
generalize (T.eq_bool_ok (unit_nf s2) (Term u nil)); case (T.eq_bool (unit_nf s2) (Term u nil)); [intro s2_eq_u | intro s2_diff_u].
trivial.
generalize (T.eq_bool_ok (unit_nf t1) (Term u nil)); case (T.eq_bool (unit_nf t1) (Term u nil)); [intro t1_eq_u | intro t1_diff_u].
generalize (T.eq_bool_ok (unit_nf t2) (Term u nil)); case (T.eq_bool (unit_nf t2) (Term u nil));[intro t2_eq_u | intro t2_diff_u].
apply th_refl.
rewrite t1_eq_u in t1_acu_t2;  rewrite (ac_const u _ t1_acu_t2) in t2_diff_u;
absurd (Term u nil = Term u nil); trivial.
generalize (T.eq_bool_ok (unit_nf t2) (Term u nil)); case (T.eq_bool (unit_nf t2) (Term u nil)); [intro t2_eq_u | intro t2_diff_u].
rewrite t2_eq_u in t1_acu_t2;  rewrite (ac_const u _ (th_sym _ _ _ t1_acu_t2)) in t1_diff_u;
absurd (Term u nil = Term u nil); trivial.
apply general_context; simpl; intuition.
apply general_context; simpl; intuition.
inversion H'''.
apply general_context; simpl; intuition.
Qed.

Lemma mutate_free :
  forall n f, arity f = Free n -> (unit_theory f = Nothing) ->
  forall l1 l2, (forall t, In t l1 -> well_formed t) -> 
  (forall t, In t l2 -> well_formed t) ->
  acu (Term f l1) (Term f l2) -> l1 = l2 \/ rwr_list acu l1 l2.
Proof.
intros n f Af UT l1 l2 Wl1 Wl2 H;
generalize (acu_is_ac_on_unit_nf (Term f l1) (Term f l2));
intros [ _ H']; generalize (ac_cf_eq (H' H)); clear H H'; intro H.
do 2 rewrite unit_nf_nothing in H; trivial.
simpl in H; rewrite Af in H; injection H; clear H; intro H;
do 2 rewrite map_map in H;
generalize l2 Wl2 H; clear f Af UT l2 Wl2 H;
induction l1 as [ | s1 l1]; intros l2 Wl2 H; 
destruct l2 as [ | s2 l2]; trivial; try discriminate.
left; trivial.
simpl in H; injection H; clear H; intros H H'.
assert (Ws1 := Wl1 _ (or_introl _ (eq_refl _))).
assert (Ws2 := Wl2 _ (or_introl _ (eq_refl _))).
right; 
generalize (acu_is_ac_on_unit_nf s1 s2); intros [ H'' _];
generalize (H''  (cf_eq_ac (well_formed_unit_nf _ Ws1) 
                              (well_formed_unit_nf _ Ws2) H'));
destruct (IHl1 (tail_prop _ Wl1) l2 (tail_prop _ Wl2) H) as [l1_eq_l2 | l1_acu_l2];
simpl.
subst; intro s1_eq_s2; apply rwr_list_cons; left; assumption.
intro s1_eq_s2; apply rwr_list_split; trivial.
left; assumption.
Qed.

Lemma mutate_free_sound :
 forall f l1 l2, rwr_list acu l1 l2 -> acu (Term f l1) (Term f l2).
Proof.
intros f  l1 l2 H; apply general_context.
apply trans_clos_is_clos.
apply trans_incl with (one_step_list acu); trivial.
clear; intro l1; induction l1 as [ | a1 l1]; intros l2 H; inversion H; clear H; subst.
apply rwr_list_cons; assumption.
apply rwr_list_tail; apply IHl1; assumption.
Qed.

Lemma mutate_lu :
  forall f u, arity f = Free 2 -> unit_theory f = LU u ->
  forall s1 t1 s2 t2, well_formed s1 -> well_formed t1 ->
  well_formed s2 -> well_formed t2 ->
  acu (Term f (s1 :: t1 :: nil)) (Term f (s2 :: t2 :: nil)) ->
  (acu s1 s2 /\ acu t1 t2) \/
  (acu s1 (Term u nil) /\ acu t1 (Term f (s2 :: t2 :: nil))) \/
  (acu (Term u nil) s2 /\ acu (Term f (s1 :: t1:: nil)) t2).  
Proof.
unfold acu; intros f u Af UT s1 t1 s2 t2 Ws1 Wt1 Ws2 Wt2 H;
generalize (acu_is_ac_on_unit_nf (Term f (s1 :: t1 :: nil)) (Term f (s2 :: t2 :: nil)));
intros [_ H']; generalize (H' H); clear H'; 
intro H'; generalize (ac_size_eq H') (ac_cf_eq H'); clear H H'; intros S H.
simpl in H; rewrite UT in H.
revert H;
generalize (T.eq_bool_ok (unit_nf s1) (Term u nil)); case (T.eq_bool (unit_nf s1) (Term u nil)); [intro s1_eq_u | intro s1_diff_u].
intro H; right; left; split.
generalize (acu_is_ac_on_unit_nf s1 (Term u nil)); intros [ H' _]; apply H';
rewrite <- s1_eq_u; rewrite unit_nf_is_idempotent;
unfold ac; apply th_refl.
generalize (acu_is_ac_on_unit_nf t1 (Term f (s2 :: t2 :: nil))); intros [ H' _]; apply H';
apply cf_eq_ac.
apply well_formed_unit_nf; trivial.
apply well_formed_unit_nf; simpl.
unfold well_formed; simpl; rewrite Af; rewrite Ws2; rewrite Wt2; trivial.
rewrite H; simpl; rewrite UT; trivial.
generalize (T.eq_bool_ok (unit_nf s2) (Term u nil)); case (T.eq_bool (unit_nf s2) (Term u nil)); [intro s2_eq_u | intro s2_diff_u].
intro H; right; right; split.
generalize (acu_is_ac_on_unit_nf (Term u nil) s2); intros [ H' _]; apply H';
rewrite <- s2_eq_u; rewrite unit_nf_is_idempotent;
unfold ac; apply th_refl.
generalize (acu_is_ac_on_unit_nf (Term f (s1 :: t1 :: nil)) t2); intros [ H' _]; apply H';
apply cf_eq_ac.
apply well_formed_unit_nf; unfold well_formed; simpl; rewrite Af; rewrite Ws1; rewrite Wt1; trivial.
apply well_formed_unit_nf; trivial.
rewrite <- H; simpl; rewrite UT; rewrite Af; 
generalize (T.eq_bool_ok (unit_nf s1) (Term u nil)); case (T.eq_bool (unit_nf s1) (Term u nil)); [intro s1_eq_u | intros _].
absurd (unit_nf s1 = Term u nil); trivial.
simpl; rewrite Af; trivial.
left; split;
[ generalize (acu_is_ac_on_unit_nf s1 s2); intros [ H' _]
| generalize (acu_is_ac_on_unit_nf t1 t2); intros [ H' _]]; 
apply H';
(apply cf_eq_ac; 
[ apply well_formed_unit_nf; trivial
| apply well_formed_unit_nf; trivial
| injection H; rewrite Af; clear H; intro H; injection H; trivial]).
Qed.

Lemma mutate_lu_sound :
  forall f u, unit_theory f = LU u ->
  forall s1 t1 s2 t2,     
  ((acu s1 s2 /\ acu t1 t2) \/
  (acu s1 (Term u nil) /\ acu t1 (Term f (s2 :: t2 :: nil))) \/
  (acu (Term u nil) s2 /\ acu (Term f (s1 :: t1:: nil)) t2)) ->
  acu (Term f (s1 :: t1 :: nil)) (Term f (s2 :: t2 :: nil)). 
Proof.
unfold acu, th_eq;
intros f u UT s1 t1 s2 t2 [[H1 H2] | [[s1_eq_u H] | [u_eq_s2 H]]].
apply general_context; simpl.
apply rwr_list_split; trivial.
apply rwr_list_cons; trivial.
apply trans_clos_is_trans with (Term f ((Term u nil) :: t1 :: nil)).
apply general_context; simpl.
apply rwr_list_cons; trivial.
apply trans_clos_is_trans with t1; trivial;
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply R_in_rwr_R; left; apply left_unit; left; trivial.
apply trans_clos_is_trans with (Term f ((Term u nil) :: t2 :: nil)).
apply trans_clos_is_trans with t2; trivial;
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; unfold th_eq; apply R_in_rwr_R; left; apply left_unit; left; trivial.
apply general_context; simpl.
apply rwr_list_cons; trivial.
Qed.

Lemma mutate_ru :
  forall f u, arity f = Free 2 -> unit_theory f = RU u ->
  forall s1 t1 s2 t2, well_formed s1 -> well_formed t1 ->
  well_formed s2 -> well_formed t2 ->
  acu (Term f (s1 :: t1 :: nil)) (Term f (s2 :: t2 :: nil)) ->
  (acu s1 s2 /\ acu t1 t2) \/
  (acu t1 (Term u nil) /\ acu s1 (Term f (s2 :: t2 :: nil))) \/
  (acu (Term u nil) t2 /\ acu (Term f (s1 :: t1:: nil)) s2).  
Proof.
unfold acu; intros f u Af UT s1 t1 s2 t2 Ws1 Wt1 Ws2 Wt2 H;
generalize (acu_is_ac_on_unit_nf (Term f (s1 :: t1 :: nil)) (Term f (s2 :: t2 :: nil)));
intros [_ H']; generalize (H' H); clear H'; 
intro H'; generalize (ac_size_eq H') (ac_cf_eq H'); clear H H'; intros S H.
simpl in H; rewrite UT in H.
revert H;
generalize (T.eq_bool_ok (unit_nf t1) (Term u nil)); case (T.eq_bool (unit_nf t1) (Term u nil)); [intro t1_eq_u | intro t1_diff_u].
intro H; right; left; split.
generalize (acu_is_ac_on_unit_nf t1 (Term u nil)); intros [ H' _]; apply H';
rewrite <- t1_eq_u; rewrite unit_nf_is_idempotent;
unfold ac; apply th_refl.
generalize (acu_is_ac_on_unit_nf s1 (Term f (s2 :: t2 :: nil))); intros [ H' _]; apply H';
apply cf_eq_ac.
apply well_formed_unit_nf; trivial.
apply well_formed_unit_nf; unfold well_formed; simpl; rewrite Af; rewrite Ws2; rewrite Wt2; trivial.
rewrite H; simpl; rewrite UT; trivial.
generalize (T.eq_bool_ok (unit_nf t2) (Term u nil)); case (T.eq_bool (unit_nf t2) (Term u nil)); [intro t2_eq_u | intro t2_diff_u].
intro H; right; right; split.
generalize (acu_is_ac_on_unit_nf (Term u nil) t2); intros [ H' _]; apply H';
rewrite <- t2_eq_u; rewrite unit_nf_is_idempotent;
unfold ac; apply th_refl.
generalize (acu_is_ac_on_unit_nf (Term f (s1 :: t1 :: nil)) s2); intros [ H' _]; apply H';
apply cf_eq_ac.
apply well_formed_unit_nf; unfold well_formed; simpl; rewrite Af; rewrite Ws1; rewrite Wt1; trivial.
apply well_formed_unit_nf; trivial.
rewrite <- H; simpl; rewrite UT; rewrite Af; 
generalize (T.eq_bool_ok (unit_nf t1) (Term u nil)); case (T.eq_bool (unit_nf t1) (Term u nil)); [intro t1_eq_u | intros _].
absurd (unit_nf t1 = Term u nil); trivial.
simpl; rewrite Af; trivial.
left; split;
[ generalize (acu_is_ac_on_unit_nf s1 s2); intros [ H' _]
| generalize (acu_is_ac_on_unit_nf t1 t2); intros [ H' _]]; 
apply H';
(apply cf_eq_ac; 
[ apply well_formed_unit_nf; trivial
| apply well_formed_unit_nf; trivial
| injection H; rewrite Af; clear H; intro H; injection H; trivial]).
Qed.

Lemma mutate_ru_sound :
  forall f u, unit_theory f = RU u ->
  forall s1 t1 s2 t2, 
  ((acu s1 s2 /\ acu t1 t2) \/
  (acu t1 (Term u nil) /\ acu s1 (Term f (s2 :: t2 :: nil))) \/
  (acu (Term u nil) t2 /\ acu (Term f (s1 :: t1:: nil)) s2)) ->
  acu (Term f (s1 :: t1 :: nil)) (Term f (s2 :: t2 :: nil)).  
Proof.
unfold acu, th_eq;
intros f u UT s1 t1 s2 t2 [[H1 H2] | [[t1_eq_u H] | [u_eq_t2 H]]].
apply general_context; simpl.
apply rwr_list_split; trivial.
apply rwr_list_cons; trivial.
apply trans_clos_is_trans with (Term f (s1 :: (Term u nil) :: nil)).
apply general_context; simpl.
apply rwr_list_tail; apply rwr_list_cons; trivial.
apply trans_clos_is_trans with s1; trivial;
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 t1_eq_u H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
unfold th_eq; apply R_in_rwr_R; left; apply right_unit; left; trivial.
apply trans_clos_is_trans with (Term f (s2 :: (Term u nil) :: nil)).
apply trans_clos_is_trans with s2; trivial;
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 u_eq_t2 H; intros t1 t2 [H | [H | H]];
 [left | right; left | right; right; trivial]; right; trivial.
apply th_sym; unfold th_eq; apply R_in_rwr_R; unfold th_eq; left; apply right_unit; left; trivial.
apply general_context; simpl.
apply rwr_list_tail; apply rwr_list_cons; trivial.
Qed.

Lemma mutate_u :
  forall f u, arity f = Free 2 -> unit_theory f = U u ->
  forall s1 t1 s2 t2, well_formed s1 -> well_formed t1 ->
  well_formed s2 -> well_formed t2 ->
  acu (Term f (s1 :: t1 :: nil)) (Term f (s2 :: t2 :: nil)) ->
  (acu s1 s2 /\ acu t1 t2) \/
  (acu t1 (Term u nil) /\ acu s1 (Term f (s2 :: t2 :: nil))) \/
  (acu (Term u nil) t2 /\ acu (Term f (s1 :: t1:: nil)) s2) \/
  (acu s1 (Term u nil) /\ acu t1 (Term f (s2 :: t2 :: nil))) \/
  (acu (Term u nil) s2 /\ acu (Term f (s1 :: t1:: nil)) t2).  
Proof.
unfold acu; intros f u Af UT s1 t1 s2 t2 Ws1 Wt1 Ws2 Wt2 H;
generalize (acu_is_ac_on_unit_nf (Term f (s1 :: t1 :: nil)) (Term f (s2 :: t2 :: nil)));
intros [_ H']; generalize (H' H); clear H'; 
intro H'; generalize (ac_size_eq H') (ac_cf_eq H'); clear H H'; intros S H.
simpl in H; rewrite UT in H.
revert H; generalize (T.eq_bool_ok (unit_nf s1) (Term u nil)); case (T.eq_bool (unit_nf s1) (Term u nil)); [intro s1_eq_u | intro s1_diff_u].
intro H; right; right; right; left; split.
generalize (acu_is_ac_on_unit_nf s1 (Term u nil)); intros [ H' _]; apply H';
rewrite <- s1_eq_u; rewrite unit_nf_is_idempotent;
unfold ac; apply th_refl.
generalize (acu_is_ac_on_unit_nf t1 (Term f (s2 :: t2 :: nil))); intros [ H' _]; apply H';
apply cf_eq_ac.
apply well_formed_unit_nf; trivial.
apply well_formed_unit_nf; unfold well_formed; simpl; rewrite Af; rewrite Ws2; rewrite Wt2; trivial.
rewrite H; simpl; rewrite UT; trivial.
generalize (T.eq_bool_ok  (unit_nf s2) (Term u nil)); case (T.eq_bool (unit_nf s2) (Term u nil)); [intro s2_eq_u | intro s2_diff_u].
right; right; right; right; split.
generalize (acu_is_ac_on_unit_nf (Term u nil) s2); intros [ H' _]; apply H';
rewrite <- s2_eq_u; rewrite unit_nf_is_idempotent;
unfold ac; apply th_refl.
generalize (acu_is_ac_on_unit_nf (Term f (s1 :: t1 :: nil)) t2); intros [ H' _]; apply H';
apply cf_eq_ac.
apply well_formed_unit_nf; unfold well_formed; simpl; rewrite Af; rewrite Ws1; rewrite Wt1; trivial.
apply well_formed_unit_nf; trivial.
simpl; rewrite <- H; simpl; rewrite UT; 
generalize (T.eq_bool_ok (unit_nf s1) (Term u nil)); case (T.eq_bool (unit_nf s1) (Term u nil)); [intro s1_eq_u | intros _].
absurd (unit_nf s1 = Term u nil); trivial.
trivial.
generalize (T.eq_bool_ok (unit_nf t1) (Term u nil)); case (T.eq_bool (unit_nf t1) (Term u nil)); [intro t1_eq_u | intro t1_diff_u].
right; left; split.
generalize (acu_is_ac_on_unit_nf t1 (Term u nil)); intros [ H' _]; apply H';
rewrite <- t1_eq_u; rewrite unit_nf_is_idempotent;
unfold ac; apply th_refl.
generalize (acu_is_ac_on_unit_nf s1 (Term f (s2 :: t2 :: nil))); intros [ H' _]; apply H';
apply cf_eq_ac.
apply well_formed_unit_nf; trivial.
apply well_formed_unit_nf; unfold well_formed; simpl; rewrite Af; rewrite Ws2; rewrite Wt2; trivial.
rewrite H; simpl; rewrite UT;
generalize (T.eq_bool_ok (unit_nf s2) (Term u nil)); case (T.eq_bool (unit_nf s2) (Term u nil)); [intro s2_eq_u | intros _].
absurd (unit_nf s2 = Term u nil); trivial.
trivial.
generalize (T.eq_bool_ok (unit_nf t2) (Term u nil)); case (T.eq_bool (unit_nf t2) (Term u nil)); [intro t2_eq_u | intro t2_diff_u].
right; right; left; split.
generalize (acu_is_ac_on_unit_nf (Term u nil) t2); intros [ H' _]; apply H';
rewrite <- t2_eq_u; rewrite unit_nf_is_idempotent;
unfold ac; apply th_refl.
generalize (acu_is_ac_on_unit_nf (Term f (s1 :: t1 :: nil)) s2); intros [ H' _]; apply H';
apply cf_eq_ac.
apply well_formed_unit_nf; unfold well_formed; simpl; rewrite Af; rewrite Ws1; rewrite Wt1; trivial.
apply well_formed_unit_nf; trivial.
simpl; rewrite UT;
generalize (T.eq_bool_ok (unit_nf s1) (Term u nil)); case (T.eq_bool (unit_nf s1) (Term u nil)); [intro s1_eq_u | intros _].
absurd (unit_nf s1 = Term u nil); trivial.
generalize (T.eq_bool_ok (unit_nf t1) (Term u nil)); case (T.eq_bool (unit_nf t1) (Term u nil)); [intro t1_eq_u | intros _].
absurd (unit_nf t1 = Term u nil); trivial.
trivial.
left; split;
[ generalize (acu_is_ac_on_unit_nf s1 s2); intros [ H' _]
| generalize (acu_is_ac_on_unit_nf t1 t2); intros [ H' _]]; 
apply H';
(apply cf_eq_ac; 
[ apply well_formed_unit_nf; trivial
| apply well_formed_unit_nf; trivial
| injection H; rewrite Af; clear H; intro H; injection H; trivial]).
Qed.

Lemma mutate_u_sound :
  forall f u, unit_theory f = U u ->
  forall s1 t1 s2 t2, 
  ((acu s1 s2 /\ acu t1 t2) \/
  (acu t1 (Term u nil) /\ acu s1 (Term f (s2 :: t2 :: nil))) \/
  (acu (Term u nil) t2 /\ acu (Term f (s1 :: t1:: nil)) s2) \/
  (acu s1 (Term u nil) /\ acu t1 (Term f (s2 :: t2 :: nil))) \/
  (acu (Term u nil) s2 /\ acu (Term f (s1 :: t1:: nil)) t2)) ->  
  acu (Term f (s1 :: t1 :: nil)) (Term f (s2 :: t2 :: nil)).
Proof.
unfold acu, th_eq;
intros f u UT s1 t1 s2 t2 
[ [H1 H2] | [ [t1_eq_u H] | [[ u_eq_t2 H] | [ [s1_eq_u H ] | [ u_eq_s2 H ]]]]].
apply general_context; simpl. 
apply rwr_list_split; trivial.
apply rwr_list_cons; trivial.
apply trans_clos_is_trans with (Term f (s1 :: (Term u nil) :: nil)).
apply general_context; simpl.
apply rwr_list_tail; apply rwr_list_cons; trivial.
apply trans_clos_is_trans with s1; trivial.
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 t1_eq_u H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply R_in_rwr_R; unfold th_eq; left; apply right_unit; right; trivial.
apply trans_clos_is_trans with (Term f (s2 :: (Term u nil) :: nil)).
apply trans_clos_is_trans with s2; trivial;
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 u_eq_t2 H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; unfold th_eq; apply R_in_rwr_R; unfold th_eq; left; apply right_unit; right; trivial.
apply general_context; simpl.
apply rwr_list_tail; apply rwr_list_cons; trivial.
apply trans_clos_is_trans with (Term f ((Term u nil) :: t1 :: nil)).
apply general_context; simpl.
apply rwr_list_cons; trivial.
apply trans_clos_is_trans with t1; trivial.
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply R_in_rwr_R; unfold th_eq; left; apply left_unit; right; trivial.
apply trans_clos_is_trans with (Term f ((Term u nil) :: t2 :: nil)).
apply trans_clos_is_trans with t2; trivial;
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; unfold th_eq; apply R_in_rwr_R; left; apply left_unit; right; trivial.
apply general_context; simpl.
apply rwr_list_cons; trivial.
Qed.

Lemma mutate_c :
  forall f, arity f = C -> (unit_theory f = Nothing) ->
  forall s1 t1 s2 t2, well_formed s1 -> well_formed t1 ->
  well_formed s2 -> well_formed t2 ->
  acu (Term f (s1 :: t1 :: nil)) (Term f (s2 :: t2 :: nil)) ->
  (acu s1 s2 /\ acu t1 t2) \/ (acu s1 t2 /\ acu t1 s2).
Proof.
intros f Af UT s1 t1 s2 t2 Ws1 Wt1 Ws2 Wt2 H;
generalize (acu_is_ac_on_unit_nf (Term f (s1 :: t1 :: nil)) (Term f (s2 :: t2 :: nil)));
intros [ _ H']; generalize (ac_cf_eq (H' H)); clear H H'; intro H.
do 2 rewrite unit_nf_nothing in H; trivial.
simpl in H; rewrite Af in H; injection H; clear H; intro H.
assert (H' := Sort.quick_permut 
                   (canonical_form (unit_nf s1) :: canonical_form (unit_nf t1) :: nil)).
rewrite H in H'; clear H.
assert (H'' := Sort.quick_permut 
                   (canonical_form (unit_nf s2) :: canonical_form (unit_nf t2) :: nil)).
assert (H := permut_trans  H' (permut_sym  H'')).
clear H' H''.
destruct (list_permut.permut_length_2 H) as 
[[s1_eq_s2 t1_eq_t2] | [s1_eq_t2 s2_eq_t1]].
left; split.
generalize (acu_is_ac_on_unit_nf s1 s2); intros [H' _]; apply H';
apply cf_eq_ac; trivial.
apply well_formed_unit_nf; trivial.
apply well_formed_unit_nf; trivial.
generalize (acu_is_ac_on_unit_nf t1 t2); intros [H' _]; apply H';
apply cf_eq_ac; trivial.
apply well_formed_unit_nf; trivial.
apply well_formed_unit_nf; trivial.
right; split.
generalize (acu_is_ac_on_unit_nf s1 t2); intros [H' _]; apply H';
apply cf_eq_ac; trivial.
apply well_formed_unit_nf; trivial.
apply well_formed_unit_nf; trivial.
generalize (acu_is_ac_on_unit_nf t1 s2); intros [H' _]; apply H';
apply cf_eq_ac.
apply well_formed_unit_nf; trivial.
apply well_formed_unit_nf; trivial.
unfold EDS.eq_A in *; trivial.
Qed.

Lemma mutate_c_sound :
  forall f, arity f = C -> (unit_theory f = Nothing) ->
  forall s1 t1 s2 t2, 
  (acu s1 s2 /\ acu t1 t2) \/ (acu s1 t2 /\ acu t1 s2) ->
 acu (Term f (s1 :: t1 :: nil)) (Term f (s2 :: t2 :: nil)).
 Proof.
unfold acu, th_eq;
intros f Af UT s1 t1 s2 t2 [[s1_eq_s2 t1_eq_t2] | [s1_eq_t2 t1_eq_s2]].
apply general_context; simpl.
apply rwr_list_split; trivial.
apply rwr_list_cons; trivial.
apply trans_clos_is_trans with (Term f (t1 :: s1 :: nil)).
apply rwr_incl with (sym_refl ac_one_step_at_top).
clear t1 t2 s1_eq_t2 t1_eq_s2; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; left; trivial.
apply comm; left; trivial.
apply general_context; simpl.
apply rwr_list_split; trivial.
apply rwr_list_cons; trivial.
Qed.

Lemma mutate_cu :
  forall f u, arity f = C -> unit_theory f = U u ->
  forall s1 t1 s2 t2, well_formed s1 -> well_formed t1 ->
  well_formed s2 -> well_formed t2 ->
  acu (Term f (s1 :: t1 :: nil)) (Term f (s2 :: t2 :: nil)) ->
  (acu s1 s2 /\ acu t1 t2) \/ (acu s1 t2 /\ acu t1 s2) \/
  (acu t1 (Term u nil) /\ acu s1 (Term f (s2 :: t2 :: nil))) \/
  (acu (Term u nil) t2 /\ acu (Term f (s1 :: t1:: nil)) s2) \/
  (acu s1 (Term u nil) /\ acu t1 (Term f (s2 :: t2 :: nil))) \/
  (acu (Term u nil) s2 /\ acu (Term f (s1 :: t1:: nil)) t2).  
Proof.
unfold acu; intros f u Af UT s1 t1 s2 t2 Ws1 Wt1 Ws2 Wt2 H;
generalize (acu_is_ac_on_unit_nf (Term f (s1 :: t1 :: nil)) (Term f (s2 :: t2 :: nil)));
intros [_ H']; generalize (H' H); clear H'; 
intro H'; generalize (ac_size_eq H') (ac_cf_eq H'); clear H H'; intros S H.
simpl in H; rewrite UT in H.
revert H;
generalize (T.eq_bool_ok (unit_nf s1) (Term u nil)); case (T.eq_bool (unit_nf s1) (Term u nil)); [intro s1_eq_u | intro s1_diff_u].
intro H; right; right; right; right; left; split.
generalize (acu_is_ac_on_unit_nf s1 (Term u nil)); intros [ H' _]; apply H';
rewrite <- s1_eq_u; rewrite unit_nf_is_idempotent;
unfold ac; apply th_refl.
generalize (acu_is_ac_on_unit_nf t1 (Term f (s2 :: t2 :: nil))); intros [ H' _]; apply H';
apply cf_eq_ac.
apply well_formed_unit_nf; trivial.
apply well_formed_unit_nf; unfold well_formed; simpl; rewrite Af; rewrite Ws2; rewrite Wt2; trivial.
rewrite H; simpl; rewrite UT; trivial.
generalize (T.eq_bool_ok (unit_nf s2) (Term u nil)); case (T.eq_bool (unit_nf s2) (Term u nil)); [intro s2_eq_u | intro s2_diff_u].
intro H; right; right; right; right; right; split.
generalize (acu_is_ac_on_unit_nf (Term u nil) s2); intros [ H' _]; apply H';
rewrite <- s2_eq_u; rewrite unit_nf_is_idempotent;
unfold ac; apply th_refl.
generalize (acu_is_ac_on_unit_nf (Term f (s1 :: t1 :: nil)) t2); intros [ H' _]; apply H';
apply cf_eq_ac.
apply well_formed_unit_nf; unfold well_formed; simpl; rewrite Af; rewrite Ws1; rewrite Wt1; trivial.
apply well_formed_unit_nf; trivial.
simpl; rewrite <- H; simpl; rewrite UT;
generalize (T.eq_bool_ok (unit_nf s1) (Term u nil)); case (T.eq_bool (unit_nf s1) (Term u nil)); [intro s1_eq_u | intros _].
absurd (unit_nf s1 = Term u nil); trivial.
trivial.
generalize (T.eq_bool_ok (unit_nf t1) (Term u nil)); case (T.eq_bool (unit_nf t1) (Term u nil)); [intro t1_eq_u | intro t1_diff_u].
intro H; right; right; left; split.
generalize (acu_is_ac_on_unit_nf t1 (Term u nil)); intros [ H' _]; apply H';
rewrite <- t1_eq_u; rewrite unit_nf_is_idempotent;
unfold ac; apply th_refl.
generalize (acu_is_ac_on_unit_nf s1 (Term f (s2 :: t2 :: nil))); intros [ H' _]; apply H';
apply cf_eq_ac.
apply well_formed_unit_nf; trivial.
apply well_formed_unit_nf; unfold well_formed; simpl; rewrite Af; rewrite Ws2; rewrite Wt2; trivial.
rewrite H; simpl; rewrite UT;
generalize (T.eq_bool_ok (unit_nf s2) (Term u nil)); case (T.eq_bool (unit_nf s2) (Term u nil)); [intro s2_eq_u | intros _].
absurd (unit_nf s2 = Term u nil); trivial.
trivial.
generalize (T.eq_bool_ok (unit_nf t2) (Term u nil)); case (T.eq_bool (unit_nf t2) (Term u nil)); [intro t2_eq_u | intro t2_diff_u].
right; right; right; left; split.
generalize (acu_is_ac_on_unit_nf (Term u nil) t2); intros [ H' _]; apply H';
rewrite <- t2_eq_u; rewrite unit_nf_is_idempotent;
unfold ac; apply th_refl.
generalize (acu_is_ac_on_unit_nf (Term f (s1 :: t1 :: nil)) s2); intros [ H' _]; apply H';
apply cf_eq_ac.
apply well_formed_unit_nf; unfold well_formed; simpl; rewrite Af; rewrite Ws1; rewrite Wt1; trivial.
apply well_formed_unit_nf; trivial.
simpl; rewrite UT;
generalize (T.eq_bool_ok (unit_nf s1) (Term u nil)); case (T.eq_bool (unit_nf s1) (Term u nil)); [intro s1_eq_u | intros _].
absurd (unit_nf s1 = Term u nil); trivial.
generalize (T.eq_bool_ok (unit_nf t1) (Term u nil)); case (T.eq_bool (unit_nf t1) (Term u nil)); [intro t1_eq_u | intros _].
absurd (unit_nf t1 = Term u nil); trivial.
trivial.
intro H; simpl in H; rewrite Af in H; injection H; clear H; intro H.
assert (H' := Sort.quick_permut 
                   (canonical_form (unit_nf s1) :: canonical_form (unit_nf t1) :: nil)).
rewrite H in H'; clear H.
assert (H'' := Sort.quick_permut 
                   (canonical_form (unit_nf s2) :: canonical_form (unit_nf t2) :: nil)).
assert (H := permut_trans  H' (permut_sym  H'')).
clear H' H''.
destruct (list_permut.permut_length_2 H) as 
[[s1_eq_s2 t1_eq_t2] | [s1_eq_t2 s2_eq_t1]].
left; split.
generalize (acu_is_ac_on_unit_nf s1 s2); intros [H' _]; apply H';
apply cf_eq_ac; trivial.
apply well_formed_unit_nf; trivial.
apply well_formed_unit_nf; trivial.
generalize (acu_is_ac_on_unit_nf t1 t2); intros [H' _]; apply H';
apply cf_eq_ac; trivial.
apply well_formed_unit_nf; trivial.
apply well_formed_unit_nf; trivial.
right; left; split.
generalize (acu_is_ac_on_unit_nf s1 t2); intros [H' _]; apply H';
apply cf_eq_ac; trivial.
apply well_formed_unit_nf; trivial.
apply well_formed_unit_nf; trivial.
generalize (acu_is_ac_on_unit_nf t1 s2); intros [H' _]; apply H';
apply cf_eq_ac.
apply well_formed_unit_nf; trivial.
apply well_formed_unit_nf; trivial.
unfold EDS.eq_A in *; trivial.
Qed.

Lemma mutate_cu_sound :
  forall f u, arity f = C -> unit_theory f = U u ->
  forall s1 t1 s2 t2, 
 (acu s1 s2 /\ acu t1 t2) \/ (acu s1 t2 /\ acu t1 s2) \/
  (acu t1 (Term u nil) /\ acu s1 (Term f (s2 :: t2 :: nil))) \/
  (acu (Term u nil) t2 /\ acu (Term f (s1 :: t1:: nil)) s2) \/
  (acu s1 (Term u nil) /\ acu t1 (Term f (s2 :: t2 :: nil))) \/
  (acu (Term u nil) s2 /\ acu (Term f (s1 :: t1:: nil)) t2) ->  
  acu (Term f (s1 :: t1 :: nil)) (Term f (s2 :: t2 :: nil)).
Proof.
unfold acu, th_eq;
intros f u Af UT s1 t1 s2 t2 
[ [H1 H2] | 
[ [H1 H2] |
[ [t1_eq_u H] | 
[ [ u_eq_t2 H] | 
[ [s1_eq_u H ] | 
[ u_eq_s2 H ] ]]]]].
apply general_context; simpl.
apply rwr_list_split; trivial.
apply rwr_list_cons; trivial.
apply trans_clos_is_trans with (Term f (t1 :: s1 :: nil)).
apply rwr_incl with (sym_refl ac_one_step_at_top).
clear t1 t2 H1 H2; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; left; trivial.
apply comm; left; trivial.
apply general_context; simpl.
apply rwr_list_split; trivial.
apply rwr_list_cons; trivial.
apply trans_clos_is_trans with (Term f (s1 :: (Term u nil) :: nil)).
apply general_context; simpl.
apply rwr_list_tail; apply rwr_list_cons; trivial.
apply trans_clos_is_trans with s1; trivial.
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 t1_eq_u H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply R_in_rwr_R; unfold th_eq; left; apply right_unit; right; trivial.
apply trans_clos_is_trans with (Term f (s2 :: (Term u nil) :: nil)).
apply trans_clos_is_trans with s2; trivial;
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 u_eq_t2 H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; unfold th_eq; apply R_in_rwr_R; unfold th_eq; left; apply right_unit; right; trivial.
apply general_context; simpl.
apply rwr_list_tail; apply rwr_list_cons; trivial.
apply trans_clos_is_trans with (Term f ((Term u nil) :: t1 :: nil)).
apply general_context; simpl.
apply rwr_list_cons; trivial.
apply trans_clos_is_trans with t1; trivial.
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 s1_eq_u H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply R_in_rwr_R; unfold th_eq; left; apply left_unit; right; trivial.
apply trans_clos_is_trans with (Term f ((Term u nil) :: t2 :: nil)).
apply trans_clos_is_trans with t2; trivial;
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 u_eq_s2 H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; unfold th_eq; apply R_in_rwr_R; unfold th_eq; left; apply left_unit; right; trivial.
apply general_context; simpl.
apply rwr_list_cons; trivial.
Qed.

(* Now, the equations of the form s1+t1 = c *)
Lemma clash : 
  forall f g l1 l2, f<> g -> 
  unit_theory f = Nothing -> unit_theory g = Nothing ->
  acu (Term f l1) (Term g l2) -> False.
Proof.
intros f g l1 l2 f_diff_g UTf UTg H; apply f_diff_g.
generalize (acu_is_ac_on_unit_nf (Term f l1) (Term g l2)); intros [_ H'].
generalize (H' H); clear H' H; intro H; 
simpl in H; rewrite UTf in H; rewrite UTg in H.
generalize (ac_top_eq H); 
destruct l1 as [ | s1 [ | t1 [ | u1 l1]]]; destruct l2 as [ | s2 [ | t2 [ | u2 l2]]];
trivial.
Qed.

Lemma mutate_free_lu :
  forall f g u l1 s2 t2, f <> g ->
  unit_theory f = Nothing -> unit_theory g = LU u ->
  acu (Term f l1) (Term g (s2 :: t2 :: nil)) -> 
  acu (Term f l1) t2 /\ acu (Term u nil) s2.
Proof.
intros f g u l1 s2 t2 f_diff_g UTf UTg H;
generalize (acu_is_ac_on_unit_nf (Term f l1) (Term g (s2 :: t2 :: nil)));
intros [ _ H' ]; generalize (H' H); clear H' H; intro H;
simpl in H; rewrite UTg in H.
revert H; generalize (T.eq_bool_ok (unit_nf s2) (Term u nil)); case (T.eq_bool (unit_nf s2) (Term u nil)); [intro s2_eq_u | intro s2_diff_u].
intro H; split.
generalize (acu_is_ac_on_unit_nf (Term f l1) t2); 
intros [H' _]; generalize (H' H); trivial.
rewrite <- s2_eq_u.
unfold acu, th_eq; 
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t2 H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; apply unit_nf_is_sound.
intro H; absurd (f=g); trivial.
rewrite UTf in H; generalize (ac_top_eq H); 
destruct l1 as [ | s1 [ | t1 [ | u1 l1]]]; trivial.
Qed.

Lemma mutate_free_lu_sound :
  forall f g u l1 s2 t2, unit_theory g = LU u ->
  acu (Term f l1) t2 /\ acu (Term u nil) s2 ->
  acu (Term f l1) (Term g (s2 :: t2 :: nil)).
Proof.
unfold acu, th_eq; 
intros f g u l1 s2 t2 UTg [ H u_eq_s2 ].
apply trans_clos_is_trans with t2; trivial.
apply trans_clos_is_trans with (Term g ((Term u nil) :: t2 :: nil)).
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t2 H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; unfold th_eq; apply R_in_rwr_R; left; apply left_unit; left; trivial.
apply general_context; simpl.
apply rwr_list_cons; trivial.
Qed.

Lemma mutate_free_ru :
  forall f g u l1 s2 t2, f <> g ->
  unit_theory f = Nothing -> unit_theory g = RU u ->
  acu (Term f l1) (Term g (s2 :: t2 :: nil)) -> 
  acu (Term f l1) s2 /\ acu (Term u nil) t2.
Proof.
intros f g u l1 s2 t2 f_diff_g UTf UTg H;
generalize (acu_is_ac_on_unit_nf (Term f l1) (Term g (s2 :: t2 :: nil)));
intros [ _ H' ]; generalize (H' H); clear H' H; intro H;
simpl in H; rewrite UTg in H; revert H.
generalize (T.eq_bool_ok (unit_nf t2) (Term u nil)); case (T.eq_bool (unit_nf t2) (Term u nil)); [intro t2_eq_u | intro t2_diff_u].
split.
generalize (acu_is_ac_on_unit_nf (Term f l1) s2); 
intros [H' _]; generalize (H' H); trivial.
rewrite <- t2_eq_u.
unfold acu, th_eq; 
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t2 t2_eq_u H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; apply unit_nf_is_sound.
intro H; absurd (f=g); trivial.
rewrite UTf in H; generalize (ac_top_eq H); 
destruct l1 as [ | s1 [ | t1 [ | u1 l1]]]; trivial.
Qed.

Lemma mutate_free_ru_sound :
  forall f g u l1 s2 t2, unit_theory g = RU u ->
  acu (Term f l1) s2 /\ acu (Term u nil) t2 ->
  acu (Term f l1) (Term g (s2 :: t2 :: nil)).
Proof.
unfold acu, th_eq; 
intros f g u l1 s2 t2 UTg [ H u_eq_t2 ].
apply trans_clos_is_trans with s2; trivial.
apply trans_clos_is_trans with (Term g (s2 :: (Term u nil) :: nil)).
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t2 u_eq_t2 H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; unfold th_eq; apply R_in_rwr_R; left; apply right_unit; left; trivial.
apply general_context; simpl.
apply rwr_list_tail; apply rwr_list_cons; trivial.
Qed.

Lemma mutate_free_u :
  forall f g u l1 s2 t2, f <> g ->
  unit_theory f = Nothing -> unit_theory g = U u ->
  acu (Term f l1) (Term g (s2 :: t2 :: nil)) -> 
  (acu (Term f l1) t2 /\ acu (Term u nil) s2) \/
  (acu (Term f l1) s2 /\ acu (Term u nil) t2).
Proof.
intros f g u l1 s2 t2 f_diff_g UTf UTg H;
generalize (acu_is_ac_on_unit_nf (Term f l1) (Term g (s2 :: t2 :: nil)));
intros [ _ H' ]; generalize (H' H); clear H' H; intro H;
simpl in H; rewrite UTg in H; revert H.
generalize (T.eq_bool_ok (unit_nf s2) (Term u nil)); case (T.eq_bool (unit_nf s2) (Term u nil)); [intro s2_eq_u | intro s2_diff_u].
intro H; left; split.
generalize (acu_is_ac_on_unit_nf (Term f l1) t2); 
intros [H' _]; generalize (H' H); trivial.
rewrite <- s2_eq_u.
unfold acu, th_eq; 
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t2 H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; apply unit_nf_is_sound.
generalize (T.eq_bool_ok (unit_nf t2) (Term u nil)); case (T.eq_bool (unit_nf t2) (Term u nil)); [intro t2_eq_u | intro t2_diff_u].
intro H; right; split.
generalize (acu_is_ac_on_unit_nf (Term f l1) s2); 
intros [H' _]; generalize (H' H); trivial.
rewrite <- t2_eq_u.
unfold acu, th_eq; 
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t2 t2_eq_u H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; apply unit_nf_is_sound.
intro H; absurd (f=g); trivial.
rewrite UTf in H; generalize (ac_top_eq H); 
destruct l1 as [ | s1 [ | t1 [ | u1 l1]]]; trivial.
Qed.

Lemma mutate_free_u_sound :
  forall f g u l1 s2 t2, unit_theory g = U u ->
  (acu (Term f l1) t2 /\ acu (Term u nil) s2) \/
  (acu (Term f l1) s2 /\ acu (Term u nil) t2) ->
  acu (Term f l1) (Term g (s2 :: t2 :: nil)).
Proof.
unfold acu, th_eq; 
intros f g u l1 s2 t2 UTg [ [H u_eq_s2] | [ H u_eq_t2] ].
apply trans_clos_is_trans with t2; trivial.
apply trans_clos_is_trans with (Term g ((Term u nil) :: t2 :: nil)).
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t2 H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; unfold th_eq; apply R_in_rwr_R; left; apply left_unit; right; trivial.
apply general_context; simpl.
apply rwr_list_cons; trivial.
apply trans_clos_is_trans with s2; trivial.
apply trans_clos_is_trans with (Term g (s2 :: (Term u nil) :: nil)).
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t2 u_eq_t2 H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; unfold th_eq; apply R_in_rwr_R; left; apply right_unit; right; trivial.
apply general_context; simpl.
apply rwr_list_tail; apply rwr_list_cons; trivial.
Qed.

Lemma mutate_lu_lu :
  forall f g uf ug s1 t1 s2 t2, f <> g ->
  unit_theory f = LU uf -> unit_theory g = LU ug ->
  acu (Term f (s1 :: t1 :: nil)) (Term g (s2 :: t2 :: nil)) -> 
  (acu (Term g (s2 :: t2 :: nil)) t1 /\ acu (Term uf nil) s1) \/
  (acu (Term f (s1 :: t1 :: nil)) t2 /\ acu (Term ug nil) s2).
Proof.
intros f g uf ug s1 t1 s2 t2 f_diff_g UTf UTg H;
generalize (acu_is_ac_on_unit_nf (Term f (s1 :: t1 :: nil)) (Term g (s2 :: t2 :: nil)));
intros [ _ H' ]; generalize (H' H); clear H' H; intro H; assert (G := H);
simpl in H; rewrite UTf in H; revert H.
generalize (T.eq_bool_ok (unit_nf s1) (Term uf nil)); case (T.eq_bool (unit_nf s1) (Term uf nil)); [intro s1_eq_uf | intro s1_diff_uf].
intro H; left; split.
generalize (acu_is_ac_on_unit_nf (Term g (s2 :: t2 :: nil)) t1); 
intros [H' _]; apply H'; apply th_sym; trivial.
rewrite <- s1_eq_uf.
unfold acu, th_eq; 
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 G H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; apply unit_nf_is_sound.
simpl in G; rewrite UTg in G; revert G.
generalize (T.eq_bool_ok (unit_nf s2) (Term ug nil)); case (T.eq_bool (unit_nf s2) (Term ug nil)); [intro s2_eq_ug | intro s2_diff_ug].
intro G; right; split.
generalize (acu_is_ac_on_unit_nf (Term f (s1 :: t1 :: nil)) t2); 
intros [H' _]; generalize (H' G); trivial.
rewrite <- s2_eq_ug.
unfold acu, th_eq; 
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 G H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; apply unit_nf_is_sound.
intro H; absurd (f=g); trivial.
rewrite UTf in H; generalize (ac_top_eq H).
generalize (T.eq_bool_ok (unit_nf s1) (Term uf nil)); case (T.eq_bool (unit_nf s1) (Term uf nil)); [intro s1_eq_uf | intros _].
absurd (unit_nf s1 = Term uf nil); trivial. 
trivial.
Qed.

Lemma mutate_lu_lu_sound :
  forall f g uf ug s1 t1 s2 t2, 
  unit_theory f = LU uf -> unit_theory g = LU ug ->
  (acu (Term g (s2 :: t2 :: nil)) t1 /\ acu (Term uf nil) s1) \/
  (acu (Term f (s1 :: t1 :: nil)) t2 /\ acu (Term ug nil) s2) ->
  acu (Term f (s1 :: t1 :: nil)) (Term g (s2 :: t2 :: nil)).
Proof.
unfold acu, th_eq;
intros f g uf ug s1 t1 s2 t2 UTf UTg [ [ H s1_eq_uf] | [ H s2_eq_ug ]].
apply trans_clos_is_trans with t1; trivial.
apply trans_clos_is_trans with (Term f ((Term uf nil) :: t1 :: nil)).
apply general_context; simpl.
apply rwr_list_cons; apply th_sym; trivial.
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply R_in_rwr_R; left; apply left_unit; left; trivial.
apply th_sym; trivial.
apply trans_clos_is_trans with t2; trivial.
apply trans_clos_is_trans with (Term g ((Term ug nil) :: t2 :: nil)).
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; unfold th_eq; apply R_in_rwr_R; left; apply left_unit; left; trivial.
apply general_context; simpl.
apply rwr_list_cons; trivial.
Qed.

Lemma mutate_lu_ru :
  forall f g uf ug s1 t1 s2 t2, f <> g ->
  unit_theory f = LU uf -> unit_theory g = RU ug ->
  acu (Term f (s1 :: t1 :: nil)) (Term g (s2 :: t2 :: nil)) -> 
  (acu (Term g (s2 :: t2 :: nil)) t1 /\ acu (Term uf nil) s1) \/
  (acu (Term f (s1 :: t1 :: nil)) s2 /\ acu (Term ug nil) t2).
Proof.
intros f g uf ug s1 t1 s2 t2 f_diff_g UTf UTg H;
generalize (acu_is_ac_on_unit_nf (Term f (s1 :: t1 :: nil)) (Term g (s2 :: t2 :: nil)));
intros [ _ H' ]; generalize (H' H); clear H' H; intro H; assert (G := H);
simpl in H; rewrite UTf in H; revert H.
generalize (T.eq_bool_ok  (unit_nf s1) (Term uf nil)); case (T.eq_bool (unit_nf s1) (Term uf nil)); [intro s1_eq_uf | intro s1_diff_uf].
intro H; left; split.
generalize (acu_is_ac_on_unit_nf (Term g (s2 :: t2 :: nil)) t1); 
intros [H' _]; generalize (H' (th_sym _ _ _ H)); trivial.
rewrite <- s1_eq_uf.
unfold acu, th_eq; 
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 G H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; apply unit_nf_is_sound.
simpl in G; rewrite UTg in G; revert G.
generalize (T.eq_bool_ok (unit_nf t2) (Term ug nil)); case (T.eq_bool (unit_nf t2) (Term ug nil)); [intro t2_eq_ug | intro t2_diff_ug].
intro G; right; split.
generalize (acu_is_ac_on_unit_nf (Term f (s1 :: t1 :: nil)) s2); 
intros [H' _]; generalize (H' G); trivial.
rewrite <- t2_eq_ug.
unfold acu, th_eq; 
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 t2_eq_ug G H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; apply unit_nf_is_sound.
intro H; absurd (f=g); trivial.
rewrite UTf in H; generalize (ac_top_eq H).
generalize (T.eq_bool_ok (unit_nf s1) (Term uf nil)); case (T.eq_bool (unit_nf s1) (Term uf nil)); [intro s1_eq_uf | intros _].
absurd (unit_nf s1 = Term uf nil); trivial. 
trivial.
Qed.

Lemma mutate_lu_ru_sound :
  forall f g uf ug s1 t1 s2 t2, 
  unit_theory f = LU uf -> unit_theory g = RU ug ->
  (acu (Term g (s2 :: t2 :: nil)) t1 /\ acu (Term uf nil) s1) \/
  (acu (Term f (s1 :: t1 :: nil)) s2 /\ acu (Term ug nil) t2) ->
  acu (Term f (s1 :: t1 :: nil)) (Term g (s2 :: t2 :: nil)).
Proof.
unfold acu, th_eq;
intros f g uf ug s1 t1 s2 t2 UTf UTg [ [ H s1_eq_uf ] | [ H t2_eq_ug ] ].
apply trans_clos_is_trans with t1; trivial.
apply trans_clos_is_trans with (Term f ((Term uf nil) :: t1 :: nil)).
apply general_context; simpl.
apply rwr_list_cons; apply th_sym; trivial.
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply R_in_rwr_R; left; apply left_unit; left; trivial.
apply th_sym; trivial.
apply trans_clos_is_trans with s2; trivial.
apply trans_clos_is_trans with (Term g (s2 :: (Term ug nil) :: nil)).
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 t2_eq_ug H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; unfold th_eq; apply R_in_rwr_R; left; apply right_unit; left; trivial.
apply general_context; simpl.
apply rwr_list_tail; apply rwr_list_cons; trivial.
Qed.

Lemma mutate_lu_u :
  forall f g uf ug s1 t1 s2 t2, f <> g ->
  unit_theory f = LU uf -> unit_theory g = U ug ->
  acu (Term f (s1 :: t1 :: nil)) (Term g (s2 :: t2 :: nil)) -> 
  (acu (Term g (s2 :: t2 :: nil)) t1 /\ acu (Term uf nil) s1) \/
  (acu (Term f (s1 :: t1 :: nil)) t2 /\ acu (Term ug nil) s2) \/
  (acu (Term f (s1 :: t1 :: nil)) s2 /\ acu (Term ug nil) t2).
Proof.
intros f g uf ug s1 t1 s2 t2 f_diff_g UTf UTg H;
generalize (acu_is_ac_on_unit_nf (Term f (s1 :: t1 :: nil)) (Term g (s2 :: t2 :: nil)));
intros [ _ H' ]; generalize (H' H); clear H' H; intro H; assert (G := H);
simpl in H; rewrite UTf in H; revert H.
generalize (T.eq_bool_ok (unit_nf s1) (Term uf nil)); case (T.eq_bool (unit_nf s1) (Term uf nil)); [intro s1_eq_uf | intro s1_diff_uf].
intro H; left; split.
generalize (acu_is_ac_on_unit_nf (Term g (s2 :: t2 :: nil)) t1); 
intros [H' _]; generalize (H' (th_sym _ _ _ H)); trivial.
rewrite <- s1_eq_uf.
unfold acu, th_eq; 
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 G H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; apply unit_nf_is_sound.
simpl in G; rewrite UTg in G; revert G;
generalize (T.eq_bool_ok (unit_nf s2) (Term ug nil)); case (T.eq_bool (unit_nf s2) (Term ug nil)); [intro s2_eq_ug | intro s2_diff_ug].
intro G; right; left; split.
generalize (acu_is_ac_on_unit_nf (Term f (s1 :: t1 :: nil)) t2); 
intros [H' _]; generalize (H' G); trivial.
rewrite <- s2_eq_ug.
unfold acu, th_eq; 
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 G H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; apply unit_nf_is_sound.
generalize (T.eq_bool_ok (unit_nf t2) (Term ug nil)); case (T.eq_bool (unit_nf t2) (Term ug nil)); [intro t2_eq_ug | intro t2_diff_ug].
intros G H; right; right; split.
generalize (acu_is_ac_on_unit_nf (Term f (s1 :: t1 :: nil)) s2); 
intros [H' _]; generalize (H' G); trivial.
rewrite <- t2_eq_ug.
unfold acu, th_eq; 
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 t2_eq_ug G H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; apply unit_nf_is_sound.
intros G H; absurd (f=g); trivial.
rewrite UTg in H; generalize (ac_top_eq H);
generalize (T.eq_bool_ok (unit_nf s2) (Term ug nil)); case (T.eq_bool (unit_nf s2) (Term ug nil)); [intro s2_eq_ug | intros _].
absurd (unit_nf s2 = Term ug nil); trivial. 
generalize (T.eq_bool_ok (unit_nf t2) (Term ug nil)); case (T.eq_bool (unit_nf t2) (Term ug nil)); [intro t2_eq_ug | intros _].
absurd (unit_nf t2 = Term ug nil); trivial. 
trivial.
Qed.

Lemma mutate_lu_u_sound :
  forall f g uf ug s1 t1 s2 t2,
  unit_theory f = LU uf -> unit_theory g = U ug ->
  (acu (Term g (s2 :: t2 :: nil)) t1 /\ acu (Term uf nil) s1) \/
  (acu (Term f (s1 :: t1 :: nil)) t2 /\ acu (Term ug nil) s2) \/
  (acu (Term f (s1 :: t1 :: nil)) s2 /\ acu (Term ug nil) t2) ->
  acu (Term f (s1 :: t1 :: nil)) (Term g (s2 :: t2 :: nil)).
Proof.
unfold acu, th_eq;
intros f g uf ug s1 t1 s2 t2 UTf UTg [ [ H s1_eq_uf ] | [ [ H s2_eq_ug ]  |  [ H t2_eq_ug]]].
apply trans_clos_is_trans with t1; trivial.
apply trans_clos_is_trans with (Term f ((Term uf nil) :: t1 :: nil)).
apply general_context; simpl.
apply rwr_list_cons; apply th_sym; trivial.
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply R_in_rwr_R; left; apply left_unit; left; trivial.
apply th_sym; trivial.
apply trans_clos_is_trans with t2; trivial.
apply trans_clos_is_trans with (Term g ((Term ug nil) :: t2 :: nil)).
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; unfold th_eq; apply R_in_rwr_R; left; apply left_unit; right; trivial.
apply general_context; simpl.
apply rwr_list_cons; trivial.
apply trans_clos_is_trans with s2; trivial.
apply trans_clos_is_trans with (Term g (s2 :: (Term ug nil) :: nil)).
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 t2_eq_ug H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; unfold th_eq; apply R_in_rwr_R; left; apply right_unit; right; trivial.
apply general_context; simpl.
apply rwr_list_tail; apply rwr_list_cons; trivial.
Qed.

Lemma mutate_ru_ru :
  forall f g uf ug s1 t1 s2 t2, f <> g ->
  unit_theory f = RU uf -> unit_theory g = RU ug ->
  acu (Term f (s1 :: t1 :: nil)) (Term g (s2 :: t2 :: nil)) -> 
  (acu (Term g (s2 :: t2 :: nil)) s1 /\ acu (Term uf nil) t1) \/
  (acu (Term f (s1 :: t1 :: nil)) s2 /\ acu (Term ug nil) t2).
Proof.
intros f g uf ug s1 t1 s2 t2 f_diff_g UTf UTg H;
generalize (acu_is_ac_on_unit_nf (Term f (s1 :: t1 :: nil)) (Term g (s2 :: t2 :: nil)));
intros [ _ H' ]; generalize (H' H); clear H' H; intro H; assert (G := H);
simpl in H; rewrite UTf in H; revert H.
generalize (T.eq_bool_ok (unit_nf t1) (Term uf nil)); case (T.eq_bool (unit_nf t1) (Term uf nil)); [intro t1_eq_uf | intro t1_diff_uf].
intro H; left; split.
generalize (acu_is_ac_on_unit_nf (Term g (s2 :: t2 :: nil)) s1); 
intros [H' _]; generalize (H' (th_sym _ _ _ H)); trivial.
rewrite <- t1_eq_uf.
unfold acu, th_eq; 
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 t1_eq_uf G H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; apply unit_nf_is_sound.
simpl in G; rewrite UTg in G; revert G.
generalize (T.eq_bool_ok (unit_nf t2) (Term ug nil)); case (T.eq_bool (unit_nf t2) (Term ug nil)); [intro t2_eq_ug | intro t2_diff_ug].
intro G; right; split.
generalize (acu_is_ac_on_unit_nf (Term f (s1 :: t1 :: nil)) s2); 
intros [H' _]; generalize (H' G); trivial.
rewrite <- t2_eq_ug.
unfold acu, th_eq; 
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 t1_diff_uf t2_eq_ug G H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; apply unit_nf_is_sound.
intros G H; absurd (f=g); trivial.
rewrite UTg in H; generalize (ac_top_eq H); 
generalize (T.eq_bool_ok (unit_nf t2) (Term ug nil)); case (T.eq_bool (unit_nf t2) (Term ug nil)); [intro t2_eq_ug | intros _].
absurd (unit_nf t2 = Term ug nil); trivial. 
trivial.
Qed.

Lemma mutate_ru_ru_sound :
  forall f g uf ug s1 t1 s2 t2, 
  unit_theory f = RU uf -> unit_theory g = RU ug ->
  (acu (Term g (s2 :: t2 :: nil)) s1 /\ acu (Term uf nil) t1) \/
  (acu (Term f (s1 :: t1 :: nil)) s2 /\ acu (Term ug nil) t2) ->
  acu (Term f (s1 :: t1 :: nil)) (Term g (s2 :: t2 :: nil)).
Proof.
unfold acu, th_eq;
intros f g uf ug s1 t1 s2 t2 UTf UTg [ [H uf_eq_t1 ] | [H ug_eq_t2]].
apply trans_clos_is_trans with s1; trivial.
apply trans_clos_is_trans with (Term f (s1 :: (Term uf nil) :: nil)).
apply general_context; simpl.
apply rwr_list_tail; apply rwr_list_cons; apply th_sym; trivial.
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 uf_eq_t1 H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply R_in_rwr_R; left; apply right_unit; left; trivial.
apply th_sym; trivial.
apply trans_clos_is_trans with s2; trivial.
apply trans_clos_is_trans with (Term g (s2 :: (Term ug nil) :: nil)).
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 ug_eq_t2 H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; unfold th_eq; apply R_in_rwr_R; left; apply right_unit; left; trivial.
apply general_context; simpl.
apply rwr_list_tail; apply rwr_list_cons; trivial.
Qed.

Lemma mutate_ru_u :
  forall f g uf ug s1 t1 s2 t2, f <> g ->
  unit_theory f = RU uf -> unit_theory g = U ug ->
  acu (Term f (s1 :: t1 :: nil)) (Term g (s2 :: t2 :: nil)) -> 
  (acu (Term g (s2 :: t2 :: nil)) s1 /\ acu (Term uf nil) t1) \/
  (acu (Term f (s1 :: t1 :: nil)) t2 /\ acu (Term ug nil) s2) \/
  (acu (Term f (s1 :: t1 :: nil)) s2 /\ acu (Term ug nil) t2).
Proof.
intros f g uf ug s1 t1 s2 t2 f_diff_g UTf UTg H;
generalize (acu_is_ac_on_unit_nf (Term f (s1 :: t1 :: nil)) (Term g (s2 :: t2 :: nil)));
intros [ _ H' ]; generalize (H' H); clear H' H; intro H; assert (G := H);
simpl in H; rewrite UTf in H; revert H.
generalize (T.eq_bool_ok (unit_nf t1) (Term uf nil)); case (T.eq_bool (unit_nf t1) (Term uf nil)); [intro t1_eq_uf | intro t1_diff_uf].
intro H; left; split.
generalize (acu_is_ac_on_unit_nf (Term g (s2 :: t2 :: nil)) s1); 
intros [H' _]; generalize (H' (th_sym _ _ _ H)); trivial.
rewrite <- t1_eq_uf.
unfold acu, th_eq;
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 t1_eq_uf G H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; apply unit_nf_is_sound.
simpl in G; rewrite UTg in G; revert G;
generalize (T.eq_bool_ok (unit_nf s2) (Term ug nil)); case (T.eq_bool (unit_nf s2) (Term ug nil)); [intro s2_eq_ug | intro s2_diff_ug].
intro G; right; left; split.
generalize (acu_is_ac_on_unit_nf (Term f (s1 :: t1 :: nil)) t2); 
intros [H' _]; generalize (H' G); trivial.
rewrite <- s2_eq_ug.
unfold acu, th_eq; 
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 t1_diff_uf G H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; apply unit_nf_is_sound.
generalize (T.eq_bool_ok (unit_nf t2) (Term ug nil)); case (T.eq_bool (unit_nf t2) (Term ug nil)); [intro t2_eq_ug | intro t2_diff_ug].
right; right; split.
generalize (acu_is_ac_on_unit_nf (Term f (s1 :: t1 :: nil)) s2); 
intros [H' _]; generalize (H' G); trivial.
rewrite <- t2_eq_ug.
unfold acu, th_eq; 
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 t1_diff_uf t2_eq_ug G H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; apply unit_nf_is_sound.
intros G H; absurd (f=g); trivial.
rewrite UTg in H; generalize (ac_top_eq H);
generalize (T.eq_bool_ok (unit_nf s2) (Term ug nil)); case (T.eq_bool (unit_nf s2) (Term ug nil)); [intro s2_eq_ug | intros _].
absurd (unit_nf s2 = Term ug nil); trivial. 
generalize (T.eq_bool_ok (unit_nf t2) (Term ug nil)); case (T.eq_bool (unit_nf t2) (Term ug nil)); [intro t2_eq_ug | intros _].
absurd (unit_nf t2 = Term ug nil); trivial. 
trivial.
Qed.

Lemma mutate_ru_u_sound :
  forall f g uf ug s1 t1 s2 t2,
  unit_theory f = RU uf -> unit_theory g = U ug ->
  (acu (Term g (s2 :: t2 :: nil)) s1 /\ acu (Term uf nil) t1) \/
  (acu (Term f (s1 :: t1 :: nil)) t2 /\ acu (Term ug nil) s2) \/
  (acu (Term f (s1 :: t1 :: nil)) s2 /\ acu (Term ug nil) t2) ->
  acu (Term f (s1 :: t1 :: nil)) (Term g (s2 :: t2 :: nil)).
Proof.
unfold acu, th_eq;
intros f g uf ug s1 t1 s2 t2 UTf UTg [ [ H t1_eq_uf ] | [ [ H s2_eq_ug ]  |  [ H t2_eq_ug]]].
apply trans_clos_is_trans with s1; trivial.
apply trans_clos_is_trans with (Term f (s1 :: (Term uf nil) :: nil)).
apply general_context; simpl.
apply rwr_list_tail; apply rwr_list_cons; apply th_sym; trivial.
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 t1_eq_uf H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply R_in_rwr_R; left; apply right_unit; left; trivial.
apply th_sym; trivial.
apply trans_clos_is_trans with t2; trivial.
apply trans_clos_is_trans with (Term g ((Term ug nil) :: t2 :: nil)).
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; unfold th_eq; apply R_in_rwr_R; left; apply left_unit; right; trivial.
apply general_context; simpl.
apply rwr_list_cons; trivial.
apply trans_clos_is_trans with s2; trivial.
apply trans_clos_is_trans with (Term g (s2 :: (Term ug nil) :: nil)).
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 t2_eq_ug H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; unfold th_eq; apply R_in_rwr_R; left; apply right_unit; right; trivial.
apply general_context; simpl.
apply rwr_list_tail; apply rwr_list_cons; trivial.
Qed.

Lemma mutate_u_u :
  forall f g uf ug s1 t1 s2 t2, f <> g ->
  unit_theory f = U uf -> unit_theory g = U ug ->
  acu (Term f (s1 :: t1 :: nil)) (Term g (s2 :: t2 :: nil)) -> 
  (acu (Term g (s2 :: t2 :: nil)) t1 /\ acu (Term uf nil) s1) \/
  (acu (Term g (s2 :: t2 :: nil)) s1 /\ acu (Term uf nil) t1) \/
  (acu (Term f (s1 :: t1 :: nil)) t2 /\ acu (Term ug nil) s2) \/
  (acu (Term f (s1 :: t1 :: nil)) s2 /\ acu (Term ug nil) t2).
Proof.
intros f g uf ug s1 t1 s2 t2 f_diff_g UTf UTg H;
generalize (acu_is_ac_on_unit_nf (Term f (s1 :: t1 :: nil)) (Term g (s2 :: t2 :: nil)));
intros [ _ H' ]; generalize (H' H); clear H' H; intro H; assert (G := H);
simpl in H; rewrite UTf in H; revert H.
generalize (T.eq_bool_ok (unit_nf s1) (Term uf nil)); case (T.eq_bool (unit_nf s1) (Term uf nil)); [intro s1_eq_uf | intro s1_diff_uf].
intro H; left; split.
generalize (acu_is_ac_on_unit_nf (Term g (s2 :: t2 :: nil)) t1); 
intros [H' _]; generalize (H' (th_sym _ _ _ H)); trivial.
rewrite <- s1_eq_uf.
unfold acu, th_eq; 
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 G H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; apply unit_nf_is_sound.
generalize (T.eq_bool_ok (unit_nf t1) (Term uf nil)); case (T.eq_bool (unit_nf t1) (Term uf nil)); [intro t1_eq_uf | intro t1_diff_uf].
intro H; right; left; split.
generalize (acu_is_ac_on_unit_nf (Term g (s2 :: t2 :: nil)) s1); 
intros [H' _]; generalize (H' (th_sym _ _ _ H)); trivial.
rewrite <- t1_eq_uf.
unfold acu, th_eq; 
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 t1_eq_uf G H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; apply unit_nf_is_sound.
simpl in G; rewrite UTg in G; revert G;
generalize (T.eq_bool_ok (unit_nf s2) (Term ug nil)); case (T.eq_bool (unit_nf s2) (Term ug nil)); [intro s2_eq_ug | intro s2_diff_ug].
intro G; right; right; left; split.
generalize (acu_is_ac_on_unit_nf (Term f (s1 :: t1 :: nil)) t2); 
intros [H' _]; generalize (H' G); trivial.
rewrite <- s2_eq_ug.
unfold acu, th_eq; 
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 t1_diff_uf G H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; apply unit_nf_is_sound.
generalize (T.eq_bool_ok (unit_nf t2) (Term ug nil)); case (T.eq_bool (unit_nf t2) (Term ug nil)); [intro t2_eq_ug | intro t2_diff_ug].
right; right; right; split.
generalize (acu_is_ac_on_unit_nf (Term f (s1 :: t1 :: nil)) s2); 
intros [H' _]; generalize (H' G); trivial.
rewrite <- t2_eq_ug.
unfold acu, th_eq; 
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 t1_diff_uf t2_eq_ug G H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; apply unit_nf_is_sound.
intros G H; absurd (f=g); trivial.
rewrite UTg in H; generalize (ac_top_eq H);
generalize (T.eq_bool_ok (unit_nf s2) (Term ug nil)); case (T.eq_bool (unit_nf s2) (Term ug nil)); [intro s2_eq_ug | intros _].
absurd (unit_nf s2 = Term ug nil); trivial. 
generalize (T.eq_bool_ok (unit_nf t2) (Term ug nil)); case (T.eq_bool (unit_nf t2) (Term ug nil)); [intro t2_eq_ug | intros _].
absurd (unit_nf t2 = Term ug nil); trivial. 
trivial.
Qed.

Lemma mutate_u_u_sound :
  forall f g uf ug s1 t1 s2 t2, 
  unit_theory f = U uf -> unit_theory g = U ug ->
  (acu (Term g (s2 :: t2 :: nil)) t1 /\ acu (Term uf nil) s1) \/
  (acu (Term g (s2 :: t2 :: nil)) s1 /\ acu (Term uf nil) t1) \/
  (acu (Term f (s1 :: t1 :: nil)) t2 /\ acu (Term ug nil) s2) \/
  (acu (Term f (s1 :: t1 :: nil)) s2 /\ acu (Term ug nil) t2) ->
 acu (Term f (s1 :: t1 :: nil)) (Term g (s2 :: t2 :: nil)).
Proof.
unfold acu, th_eq;
intros f g uf ug s1 t1 s2 t2 UTf UTg
[ [H uf_eq_s1] | [ [ H uf_eq_t1 ] | [ [ H ug_eq_s2 ] | [ ug_eq_t2 H ] ]]].
apply trans_clos_is_trans with (Term f ((Term uf nil) :: t1 :: nil)).
apply general_context; simpl.
apply rwr_list_cons; apply th_sym; trivial.
apply trans_clos_is_trans with t1; trivial.
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply R_in_rwr_R; left; apply left_unit; right; trivial.
apply th_sym; trivial.

apply trans_clos_is_trans with (Term f (s1 :: (Term uf nil) :: nil)).
apply general_context; simpl.
apply rwr_list_tail; apply rwr_list_cons; apply th_sym; trivial.
apply trans_clos_is_trans with s1.
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 uf_eq_t1 H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply R_in_rwr_R; left; apply right_unit; right; trivial.
apply th_sym; trivial.

apply trans_clos_is_trans with (Term g ((Term ug nil) :: t2 :: nil)).
apply trans_clos_is_trans with t2; trivial.
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; unfold th_eq; apply R_in_rwr_R; left; apply left_unit; right; trivial.
apply general_context; simpl.
apply rwr_list_cons; trivial.
apply trans_clos_is_trans with (Term g (s2 :: (Term ug nil) :: nil)).
apply trans_clos_is_trans with s2; trivial;
apply rwr_incl with (sym_refl unit_one_step_at_top).
clear t1 t2 ug_eq_t2 H; intros t1 t2 [H | [H | H]]; [left | right; left | right; right; trivial];
unfold union; right; trivial.
apply th_sym; unfold th_eq; apply R_in_rwr_R; left; apply right_unit; right; trivial.
apply general_context; simpl.
apply rwr_list_tail; apply rwr_list_cons; trivial.
Qed.

End Make.
