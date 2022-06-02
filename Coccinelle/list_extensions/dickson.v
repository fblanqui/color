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


(**  *Dickson Lemma: the multiset extension of a well-founded ordering is well-founded.
 *)

Set Implicit Arguments. 

From Coq Require Import Relations List Multiset Arith Morphisms FunInd.
From CoLoR Require Import closure more_list list_permut ordered_set.

Ltac dummy a b a_eq_b :=
assert (Dummy : a = b); [exact a_eq_b | clear a_eq_b; rename Dummy into a_eq_b].

Module Type D.

  Declare Module Import DS : decidable_set.S.
  Declare Module Import LP : list_permut.S with Definition EDS.A := DS.A 
                                                                  with Definition EDS.eq_A := (@eq DS.A).

(** ** Definition of the multiset extension of a relation. *)
Inductive multiset_extension_step (R : relation A) : list A -> list A -> Prop :=
  | rmv_case : 
     forall l1 l2 l la a, (forall b, mem EDS.eq_A b la -> R b a) -> 
      permut l1 (la ++ l) -> permut l2 (a :: l) ->
      multiset_extension_step R l1 l2.

(** [multiset_extension_step] is compatible with permutation. *)
Parameter list_permut_multiset_extension_step_1 :
  forall R l1 l2 l, permut l1 l2 -> 
  multiset_extension_step R l1 l -> multiset_extension_step R l2 l.

Parameter list_permut_multiset_extension_step_2 :
  forall R l1 l2 l, permut l1 l2 -> 
  multiset_extension_step R l l1 -> multiset_extension_step R l l2.

Global Declare Instance mult_morph (R : relation A) :
  Proper (permut ==> permut ==> iff) (multiset_extension_step R).

(** *** Accessibility lemmata. *)
Parameter list_permut_acc :
  forall R l1 l2, permut l2 l1 -> 
  Acc (multiset_extension_step R) l1 -> Acc (multiset_extension_step R) l2.

(** Main lemma. *)
Parameter dickson : 
  forall R, well_founded R -> well_founded (multiset_extension_step R).

Parameter dickson_strong : 
  forall R l, (forall a, In a l -> Acc R a) -> Acc (multiset_extension_step R) l.

Parameter context_trans_clos_multiset_extension_step_app1 :
  forall R l1 l2 l, trans_clos (multiset_extension_step R) l1 l2 ->
                         trans_clos (multiset_extension_step R) (l ++ l1) (l ++ l2).

Function consn (ll : list (A * list A)) : list A :=
  match ll with 
  | nil => nil
  | (e,_) :: ll => e:: (consn ll)
  end.

Function appendn (ll : list (A * list A)) : list A :=
  match ll with 
  | nil => nil
  | (_,l) :: ll => l ++ (appendn ll)
  end.

Parameter multiset_closure :
  forall R, (forall x y, {R x y}+{~R x y}) -> transitive _ R ->
  forall p q, trans_clos (multiset_extension_step R) p q ->
  exists l, exists pq,
  permut p ((appendn l) ++ pq) /\
  permut q ((consn l) ++ pq) /\
  l <> nil /\
  (forall a, forall la, In (a,la) l -> forall b, mem EDS.eq_A b la -> R b a) /\
  ((forall a, ~R a a) -> forall a, mem EDS.eq_A a (consn l) -> mem EDS.eq_A a (appendn l) -> False).

End D.

Module Make (DS1 : decidable_set.S).

Module Import DS := decidable_set.Convert (DS1).
Module Import LP := list_permut.Make (DS).




(** ** Definition of the multiset extension of a relation. *)
Inductive multiset_extension_step (R : relation A) : list A -> list A -> Prop :=
  | rmv_case : 
     forall l1 l2 l la a, (forall b, mem EDS.eq_A b la -> R b a) -> 
      permut l1 (la ++ l) -> permut l2 (a :: l) ->
      multiset_extension_step R l1 l2.

(** [multiset_extension_step] is compatible with permutation. *)
Lemma list_permut_multiset_extension_step_1 :
  forall R l1 l2 l, permut l1 l2 -> 
  multiset_extension_step R l1 l -> multiset_extension_step R l2 l.
Proof.
intros R l1 l2 l P M1; inversion M1 as [ k1 k l1' la a la_R_a P1 P2]; subst.
apply (rmv_case (l1:=l2) (l2:=l) (l:=l1') R la la_R_a); trivial.
apply permut_trans with l1.
apply permut_sym; assumption.
assumption.
Qed.

Lemma list_permut_multiset_extension_step_2 :
  forall R l1 l2 l, permut l1 l2 -> 
  multiset_extension_step R l l1 -> multiset_extension_step R l l2.
Proof.
intros R l1 l2 l P M1; inversion M1 as [ k1 k l1' la a la_R_a P1 P2]; subst.
apply (rmv_case (l1:=l) (l2:=l2) (l:=l1') R la la_R_a); trivial.
apply permut_trans with l1.
apply permut_sym; assumption.
assumption.
Defined.

Global Instance mult_morph (R : relation A) :
  Proper (permut ==> permut ==> iff) (multiset_extension_step R).

Proof.
intros l1 l2 P12 l3 l4 P34; split; [intro R13 | intro R24].
apply list_permut_multiset_extension_step_2 with l3; trivial.
apply list_permut_multiset_extension_step_1 with l1; trivial.
apply list_permut_multiset_extension_step_2 with l4; auto;
apply list_permut_multiset_extension_step_1 with l2; auto.
Qed.

(** If n << {a} U m, then 
      either, there exists n' such that n = {a} U n' and n' << m,
      or, there exists k, such that n = k U m, and k << {a}. *)
Lemma two_cases :
 forall R a m n, 
 multiset_extension_step R n (a :: m) ->
 (exists n', permut n (a :: n') /\ 
             multiset_extension_step R n' m) \/
 (exists k, (forall b, mem EDS.eq_A b k -> R b a) /\ 
            permut n (k ++ m)).
Proof.
intros R a m n M; inversion_clear M as [x1 x2 l la b H H0 H1];
generalize (eq_bool_ok a b); case (DS1.eq_bool a b); [intro a_eq_b; subst b | intro a_diff_b].
rewrite <- permut_cons in H1; [idtac | apply (equiv_refl _ _ eq_proof)].
right; exists la; split; trivial.
apply permut_trans with (la ++ l).
assumption.
rewrite <- permut_app1; auto.

left; generalize (remove_is_sound b m); case (@remove A eq_bool b m).
intros m' P; exists (la ++ m'); split.
refine (permut_trans H0 _).
apply permut_trans with (la ++ a :: m').
refine (proj1 (permut_app1 _ _ _) _).
apply permut_sym.
rewrite (@permut_cons b b (a :: m') l).
apply permut_trans with (a :: m).
apply permut_sym; rewrite <- (permut_cons_inside (e1 := a) (e2 := a) m (b :: nil) m').
assumption.
apply (equiv_refl _ _ eq_proof).
assumption.
apply (equiv_refl _ _ eq_proof).
apply permut_sym; rewrite <- (permut_cons_inside (e1 := a) (e2 := a) (la ++ m') la m').
apply permut_refl.
apply (equiv_refl _ _ eq_proof).
apply (rmv_case (l1:=la ++ m') (l2:= m) (l:= m') R la H); auto; 
apply permut_sym; rewrite <- permut_cons_inside; auto.
intro b_not_mem_m; apply False_rect.
assert (b_mem_am : mem EDS.eq_A b (a :: m)).
rewrite (mem_permut_mem b H1); left.
apply (equiv_refl _ _ eq_proof).
simpl in b_mem_am; case b_mem_am; clear b_mem_am.
intro; apply a_diff_b; apply sym_eq; assumption.
exact b_not_mem_m.
Qed.


(** *** Accessibility lemmata. *)
Lemma list_permut_acc :
  forall R l1 l2, permut l2 l1 -> 
  Acc (multiset_extension_step R) l1 -> Acc (multiset_extension_step R) l2.
Proof.
intros R l1 l2 Meq A1; apply Acc_intro; intros l M2;
inversion A1; apply H; subst.
apply list_permut_multiset_extension_step_2 with l2; assumption.
Defined.

Lemma dickson_aux1 :
forall (R : relation A) a,
 (forall b, R b a -> 
  forall m, Acc (multiset_extension_step R) m -> 
            Acc (multiset_extension_step R) (b :: m)) ->
 forall m, Acc (multiset_extension_step R) m -> 
 (forall m', (multiset_extension_step R) m' m -> 
             Acc (multiset_extension_step R) (a :: m')) ->
 Acc (multiset_extension_step R) (a :: m).
Proof. 
intros R a IH2_a m Acc_m IHa_M; apply Acc_intro;
intros n H; elim (two_cases H); clear H.
intros [n' [P M]]; refine (list_permut_acc P _); apply IHa_M; trivial.
intros [k [M P]]; refine (list_permut_acc P _); clear P; induction k; trivial; simpl;
apply IH2_a.
apply M; left.
apply (equiv_refl _ _ eq_proof).
apply IHk; intros; apply M; right; trivial.
Defined.

Lemma dickson_aux2 :
forall R m,
  Acc (multiset_extension_step R) m ->
  forall a, (forall b, R b a -> 
             forall m, Acc (multiset_extension_step R) m -> 
                       Acc (multiset_extension_step R) (b :: m)) ->
   Acc (multiset_extension_step R) (a :: m). 
Proof.
intros R m Acc_m a IH2_a;
apply (Acc_iter  (R:= multiset_extension_step R)
(fun m => Acc (multiset_extension_step R) m -> 
Acc (multiset_extension_step R) (a :: m))); trivial;
clear m Acc_m;
intros m H Acc_m; apply dickson_aux1; trivial;
intros; apply H; trivial;
apply Acc_inv with m; trivial.
Defined.

Lemma dickson_aux3 :
forall R a, Acc R a -> forall m, Acc (multiset_extension_step R) m ->
Acc (multiset_extension_step R) (a :: m).
Proof.
intros R a Acc_a;
apply (Acc_iter  (R:= R)
(fun a => Acc R a -> forall m, Acc (multiset_extension_step R) m -> 
Acc (multiset_extension_step R) (a :: m))); trivial;
clear a Acc_a;
intros a H Acc_a m Acc_m; apply dickson_aux2; trivial;
intros; apply H; trivial;
apply Acc_inv with a; trivial.
Defined.

(** Main lemma. *)
Lemma dickson : 
  forall R, well_founded R -> well_founded (multiset_extension_step R).
Proof.
intros R Wf_R; unfold well_founded in *;
intros m; induction m as [ | a m].
apply Acc_intro; intros m H; inversion_clear H;
absurd (a :: l = nil).
discriminate.
apply (permut_nil (R := eq_A)).
apply permut_sym; trivial.
apply dickson_aux3; trivial.
Defined.

Lemma dickson_strong : 
  forall R l, (forall a, In a l -> Acc R a) -> Acc (multiset_extension_step R) l.
Proof.
intros R m; induction m as [ | a m].
intros _; apply Acc_intro; intros m H; inversion_clear H;
absurd (a :: l = nil).
discriminate.
apply (permut_nil (R := eq_A)).
apply permut_sym; trivial.
intros; apply dickson_aux3.
apply H; left; trivial.
apply IHm; intros; apply H; right; trivial.
Qed.

(** ** More results on transitive closure of mult_step *)

Lemma list_permut_trans_clos_multiset_extension_step_1 :
  forall R l1 l2 l, permut l1 l2 -> 
  (trans_clos (multiset_extension_step R)) l1 l -> 
  (trans_clos (multiset_extension_step R)) l2 l.
Proof.
intros R l1 l1' l P H; induction H as [ l1 l2 H | l1 l2 l3 H1 H2 H3].
apply t_step; apply list_permut_multiset_extension_step_1 with l1; trivial.
apply t_trans with l2; trivial; apply list_permut_multiset_extension_step_1 with l1; trivial.
Qed.

Lemma list_permut_trans_clos_multiset_extension_step_2 :
  forall R l1 l2 l, permut l1 l2 -> 
  (trans_clos (multiset_extension_step R)) l l1 -> 
  (trans_clos (multiset_extension_step R)) l l2.
Proof.
intros R l1 l3 l P H; induction H as [ l1 l2 H | l1 l2 l3' H1 H2 H3].
apply t_step; apply list_permut_multiset_extension_step_2 with l2; trivial.
apply t_trans with l2; trivial; apply H3; trivial.
Qed.

Lemma context_multiset_extension_step_app1 :
  forall R l1 l2 l, multiset_extension_step R l1 l2 ->
                         multiset_extension_step R (l ++ l1) (l ++ l2).
Proof.
intros R l1 l2 l H; destruct H as [l1 l2 l12 la a H P1 P2].
apply (@rmv_case R (l++l1) (l++l2) (l++l12) la a); trivial.
apply permut_trans with (l ++ la ++ l12).
rewrite <- permut_app1; trivial.
do 2 rewrite <- app_ass; rewrite <- permut_app2; trivial.
apply list_permut_app_app.
apply permut_trans with (l ++ a :: l12).
rewrite <- permut_app1; trivial.
apply permut_sym; rewrite <- permut_cons_inside.
apply permut_refl.
apply (equiv_refl _ _ eq_proof).
Qed.

Lemma context_trans_clos_multiset_extension_step_app1 :
  forall R l1 l2 l, trans_clos (multiset_extension_step R) l1 l2 ->
                         trans_clos (multiset_extension_step R) (l ++ l1) (l ++ l2).
Proof.
intros R l1 l2 l H; induction H.
apply t_step; apply context_multiset_extension_step_app1; trivial.
apply t_trans with (l ++ y); trivial.
apply context_multiset_extension_step_app1; trivial.
Qed.

Lemma context_multiset_extension_step_cons :
  forall R, (forall a, ~R a a) -> 
  forall a l1 l2, multiset_extension_step R (a :: l1) (a :: l2) ->
                         multiset_extension_step R l1 l2.
Proof.
intros R irrefl_R a l1 l2 H;
inversion H as [a_l1 a_l2 lc lb b H' P1 P2 H2 H3]; subst.
assert (a_mem_blc : mem EDS.eq_A a (b :: lc)).
apply cons_permut_mem with l2 a; trivial.
apply (equiv_refl _ _ eq_proof).
simpl in a_mem_blc; destruct a_mem_blc as [a_eq_b | a_mem_lc].
dummy a b a_eq_b;
subst b; assert (a_mem_lb_lc : mem EDS.eq_A a (lb ++ lc)).
apply cons_permut_mem with l1 a; trivial.
apply (equiv_refl _ _ eq_proof).
rewrite <- mem_or_app in a_mem_lb_lc.
destruct a_mem_lb_lc as [a_mem_lb | a_mem_lc].
absurd (R a a); [apply (irrefl_R a) | apply H'; trivial].
generalize (mem_split_set _ _ eq_bool_ok _ _ a_mem_lc).
intros [a' [lc' [lc'' [a_eq_a' [H'' _]]]]]; 
dummy a a' a_eq_a';
subst a' lc; apply (rmv_case R (l1:=l1) (l2:= l2) (l:=lc' ++ lc'') lb (a:=a)); trivial.
rewrite <- app_ass in P1; rewrite <- (permut_cons_inside) in P1.
rewrite <- ass_app in P1; trivial.
apply (equiv_refl _ _ eq_proof).
rewrite app_comm_cons in P2; rewrite <- (permut_cons_inside) in P2; trivial.
apply (equiv_refl _ _ eq_proof).

generalize (mem_split_set _ _ eq_bool_ok _ _ a_mem_lc).
intros [a' [lc' [lc'' [a_eq_a' [H'' _]]]]]; 
dummy a a' a_eq_a';
subst a' lc; apply (rmv_case R (l1:=l1) (l2:= l2) (l:=lc' ++ lc'') lb (a:=b)); trivial.
rewrite <- app_ass in P1; rewrite <- (permut_cons_inside) in P1.
rewrite <- ass_app in P1; trivial.
apply (equiv_refl _ _ eq_proof).
rewrite app_comm_cons in P2; rewrite <- (permut_cons_inside) in P2.
simpl  in P2; trivial.
apply (equiv_refl _ _ eq_proof).
Qed.

Lemma remove_context_multiset_extension_step_app1 :
  forall R,  (forall a, ~R a a) -> 
  forall l1 l2 l, multiset_extension_step R (l ++ l1) (l ++ l2) ->
                         multiset_extension_step R l1 l2.
Proof.
intros R irrefl_R l1 l2 l; generalize l1 l2; clear l1 l2; 
induction l as [ | a l]; trivial.
intros l1 l2 H; 
assert (H' : multiset_extension_step R (a :: l1) (a :: l2)).
apply IHl.
apply list_permut_multiset_extension_step_2 with ((a :: l) ++ l2).
simpl; rewrite <- permut_cons_inside; auto.
apply (equiv_refl _ _ eq_proof).
apply list_permut_multiset_extension_step_1 with ((a :: l) ++ l1); trivial.
simpl; rewrite <- permut_cons_inside; auto.
apply (equiv_refl _ _ eq_proof).
apply context_multiset_extension_step_cons with a; trivial.
Qed.

Lemma context_multiset_extension_step_app2 :
  forall R l1 l2 l, multiset_extension_step R l1 l2 ->
                         multiset_extension_step R (l1 ++ l) (l2 ++ l).
Proof.
intros R l1 l2 l H; destruct H as [l1 l2 l12 la a H P1 P2].
apply (@rmv_case R (l1++l) (l2++l) (l12++l) la a); trivial.
rewrite <- app_ass; rewrite <- permut_app2; trivial.
rewrite app_comm_cons; rewrite <- permut_app2; trivial.
Qed.

Function consn (ll : list (A * list A)) : list A :=
  match ll with 
  | nil => nil
  | (e,_) :: ll => e:: (consn ll)
  end.

Lemma mem_consn : 
  forall a ll, mem EDS.eq_A a (consn ll) <-> exists la, In (a,la) ll.
Proof.
intros a ll; split; intro H;
functional induction (consn ll) 
   as [ | H1 b lb ll H2 IH].
contradiction.
simpl in H; destruct H as [a_eq_b | a_in_cnsl].
dummy a b a_eq_b;
exists lb; subst; left; trivial.
destruct (IH a_in_cnsl) as [la H].
exists la; right; trivial.
destruct H; contradiction.
destruct H as [la [ala_eq_blb | ala_in_ll]].
injection ala_eq_blb; intros; subst; left; apply (equiv_refl _ _ eq_proof); trivial.
right; apply IH; exists la; trivial.
Qed.

Lemma consn_app :
 forall ll1 ll2, consn (ll1 ++ ll2) = consn ll1 ++ consn ll2.
Proof.
intros ll1; induction ll1 as [ | [a la] ll1]; simpl; trivial; simpl; 
intros; rewrite IHll1; trivial.
Qed.

Function appendn (ll : list (A * list A)) : list A :=
  match ll with 
  | nil => nil
  | (_,l) :: ll => l ++ (appendn ll)
  end.

Lemma appendn_app :
 forall ll1 ll2, appendn (ll1 ++ ll2) = appendn ll1 ++ appendn ll2.
Proof.
intros ll1; induction ll1 as [ | [a la] ll1]; simpl; trivial; simpl; 
intros; rewrite IHll1; rewrite ass_app; trivial.
Qed.

Lemma in_appendn : 
  forall a ll, mem EDS.eq_A a (appendn ll) -> exists b, exists lb, In (b,lb) ll /\ mem EDS.eq_A a lb.
Proof.
intros a ll H; 
functional induction (appendn ll) 
   as [ | H1 b lb ll H2 IH].
contradiction.
rewrite <- mem_or_app in H; destruct H as [a_mem_lb | a_mem_appl].
exists b; exists lb; split; trivial; left; trivial.
destruct (IH a_mem_appl) as [c [lc [H1 H2]]]; 
exists c; exists lc; split; trivial; right; trivial.
Qed.

Lemma multiset_closure_aux :
  forall (R : relation A) p q l pq, 
  permut p ((appendn l) ++ pq) ->
  permut q ((consn l) ++ pq) ->
  l <> nil ->
  (forall a, forall la, In (a,la) l -> forall b, mem EDS.eq_A b la -> R b a) ->
  trans_clos (multiset_extension_step R) p q.
Proof.
intros R p q l; generalize p q; clear p q; induction l as [ | [x lx] l].
simpl; intros p q pq Pp Pq H; absurd (@nil (A * list A) = nil); trivial.
simpl; intros p q pq Pp Pq _ H.
assert (lx_lt_x : forall b, mem EDS.eq_A b lx -> R b x).
apply H; left; trivial.
destruct l as [ | [y ly] l]; simpl in *.
rewrite <- app_nil_end in Pp.
simpl in Pq; apply t_step. 
exact (rmv_case R lx lx_lt_x Pp Pq).
apply t_trans with (x :: ly ++ (appendn l) ++ pq).
do 2 rewrite app_ass in Pp;
refine (rmv_case R lx lx_lt_x Pp (permut_refl _)).
refine (list_permut_trans_clos_multiset_extension_step_2  
                      (permut_sym Pq) _).
apply (@context_trans_clos_multiset_extension_step_app1 R
            (ly ++ appendn l ++ pq) (y :: consn l ++ pq) (x :: nil)); 
apply (@IHl (ly ++ appendn l ++ pq) (y :: consn l ++ pq) pq); auto.
rewrite ass_app; auto.
discriminate.
intros a la H1 b b_in_la; apply (H a la); trivial; right; trivial.
Qed.

Lemma multiset_closure_aux2 :
  forall (R : relation A) p q le l pq, 
  permut p ((appendn l) ++ pq) ->
  permut q (le ++ (consn l) ++ pq) ->
  l <> nil \/ le <> nil ->
  (forall a, forall la, In (a,la) l -> forall b, mem EDS.eq_A b la -> R b a) ->
  trans_clos (multiset_extension_step R) p q.
Proof.
intros R p q le l pq Pp Pq H H';
apply (@multiset_closure_aux R p q ((map (fun x => (x, @nil A)) le) ++ l) pq).
apply permut_trans with (appendn l ++ pq).
assumption.
rewrite <- permut_app2;
rewrite appendn_app; clear Pq H; induction le as [ | e le]; simpl; auto.
apply permut_trans with (le ++ consn l ++ pq).
assumption.
rewrite ass_app; rewrite <- permut_app2;
rewrite consn_app; clear Pq H; induction le as [ | e le]; simpl; auto.
rewrite <- permut_cons; trivial.
apply (equiv_refl _ _ eq_proof).
intro H''; destruct (app_eq_nil _ _ H'') as [ l_eq_nil le_eq_nil];
destruct H as [le_diff_nil | l_diff_nil].
absurd (l = nil); trivial.
destruct le as [ | e le].
absurd (@nil A = nil); trivial.
discriminate.
clear Pq H; induction le as [ | e le]; simpl; trivial.
intros a la [H | H] b b_in_la; 
[injection H; intros; subst; contradiction | apply (IHle a la); trivial].
Qed.


Module LDS.

Definition A := (A * (list A))%type.
Definition eq_A := @eq A.

Lemma eq_proof : equivalence A eq_A.
unfold eq_A; split.
intro n; apply eq_refl.
intros a1 a2 a3 H1 H2; rewrite H1; assumption.
intros a1 a2 H; rewrite H; apply eq_refl.
Qed.

  Add Relation A eq_A 
  reflexivity proved by (Relation_Definitions.equiv_refl _ _ eq_proof)
    symmetry proved by (Relation_Definitions.equiv_sym _ _ eq_proof)
      transitivity proved by (Relation_Definitions.equiv_trans _ _ eq_proof) as EQA.

Fixpoint eq_bool_list l1 l2: bool :=
     match l1, l2 with
     | nil, nil => true
     | nil, (_ :: _) => false
     | (a1 :: l1), nil => false
     | (a1 :: l1), (a2 :: l2) => if DS1.eq_bool a1 a2 then eq_bool_list l1 l2 else false
     end.

Definition eq_bool al1 al2 : bool :=  
  match al1, al2 with
  | (e1,l1), (e2,l2) => if DS1.eq_bool e1 e2 then eq_bool_list l1 l2 else false
  end.

Lemma eq_bool_ok : forall al1 al2, match eq_bool al1 al2 with true => al1 = al2 | false => ~al1 = al2 end.
Proof.
intros [e1 l1] [e2 l2]; simpl.
generalize (DS1.eq_bool_ok e1 e2); case (DS1.eq_bool e1 e2); [intros e1_eq_e2 | intros e1_diff_e2].
revert l1 l2.
assert (H :  forall l1 l2, match eq_bool_list l1 l2 with true => l1 = l2 | false => ~l1 = l2 end).
fix eq_bool_ok0 1.
intros [ | a1 l1] [ | a2 l2]; simpl.
apply eq_refl.
discriminate.
discriminate.
generalize (DS1.eq_bool_ok a1 a2); case (DS1.eq_bool a1 a2); [intros a1_eq_a2 | intros a1_diff_a2].
generalize (eq_bool_ok0 l1 l2); case (eq_bool_list l1 l2); [intro l1_eq_l2 | intro l1_diff_l2].
subst; apply eq_refl.
intro E; apply l1_diff_l2; injection E; intros; subst; apply eq_refl.
intro E; apply a1_diff_a2; injection E; intros; subst; apply eq_refl.
intros l1 l2; generalize (H l1 l2).
case (eq_bool_list l1 l2); [intro l1_eq_l2 | intro l1_diff_l2].
subst; apply (equiv_refl _ _ eq_proof).
intro E; apply l1_diff_l2; injection E; intros; subst; apply eq_refl.
intro E; apply e1_diff_e2; injection E; intros; subst; apply eq_refl.
Defined.

End LDS.

Module LEDS := decidable_set.Convert(LDS).
Module LLP := list_permut.Make (LEDS).

Lemma permut_consn :
 forall ll1 ll2, LLP.permut ll1 ll2 -> permut (consn ll1) (consn ll2).
Proof.
intros ll1; induction ll1 as [ | [a la] ll1]; simpl; intros ll2 P.
rewrite (permut_nil (LLP.permut_sym P)); simpl; auto.
assert (ala_in_ll2 : In (a,la) ll2).
rewrite <- (in_permut_in P); left; trivial.
destruct (In_split _ _ ala_in_ll2) as [ll2' [ll2'' H]]; subst.
rewrite <- LLP.permut_cons_inside in P.
rewrite consn_app; simpl; rewrite <- permut_cons_inside.
rewrite <- consn_app; apply IHll1; trivial.
apply (equiv_refl _ _ eq_proof).
apply (equiv_refl _ _ LEDS.eq_proof).
Qed.

Lemma permut_appendn :
 forall ll1 ll2, LLP.permut ll1 ll2 -> permut (appendn ll1) (appendn ll2).
Proof.
intros ll1; induction ll1 as [ | [a la] ll1]; simpl; intros ll2 P.
rewrite (permut_nil (LLP.permut_sym P)); simpl; auto.
assert (ala_in_ll2 : In (a,la) ll2).
rewrite <- (in_permut_in P); left; trivial.
destruct (In_split _ _ ala_in_ll2) as [ll2' [ll2'' H]]; subst.
rewrite appendn_app; simpl.
refine (permut_trans _ (list_permut_app_app _ _)).
rewrite <- ass_app.
rewrite <- permut_app1.
refine (permut_trans _ (list_permut_app_app _ _)).
rewrite <- appendn_app; apply IHll1; trivial.
rewrite <- LLP.permut_cons_inside in P; trivial.
apply (equiv_refl _ _ LEDS.eq_proof).
Qed.

Lemma multiset_closure_aux3 :
  forall l lc cns, permut (consn l) (lc ++ cns) ->
               exists ll, exists ll',  LLP.permut l (ll ++ ll') /\ 
                                           permut (consn ll)  lc /\ 
                                           permut (consn ll') cns.
Proof.
assert (H : forall consnl lccns, permut consnl lccns -> 
               forall l lc cns ,  consnl = consn l -> lccns = lc ++ cns ->
               exists ll, exists ll',  LLP.permut l (ll ++ ll') /\ 
                                           permut (consn ll)  lc /\ 
                                           permut (consn ll') cns).
intros consnl lccns P; induction P as [ | a1 a1' consnl k1 k2 H P].
intros [ | [a1 l1] l].
intros [ | c lc].
intros [ | c' cns] H1 H2.
exists (@nil (A * list A)); exists (@nil (A * list A)); simpl; repeat split; auto.
discriminate.
intros cns _ H2; discriminate.
intros lc cns H1; discriminate.
intros [ | [b1 l1] l] lc cns H1 H2.
discriminate.
injection H1; clear H1; intros; subst.
generalize (split_list _ _ _ _ H2); clear H2; intros [[k [H3 H4]] | [k [H3 H4]]]; subst.
generalize (IHP l lc (k ++ k2) (eq_refl _)); rewrite ass_app.
intro IH; generalize (IH (eq_refl _)); clear IH.
intros [ll [ll' [Q1 [Q2 Q3]]]].
exists ll; exists ((b1,l1) :: ll'); simpl; repeat split; trivial.
rewrite <- LLP.permut_cons_inside; [assumption | apply eq_refl].
rewrite <- permut_cons_inside; assumption.
revert H4; case k; [idtac | intros a k']; intro H4.
simpl in H4; subst.
generalize (IHP l k1 k2 (eq_refl _) (eq_refl _)).
intros [ll [ll' [Q1 [Q2 Q3]]]].
exists ll; exists ((b1,l1) :: ll'); repeat split.
rewrite <- LLP.permut_cons_inside; [assumption | apply eq_refl].
rewrite <- app_nil_end; assumption.
simpl; rewrite <- permut_cons; assumption.
injection H4; clear H4; intros; subst a k2.
assert (IH := IHP l (k1 ++ k') cns (eq_refl _)).
rewrite ass_app in IH.
generalize (IH (eq_refl _)); clear IH; intros [ll [ll' [Q1 [Q2 Q3]]]].
exists ((b1, l1) :: ll); exists ll'; repeat split.
simpl; rewrite <- LLP.permut_cons; [assumption | apply eq_refl].
simpl; rewrite <- permut_cons_inside; assumption.
assumption.
intros l lc cns P; apply (H (consn l) (lc ++ cns) P _ _ _ (eq_refl _) (eq_refl _)).
Qed.

Lemma multiset_closure :
  forall R, transitive _ R ->
  forall p q, trans_clos (multiset_extension_step R) p q ->
  exists l, exists pq,
  permut p ((appendn l) ++ pq) /\
  permut q ((consn l) ++ pq) /\
  l <> nil /\
  (forall a, forall la, In (a,la) l -> forall b, mem EDS.eq_A b la -> R b a) /\
  ((forall a, ~R a a) -> forall a, mem EDS.eq_A a (consn l) -> mem EDS.eq_A a (appendn l) -> False).
Proof.
intros R trans_R p q p_lt_q; induction p_lt_q as [p q p_lt_q | p q r p_lt_q q_lt_r].
(* R_step *)
destruct p_lt_q as [p q pq la a la_lt_a Pp Pq].
exists ((a,la) :: nil); exists pq; simpl; repeat split; auto.
rewrite <- app_nil_end; auto.
discriminate.
intros x lx [H | H] b b_in_lx; 
[injection H; intros; subst; apply la_lt_a; trivial | contradiction].
rewrite <- app_nil_end; intros irrefl_R b [a_eq_b | Abs] b_in_la.
dummy b a a_eq_b;
subst b; apply (irrefl_R a); apply la_lt_a; trivial.
contradiction.

(* Transitive step *)
destruct p_lt_q as [p q pq la a la_lt_a Pp Pq].
destruct IHq_lt_r as [l [qr [Pq' [Pr [l_diff_nil [app_lt_cns app_disj_cns]]]]]].
assert (a_in_appl_qr : mem EDS.eq_A a ((appendn l) ++ qr)).
apply (proj1 (mem_permut_mem a Pq')).
apply (proj1 (mem_permut_mem a (permut_sym Pq))).
left; apply (equiv_refl _ _ eq_proof).
rewrite <- mem_or_app in a_in_appl_qr.
generalize (mem_bool_ok _ _ EDS.eq_bool_ok a (appendn l)).
case (mem_bool EDS.eq_bool a (appendn l)); [intro a_in_appl | intro a_not_in_appl].
destruct (in_appendn _ _ a_in_appl) as [x [lx [xlx_in_l a_in_lx]]].
destruct (mem_split_set _ _ eq_bool_ok _ _ a_in_lx) as [a' [lx' [lx'' [a_eq_a' [H _]]]]].
simpl in a_eq_a'; simpl in H; subst lx.
destruct (In_split _ _  xlx_in_l) as [l' [l'' H]]; subst l.
rewrite appendn_app in Pq'; simpl in Pq'; do 3 rewrite <-  ass_app in Pq'.
simpl in Pq'; rewrite ass_app in Pq'.
generalize (permut_trans (permut_sym Pq) Pq'); clear Pq'; intro Pq'.
rewrite <- permut_cons_inside in Pq'.
rewrite <- ass_app in Pq'.
generalize (remove_equiv_is_sound (consn (l' ++ l'')) la).
destruct (@remove_equiv A eq_bool  (consn (l' ++ l'')) la) as [cns la'].
intros [lc [Pcns [Pla cns_disj_la']]];
destruct (multiset_closure_aux3 (l' ++ l'') lc cns Pcns) as [ll [ll' [P' [H1 H2]]]];
exists ((x, lx' ++ lx'' ++ la' ++ (appendn ll)) :: ll'); exists (lc ++ qr); split.
apply permut_trans with (la ++ pq).
assumption.
apply permut_trans with ((lc ++ la') ++ pq).
rewrite <- permut_app2; trivial.
apply permut_trans with ((lc ++ la') ++ (appendn l' ++ lx' ++ lx'' ++ appendn l'' ++ qr)).
rewrite <- permut_app1; trivial.
simpl; do 5 rewrite ass_app; rewrite <- permut_app2.
refine (permut_trans _ (list_permut_app_app _ _)).
do 5 rewrite <- ass_app; rewrite <- permut_app1.
rewrite ass_app.
refine (permut_trans (list_permut_app_app _ _) _).
do 3 rewrite <- ass_app; do 2 rewrite <- permut_app1.
refine (permut_trans (list_permut_app_app _ _) _).
do 2 rewrite <- ass_app; rewrite <- permut_app1.
do 2 rewrite <- appendn_app; apply permut_appendn; trivial.
split.
rewrite ass_app.
apply permut_trans with (consn (l' ++ (x, lx' ++ a' :: lx'') :: l'') ++ qr).
assumption.
rewrite <- permut_app2;
rewrite consn_app; simpl; apply permut_sym; 
rewrite <- permut_cons_inside.
apply permut_trans with (cns ++ lc).
rewrite <- permut_app2; assumption.
refine (permut_trans (list_permut_app_app _ _) _).
apply permut_trans with  (consn (l' ++ l'')).
apply permut_sym; assumption.
rewrite consn_app; auto.
apply (equiv_refl _ _ eq_proof).
split.
discriminate.
split.
simpl; intros y ly [yly_eq_xly | yly_in_ll''] b b_in_ly.
injection yly_eq_xly; intros; subst y ly; clear yly_eq_xly.
rewrite ass_app in b_in_ly;
rewrite <- mem_or_app in b_in_ly.
destruct b_in_ly as [b_in_lx | b_in_la_app].
apply (app_lt_cns x (lx' ++ a' :: lx'')); trivial.
apply mem_insert; trivial.
rewrite <- mem_or_app in b_in_la_app.
destruct b_in_la_app as [b_in_la | b_in_app].
apply trans_R with a.
apply la_lt_a.
rewrite (mem_permut_mem b Pla); rewrite <- mem_or_app; right; trivial.
apply (app_lt_cns x (lx' ++ a' :: lx'')); trivial.
destruct (in_appendn _ _ b_in_app) as [y [ly [yly_in_ll b_in_ly]]].
apply trans_R with y.
apply (app_lt_cns y ly); trivial; apply in_insert.
rewrite (list_permut.in_permut_in P'); apply in_or_app; left; trivial.
assert (y_in_lc : mem eq_A y lc).
rewrite <- (mem_permut_mem y H1).
rewrite mem_consn; exists ly; trivial.
apply trans_R with a.
apply la_lt_a; rewrite (mem_permut_mem y Pla); rewrite <- mem_or_app; left; trivial.
apply (app_lt_cns x (lx' ++ a' :: lx'')).
apply in_or_app; right; left; apply eq_refl.
rewrite <- mem_or_app; right; left; trivial.
apply (app_lt_cns y ly); trivial; apply in_insert; trivial.
rewrite (list_permut.in_permut_in P').
apply in_or_app; right; trivial.
simpl; intros irrefl_R b [x_eq_b | b_in_cns] b_in_lx_la_app;
do 3 rewrite <- ass_app in b_in_lx_la_app; do 2 rewrite ass_app in b_in_lx_la_app.
dummy b x x_eq_b;
subst b; rewrite <- mem_or_app in b_in_lx_la_app.
destruct b_in_lx_la_app as [b_in_lx_la | b_in_app].
rewrite <- mem_or_app in b_in_lx_la.
destruct b_in_lx_la as [b_in_lx | b_in_la].
apply (irrefl_R x); apply (app_lt_cns x (lx' ++ a' :: lx'')).
apply in_or_app; right; left; apply eq_refl.
apply mem_insert; trivial.
apply (irrefl_R x); apply trans_R with a.
apply la_lt_a; rewrite (mem_permut_mem x Pla); rewrite <- mem_or_app; right; trivial.
apply (app_lt_cns x (lx' ++ a' :: lx'')).
apply in_or_app; right; left; apply eq_refl.
rewrite <- mem_or_app; right; left; trivial.
apply (app_disj_cns irrefl_R x).
rewrite consn_app; rewrite <- mem_or_app; right; left.
apply (equiv_refl _ _ eq_proof).
rewrite <- appendn_app in b_in_app.
rewrite <- (mem_permut_mem x (permut_appendn P')) in b_in_app.
rewrite appendn_app; rewrite <- mem_or_app.
rewrite appendn_app in b_in_app; rewrite <- mem_or_app in b_in_app.
destruct b_in_app as [b_in_app | b_in_app].
left; trivial.
right; simpl; rewrite <- mem_or_app; right; trivial.
simpl; rewrite <- mem_or_app in b_in_lx_la_app.
destruct b_in_lx_la_app as [b_in_lx_la | b_in_app].
simpl; rewrite <- mem_or_app in b_in_lx_la.
destruct b_in_lx_la as [b_in_lx | b_in_la].
apply (app_disj_cns irrefl_R b).
rewrite consn_app; simpl; apply mem_insert; rewrite <- consn_app. 
rewrite (mem_permut_mem b (permut_consn P'));
rewrite consn_app; rewrite <- mem_or_app; right; trivial.
rewrite appendn_app; rewrite <- mem_or_app; right;
simpl; rewrite <- mem_or_app; left; apply mem_insert; trivial.
apply (cns_disj_la' b); trivial.
rewrite <- (mem_permut_mem b H2); trivial.
apply (app_disj_cns irrefl_R b).
rewrite consn_app; simpl; apply mem_insert;
rewrite <- consn_app; rewrite (mem_permut_mem b (permut_consn P'));
rewrite consn_app; rewrite <- mem_or_app; right; trivial.
rewrite <- appendn_app in b_in_app;
rewrite <- (mem_permut_mem b (permut_appendn P')) in b_in_app.
rewrite appendn_app; rewrite <- mem_or_app;
rewrite appendn_app in b_in_app. 
rewrite <- mem_or_app in b_in_app; 
destruct b_in_app as [b_in_app | b_in_app];
[left | simpl; right; rewrite <- mem_or_app; right]; trivial.
trivial.
assert (a_in_qr : mem eq_A a qr).
destruct a_in_appl_qr as [a_in_appl | a_in_qr]; trivial.
absurd (mem eq_A a (appendn l)); trivial.
destruct (mem_split_set _ _ eq_bool_ok _ _ a_in_qr) as [a' [qr' [qr'' [a_eq_a' [H _]]]]]; subst qr.
generalize (permut_trans (permut_sym Pq) Pq'); clear Pq'; intro Pq'.
rewrite ass_app in Pq';
rewrite <- permut_cons_inside in Pq'; rewrite <- ass_app in Pq'.
generalize (remove_equiv_is_sound (consn l) la);
destruct (@remove_equiv A eq_bool (consn l) la) as [cns la'];
intros [lc [Pcns [Pla cns_disj_la']]];
destruct (multiset_closure_aux3 l lc cns Pcns) as [ll [ll' [P' [H1 H2]]]].
exists ((a, la' ++ (appendn ll)) :: ll'); exists (lc ++ (qr' ++ qr'')); split.
simpl; apply permut_trans with (la ++ pq).
assumption.
apply permut_trans with (la ++ (appendn l ++ qr' ++ qr'')).
rewrite <- permut_app1.
assumption.
do 4 rewrite ass_app; do 2 rewrite <- permut_app2.
apply permut_trans with ((lc ++ la') ++ appendn l).
rewrite <- permut_app2; assumption.
rewrite <- ass_app; refine (permut_trans (list_permut_app_app _ _) _);
rewrite <- permut_app2; rewrite <- ass_app;
rewrite <- appendn_app; rewrite <- permut_app1.
apply permut_appendn; assumption.
split.
apply permut_trans with (consn l ++ qr' ++ a' :: qr'').
assumption.
simpl; rewrite ass_app; apply permut_sym; 
rewrite <- permut_cons_inside; trivial.
do 2 rewrite ass_app;
do 2 rewrite <- permut_app2.
apply permut_trans with (consn ll' ++ consn ll).
rewrite <- permut_app1; apply permut_sym; assumption.
rewrite <- consn_app; apply permut_consn.
apply LLP.permut_trans with (ll ++ ll').
apply LLP.list_permut_app_app.
apply LLP.permut_sym; assumption.
split.
discriminate.
split.
intros y ly [yly_eq_aly | yly_in_ll'] b b_in_ly.
injection yly_eq_aly; intros; subst y ly; clear yly_eq_aly.
rewrite <- mem_or_app in b_in_ly.
destruct b_in_ly as [b_in_la' | b_in_app].
apply la_lt_a.
rewrite (mem_permut_mem b Pla).
rewrite <- mem_or_app; right; trivial.
destruct (in_appendn _ _ b_in_app) as [z [lz [zlz_in_ll b_in_lz]]].
apply trans_R with z.
apply (app_lt_cns z lz); trivial.
rewrite (list_permut.in_permut_in P').
apply in_or_app; left; trivial.
apply la_lt_a; rewrite (mem_permut_mem z Pla); rewrite <- mem_or_app; left.
rewrite <- (mem_permut_mem z H1).
rewrite mem_consn; exists lz; trivial.
apply (app_lt_cns y ly); trivial; 
rewrite (list_permut.in_permut_in P'); apply in_or_app; right; trivial.
intros irrefl_R; simpl; rewrite <- ass_app; rewrite ass_app;
intros b b_in_a_cns b_in_la_app.
rewrite <- mem_or_app in b_in_la_app.
destruct b_in_la_app as [b_in_la | b_in_app].
destruct b_in_a_cns as [b_eq_a | b_in_cns].
rewrite <- mem_or_app in b_in_la.
destruct b_in_la as [b_in_la' | b_in_app].
apply (irrefl_R a); apply la_lt_a; rewrite (mem_permut_mem a Pla); 
rewrite <- mem_or_app; right; 
dummy b a b_eq_a;
subst; trivial.
destruct (in_appendn _ _ b_in_app) as [z [lz [zlz_in_ll b_in_lz]]].
apply (irrefl_R a); apply trans_R with z.
apply (app_lt_cns z lz); subst; trivial.
rewrite (list_permut.in_permut_in P').
apply in_or_app; left; trivial.
apply (mem_eq_mem eq_proof) with b; assumption.
apply la_lt_a; rewrite (mem_permut_mem z Pla); 
rewrite <- mem_or_app; left; rewrite <- (mem_permut_mem z H1).
rewrite mem_consn; exists lz; trivial.
rewrite <- mem_or_app in b_in_la.
destruct b_in_la as [b_in_la' | b_in_app].
apply (cns_disj_la' b); trivial; rewrite <- (mem_permut_mem b H2); trivial.
apply (app_disj_cns irrefl_R b).
rewrite (mem_permut_mem b (permut_consn P')); rewrite consn_app; 
rewrite <- mem_or_app; right; trivial.
rewrite (mem_permut_mem b (permut_appendn P')); rewrite appendn_app; 
rewrite <- mem_or_app; left; trivial.
destruct b_in_a_cns as [b_eq_a | b_in_cns].
dummy b a b_eq_a;
subst b.
apply a_not_in_appl;
rewrite (mem_permut_mem a (permut_appendn P'));
rewrite appendn_app; rewrite <- mem_or_app; right; trivial.
apply (app_disj_cns irrefl_R b).
rewrite (mem_permut_mem b (permut_consn P')); rewrite consn_app; 
rewrite <- mem_or_app; right; trivial.
rewrite (mem_permut_mem b (permut_appendn P')); rewrite appendn_app; 
rewrite <- mem_or_app; right; trivial.
simpl; trivial.
Qed.

Lemma context_trans_clos_multiset_extension_step_cons :
  forall R, transitive _ R -> (forall a, ~R a a) -> 
  forall a l1 l2, trans_clos (multiset_extension_step R) (a :: l1) (a :: l2) ->
                         trans_clos (multiset_extension_step R) l1 l2.
Proof.
intros R trans_R irrefl_R a l1 l2 H.
destruct (multiset_closure trans_R H)
    as [ll [q [P1 [P2 [p_diff_nil [app_lt_cns cns_disj_app]]]]]].
generalize (mem_bool_ok _ _ eq_bool_ok a q).
case (mem_bool DS1.eq_bool a q); [intro a_in_q | intro a_not_in_q].
destruct (mem_split_set _ _ eq_bool_ok _ _ a_in_q) as [a' [q' [q'' [a_eq_a' [H' _]]]]]; 
simpl in a_eq_a'; simpl in H'; subst q.
rewrite ass_app in P1; rewrite <- permut_cons_inside in P1; 
rewrite <- ass_app in P1.
rewrite ass_app in P2; rewrite <- permut_cons_inside in P2; 
rewrite <- ass_app in P2.
apply (multiset_closure_aux R (q' ++ q'') P1 P2 p_diff_nil).
intros a'' la ala'_in_ll; apply app_lt_cns; trivial.
trivial.
trivial.
apply False_rect; apply (cns_disj_app irrefl_R a).
assert (a_in_cns_ll_q : mem eq_A a (consn ll ++ q)).
rewrite <- (mem_permut_mem a P2); left; trivial.
apply (equiv_refl _ _ eq_proof).
rewrite <- mem_or_app in a_in_cns_ll_q.
destruct a_in_cns_ll_q as [a_in_cns_ll | a_in_q]; 
[trivial | absurd (mem eq_A a q); trivial; intro].
assert (a_in_app_ll_q : mem eq_A a (appendn ll ++ q)).
rewrite <- (mem_permut_mem a P1); left; trivial.
apply (equiv_refl _ _ eq_proof).
rewrite <- mem_or_app in a_in_app_ll_q.
destruct a_in_app_ll_q as [a_in_app_ll | a_in_q]; 
[trivial | absurd (mem eq_A a q); trivial].
Qed.

Lemma remove_context_trans_clos_multiset_extension_step_app1 :
  forall R, transitive _ R -> (forall a, ~R a a) -> 
  forall l1 l2 l, trans_clos (multiset_extension_step R) (l ++ l1) (l ++ l2) ->
                         trans_clos (multiset_extension_step R) l1 l2.
Proof.
intros R trans_R irrefl_R l1 l2 l; generalize l1 l2; clear l1 l2; 
induction l as [ | a l]; trivial.
intros l1 l2 H; apply IHl;
apply context_trans_clos_multiset_extension_step_cons with a; trivial.
Qed.

Lemma nil_is_the_smallest :
  forall R e l, trans_clos (multiset_extension_step R) nil (e :: l).
Proof.
intros R e' l; generalize e'; clear e'; induction l as [ | e l].
intros e; apply t_step; refine (@rmv_case _ _ _ nil nil e _ _ _); auto; contradiction.
intros e'; apply trans_clos_is_trans with (e' :: l); trivial.
apply t_step; refine (@rmv_case _ _ _ (e' :: l) nil e _ _ _); auto.
contradiction.
rewrite <- (permut_cons_inside (e1 := e') (e2 := e') (e :: l) (e :: nil) l).
auto.
apply (equiv_refl _ _ eq_proof).
Qed.

Section Mult.

Variable R : relation A.
Variable R_bool : A -> A -> bool.
Variable R_bool_ok : 
   forall a1 a2, 
   match R_bool a1 a2 with
   | true => R a1 a2
   | false => ~ R a1 a2
   end.

Definition mult (l1 l2 : list A) : comp :=
  match remove_equiv eq_bool l1 l2 with
    | (nil, nil) => Equivalent
    | (l1, l2) => 
	match list_forall (fun t2 => list_exists (fun t1 => R_bool t2 t1) l1) l2 with
        | true => Greater_than
	| false =>
	  match list_forall (fun t1 => list_exists (fun t2 => R_bool t1 t2) l2) l1 with
	  | true => Less_than
	  | false => Uncomparable
          end
     end
end.

Lemma greater_case :
   forall l1 l2, (forall a, mem eq_A a l1 -> mem eq_A a l2 -> False) ->
  list_forall (fun t2 => list_exists (fun t1 => R_bool t2 t1) l1) l2 = true ->
   exists le, exists ll, permut l1 (consn ll ++ le) /\
                              permut  l2 (appendn ll) /\
                              (forall a la, In (a,la) ll -> forall b, mem eq_A b la -> R b a).
Proof. 
intros l1 l2; revert l2 l1.
fix greater_case 1.
intros [ | a2 l2].
intros [ | a1 l1]; simpl.
intros _ _; exists (@nil A);  exists (@nil (A * list A)); simpl; intuition.
intros _ _; exists (a1 :: l1); exists (@nil (A * list A)); simpl; intuition.
intros l1 E; simpl.
generalize (list_exists_is_sound (fun t1 : A => R_bool a2 t1) l1);
case (list_exists (fun t1 : A => R_bool a2 t1) l1).
intro H; generalize (proj1 H (eq_refl _)); clear H;
intros [a1 [a1_in_l1 a2_R_a1]].
assert (a2_R_a1' : R a2 a1).
generalize (R_bool_ok a2 a1); rewrite a2_R_a1; trivial.
assert (E' : forall x : A, mem eq_A x l1 -> mem eq_A x l2 -> False).
intros x x_in_l1 x_in_l2; apply (E x); [idtac | right]; assumption.
generalize (greater_case l2 l1 E'); simpl.
case (list_forall (fun t2 : A => list_exists (fun t1 : A => R_bool t2 t1) l1) l2).
case_eq l1; [intros l1_eq_nil | intros b1 k1 H]; subst l1.
contradiction.
intros H1 H2; generalize (H1 H2); clear H1 H2; intros [le [ll [P1 [P2 app_lt_cns]]]].
assert (a1_mem_cns_ll_le : mem eq_A a1 (consn ll ++ le)).
rewrite <- (mem_permut_mem a1 P1); apply in_impl_mem; trivial.
intro; apply (equiv_refl _ _ eq_proof).
rewrite <- mem_or_app in a1_mem_cns_ll_le.
case a1_mem_cns_ll_le; [intro a1_mem_cns_ll | intro a1_mem_le].
generalize (proj1 (mem_consn _ _) a1_mem_cns_ll); intros [la ala_in_ll].
generalize (In_split _ _ ala_in_ll); intros [ll' [ll'' H]]; subst ll.
exists le; exists (ll' ++ (a1, a2 :: la) :: ll''); split.
rewrite consn_app; simpl; rewrite consn_app in P1; simpl in P1; trivial.
split.
rewrite appendn_app; simpl; rewrite <- permut_cons_inside;
rewrite appendn_app in P2; simpl in P2; trivial.
apply (equiv_refl _ _ eq_proof).
intros x lx xlx_in_ll b b_in_lx;
case (in_app_or _ _ _ xlx_in_ll); [intros xlx_ll' | intros [xlx_eq_a1la | xlx_in_ll'']].
apply (app_lt_cns x lx); trivial; apply in_or_app; left; trivial.
injection xlx_eq_a1la; intros; subst x lx.
case b_in_lx; [intros b_eq_a2 | intros b_in_la];
 [dummy b a2 b_eq_a2; subst b | apply (app_lt_cns a1 la)]; trivial.
apply (app_lt_cns x lx); trivial; apply in_or_app; do 2 right; trivial.

generalize (mem_split_set _ _ eq_bool_ok _ _ a1_mem_le); intros [a1' [le' [le'' [a1_eq_a1' [H _]]]]]; 
simpl in a1_eq_a1'; simpl in H; subst le.
exists (le' ++ le''); exists ((a1, a2 :: nil) :: ll); split.
simpl.
apply permut_trans with (consn ll ++ le' ++ a1' :: le'').
assumption.
rewrite ass_app; apply permut_sym;
rewrite <- permut_cons_inside; trivial.
rewrite ass_app; auto.
split.
simpl; rewrite <- permut_cons; trivial.
apply (equiv_refl _ _ eq_proof).
intros x lx [xlx_eq_a1_e2 | xlx_in_ll] b b_in_lx.
injection xlx_eq_a1_e2; intros; subst x lx;
case b_in_lx; [intros b_eq_e2 | intros Abs]; 
[dummy b a2 b_eq_e2; subst b; trivial | contradiction].
apply (app_lt_cns x lx); trivial; right; trivial.
intros _.
case (list_forall
      (fun t1 : A =>
       Bool.ifb (R_bool t1 a2) true
         (list_exists (fun t2 : A => R_bool t1 t2) l2)) l1); case l1; intros; discriminate.

intros _; simpl.
case (list_forall
         (fun t1 : A =>
          Bool.ifb (R_bool t1 a2) true
            (list_exists (fun t2 : A => R_bool t1 t2) l2)) l1); case l1; intros; discriminate.
Qed.

Lemma mult_is_sound :
 forall l1 l2,
  match mult l1 l2 with
  | Equivalent => permut l1 l2
  | Less_than => trans_clos (multiset_extension_step R) l1 l2
  | Greater_than => trans_clos (multiset_extension_step R) l2 l1
  | _ => True
  end.
Proof.
intros l1 l2; unfold mult; 
generalize (remove_equiv_is_sound l1 l2).
unfold A in *.
case (@remove_equiv DS1.A eq_bool l1 l2); intros k1 k2 [l [P1 [P2 E]]].
revert P1 P2 E; case k1; [ idtac| intros e1' l1']; (case k2; [ idtac | intros e2' l2']); intros P1 P2 E.
apply permut_trans with (l ++ nil).
assumption.
apply permut_sym; assumption.
simpl; rewrite <- app_nil_end in P1;
apply (multiset_closure_aux2 R (p := l1) (q := l2) 
                      (le := e2' :: l2') (l := nil) l); simpl; auto.
apply permut_trans with (l ++ e2' :: l2').
assumption.
rewrite app_comm_cons; apply list_permut_app_app.
right; discriminate.
intros; contradiction.
simpl; rewrite <- app_nil_end in P2;
apply (multiset_closure_aux2 R (p := l2) (q := l1) 
                      (le := e1' :: l1') (l := nil) l); simpl; auto.
apply permut_trans with (l ++ e1' :: l1').
assumption.
rewrite app_comm_cons; apply list_permut_app_app.
right; discriminate.
intros; contradiction.
generalize (greater_case (e1' :: l1') (e2' :: l2') E); unfold A in *.
case (list_forall (fun t2 : DS1.A => list_exists (fun t1 : DS1.A => R_bool t2 t1) (e1' :: l1')) (e2' :: l2')).
intro H; generalize (H (eq_refl _)); clear H; intros [le [ll [P1' [P2' app_lt_cns]]]].
apply (multiset_closure_aux2 R (p := l2) (q := l1) (le := le)  (l := ll) l); simpl; auto.
apply permut_trans with (l ++ e2' :: l2').
assumption.
apply permut_trans with (l ++ appendn ll).
rewrite <- permut_app1; assumption.
apply list_permut_app_app.
apply permut_trans with (l ++ e1' :: l1').
assumption.
apply permut_trans with (l ++ consn ll ++ le).
rewrite <- permut_app1; assumption.
apply permut_trans with (l ++ le ++ consn ll).
rewrite <- permut_app1; apply list_permut_app_app.
rewrite (ass_app le); apply list_permut_app_app.
destruct ll as [ | [x lx] ll].
destruct le as [ | e le].
generalize (permut_length P1'); simpl; intro; 
absurd (S (length l1') = 0); trivial; discriminate.
right; discriminate.
left; discriminate.
assert (E' : forall x : DS1.A, mem eq_A x (e2' :: l2') -> mem eq_A x (e1' :: l1') -> False).
intros x H2 H1; apply (E x H1 H2).
intros _; generalize (greater_case (e2' :: l2') (e1' :: l1') E'); unfold A in *;
case (list_forall (fun t1 : DS1.A => list_exists (fun t2 : DS1.A => R_bool t1 t2) (e2' :: l2')) (e1' :: l1')).
intro H; generalize (H (eq_refl _)); clear H; intros [le [ll [P2' [P1' app_lt_cns]]]].
apply (multiset_closure_aux2 R (p := l1) (q := l2) (le := le)  (l := ll) l); simpl; auto.
apply permut_trans with (l ++ e1' :: l1').
assumption.
apply permut_trans with (l ++ appendn ll).
rewrite <- permut_app1; assumption.
apply list_permut_app_app.
apply permut_trans with (l ++ e2' :: l2').
assumption.
apply permut_trans with (l ++ consn ll ++ le).
rewrite <- permut_app1; assumption.
apply permut_trans with (l ++ le ++ consn ll).
rewrite <- permut_app1; apply list_permut_app_app.
rewrite (ass_app le); apply list_permut_app_app.
destruct ll as [ | [x lx] ll].
destruct le as [ | e le].
generalize (permut_length P2'); simpl; intro; 
absurd (S (length l2') = 0); trivial; discriminate.
right; discriminate.
left; discriminate.
trivial.
Defined.

Lemma mult_is_complete_equiv :
 forall l1 l2, permut l1 l2 -> mult l1 l2 = Equivalent.
Proof.
intros l1 l2 P; 
assert (P1 : permut l1 (l1 ++ nil)).
rewrite <- app_nil_end; apply permut_refl.
assert (P2 : permut l2 (l1 ++ nil)).
rewrite <- app_nil_end; apply permut_sym; assumption.
assert (E : forall x : A, mem eq_A x nil -> mem eq_A x nil -> False).
intros; contradiction.
generalize (@remove_equiv_is_complete l1 l2 l1 nil nil P1 P2 E).
unfold mult; unfold A in *; case (@remove_equiv DS1.A eq_bool l1 l2); intros k1 k2 [Q1 Q2].
simpl in Q1; rewrite (permut_nil Q1).
simpl in Q2; rewrite (permut_nil Q2).
apply eq_refl.
Defined.

Lemma mult_is_complete_greater_aux :
 transitive _ R -> (forall a, ~ R a a) ->
 forall l l1 l2, (forall a, mem eq_A a l1 -> mem eq_A a l2 -> False) ->
   trans_clos (multiset_extension_step R) (l ++ l2) (l ++ l1) -> 
	(list_forall (fun t2 => list_exists (fun t1 => R_bool t2 t1) l1) l2) = true.
Proof.
intros trans_R irrefl_R l l1 l2 l2_disj_l1 ll2_lt_ll1.
assert (l2_lt_l1 := remove_context_trans_clos_multiset_extension_step_app1 trans_R irrefl_R l2 l1 l ll2_lt_ll1).
clear l ll2_lt_ll1.
generalize (multiset_closure trans_R l2_lt_l1).
intros [ll [lc [P2 [P1 [ll_diff_nil [app_lt_cns cns_disj_app]]]]]].
generalize (cns_disj_app irrefl_R); clear cns_disj_app; intro cns_disj_app.
assert (lc_eq_nil : lc = nil).
revert P2 P1 cns_disj_app.
case lc; clear lc; [intros _ _ _; apply eq_refl | intros c lc P2 P1 cns_disj_app].
apply False_rect.
apply (l2_disj_l1 c).
rewrite (mem_permut_mem c P1); rewrite <- mem_or_app; right; left; apply (equiv_refl _ _ eq_proof).
rewrite (mem_permut_mem c P2); rewrite <- mem_or_app; right; left; apply (equiv_refl _ _ eq_proof).
subst lc; rewrite <- app_nil_end in P1; rewrite <- app_nil_end in P2.
assert (Compat : forall ta ta' tb tb' : A, eq_A ta tb -> eq_A ta' tb' -> R_bool ta ta' = R_bool tb tb').
unfold eq_A; intros a a' b b' a_eq_a' b_eq_b'; subst; apply eq_refl.
rewrite (permut_list_forall_exists R_bool R_bool Compat P2 P1); 
clear Compat cns_disj_app P1 P2 ll_diff_nil; induction ll as [ | [a la] ll]; simpl; trivial.
rewrite list_forall_app; rewrite Bool.andb_true_iff; split.
generalize la (app_lt_cns a la (or_introl _ (eq_refl _)));
clear la app_lt_cns; intros la la_lt_a; induction la as [ | b la]; trivial.
simpl; generalize (R_bool_ok b a); case (R_bool b a); [intro b_R_a | intro not_b_R_a]; simpl.
apply IHla; intros; apply la_lt_a; right; assumption.
apply False_rect; apply not_b_R_a; apply la_lt_a; left; apply (equiv_refl _ _ eq_proof).
rewrite (list_forall_impl (fun t1 : A => list_exists (fun t2 : A => R_bool t1 t2) (consn ll))
                                        (fun t1 : A =>  Bool.ifb (R_bool t1 a) true
                                                                             (list_exists (fun t2 : A => R_bool t1 t2) (consn ll)))
                                        (appendn ll)).
apply eq_refl.
intros b b_in_all H; case (R_bool b a); simpl; [apply eq_refl | assumption].
apply IHll; intros b lb blb_in_ll; apply app_lt_cns; right; assumption.
Qed.

Lemma mult_irrefl :
 transitive _ R -> (forall a, ~ R a a) -> forall l, trans_clos (multiset_extension_step R) l l -> False.
Proof.
intros trans_R irrefl_R l l_lt_l.
rewrite (app_nil_end l) in l_lt_l.
assert (nil_lt_nil := remove_context_trans_clos_multiset_extension_step_app1 trans_R irrefl_R nil nil l l_lt_l).
clear l l_lt_l.
assert (H : forall l1 l2, trans_clos (multiset_extension_step R) l1 l2 -> l2 = nil -> False).
intros l1 l2 T; induction T as [k1 k2 H | k1 k2 k3 H1 H2]; intros; subst.
inversion H as [l1 l2 l la a la_lt_a P1 P2]; subst.
generalize (permut_length P2); simpl; discriminate.
apply IHH2; apply eq_refl.
apply (H _ _ nil_lt_nil); apply eq_refl.
Qed.

Lemma mult_is_complete_greater :
 transitive _ R -> (forall a, ~ R a a) ->
   forall l1 l2, trans_clos (multiset_extension_step R) l2 l1 -> mult l1 l2 = Greater_than.
Proof.
intros trans_R irrefl_R l1 l2 l2_lt_l1.
generalize (remove_equiv_is_sound l1 l2); unfold mult; unfold A in *; case_eq (remove_equiv eq_bool l1 l2); 
intros k1 k2 H [l [P1 [P2 k1_disj_k2]]].
assert (lk2_lt_lk1 : trans_clos (multiset_extension_step R) (l ++ k2) (l ++ k1)).
apply list_permut_trans_clos_multiset_extension_step_1 with l2; [assumption | idtac].
apply list_permut_trans_clos_multiset_extension_step_2 with l1; assumption.
assert (Dummy := @mult_is_complete_greater_aux trans_R irrefl_R l _ _ k1_disj_k2 lk2_lt_lk1).
unfold A in Dummy; rewrite Dummy; clear Dummy.
revert lk2_lt_lk1; case k1; [idtac | intros _ _ _; apply eq_refl].
case k2; [idtac | intros _ _ _; apply eq_refl].
intro T; apply False_rect.
apply (mult_irrefl trans_R irrefl_R T).
Qed.

Lemma mult_is_complete_less_than :
 transitive _ R -> (forall a, ~ R a a) ->
   forall l1 l2, trans_clos (multiset_extension_step R) l1 l2 -> mult l1 l2 = Less_than.
Proof.
intros trans_R irrefl_R l1 l2 l1_lt_l2.
generalize (multiset_closure trans_R l1_lt_l2).
intros [ll [lc [P1 [P2 [ll_diff_nil [app_lt_cns disj]]]]]].
assert (cns_disj_app := disj irrefl_R); clear disj.
assert (Q1 : permut l1 (lc ++ appendn ll)).
apply permut_trans with (appendn ll ++ lc).
assumption.
apply permut_swapp; apply permut_refl.
assert (Q2 : permut l2 (lc ++ consn ll)).
apply permut_trans with (consn ll ++ lc).
assumption.
apply permut_swapp; apply permut_refl.
assert (app_disj_cns : forall x : A, mem eq_A x (appendn ll) -> mem eq_A x (consn ll) -> False).
intros x x_in_app x_in_cns; apply (cns_disj_app x); assumption.
generalize (remove_equiv_is_complete _ _ _ Q1 Q2 app_disj_cns) (mult_is_sound l1 l2).
unfold mult; unfold A in *; case (@remove_equiv DS1.A eq_bool l1 l2); simpl; intros k1 k2 [Q1' Q2'].
assert (Dummy := mult_is_complete_greater_aux trans_R irrefl_R lc k2 k1).
unfold A in Dummy; rewrite Dummy; clear Dummy.
revert ll_diff_nil Q1' Q2'; case k1.
case k2.
case ll.
intro ll_diff_nil; apply False_rect; apply ll_diff_nil; apply eq_refl.
intros [a la] ll' _ _ Q2'; apply False_rect.
assert (L := permut_length Q2'); discriminate.
intros; apply eq_refl.
clear k1; intros a1 k1 ll_diff_nil Q1' Q2'.
case (list_forall (fun t2 : DS1.A => list_exists (fun t1 : DS1.A => R_bool t2 t1) (a1 :: k1)) k2).
intro l2_lt_l1; apply False_rect.
apply (@mult_irrefl trans_R irrefl_R l1).
apply trans_clos_is_trans with l2; assumption.
intros; apply eq_refl.

intros x x_in_k2 x_in_k1; apply (cns_disj_app x).
rewrite <- (mem_permut_mem x Q2'); assumption.
rewrite <- (mem_permut_mem x Q1'); assumption.
apply list_permut_trans_clos_multiset_extension_step_1 with l1.
apply permut_trans with (k1 ++ lc).
apply permut_trans with (appendn ll ++ lc).
assumption.
rewrite <- permut_app2; apply permut_sym; assumption.
apply permut_swapp; apply permut_refl.
apply list_permut_trans_clos_multiset_extension_step_2 with l2.
apply permut_trans with (k2 ++ lc).
apply permut_trans with (consn ll ++ lc).
assumption.
rewrite <- permut_app2; apply permut_sym; assumption.
apply permut_swapp; apply permut_refl.
assumption.
Defined.

Lemma mult_is_complete : 
 transitive _ R -> (forall a, ~ R a a) ->
 forall l1 l2,
  match mult l1 l2 with
  | Uncomparable => ~ permut l1 l2 /\
                                      ~trans_clos (multiset_extension_step R) l1 l2 /\ 
                                      ~trans_clos (multiset_extension_step R) l2 l1
  | _ => True
  end.
Proof.
intros trans_R irrefl_R l1 l2.
generalize (mult_is_sound l1 l2) (@mult_is_complete_equiv l1 l2) 
                    (@mult_is_complete_greater trans_R irrefl_R l1 l2) (@mult_is_complete_less_than trans_R irrefl_R l1 l2).
case (mult l1 l2); trivial.
intros _ H1 H2 H3; repeat split; intro H.
generalize (H1 H); discriminate.
generalize (H3 H); discriminate.
generalize (H2 H); discriminate.
Qed.

End Mult.

End Make.

Module NatMul := Make (ordered_set.Nat).
