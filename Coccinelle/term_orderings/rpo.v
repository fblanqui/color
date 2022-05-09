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

(* RPO definition extended by Sorin Stratulat by considering a
quasi-ordering for the precedence instead of an ordering. *)

From Coq Require Import Bool Peano List.
From CoLoR Require Import closure more_list equiv_list list_permut dickson.
From Coq Require Import Relations Wellfounded Arith Wf_nat Recdef Program Morphisms Lia.
From CoLoR Require Import term_spec term decidable_set ordered_set.

Import ListNotations.

Set Implicit Arguments.

(** A non-dependant version of lexicographic extension. *)
Definition lex (A B : Type) 
     (eq_bool : A -> A -> bool) 
     (o1 : relation A) (o2 : relation B) (s t : _ * _) :=
  match s with
  | (s1,s2) =>
    match t with
    | (t1,t2) => 
       if eq_bool s1 t1
       then o2 s2 t2
       else o1 s1 t1
     end
   end.

(** Transitivity of  lexicographic extension. *)
Lemma lex_trans :
 forall (A B : Type) (eq_bool : A -> A -> bool) o1 o2
 (eq_bool_ok : forall a1 a2, if eq_bool a1 a2 then a1 = a2 else a1 <> a2), 
 antisymmetric A o1 -> transitive A o1 -> transitive B o2 ->
 transitive _ (lex eq_bool o1 o2).
Proof.
unfold transitive, lex; 
intros A B eq_bool o1 o2 eq_bool_ok A1 T1 T2 p1 p2 p3; 
destruct p1 as [a1 b1]; destruct p2 as [a2 b2]; destruct p3 as [a3 b3].
generalize (eq_bool_ok a1 a2); case (eq_bool a1 a2); [intro a1_eq_a2; subst a1 | intro a1_diff_a2].
generalize (eq_bool_ok a2 a3); case (eq_bool a2 a3); [intro a2_eq_a3; subst a2 | intro a2_diff_a3].
apply T2.
intros _ a2_t_a3; assumption.
generalize (eq_bool_ok a2 a3); case (eq_bool a2 a3); [intro a2_eq_a3; subst a2 | intro a2_diff_a3].
generalize (eq_bool_ok a1 a3); case (eq_bool a1 a3); [intro a1_eq_a3; subst a1 | intro a1_diff_a3].
apply False_rect; apply a1_diff_a2; reflexivity.
intros a1_lt_a3 _; assumption.
generalize (eq_bool_ok a1 a3); case (eq_bool a1 a3); [intro a1_eq_a3; subst a1 | intro a1_diff_a3].
intros a3_lt_a2 a2_lt_a3; absurd (a3 = a2).
assumption.
exact ( A1 a3 a2 a3_lt_a2 a2_lt_a3).
intros a1_lt_a2 a2_lt_a3; exact (T1 _ _ _ a1_lt_a2 a2_lt_a3).
Qed.

(** Well-foundedness of  lexicographic extension. *)
Lemma wf_lex :
  forall A B (eq_bool : A -> A -> bool) o1 o2 
  (eq_bool_ok : forall a1 a2, if eq_bool a1 a2 then a1 = a2 else a1 <> a2), 
  well_founded o1 -> well_founded o2 ->
  well_founded (@lex A B eq_bool o1 o2).
Proof.
intros A B eq_bool o1 o2 eq_bool_ok W1 W2.
intros [a1 a2]; revert a2; generalize (W1 a1); intros Wa1 a2; generalize (W2 a2).
revert a2; induction Wa1 as [a1 Wa1 wf_lex].
intros a2 Wa2.
revert a1 Wa1 wf_lex.
revert a2 Wa2; fix wf_lex2 2.
intros a2 Wa2 a1 Wa1 wf_lex.
apply Acc_intro; intros [b1 b2]; simpl.
generalize (eq_bool_ok b1 a1); case (eq_bool b1 a1); [intro b1_eq_a1 | intro b1_diff_a1].
intros b2_lt_a2; rewrite b1_eq_a1.
apply (wf_lex2 b2 (Acc_inv Wa2 b2_lt_a2) a1 Wa1 wf_lex).
intro b1_lt_a1; exact (wf_lex b1 b1_lt_a1 _ (W2 b2)).
Defined.


(** ** Module Type Precedence, 
** Definition of a precedence. *)

Inductive status_type : Type :=
  | Lex : status_type
  | Mul : status_type.
(*
Module Type Precedence.
Parameter A : Type.
Parameter status : A -> status_type.

Parameter prec : relation A.
Parameter prec_bool : A -> A -> bool.

Parameter prec_bool_ok : forall a1 a2, match prec_bool a1 a2 with true => prec a1 a2 | false => ~prec a1 a2 end.
Parameter prec_antisym : forall s, prec s s -> False.
Parameter prec_transitive : transitive A prec.

End Precedence.
*)

Record Precedence (A : Type) : Type := {
  status : A -> status_type;
  prec : relation A;
  prec_eq: relation A;
  prec_bool : A -> A -> bool;
  prec_eq_bool : A -> A -> bool;
  prec_bool_ok : forall a1 a2, match prec_bool a1 a2 with true => prec a1 a2 | false => ~prec a1 a2 end;
 prec_eq_bool_ok: forall a1 a2, match prec_eq_bool a1 a2 with true => prec_eq a1 a2 | false => ~prec_eq a1 a2 end;
  prec_antisym : forall s, prec s s -> False;
  prec_transitive : transitive A prec;
  prec_eq_transitive: transitive A prec_eq;
  prec_eq_prec1: forall a1 a2 a3, prec a1 a2 -> prec_eq a2 a3 -> prec a1 a3;
  prec_eq_prec2: forall a1 a2 a3, prec a1 a2 -> prec_eq a1 a3 -> prec a3 a2;
  prec_eq_sym : forall s t, prec_eq s t -> prec_eq t s;
  prec_eq_refl : forall s, prec_eq s s;
  prec_eq_status: forall f g, prec_eq f g -> status f = status g;
  prec_not_prec_eq: forall f g, prec f g -> prec_eq f g -> False
}.


(** ** Module Type RPO, 
** Definition of RPO from a precedence on symbols. *)

Module Type RPO.

  Declare Module Import T : Term.
(*Declare Module Import P : Precedence with Definition A:= T.symbol.*)
  Section S.
    Variable P : Precedence T.symbol.
(** ** Definition of rpo.*)
    Inductive equiv : term -> term -> Prop :=
    | Eq : forall t, equiv t t
    | Eq_lex : 
      forall f g l1 l2, status P f = Lex -> status P g = Lex -> prec_eq P f g -> equiv_list_lex l1 l2 -> 
        equiv (Term f  l1) (Term g l2) 
    | Eq_mul :
      forall f g l1 l2,  status P f = Mul -> status P g = Mul -> prec_eq P f g -> permut0 equiv l1 l2 ->
        equiv (Term f l1) (Term g l2)

    with equiv_list_lex : list term -> list term -> Prop :=
    | Eq_list_nil : equiv_list_lex nil nil
    | Eq_list_cons : 
      forall t1 t2 l1 l2, equiv t1 t2 -> equiv_list_lex l1 l2 ->
        equiv_list_lex (t1 :: l1) (t2 :: l2).

    Parameter equiv_in_list : 
      forall f g (f_stat : status P f= Lex) (g_stat: status P g = Lex) l1 l2, length l1 = length l2 -> prec_eq P f g ->
        (forall t1 t2, In (t1, t2) (combine l1 l2) -> equiv  t1  t2) -> 
        equiv (Term f l1) (Term g l2).

(* equiv is actually an equivalence *)
    Parameter equiv_equiv  : Equivalence equiv.

    Parameter equiv_dec : forall t1 t2, {equiv t1 t2}+{~equiv t1 t2}.
(*
Declare Module Import LP : 
    list_permut.S with Definition EDS.A:=term 
                        with Definition EDS.eq_A := equiv.
*)

    Inductive rpo (bb : nat) : term -> term -> Prop :=
    | Subterm : forall f l t s, mem equiv s l -> rpo_eq bb t s -> rpo bb t (Term f l)
    | Top_gt : 
      forall f g l l', prec P g f -> (forall s', mem equiv s' l' -> rpo bb s' (Term f l)) -> 
        rpo bb (Term g l') (Term f l)
    | Top_eq_lex : 
      forall f g l l', status P f = Lex -> status P g = Lex -> prec_eq P f g -> (length l = length l' \/ (length l' <= bb /\ length l <= bb)) -> rpo_lex bb l' l -> 
        (forall s', mem equiv s' l' -> rpo bb s' (Term g l)) ->
        rpo bb (Term f l') (Term g l)
    | Top_eq_mul : 
      forall f g l l', status P f = Mul  -> status P g = Mul -> prec_eq P f g -> rpo_mul bb l' l -> 
        rpo bb (Term f l') (Term g l)

    with rpo_eq (bb : nat) : term -> term -> Prop :=
    | Equiv : forall t t', equiv t t' -> rpo_eq bb t t'
    | Lt : forall s t, rpo bb s t -> rpo_eq bb s t

    with rpo_lex (bb : nat) : list term -> list term -> Prop :=
    | List_gt : forall s t l l', rpo bb s t -> rpo_lex bb (s :: l) (t :: l')
    | List_eq : forall s s' l l', equiv s s' -> rpo_lex bb l l' -> rpo_lex bb (s :: l) (s' :: l')
    | List_nil : forall s l, rpo_lex bb nil (s :: l)

    with rpo_mul ( bb : nat) : list term -> list term -> Prop :=
    | List_mul : forall a lg ls lc l l', 
      permut0 equiv l' (ls ++ lc) -> permut0 equiv l (a :: lg ++ lc) ->
      (forall b, mem equiv b ls -> exists a', mem equiv a' (a :: lg) /\ rpo bb b a') ->
      rpo_mul bb l' l.

(* Two equivalent terms have the same behaviour for rpo *)
    Parameter equiv_rpo_equiv_1 :
      forall bb t t', equiv t t' -> (forall s, rpo bb s t <-> rpo bb s t').

    Parameter equiv_rpo_equiv_2 :
      forall bb t t', equiv t t' -> (forall s, rpo bb t s <-> rpo bb t' s).

    Parameter equiv_rpo_equiv_3 :
      forall bb t t', equiv t t' -> (forall s, rpo_eq bb s t <-> rpo_eq bb s t').

    Parameter equiv_rpo_equiv_4 :
      forall bb t t', equiv t t' -> (forall s, rpo_eq bb t s <-> rpo_eq bb t' s).

(** ** rpo is a preorder, and its reflexive closure is an ordering. *)
    Parameter rpo_closure :
      forall bb s t u, 
        (rpo bb t s -> rpo bb u t -> rpo bb u s) /\
        (rpo bb s t -> rpo bb t s -> False) /\
        (rpo bb s s -> False) /\
        (rpo_eq bb s t -> rpo_eq bb t s -> equiv s  t).

    Parameter rpo_trans : forall bb s t u, rpo bb s t -> rpo bb t u -> rpo bb s u.

(** ** Main theorem: when the precedence is well-founded, so is the rpo. *)
    Parameter wf_rpo :  well_founded (prec P) -> forall bb, well_founded (rpo bb).

(** ** RPO is compatible with the instanciation by a substitution. *)
    Parameter equiv_subst :
      forall s t, equiv s t -> 
        forall sigma, equiv (apply_subst sigma s) (apply_subst sigma t).

    Parameter rpo_subst :
      forall bb s t, rpo bb s t -> 
        forall sigma, rpo bb (apply_subst sigma s) (apply_subst sigma t).

    Parameter rpo_eq_subst :
      forall bb s t, rpo_eq bb s t -> 
        forall sigma, rpo_eq bb (apply_subst sigma s) (apply_subst sigma t).

(** ** RPO is compatible with adding context. *)
    Parameter equiv_add_context :
      forall p ctx s t, equiv s t -> is_a_pos ctx p = true -> 
        equiv (replace_at_pos ctx s p) (replace_at_pos ctx t p).

    Parameter rpo_add_context :
      forall bb p ctx s t, rpo bb s t -> is_a_pos ctx p = true -> 
        rpo bb (replace_at_pos ctx s p) (replace_at_pos ctx t p).

    Parameter rpo_eq_add_context :
      forall bb p ctx s t, rpo_eq bb s t -> is_a_pos ctx p = true -> 
        rpo_eq bb (replace_at_pos ctx s p) (replace_at_pos ctx t p).

    Parameter rpo_dec : forall bb t1 t2, {rpo bb t1 t2}+{~rpo bb t1 t2}.
  End S.
End RPO.

Module Make (T1: Term) 
(*                     (P1 : Precedence with Definition A := T1.symbol) *)
<: RPO with Module T := T1(*  with Module P:=P1 *). 

Module T := T1.
Import T1.

(* Module P := P1. *)
(* Import P. *)

(** ** Definition of size-based well-founded orderings for induction.*)
Definition o_size s t := size s < size t.

Lemma wf_size :  well_founded o_size.
Proof.
generalize (well_founded_ltof _ size); unfold ltof; trivial.
Defined.

Definition size2 s := match s with (s1,s2) => (size s1, size s2) end.
Definition o_size2 s t := lex beq_nat lt lt (size2 s) (size2 t).

Lemma wf_size2 : well_founded o_size2.
Proof.
refine (wf_inverse_image _ _ (lex  beq_nat lt lt) size2 _);
apply wf_lex.
exact beq_nat_ok.
apply lt_wf.
apply lt_wf.
Defined.

Lemma size2_lex1 : 
 forall s f l t1 t2, In s l -> o_size2 (s,t1) (Term f l,t2).
Proof.
intros s f l t1 t2 s_in_l; unfold o_size2, size2, lex.
generalize (beq_nat_ok (size s) (size (Term f l))); case (beq_nat (size s) (size (Term f l))); [intro s_eq_t | intro s_lt_t].
absurd (size (Term f l) < size (Term f l)); auto with arith;
generalize (size_direct_subterm s (Term f l) s_in_l); rewrite s_eq_t; trivial.
apply (size_direct_subterm s (Term f l) s_in_l).
Defined.

Lemma size2_lex1_bis : 
 forall a f l t1 t2, o_size2 (Term f l, t1) (Term f (a::l), t2).
Proof.
intros a f l t1 t2; unfold o_size2, size2, lex;
generalize (beq_nat_ok (size (Term f l)) (size (Term f (a :: l)))); 
case (beq_nat (size (Term f l)) (size (Term f (a :: l)))); [intro s_eq_t | intro s_lt_t].
do 2 rewrite size_unfold in s_eq_t; injection s_eq_t; clear s_eq_t; intro s_eq_t;
absurd (list_size size l < list_size size l); auto with arith;
generalize (plus_le_compat_r _ _ (list_size size l) (size_ge_one a));
rewrite <- s_eq_t; trivial.
do 2 rewrite size_unfold;
simpl; apply lt_n_S; apply lt_le_trans with (1 + list_size size l);
auto with arith; 
apply plus_le_compat_r; apply size_ge_one.
Defined.

Lemma size2_lex1_bis_prec_eq : 
 forall a f g P l t1 t2, prec_eq P f g -> o_size2 (Term f l, t1) (Term g (a::l), t2).
Proof.
intros a f g P l t1 t2 f_eq_g; unfold o_size2, size2, lex.
generalize (beq_nat_ok (size (Term f l)) (size (Term g (a :: l))));
case (beq_nat (size (Term f l)) (size (Term g (a :: l)))); [intro s_eq_t | intro s_lt_t].
do 2 rewrite size_unfold in s_eq_t; injection s_eq_t; clear s_eq_t; intro s_eq_t;
absurd (list_size size l < list_size size l); auto with arith;
generalize (plus_le_compat_r _ _ (list_size size l) (size_ge_one a));
rewrite <- s_eq_t; trivial.
do 2 rewrite size_unfold;
simpl; apply lt_n_S; apply lt_le_trans with (1 + list_size size l);
auto with arith; 
apply plus_le_compat_r; apply size_ge_one.
Defined.


Lemma size2_lex2 :
  forall t f l s, In t l -> o_size2 (s,t) (s, Term f l).
Proof.
intros t f l s t_in_l;
unfold o_size2, size2, lex;
generalize (beq_nat_ok (size s) (size s)); case (beq_nat (size s) (size s)); [intros _ | intro s_diff_s].
apply size_direct_subterm; trivial.
apply False_rect; apply s_diff_s; reflexivity.
Defined.

Lemma size2_lex2_bis :
  forall t f l s, o_size2 (s,Term f l) (s, Term f (t :: l)).
Proof.
intros a f l s;
unfold o_size2, size2, lex;
generalize (beq_nat_ok (size s) (size s)); case (beq_nat (size s) (size s)); [intros _ | intro s_diff_s].
do 2 rewrite size_unfold; apply plus_lt_compat_l; simpl.
exact (plus_le_compat_r _ _ (list_size size l) (size_ge_one a)).
apply False_rect; apply s_diff_s; reflexivity.
Defined.

Lemma size2_lex2_bis_prec_eq :
  forall t f g P l s, prec_eq P f g -> o_size2 (s,Term f l) (s, Term g (t :: l)).
Proof.
intros a f g P l s f_eq_g;
unfold o_size2, size2, lex;
generalize (beq_nat_ok (size s) (size s)); case (beq_nat (size s) (size s)); [intros _ | intro s_diff_s].
do 2 rewrite size_unfold; apply plus_lt_compat_l; simpl.
exact (plus_le_compat_r _ _ (list_size size l) (size_ge_one a)).
apply False_rect; apply s_diff_s; reflexivity.
Defined.

Lemma o_size2_trans : transitive _ o_size2.
Proof.
intros [x1 x2] [y1 y2] [z1 z2].
apply (lex_trans beq_nat beq_nat_ok).
intros n m n_lt_m m_lt_n;
generalize (lt_asym n m n_lt_m m_lt_n); contradiction.
intros n1 n2 n3; apply lt_trans.
intros n1 n2 n3; apply lt_trans.
Qed.

Definition size3 s := match s with (s1,s2) => (size s1, size2 s2) end.
Definition o_size3 s t := 
  lex beq_nat lt (lex beq_nat lt lt) (size3 s) (size3 t).

Lemma wf_size3 : well_founded o_size3.
Proof.
refine (wf_inverse_image _ _ 
  (lex  beq_nat lt (lex  beq_nat lt lt)) size3 _).
apply wf_lex; 
[ exact beq_nat_ok 
| apply lt_wf 
| apply wf_lex; [ exact beq_nat_ok | apply lt_wf | apply lt_wf ]].
Defined.

Lemma size3_lex1 : 
 forall s f l t1 u1 t2 u2, In s l -> o_size3 (s,(t1,u1)) (Term f l,(t2,u2)).
Proof.
intros s f l t1 u1 t2 u2 s_in_l; unfold o_size3, size3, size2, lex.
generalize (beq_nat_ok (size s) (size (Term f l))); case (beq_nat (size s) (size (Term f l))); [intro s_eq_t | intro s_lt_t].
absurd (size (Term f l) < size (Term f l)); auto with arith;
generalize (size_direct_subterm s (Term f l) s_in_l); rewrite s_eq_t; trivial.
apply (size_direct_subterm s (Term f l) s_in_l).
Defined.

Lemma size3_lex1_bis : 
 forall a f l t1 u1 t2 u2, o_size3 (Term f l,(t1,u1)) (Term f (a::l),(t2,u2)).
Proof.
intros a f l t1 u1 t2 u2; unfold o_size3, size3, lex;
generalize (beq_nat_ok (size (Term f l)) (size (Term f (a :: l)))); 
case (beq_nat (size (Term f l)) (size (Term f (a :: l)))); [intro s_eq_t | intro s_lt_t].
do 2 rewrite size_unfold in s_eq_t; injection s_eq_t; clear s_eq_t; intro s_eq_t;
absurd (list_size size l < list_size size l); auto with arith;
generalize (plus_le_compat_r _ _ (list_size size l) (size_ge_one a));
rewrite <- s_eq_t; trivial.
do 2 rewrite size_unfold;
simpl; apply lt_n_S; apply lt_le_trans with (1 + list_size size l);
auto with arith; 
apply plus_le_compat_r; apply size_ge_one.
Defined.


Lemma size3_lex1_bis_prec_eq : 
 forall a f g P l t1 u1 t2 u2, prec_eq P f g -> o_size3 (Term f l,(t1,u1)) (Term f (a::l),(t2,u2)).
Proof.
intros a f g P l t1 u1 t2 u2 f_eq_g ; unfold o_size3, size3, lex;
generalize (beq_nat_ok (size (Term f l)) (size (Term f (a :: l)))); 
case (beq_nat (size (Term f l)) (size (Term f (a :: l)))); [intro s_eq_t | intro s_lt_t].
do 2 rewrite size_unfold in s_eq_t; injection s_eq_t; clear s_eq_t; intro s_eq_t;
absurd (list_size size l < list_size size l); auto with arith;
generalize (plus_le_compat_r _ _ (list_size size l) (size_ge_one a));
rewrite <- s_eq_t; trivial.
do 2 rewrite size_unfold;
simpl; apply lt_n_S; apply lt_le_trans with (1 + list_size size l);
auto with arith; 
apply plus_le_compat_r; apply size_ge_one.
Defined.

Lemma size3_lex2 :
  forall t f l s u1 u2, In t l -> o_size3 (s,(t,u1)) (s,(Term f l, u2)).
Proof.
intros t f l s u1 u2 t_in_l;
unfold o_size3, size3, size2, lex.
generalize (beq_nat_ok (size s) (size s)); case (beq_nat (size s) (size s)); [intros _ | intro s_diff_s].
generalize (beq_nat_ok (size t) (size (Term f l))); case (beq_nat (size t) (size (Term f l))); [intro t_eq_fl | intro t_lt_fl].
absurd (size (Term f l) < size (Term f l)); auto with arith;
generalize (size_direct_subterm t (Term f l) t_in_l); rewrite t_eq_fl; trivial.
apply (size_direct_subterm t (Term f l) t_in_l).
apply False_rect; apply s_diff_s; reflexivity.
Defined.
 
Lemma size3_lex3 :
  forall u f l s t, In u l -> o_size3 (s,(t,u)) (s,(t,Term f l)).
Proof.
intros u f l s t u_in_l;
unfold o_size3, size3, size2, lex;
generalize (beq_nat_ok (size s) (size s)); case (beq_nat (size s) (size s)); [intros _ | intro s_diff_s].
generalize (beq_nat_ok (size t) (size t)); case (beq_nat (size t) (size t)); [intros _ | intro t_diff_t].
apply (size_direct_subterm u (Term f l) u_in_l).
apply False_rect; apply t_diff_t; reflexivity.
apply False_rect; apply s_diff_s; reflexivity.
Defined.

Lemma o_size3_trans : transitive _ o_size3.
Proof.
intros [x1 x2] [y1 y2] [z1 z2].
apply (@lex_trans _ _ beq_nat lt (lex beq_nat lt lt) beq_nat_ok).
intros n m n_lt_m m_lt_n;
generalize (lt_asym n m n_lt_m m_lt_n); contradiction.
intros n1 n2 n3; apply lt_trans.
apply lex_trans.
exact beq_nat_ok.
intros n m n_lt_m m_lt_n;
generalize (lt_asym n m n_lt_m m_lt_n); contradiction.
intros n1 n2 n3; apply lt_trans.
intros n1 n2 n3; apply lt_trans.
Qed.

(** ** Definition of rpo.*)
(** *** Equivalence modulo rpo *)
Section S.
Variable Prec:Precedence T1.symbol.
    Inductive equiv : term -> term -> Prop :=
    | Eq : forall t, equiv t t
    | Eq_lex : 
      forall f g l1 l2, status Prec f = Lex -> status Prec g = Lex -> prec_eq Prec f g -> equiv_list_lex l1 l2 -> 
        equiv (Term f  l1) (Term g l2) 
    | Eq_mul :
      forall f g l1 l2,  status Prec f = Mul -> status Prec g = Mul -> prec_eq Prec f g -> permut0 equiv l1 l2 ->
        equiv (Term f l1) (Term g l2)

    with equiv_list_lex : list term -> list term -> Prop :=
    | Eq_list_nil : equiv_list_lex nil nil
    | Eq_list_cons : 
      forall t1 t2 l1 l2, equiv t1 t2 -> equiv_list_lex l1 l2 ->
        equiv_list_lex (t1 :: l1) (t2 :: l2).
 
Lemma equiv_same_top :
  forall f g l l', equiv (Term f l) (Term g l') -> prec_eq Prec f g.
Proof.
intros f g l l' H; inversion H; subst; trivial.
apply prec_eq_refl.
Qed.

Lemma equiv_list_lex_same_length :
  forall l1 l2, equiv_list_lex l1 l2 -> length l1 = length l2.
Proof.
intros l1; induction l1 as [ | t1 l1]; intros l2 l1_eq_l2; 
inversion l1_eq_l2 as [ | s1 s2 l1' l2' _ l1'_eq_l2']; subst; trivial.
simpl; rewrite (IHl1 l2'); trivial.
Qed.

Lemma equiv_same_length :
  forall f1 f2 l1 l2, equiv (Term f1 l1) (Term f2 l2) -> length l1 = length l2.
Proof.
intros f1 f2 l1 l2 t1_eq_t2.
inversion t1_eq_t2.
trivial.
apply equiv_list_lex_same_length; assumption.  
apply (@permut_length _ equiv); trivial.
Qed.

Lemma equiv_same_size :
  forall t t', equiv t t' -> size t = size t'.
Proof.
intros t; pattern t; apply term_rec2.
intro n; induction n as [ | n]; intros t1 St1 t2 t1_eq_t2.
absurd (1 <= 0); auto with arith; apply le_trans with (size t1); trivial;
apply size_ge_one.
inversion t1_eq_t2 as [ | f g l1' l2' Sf Sg prec_eq_f_g l1_eq_l2 | f g l1' l2' Sf Sg prec_eq_f_g P];  
subst.
trivial.
(* Lex case *)
do 2 rewrite size_unfold; apply (f_equal (fun n => 1 + n)).
generalize l2' l1_eq_l2; clear l2' l1_eq_l2 t1_eq_t2.
induction l1' as [ | t1 l1]; intros l2 l1_eq_l2; 
inversion l1_eq_l2 as [ | s1 s2 l1' l2' s1_eq_s2 l1'_eq_l2']; subst; trivial.
simpl.
assert (St1' : size t1 <= n).
apply le_S_n; apply le_trans with (size (Term f (t1 :: l1))); trivial.
apply size_direct_subterm; left; trivial.
rewrite (IHn t1 St1' s2); trivial. 
assert (Sl1 : size (Term f l1) <= S n).
apply le_trans with (size (Term f (t1 :: l1))); trivial.
do 2 rewrite size_unfold.
simpl; apply le_n_S.
apply (plus_le_compat_r 0 (size t1) (list_size size l1)).
apply lt_le_weak; apply (size_ge_one t1).
rewrite (IHl1 Sl1 l2'); trivial.
(* Mul case *)
subst; do 2 rewrite size_unfold; apply (f_equal (fun n => 1 + n)).
apply (@permut_size _ _ equiv); trivial.
intros a a' a_in_l1 _ a_eq_a'; apply IHn; trivial.
apply le_S_n.
apply le_trans with (size (Term f l1')); trivial.
apply size_direct_subterm; trivial.
Qed.

Lemma equiv_in_list : 
    forall f g (f_stat : status Prec f= Lex) (g_stat: status Prec g = Lex) l1 l2, length l1 = length l2 -> prec_eq Prec f g ->
      (forall t1 t2, In (t1, t2) (combine l1 l2) -> equiv  t1  t2) -> 
      equiv (Term f l1) (Term g l2).
Proof.
intros f g f_stat g_stat l1 l2 L prec_eq_f_g E.  apply (Eq_lex f g f_stat g_stat prec_eq_f_g).
clear f f_stat prec_eq_f_g; revert l1 l2 L E; fix equiv_in_list 1; intro l1; case l1; clear l1.
intros l2; case l2; clear l2.
intros _ _; apply Eq_list_nil.
intros a2 l2 L _; discriminate.
intros a1 l1 l2; case l2; clear l2.
intro L; discriminate.
intros a2 l2 L E; apply Eq_list_cons.
apply E; left; apply eq_refl.
apply (equiv_in_list l1 l2).
injection L; intros; assumption.
intros t1 t2 H; apply E; right; assumption.
Qed.

(* equiv is actually an equivalence *)
#[global] Instance equiv_equiv  : Equivalence equiv.
Proof.
constructor.
(* Reflexivity *)
intro t; apply Eq.
(* Symmetry *)
intros t1; pattern t1; apply term_rec3; clear t1.
intros v t2 t1_eq_t2; inversion t1_eq_t2; subst; trivial.
intros f l1 IHl t2 t1_eq_t2; 
inversion t1_eq_t2 as 
  [ 
  | f' g' l1' l2 Sf Sg preceq_f_g l1_eq_l2 
  | f' g' l1' l2 Sf Sg preceq_f_g P]; clear t1_eq_t2; subst.
apply Eq.
apply Eq_lex; trivial.
apply prec_eq_sym. trivial.
generalize l2 l1_eq_l2; clear l2 l1_eq_l2; 
induction l1 as [ | t1 l1]; intros l2 l1_eq_l2;
inversion l1_eq_l2 as [ | s1 s2 l1' l2' s1_eq_s2 l1'_eq_l2']; subst; trivial.
apply Eq_list_cons.
apply IHl; trivial; left; trivial.
apply IHl1; trivial.
intros t t_in_l1; apply IHl; right; trivial.
apply Eq_mul; trivial.
apply prec_eq_sym. trivial.
apply permut_sym; trivial.
intros a b a_in_l1 _; apply IHl; trivial.
(* Transitivity *)
intros t1; pattern t1; apply term_rec3; clear t1.
(* 1/3 variable case *)
intros v t2 t3 t1_eq_t2 t2_eq_t3; inversion t1_eq_t2; subst; trivial.
(* 1/2 compound case *)
intros f l1 E_l1 t2 t3 t1_eq_t2 t2_eq_t3; 
inversion t1_eq_t2 as [ | f' g' l1' l2 Sf Sg eq_f_g l1_eq_l2 H2 H' | f' g' l1' l2 Sf Sg eq_f_g P]; subst; trivial;
inversion t2_eq_t3 as [ | f' g'' l2' l3 Sf' Sg' eq_f_g' l2_eq_l3 H2 H'' | f' g'' l2' l3 Sf' Sg' eq_f_g' P' ]; subst; trivial.
(* 1/5 Lex case *)
apply Eq_lex; trivial.
apply prec_eq_transitive with g'; trivial.
generalize l2 l3 l1_eq_l2 l2_eq_l3;
clear t1_eq_t2 t2_eq_t3 l2 l3 l1_eq_l2 l2_eq_l3;
induction l1 as [ |s1 l1]; intros l2 l3 l1_eq_l2 l2_eq_l3.
inversion l1_eq_l2; subst; trivial.
inversion l1_eq_l2 as [ | s1' s2 l1' l2' s1_eq_s2 l1'_eq_l2']; subst.
inversion l2_eq_l3 as [ | s2' s3 l2'' l3' s2_eq_s3 l2''_eq_l3']; subst.
apply Eq_list_cons.
apply E_l1 with s2; trivial; left; trivial.
apply IHl1 with l2'; trivial.
intros t t_in_l1; apply E_l1; right; trivial.
(* 1/4 absurd case *)
rewrite Sg in Sf'; discriminate.
(* 1/3 absurd case *)
rewrite Sg in Sf'; discriminate.
(* 1/2 Mul case *)
apply Eq_mul; trivial.
apply prec_eq_transitive with g'; trivial.
apply permut_trans with l2; trivial.
intros a b c a_in_l1 _ _; apply E_l1; trivial.
Qed.

#[global] Instance equiv_Equivalence : Equivalence equiv.

Proof. generalize equiv_equiv. firstorder. Qed.

Definition equiv_bool_F := 
(fun (equiv_bool : term -> term -> bool) (t1 t2 : term) =>
match t1, t2 with
| Var v1, Var v2 => X.eq_bool v1 v2
| Var _, Term _ _ => false
| Term _ _, Var _ => false
| Term f1 l1, Term f2 l2 =>
    if prec_eq_bool Prec f1 f2
    then
    match status Prec f1 with
    | Lex => 
         let equiv_lex_bool :=
              (fix equiv_lex_bool (kk1 kk2 : list term) {struct kk1} :  bool :=  
               (match kk1 with
               | [] => match kk2 with [] => true | _ :: _=> false end
               | t1 :: k1 => 
                     match kk2 with 
                         [] => false 
                       | t2 :: k2=> (equiv_bool t1 t2) && (equiv_lex_bool k1 k2)
                       end
                 end)) in
              (equiv_lex_bool l1 l2)
    | Mul => 
       let equiv_mult_bool :=
              (fix equiv_mult_bool (kk1 kk2 : list term) {struct kk1} :  bool :=  
               (match kk1 with
               | [] => match kk2 with [] => true | _ :: _=> false end
               | t1 :: k1 => 
                     match remove equiv_bool t1 kk2 with 
                           None => false 
                         | Some k2 => equiv_mult_bool k1 k2 end
                         end)) in
              (equiv_mult_bool l1 l2)
    end
    else false
end) : (term -> term -> bool) -> term -> term -> bool.


Definition equiv_bool_terminate :
forall t1 t2 : term,
       {v : bool |  forall k : nat, (size t1) <= k ->
         forall def : term -> term -> bool,
         iter (term -> term -> bool) k equiv_bool_F def t1 t2 = v}.
Proof.
intro t1.
assert (Acc_t1 := well_founded_ltof term size t1).
induction Acc_t1 as [t1 Acc_t1 IHAcc].
revert Acc_t1 IHAcc; case t1; clear t1; [intro v1 | intros f1 l1]; 
(intros Acc_t1 IHAcc t2; case t2; clear t2; [intro v2 | intros f2 l2]).

exists (X.eq_bool v1 v2); intros [ | p] p_lt_k def.
apply False_ind; exact (gt_irrefl 0 p_lt_k).
exact (eq_refl _).

exists false; intros [ | p] p_lt_k def.
apply False_ind; exact (gt_irrefl 0 p_lt_k).
exact (eq_refl _).

exists false; intros [ | p] p_lt_k def.
apply False_ind; exact (le_Sn_O _ p_lt_k).
exact (eq_refl _).

rewrite size_unfold.
assert ({v : bool |
  forall k : nat,
  list_size size l1 <= k ->
  forall def : term -> term -> bool,
  iter (term -> term -> bool) (S k) equiv_bool_F def (Term f1 l1) (Term f2 l2) = v}).
unfold iter; simpl.
case (prec_eq_bool Prec f1 f2).
assert (IH : forall t1 : term, In t1 l1 ->
     forall t2 : term,
     {v : bool |
       forall k : nat,
       size t1 <= k ->
       forall def : term -> term -> bool,
       iter (term -> term -> bool) k equiv_bool_F def t1 t2 = v}).
intros t1 t1_in_l1; exact (IHAcc t1 (size_direct_subterm t1 (Term f1 l1) t1_in_l1)).
case (status Prec f1).
clear IHAcc Acc_t1 f2; revert l1 IH l2; fix equiv_lex_bool 1.
intros l1; case l1.
intros _ l2; case l2.
exists true; intros k p_lt_k def; exact (eq_refl _).
exists false; intros k p_lt_k def; exact (eq_refl _).
intros a1 k1 IHl1 l2; case l2.
exists false; intros k p_lt_k def; exact (eq_refl _).
intros a2 k2; case (equiv_lex_bool k1 (tail_set _ IHl1) k2); intros bl IH'.
case (IHl1 a1 (or_introl _ (eq_refl _)) a2); intros ba IH''.
exists (ba && bl); intros k p_le_k def.
assert (pa_lt_k : size a1 <= k).
apply le_trans with (list_size size (a1 :: k1)); [apply le_plus_l | exact p_le_k].
rewrite (IH'' k pa_lt_k).
assert (pl_le_k : list_size size k1 <= k).
apply le_trans with (list_size size (a1 :: k1)); [apply le_plus_r | exact p_le_k].
rewrite (IH' k pl_le_k def).
reflexivity.

clear IHAcc Acc_t1 f2.
revert l1 IH l2; fix IHl1 1.
intro l1; case l1; clear l1.
intros _ l2; case l2.
exists true; intros k p_lt_k def; exact (eq_refl _).
exists false; intros k p_lt_k def; exact (eq_refl _).
intros a1 l1 IH l2.
assert (Hrem : {ok : option (list term) |
                             forall k : nat, list_size size (a1 :: l1) <= k ->
                             forall def : term -> term -> bool,
                             remove (iter _ k equiv_bool_F def) a1 l2 = ok}).
revert l2; fix IHl2 1.
intro l2; case l2; clear l2.
exists (@None (list term)); intro k; case k; clear k.
intro L; apply False_rect.
apply (le_Sn_O _ (le_trans 1 _ 0 (size_ge_one a1) (le_trans (size a1) _ 0 (le_plus_l _ _) L))).
intros k _ def; reflexivity.
intros a2 l2;
case (IH a1 (or_introl _ (eq_refl _)) a2); intro v; case v; intro Ha1.
exists (Some l2); intros k L def; simpl; rewrite Ha1.
reflexivity.
apply le_trans with (list_size size (a1 :: l1)); [apply le_plus_l | apply L].
case (IHl2 l2); clear IHl2; intro ok; case ok; clear ok.
intros k2 IHl2; exists (Some (a2 :: k2)); intros k L def; simpl.
rewrite Ha1.
rewrite IHl2.
reflexivity.
apply L.
apply le_trans with (list_size size (a1 :: l1)); [apply le_plus_l | apply L].
intro IHl2; exists (@None (list term)); intros k L def; simpl.
rewrite Ha1.
rewrite IHl2.
reflexivity.
apply L.
apply le_trans with (list_size size (a1 :: l1)); [apply le_plus_l | apply L].
case Hrem; clear Hrem; intro ok; case ok; clear ok.
intros k2 Hrem.
case (IHl1 _ (tail_set _ IH) k2); intros v Hl1; exists v; intros k L def.
rewrite (Hrem k L).
assert (l1_le_k : list_size size l1 <= k).
refine (le_trans _ _ _ _ L); apply le_plus_r.
rewrite (Hl1 k l1_le_k def).
reflexivity.
intro Hrem; exists false; intros k L def.
rewrite (Hrem k L).
reflexivity.

exists false; intros _ _ _; exact (eq_refl _).

case H; clear H; intros v H; exists v; intro k; case k; clear k.
intro L; apply False_rect.
apply (le_Sn_O _ (le_trans 1 _ 0 (le_plus_l _ _) L)).
intros k L def; rewrite (H k).
reflexivity.
apply (le_S_n  _ _ L).
Defined.

Definition equiv_bool := fun t1 t2 => let (v,_) := equiv_bool_terminate t1 t2 in v.

Lemma equiv_bool_equation :
  forall t1 t2, equiv_bool t1 t2 = 
match t1, t2 with
| Var v1, Var v2 => X.eq_bool v1 v2
| Var _, Term _ _ => false
| Term _ _, Var _ => false
| Term f1 l1, Term f2 l2 =>
    if prec_eq_bool Prec f1 f2
    then
    match status Prec f1 with
    | Lex => 
         let equiv_lex_bool :=
              (fix equiv_lex_bool (kk1 kk2 : list term) {struct kk1} :  bool :=  
               (match kk1 with
               | [] => match kk2 with [] => true | _ :: _=> false end
               | t1 :: k1 => 
                     match kk2 with 
                         [] => false 
                       | t2 :: k2=> (equiv_bool t1 t2) && (equiv_lex_bool k1 k2)
                       end
                 end)) in
              (equiv_lex_bool l1 l2)
    | Mul => 
       let equiv_mult_bool :=
              (fix equiv_mult_bool (kk1 kk2 : list term) {struct kk1} :  bool :=  
               (match kk1 with
               | [] => match kk2 with [] => true | _ :: _=> false end
               | t1 :: k1 => 
                     match remove equiv_bool t1 kk2 with 
                           None => false 
                         | Some k2 => equiv_mult_bool k1 k2 end
                         end)) in
              (equiv_mult_bool l1 l2)
    end
    else false
end.
Proof.
assert (H : forall t1 t2 k, size t1 <= k -> iter (term -> term -> bool) k equiv_bool_F equiv_bool t1 t2 = equiv_bool t1 t2).
intros t1 t2 k L; unfold equiv_bool at 2; generalize (equiv_bool_terminate t1 t2).
intro H; case H; clear H; intros v H; apply H; apply L.
intro t1; pattern t1; apply term_rec3; clear t1.
intros v1 [v2 | f2 l2]; reflexivity.
intros f1 l1 IH [v2 | f2 l2].
reflexivity.
rewrite <- (H (Term f1 l1) (Term f2 l2) _ (le_n _)); rewrite size_unfold; simpl.
case (prec_eq_bool Prec f1 f2); [idtac | reflexivity].
case (status Prec f1); clear f1.
assert (H' : forall l1 f1 f2, (forall t1, In t1 l1 -> forall t2, f1 t1 t2 = f2 t1 t2) -> forall l2,
                 (fix equiv_lex_bool (kk1 kk2 : list term) : bool :=
                 match kk1 with
                 | [] => match kk2 with
                 | [] => true
                 | _ :: _ => false
                 end
                 | t1 :: k1 =>
                 match kk2 with
                 | [] => false
                 | t2 :: k2 => f1 t1 t2 && equiv_lex_bool k1 k2
       end
   end) l1 l2 =
(fix equiv_lex_bool (kk1 kk2 : list term) : bool :=
                 match kk1 with
                 | [] => match kk2 with
                 | [] => true
                 | _ :: _ => false
                 end
                 | t1 :: k1 =>
                 match kk2 with
                 | [] => false
                 | t2 :: k2 => f2 t1 t2 && equiv_lex_bool k1 k2
       end
   end) l1 l2).
clear l1 l2 IH; intro l1; induction l1 as [ | a1 l1]; intros g1 g2 IH [ | a2 l2].
reflexivity.
reflexivity.
reflexivity.
apply f_equal2.
apply IH; left; reflexivity.
apply (IHl1 g1 g2 (tail_prop _ IH) l2).
refine (H' l1 _ _ _ l2); clear H'.
intros t1 t1_in_l1 t2; apply H.
generalize (size_direct_subterm t1 (Term f2 l1) t1_in_l1).
rewrite (size_unfold (Term f2 l1)).
simpl; intro L; apply (le_S_n _ _ L).
assert (H' : forall l1 f1 f2, (forall t1, In t1 l1 -> forall t2, f1 t1 t2 = f2 t1 t2) -> forall l2,
                 (fix equiv_mult_bool (kk1 kk2 : list term) : bool :=
   match kk1 with
   | [] => match kk2 with
           | [] => true
           | _ :: _ => false
           end
   | t1 :: k1 =>
       match
         remove f1 t1 kk2
       with
       | Some k2 => equiv_mult_bool k1 k2
       | None => false
       end
   end) l1 l2 =
(fix equiv_mult_bool (kk1 kk2 : list term) : bool :=
   match kk1 with
   | [] => match kk2 with
           | [] => true
           | _ :: _ => false
           end
   | t1 :: k1 =>
       match remove f2 t1 kk2 with
       | Some k2 => equiv_mult_bool k1 k2
       | None => false
       end
   end) l1 l2).
clear l1 l2 IH; intro l1; induction l1 as [ | a1 l1]; intros g1 g2 IH l2.
reflexivity.
assert (H' : forall f1 f2, (forall t2, f1 a1 t2 = f2 a1 t2) -> forall l2, remove f1 a1 l2 = remove f2 a1 l2).
clear l1 l2 g1 g2 IH IHl1; intros g1 g2 IH; induction l2 as [ | a2 l2].
reflexivity.
simpl; rewrite (IH a2); rewrite IHl2; reflexivity.
rewrite (H' g1 g2 (IH a1 (or_introl _ (eq_refl _)))).
case (remove g2 a1 l2).
intro k2; apply (IHl1 g1 g2 (tail_prop _ IH)).
reflexivity.
refine (H' l1 _ _ _ l2).
intros t1 t1_in_l1 t2; apply H.
generalize (size_direct_subterm t1 (Term f2 l1) t1_in_l1).
rewrite (size_unfold (Term f2 l1)).
simpl; intro L; apply (le_S_n _ _ L).
Defined.

Lemma equiv_bool_ok : forall t1 t2, match equiv_bool t1 t2 with true => equiv t1 t2 | false => ~equiv t1 t2 end.
Proof.
intros t1; pattern t1; apply term_rec3; clear t1.
intros v1 t2; case t2; clear t2.
intro v2; rewrite equiv_bool_equation; generalize (X.eq_bool_ok v1 v2); case (X.eq_bool v1 v2).
intro v1_eq_v2; rewrite v1_eq_v2; apply Eq.
intros v1_diff_v2 v1_eq_v2; apply v1_diff_v2; inversion v1_eq_v2; reflexivity.
intros f2 l2; rewrite equiv_bool_equation; intro t1_eq_t2; inversion t1_eq_t2.
intros f1 l1 IH t2; case t2; clear t2.
intros v2; rewrite equiv_bool_equation; intro t1_eq_t2; inversion t1_eq_t2.
intros f2 l2; rewrite equiv_bool_equation.
case_eq (prec_eq_bool Prec f1 f2).
intro f1_eq_f2; case_eq (status Prec f1).
intro Lex_f1; simpl.
assert (H : if (fix equiv_lex_bool (kk1 kk2 : list term) : bool :=
      match kk1 with
      | [] => match kk2 with
              | [] => true
              | _ :: _ => false
              end
      | t1 :: k1 =>
          match kk2 with
          | [] => false
          | t2 :: k2 => equiv_bool t1 t2 && equiv_lex_bool k1 k2
          end
      end) l1 l2
   then equiv_list_lex l1 l2 else ~equiv_list_lex l1 l2).
revert l2; induction l1 as [ | a1 l1]; intro l2; case l2; clear l2.
apply Eq_list_nil.
intros a2 l2; simpl; intro l1_eq_l2; inversion l1_eq_l2.
simpl; intro l1_eq_l2; inversion l1_eq_l2.
intros a2 l2; simpl; generalize (IH a1 (or_introl _ (eq_refl _)) a2).
case (equiv_bool a1 a2).
intro a1_eq_a2; generalize (IHl1 (tail_prop _ IH) l2).
simpl.
case ((fix equiv_lex_bool (kk1 kk2 : list term) : bool :=
       match kk1 with
       | [] => match kk2 with
               | [] => true
               | _ :: _ => false
               end
       | t1 :: k1 =>
           match kk2 with
           | [] => false
           | t3 :: k2 => equiv_bool t1 t3 && equiv_lex_bool k1 k2
           end
       end) l1 l2).
intro l1_eq_l2; apply Eq_list_cons; assumption.
intros l1_diff_l2 l1_eq_l2; apply l1_diff_l2; inversion l1_eq_l2; assumption.
intros a1_diff_a2 l1_eq_l2; apply a1_diff_a2; inversion l1_eq_l2; assumption.
revert H; simpl.
case ((fix equiv_lex_bool (kk1 kk2 : list term) : bool :=
       match kk1 with
       | [] => match kk2 with
               | [] => true
               | _ :: _ => false
               end
       | t1 :: k1 =>
           match kk2 with
           | [] => false
           | t3 :: k2 => equiv_bool t1 t3 && equiv_lex_bool k1 k2
           end
       end) l1 l2).
intro l1_eq_l2.  apply Eq_lex; trivial. assert (H2:= prec_eq_bool_ok). assert (H2':= H2 symbol Prec  f1 f2). rewrite f1_eq_f2 in H2'.  assert (H5:= prec_eq_status Prec f1 f2). assert (H6: status Prec f1 = status Prec f2). apply H5; trivial. rewrite <- H6. trivial.
assert (H2:= prec_eq_bool_ok). assert (H2':= (H2 symbol Prec f1 f2)). rewrite f1_eq_f2 in H2'. trivial.
intros l1_diff_l2 t1_eq_t2; inversion t1_eq_t2; subst l2.
apply l1_diff_l2; generalize l1; intro l; induction l as [ | a l].
apply Eq_list_nil.
apply Eq_list_cons; [apply Eq | assumption].
apply l1_diff_l2; assumption.
subst f2; rewrite Lex_f1 in H3. discriminate.
intro Mul_f1; simpl.
assert (H : if (fix equiv_mult_bool (kk1 kk2 : list term) : bool :=
      match kk1 with
      | [] => match kk2 with
              | [] => true
              | _ :: _ => false
              end
      | t1 :: k1 =>
          match remove equiv_bool t1 kk2 with
          | Some k2 => equiv_mult_bool k1 k2
          | None => false
          end
      end) l1 l2
    then permut0 equiv l1 l2 else ~permut0 equiv l1 l2).
revert l2; induction l1 as [ | a1 l1].
intro l2; case l2; clear l2.
simpl; apply Pnil.
intros a2 l2; simpl; intro t1_eq_t2; inversion t1_eq_t2.
assert (R : forall l2, match remove equiv_bool a1 l2 with
 | Some _ =>
     {a2 : term & 
     {l2' : list term & 
     {l2'' : list term |
     equiv a1 a2 /\
     l2 = l2' ++ a2 :: l2'' /\ remove equiv_bool a1 l2 = Some (l2' ++ l2'')}}}
 | None => forall a2, equiv a1 a2 -> ~ In a2  l2
 end).
intro l2; induction l2 as [ | a2 l2].
intros a2 a1_eq_a2 F; assumption.
rewrite remove_equation.
generalize (IH a1 (or_introl _ (eq_refl _)) a2); case (equiv_bool a1 a2).
intro a1_eq_a2; exists a2; exists (@nil term); exists l2; repeat split; assumption.
intro a1_diff_a2; revert IHl2; case (remove equiv_bool a1 l2).
intros k2 [a1' [l2' [l2'' [H1 [H2 H3]]]]]; exists a1'; exists (a2 :: l2'); exists l2''; repeat split.
assumption.
simpl; apply f_equal; assumption.
simpl; do 2 apply f_equal; injection H3; intros; assumption.
simpl; intros a1_not_in_l2; intros a a_eq_a1 [a_eq_a2 | a_in_l2].
subst a; apply a1_diff_a2; assumption.
apply (a1_not_in_l2 a a_eq_a1 a_in_l2).
intro l2; generalize (R l2); case (remove equiv_bool a1 l2).
intros k2 [a2 [k2' [k2'' [H1 [H2 H3]]]]].
generalize (IHl1 (tail_prop _ IH) k2); simpl.
injection H3; clear H3; intro H3; 
case ((fix equiv_mult_bool (kk1 kk2 : list term) : bool :=
       match kk1 with
       | [] => match kk2 with
               | [] => true
               | _ :: _ => false
               end
       | t1 :: k1 =>
           match remove equiv_bool t1 kk2 with
           | Some k3 => equiv_mult_bool k1 k3
           | None => false
           end
       end) l1 k2).
intro P; subst l2 k2; apply Pcons; assumption.
intros not_P P; subst l2 k2; apply not_P.
apply (@permut_cons_inside term term equiv) with a1 a2.
intros u3 u1 u4 u2 _ _ _ _ H31 H41 H42; transitivity u1.
assumption.
transitivity u4.
symmetry; assumption.
assumption.
assumption.
assumption.
intros H P; inversion P as [ | a1' a2 l1' l2' l2'' a1_eq_a2 P'].
apply (H a2 a1_eq_a2); subst l2; apply in_or_app; right; left; reflexivity.
revert H; case ((fix equiv_mult_bool (kk1 kk2 : list term) : bool :=
      match kk1 with
      | [] => match kk2 with
              | [] => true
              | _ :: _ => false
              end
      | t1 :: k1 =>
          match remove equiv_bool t1 kk2 with
          | Some k2 => equiv_mult_bool k1 k2
          | None => false
          end
      end) l1 l2).
intro P.  apply Eq_mul. assumption.
 assert (H2:= prec_eq_bool_ok). assert (H2':= H2 symbol Prec  f1 f2). rewrite f1_eq_f2 in H2'. assert (H6:= prec_eq_status Prec f1 f2); trivial. assert (H7: status Prec f1 = status Prec f2). apply H6. trivial.  rewrite <- H7. trivial. 
 assert (H2:= prec_eq_bool_ok). assert (H2':= H2 symbol Prec  f1 f2). rewrite f1_eq_f2 in H2'. trivial.
trivial. 
intros not_P t1_eq_t2.
inversion t1_eq_t2. subst l2.
apply not_P; apply permut_refl; intros; reflexivity.
rewrite Mul_f1 in H3; discriminate.
apply not_P; assumption.
intros f1_diff_f2 t1_eq_t2. inversion t1_eq_t2. rewrite H1 in f1_diff_f2. assert (H3:= prec_eq_bool_ok). assert (H3':= H3 symbol Prec f2 f2).  rewrite f1_diff_f2 in H3'. contradict H3'.   apply prec_eq_refl. trivial.
assert (H8:= prec_eq_bool_ok). assert (H8':= H8 symbol Prec f1 f2).  rewrite f1_diff_f2 in H8'. contradict H8'. trivial. 
assert (H8:= prec_eq_bool_ok). assert (H8':= H8 symbol Prec f1 f2).  rewrite f1_diff_f2 in H8'. contradict H8'.  trivial. 
Defined.

Lemma equiv_dec :
  forall t1 t2, {equiv t1 t2}+{~equiv t1 t2}.
Proof.
intros t1 t2; generalize (equiv_bool_ok t1 t2); case (equiv_bool t1 t2).
left; assumption.
right; assumption.
Defined.

Lemma term_rec3_mem : 
   forall P : term -> Type,
       (forall v : variable, P (Var v)) ->
       (forall (f : symbol) (l : list term),
        (forall t : term, mem equiv t l -> P t) -> P (Term f l)) ->
       forall t : term, P t.
Proof.
intros P Hvar Hterm. 
apply term_rec2; induction n; intros t Size_t.
absurd (1 <= 0); auto with arith; 
apply le_trans with (size t); trivial; apply size_ge_one.
destruct t as [ x | f l ]; trivial;
apply Hterm; intros; apply IHn;
apply lt_n_Sm_le.
apply lt_le_trans with (size (Term f l)); trivial.
destruct (mem_split_set _ _ equiv_bool_ok _ _ H) as [t' [l1 [l2 [t_eq_t' [H' _]]]]].
simpl in t_eq_t'; simpl in H'; subst l.
rewrite (equiv_same_size t_eq_t').
apply size_direct_subterm; simpl; apply in_or_app; right; left; trivial.
Qed.

Inductive rpo (bb : nat) : term -> term -> Prop :=
  | Subterm : forall f l t s, mem equiv s l -> rpo_eq bb t s -> rpo bb t (Term f l)
  | Top_gt : 
       forall f g l l', prec Prec g f -> (forall s', mem equiv s' l' -> rpo bb s' (Term f l)) -> 
       rpo bb (Term g l') (Term f l)
  | Top_eq_lex : 
        forall f g l l', status Prec f = Lex  -> status Prec g = Lex -> prec_eq Prec f g -> (length l = length l' \/ (length l' <= bb /\ length l <= bb)) -> rpo_lex bb l' l -> 
        (forall s', mem equiv s' l' -> rpo bb s' (Term g l)) ->
        rpo bb (Term f l') (Term g l)
  | Top_eq_mul : 
        forall f g l l', status Prec f = Mul  -> status Prec g = Mul -> prec_eq Prec f g -> rpo_mul bb l' l -> 
        rpo bb (Term f l') (Term g l)

with rpo_eq (bb : nat) : term -> term -> Prop :=
  | Equiv : forall t t', equiv t t' -> rpo_eq bb t t'
  | Lt : forall s t, rpo bb s t -> rpo_eq bb s t

with rpo_lex (bb : nat) : list term -> list term -> Prop :=
  | List_gt : forall s t l l', rpo bb s t -> rpo_lex bb (s :: l) (t :: l')
  | List_eq : forall s s' l l', equiv s s' -> rpo_lex bb l l' -> rpo_lex bb (s :: l) (s' :: l')
  | List_nil : forall s l, rpo_lex bb nil (s :: l)

with rpo_mul ( bb : nat) : list term -> list term -> Prop :=
  | List_mul : forall a lg ls lc l l', 
       permut0 equiv l' (ls ++ lc) -> permut0 equiv l (a :: lg ++ lc) ->
       (forall b, mem equiv b ls -> exists a', mem equiv a' (a :: lg) /\ rpo bb b a') ->
       rpo_mul bb l' l.

Lemma size_direct_subterm_mem :
  forall n t f l, size (Term f l) <= S n -> mem equiv t l -> size t <= n.
Proof.
intros n t f l Sfl t_mem_l;
apply le_S_n.
apply le_trans with (size (Term f l)); trivial.
destruct (mem_split_set _ _ equiv_bool_ok _ _ t_mem_l) as [t' [l1 [l2 [t_eq_t' [H _]]]]].
simpl in t_eq_t'; simpl in H; subst l.
rewrite (equiv_same_size t_eq_t').
apply size_direct_subterm; simpl; apply in_or_app; right; left; trivial.
Qed.

Lemma size2_lex1_mem : 
 forall s f l t1 t2, mem equiv s l -> o_size2 (s,t1) (Term f l,t2).
Proof.
intros s f l t1 t2 s_mem_l;
destruct (mem_split_set _ _ equiv_bool_ok _ _ s_mem_l) as [s' [l1 [l2 [s_eq_s' [H _]]]]].
simpl in s_eq_s'; simpl in H.
unfold o_size2, size2; rewrite (equiv_same_size s_eq_s').
apply (size2_lex1 s' f l t1 t2).
subst l; apply in_or_app; right; left; trivial.
Qed.

Lemma size2_lex2_mem :
  forall t f l s, mem equiv t l -> o_size2 (s,t) (s, Term f l).
Proof.
intros t f l s t_mem_l;
destruct (mem_split_set _ _ equiv_bool_ok _ _ t_mem_l) as [t' [l1 [l2 [t_eq_t' [H _]]]]].
simpl in t_eq_t'; simpl in H.
unfold o_size2, size2; rewrite (equiv_same_size t_eq_t').
apply (size2_lex2 t' f l s).
subst l; apply in_or_app; right; left; trivial.
Qed.

Lemma size3_lex1_mem :
 forall s f l t1 u1 t2 u2, mem equiv s l -> o_size3 (s,(t1,u1)) (Term f l,(t2,u2)).
Proof.
intros s f l t1 u1 t2 u2 s_mem_l;
destruct (mem_split_set _ _ equiv_bool_ok _ _ s_mem_l) as [s' [l1 [l2 [s_eq_s' [H _]]]]].
simpl in s_eq_s'; simpl in H.
unfold o_size3, size3; rewrite (equiv_same_size s_eq_s').
apply (size3_lex1 s' f l t1 u1 t2 u2).
subst l; apply in_or_app; right; left; trivial.
Qed.

Lemma size3_lex2_mem :
  forall t f l s u1 u2, mem equiv t l -> o_size3 (s,(t,u1)) (s,(Term f l, u2)).
Proof.
intros t f l s u1 u2 t_mem_l;
destruct (mem_split_set _ _ equiv_bool_ok _ _ t_mem_l) as [t' [l1 [l2 [t_eq_t' [H _]]]]].
simpl in t_eq_t'; simpl in H.
unfold o_size3, size3, size2; rewrite (equiv_same_size t_eq_t').
apply (size3_lex2 t' f l s u1 u2).
subst l; apply in_or_app; right; left; trivial.
Qed.


Lemma size3_lex3_mem :
  forall u f l s t, mem equiv u l -> o_size3 (s,(t,u)) (s,(t,Term f l)).
Proof.
intros u f l s t u_mem_l;
destruct (mem_split_set _ _ equiv_bool_ok _ _ u_mem_l) as [u' [l1 [l2 [u_eq_u' [H _]]]]].
simpl in u_eq_u'; simpl in H.
unfold o_size3, size3, size2; rewrite (equiv_same_size u_eq_u').
apply (size3_lex3 u' f l s t).
subst l; apply in_or_app; right; left; trivial.
Qed.

 
Lemma size3_lex3_prec :
  forall u f g h l l' s, In u l -> prec_eq Prec g h -> o_size3 (s,(Term g l',u)) (s,(Term h l',Term f l)).
Proof.
intros u f g h l l' s u_in_l;
unfold o_size3, size3, size2, lex;
generalize (beq_nat_ok (size s) (size s)); case (beq_nat (size s) (size s)); [intros _ | intro s_diff_s].
generalize (beq_nat_ok (size (Term g l')) (size (Term h l')));  case (beq_nat (size (Term g l')) (size (Term h l'))); [intros _ | intro t_diff_t]. intros.
apply (size_direct_subterm u (Term f l) u_in_l). intros.
apply False_rect; apply t_diff_t; reflexivity.
apply False_rect; apply s_diff_s; reflexivity.
Defined.

Lemma size3_lex3_mem_preceq :
  forall u f g h l l' s, mem equiv u l -> prec_eq Prec g h -> o_size3 (s,(Term g l',u)) (s,(Term h l',Term f l)).
Proof.
intros u f g h l l' s u_mem_l;
destruct (mem_split_set _ _ equiv_bool_ok _ _ u_mem_l) as [u' [l1 [l2 [u_eq_u' [H _]]]]].
simpl in u_eq_u'; simpl in H.
unfold o_size3, size3, size2; rewrite (equiv_same_size u_eq_u').
intros prec_g_h.
apply (size3_lex3_prec u' f g h l l' s).
subst l; apply in_or_app; right; left; trivial. trivial.
Qed.

Lemma mem_mem :
 forall t l1 l2, equiv_list_lex l1 l2 ->  (mem equiv t l1 <-> mem equiv t l2).
Proof.
intros t l1 l2 l1_eq_l2; split.
generalize t l2 l1_eq_l2; clear t l2 l1_eq_l2; induction l1 as [ | t1 l1]; 
intros t l2 l1_eq_l2 t_mem_l1.
contradiction.
inversion l1_eq_l2 as [ | s1 s2 l1' l2' s1_eq_s2 l1_eq_l2']; subst.
destruct t_mem_l1 as [ t_eq_t1 | t_mem_l1].
left; transitivity t1; trivial.
right; apply IHl1; trivial.
generalize t l2 l1_eq_l2; clear t l2 l1_eq_l2; induction l1 as [ | t1 l1]; 
intros t l2 l1_eq_l2 t_mem_l2;
inversion l1_eq_l2 as [ | s1 s2 l1' l2' s1_eq_s2 l1_eq_l2']; subst.
trivial.
destruct t_mem_l2 as [ t_eq_t2 | t_mem_l2].
left; transitivity s2; trivial.
symmetry; trivial.
right; apply IHl1 with l2'; trivial.
Qed.

Lemma equiv_rpo_equiv_1 :
  forall bb t t', equiv t t' -> (forall s, rpo bb s t <-> rpo bb s t').
Proof.
intro bb.
assert (H : forall p, match p with (s,t) =>
                              forall t', equiv t t' -> rpo bb s t -> rpo bb s t'
                 end).
intro p; pattern p; refine (well_founded_ind wf_size2 _ _ _); clear p.
intros [s t] IH t' t_eq_t' s_lt_t.
inversion t_eq_t' as [ t'' | f g'' l1 l2 Statf Statg eq_f_g H | f g'' l1 l2 Statf Statg eq_f_g P]; subst.
(* 1/4 equivalence is syntactic identity *)
trivial.
(* 1/3 equivalence with Lex top symbol *)
inversion s_lt_t as  [g l t'' t' t'_mem_l t''_le_t'
                            | g g' l l' g_prec_f l'_lt_t
                            | g g''' l l' Stat_g Statg''' eq_g_g''' L l'_lt_ll1 l'_lt_t
                            | g g''' l l' Stat_g Statg''' eq_g_g''' l'_lt_ll1 ]; subst.
(* 1/6 equivalence with Lex top symbol , Subterm *)
destruct t''_le_t' as [t'' t' t''_eq_t' | t'' t' t''_lt_t'];
apply Subterm with t'; trivial.
rewrite <- (mem_mem t' H); trivial.
apply Equiv; trivial.
rewrite <- (mem_mem t' H); trivial.
apply Lt; trivial.
(* 1/5 equivalence with Lex top symbol,  Top_gt *)
apply Top_gt; trivial.
apply prec_eq_prec1 with f. trivial. trivial.
intros s' s'_mem_l'.
apply (IH (s',(Term f l1))); trivial.
apply size2_lex1_mem; trivial.
apply l'_lt_t; trivial.
(* 1/4 equivalence with Lex top symbol,  Top_eq_lex *)
apply Top_eq_lex; trivial. apply prec_eq_transitive with f; trivial.
rewrite <- (equiv_list_lex_same_length H); assumption.
clear t_eq_t' l'_lt_t s_lt_t L. revert l2 l' l'_lt_ll1 IH H. 
induction l1 as [ | t1 l1]; intros l2 l' l'_lt_l1 IH l1_eq_l2;
inversion l'_lt_l1 as [ s t1' l'' l1' s_lt_t1' L_eq 
                             | t1' t1'' l'' l1' t1'_eq_t1'' l''_lt_l1' | s l'']; subst;
inversion l1_eq_l2 as [ | t1'' t2 l1' l2' t1''_eq_t2 l1_eq_l2']; subst.
simpl; apply List_gt.
apply (IH (s,t1)); trivial.
apply size2_lex1; left; trivial.
apply List_eq.
transitivity t1; trivial.
apply IHl1; trivial.
intros y H; apply IH.
refine (o_size2_trans _ _ _ H _).
apply size2_lex1_bis.
apply List_nil.
intros s' s'_mem_l'.
apply (IH (s', Term f l1)); trivial.
apply size2_lex1_mem; trivial.
apply l'_lt_t; trivial.
(* 1/3 equivalence with Lex top symbol,  Top_eq_mul *)
rewrite Statf in Statg'''; discriminate.
(* 1/2 equivalence with Mul top symbol *)
inversion s_lt_t as  [g l t'' t' t'_mem_l t''_le_t'
                            | g g' l l' g_prec_f l'_lt_t
                            | g g''' l l' Stat_g Statg''' eq_g_g''' L l'_lt_ll1 l'_lt_t
                            | g g''' l l' Stat_g Statg''' eq_g_g''' l'_lt_ll1 ]; subst.
(* 1/5 equivalence with Mul top symbol , Subterm *)
destruct t''_le_t' as [t'' t' t''_eq_t' | t'' t' t''_lt_t'];
apply Subterm with t'; trivial.
rewrite <- (mem_permut0_mem equiv_equiv  t' P); trivial.
apply Equiv; trivial.
rewrite <- (mem_permut0_mem equiv_equiv t' P); trivial.
apply Lt; trivial.
(* 1/4 equivalence with Mul top symbol,  Top_gt *)
apply Top_gt; trivial. apply prec_eq_prec1 with f. trivial. trivial.
intros s' s'_mem_l2.
apply (IH (s', Term f l1)); trivial.
apply size2_lex1_mem; trivial.
apply l'_lt_t; trivial.
(* 1/3 equivalence with Mul top symbol,  Top_eq_lex *)
rewrite Statf in Statg'''; discriminate.
(* 1/2 equivalence with Mul top symbol,  Top_eq_mul *)
apply Top_eq_mul; trivial.
apply prec_eq_transitive with f. trivial. trivial.
inversion l'_lt_ll1 as [a lg ls lc l'' l''' Q1 Q2 ls_lt_alg]; subst.
apply (@List_mul bb a lg ls lc); trivial.
apply (permut0_trans equiv_equiv) with l1.
apply (permut0_sym equiv_equiv). trivial. 
exact Q2.

intros t t' t_eq_t' s; split.
apply (H (s,t)); trivial.
apply (H (s,t')); trivial.
symmetry; assumption.
Qed.

Lemma equiv_rpo_equiv_2 :
  forall bb t t', equiv t t' -> (forall s, rpo bb t s <-> rpo bb t' s).
Proof.
intro bb.
assert (H : forall p, match p with (s,t) =>
                              forall t', equiv t t' -> rpo bb t s -> rpo bb t' s
                 end).
intro p; pattern p; refine (well_founded_ind wf_size2 _ _ _); clear p.
intros [s t] IH t' t_eq_t' t_lt_s.
inversion t_eq_t' as [ t'' | g g' l1 l2 Stat Statg' g_eq_g' l1_eq_l2 | g g' l1 l2 Stat Statg' g_eq_g' P]; subst.
(* 1/4 equivalence is syntactic identity *)
trivial.
(* 1/3 equivalence with Lex top symbol *)
inversion t_lt_s as  [f l t'' t' t'_mem_l t''_le_t'
                            | f f' l l' g_prec_f l'_lt_s
                            | f' f l l' Stat_g Stat' f_stat_g L ll1_lt_l ll_lt_s
                            | f' f l l' Stat_g Stat' f_stat_g ll1_lt_l ]; subst.
(* 1/6 equivalence with Lex top symbol , Subterm *)
destruct t''_le_t' as [t'' t' t''_eq_t' | t'' t' t''_lt_t'];
apply Subterm with t'; trivial.
apply Equiv.
transitivity t''; trivial.
symmetry; trivial.
apply Lt.
apply (IH (t',t'')); trivial.
apply size2_lex1_mem; trivial.
(* 1/5 equivalence with Lex top symbol,  Top_gt *)
apply Top_gt; trivial.
apply prec_eq_prec2 with g; trivial.
intros s' s'_mem_l2. apply l'_lt_s.
rewrite (@mem_mem s' l1 l2); trivial.
(* 1/4 equivalence with Lex top symbol,  Top_eq_lex *)
apply Top_eq_lex; trivial.
apply prec_eq_transitive with g. apply prec_eq_sym. trivial. trivial.
rewrite <- (equiv_list_lex_same_length l1_eq_l2); assumption.
clear t_eq_t' ll_lt_s t_lt_s L; revert l2 l l1_eq_l2 ll1_lt_l IH.
induction l1 as [ | t1 l1]; intros l2 l l1_eq_l2 l1_lt_l IH;
inversion l1_lt_l as [ t1' s l1' l' t1'_lt_s L_eq 
                            | t1' s l1' l'' t1'_eq_s l1'_lt_l'' 
                            | s l']; subst;
inversion l1_eq_l2 as [ | t1'' t2 l1' l2' t1''_eq_t2 l1_eq_l2']; subst.
apply List_nil.
simpl; apply List_gt.
apply (IH (s,t1)); trivial.
apply size2_lex1; left; trivial.
simpl; apply List_eq.
transitivity t1; trivial.
symmetry; trivial.
apply IHl1; trivial.
intros y H; apply IH.
refine (o_size2_trans _ _ _ H _).
apply size2_lex1_bis.
intros s' s'_in_l2; apply ll_lt_s.
rewrite (@mem_mem s' l1 l2); trivial.
(* 1/3 equivalence with Lex top symbol,  Top_eq_mul *)
rewrite Stat in Stat_g; discriminate.
(* 1/2 equivalence with Mul top symbol *)
inversion t_lt_s as  [f l t'' t' t'_mem_l t''_le_t'
                            | f f' l l' g_prec_f l'_lt_s
                            | f' f l l' Stat_g Stat' f_stat_g L ll1_lt_l ll_lt_s
                            | f' f l l' Stat_g Stat' f_stat_g ll1_lt_l ]; subst.
(* 1/5 equivalence with Mul top symbol , Subterm *)
destruct t''_le_t' as [t'' t' t''_eq_t' | t'' t' t''_lt_t'];
apply Subterm with t'; trivial.
apply Equiv.
transitivity t''; trivial.
symmetry; trivial.
apply Lt.
apply (IH (t',t'')); trivial.
apply size2_lex1_mem; trivial.
(* 1/4 equivalence with Mul top symbol,  Top_gt *)
apply Top_gt; trivial.
apply prec_eq_prec2 with g; trivial.
intros s' s'_mem_l2; apply l'_lt_s.
rewrite (mem_permut0_mem equiv_equiv s' P); trivial.
(* 1/3 equivalence with Mul top symbol,  Top_eq_lex *)
rewrite Stat in Stat_g; discriminate.
(* 1/3 equivalence with Mul top symbol,  Top_eq_mul *)
apply Top_eq_mul; trivial.
apply prec_eq_transitive with g. apply prec_eq_sym; trivial. trivial.
inversion ll1_lt_l as [a lg ls lc l' l'' Q1 Q2 ls_lt_alg]; subst.
apply (@List_mul bb a lg ls lc); trivial. 
apply permut0_trans with l1.
exact equiv_equiv.
apply (permut0_sym equiv_equiv). assumption. assumption.

intros t t' t_eq_t' s; split.
apply (H (s,t)); trivial.
apply (H (s,t')); trivial.
symmetry; assumption.
Qed.

Lemma equiv_rpo_equiv_3 :
  forall bb t t', equiv t t' -> (forall s, rpo_eq bb s t <-> rpo_eq bb s t').
Proof.
intro bb.
assert (H: forall t t', equiv t t' -> (forall s, rpo_eq bb s t -> rpo_eq bb s t')).
intros t t' t_eq_t' s s_le_t; inversion s_le_t; subst.
apply Equiv; transitivity t; trivial.
apply Lt; rewrite <- (equiv_rpo_equiv_1 _ t_eq_t'); trivial.
intros t t' t_eq_t' s; split; apply H; trivial.
symmetry; trivial.
Qed.

Lemma equiv_rpo_equiv_4 :
  forall bb t t', equiv t t' -> (forall s, rpo_eq bb t s <-> rpo_eq bb t' s).
Proof.
intro bb.
assert (H: forall t t', equiv t t' -> (forall s, rpo_eq bb t s -> rpo_eq bb t' s)).
intros t t' t_eq_t' s t_le_s; inversion t_le_s; subst.
apply Equiv; transitivity t; trivial;
symmetry; trivial.
apply Lt; rewrite <- (equiv_rpo_equiv_2 _ t_eq_t'); trivial.
intros t t' t_eq_t' s; split; apply H; trivial.
symmetry; trivial.
Qed.

(** ** rpo is a preorder, and its reflexive closure is an ordering. *)

Lemma rpo_subterm_equiv :
 forall bb s t, equiv t s -> forall tj, direct_subterm tj t -> rpo bb tj s.
Proof.
intros bb s [ | f l] fl_eq_s tj; simpl. 
contradiction.
intro tj_in_l; rewrite <- (equiv_rpo_equiv_1 _  fl_eq_s).
apply Subterm with tj.
apply in_impl_mem; trivial.
intros; apply Eq.
intros; apply Equiv; apply Eq.
Qed.

Lemma rpo_subterm :
 forall bb s t, rpo bb t s -> forall tj, direct_subterm tj t -> rpo bb tj s.
Proof.
intros bb s t; 
cut (forall p : term * term,
             match p with
              | (s,t) => rpo bb t s -> forall tj, direct_subterm tj t -> rpo bb tj s
             end).
intro H; apply (H (s,t)).

clear s t; intro p; pattern p; refine (well_founded_ind wf_size2 _ _ _); clear p.
intros [s [ v | f l]] IH t_lt_s tj tj_in_l; simpl in tj_in_l; [ contradiction | idtac].
inversion t_lt_s as [ f' l' t' s' s'_in_l' t'_le_s'
                               | f' g' k k' g'_prec_f' H
                               | f' g k k' Sf' Sg f_eq_g L k'_lt_k H
                               | f' g k k' Sf' Sg f_eq_g k'_lt_k ].
(* 1/4 Subterm *)
subst; inversion t'_le_s' as [ t'' s'' t'_eq_s' | t'' s'' t'_lt_s']; clear t'_le_s'; subst.
apply (@Subterm bb f' l' tj s'); trivial;
apply Lt; apply rpo_subterm_equiv with (Term f l); trivial.
apply (@Subterm bb f' l' tj s'); trivial.
apply Lt; apply (IH (s', Term f l)); trivial.
apply size2_lex1_mem; trivial.
(* 1/3 Top_gt *)
subst; apply H; apply in_impl_mem; trivial.
intros; apply Eq.
(* 1/2 Top_eq_lex *)
subst; apply H; apply in_impl_mem; trivial.
intros; apply Eq.
(* Top_eq_mul *)
inversion k'_lt_k as [a lg ls lc l1 l2 P1 P2 H']; subst.
assert (tj_mem_l := in_impl_mem equiv Eq tj l tj_in_l).
rewrite (mem_permut0_mem equiv_equiv tj P1) in tj_mem_l.
rewrite <- mem_or_app in tj_mem_l.
destruct tj_mem_l as [tj_mem_ls | tj_mem_llc].
destruct (H' _ tj_mem_ls) as [a' [a'_mem_a_lg tj_lt_a']].
apply (@Subterm bb g k tj a').
rewrite (mem_permut0_mem equiv_equiv a' P2); rewrite app_comm_cons.
rewrite <- mem_or_app; left; trivial.
apply Lt; trivial.
apply (@Subterm bb g k tj tj).
rewrite (mem_permut0_mem equiv_equiv tj P2).
right; rewrite <- mem_or_app; right; trivial.
apply Equiv; apply Eq.
Qed.

Lemma rpo_subterm_mem :
 forall bb s f l, rpo bb (Term f l) s -> forall tj, mem equiv tj l -> rpo bb tj s.
Proof.
intros bb s f l fl_lt_s tj tj_mem_l.
destruct (mem_split_set _ _ equiv_bool_ok _ _ tj_mem_l) as [tj' [l1 [l2 [tj_eq_tj' [H _]]]]].
simpl in tj_eq_tj'; simpl in H.
rewrite (equiv_rpo_equiv_2  _ tj_eq_tj').
apply rpo_subterm with (Term f l); trivial.
subst l; simpl; apply in_or_app; right; left; trivial.
Qed.

#[global] Instance EQA : Equivalence equiv.

Proof. generalize equiv_equiv. firstorder. Qed.

#[global] Instance LP : Equivalence (permut0 equiv).

Proof.
  split; intro x.
  apply permut0_refl. apply equiv_equiv.
  apply permut0_sym. apply equiv_equiv.
  apply permut0_trans. apply equiv_equiv.
Qed.

#[global] Instance mem_morph2 : Proper (equiv ==> permut0 equiv ==> iff) (mem equiv).

Proof. exact (mem_morph2 equiv_equiv). Qed.

#[global] Instance app_morph :
  Proper (permut0 equiv ==> permut0 equiv ==> permut0 equiv) (@List.app term).

Proof. exact (app_morph equiv_equiv). Qed.

#[global] Instance add_A_morph :
  Proper (equiv ==> permut0 equiv ==> permut0 equiv) (@List.cons term).

Proof. exact (add_A_morph equiv_equiv). Qed.

Lemma rpo_trans : forall bb u t s, rpo bb u t -> rpo bb t s ->  rpo bb u s.

Proof.
intros bb u t s;
cut (forall triple : term * (term * term),
       match triple with
       | (s,(t,u)) => rpo bb t s -> rpo bb u t -> rpo bb u s
       end).
intros H u_lt_t t_lt_s; apply (H (s,(t,u))); trivial.
clear s t u; intro triple; pattern triple; 
refine (well_founded_ind wf_size3 _ _ triple); clear triple.
intros [[v | f l] [t u]] IH.
(* 1/2 Variable case *)
intros t_lt_v; inversion t_lt_v.
(* 1/1 Compound case *)
intros t_lt_fl u_lt_t;
inversion t_lt_fl as [ f'' l' s' t' t'_in_l' t_le_t'
                               | f'' f' k'' l' f'_prec_f H''
                               | f'' g'' k'' l' Sf Sg f''_eq_g'' L l'_lt_l H H1 H2 
                               | f'' g'' k'' l' Sf Sg f''_eq_g'' l'_lt_l ]; subst.
(* 1/4 Subterm *)
apply Subterm with t'; trivial; apply Lt;
inversion t_le_t' as [t'' t''' t_eq_t' | t'' t''' t_lt_t']; subst.
rewrite <- (equiv_rpo_equiv_1  _ t_eq_t'); trivial.
apply (IH (t',(t,u))); trivial.
apply size3_lex1_mem; trivial.
(* 1/3 Top_gt *)
inversion u_lt_t as [ f'' l'' s' t' t'_in_l' u_le_t'
                               | g'' f'' k'' l'' f''_prec_f'' H'''
                               | g'' g' k'' l'' Sf' Sf'' g''_eq_g' L l''_lt_l' H H1 H2 
                               | g'' g' k'' l'' Sf' Sf'' g''_eq_g' l''_lt_l' ]; subst.
(* 1/6 Top_gt, Subterm *)
inversion u_le_t' as [t'' t''' u_eq_t' | t'' t''' u_lt_t']; subst.
rewrite (equiv_rpo_equiv_2 _ u_eq_t'); trivial; apply H''; trivial.
apply (IH (Term f l,(t',u))); trivial.
apply size3_lex2_mem; trivial.
apply H''; trivial.
(* 1/5 Top_gt, Top_gt *)
apply Top_gt.
apply prec_transitive with f'; trivial.
intros u u_in_l''; apply (IH (Term f l, (Term f' l', u))); trivial.
apply size3_lex3_mem; trivial.
apply H'''; trivial.
(* 1/4 Top_gt, Top_eq_lex *)
apply Top_gt. apply prec_eq_prec2 with f'. trivial.
apply prec_eq_sym. trivial.
intros u u_in_l''; apply (IH (Term f l, (Term f' l', u))); trivial.
apply size3_lex3_mem; trivial.
apply H; trivial.
(* 1/3 Top_gt, Top_eq_mul *)
apply Top_gt. apply prec_eq_prec2 with f'. trivial.
apply prec_eq_sym. trivial.
intros u u_in_l''. apply (IH (Term f l, (Term f' l', u))); trivial.
apply size3_lex3_mem; trivial.
apply rpo_subterm_mem with g'' l''; trivial.
(* 1/2 Top_eq_lex *)
inversion u_lt_t as [ f''' l'' s' t' t'_in_l' u_le_t'
                               | g'' f''' k'' l'' f''_prec_f' H'''
                               | g'' f''' k'' l'' Sf' Sg' f_eq_g' L' l''_lt_l' H' H1 H2 
                               | g'' f''' k'' l'' Sf' Sg' f_eq_g' l''_lt_l' ]; subst.
(* 1/5 Top_eq_lex, Subterm *)
inversion u_le_t' as [t'' t''' u_eq_t' | t'' t''' u_lt_t']; subst.
rewrite (equiv_rpo_equiv_2 _ u_eq_t').
apply rpo_subterm_mem with f'' l'; trivial.
apply (IH (Term f l, (t', u))); trivial.
apply size3_lex2_mem; trivial.
apply H; trivial.
(* 1/4 Top_eq_lex, Top_gt *)
apply Top_gt. apply prec_eq_prec1 with f''; trivial.
intros u u_in_l''. apply (IH (Term f l, (Term f'' l', u))). 
apply size3_lex3_mem. trivial. trivial. 
apply H'''. trivial. 

(* 1/3 Top_eq_lex, Top_eq_lex *)
apply Top_eq_lex; trivial.
apply prec_eq_transitive with f''. trivial. trivial.
destruct L as [L | [L1 L2]].
rewrite L; assumption.
destruct L' as [L' | [L1' L2']].
rewrite <- L'; right; split; assumption.
right; split; assumption.
generalize l' l'' l'_lt_l l''_lt_l' IH; clear l' l'' l'_lt_l l''_lt_l' IH H H' t_lt_fl u_lt_t L L';
induction l as [ | s l]; intros l' l'' l'_lt_l l''_lt_l' IH.
inversion l'_lt_l.
inversion l'_lt_l as [ t s' k' k t_lt_s  | t s' k' k t_eq_s k'_lt_k | t k];
inversion l''_lt_l' as [ u t' k'' h' u_lt_t | u t' k'' h' u_eq_t k''_lt_k' | u k1].
subst; injection H3; intros; subst; apply List_gt.
apply (IH (s,(t,u))); trivial.
apply size3_lex1; left; trivial.
subst; injection H3; intros; subst; apply List_gt.
rewrite (equiv_rpo_equiv_2 _ u_eq_t); trivial.
apply List_nil.
subst; injection H3; intros; subst; apply List_gt.
rewrite <- (equiv_rpo_equiv_1 _ t_eq_s); trivial.
subst; injection H3; intros; subst; apply List_eq.
transitivity t; trivial.
apply IHl with k'; trivial.
intros; apply IH;
apply o_size3_trans with (Term f l, (Term f k', Term f k'')); trivial.
apply size3_lex1_bis.
apply List_nil.
subst; discriminate H3.
subst; discriminate H3.
subst; discriminate H3.
intros u u_in_l''. apply (IH (Term f l, (Term f'' l', u))); trivial.
apply size3_lex3_mem. trivial.
apply H'; trivial.
(* 1/2 Top_eq_lex, Top_eq_mul *)
rewrite Sf in Sg'; discriminate.
(* 1/1 Top_eq_mul *)
inversion u_lt_t as [ f''' l'' s' t' t'_in_l' u_le_t'
                               | g'' f''' k'' l'' f''_prec_f' H'''
                               | g'' f''' k'' l'' Sf' Sf''' Seq_g''_f''' L l''_lt_l' H H1 H2 
                               | g'' f''' k'' l'' Sf' Sf''' Seq_g''_f''' l''_lt_l' ]; subst.
(* 1/4 Top_mul_lex, Subterm *)
inversion u_le_t' as [t'' t''' u_eq_t' | t'' t''' u_lt_t']; subst.
rewrite (equiv_rpo_equiv_2 _ u_eq_t').
apply rpo_subterm_mem with f'' l'; trivial. 
apply (IH (Term f l, (t', u))); trivial.
apply size3_lex2_mem; trivial.
apply rpo_subterm_mem with f'' l'; trivial.
(* 1/3 Top_eq_mul, Top_gt *)
apply Top_gt; trivial. apply prec_eq_prec1 with f''. trivial. trivial.
intros u u_in_l''; apply (IH (Term f l, (Term f'' l', u))); trivial.
apply size3_lex3_mem; trivial.
apply H'''; trivial.
(* 1/2 Top_eq_mul, Top_eq_lex *)
rewrite Sf in Sf'''; discriminate.
(* 1/1 Top_eq_mul, Top_eq_mul *)
apply Top_eq_mul; trivial. apply prec_eq_transitive with f''. trivial. trivial. 
destruct l'_lt_l as [a lg ls lc l l' P' P ls_lt_alg].
destruct l''_lt_l' as [a' lg' ls' lc' l' l'' Q' Q ls'_lt_alg'].
rewrite P' in Q; rewrite app_comm_cons in Q.
destruct (@ac_syntactic _ _ equiv_equiv _ equiv_bool_ok _ _ _ _ Q) as [k1 [k2 [k3 [k4 [P1 [P2 [P3 P4]]]]]]]. 
apply (@List_mul bb a (lg ++ k2) (ls' ++ k3) k1).
rewrite Q'.
rewrite <- ass_app.
rewrite <- permut_app1.
rewrite list_permut0_app_app; trivial. apply equiv_equiv. apply equiv_equiv.
rewrite P.
rewrite <- permut0_cons;[|apply equiv_equiv|reflexivity].
rewrite <- ass_app.
rewrite <- permut_app1.
rewrite list_permut0_app_app; trivial.  apply equiv_equiv. apply equiv_equiv.
intros b b_mem_ls'_k3; rewrite <- mem_or_app in b_mem_ls'_k3.
destruct b_mem_ls'_k3 as [b_mem_ls' | b_mem_k3].
destruct (ls'_lt_alg'  _ b_mem_ls') as [a'' [a''_in_a'lg' b_lt_a'']].
rewrite (mem_permut0_mem equiv_equiv a'' P4) in a''_in_a'lg'.
rewrite <- mem_or_app in a''_in_a'lg'.
destruct a''_in_a'lg' as [a''_mem_k2 | a''_mem_k4].
exists a''; split; trivial.
rewrite app_comm_cons; rewrite <- mem_or_app; right; trivial.
destruct (ls_lt_alg a'') as [a3 [a3_in_alg a''_lt_a3]].
rewrite (mem_permut0_mem equiv_equiv a'' P2).
rewrite <- mem_or_app; right; trivial.
exists a3; split.
rewrite app_comm_cons; rewrite <- mem_or_app; left; trivial.
apply (IH (a3,(a'',b))); trivial.
apply size3_lex1_mem.
rewrite (mem_permut0_mem equiv_equiv a3 P).
rewrite app_comm_cons; rewrite <- mem_or_app; left; trivial.
destruct (ls_lt_alg b) as [a'' [a''_in_alg b_lt_a'']].
rewrite (mem_permut0_mem equiv_equiv b P2); rewrite <- mem_or_app; left; trivial.
exists a''; split; trivial.
rewrite app_comm_cons; rewrite <- mem_or_app; left; trivial.
Qed.

Lemma rpo_mul_remove_equiv_aux :
  forall bb l l' s s', (forall t, mem equiv t (s :: l) -> rpo bb t t -> False) -> 
                      equiv s s' -> rpo_mul bb (s :: l) (s' :: l') -> rpo_mul bb l l'. 
Proof.
intros bb l l' s s' Antirefl s_eq_s' sl_lt_s'l';  
inversion sl_lt_s'l' as [a lg ls lc k' k P P' ls_lt_alg]; subst.
assert (s_mem_ls_lc : mem equiv s (ls ++ lc)).
rewrite <- (mem_permut0_mem equiv_equiv s P); left; reflexivity.
rewrite <- mem_or_app in s_mem_ls_lc.
destruct s_mem_ls_lc as [s_mem_ls | s_mem_lc].
assert (s'_mem_alg_lc : mem equiv s' (a :: lg ++ lc)).
rewrite <- (mem_permut0_mem equiv_equiv s' P'); left; reflexivity.
rewrite app_comm_cons in s'_mem_alg_lc.
rewrite <- mem_or_app in s'_mem_alg_lc.
destruct s'_mem_alg_lc as [s'_mem_alg | s'_mem_lc].
(* 1/3 s in in ls, s' is in (a :: lg) *)
destruct lg as [ | g lg].
(* 1/4 s in in ls, s' is in (a :: lg), lg = nil *)
assert (s'_eq_a : equiv s' a).
destruct s'_mem_alg; trivial; contradiction.
destruct (ls_lt_alg _ s_mem_ls) as [a' [[a_eq_a' | a'_mem_nil] b_lt_a']].
apply False_rect.
apply (Antirefl s).
left; reflexivity.
rewrite (equiv_rpo_equiv_1 _ s_eq_s').
rewrite (equiv_rpo_equiv_1 _ s'_eq_a).
rewrite <- (equiv_rpo_equiv_1 _ a_eq_a'); trivial.
contradiction.
(* s in in ls, s' is in (a :: lg), 1/3 lg <> nil *)
destruct (mem_split_set _ _ equiv_bool_ok _ _ s'_mem_alg) as [u' [alg' [alg'' [s'_eq_u' [H _]]]]]; 
simpl in s'_eq_u'; simpl in H; subst.
assert (P'' : permut0 equiv l' ((alg' ++ alg'') ++ lc)).
rewrite app_comm_cons in P'; rewrite H in P'.
rewrite <- ass_app in P'; simpl in P'.
rewrite <- ass_app; rewrite <- permut0_cons_inside in P'; trivial. apply equiv_equiv.
destruct (mem_split_set _ _ equiv_bool_ok _ _ s_mem_ls) as [u [ls' [ls'' [s_eq_u [H' _]]]]]; 
simpl in s_eq_u; simpl in H'; subst.
assert (ls'ls''_lt_alg'alg'' : forall b,
            mem equiv b (ls' ++ ls'') -> exists a', mem equiv a' (alg' ++ alg'') /\ rpo bb b a').
intros b b_in_ls'ls''; destruct (ls_lt_alg b) as [a' [a'_mem_aglg b_lt_a']].
apply mem_insert; trivial.
rewrite H in a'_mem_aglg.
rewrite <- mem_or_app in a'_mem_aglg.
destruct a'_mem_aglg as [a'_mem_alg' | [u'_eq_a' | a'_mem_alg'']].
exists a'; split; trivial.
rewrite <- mem_or_app; left; trivial.
destruct (ls_lt_alg a') as [a'' [a''_mem_aglg a'_lt_a'']].
rewrite <- mem_or_app; right; left.
transitivity u'; trivial.
transitivity s; trivial.
symmetry.
transitivity s'; trivial.
exists a''; split.
apply diff_mem_remove with u'.
intro a''_eq_u'.
destruct (mem_split_set _ _ equiv_bool_ok u (s :: l)) as [u'' [l1 [l2 [u_eq_u'' [H' _]]]]].
left; symmetry; trivial.
simpl in u_eq_u''; simpl in H'.
apply (Antirefl u'').
rewrite (mem_permut0_mem equiv_equiv u'' P).
rewrite <- mem_or_app; left.
rewrite <- mem_or_app; right; left; symmetry; trivial.
assert (u''_eq_u' : equiv u'' u'). 
transitivity s'; trivial.
transitivity s; trivial.
transitivity u.
symmetry; trivial.
symmetry; trivial.
rewrite (equiv_rpo_equiv_2 _ u''_eq_u').
rewrite <- (equiv_rpo_equiv_2 _ u'_eq_a').
rewrite (equiv_rpo_equiv_1 _ u''_eq_u').
rewrite <- (equiv_rpo_equiv_1 _ a''_eq_u'); trivial.
rewrite <- H; trivial.
apply rpo_trans with a'; trivial.
exists a'; split; trivial.
rewrite <- mem_or_app; right; trivial.
assert (L : length (alg' ++ alg'') = S (length lg)).
assert (L' := f_equal (fun l => length l) H).
simpl in L'; rewrite length_app in L'; simpl in L'.
rewrite plus_comm in L'; simpl in L'; rewrite plus_comm in L'.
rewrite <- length_app in L'; injection L'; intro L''; symmetry; assumption.
destruct (alg' ++ alg'') as [ | a' lg'].
discriminate.
apply (@List_mul bb a' lg' (ls' ++ ls'') lc); trivial.
rewrite <- ass_app in P; simpl in P.
rewrite <- permut0_cons_inside in P; trivial;[|apply equiv_equiv].
rewrite <- ass_app; trivial.
(* 1/2 s in in ls, s' is in lc *)
destruct (mem_split_set _ _ equiv_bool_ok _ _ s'_mem_lc) as [s'' [lc' [lc'' [s_eq_s'' [H _]]]]].
simpl in s_eq_s''; simpl in H.
apply (@List_mul bb a lg ls (lc' ++ lc'')); trivial.
rewrite H in P.
rewrite ass_app in P.
rewrite <- permut0_cons_inside in P.
rewrite ass_app; trivial. 
apply equiv_equiv.
transitivity s'; trivial.
rewrite H in P'.
rewrite app_comm_cons in P'.
rewrite ass_app in P'.
rewrite <- permut0_cons_inside in P'; trivial.
rewrite app_comm_cons; rewrite ass_app; trivial. apply equiv_equiv.
(* 1/1 s in lc *)
destruct (mem_split_set _ _ equiv_bool_ok _ _ s_mem_lc) as [s'' [lc' [lc'' [s_eq_s'' [H _]]]]].
simpl in s_eq_s''; simpl in H.
apply (@List_mul bb a lg ls (lc' ++ lc'')); trivial.
rewrite H in P.
rewrite ass_app in P.
rewrite <- permut0_cons_inside in P; trivial. 
rewrite ass_app; trivial. apply equiv_equiv.
rewrite H in P'.
rewrite app_comm_cons in P'.
rewrite ass_app in P'.
rewrite <- permut0_cons_inside in P'.
rewrite app_comm_cons; rewrite ass_app; trivial. apply equiv_equiv.
transitivity s; trivial.
symmetry; trivial.
Qed.

Lemma rpo_antirefl :
  forall bb s, rpo bb s s -> False.
Proof.
intros bb s; pattern s; apply term_rec3_mem; clear s.
intros v v_lt_v; inversion v_lt_v.
intros f l IHl t_lt_t;
inversion t_lt_t  as [ f' l' s'' s' s'_mem_l s_le_s'
                               | f' f'' l' l'' f_prec_f H' H1 H2
                               | f' g' l' l'' Sf Sg f_eq_g L l_lt_l H H1 H2
                               | f' g' l' l'' Sf Sg f_eq_g l_lt_l ]; clear t_lt_t; subst.
(* 1/4 Antirefl, subterm *)
apply (IHl s'); trivial.
inversion s_le_s' as [u u' s_eq_s' | u u' s_lt_s']; subst.
rewrite <- (equiv_rpo_equiv_1 _ s_eq_s').
apply Subterm with s'; trivial; apply Equiv; apply Eq.
apply rpo_trans with (Term f l); trivial.
apply Subterm with s'; trivial; apply Equiv; apply Eq.
(* 1/3 Antirefl, Top_gt *)
apply (prec_antisym Prec) with f; trivial.
(* 1/2 Antirefl, Top_eq_lex *)
clear H;induction l as [| t l]. inversion l_lt_l. 
inversion l_lt_l as [ s t' l' l'' s_lt_t | 
  s t' l' l'' s_eq_t l'_lt_l'' | 
    s l']; subst.
apply IHl with t; trivial; left; reflexivity.
apply IHl0; trivial.
intros s s_in_l; apply IHl; right; trivial.
left; apply eq_refl.

(* 1/1 Antirefl, Top_eq_mul *)
induction l as [ | s l].
inversion l_lt_l as [a lg ls lc l' l'' ls_lt_alg]; subst.
assert (L := permut_length H); discriminate.
apply IHl0.
intros t t_mem_l; apply IHl; right; trivial.
apply rpo_mul_remove_equiv_aux with s s; trivial.
apply Eq.
Qed.

Lemma rpo_closure :
  forall bb s t u, 
  (rpo bb t s -> rpo bb u t -> rpo
 bb u s) /\
  (rpo bb s t -> rpo bb t s -> False) /\
  (rpo bb s s -> False) /\
  (rpo_eq bb s t -> rpo_eq bb t s -> equiv s t).
Proof.
intros bb s t u; repeat split.
intros; apply (@rpo_trans bb u t s); trivial.
intros; apply (@rpo_antirefl bb s); apply rpo_trans with t; trivial.
apply rpo_antirefl.
intros s_le_t t_le_s;
destruct s_le_t as [s t s_eq_t | s t s_lt_t]; trivial.
destruct t_le_s as [t s t_eq_s | t s t_lt_s].
symmetry; trivial.
assert False; [idtac | contradiction].
apply (@rpo_antirefl bb s); apply rpo_trans with t; trivial.
Qed.

(** ** Well-foundedness of rpo. *)
Lemma equiv_acc_rpo :
  forall bb t t', equiv t t' -> Acc (rpo bb) t -> Acc (rpo bb) t'.
Proof.
intros bb t t' t_eq_t' Acc_t; apply Acc_intro.
intro s; rewrite <- (equiv_rpo_equiv_1 _ t_eq_t').
inversion Acc_t as [H]; apply (H s); trivial.
Qed.

Inductive rpo_lex_rest (bb bb' : nat) : list term -> list term -> Prop :=
| Rpo_lex_rest : 
     forall l l', (length l = length l' \/ (length l' <= bb /\ length l <= bb)) ->
     (forall s, mem equiv s l -> Acc (rpo bb') s) -> (forall s, mem equiv s l' -> Acc (rpo bb') s) ->
     rpo_lex bb' l' l -> rpo_lex_rest bb bb' l' l.

Lemma wf_rpo_lex_rest : forall bb bb', well_founded (rpo_lex_rest bb bb').
Proof.
intro bb; unfold well_founded; induction bb.
(* 1/2 bb = 0 *)
intros bb' l; revert bb'; pattern l; apply list_rec2; clear l.
induction n as [ | n]; intros [ | a l] L bb'.
apply Acc_intro; intros k H; inversion H as [k' k'' L' Acc_k Acc_k' H' H1 H2]; clear H; subst; inversion H'.
inversion L.
apply Acc_intro; intros k H; inversion H as [k' k'' L' Acc_k Acc_k' H' H1 H2]; clear H; subst; inversion H'.
apply Acc_intro; intros k H; inversion H as [k' k'' L' Acc_k Acc_k' H' H1 H2]; subst.
assert (Acc_a : Acc (rpo bb') a).
apply Acc_k; left; apply Eq.
assert (Acc_l' : forall s : term, mem equiv s l -> Acc (rpo bb') s).
intros; apply Acc_k; right; assumption.
apply Acc_inv with (a :: l); [idtac | assumption].
clear k H L' Acc_k' H'.
clear -IHn Acc_a L Acc_l'.
simpl in L; generalize (le_S_n _ _ L); clear L; intro L.
revert l L Acc_l'; induction Acc_a as [a Acc_a IHa]; intros l L Acc_l.
assert (Acc_l' := IHn _ L bb').
induction Acc_l' as [l Acc_l' IHl].
apply Acc_intro; intros l' H; inversion H as [ k k' L' Acc_al Acc_l'' H' H1 H2]; clear H; subst.
destruct L' as [L' | [L1 L2]]; [idtac | inversion L2].
inversion H' as [u s' k' k'' u_lt_s | s' s'' k' k'' s'_eq_s k'_lt_l H1 H2 | u k']; clear H'; subst.
(* 1/4 *)
apply IHa; trivial.
injection L'; clear L'; intro L'; rewrite <- L'; assumption.
intros; apply Acc_l''; right; assumption.
(* 1/3 *)
apply Acc_intro.
intros k'' H'; apply Acc_inv with (a :: k').
apply IHl.
constructor; trivial.
left; injection L'; intro; assumption.
intros; apply Acc_l''; right; assumption.
injection L'; clear L'; intro L'; rewrite <- L'; assumption.
intros; apply Acc_l''; right; assumption.
inversion  H' as [k1 k1' L'' Acc_l1 Acc_l1' H1' H1 H2]; subst.
constructor; trivial.
simpl; intros s [s_eq_a | s_in_k']; [idtac | apply Acc_l1; right; assumption].
apply Acc_intro; intros; apply Acc_inv with a.
apply Acc_intro; apply Acc_a; trivial.
rewrite <- (equiv_rpo_equiv_1 _ s_eq_a); trivial.
inversion H1' as [u s'' k1' k1'' u_lt_s | s1' s'' k1' k1'' s'_eq_s1 k'_lt_l1 H1 H2 | u k1']; clear H1'; subst.
constructor 1; trivial.
rewrite <- (equiv_rpo_equiv_1 _ s'_eq_s); trivial.
constructor 2; trivial.
transitivity s'; trivial.
constructor 3.
(* 1/2 *)
apply Acc_intro; intros l' H; inversion H as [ k k' L'' Acc_l1 Acc_l1' H' H1 H2]; clear H; subst.
inversion H'.

(* 1/1 induction step *)
intros bb' l.
apply Acc_intro; intros k H; inversion H as [k' k'' L' Acc_k Acc_k' H' H1 H2]; subst.
destruct l as [ | a l].
inversion H'.
apply Acc_inv with (a :: l); [idtac | assumption].
clear -IHbb Acc_k.
assert (Acc_a : Acc (rpo bb') a).
apply Acc_k; left; apply Eq.
assert (Acc_l : forall s : term, mem equiv s l -> Acc (rpo bb') s).
intros; apply Acc_k; right; assumption.
revert Acc_l; clear Acc_k.
revert l; induction Acc_a as [a Acc_a IHa]; intros l.
pattern l; apply (well_founded_ind (IHbb bb')); clear l; intros l IHl Acc_l.
apply Acc_intro; intros l' H; inversion H as [ k k' L Acc_al Acc_l' H' H1 H2]; clear H; subst.
inversion H' as [u s' k' k'' u_lt_s | s' s'' k' k'' s'_eq_s k'_lt_l H1 H2 | u k']; clear H'; subst.
(* 1/3 *)
apply IHa; trivial.
intros; apply Acc_l'; right; assumption.
(* 1/2 *)
apply Acc_intro.
intros k'' H'; apply Acc_inv with (a :: k').
apply IHl; constructor.
destruct L as [L | [L1 L2]].
left; injection L; intro; assumption.
right; split; apply le_S_n; assumption.
intros; apply Acc_al; right; assumption.
intros; apply Acc_l'; right; assumption.
assumption.
apply Acc_inv; apply Acc_l'; right; assumption.
inversion  H' as [ k1 k1' L' Acc_l1 Acc_l1' H1' H1 H2]; subst.
constructor; trivial.
simpl; intros s [s_eq_a | s_in_k']; [idtac | apply Acc_l1; right; assumption].
apply Acc_intro; intros; apply Acc_inv with a.
apply Acc_intro; apply Acc_a; trivial.
rewrite <- (equiv_rpo_equiv_1 _ s_eq_a); trivial.
inversion H1' as [u s'' k1' k1'' u_lt_s | s1' s'' k1' k1'' s'_eq_s1 k'_lt_l1 H1 H2 | u k1']; clear H1'; subst.
constructor 1; trivial.
rewrite <- (equiv_rpo_equiv_1 _ s'_eq_s); trivial.
constructor 2; trivial.
transitivity s'; trivial.
constructor 3.
(* 1/1 *)
apply Acc_intro; intros l' H; inversion H as [ k k' L' Acc_l1 Acc_l1' H' H1 H2]; clear H; subst.
inversion H'.
Qed.

(** Definition of a finer grain for multiset extension. *)
Inductive rpo_mul_step (bb : nat) : list term -> list term -> Prop :=
  | List_mul_step : 
       forall a ls lc l l',  
        permut0 equiv l' (ls ++ lc) -> permut0 equiv l (a :: lc) ->
       (forall b, mem equiv b ls -> rpo bb b a) ->
       rpo_mul_step bb l' l.

(** The plain multiset extension is in the transitive closure of
the finer grain extension. *)
Lemma rpo_mul_trans_clos :
  forall bb, inclusion _ (rpo_mul bb) (clos_trans _ (rpo_mul_step bb)).
Proof.
intro bb; unfold inclusion; intros l' l H; 
inversion H as [a lg ls lc k k' P' P ls_lt_alg]; subst.
generalize l' l a ls lc P P' ls_lt_alg;
clear l' l a ls lc P P' ls_lt_alg H;
induction lg as [ | g lg]; intros l' l a ls lc P P' ls_lt_alg.
apply t_step; apply (@List_mul_step bb a ls lc); trivial.
intros b b_in_ls; destruct (ls_lt_alg b b_in_ls) as [a' [[a'_eq_a | a'_in_nil] b_lt_a']].
rewrite <- (equiv_rpo_equiv_1 _ a'_eq_a); trivial.
contradiction.
assert (H: exists ls1, exists ls2, 
 permut0 equiv ls (ls1 ++ ls2) /\
 (forall b, mem equiv b ls1 -> rpo bb b g) /\
 (forall b, mem equiv b ls2 -> exists a', mem equiv a' (a :: lg) /\ rpo bb b a')).
clear P'; induction ls as [ | s ls].
exists (nil : list term); exists (nil : list term); intuition. reflexivity.
destruct IHls as [ls1 [ls2 [P' [ls1_lt_g ls2_lt_alg]]]].
intros b b_in_ls; apply ls_lt_alg; right; trivial.
destruct (ls_lt_alg s) as [a' [[a'_eq_a | [a'_eq_g | a'_in_lg]] b_lt_a']].
left; reflexivity.
exists ls1; exists (s :: ls2); repeat split; trivial.
rewrite <- permut0_cons_inside; trivial. apply equiv_equiv.
reflexivity.
intros b [b_eq_s | b_in_ls2].
exists a; split.
left; reflexivity.
rewrite (equiv_rpo_equiv_2 _ b_eq_s).
rewrite <- (equiv_rpo_equiv_1 _ a'_eq_a); trivial.
apply ls2_lt_alg; trivial.
exists (s :: ls1); exists ls2; repeat split; trivial.
simpl; rewrite <- permut0_cons; trivial. apply equiv_equiv.
reflexivity.
intros b [b_eq_s | b_in_ls1].
rewrite (equiv_rpo_equiv_2 _ b_eq_s).
rewrite <- (equiv_rpo_equiv_1 _ a'_eq_g); trivial.
apply ls1_lt_g; trivial.
exists ls1; exists (s :: ls2); repeat split; trivial.
rewrite <- permut0_cons_inside; trivial. apply equiv_equiv.
reflexivity.
intros b [b_eq_s | b_in_ls2].
exists a'; split.
right; trivial.
rewrite (equiv_rpo_equiv_2 _ b_eq_s); trivial.
apply ls2_lt_alg; trivial.
destruct H as [ls1 [ls2 [Pls [ls1_lt_g ls2_lt_alg]]]].
apply t_trans with (g :: ls2 ++ lc).
apply t_step; apply (@List_mul_step bb g ls1 (ls2 ++ lc)); auto.
rewrite P'.
rewrite ass_app; rewrite <- permut_app2; trivial. apply equiv_equiv. reflexivity.
apply (IHlg (g :: ls2 ++ lc) l a ls2 (g :: lc)); trivial.
rewrite P.
simpl; rewrite <- permut0_cons;[|apply equiv_equiv|reflexivity].
rewrite <- permut0_cons_inside;[reflexivity|apply equiv_equiv|reflexivity].  
rewrite <- permut0_cons_inside;[reflexivity|apply equiv_equiv|reflexivity].  
Qed.

Inductive rpo_mul_rest (bb : nat) : list term -> list term -> Prop :=
| Rpo_mul_rest : 
     forall l l', (forall s, mem equiv s l -> Acc (rpo bb) s) -> 
                  (forall s, mem equiv s l' -> Acc (rpo bb) s) ->
     rpo_mul bb l' l -> rpo_mul_rest bb l' l.

Inductive rpo_mul_step_rest (bb : nat) : list term -> list term -> Prop :=
| Rpo_mul_step_rest : 
     forall l l', (forall s, mem equiv s l -> Acc (rpo bb) s) -> 
                  (forall s, mem equiv s l' -> Acc (rpo bb) s) ->
     rpo_mul_step bb l' l -> rpo_mul_step_rest bb l' l.

Lemma rpo_mul_rest_trans_clos :
  forall bb, inclusion _ (rpo_mul_rest bb) (clos_trans _ (rpo_mul_step_rest bb)).
Proof.
intro bb; unfold inclusion; intros l' l H; 
inversion H as [k k' Acc_l Acc_l' H' H1 H2 ]; subst.
inversion H' as [a lg ls lc k k' P' P ls_lt_alg]; subst.
generalize l' l a ls lc P' P ls_lt_alg Acc_l Acc_l'; 
clear l' l a ls lc P' P ls_lt_alg H Acc_l Acc_l' H';
induction lg as [ | g lg]; intros l' l a ls lc P' P ls_lt_alg Acc_l Acc_l'.
apply t_step; apply Rpo_mul_step_rest; trivial;
apply (@List_mul_step bb a ls lc); trivial.
intros b b_in_ls; destruct (ls_lt_alg b b_in_ls) as [a' [[a'_eq_a | a'_in_nil] b_lt_a']].
rewrite <- (equiv_rpo_equiv_1 _ a'_eq_a); trivial.
contradiction.
assert (H: exists ls1, exists ls2, 
 permut0 equiv ls (ls1 ++ ls2) /\
 (forall b, mem equiv b ls1 -> rpo bb b g) /\
 (forall b, mem equiv b ls2 -> exists a', mem equiv a' (a :: lg) /\ rpo bb b a')).
clear P'; induction ls as [ | s ls].
exists (nil : list term); exists (nil : list term); intuition. reflexivity.
destruct IHls as [ls1 [ls2 [P' [ls1_lt_g ls2_lt_alg]]]].
intros b b_in_ls; apply ls_lt_alg; right; trivial.
destruct (ls_lt_alg s) as [a' [[a'_eq_a | [a'_eq_g | a'_in_lg]] b_lt_a']].
left; reflexivity.
exists ls1; exists (s :: ls2); repeat split; trivial.
rewrite <- permut0_cons_inside; trivial. apply equiv_equiv.
reflexivity.
intros b [b_eq_s | b_in_ls2].
exists a; split.
left; reflexivity.
rewrite (equiv_rpo_equiv_2 _ b_eq_s).
rewrite <- (equiv_rpo_equiv_1 _ a'_eq_a); trivial.
apply ls2_lt_alg; trivial.
exists (s :: ls1); exists ls2; repeat split; trivial.
simpl; rewrite <- permut0_cons; trivial. apply equiv_equiv.
reflexivity.
intros b [b_eq_s | b_in_ls1].
rewrite (equiv_rpo_equiv_2 _ b_eq_s).
rewrite <- (equiv_rpo_equiv_1 _ a'_eq_g); trivial.
apply ls1_lt_g; trivial.
exists ls1; exists (s :: ls2); repeat split; trivial.
rewrite <- permut0_cons_inside; trivial. apply equiv_equiv.
reflexivity.
intros b [b_eq_s | b_in_ls2].
exists a'; split.
right; trivial.
rewrite (equiv_rpo_equiv_2 _ b_eq_s); trivial.
apply ls2_lt_alg; trivial.
destruct H as [ls1 [ls2 [Pls [ls1_lt_g ls2_lt_alg]]]].
apply t_trans with (g :: ls2 ++ lc).
apply t_step; apply Rpo_mul_step_rest; trivial.
simpl; intros s [g_eq_s | s_mem_ls2lc].
apply Acc_l.
rewrite P; right; left; trivial.
apply Acc_l'.
rewrite P'; rewrite <- mem_or_app.
rewrite <- mem_or_app in s_mem_ls2lc.
destruct s_mem_ls2lc as [s_mem_ls2 | s_mem_lc].
left; rewrite Pls; rewrite <- mem_or_app; right; trivial.
right; trivial.
apply (@List_mul_step bb g ls1 (ls2 ++ lc)); reflexivity || auto.
rewrite P'; rewrite Pls; rewrite ass_app; reflexivity || auto.
apply (IHlg (g :: ls2 ++ lc) l a ls2 (g :: lc)); trivial.
rewrite <- permut0_cons_inside; try reflexivity. apply equiv_equiv.
rewrite P.
rewrite <- permut0_cons;[|apply equiv_equiv|reflexivity]. 
simpl; rewrite <- permut0_cons_inside;[reflexivity|apply equiv_equiv|reflexivity].
simpl; intros s [g_eq_s | s_mem_ls2lc].
apply Acc_l.
rewrite P; right; left; trivial.
apply Acc_l'.
rewrite P'; rewrite <- mem_or_app.
rewrite <- mem_or_app in s_mem_ls2lc.
destruct s_mem_ls2lc as [s_mem_ls2 | s_mem_lc].
left; rewrite Pls; rewrite <- mem_or_app; right; trivial.
right; trivial.
Qed.

(** Splitting in two disjoint cases. *)
Lemma two_cases_rpo :
 forall bb a m n, 
 rpo_mul_step bb n (a :: m) ->
 (exists a', exists n', equiv a a' /\ permut0 equiv n (a' :: n') /\ 
                                                           rpo_mul_step bb n' m) \/
 (exists ls, (forall b, mem equiv b ls -> rpo bb b a) /\ permut0 equiv n (ls ++ m)).
Proof.
intros bb b m n M; inversion M as [a ls lc l l' P' P ls_lt_a]; subst.
assert (b_mem_a_lc : mem equiv b (a :: lc)).
rewrite <- (mem_permut0_mem equiv_equiv b P); left; reflexivity.
simpl in b_mem_a_lc; destruct b_mem_a_lc as [b_eq_a | b_mem_lc].
right; exists ls; repeat split; trivial.
intros c c_mem_ls; rewrite (equiv_rpo_equiv_1 _ b_eq_a).
apply ls_lt_a; trivial.
rewrite P'; rewrite <- permut_app1.
rewrite <- permut0_cons in P;  try (symmetry; trivial). apply equiv_equiv.
symmetry;trivial.
apply equiv_equiv.
destruct (mem_split_set _ _ equiv_bool_ok _ _ b_mem_lc) as [b' [lc1 [lc2 [b_eq_b' [H _]]]]];
simpl in b_eq_b'; simpl in H.
left; exists b'; exists (ls ++ (lc1 ++ lc2)); repeat split; trivial.
rewrite P'; subst lc.
rewrite ass_app; apply permut0_sym. apply equiv_equiv.
rewrite <- permut0_cons_inside;[|apply equiv_equiv|reflexivity]. 
rewrite ass_app; reflexivity.
apply (@List_mul_step bb a ls (lc1 ++ lc2)); try reflexivity.
rewrite app_comm_cons.
rewrite (@permut0_cons_inside _ _ equiv_equiv _ _ m (a :: lc1) lc2 b_eq_b').
rewrite P.
simpl; subst lc; reflexivity.
auto.
Qed.

Lemma list_permut_map_acc :
 forall bb l l', permut0 equiv l l' ->
 Acc (rpo_mul_step_rest bb) l ->  Acc (rpo_mul_step_rest bb) l'.
Proof.
intros bb l l' P A1; apply Acc_intro; intros l'' M2.
inversion A1 as [H]; apply H; 
inversion M2 as [k' k'' Acc_l' Acc_l'' H']; subst.
inversion H' as [a ls lc k' k'' P'' P' ls_lt_a]; subst.
apply Rpo_mul_step_rest; trivial.
intros s s_in_l; apply Acc_l'; rewrite <- (mem_permut0_mem equiv_equiv s P); trivial.
apply (@List_mul_step bb a ls lc); trivial;
apply permut0_trans with l'; trivial. apply equiv_equiv.
Qed.

(** Multiset extension of rpo on accessible terms lists is well-founded. *)
Lemma wf_rpo_mul_rest : forall bb, well_founded (rpo_mul_rest bb).
Proof.
intro bb; apply wf_incl with (clos_trans _ (rpo_mul_step_rest bb)).
unfold inclusion; apply rpo_mul_rest_trans_clos.
apply wf_clos_trans.
unfold well_founded; intro l; induction l as [ | s l]. 
(* 1/2 l = nil *)
apply Acc_intro; intros m H; inversion H as [l l' Acc_l Acc_l' H']; subst;
inversion H' as [a ls lc l l'  P P']; subst.
assert (L := permut_length P'); discriminate.
(* 1/1 induction step *)
assert (Acc (rpo bb) s -> Acc (rpo_mul_step_rest bb) (s :: l)).
intro Acc_s; generalize l IHl; clear l IHl; 
pattern s; apply Acc_ind with term (rpo bb); trivial; clear s Acc_s.
intros s Acc_s IHs l Acc_l; pattern l; 
apply Acc_ind with (list term) (rpo_mul_step_rest bb); trivial; clear l Acc_l.
intros l Acc_l IHl; apply Acc_intro.
intros l' H; inversion H as [s_k k' Acc_s_l Acc_l' H']; subst.
destruct (@two_cases_rpo bb s l l' H') as [[s' [n' [s_eq_s' [P H'']]]] | [ls [ls_lt_s P]]].
(* 1/3 First case *)
apply (@list_permut_map_acc bb (s :: n')).
rewrite P; rewrite <- permut0_cons; reflexivity || apply equiv_equiv || auto. symmetry;assumption.
apply Acc_intro; intros l'' l''_lt_s'_n; apply Acc_inv with (s :: n').
apply IHl; apply Rpo_mul_step_rest; trivial.
intros; apply Acc_s_l; right; trivial.
intros s'' s''_in_n'; apply Acc_l'; rewrite (mem_permut0_mem equiv_equiv s'' P); right; trivial.
trivial.
(* 1/2 Second case *)
apply (@list_permut_map_acc bb (ls ++ l)).
apply permut0_sym; trivial. apply equiv_equiv.
clear P; induction ls as [ | b ls].
simpl; apply Acc_intro; trivial.
simpl; apply IHs.
apply ls_lt_s; left; reflexivity.
apply IHls; intros; apply ls_lt_s; right; trivial.
apply Acc_intro.
intros l' H'.
apply Acc_inv with (s :: l); trivial.
inversion H' as [k k' Acc_s_l Acc_l']; subst;
apply H; apply Acc_s_l; left; reflexivity.
Qed.

Inductive rpo_rest (bb : nat) : (symbol * list term) -> (symbol * list term) -> Prop :=
 | Top_gt_rest : 
       forall f g l l', prec Prec g f -> 
       (forall s, mem equiv s l -> Acc (rpo bb) s) -> (forall s, mem equiv s l' -> Acc (rpo bb) s) ->
       rpo_rest bb (g, l') (f, l)
  | Top_eq_lex_rest : 
        forall f g l l', status Prec f = Lex -> status Prec g = Lex -> prec_eq Prec f g -> (length l = length l' \/ length l' <= bb /\ length l <= bb) -> rpo_lex bb l' l -> 
        (forall s, mem equiv s l -> Acc (rpo bb) s) -> (forall s, mem equiv s l' -> Acc (rpo bb) s) ->
        rpo_rest bb (f, l') (g, l)
  | Top_eq_mul_rest : 
        forall f g l l', status Prec f = Mul -> status Prec g = Mul -> prec_eq Prec f g -> rpo_mul bb l' l -> 
        (forall s, mem equiv s l -> Acc (rpo bb) s) -> (forall s, mem equiv s l' -> Acc (rpo bb) s) ->
        rpo_rest bb (f, l') (g, l).

Lemma rpo_rest_prec_eq : forall bb f g l, prec_eq Prec f g -> Acc (rpo_rest bb) (f, l) -> Acc (rpo_rest bb) (g, l).
Proof.
intros.
destruct H0.
apply Acc_intro.
intros.
apply H0. clear H0.
destruct y.
inversion H1.
apply Top_gt_rest.
apply prec_eq_prec1 with g. trivial. apply prec_eq_sym. trivial. trivial. trivial.
apply Top_eq_lex_rest; trivial. assert (H13:= prec_eq_status Prec f g). assert (H14: status Prec f = status Prec g). apply H13. trivial. rewrite  H14. trivial. 
apply prec_eq_transitive with g; trivial. 
apply prec_eq_sym; trivial.
apply Top_eq_mul_rest; trivial.
 assert (H13:= prec_eq_status Prec f g). assert (H14: status Prec f = status Prec g). apply H13. trivial. rewrite  H14. trivial. 
apply prec_eq_transitive with g; trivial. 
apply prec_eq_sym; trivial.
Qed.

Lemma wf_rpo_rest : well_founded (prec Prec) -> forall bb, well_founded (rpo_rest bb).
Proof.
intros wf_prec bb; unfold well_founded; intros [f l]; generalize l; clear l; 
pattern f; apply (well_founded_induction_type wf_prec); clear f.
intros f IHf l; assert (Sf : forall f', f' = f -> status Prec f' = status Prec f).
intros; subst; trivial.
destruct (status Prec f); generalize (Sf _ (eq_refl _)); clear Sf; intro Sf.
pattern l; apply (well_founded_induction_type (wf_rpo_lex_rest bb bb)); clear l.
intros l IHl; apply Acc_intro; intros [g l'] H. 
inversion H as [ f' g' k k' g_prec_f Acc_l Acc_l' 
                      | f' g' k k' Sf' Sg' eq_f'_g' L H' Acc_l Acc_l'
                      | f' g' k k' Sf' Sg' eq_f'_g' H' Acc_l Acc_l' ]; subst.
apply IHf; trivial.
apply rpo_rest_prec_eq with f. apply prec_eq_sym; trivial.
apply rpo_rest_prec_eq with f. apply prec_eq_refl.
apply IHl; apply Rpo_lex_rest; trivial.
rewrite Sf in Sg'; discriminate.


pattern l; apply (well_founded_induction_type (wf_rpo_mul_rest bb)); clear l.
intros l IHl; apply Acc_intro; intros [g l'] H; 
inversion H as [ f' g' k k' g_prec_f Acc_l Acc_l' 
                         | f' k k' Sf' L H' Acc_l Acc_l'
                         | f' k k' Sf' H' Acc_l Acc_l' ]; subst.
apply IHf; trivial.
absurd (Lex = Mul); [discriminate | apply trans_eq with (status Prec f); auto].
apply rpo_rest_prec_eq with f. apply prec_eq_sym; trivial.
apply IHl; apply Rpo_mul_rest; trivial.
Qed.

Lemma acc_build :
  well_founded (prec Prec) -> forall bb f_l,
  match f_l with (f, l) => 
  (forall t, mem equiv t l -> Acc (rpo bb) t) ->  Acc (rpo bb) (Term f l)
  end.
Proof.
intros wf_prec bb f_l; pattern f_l;
apply (well_founded_induction_type (wf_rpo_rest wf_prec bb)); clear f_l.
intros [f l] IH Acc_l; apply Acc_intro;
intros s; pattern s; apply term_rec3_mem; clear s.
intros v _; apply Acc_intro.
intros t t_lt_v; inversion t_lt_v.
intros g k IHl gk_lt_fl;
inversion gk_lt_fl as [ f' l' s' t t_in_l H' 
                               | f' g' k' l' g_prec_f 
                               | f' g' k' l' Sf Sg f_eq_g L H' H''
                               | f' g' k' l' Sf Sg f_eq_g H']; subst.
(* 1/4 Subterm case *)
assert (Acc_t := Acc_l _ t_in_l).
subst; inversion H' as [s' t' s_eq_t | s' t' s_lt_t ]; 
subst s' t'; [idtac | apply Acc_inv with t; trivial ].
apply Acc_intro; intro u.
rewrite (@equiv_rpo_equiv_1 _ (Term g k) t); trivial;
intro; apply Acc_inv with t; trivial.
(* 1/3 Top gt *)
assert (Acc_k : forall s, mem equiv s k -> Acc (rpo bb) s).
intros s s_mem_k; apply IHl; trivial.
apply H; trivial.
apply (IH (g,k)); trivial.
apply Top_gt_rest; trivial.
(* 1/2 Top_eq_lex *)
assert (Acc_k : forall s, mem equiv s k -> Acc (rpo bb) s).
intros s s_mem_k; apply IHl; trivial.
apply H''; trivial.
apply (IH (g,k)); trivial.
apply Top_eq_lex_rest; trivial.
(* 1/1 Top_eq_mul *)
assert (Acc_k : forall s, mem equiv s k -> Acc (rpo bb) s).
intros s s_mem_k; apply IHl; trivial.
apply rpo_trans with (Term g k); trivial; apply Subterm with s; trivial; 
apply Equiv; apply Eq.
apply (IH (g,k)); trivial.
apply Top_eq_mul_rest; trivial.
Qed.

(** ** Main theorem: when the precedence is well-founded, so is the rpo. *)
Lemma wf_rpo : well_founded (prec Prec) -> forall bb, well_founded (rpo bb).
Proof.
intros wf_prec bb;
unfold well_founded; intro t; pattern t; apply term_rec3_mem; clear t.
intro v; apply Acc_intro; intros s s_lt_t; inversion s_lt_t.
intros f l Acc_l; apply (acc_build wf_prec bb (f,l)); trivial.
Qed.

(** ** RPO is compatible with the instanciation by a substitution. *)
Lemma equiv_subst :
  forall s t, equiv s t -> 
  forall sigma, equiv (apply_subst sigma s) (apply_subst sigma t).
Proof.
intros s t; generalize s; clear s.
pattern t; apply term_rec3_mem; clear t.
intros v s v_eq_s; inversion v_eq_s; subst; intro sigma; apply Eq.
intros f l IHl s fl_eq_s sigma; 
inversion fl_eq_s as [ s' 
                               | f' g l1 l2 Sf Sg f'_eq_g l1_eq_l2
                               | f' g l1 l2 Sf Sg f'_eq_g P ]; subst.
(* 1/3 Syntactic equality *)
apply Eq.
(* 1/2 Lex top symbol *)
simpl; apply Eq_lex; trivial.
generalize l1 l1_eq_l2; clear fl_eq_s l1 l1_eq_l2; 
induction l as [ | s l]; intros l1 l1_eq_l2;
inversion l1_eq_l2 as [ | s1 s' l1' l' s1_eq_s' l1'_eq_l']; subst.
simpl; apply Eq_list_nil.
simpl; apply Eq_list_cons.
apply IHl; trivial; left; reflexivity.
apply IHl0; trivial.
intros t t_in_l; apply IHl; right; trivial.
(* 1/1 Mul top symbol *)
simpl; apply Eq_mul; trivial.
apply (permut_map (A := term) (B := term) (A' := term) (B' := term) (R := equiv)).
intros a1 a2 a1_in_l1 _ a1_eq_a2; symmetry; apply IHl.
rewrite <- (mem_permut0_mem equiv_equiv a1 P).
apply in_impl_mem; trivial.
intros; apply Eq.
symmetry; trivial.
trivial.
Qed.

Lemma rpo_subst :
  forall bb s t, rpo bb s t -> 
  forall sigma, rpo bb (apply_subst sigma s) (apply_subst sigma t).
Proof.
intro bb.
cut (forall p, match p with 
            (s,t) => rpo bb s t -> 
              forall sigma, rpo bb (apply_subst sigma s) (apply_subst sigma t)
        end).
intros H s t s_lt_t sigma; apply (H (s,t)); trivial.
intro p; pattern p; refine (well_founded_ind wf_size2 _ _ _); clear p.
intros [s t] IH s_lt_t sigma.
inversion s_lt_t as [ f l s' t' t'_mem_l R' 
                       | f g l l' R' R'' 
                       | f g l l' f_lex g_lex f_eq_g L Rlex R' H2 H3
                       | f g l l' f_mul g_mul f_eq_g Rmul R' H2 ]; subst.
(* 1/4 case Subterm *)
simpl; apply Subterm with (apply_subst sigma t').
destruct (mem_split_set _ _ equiv_bool_ok _ _ t'_mem_l) as [t'' [l1 [l2 [t'_eq_t'' [H _]]]]];
simpl in t'_eq_t''; simpl in H; subst l.
rewrite map_app; rewrite <- mem_or_app.
right; left; apply equiv_subst; trivial.
inversion R' as [ s' R'' | s' t'' R'' ]; subst. 
apply Equiv; apply equiv_subst; trivial.
apply Lt; apply (IH (s,t')); trivial.
apply size2_lex2_mem; trivial.
(* 1/3 case Top_gt *)
simpl; apply Top_gt; trivial.
intros s' s'_mem_l'_sigma; 
destruct (mem_split_set _ _ equiv_bool_ok _ _ s'_mem_l'_sigma) as [s'' [l1 [l2 [s'_eq_s'' [H _]]]]];
simpl in s'_eq_s''; simpl in H.
rewrite (equiv_rpo_equiv_2 _ s'_eq_s'').
assert (s''_in_l'_sigma : In s'' (map (apply_subst sigma) l')).
rewrite H; apply in_or_app; right; left; trivial.
rewrite in_map_iff in s''_in_l'_sigma.
destruct s''_in_l'_sigma as [u [s_eq_u_sigma u_in_l']].
subst s''; 
replace (Term f (map (apply_subst sigma) l)) with 
              (apply_subst sigma (Term f l)); trivial.
apply (IH (u, Term f l)).
apply size2_lex1; trivial.
apply rpo_trans with (Term g l'); trivial.
apply Subterm with u.
apply in_impl_mem; trivial.
exact Eq.
apply Equiv; apply Eq.
(* 1/2 case Top_eq_lex *)
simpl; apply Top_eq_lex; trivial.
do 2 rewrite length_map; assumption.
generalize l Rlex IH; clear l s_lt_t Rlex R' IH L;
induction l' as [ | s' l' ]; intros l Rlex IH; 
inversion Rlex as [s'' t' k k' s'_lt_t' L | s'' t' k k' s'_eq_t' k_lt_k' | ]; subst; simpl.
apply List_nil.
apply List_gt.
apply (IH (s',t')); trivial.
apply size2_lex1; left; trivial.
apply List_eq.
apply equiv_subst; trivial.
apply IHl'; trivial.
intros [s t] S s_lt_t tau; apply (IH (s,t)); trivial.
apply o_size2_trans with (Term f l', Term f k'); trivial.
apply size2_lex1_bis.
intros s' s'_mem_l'_sigma; 
destruct (mem_split_set _ _ equiv_bool_ok _ _ s'_mem_l'_sigma) as [s'' [l1 [l2 [s'_eq_s'' [H _]]]]];
simpl in s'_eq_s''; simpl in H.
rewrite (equiv_rpo_equiv_2 _ s'_eq_s'').
assert (s''_in_l'_sigma : In s'' (map (apply_subst sigma) l')).
rewrite H; apply in_or_app; right; left; trivial.
rewrite in_map_iff in s''_in_l'_sigma.
destruct s''_in_l'_sigma as [u [s_eq_u_sigma u_in_l']].
subst s''; 
replace (Term f (map (apply_subst sigma) l)) with 
              (apply_subst sigma (Term f l)); trivial.
apply (IH (u, Term g l)).
apply size2_lex1; trivial.
apply rpo_trans with (Term f l'); trivial.
apply Subterm with u.
apply in_impl_mem; trivial.
exact Eq.
apply Equiv; apply Eq.
(* 1/1 case Top_eq_mul *)
simpl; apply Top_eq_mul; trivial;
inversion Rmul as [ a lg ls lc l0 k0 Pk Pl ls_lt_alg]; subst.
apply (@List_mul bb (apply_subst sigma a) (map (apply_subst sigma) lg)
(map (apply_subst sigma) ls) (map (apply_subst sigma) lc)).
rewrite <- map_app; apply permut_map with equiv; trivial.
intros b b' _ _ b_eq_b'; apply equiv_subst; trivial.
rewrite <- map_app.
refine (@permut_map term term term term equiv 
                    equiv (apply_subst sigma) _ _ (a :: lg ++ lc) _ _); trivial.
intros b b' b_in_l _ b_eq_b'; apply equiv_subst; trivial.
intros b b_mem_ls_sigma; 
destruct (mem_split_set _ _ equiv_bool_ok _ _ b_mem_ls_sigma) as [b' [ls1 [ls2 [b_eq_b' [H _]]]]];
simpl in b_eq_b'; simpl in H.
assert (b'_in_ls_sigma : In b' (map (apply_subst sigma) ls)).
rewrite H; apply in_or_app; right; left; trivial.
rewrite in_map_iff in b'_in_ls_sigma.
destruct b'_in_ls_sigma as [b'' [b''_sigma_eq_b' b''_in_ls]].
destruct (ls_lt_alg b'') as [a' [a'_mem_alg b''_lt_a']].
apply in_impl_mem; trivial.
exact Eq.
destruct (mem_split_set _ _ equiv_bool_ok _ _ a'_mem_alg) as [a'' [alg' [alg'' [a'_eq_a'' [H' _]]]]];
simpl in a'_eq_a''; simpl in H'.
exists (apply_subst sigma a''); split; trivial.
apply in_impl_mem.
exact Eq.
rewrite (in_map_iff (apply_subst sigma) (a :: lg)).
exists a''; split; trivial.
rewrite H'; apply in_or_app; right; left; trivial.
rewrite (equiv_rpo_equiv_2 _ b_eq_b').
subst b'; apply (IH (b'',a'')).
apply size2_lex1_mem.
rewrite Pk; rewrite <- mem_or_app; left;
apply in_impl_mem; trivial. 
exact Eq.
rewrite <- (equiv_rpo_equiv_1 _ a'_eq_a''); trivial.
Qed.

Lemma rpo_eq_subst :
  forall bb s t, rpo_eq bb s t -> 
  forall sigma, rpo_eq bb (apply_subst sigma s) (apply_subst sigma t).
Proof.
intros bb s t H sigma; inversion H as [t1 t2 Heq | t1 t2 Hlt]; subst t1 t2.
apply Equiv; apply equiv_subst; assumption.
apply Lt; apply rpo_subst; assumption.
Qed.

(** ** RPO is compatible with adding context. *)
Lemma equiv_add_context :
 forall p ctx s t, equiv s t -> is_a_pos ctx p = true -> 
  equiv (replace_at_pos ctx s p) (replace_at_pos ctx t p).
Proof.
intro p; induction p as [ | i p ]; intros ctx s t R H; trivial;
destruct ctx as [ v | f l ].
discriminate.
assert (Status : forall g, g = f -> status Prec g = status Prec f).
intros; subst; trivial.
do 2 (rewrite replace_at_pos_unfold);
destruct (status Prec f); generalize (Status f (eq_refl _)); clear Status;
intro Status.
(* 1/2 Lex case *)
apply Eq_lex; trivial.
apply prec_eq_refl.
generalize i H; clear i H; induction l as [ | u l]; intros i H; simpl. 
apply Eq_list_nil.
destruct i as [ | i].
apply Eq_list_cons. 
simpl in H; apply IHp; trivial.
generalize l; intro l'; induction l' as [ | u' l'].
apply Eq_list_nil.
apply Eq_list_cons; trivial; reflexivity.
apply Eq_list_cons.
reflexivity.
apply IHl; trivial.
(* 1/1 Mul case *)
apply Eq_mul; trivial.
apply prec_eq_refl.
generalize i H; clear i H; induction l as [ | u l]; intros i H; simpl; reflexivity || auto.
destruct i as [ | i].
rewrite <- permut0_cons.
reflexivity.
apply equiv_equiv. 
simpl in H; apply IHp; trivial.
rewrite <- permut0_cons.
apply IHl; trivial. apply equiv_equiv.
reflexivity.
Qed.

Lemma rpo_add_context :
 forall bb p ctx s t, rpo bb s t -> is_a_pos ctx p = true -> 
  rpo bb (replace_at_pos ctx s p) (replace_at_pos ctx t p).
Proof.
intros bb p; induction p as [ | i p ]; intros ctx s t R H; trivial;
destruct ctx as [ v | f l ].
discriminate.
assert (Status : forall g, g = f -> status Prec g = status Prec f).
intros; subst; trivial.
do 2 (rewrite replace_at_pos_unfold);
destruct (status Prec f); generalize (Status f (eq_refl _)); clear Status;
intro Status.
(* 1/2 Lex case *)
apply Top_eq_lex; trivial. 
apply prec_eq_refl.
left; clear; revert l; induction i as [ | i]; intros [ | a l]; simpl; trivial.
rewrite IHi; apply eq_refl.
generalize i H; clear i H; induction l as [ | u l]; intros i H; simpl.
simpl in H; destruct i; discriminate.
destruct i as [ | i].
apply List_gt; trivial.
simpl in H; apply IHp; trivial.
apply List_eq.
reflexivity.
apply IHl; trivial.
intros s' s'_mem_ls;
assert (H' : exists s'', rpo_eq bb s' s'' /\ mem equiv s'' (replace_at_pos_list l t i p)). 
generalize i H s' s'_mem_ls; clear i H s' s'_mem_ls; 
induction l as [ | u l]; intros i H; simpl.
intros; contradiction.
destruct i as [ | i].
intros s' [s'_eq_s'' | s'_mem_l].
exists (replace_at_pos u t p); split.
apply Lt; rewrite (equiv_rpo_equiv_2 _ s'_eq_s'').
apply IHp; trivial.
left; reflexivity.
exists s'; split.
apply Equiv; apply Eq.
right; trivial.
intros s' [s'_eq_u | s'_mem_l].
exists u; split.
apply Equiv; trivial.
left; reflexivity.
simpl in IHl; simpl in H.
destruct (IHl i H s' s'_mem_l) as [s'' [s'_le_s'' s''_mem_l']].
exists s''; split; trivial.
right; trivial.
destruct H' as [s'' [s'_le_s'' s''_mem_l']].
apply Subterm with s''; trivial.
(* 1/1 Mul case *)
apply Top_eq_mul; trivial.
apply prec_eq_refl.
generalize i H; clear i H; induction l as [ | u l]; intros i H; simpl.
simpl in H; destruct i; discriminate.
destruct i as [ | i].
apply (@List_mul bb (replace_at_pos u t p) nil (replace_at_pos u s p :: nil) l); reflexivity || auto.
intros b [b_eq_s' | b_mem_nil].
exists (replace_at_pos u t p); split.
left; reflexivity.
rewrite (equiv_rpo_equiv_2 _ b_eq_s').
apply IHp; trivial.
contradiction.
simpl in IHl; simpl in H; assert (H' := IHl i H).
inversion H' as [a lg ls lc l' l'' ls_lt_alg P1 P2]; subst.
apply (@List_mul bb a lg ls (u :: lc)); trivial.
rewrite <- permut0_cons_inside; trivial; try reflexivity. apply equiv_equiv.
rewrite app_comm_cons.
rewrite <- permut0_cons_inside; trivial; try reflexivity. apply equiv_equiv.
Qed.

Lemma rpo_eq_add_context :
 forall bb p ctx s t, rpo_eq bb s t -> is_a_pos ctx p = true -> 
  rpo_eq bb (replace_at_pos ctx s p) (replace_at_pos ctx t p).
Proof.
intros bb p ctx s t H P; inversion H; clear H; subst.
apply Equiv; apply equiv_add_context; assumption.
apply Lt; apply rpo_add_context; assumption.
Qed.

Function remove_equiv (t : term) (l : list term) {struct l} : option (list term) :=
  match l with
     | nil => @None _
     | a :: l => 
         if  equiv_dec t a
         then Some l
         else
            match remove_equiv t l with
            | None => @ None _
            | Some l' => Some (a :: l')
            end
    end.

Function  remove_equiv_list (l1 l2 : list term) {struct l1} : (list term) * (list term) :=
    match l1, l2 with
    | _, nil => (l1,l2)
    | nil, _ => (l1,l2)
    | a1 :: l1, l2 =>
          match remove_equiv a1 l2 with
          | Some l2' =>  remove_equiv_list l1 l2' 
          | None =>
               match remove_equiv_list l1 l2 with
                      | (l1',l2') => (a1 :: l1', l2')
               end
          end
   end.

Lemma remove_equiv_is_sound_some : 
  forall t l l', remove_equiv t l = Some l' -> 
    {t' | equiv t t' /\ permut0 equiv l (t' :: l')}.
Proof.
intros t l; induction l as [ | a l]; intros l' R; simpl in R.
discriminate.
destruct (equiv_dec t a) as [t_eq_a | t_diff_a].
injection R; intro; subst l'; clear R;
exists a; split; reflexivity || auto.
destruct (remove_equiv t l) as [ l'' | ].
injection R; intro; subst l'; clear R.
destruct (IHl l'' (eq_refl _)) as [t' [t_eq_t' P]].
exists t'; split; trivial.
rewrite <- (@permut0_cons_inside _ _ equiv_equiv a a l (t' :: nil) l''); trivial.
reflexivity.
discriminate.
Qed.

Lemma remove_equiv_is_sound_none : 
  forall t l, remove_equiv t l = None -> forall t', mem equiv t' l -> ~ (equiv t t').
Proof.
intros t l; 
functional induction (remove_equiv t l) as 
  [ 
  | H1 a l t' t_eq_a _ 
  | H1 a l t' t_diff_a _ IH H 
  | H1 a l t' t_diff_a _ IH l' H ].
(* 1/4 *) 
simpl; intros; contradiction.
(* 1/3 *)
intros; discriminate.
(* 1/2 *)
intros _; rewrite H in IH; intros t' [a_eq_t' | t'_mem_l].
intro t_eq_t'; apply t_diff_a.
transitivity t'; trivial.
apply IH; trivial.
(* 1/1 *)
intros; discriminate.
Qed.

Lemma remove_equiv_list_is_sound :
  forall l1 l2, 
    match remove_equiv_list l1 l2 with
         | (l1',l2') => 
             {lc | permut0 equiv l1 (l1' ++ lc) /\ permut0 equiv l2 (l2' ++ lc) /\
                           (forall t1 t2, mem equiv t1 l1' -> mem equiv t2 l2' -> ~ equiv t1 t2)}
   end.            
Proof.
intros l1 l2; 
functional induction (remove_equiv_list l1 l2) as
[ l1
| H1 l2 H2 H3 H4 H'
| H1 l2 t1 l1 H2 H3 H4 _ l2' H IH 
| H1 l2 t1 l1 H2 H3 H4 H' H IH l1' l2' R].
(* 1/ 4 *)
exists (@nil term); simpl; repeat split; reflexivity || auto.
rewrite <- app_nil_end; reflexivity || auto.
(* 1/3 *)
destruct l2 as [ | t2 l2].
contradiction.
exists (@nil term); simpl; repeat split; reflexivity || auto.
rewrite <- app_nil_end; reflexivity || auto.
(* 1/2 *)
destruct (@remove_equiv_is_sound_some t1 l2 l2' H) as [t2 [t1_eq_t2 P2]].
destruct (remove_equiv_list l1 l2') as [l1'' l2''].
destruct IH as [lc [P1 [P2' D]]].
exists (t1 :: lc); repeat split; reflexivity || auto.
rewrite <- permut0_cons_inside; trivial. apply equiv_equiv.
reflexivity.
rewrite P2; rewrite <- permut0_cons_inside; trivial. apply equiv_equiv.
symmetry; trivial.
(* 1/1 *)
rewrite R in IH.
destruct IH as [lc [P1 [P2 D]]].
exists lc; repeat split; auto.
simpl; rewrite <- permut0_cons; trivial. apply equiv_equiv.
reflexivity.
intros u1 u2 [t1_eq_u1 | u1_mem_l1'] u2_mem_u2'.
assert (H'' := @remove_equiv_is_sound_none t1 l2 H).
intro u1_eq_u2; apply (H'' u2).
rewrite P2; rewrite <- mem_or_app; left; trivial.
transitivity u1; trivial.
symmetry; trivial.
apply D; trivial.
Qed.
 
Lemma rpo_dec : forall bb t1 t2, {rpo bb t1 t2}+{~rpo bb t1 t2}.
Proof.
intro bb.
cut (forall p, match p with (t2,t1) =>
                              {rpo bb t1 t2}+{~rpo bb t1 t2}
                 end).
intros H t1 t2; apply (H (t2,t1)).
intro p; pattern p; refine (well_founded_induction wf_size2 _ _ _); clear p.
intros [[v | f l] t1] IH.
(* 1/2 t2 is a variable *)
right; intro t1_lt_t2; inversion t1_lt_t2.
(* 1/1 t2 is a compound term *)
(* Try the Subterm case *)
assert (H : {t | mem equiv t l /\ rpo_eq bb t1 t}+{~exists t, mem equiv t l /\ rpo_eq bb t1 t}).
induction l as [ | s l].
right; intros [t [t_mem_nil _]]; contradiction.
destruct (equiv_dec t1 s) as [t1_eq_s | t1_diff_s].
left; exists s; split.
left; reflexivity.
apply Equiv; trivial.
destruct (IH (s,t1)) as [t1_lt_s | not_t1_lt_s].
apply size2_lex1; left; trivial.
left; exists s; split.
left; reflexivity.
apply Lt; trivial.
destruct IHl as [Ok | Ko].
intros [t2 t1'] H; apply (IH (t2,t1')).
apply o_size2_trans with (Term f l, t1); trivial.
apply size2_lex1_bis.
destruct Ok as [t [t_mem_l t1_le_t]].
left; exists t; split; trivial.
right; trivial.
right; intros [t [[s_eq_t | t_mem_l] t1_le_t]].
destruct t1_le_t.
apply t1_diff_s; transitivity t'; trivial; symmetry; trivial.
apply not_t1_lt_s; rewrite <- (equiv_rpo_equiv_1 _ s_eq_t); trivial.
apply Ko; exists t; split; trivial.
destruct H as [[t [t_mem_l t1_le_t]] | H].
left; apply Subterm with t; trivial.
(* Subterm has failed, trying Top_eq_lex or Top_eq_mul *)
revert IH H. destruct t1 as [v | g k]; intros IH H.
(* 1/2 t1 is a variable, t2 is a compound term *)
right; intro v_lt_fl; inversion v_lt_fl; subst.
apply H; exists s; split; trivial.
(* 1/1 t1 and t2 are compound terms *)
 case_eq (prec_eq_bool Prec g f); [intro g_eq_f | intro g_diff_f].
(* 1/2 g = f *)
assert (f_eq_g: prec_eq Prec f g).
assert (H1:= prec_eq_bool_ok). assert (H1':= H1 symbol Prec g f). rewrite g_eq_f in H1'. apply prec_eq_sym; trivial.
assert (Sf_eq_Sg: status Prec g = status Prec f). apply prec_eq_status; apply prec_eq_sym; trivial.
case_eq (status Prec f); intro Sf.
(* 1/3 Trying Top_eq_lex, status f = Lex *)
assert (H' : {rpo_lex bb k l}+{~rpo_lex bb k l}).
generalize k IH; clear k IH H; induction l as [ | t l]; intros k IH.
right; intro k_lt_nil; inversion k_lt_nil.
revert IH; destruct k as [ | s k]; intro IH.
left; apply List_nil.
destruct (IH (t,s)) as [s_lt_t | not_s_lt_t].
apply size2_lex1; left; trivial.
left; apply List_gt; trivial.
destruct (equiv_dec s t) as [s_eq_t | s_diff_t].
destruct (IHl k) as [k_lt_l | not_k_lt_l].
intros [t2 t1] H; apply (IH (t2,t1)).
apply o_size2_trans with (Term f l, Term g k); trivial.
apply size2_lex1_bis.
left; apply List_eq; trivial.
right; intro sk_lt_tl; inversion sk_lt_tl; subst.
absurd (rpo bb s t); trivial.
absurd (rpo_lex bb k l); trivial.
right; intro sk_lt_tl; inversion sk_lt_tl; subst.
absurd (rpo bb s t); trivial.
absurd (equiv s t); trivial.
destruct H' as [k_lt_l | not_k_lt_l].
let P := constr:(forall (s:term), mem equiv s k -> rpo bb s (Term f l)) in
assert (H'' : { P }+{~P}).
clear k_lt_l H; revert IH; induction k as [ | s k IHk]; intro IH.
left; intros s s_mem_nil; contradiction.
destruct (IH (Term f l, s)) as [s_lt_fl | not_s_lt_fl].
apply size2_lex2; left; trivial.
destruct IHk as [Ok | Ko].
intros [t2 t1] H'; apply (IH (t2,t1)).
apply o_size2_trans with (Term f l, Term f k); trivial.
apply size2_lex2_bis_prec_eq with Prec; trivial.
left; intros s' [s_eq_s' | s'_mem_k].
rewrite (equiv_rpo_equiv_2 _ s_eq_s'); trivial.
apply Ok; trivial.
right; intro H; apply Ko.
intros s' s'_mem_k; apply H; right; trivial.
right; intro H; apply not_s_lt_fl; apply H; left; reflexivity.
destruct H'' as [Ok | Ko].
destruct (eq_nat_dec (length l) (length k)).
left; apply Top_eq_lex; trivial. rewrite Sf_eq_Sg; trivial. apply prec_eq_sym; trivial. left; trivial.
destruct (le_lt_dec (length k) bb).
destruct (le_lt_dec (length l) bb).
left; apply Top_eq_lex; trivial. rewrite Sf_eq_Sg; trivial. apply prec_eq_sym; trivial. right; split;  assumption.
right; intro fk_lt_fl; inversion fk_lt_fl; subst.
apply H; exists s; split; assumption.
apply prec_not_prec_eq with symbol Prec g f; trivial. apply prec_eq_sym; trivial.
destruct H7 as [H7 | [H7 H7']].
apply n; assumption.
apply lt_irrefl with bb.
apply lt_le_trans with (length l); assumption.
rewrite H5 in Sf; discriminate.
right; intro fk_lt_fl; inversion fk_lt_fl; subst.
apply H; exists s; split; assumption.
apply (prec_antisym Prec f); trivial.
assert (H6: False).
apply prec_not_prec_eq with symbol Prec g f; trivial. apply prec_eq_sym; trivial. contradict H6.
destruct H7 as [H7 | [H7 H7']].
apply n; assumption.
apply lt_irrefl with bb.
apply lt_le_trans with (length k); assumption.
rewrite H5 in Sf; discriminate.
right;  intro fk_lt_fl; inversion fk_lt_fl; subst.
apply Ko; intros s' s'_mem_k; apply rpo_trans with (Term g k); trivial.
apply Subterm with s'; trivial.
apply Equiv; reflexivity.
apply (prec_antisym Prec f); trivial.
contradict Ko; trivial.
contradict Ko; trivial.
rewrite H5 in Sf; discriminate.
right ; intro fk_lt_fl; inversion fk_lt_fl; subst.
apply H; exists s; split; trivial.
apply (prec_antisym Prec f); trivial.
assert (H6: False). apply prec_not_prec_eq with symbol Prec g f; trivial. apply prec_eq_sym; trivial. contradict H6.
apply not_k_lt_l; trivial.
rewrite H5 in Sf; discriminate.
(* 1/2 Trying Top_eq_mul, status f = Mul *)
assert (H' := remove_equiv_list_is_sound k l).
revert IH H H'; destruct (remove_equiv_list k l) as [k' l'];
intros IH H H'; destruct H' as [lc [Pk [Pl D]]].
assert (Rem : rpo_mul bb k l -> rpo_mul bb k' l').
generalize l k l' k' Pk Pl; clear l k l' k' Pk Pl D IH H.
induction lc as [ | c lc]; intros l k l' k' Pk Pl k_lt_l.
inversion k_lt_l as [a lg ls lc' k'' l'' Rk Rl ls_lt_alg]; subst.
apply (@List_mul bb a lg ls lc'); trivial.
transitivity k; trivial; symmetry; rewrite <- app_nil_end in Pk; trivial.
transitivity l; trivial; symmetry; rewrite <- app_nil_end in Pl; trivial.
assert (H := IHlc l k (l' ++ c :: nil) (k' ++ c :: nil)).
do 2 rewrite <- ass_app in H; simpl in H.
generalize (H Pk Pl k_lt_l); clear H; intro H.
apply (@rpo_mul_remove_equiv_aux bb k' l' c c).
intros t _; apply rpo_antirefl.
reflexivity.
inversion H as [a lg ls lc' k'' l'' Rk Rl ls_lt_alg]; subst.
apply (@List_mul bb a lg ls lc'); trivial.
rewrite <- Rk; rewrite <- permut0_cons_inside;[|apply equiv_equiv|reflexivity].
rewrite <- app_nil_end; reflexivity || auto.
rewrite <- Rl; rewrite <- permut0_cons_inside;[|apply equiv_equiv|reflexivity].
rewrite <- app_nil_end; reflexivity || auto.
let P := constr:(forall u, mem equiv u k' -> exists v,  mem equiv v l' /\ rpo bb u v) in
assert (H' : {P} + {~ P}).
assert (IH' : forall u v, mem equiv u k' -> mem equiv v l' -> {rpo bb u v}+{~rpo bb u v}).
intros u v u_mem_k' v_mem_l'; apply (IH (v,u)).
apply size2_lex1_mem.
rewrite Pl; rewrite <- mem_or_app; left; trivial.
generalize l' IH'; clear l k IH H l' lc Pk Pl D IH' Rem.
induction k' as [ | u' k']; intros l' IH'.
left; intros; contradiction.
let P:=constr:(forall v, mem equiv v l' -> ~rpo bb u' v) in
assert (H : {v | mem equiv v l' /\ rpo bb u' v}+{P}).
assert (IH'' : forall v, mem equiv v l' -> {rpo bb u' v}+{~rpo bb u' v}).
intros v v_mem_l'; apply (IH' u' v); trivial.
left; reflexivity.
clear IHk' IH'; induction l' as [ | v' l'].
right; intros; contradiction.
destruct IHl' as [Ok | Ko].
intros; apply IH''; right; trivial.
destruct Ok as [v [v_mem_l' u'_lt_v]]; left; exists v; split; trivial.
right; trivial.
destruct (IH'' v') as [Ok' | Ko'].
left; reflexivity.
left; exists v'; split; trivial.
left; reflexivity.
right; intros v [v'_eq_v | v_mem_l'].
intros u'_lt_v; apply Ko'.
rewrite <- (equiv_rpo_equiv_1 _ v'_eq_v); trivial.
apply Ko; trivial.
destruct H as [[v [v_mem_l' u'_lt_v]] | Ko].
destruct (IHk' l') as [Ok' | Ko'].
intros u v' u_mem_k' v'_mem_l'; apply IH'; trivial; right; trivial.
left; intros u [u'_eq_u | u_mem_k'].
exists v; split; trivial.
rewrite (equiv_rpo_equiv_2 _ u'_eq_u); trivial.
apply Ok'; trivial.
right; intro H; apply Ko'.
intros u u_mem_k'; apply H; right; trivial.
right; intro H.
destruct (H u') as [v [v_mem_l' u'_lt_v]].
left; reflexivity.
apply (Ko v); trivial.
destruct l' as [ | v' l'].
right; intro fk_lt_fl.
inversion fk_lt_fl as [f' l' t'' t' t'_mem_l fk_le_t'
                            | f' f'' k'' l'' f_prec_f k''_lt_fl
                            | f' g' k'' l'' Sf' Sg' f'_eq_g' L k''_lt_l'' l'_lt_t
                            | f' g' k'' l'' Sf' Sg' f'_eq_g' k_lt_l ]; subst.
apply H; exists t'; split; trivial.
assert (H5:False). apply prec_not_prec_eq with symbol Prec g f; trivial. apply prec_eq_sym; trivial. contradict H5.
rewrite Sf in Sg'; discriminate.
assert (k'_lt_nil := Rem k_lt_l).
inversion k'_lt_nil as [a lg ls lc' k'' l'' Rk Rl ls_lt_alg]; subst.
assert (L := permut_length Rl); discriminate.
destruct H' as [Ok | Ko].
left; apply Top_eq_mul; trivial. rewrite Sf_eq_Sg; trivial. apply prec_eq_sym; trivial.
apply (@List_mul bb v' l' k' lc); trivial.
right; intro fk_lt_fl.
inversion fk_lt_fl as [f' l'' t'' t' t'_mem_l fk_le_t'
                            | f' f'' k'' l'' f_prec_f k''_lt_fl
                            | f' f'' k'' l'' Sf' Sf'' f'_eq_f'' L k''_lt_l'' l'_lt_t
                            | f' f'' k'' l'' Sf' Sf'' f'_eq_f'' k_lt_l ]; subst.
rewrite Pl in t'_mem_l; rewrite <- mem_or_app in t'_mem_l.
destruct t'_mem_l as [t'_mem_vl' | t'_mem_lc].
apply Ko; intros u u_mem_k'; exists t'; split; trivial.
inversion fk_le_t'; subst.
rewrite <- (@equiv_rpo_equiv_1 _ (Term g k) t'); trivial.
apply Subterm with u.
rewrite Pk; rewrite <- mem_or_app; left; trivial.
apply Equiv; apply Eq.
apply rpo_trans with (Term g k); trivial.
apply Subterm with u.
rewrite Pk; rewrite <- mem_or_app; left; trivial.
apply Equiv; apply Eq.
apply (@rpo_antirefl bb (Term g k)).
inversion fk_le_t'; subst.
rewrite (@equiv_rpo_equiv_2 _ (Term g k) t'); trivial.
apply Subterm with t'.
rewrite Pk; rewrite <- mem_or_app; right; trivial.
apply Equiv; apply Eq.
apply rpo_trans with t'; trivial.
apply Subterm with t'.
rewrite Pk; rewrite <- mem_or_app; right; trivial.
apply Equiv; apply Eq.
assert (H5:False). apply prec_not_prec_eq with symbol Prec g f; trivial. apply prec_eq_sym; trivial. contradict H5.
rewrite Sf in Sf''; discriminate.
assert (k'_lt_vl' := Rem k_lt_l).
apply Ko.
inversion k'_lt_vl' as [a lg ls lc' k'' l'' Rk Rl ls_lt_alg]; subst.
intro u; rewrite Rk; rewrite <- mem_or_app.
intros [u_mem_ls | u_mem_lc'].
destruct (ls_lt_alg _ u_mem_ls) as [a' [a'_mem_alg u_lt_a']];
exists a'; split; trivial.
rewrite Rl; rewrite app_comm_cons;
rewrite <- mem_or_app; left; trivial.
assert False.
apply (D u u).
rewrite Rk; rewrite <- mem_or_app; right; trivial.
rewrite Rl; rewrite app_comm_cons;
rewrite <- mem_or_app; right; trivial.
reflexivity.
contradiction.
(* 1/1 f <> g, trying last possible case Top_gt *)
generalize (prec_bool_ok Prec g f); case (prec_bool Prec g f); [intro g_prec_f | intro not_g_prec_f].
let P:=constr:(forall t, mem equiv t k -> rpo bb t (Term f l)) in
assert (H' : {P}+{~P}).
clear H; revert IH; induction k as [ | s k]; intro IH.
left; intros; contradiction.
destruct (IH (Term f l,s)) as [s_lt_fl | not_s_lt_fl].
apply size2_lex2; left; trivial.
destruct IHk as [Ok | Ko].
intros [t2 t1] St; apply (IH (t2,t1)).
apply o_size2_trans with (Term f l, Term g k); trivial.
apply size2_lex2_bis.
left; intros t [t_eq_s | t_mem_k].
rewrite (equiv_rpo_equiv_2 _ t_eq_s); trivial.
apply Ok; trivial.
right; intro sk_lt_fl; apply Ko; intros; apply sk_lt_fl; right; trivial.
right; intro sk_lt_fl; apply not_s_lt_fl; intros; apply sk_lt_fl; left;
reflexivity.
destruct H' as [Ok | Ko].
left; apply Top_gt; trivial.
right; intro gk_lt_fl;
inversion gk_lt_fl as [f' l'' t'' t' t'_mem_l fk_le_t'
                            | f' f'' k'' l'' f_prec_f k''_lt_fl
                            | f' f'' k'' l'' Sf' Sf'' f'_eq_f'' L k''_lt_l'' l'_lt_t
                            | f' f'' k'' l'' Sf' Sf'' f'_eq_f'' k_lt_l ]; subst.
apply H; exists t'; split; trivial.
apply Ko; trivial.
apply (prec_antisym Prec f); trivial. apply prec_eq_prec2 with g; trivial.
apply (prec_antisym Prec f); trivial.
apply prec_eq_prec2 with g; trivial.
right; intro gk_lt_fl;
inversion gk_lt_fl as [f' l'' t'' t' t'_mem_l fk_le_t'
                            | f' f'' k'' l'' f_prec_f k''_lt_fl
                            | f' f'' k'' l'' Sf' Sf'' f'_eq_f'' L k''_lt_l'' l'_lt_t
                            | f' f'' k'' l'' Sf' Sf'' f'_eq_f'' k_lt_l ]; subst.
apply H; exists t'; split; trivial.
absurd (prec Prec g f); trivial.
assert (H5:=prec_eq_bool_ok). assert (H5':= H5 symbol Prec g f). rewrite g_diff_f in H5'. contradict H5'; trivial.
assert (H5:=prec_eq_bool_ok). assert (H5':= H5 symbol Prec g f). rewrite g_diff_f in H5'. contradict H5'; trivial.
Defined.

Lemma trans_clos_subterm_rpo:
  forall bb s t,  (trans_clos direct_subterm) s t -> rpo bb s t.
Proof.
intros bb s t H; induction H as [ s [ v | f l ] H | s t u H1 H2].
inversion H.
apply (@Subterm bb f l s s); trivial.
simpl in H; apply in_impl_mem; trivial.
exact Eq.
apply Equiv; apply Eq.
apply (@rpo_subterm bb u t); trivial.
Qed.

Definition prec_eval f1 f2 :=
  if (prec_eq_bool Prec f1 f2) 
  then Equivalent
  else 
     if prec_bool Prec f1 f2 then Less_than
     else 
        if prec_bool Prec f2 f1 then Greater_than
        else Uncomparable.

Lemma prec_eval_is_sound :  
  forall f1 f2, 
  match prec_eval f1 f2 with
  | Equivalent => prec_eq Prec f1  f2
  | Less_than => prec Prec f1 f2
  | Greater_than => prec Prec f2 f1 
  | Uncomparable => ~ prec_eq Prec f1 f2 /\ ~prec Prec f1 f2 /\ ~prec Prec f2 f1
  end.
Proof.
intros f1 f2; unfold prec_eval.
case_eq (prec_eq_bool Prec f1 f2). intros.
assert (H1:= prec_eq_bool_ok). assert (H1':= H1 symbol Prec f1 f2).
rewrite H in H1'. trivial.
intro.
case_eq (prec_bool Prec f1 f2).
intros.
assert (H1:= prec_bool_ok). assert (H1':= H1 symbol Prec f1 f2).
rewrite H0 in H1'. trivial.
intros.
case_eq (prec_bool Prec f2 f1).
intro prec'.
assert (H1:= prec_bool_ok). assert (H1':= H1 symbol Prec f2 f1).
rewrite prec' in H1'. trivial.
intros.
split.
assert (H3:= prec_eq_bool_ok). assert (H3':= H3 symbol Prec f1 f2).
rewrite H in H3'. trivial.
split. 
assert (H3:= prec_bool_ok). assert (H3':= H3 symbol Prec f1 f2).
rewrite H0 in H3'. trivial.
assert (H3:= prec_bool_ok). assert (H3':= H3 symbol Prec f2 f1).
rewrite H1 in H3'. trivial.
Qed.

Inductive result (A : Type) : Type := 
  | Not_found : result A
  | Not_finished : result A
  | Found : A -> result A.

Arguments Not_found {A}.
Arguments Not_finished {A}.

Record rpo_inf : Type := 
  { bb : nat;
    rpo_l : list (term*term);
    rpo_eq_l : list (term*term);
    equiv_l : list (term*term);
    rpo_l_valid : forall t t', In (t,t') rpo_l -> rpo bb t t';
    rpo_eq_valid : forall t t', In (t,t') rpo_eq_l -> rpo_eq bb t t';
    equiv_l_valid : forall t t', In (t,t') equiv_l -> equiv t t'
  }.

Function remove_equiv_eval (p : term -> term -> option bool) 
    (t : term) (l : list term) {struct l} : result (list term) :=
     match l with
     | nil => Not_found
     | a :: l => 
            match p t a with
            | Some true => (Found l)
            | Some false =>
               match remove_equiv_eval p t l  with
               | Found l' => Found (a :: l')
               | Not_found => Not_found
               | Not_finished => Not_finished
               end
             | None => Not_finished
             end 
            end.

Function  remove_equiv_eval_list (p : term -> term -> option bool) (l1 l2 : list term) 
  {struct l1} : option ((list term) * (list term)):=
    match l1, l2 with
    | _, nil => Some (l1,l2)
    | nil, _ => Some (l1,l2)
    | a1 :: l1, l2 =>
          match remove_equiv_eval p a1 l2 with
          | Found l2' =>  remove_equiv_eval_list p l1 l2' 
          | Not_found =>
                      match remove_equiv_eval_list p l1 l2 with
                      | Some (l1',l2') => Some (a1 :: l1', l2')
                      | None => None
                      end
          | Not_finished => None
          end
     end.

Function equiv_eval_list (p : term -> term -> option bool) (l1 l2 : list term) 
{struct l1} : option bool := 
     match l1, l2 with
    | nil, nil => Some true
    | (a :: l), (b :: l') => 
              match p a b with
              | Some true => equiv_eval_list p l l'
              | Some false => Some false
              | None => None
              end
         | _, _ => Some false
    end.

Definition eq_tt_bool t12 t12' := 
match t12, t12' with 
(t1,t2), (t1',t2') => andb (eq_bool t1 t1') (eq_bool t2 t2')
end.

Lemma eq_tt_bool_ok : forall t12 t12', match eq_tt_bool t12 t12' with true => t12 = t12' | false => t12 <> t12' end.
Proof.
unfold eq_tt_bool; intros [t1 t2] [t1' t2']; generalize (eq_bool_ok t1 t1'); case (eq_bool t1 t1').
intro t1_eq_t1'; generalize (eq_bool_ok t2 t2'); case (eq_bool t2 t2').
intro t2_eq_t2'; simpl; subst; reflexivity.
intro t2_diff_t2'; simpl; intro H; apply t2_diff_t2'; injection H; intros; assumption.
intro t1_diff_t1'; simpl; intro H; apply t1_diff_t1'; injection H; intros; assumption.
Defined.

Fixpoint equiv_eval rpo_infos (n : nat) (t1 t2 : term) {struct n} : option bool := 
   match n with
   | 0 => None
   | S m =>
     match t1, t2 with
     | Var v1, Var v2 => Some (X.eq_bool v1 v2)
     | Term f1 l1, Term f2 l2 =>
       if mem_bool eq_tt_bool  (t1, t2) rpo_infos.(equiv_l)
         then  Some true 
         else
           if prec_eq_bool Prec f1 f2 
             then 
               match status Prec f1 with
                 | Lex =>  equiv_eval_list (equiv_eval rpo_infos m) l1 l2
                 | Mul => 
                   match remove_equiv_eval_list (equiv_eval rpo_infos m) l1 l2 with
                     | Some (nil,nil) => Some true
                     | Some _ => Some false
                     | None => None
                   end
               end
             else Some false
       | _, _ => Some false
     end
   end.

Lemma equiv_eval_equation :
  forall rpo_infos n t1 t2, equiv_eval rpo_infos n t1 t2 =
   match n with
   | 0 => None
   | S m =>
     match t1, t2 with
     | Var v1, Var v2 => Some (X.eq_bool v1 v2)
     | Term f1 l1, Term f2 l2 =>
       if mem_bool eq_tt_bool (t1,t2) rpo_infos.(equiv_l)
         then  Some true 
         else
           if prec_eq_bool Prec f1 f2 
             then 
               match status Prec f1 with
                 | Lex =>  equiv_eval_list (equiv_eval rpo_infos m) l1 l2
                 | Mul => 
                   match remove_equiv_eval_list (equiv_eval rpo_infos m) l1 l2 with
                     | Some (nil,nil) => Some true
                     | Some _ => Some false
                     | None => None
                   end
               end
             else Some false
       | _, _ => Some false
     end
   end.
Proof.
intros rpo_infos [ | n] [v1 | f1 l1] [v2 | f2 l2];
unfold equiv_eval; simpl; trivial.
Qed.

Lemma equiv_eval_list_is_sound :
  forall p l1 l2, match equiv_eval_list p l1 l2 with
      | Some true => length l1 = length l2 /\ 
                              (forall t1 t2, In (t1,t2) (combine l1 l2) -> p t1 t2 = Some true)
      | Some false => length l1 <> length l2 \/
                               (exists t1, exists t2, 
                                 In (t1,t2) (combine l1 l2) /\ p t1 t2 = Some false)
      | None => exists t1, exists t2, In (t1,t2) (combine l1 l2) /\
                            p t1 t2 = None
      end.
Proof.
intros p l1; induction l1 as [ | t1 l1]; intros [ | t2 l2]; simpl.
split; trivial; intros; contradiction.
left; discriminate.
left; discriminate.
assert (H : forall u2, u2 = t2 -> p t1 u2 = p t1 t2).
intros; subst; trivial.
destruct (p t1 t2) as [ [ | ] | ]; generalize (H _ (eq_refl _)); clear H; intro H.
generalize (IHl1 l2); destruct (equiv_eval_list p l1 l2) as [ [ | ] | ].
intros [L H']; repeat split.
rewrite L; trivial.
intros t3 t4 [t3t4_eq_t1t2 | t3t4_in_ll].
injection t3t4_eq_t1t2; intros; subst; trivial.
apply H'; trivial.
intros [L | [t3 [t4 [H' H'']]]].
left; intros H''; apply L; injection H''; intros; trivial.
right; exists t3; exists t4; split; trivial; right; trivial.
intros [t3 [t4 [H' H'']]]; exists t3; exists t4; split; trivial; right; trivial.
right; exists t1; exists t2; split; trivial; left; trivial.
exists t1; exists t2; split; trivial; left; trivial.
Qed.

Lemma remove_equiv_eval_is_sound : 
  forall p t l, 
      match remove_equiv_eval p t l with
      | Found l' => 
                exists t', p t t' = Some true /\ 
                   list_permut.permut0 (@eq term) l (t' :: l')
      | Not_found => forall t', In t' l -> p t t' = Some false
      | Not_finished => exists t', In t' l /\ p t t' = None
      end.
intros p t l; 
functional induction (remove_equiv_eval p t l) as 
  [ 
  | H1 a l t' H 
  | H1 a l t' H IH l' H' 
  | H1 a l t' H IH H' 
  | H1 a l t' H IH H' 
  | H1 a l t' H].
simpl; intros; contradiction.
exists a; split; auto.
apply list_permut.permut_refl; intro; trivial.
rewrite H' in IH; destruct IH as [t' [H'' P]]; exists t'; split; trivial.
apply (Pcons (R := @eq term) a a (l := l) (t' :: nil) l'); trivial.
rewrite H' in IH; intros t' [a_eq_t' | t'_in_l]; [subst | apply IH]; trivial.
rewrite H' in IH; destruct IH as [t' [t'_in_l ptt'_eq_none]]; 
exists t'; split; trivial; right; trivial.
exists a; split; trivial; left; trivial.
Qed.

Lemma remove_equiv_eval_list_is_sound :
  forall p l1 l2, 
    match remove_equiv_eval_list p l1 l2 with
         | Some (l1',l2') => 
              exists ll, (forall t1 t2, In (t1,t2) ll -> p t1 t2 = Some true) /\
                list_permut.permut0 (@eq term) l1 (l1' ++ (map (fun st => fst st) ll)) /\
                list_permut.permut0 (@eq term) l2 (l2' ++ (map (fun st => snd st) ll)) /\
                (forall t1 t2, In t1 l1' -> In t2 l2' -> p t1 t2 = Some false)
         | None => exists t1, exists t2, In t1 l1 /\ In t2 l2 /\ p t1 t2 = None
    end.
Proof.
intros p l1 l2; 
functional induction (remove_equiv_eval_list p l1 l2) as
[ l1
| H1 l2 H2 H3 H4 H'
| H1 l2 t1 l1 H2 H3 H4 H' l2' H IH 
| H1 l2 t1 l1 H2 H3 H4 H' H IH l1' l2' R
| H1 l2 t1 l1 H2 H3 H4 H' H IH R
| H1 l2 t1 l1 H2 H3 H4 H' H].
(* 1/ 6 *)
exists (@nil (term * term)); simpl; intuition; intros.
rewrite <- app_nil_end; apply list_permut.permut_refl; intro; trivial.
(* 1/5 *)
destruct l2 as [ | t2 l2].
contradiction.
exists (@nil (term * term)); simpl; intuition; intros.
rewrite <- app_nil_end; apply list_permut.permut_refl; intro; trivial.
(* 1/4 *)
assert (K := remove_equiv_eval_is_sound p t1 l2); rewrite H in K.
destruct K as [t2' [pt1t2_eq_true P]].
destruct (remove_equiv_eval_list p l1 l2') as [ [l1'' l2''] | ].
destruct IH as [ll [E_ll [P1 [P2 F]]]]; exists ((t1,t2') :: ll); repeat split; trivial.
intros u1 u2 [u1u2_eq_t1t2' | u1u2_in_ll].
injection u1u2_eq_t1t2'; intros; subst; apply pt1t2_eq_true.
apply E_ll; trivial.
simpl; apply Pcons; trivial.
apply list_permut.permut_trans with (t2' :: l2').
intros a b c _ a_eq_b b_eq_c; transitivity b; trivial. trivial.
simpl. apply Pcons. trivial.
trivial. 
destruct IH as [t1' [t2 [t1_in_l1 [t2_in_l2 p1p2_eq_none]]]];
exists t1'; exists t2; repeat split; trivial.
right; trivial.
destruct (list_permut.permut_inv_right P) as [t2'' [k2 [k2' [t2''_eq_t2' [H'' P']]]]].
subst l2; apply in_insert.
generalize (k2 ++ k2') l2' t2_in_l2 P'; intro k; induction k as [ | u k];
intros l t2_in_l Q; inversion Q as [ | a b k' l1' l2]; subst; trivial.
destruct (in_app_or _ _ _ t2_in_l) as [t2_in_l1' | [t2_eq_b | t2_in_l2']].
right; apply (IHk (l1' ++ l2)); trivial; apply in_or_app; left; trivial.
left; subst; trivial.
right; apply (IHk (l1' ++ l2)); trivial; apply in_or_app; right; trivial.
(* 1/3 *)
assert (K := remove_equiv_eval_is_sound p t1 l2); rewrite H in K.
rewrite R in IH; destruct IH as [ll [E_ll [P1 [P2 F]]]]; 
exists ll; repeat split; auto.
simpl. apply (Pcons (R := @eq term) t1 t1 (l := l1) nil
                       (l1' ++ map (fun st : term * term => fst st) ll)); trivial.
simpl; intros u1 u2 [u1_eq_t1 | u1_in_l1'] u2_in_l2'.
subst u1; apply K; rewrite (in_permut_in P2);
apply in_or_app; left; trivial.
apply F; trivial.
(* 1/2 *)
rewrite R in IH; destruct IH as [u1 [u2 [u1_in_l1 [u2_in_l2 pu1u2_eq_none]]]];
exists u1; exists u2; repeat split; trivial; right; trivial.
(* 1/1 *)
assert (K := remove_equiv_eval_is_sound p t1 l2); rewrite H in K.
destruct K as [t2 [t2_in_l2 pt1t2_eq_none]];
exists t1; exists t2; repeat split; trivial; left; trivial.
Qed.

Lemma find_is_sound : 
  forall (I: term -> term -> Prop) l (l_sound: forall t t', In (t,t') l -> I t t') t1 t2,  
    mem_bool eq_tt_bool (t1,t2) l = true -> 
    I t1 t2.
Proof.
  intros I l l_sound t1 t2 H; apply l_sound.
  apply (mem_impl_in (@eq (term*term))).
  intros; assumption.
  generalize (mem_bool_ok _ _ eq_tt_bool_ok (t1,t2) l); rewrite H; intros; assumption.
Qed.    

Lemma equiv_eval_is_sound_weak :
  forall rpo_infos n t1 t2, equiv_eval rpo_infos n t1 t2 = Some true -> equiv t1 t2.
intros rpo_infos n; induction n as [ | n].
(* n = 0 *)
intros; discriminate.
(* n = S n *)
destruct t1 as [v1 | f1 l1]; destruct t2 as [v2 | f2 l2]; simpl.
(* t1 = Var v1 ; t2 = v2 *)
generalize (X.eq_bool_ok v1 v2); case (X.eq_bool v1 v2); [intro v1_eq_v2 | intro v1_diff_v2].
(* v1 = v2 *)
subst; intuition; apply Eq.
(* v1 <> v2 *)
intro; discriminate.
(*t1 = Var v1 ; t2 = f2 l2*)
intro; discriminate.
(*t1 = f1 l1 ; t2 = v2 *)
intro; discriminate.
(*t1 = f1 l1 ; t2 = f2 l2 *)
case_eq (mem_bool eq_tt_bool ((Term f1 l1), (Term f2 l2)) (equiv_l rpo_infos));simpl.
(* (t1,t2) in (equiv_l rpo_infos) *)
intros H _ ;eapply find_is_sound with (1:=equiv_l_valid rpo_infos);auto.
intros _.
case_eq (prec_eq_bool Prec f1 f2); [intro f1_eq_f2 | intro f1_diff_f2].
case_eq (status Prec f1). intros Status.
intro H; apply Eq_lex; trivial.
assert (H1:= prec_eq_status). assert (H1':= H1 symbol Prec f1 f2).
assert (status Prec f1 = status Prec f2). apply H1'; trivial. trivial.
assert (H3:= prec_eq_bool_ok). assert (H3':= H3 symbol Prec f1 f2).
rewrite f1_eq_f2 in H3'. trivial. rewrite <- H0. trivial.
assert (H3:= prec_eq_bool_ok). assert (H3':= H3 symbol Prec f1 f2).
rewrite f1_eq_f2 in H3'. trivial.
generalize l1 l2 H; clear l1 l2 H;
intro l; induction l as [ | t l]; intros [ | t' l'] H.
apply Eq_list_nil.
discriminate.
discriminate.
simpl in H; apply Eq_list_cons.
apply IHn; destruct (equiv_eval rpo_infos n t t') as [ [ | ] | ]; 
trivial; discriminate.
apply IHl; destruct (equiv_eval rpo_infos n t t') as [ [ | ] | ]; 
trivial; discriminate. intro Status.

intro H; assert (H' := remove_equiv_eval_list_is_sound (equiv_eval rpo_infos n) l1 l2);
destruct (remove_equiv_eval_list (equiv_eval rpo_infos n) l1 l2) as [ [l1' l2'] | ].
destruct H' as [ll [E_ll [P1 [P2 H']]]];
apply Eq_mul; trivial.
assert (H1:= prec_eq_status). assert (H1':= H1 symbol Prec f1 f2).
assert (status Prec f1 = status Prec f2). apply H1'; trivial. trivial.
assert (H3:= prec_eq_bool_ok). assert (H3':= H3 symbol Prec f1 f2).
rewrite f1_eq_f2 in H3'. trivial. rewrite <- H0. trivial.
assert (H3:= prec_eq_bool_ok). assert (H3':= H3 symbol Prec f1 f2).
rewrite f1_eq_f2 in H3'. trivial.
destruct l1'; destruct l2'; try discriminate; simpl in P1; trivial.
generalize l1 l2 P1 P2; clear l1 l2 P1 P2; 
induction ll as [ | [t1 t2] ll]; intros l1 l2 P1 P2.
rewrite (permut_nil P1); rewrite (permut_nil P2); apply Pnil.
destruct (permut_inv_right P1) as [t1' [l1' [l1'' [t1_eq_t1' [H'' Q1]]]]]; subst l1 t1'.
destruct (permut_inv_right P2) as [t2' [l2' [l2'' [t2_eq_t2' [H'' Q2]]]]]; subst l2 t2'.
simpl; apply permut_strong.
apply IHn; apply E_ll; left; trivial.
apply IHll; trivial.
intros; apply E_ll; right; trivial.
discriminate.
intro; discriminate.
Qed.

Lemma equiv_eval_list_fully_evaluates :
  forall p l1 l2, (forall t1 t2, In t1 l1 -> In t2 l2 -> p t1 t2 <> None) ->
  equiv_eval_list p l1 l2 <> None.
Proof.
intros p l1 l2 E;
functional induction (equiv_eval_list p l1 l2) as 
[ 
| H1 H2 t1 l1 H3 t2 l2 H4 H IH
| H1 H2 t1 l1 H3 t2 l2 H4 H
| H1 H2 t1 l1 H3 t2 l2 H4 H
| l1 l2 H1 H2 H3 H4 H].
(* 1/5 *) 
discriminate.
(* 1/4 *)
apply IH; intros u1 u2 u1_in_l1 u2_in_l2; apply E; right; trivial.
(* 1/3 *)
discriminate.
(* 1/2 *)
assert (E' := E t1 t2); rewrite H in E'; apply E'; left; trivial.
(* 1/1 *)
discriminate.
Qed.

Lemma remove_equiv_eval_fully_evaluates :
  forall p t l, (forall t', In t' l -> p t t' <> None) -> 
  remove_equiv_eval p t l <> @Not_finished _.
Proof.
intros p t l E;
functional induction (remove_equiv_eval p t l) as 
  [ 
  | H1 a l t' H 
  | H1 a l t' H IH l' H' 
  | H1 a l t' H IH H' 
  | H1 a l t' H IH H' 
  | H1 a l t' H].
discriminate.
discriminate.
discriminate.
discriminate.
rewrite H' in IH; apply IH; intros; apply E; right; trivial.
assert (H' := E _ (or_introl _ (eq_refl _)) H); contradiction.
Qed.

Lemma remove_equiv_eval_list_fully_evaluates :
  forall p l1 l2, (forall t1 t2, In t1 l1 -> In t2 l2 -> p t1 t2 <> None) ->
  remove_equiv_eval_list p l1 l2 <> None.
Proof.
intros p l1 l2 E; 
functional induction (remove_equiv_eval_list p l1 l2) as
[ l1
| H1 l2 H2 H3 H4 H'
| H1 l2 t1 l1 H2 H3 H4 H' l2' H IH 
| H1 l2 t1 l1 H2 H3 H4 H' H IH l1' l2' R
| H1 l2 t1 l1 H2 H3 H4 H' H IH R
| H1 l2 t1 l1 H2 H3 H4 H' H].
(* 1/6 *)
discriminate.
(* 1/5 *)
discriminate.
(* 1/4 *)
assert (K := remove_equiv_eval_is_sound p t1 H3); rewrite H in K;
destruct K as [t2 [t2_in_l2 P2]];
apply IH; intros u1 u2 u1_in_l1 u2_in_l2'; apply E; trivial.
right; trivial.
rewrite (in_permut_in P2); right; trivial.
(* 1/3 *)
discriminate.
(* 1/2 *)
rewrite R in IH; apply IH; intros u1 u2 u1_in_l1 u2_in_l2; apply E; trivial;
right; trivial.
(* 1/1 *)
assert (K := remove_equiv_eval_fully_evaluates p t1 H3);
rewrite H in K; intros _; apply K; trivial.
intros t2 t2_in_l2; apply E; trivial; left; trivial.
Qed.

Lemma equiv_eval_terminates :
  forall rpo_infos n t1 t2, size t1 + size t2 <= n -> equiv_eval rpo_infos n t1 t2 <> None.
Proof.
intros rpo_infos n; induction n as [ | n].
(* base case *)
intros t1 t2 St1; 
absurd (1 <= 0); auto with arith; 
apply le_trans with (size t1 + size t2); trivial;
apply le_trans with (1 + size t2);
[apply le_plus_l | apply plus_le_compat_r; apply size_ge_one].
(* induction step *)
intros t1 t2 St; rewrite equiv_eval_equation.
destruct t1 as [ v1 | f1 l1]; destruct t2 as [ v2 | f2 l2].
discriminate.
intros; discriminate.
intros; discriminate.
case (mem_bool eq_tt_bool ((Term f1 l1), (Term f2 l2)) (equiv_l rpo_infos));simpl.
discriminate.
case_eq (prec_eq_bool Prec f1 f2). intro f1_eq_f2.
assert (H : forall t1 t2 : term, In t1 l1 -> In t2 l2 -> equiv_eval rpo_infos n t1 t2 <> None).
intros t1 t2 t1_in_l1 t2_in_l2; apply IHn.
rewrite size_unfold in St; rewrite <- plus_assoc in St.
rewrite size_unfold in St; simpl in St.
refine (le_trans _ _ _ _ (le_S_n _ _ St)); apply plus_le_compat.
generalize (size_direct_subterm t1 (Term f1 l1) t1_in_l1);
rewrite (size_unfold (Term f1 l1)); simpl; auto with arith.
generalize (size_direct_subterm t2 (Term f1 l2) t2_in_l2);
rewrite (size_unfold (Term f1 l2)); simpl; auto with arith.
case (status Prec f1).
apply equiv_eval_list_fully_evaluates; trivial.
assert (H':= remove_equiv_eval_list_fully_evaluates (equiv_eval rpo_infos n) l1 l2 H);
destruct (remove_equiv_eval_list (equiv_eval rpo_infos n) l1 l2) as [ [[ | t1' l1'] [ | t2' l2']] | ];
try discriminate.
apply False_rect; apply H'; trivial.
intros.
discriminate.
Qed.

Lemma equiv_eval_is_complete_true :
  forall rpo_infos n t1 t2, size t1 + size t2 <= n -> equiv t1 t2 -> 
     equiv_eval rpo_infos n t1 t2 = Some true.
Proof.
intros rpo_infos n; induction n as [ | n ].
(* base case *)
intros t1 t2 St; absurd (1 <= 0); auto with arith.
refine (le_trans _ _ _ _ St); apply le_trans with (size t1);
[ apply size_ge_one | apply le_plus_l].
(* induction step *)
intros t1 t2 St t1_eq_t2; 
inversion t1_eq_t2 as 
[ t
| f g l1 l2 Sf Sg f_eq_g
| f g l1 l2 Sf Sg f_eq_g P1 P2]; subst.
(* 1/3 syntactic equality *)
destruct t2 as [v2 | f2 l2]; simpl.
generalize (X.eq_bool_ok v2 v2); case (X.eq_bool v2 v2); [intros _ | intro v2_diff_v2; absurd (v2 = v2)]; trivial.
case (mem_bool eq_tt_bool (Term f2 l2, Term f2 l2) (equiv_l rpo_infos)); [reflexivity | idtac].
case_eq (prec_eq_bool Prec f2 f2).
intro H. clear H.
assert (H : forall t2, In t2 l2 -> equiv_eval rpo_infos n t2 t2 = Some true).
intros t2 t2_in_l2; apply IHn.
apply le_S_n; refine (le_trans _ _ _ _ St);
replace (S (size t2 + size t2)) with (S (size t2) + size t2); trivial;
apply plus_le_compat; [idtac | apply lt_le_weak];
apply size_direct_subterm; trivial.
apply Eq.
destruct (status Prec f2).
(* 1/5 f2 has a Lex status *)
clear St t1_eq_t2; induction l2 as [ | t2 l2]; simpl; trivial.
rewrite (H t2); [rewrite IHl2 | left]; trivial; intros; apply H; right; trivial.
(* 1/4 f2 has a Mul status *)
assert (H' : remove_equiv_eval_list (equiv_eval rpo_infos n) l2 l2 = Some (nil,nil)).
clear St t1_eq_t2; induction l2 as [ | t2 l2]; simpl; trivial.
rewrite (H t2); [rewrite IHl2 | left]; trivial; intros; apply H; right; trivial.
rewrite H'; trivial.
intros H. assert (H2:= prec_eq_bool_ok). assert (H2':= H2 symbol Prec f2 f2). rewrite H in H2'. contradict H2'. apply prec_eq_refl.
(* 1/2 Eq_lex *)
rewrite equiv_eval_equation.
case (mem_bool eq_tt_bool (Term f l1, Term g l2) (equiv_l rpo_infos)); [reflexivity | idtac].
rewrite Sf; 
generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); [intros _ | intro f_diff_f; absurd (f = f); trivial].
assert (Size : forall t1 t2, In t1 l1 -> In t2 l2 -> size t1 + size t2 <= n).
intros t1 t2 t1_in_l1 t2_in_l2;
apply le_S_n; refine (le_trans _ _ _ _ St);
replace (S (size t1 + size t2)) with (S (size t1) + size t2); trivial;
apply plus_le_compat; [idtac | apply lt_le_weak];
apply size_direct_subterm; trivial.
generalize l2 H Size; clear l2 H Size St t1_eq_t2; 
induction l1 as [ | t1 l1]; intros l2 H Size;
inversion H as [ | s t2 l l2' t1_eq_t2 l1_eq_l2']; subst; simpl.
case_eq (prec_eq_bool Prec f g).
intros. trivial.
intro eq_f_g. assert (H1:= prec_eq_bool_ok). assert (H1':= H1 symbol Prec f g ). rewrite eq_f_g in H1'. contradict H1'; trivial. 
rewrite (IHn t1 t2); trivial.
apply IHl1; trivial.
intros; apply Size; right; trivial.
apply Size; left; trivial.
(* 1/1 Eq_mul *)
assert (St' : forall t1 t2, In t1 l1 -> In t2 l2 -> size t1 + size t2 <= n).
intros t1 t2 t1_in_l1 t2_in_l2; apply le_S_n; refine (le_trans _ _ _ _ St);
replace (S (size t1 + size t2)) with (S (size t1) + size t2); trivial;
apply plus_le_compat; [idtac | apply lt_le_weak];
apply size_direct_subterm; trivial.
assert (T : forall t1 t2, In t1 l1 -> In t2 l2 -> equiv_eval rpo_infos n t1 t2 <> None).
intros t1 t2 t1_in_l1 t2_in_l2; apply equiv_eval_terminates; apply St'; trivial.
assert (H' : remove_equiv_eval_list (equiv_eval rpo_infos n) l1 l2 = Some (nil,nil)).
generalize l2 P1 St' T; clear l2 P1 St t1_eq_t2 St' T;
induction l1 as [ | t1 l1]; intros l2 P1 St' T; 
inversion P1 as [ | t1' t2 l1' l2' l2'' t1_eq_t2 l1_eq_l2]; trivial.
assert (H' := remove_equiv_eval_is_sound (equiv_eval rpo_infos n) t1 l2).
subst; simpl.
destruct (remove_equiv_eval (equiv_eval rpo_infos n) t1 (l2' ++ t2 :: l2'')) 
  as [ | | l'].
assert (H'' := H' t2); rewrite (IHn t1 t2) in H''; trivial.
assert (H''' : Some true = Some false).
apply H''; apply in_or_app; right; left; trivial.
discriminate.
apply St'.
left; trivial.
apply in_or_app; right; left; trivial.
assert False.
destruct H' as [t' [t'_in_l2 H'']].
apply (T t1 t'); trivial; left; trivial.
contradiction.
destruct H' as [t' [t1_eq_t' P2]].
assert (H : l2' ++ t2 :: l2'' <> nil).
destruct l2' as [ | t2' l2']; simpl; discriminate.
assert (Q : list_permut.permut0 (eq (A:=term)) (t2 :: l2' ++ l2'') (l2' ++ t2 :: l2'')).
apply Pcons; trivial.
apply list_permut.permut_refl; intro; trivial.
destruct (l2' ++ t2 :: l2'') as [ | t2' k2].
absurd (@nil term = nil); trivial.
apply IHl1; trivial.
apply permut0_trans with (l2' ++ l2''); trivial. apply equiv_equiv.
assert (t1_eq_t'' : equiv t1 t').
apply (equiv_eval_is_sound_weak _ _ _ _ t1_eq_t').
assert (t2_eq_t' : equiv t2 t').
transitivity t1; trivial; symmetry; reflexivity || trivial.
rewrite (@permut0_cons _ _ equiv_equiv _ _  (l2' ++ l2'') l'  t2_eq_t').
apply permut_impl with (@eq term); trivial.
intros; subst; apply Eq.
apply list_permut.permut_trans with (t2' :: k2); trivial. 
intros a b c _ _ _ a_eq_b b_eq_c; subst; trivial.
intros; apply St'.
right; trivial.
rewrite (in_permut_in P2); right; trivial.
intros; apply T.
right; trivial.
rewrite (in_permut_in P2); right; trivial.
rewrite equiv_eval_equation; rewrite Sf; rewrite H'.
case (mem_bool eq_tt_bool (Term f l1, Term g l2) (equiv_l rpo_infos)); [reflexivity | idtac].
case_eq (prec_eq_bool Prec f g).
intro; trivial.
intro f_eq'_g.
assert (H1:= prec_eq_bool_ok). assert (H1':= H1 symbol Prec f g).
rewrite f_eq'_g in H1'.
contradict H1'; trivial.
Qed.

Lemma equiv_eval_is_sound :
  forall rpo_infos n t1 t2, size t1 + size t2 <= n ->
     match equiv_eval rpo_infos n t1 t2 with
     | Some true => equiv t1 t2
     | Some false => ~equiv t1 t2
     | None => False
     end.
Proof.
intros rpo_infos n t1 t2 St;
assert (H := equiv_eval_is_sound_weak rpo_infos n t1 t2);
assert (T := @equiv_eval_terminates rpo_infos n t1 t2 St);
assert (H' := @equiv_eval_is_complete_true rpo_infos n t1 t2 St);
destruct (equiv_eval rpo_infos n t1 t2) as [ [ | ] | ].
apply H; trivial.
intro t1_eq_t2; assert (H'' := H' t1_eq_t2); discriminate.
apply T; trivial.
Qed.

Definition term_gt_list (p : term -> term -> option comp) s l :=
  list_forall_option 
      (fun t => 
          match p s t with
          | Some Greater_than => Some true
          | Some _ => Some false
          | None => None
          end) l.

Fixpoint lexico_eval (p : term -> term -> option comp) (s1 s2 : term)
   (l1 l2 : list term) {struct l1} : option comp :=
    match l1, l2 with
    | nil, nil => Some Equivalent
    | nil, (_ :: _) => Some Less_than
    | (_ :: _), nil => Some Greater_than
    | (t1 :: l1'), (t2 :: l2') =>
          match p t1 t2 with
          | Some Equivalent => lexico_eval p s1 s2 l1' l2'
          | Some Greater_than => 
              match term_gt_list p s1 l2 with
              | Some true => Some Greater_than
              | Some false => Some Uncomparable
              | None => None
              end
          | Some Less_than =>
              match term_gt_list p s2 l1 with
              | Some true => Some Less_than
              | Some false => Some Uncomparable
              | None => None
              end
         | Some Uncomparable => Some Uncomparable
         | None => None
     end
end.

Lemma lexico_eval_equation :
  forall p s1 s2 l1 l2, lexico_eval p s1 s2 l1 l2 =
    match l1, l2 with
    | nil, nil => Some Equivalent
    | nil, (_ :: _) => Some Less_than
    | (_ :: _), nil => Some Greater_than
    | (t1 :: l1'), (t2 :: l2') =>
          match p t1 t2 with
          | Some Equivalent => lexico_eval p s1 s2 l1' l2'
          | Some Greater_than => 
              match term_gt_list p s1 l2 with
              | Some true => Some Greater_than
              | Some false => Some Uncomparable
              | None => None
              end
          | Some Less_than =>
              match term_gt_list p s2 l1 with
              | Some true => Some Less_than
              | Some false => Some Uncomparable
              | None => None
              end
         | Some Uncomparable => Some Uncomparable
         | None => None
     end
end.
Proof.
intros p s1 s2 [ | t1 l1] [ | t2 l2]; apply eq_refl.
Qed.

Definition list_gt_list  (p : term -> term -> option comp) lg ls :=
           list_forall_option 
     (fun s => 
list_exists_option 
  (fun g => 
     match p g s with
| Some Greater_than => Some true
| Some _ => Some false
                        | None => None
                      end) lg) ls.

Definition mult_eval (p : term -> term -> option comp) (l1 l2 : list term)  : option comp :=
         match list_gt_list p l1 l2 with
         | None => None
         | Some true => Some Greater_than
         | Some false =>
          match list_gt_list p l2 l1 with
 | Some true => Some Less_than
 | Some false => Some Uncomparable
          | None => None
          end
end.

Fixpoint rpo_eval rpo_infos (n : nat) (t1 t2 : term) {struct n} : option comp :=
    if mem_bool eq_tt_bool (t1, t2) (rpo_l rpo_infos) 
      then Some Less_than
      else if mem_bool eq_tt_bool (t2, t1) (rpo_l rpo_infos) 
        then Some Greater_than 
        else if mem_bool eq_tt_bool (t1, t2) (equiv_l rpo_infos) 
          then Some Equivalent 
          else if mem_bool eq_tt_bool (t2, t1) (equiv_l rpo_infos) 
            then Some Equivalent 
            else
          



  (match equiv_eval rpo_infos n t1 t2 with
  | None => None
  | Some true => Some Equivalent
  | Some false =>
     (match t1, t2 with
     | Var _, Var _ => Some Uncomparable

     | Var x, (Term _ l) =>
        if var_in_term_list x l
        then Some Less_than
        else Some Uncomparable

     | (Term _ l), Var x =>
        if var_in_term_list x l
        then Some Greater_than
        else Some Uncomparable

     | (Term f1 l1), (Term f2 l2) =>
       (match n with
       | 0 => None
       | S m => 
         let check_l1_gt_t2 :=
                     list_exists_option 
          (fun t => match rpo_eval rpo_infos m t t2 with 
                                    | Some Equivalent 
                                    | Some Greater_than => Some true
                                    | Some _ => Some false
                           | None => None
                                   end) l1 in
          (match check_l1_gt_t2 with
          | None => None
          | Some true => Some Greater_than
          | Some false =>
            let check_l2_gt_t1 :=
                   list_exists_option 
       (fun t => match rpo_eval rpo_infos m t1 t with
                                       | Some Equivalent 
                                       | Some Less_than => Some true
                                       | Some _ => Some false
                                       | None  => None
                                     end) l2 in
          (match check_l2_gt_t1 with
          | None => None
          | Some true => Some Less_than
          | Some false =>
             (match prec_eval f1 f2 with
 | Uncomparable => Some Uncomparable
 | Greater_than =>
      let check_l2_lt_t1 :=
                          list_forall_option
     (fun t => match rpo_eval rpo_infos m t1 t with
                                               | Some Greater_than => Some true
                                               | Some _ => Some false
        	                       | None => None
                                               end) l2 in
                     (match check_l2_lt_t1 with
                     | None => None
                     | Some true => Some Greater_than
                     | Some false => Some Uncomparable
                    end)
 | Less_than =>
                      let check_l1_lt_t2 :=
         list_forall_option
   (fun t => match rpo_eval rpo_infos m t t2 with
                                               | Some Less_than => Some true
                                               | Some _ => Some false
                                               | None => None
                                               end) l1 in
                      (match check_l1_lt_t2 with
                      | None => None
     | Some true => Some Less_than
     | Some false => Some Uncomparable
                    end)
 | Equivalent =>
(match status Prec f1 with
 | Mul => 
                                match remove_equiv_eval_list (equiv_eval rpo_infos m) l1 l2 with
                                | None => None
                                | Some (nil, nil) => Some Equivalent
                                | Some (nil, _ :: _) => Some Less_than
                                | Some (_ :: _,nil) => Some Greater_than
                                | Some (l1, l2) => mult_eval (rpo_eval rpo_infos m) l1 l2
                                end
 | Lex => 
                               if (beq_nat (length l1) (length l2)) || 
                                  (leb (length l1) rpo_infos.(bb) && leb (length l2) rpo_infos.(bb))
                               then lexico_eval (rpo_eval rpo_infos m) t1 t2 l1 l2
                               else Some Uncomparable
                       end) 
          end)
        end)
      end)
    end)
  end)
end).

Lemma rpo_eval_equation :
  forall rpo_infos n t1 t2, rpo_eval rpo_infos n t1 t2 =
    if mem_bool eq_tt_bool (t1, t2) (rpo_l rpo_infos) 
      then Some Less_than
      else if mem_bool eq_tt_bool (t2, t1) (rpo_l rpo_infos) 
        then Some Greater_than 
        else if mem_bool eq_tt_bool (t1, t2) (equiv_l rpo_infos) 
          then Some Equivalent 
          else if mem_bool eq_tt_bool (t2, t1) (equiv_l rpo_infos) 
            then Some Equivalent 
            else
          



  (match equiv_eval rpo_infos n t1 t2 with
  | None => None
  | Some true => Some Equivalent
  | Some false =>
     (match t1, t2 with
     | Var _, Var _ => Some Uncomparable

     | Var x, (Term _ l) =>
        if var_in_term_list x l
        then Some Less_than
        else Some Uncomparable

     | (Term _ l), Var x =>
        if var_in_term_list x l
        then Some Greater_than
        else Some Uncomparable

     | (Term f1 l1), (Term f2 l2) =>
       (match n with
       | 0 => None
       | S m => 
         let check_l1_gt_t2 :=
                     list_exists_option 
          (fun t => match rpo_eval rpo_infos m t t2 with 
                                    | Some Equivalent 
                                    | Some Greater_than => Some true
                                    | Some _ => Some false
                           | None => None
                                   end) l1 in
          (match check_l1_gt_t2 with
          | None => None
          | Some true => Some Greater_than
          | Some false =>
            let check_l2_gt_t1 :=
                   list_exists_option 
       (fun t => match rpo_eval rpo_infos m t1 t with
                                       | Some Equivalent 
                                       | Some Less_than => Some true
                                       | Some _ => Some false
                                       | None  => None
                                     end) l2 in
          (match check_l2_gt_t1 with
          | None => None
          | Some true => Some Less_than
          | Some false =>
             (match prec_eval f1 f2 with
 | Uncomparable => Some Uncomparable
 | Greater_than =>
      let check_l2_lt_t1 :=
                          list_forall_option
     (fun t => match rpo_eval rpo_infos m t1 t with
                                               | Some Greater_than => Some true
                                               | Some _ => Some false
        	                       | None => None
                                               end) l2 in
                     (match check_l2_lt_t1 with
                     | None => None
                     | Some true => Some Greater_than
                     | Some false => Some Uncomparable
                    end)
 | Less_than =>
                      let check_l1_lt_t2 :=
         list_forall_option
   (fun t => match rpo_eval rpo_infos m t t2 with
                                               | Some Less_than => Some true
                                               | Some _ => Some false
                                               | None => None
                                               end) l1 in
                      (match check_l1_lt_t2 with
                      | None => None
     | Some true => Some Less_than
     | Some false => Some Uncomparable
                    end)
 | Equivalent =>
(match status Prec f1 with
 | Mul => 
                                match remove_equiv_eval_list (equiv_eval rpo_infos m) l1 l2 with
                                | None => None
                                | Some (nil, nil) => Some Equivalent
                                | Some (nil, _ :: _) => Some Less_than
                                | Some (_ :: _,nil) => Some Greater_than
                                | Some (l1, l2) => mult_eval (rpo_eval rpo_infos m) l1 l2
                                end
 | Lex => 
                               if (beq_nat (length l1) (length l2)) || 
                                  (leb (length l1) rpo_infos.(bb) && leb (length l2) rpo_infos.(bb))
                               then lexico_eval (rpo_eval rpo_infos m) t1 t2 l1 l2
                               else Some Uncomparable
                       end) 
          end)
        end)
      end)
    end)
  end)
end).
Proof.
intros rpo_infos [ | n] [v1 | f1 l1] [v2 | f2 l2];
unfold rpo_eval; simpl; trivial.
Qed.

Lemma term_gt_list_is_sound :
  forall p s l,
   match term_gt_list p s l with
   | Some true => forall t, In t l -> p s t = Some Greater_than
   | _ => True
   end.
Proof.
intros p s l; induction l as [ | t l]; simpl.
intros; contradiction.
replace (term_gt_list p s (t :: l)) with
  (match p s t with
    | Some Greater_than => term_gt_list p s l
    | Some _ => match term_gt_list p s l with Some _ => Some false | None => None end
    | None => None
    end).
case_eq (p s t); [intros [ | | | ] H | trivial].
destruct (term_gt_list p s l) as [ [ | ] | ]; trivial.
destruct (term_gt_list p s l) as [ [ | ] | ]; trivial.
destruct (term_gt_list p s l) as [ [ | ] | ]; trivial.
intros u [u_eq_t | u_in_l]; [subst | apply IHl]; assumption.
destruct (term_gt_list p s l) as [ [ | ] | ]; trivial.
unfold term_gt_list; simpl.
destruct (p s t) as [[ | | | ] | ]; trivial.
Qed.

Lemma lexico_eval_is_sound :
  forall (p : term -> term -> option comp) s1 s2 l1 l2,
           match lexico_eval p s1 s2 l1 l2 with
           | Some Equivalent => 
             (exists ll, (forall t1 t2, In (t1,t2) ll -> p t1 t2 = Some Equivalent) /\
                            l1 = map (fun st => fst st) ll /\
                            l2 = map (fun st => snd st) ll) 
             |  Some Less_than => 
                 (l1 = nil /\ l2 <> nil) \/
                 (exists ll, exists t2, exists l2',
                   (forall t1 t2, In (t1,t2) ll -> p t1 t2 = Some Equivalent) /\
                   l1 = map (fun st => fst st) ll /\
                   l2 = map (fun st => snd st) ll ++ t2 :: l2') \/
                 (exists ll, exists t1, exists t2, exists l1', exists l2',
                   (forall t1 t2, In (t1,t2) ll -> p t1 t2 = Some Equivalent) /\
                   p t1 t2 = Some Less_than /\
                   (forall t1, In t1 l1 -> 
                   ((exists t2, In t2 l2 /\ (p t1 t2 = Some Equivalent \/
                                                     p t1 t2 = Some Less_than)) \/ 
                                                  p s2 t1 = Some Greater_than)) /\
                   l1 = map (fun st => fst st) ll ++ t1 :: l1' /\
                   l2 = map (fun st => snd st) ll ++ t2 :: l2')
             |  Some Greater_than => 
                 (l1 <> nil /\ l2 = nil) \/
                 (exists ll, exists t1, exists l1',
                   (forall t1 t2, In (t1,t2) ll -> p t1 t2 = Some Equivalent) /\
                   l1 = map (fun st => fst st) ll ++ t1 :: l1' /\
                   l2 = map (fun st => snd st) ll) \/
                (exists ll, exists t1, exists t2, exists l1', exists l2',
                   (forall t1 t2, In (t1,t2) ll -> p t1 t2 = Some Equivalent) /\
                   p t1 t2 = Some Greater_than /\
                   (forall t2, In t2 l2 -> 
                   ((exists t1, In t1 l1 /\ (p t1 t2 = Some Equivalent \/
                                                     p t1 t2 = Some Greater_than)) \/ 
                                                  p s1 t2 = Some Greater_than)) /\
                   l1 = map (fun st => fst st) ll ++ t1 :: l1' /\
                   l2 = map (fun st => snd st) ll ++ t2 :: l2')
            | _ => True
end.
Proof. 
intros p s1 s2 l1; induction l1 as [ | t1 l1]; intros [ | t2 l2].
simpl; exists (@nil (term * term)); simpl; intuition.
simpl; left; split; [apply eq_refl | discriminate].
simpl; left; split; [discriminate | apply eq_refl].
simpl; case_eq (p t1 t2); [idtac | trivial].
intros [ | | | ] Ht; generalize (IHl1 l2).
(* 1/4 p t1 t2 = Some Equivalent *)
case_eq (lexico_eval p s1 s2 l1 l2); [intros [ | | | ] Hl | trivial].
(* 1/7 lexico_eval p s1 s2 l1 l2 = Some Equivalent *)
intros [ll [Hll [H1 H2]]]; exists ((t1,t2) :: ll); split.
simpl; intros u1 u2 [u1u2_eq_t1t2 | u1u2_in_ll]; [injection u1u2_eq_t1t2; intros; subst | apply Hll]; assumption.
simpl; split; subst; apply eq_refl.
(* 1/6 lexico_eval p s1 s2 l1 l2 = Some Less_than *)
intros [[H1 H2] | [[ll [a2 [l2' [Hll [H1 H2]]]]] | [ll [a1 [a2 [l1' [l2' [Hll [Ha [H [H1 H2]]]]]]]]]]].
right; left; subst; destruct l2 as [ | a2 l2].
discriminate.
exists ((t1,t2) :: nil); exists a2; exists l2; split.
simpl; intros u1 u2 [u1u2_eq_t1t2 | u1u2_in_nil]; [injection u1u2_eq_t1t2; intros; subst; assumption | contradiction].
split; apply eq_refl.
right; left; exists ((t1,t2) :: ll); exists a2; exists l2'; split.
simpl; intros u1 u2 [u1u2_eq_t1t2 | u1u2_in_ll]; [injection u1u2_eq_t1t2; intros; subst | apply Hll]; assumption.
split; subst; apply eq_refl.
do 2 right; exists ((t1,t2) :: ll); exists a1; exists a2; exists l1'; exists l2'; split.
simpl; intros u1 u2 [u1u2_eq_t1t2 | u1u2_in_ll]; [injection u1u2_eq_t1t2; intros; subst | apply Hll]; assumption.
split.
assumption.
split.
intros u [t1_eq_u | u_in_l1].
subst u; left; exists t2; split; left; trivial.
destruct (H _ u_in_l1) as [[u2 [u2_in_l2 H']] | H'].
left; exists u2; split; [right | idtac]; assumption.
right; assumption.
split; subst; apply eq_refl.
(* 1/5 lexico_eval p s1 s2 l1 l2 = Some Greater_than *)
intros [[H1 H2] | [[ll [a1 [l1' [Hll [H1 H2]]]]] | [ll [a1 [a2 [l1' [l2' [Hll [Ha [H [H1 H2]]]]]]]]]]].
right; left; subst; destruct l1 as [ | a1 l1].
discriminate.
exists ((t1,t2) :: nil); exists a1; exists l1; split.
simpl; intros u1 u2 [u1u2_eq_t1t2 | u1u2_in_nil]; [injection u1u2_eq_t1t2; intros; subst; assumption | contradiction].
split; apply eq_refl.
right; left; exists ((t1,t2) :: ll); exists a1; exists l1'; split.
simpl; intros u1 u2 [u1u2_eq_t1t2 | u1u2_in_ll]; [injection u1u2_eq_t1t2; intros; subst | apply Hll]; assumption.
split; subst; apply eq_refl.
do 2 right; exists ((t1,t2) :: ll); exists a1; exists a2; exists l1'; exists l2'; split.
simpl; intros u1 u2 [u1u2_eq_t1t2 | u1u2_in_ll]; [injection u1u2_eq_t1t2; intros; subst | apply Hll]; assumption.
split.
assumption.
split.
intros u [t2_eq_u | u_in_l2].
subst u; left; exists t1; split; left; trivial.
destruct (H _ u_in_l2) as [[u1 [u1_in_l1 H']] | H'].
left; exists u1; split; [right | idtac]; assumption.
right; assumption.
split; subst; apply eq_refl.
(* 1/4 lexico_eval p s1 s2 l1 l2 = Some Uncomparable *)
trivial.
(* 1/3 p t1 t2 = Some Less_than *)
case_eq (lexico_eval p s1 s2 l1 l2).
intros [ | | | ] Hl.
(* 1/7 lexico_eval p s1 s2 l1 l2 = Some Equivalent *)
intros [ll [Hll [H1 H2]]].
generalize (term_gt_list_is_sound p s2 (t1 :: l1)).
destruct (term_gt_list p s2 (t1 :: l1)) as [[ | ] | ].
intro H; do 2 right; exists (@nil (term * term)); exists t1; exists t2; exists l1; exists l2; split.
intros; contradiction.
split.
assumption.
split.
intros u u_in_t1l1; right; apply H; trivial.
simpl; split; subst; apply eq_refl.
trivial.
trivial.
(* 1/6 lexico_eval p s1 s2 l1 l2 = Some Less_than *)
intros [[H1 H2] | [[ll [a2 [l2' [Hll [H1 H2]]]]] | [ll [a1 [a2 [l1' [l2' [Hll [Ha [H [H1 H2]]]]]]]]]]];
generalize (term_gt_list_is_sound p s2 (t1 :: l1)); destruct (term_gt_list p s2 (t1 :: l1)) as [[ | ] | ]; intro H'; trivial;
do 2 right; exists (@nil (term * term)); exists t1; exists t2; exists l1; exists l2; split.
intros; contradiction.
split.
assumption.
split.
intros u u_in_t1l1; right; apply H'; assumption.
split; apply eq_refl.
intros; contradiction.
split.
assumption.
split.
intros u u_in_t1l1; right; apply H'; assumption.
split; apply eq_refl.
intros; contradiction.
split.
assumption.
split.
intros u u_in_t1l1; right; apply H'; assumption.
split; apply eq_refl.
(* 1/5 lexico_eval p s1 s2 l1 l2 = Some Greater_than *)
intros _.
generalize (term_gt_list_is_sound p s2 (t1 :: l1)); destruct (term_gt_list p s2 (t1 :: l1)) as [[ | ] | ]; intro H'; trivial.
do 2 right; exists (@nil (term * term)); exists t1; exists t2; exists l1; exists l2; split.
intros; contradiction.
split.
assumption.
split.
intros u u_in_t1l1; right; apply H'; assumption.
split; apply eq_refl.
(* 1/4 lexico_eval p s1 s2 l1 l2 = Some  Some Uncomparable *)
intros _.
generalize (term_gt_list_is_sound p s2 (t1 :: l1)); destruct (term_gt_list p s2 (t1 :: l1)) as [[ | ] | ]; intro H'; trivial.
do 2 right; exists (@nil (term * term)); exists t1; exists t2; exists l1; exists l2; split.
intros; contradiction.
split.
assumption.
split.
intros u u_in_t1l1; right; apply H'; assumption.
split; apply eq_refl.
(* 1/3 lexico_eval p s1 s2 l1 l2 = None *)
intros _.
generalize (term_gt_list_is_sound p s2 (t1 :: l1)); destruct (term_gt_list p s2 (t1 :: l1)) as [[ | ] | ]; intro H'; trivial.
do 2 right; exists (@nil (term * term)); exists t1; exists t2; exists l1; exists l2; split.
intros; contradiction.
split.
assumption.
split.
intros u u_in_t1l1; right; apply H'; assumption.
split; apply eq_refl.
(* 1/3 p t1 t2 = Some Greater_than *)
case_eq (lexico_eval p s1 s2 l1 l2).
intros [ | | | ] Hl.
(* 1/6 lexico_eval p s1 s2 l1 l2 = Some Equivalent *)
intros [ll [Hll [H1 H2]]].
generalize (term_gt_list_is_sound p s1 (t2 :: l2)).
destruct (term_gt_list p s1 (t2 :: l2)) as [[ | ] | ].
intro H; do 2 right; exists (@nil (term * term)); exists t1; exists t2; exists l1; exists l2; split.
intros; contradiction.
split.
assumption.
split.
intros u u_in_t1l2; right; apply H; trivial.
simpl; split; subst; apply eq_refl.
trivial.
trivial.
(* 1/5 lexico_eval p s1 s2 l1 l2 = Some Less_than *)
intros [[H1 H2] | [[ll [a2 [l2' [Hll [H1 H2]]]]] | [ll [a1 [a2 [l1' [l2' [Hll [Ha [H [H1 H2]]]]]]]]]]];
generalize (term_gt_list_is_sound p s1 (t2 :: l2)); destruct (term_gt_list p s1 (t2 :: l2)) as [[ | ] | ]; intro H'; trivial;
do 2 right; exists (@nil (term * term)); exists t1; exists t2; exists l1; exists l2; split.
intros; contradiction.
split.
assumption.
split.
intros u u_in_t2l2; right; apply H'; assumption.
split; apply eq_refl.
intros; contradiction.
split.
assumption.
split.
intros u u_in_t2l2; right; apply H'; assumption.
split; apply eq_refl.
intros; contradiction.
split.
assumption.
split.
intros u u_in_t2l2; right; apply H'; assumption.
split; apply eq_refl.
(* 1/4 lexico_eval p s1 s2 l1 l2 = Some Greater_than *)
intros _.
generalize (term_gt_list_is_sound p s1 (t2 :: l2)); destruct (term_gt_list p s1 (t2 :: l2)) as [[ | ] | ]; intro H'; trivial.
do 2 right; exists (@nil (term * term)); exists t1; exists t2; exists l1; exists l2; split.
intros; contradiction.
split.
assumption.
split.
intros u u_in_t2l2; right; apply H'; assumption.
split; apply eq_refl.
(* 1/3 lexico_eval p s1 s2 l1 l2 = Some  Some Uncomparable *)
intros _.
generalize (term_gt_list_is_sound p s1 (t2 :: l2)); destruct (term_gt_list p s1 (t2 :: l2)) as [[ | ] | ]; intro H'; trivial.
do 2 right; exists (@nil (term * term)); exists t1; exists t2; exists l1; exists l2; split.
intros; contradiction.
split.
assumption.
split.
intros u u_in_t2l2; right; apply H'; assumption.
split; apply eq_refl.
(* 1/2 lexico_eval p s1 s2 l1 l2 = None *)
intros _.
generalize (term_gt_list_is_sound p s1 (t2 :: l2)); destruct (term_gt_list p s1 (t2 :: l2)) as [[ | ] | ]; intro H'; trivial.
do 2 right; exists (@nil (term * term)); exists t1; exists t2; exists l1; exists l2; split.
intros; contradiction.
split.
assumption.
split.
intros u u_in_t2l2; right; apply H'; assumption.
split; apply eq_refl.
(* 1/1 p t1 t2 = Some Uncomparable *)
trivial.
(*SLOW*)Qed.

Lemma list_gt_list_is_sound :
  forall p lg ls,
   match list_gt_list p lg ls with
   | Some true => forall s, In s ls -> exists g, In g lg /\ p g s = Some Greater_than
   | _ => True
   end.
Proof.
intros p lg ls; revert lg; induction ls as [ | s ls]; intro lg.
simpl; intros; contradiction.
unfold list_gt_list; simpl.
generalize (list_exists_option_is_sound 
  (fun g : term =>
       match p g s with
       | Some Equivalent => Some false
       | Some Less_than => Some false
       | Some Greater_than => Some true
       | Some Uncomparable => Some false
       | None => None
       end) lg).
destruct 
(list_exists_option
    (fun g : term =>
     match p g s with
     | Some Equivalent => Some false
     | Some Less_than => Some false
     | Some Greater_than => Some true
     | Some Uncomparable => Some false
     | None => None
     end) lg) as [[ | ] | ].
intros [g [g_in_ls H]].
generalize (IHls lg); unfold list_gt_list;
destruct 
(list_forall_option
    (fun s0 : term =>
     list_exists_option
       (fun g0 : term =>
        match p g0 s0 with
        | Some Equivalent => Some false
        | Some Less_than => Some false
        | Some Greater_than => Some true
        | Some Uncomparable => Some false
        | None => None
        end) lg) ls) as [[ | ] | ].
intros H' u [s_eq_u | u_in_ls].
subst u; exists g; split; trivial.
destruct (p g s) as [[ | | | ] | ]; (apply eq_refl || discriminate).
apply H'; assumption.
trivial.
trivial.
intros _;
destruct 
(list_forall_option
    (fun s0 : term =>
     list_exists_option
       (fun g0 : term =>
        match p g0 s0 with
        | Some Equivalent => Some false
        | Some Less_than => Some false
        | Some Greater_than => Some true
        | Some Uncomparable => Some false
        | None => None
        end) lg) ls) as [[ | ] | ]; trivial.
trivial.
Qed. 
 

Lemma in_mem : forall s l, In s l -> mem equiv s l.
Proof.
intro s.
induction l.
intro H.
unfold In in H.
auto.
intro H.
unfold In in H.
destruct H.
rewrite H.
simpl.
left.
reflexivity.
simpl.
right.
auto.
Qed.

Lemma mult_eval_is_sound_weak                              :
  forall p l1 l2, 
   match mult_eval p l1 l2 with
     | Some Equivalent => False
     | Some Less_than =>  
       forall t1, In t1 l1 -> exists t2, In t2 l2 /\ p t2 t1 = Some Greater_than
     | Some Greater_than =>  
       forall t2, In t2 l2 -> exists t1, In t1 l1 /\ p t1 t2 = Some Greater_than
     | _ => True
     end.
Proof.
intros p l1 l2; unfold mult_eval.
generalize (list_gt_list_is_sound p l1 l2); destruct (list_gt_list p l1 l2) as [[ | ] | ]; trivial.
intros; generalize (list_gt_list_is_sound p l2 l1); destruct (list_gt_list p l2 l1) as [[ | ] | ]; trivial.
Qed.




Lemma rpo_eval_is_sound_weak :
  forall rpo_infos n t1 t2, 
                match rpo_eval rpo_infos n t1 t2 with
                     | Some Equivalent => equiv t1 t2
                     | Some Greater_than => rpo rpo_infos.(bb) t2 t1
                     | Some Less_than => rpo rpo_infos.(bb) t1 t2
                     | _ => True
                     end.
Proof.
intros rpo_infos n; induction n as [ | n].
intros t1 t2. simpl.
case_eq (mem_bool eq_tt_bool (t1, t2) (rpo_l rpo_infos)). 
intros Hfind;apply (find_is_sound (rpo rpo_infos.(bb)) _ (rpo_l_valid rpo_infos) _ _ (Hfind)).
intro;
case_eq (mem_bool eq_tt_bool (t2, t1) (rpo_l rpo_infos)). 
intros Hfind;apply (find_is_sound (rpo rpo_infos.(bb)) _ (rpo_l_valid rpo_infos) _ _ (Hfind)).
intro. 
case_eq (mem_bool eq_tt_bool (t1, t2) (equiv_l rpo_infos)). 
intros Hfind;apply (find_is_sound equiv _ (equiv_l_valid rpo_infos) _ _ (Hfind)).
intro;
case_eq (mem_bool eq_tt_bool (t2, t1) (equiv_l rpo_infos)). 
intro Hfind. symmetry.
apply (find_is_sound equiv _ (equiv_l_valid rpo_infos) _ _ (Hfind)).
tauto.
(* induction step *)
intros t1 t2; rewrite rpo_eval_equation.
case_eq (mem_bool eq_tt_bool (t1, t2) (rpo_l rpo_infos)). 
intros Hfind;apply (find_is_sound (rpo rpo_infos.(bb)) _ (rpo_l_valid rpo_infos) _ _ (Hfind)).
intros _;
case_eq (mem_bool eq_tt_bool (t2, t1) (rpo_l rpo_infos)). 
intros Hfind;apply (find_is_sound (rpo rpo_infos.(bb)) _ (rpo_l_valid rpo_infos) _ _ (Hfind)).
intros _. 
case_eq (mem_bool eq_tt_bool (t1, t2) (equiv_l rpo_infos)). 
intros Hfind;apply (find_is_sound equiv _ (equiv_l_valid rpo_infos) _ _ (Hfind)).
intros _;
case_eq (mem_bool eq_tt_bool (t2, t1) (equiv_l rpo_infos)). 
intro Hfind. symmetry.
apply (find_is_sound equiv _ (equiv_l_valid rpo_infos) _ _ (Hfind)).
intros _.
assert (E1 := equiv_eval_is_sound_weak rpo_infos (S n) t1 t2); 
destruct (equiv_eval rpo_infos (S n) t1 t2) as [ [ | ] | ].
(* 1/3 t1 and t2 are equivalent *)
apply E1; trivial.
(* 1/2 t1 and t2 are not equivalent *)
clear E1; 
assert (H : forall v f l, var_in_term_list v l = true -> rpo rpo_infos.(bb) (Var v) (Term f l)).
intros v f l H; apply trans_clos_subterm_rpo; trivial.
assert (H' : (In (Var v) l \/ 
                  (exists t, In t l /\ trans_clos direct_subterm (Var v) t)) -> trans_clos direct_subterm (Var v) (Term f l)).
intros [v_in_l | [t [t_in_l H']]].
left; trivial.
apply trans_clos_is_trans with t; trivial; left; trivial.
apply H'; clear H'.
generalize H; clear H; pattern l; refine (list_rec3 size _ _ _); clear l.
intros m; induction m as [ | m]; intros [ | t l] L.
intros; discriminate.
simpl in L; absurd (1 <= 0); auto with arith;
refine (le_trans _ _ _ _ L); apply le_trans with (size t); auto with arith;
apply size_ge_one.
intros; discriminate.
simpl in L; assert (Sl : list_size size l <= m).
apply le_S_n; refine (le_trans _ _ _ _ L); 
apply (plus_le_compat_r 1 (size t) (list_size size l));
apply size_ge_one.
destruct t as [v' | f' l']; rewrite var_in_term_list_equation.
generalize (X.eq_bool_ok v v'); case (X.eq_bool v v'); [intros v_eq_v' _ | intro v_diff_v'].
left; subst; left; trivial.
intro H; destruct (IHm _ Sl H) as [v_in_l | [t [t_in_l H']]].
left; right; trivial.
right; exists t; split; trivial; right; trivial.
assert (Sl' : list_size size l' <= m).
apply le_S_n; refine (le_trans _ _ _ _ L); rewrite size_unfold; simpl;
apply le_n_S; auto with arith.
generalize (IHm _ Sl'); destruct (var_in_term_list v l').
intro H; destruct (H (eq_refl _)) as [v_in_l' | [t [t_in_l' H']]].
right; exists (Term f' l'); split.
left; trivial.
left; trivial.
right; exists (Term f' l'); split.
left; trivial.
apply trans_clos_is_trans with t; trivial; left; trivial.
intros _; generalize (IHm _ Sl); destruct (var_in_term_list v l).
intro H; destruct (H (eq_refl _)) as [v_in_l' | [t [t_in_l' H']]].
left; right; trivial.
right; exists t; split; trivial; right; trivial.
intros; discriminate.
destruct t1 as [v1 | f1 l1]; destruct t2 as [v2 | f2 l2]; trivial.
generalize (H v1 f2 l2); destruct (var_in_term_list v1 l2); 
intro H'; trivial; apply H'; trivial.
generalize (H v2 f1 l1); destruct (var_in_term_list v2 l1); 
intro H'; trivial; apply H'; trivial.
(* 1/2 t1 = Term f1 l1, t2 = Term f2 l2 *)
generalize (list_exists_option_is_sound 
  (fun t : term =>
        match rpo_eval rpo_infos n t (Term f2 l2) with
        | Some Equivalent => Some true
        | Some Less_than => Some false
        | Some Greater_than => Some true
        | Some Uncomparable => Some false
        | None => None (A:=bool)
        end) l1);
destruct (list_exists_option
     (fun t : term =>
      match rpo_eval rpo_infos n t (Term f2 l2) with
      | Some Equivalent => Some true
      | Some Less_than => Some false
      | Some Greater_than => Some true
      | Some Uncomparable => Some false
      | None => None (A:=bool)
      end) l1) as [ [ | ] | ].
(* 1/4 there is a term in l1 which is greater than (Term f2 l2) *)
intros [t1 [t1_in_l1 t1_gt_f2l2]]; simpl; 
apply Subterm with t1; trivial.
apply in_impl_mem; trivial.
exact Eq.
generalize (IHn t1 (Term f2 l2)); 
destruct (rpo_eval rpo_infos n t1 (Term f2 l2)) as [ [ | | | ] | ]; try discriminate.
intro H1; apply Equiv; symmetry; trivial.
intro H1; apply Lt; trivial.
(* 1/3 there are no terms in l1 which are greater than (Term f2 l2) *)
intros _;
generalize (list_exists_option_is_sound 
  (fun t : term =>
        match rpo_eval rpo_infos n (Term f1 l1) t with
        | Some Equivalent => Some true
        | Some Less_than => Some true
        | Some Greater_than => Some false
        | Some Uncomparable => Some false
        | None => None (A:=bool)
        end) l2);
destruct (list_exists_option
     (fun t : term =>
      match rpo_eval rpo_infos n (Term f1 l1) t with
      | Some Equivalent => Some true
      | Some Less_than => Some true
      | Some Greater_than => Some false
      | Some Uncomparable => Some false
      | None => None (A:=bool)
      end) l2) as [ [ | ] | ].
(* 1/5 there is a term in l2 which is greater than (Term f1 l1) *)
intros [t2 [t2_in_l2 t2_gt_f1l1]]; simpl; apply Subterm with t2; trivial.
apply in_impl_mem; trivial.
exact Eq.
generalize (IHn (Term f1 l1) t2); 
destruct (rpo_eval rpo_infos n (Term f1 l1) t2) as [ [ | | | ] | ]; try discriminate.
intro; apply Equiv; trivial.
intro; apply Lt; trivial.
(* 1/4 there are no terms in l2 which are greater than (Term f1 l1) *)
intros _;
generalize (prec_eval_is_sound f1 f2); destruct (prec_eval f1 f2).
(* 1/7 f1 = f2 *)
intro f1_eq_f2. 
assert (Sf1:status Prec f1 = status Prec f2).
 apply prec_eq_status; trivial.
destruct (status Prec f2). rewrite Sf1.
(* 1/8 f1 has a Lex status *)
simpl; assert (H' := lexico_eval_is_sound (rpo_eval rpo_infos n) (Term f1 l1)
                                (Term f2 l2) l1 l2).
destruct (lexico_eval (rpo_eval rpo_infos n) (Term f1 l1) (Term f2 l2) l1 l2) as [ [ | | | ] | ].
(* 1/12 lexico_eval (rpo_eval rpo_infos n) (Term f1 l1) (Term f1 l2) l1 l2 = Some Equivalent *)
destruct H' as [ll [E_ll [H1 H2]]].
rewrite (f_equal (@length _) H1); rewrite (f_equal (@length _) H2); do 2 rewrite length_map.
rewrite <- beq_nat_refl; simpl.
apply (@Eq_lex f1 f2 l1 l2 Sf1). assert (H3:= prec_eq_status). assert (H3':= H3 symbol Prec f1 f2). assert (H4: status Prec f1 = status Prec f2). apply H3'; trivial. rewrite <- H4; trivial. trivial.
subst l1 l2; induction ll as [ | [t1 t2] ll]; simpl.
apply Eq_list_nil.
apply Eq_list_cons.
generalize (IHn t1 t2); rewrite (E_ll _ _ (or_introl _ (eq_refl _))); intro; assumption.
apply IHll; intros; apply E_ll; right; assumption.
(* 1/11 lexico_eval (rpo_eval rpo_infos n) (Term f1 l1) (Term f1 l2) l1 l2 = Some Less_than *)
case_eq (beq_nat (length l1) (length l2)); simpl.
intro L; apply (@Top_eq_lex rpo_infos.(bb) f1 f2 l2 l1 Sf1).  assert (H3:= prec_eq_status). assert (H3':= H3 symbol Prec f1 f2). assert (H4: status Prec f1 = status Prec f2). apply H3'; trivial. rewrite <- H4; trivial. trivial.
left; apply sym_eq; apply beq_nat_true; assumption.
destruct H' as [[H1 H2] | [[ll [t2 [l2' [ _ [H1 H2]]]]] | [ll [t1 [t2 [l1' [l2' [Hll [Ht [H' [H1 H2]]]]]]]]]]].
destruct l2 as [ | a2 l2]; [apply False_rect; apply H2; apply eq_refl | subst l1; discriminate].
subst l1 l2; rewrite length_app in L; do 2 rewrite length_map in L.
apply False_rect; generalize (beq_nat_true _ _ L); clear L; induction ll as [ | [u1 u2] ll].
discriminate.
intro L; injection L; clear L; intro L; apply IHll; assumption.
clear L H'; subst l1 l2; induction ll as [ | [u1 u2] ll].
simpl; constructor 1; generalize (IHn t1 t2); rewrite Ht; intro; assumption.
simpl; constructor 2.
generalize (IHn u1 u2); rewrite (Hll _ _ (or_introl _ (eq_refl _))); intro; assumption.
apply IHll; intros; apply Hll; right; assumption.
destruct H' as [[H1 H2] | [[ll [t2 [l2' [_ [H1 H2]]]]] | [ll [t1 [t2 [l1' [l2' [Hll [Ht [H' [H1 H2]]]]]]]]]]].
intros; subst l1; contradiction.
subst l1 l2; rewrite length_app in L; do 2 rewrite length_map in L.
apply False_rect; generalize (beq_nat_true _ _ L); clear L; induction ll as [ | [u1 u2] ll].
discriminate.
intro L; injection L; clear L; intro L; apply IHll; assumption.
intros u u_in_l1; rewrite mem_in_eq in u_in_l1; destruct u_in_l1 as [u' [u_eq_u' u'_in_l1]].
destruct (H' _ u'_in_l1) as [ [u2 [u2_in_l2 u'_le_u2]] | H''].
apply Subterm with u2.
apply in_impl_mem; trivial.
intros; apply Eq.
destruct u'_le_u2 as [u'_eq_u2 | u'_lt_u2].
left; transitivity u'; trivial.
generalize (IHn u' u2); rewrite u'_eq_u2; intro; assumption.
right; rewrite (equiv_rpo_equiv_2 _ u_eq_u'); generalize (IHn u' u2); rewrite u'_lt_u2; intro; assumption.
rewrite (equiv_rpo_equiv_2 _ u_eq_u'); generalize (IHn (Term f2 l2) u'); rewrite H''; intro; assumption.
intros _; generalize (leb_complete (length l1) (rpo_infos.(bb))); case (leb (length l1) rpo_infos.(bb)); [idtac | simpl; trivial].
generalize (leb_complete (length l2) (rpo_infos.(bb))); case (leb (length l2) (bb rpo_infos)); simpl; [idtac | trivial].
intros L2 L1; apply (@Top_eq_lex rpo_infos.(bb) f1 f2 l2 l1 Sf1).  assert (H3:= prec_eq_status). assert (H3':= H3 symbol Prec f1 f2). assert (H4: status Prec f1 = status Prec f2). apply H3'; trivial. rewrite <- H4; trivial. trivial.
right; split; [apply L1 | apply L2]; apply eq_refl.
clear L1 L2; destruct H' as [[H1 H2] | [[ll [t2 [l2' [Hll [H1 H2]]]]] | [ll [t1 [t2 [l1' [l2' [Hll [Ht [H' [H1 H2]]]]]]]]]]].
subst l1; destruct l2 as [ | a2 l2]; [apply False_rect; apply H2; apply eq_refl | constructor 3].
subst l1 l2; induction ll as [ | [u1 u2] ll].
simpl; constructor 3.
simpl; constructor 2.
generalize (IHn u1 u2); rewrite (Hll _ _ (or_introl _ (eq_refl _))); intro; assumption.
apply IHll; intros; apply Hll; right; assumption.
clear H'; subst l1 l2; induction ll as [ | [u1 u2] ll].
simpl; constructor 1; generalize (IHn t1 t2); rewrite Ht; intro; assumption.
simpl; constructor 2.
generalize (IHn u1 u2); rewrite (Hll _ _ (or_introl _ (eq_refl _))); intro; assumption.
apply IHll; intros; apply Hll; right; assumption.
clear L1 L2; destruct H' as [[H1 H2] | [[ll [t2 [l2' [Hll [H1 H2]]]]] | [ll [t1 [t2 [l1' [l2' [Hll [Ht [H' [H1 H2]]]]]]]]]]].
intros; subst l1; contradiction.
intros u u_in_l1; rewrite mem_in_eq in u_in_l1; destruct u_in_l1 as [u' [u_eq_u' u'_in_l1]].
subst l1; rewrite in_map_iff in u'_in_l1; destruct u'_in_l1 as [[u1 u2] [H1 K2]].
apply Subterm with u2.
subst l2; rewrite <- mem_or_app; left; apply in_impl_mem.
apply Eq.
rewrite in_map_iff; exists (u1,u2); split; trivial.
simpl in H1; subst u1; left; transitivity u'; trivial.
generalize (IHn u' u2); rewrite (Hll _ _ K2); intro; assumption.
intros u u_in_l1; rewrite mem_in_eq in u_in_l1; destruct u_in_l1 as [u' [u_eq_u' u'_in_l1]].
destruct (H' _ u'_in_l1) as [ [u2 [u2_in_l2 u'_le_u2]] | H''].
apply Subterm with u2.
apply in_impl_mem; trivial.
intros; apply Eq.
destruct u'_le_u2 as [u'_eq_u2 | u'_lt_u2].
left; transitivity u'; trivial.
generalize (IHn u' u2); rewrite u'_eq_u2; intro; assumption.
right; rewrite (equiv_rpo_equiv_2 _ u_eq_u'); generalize (IHn u' u2); rewrite u'_lt_u2; intro; assumption.
rewrite (equiv_rpo_equiv_2 _ u_eq_u'); generalize (IHn (Term f2 l2) u'); rewrite H''; intro; assumption.
(* 1/10 lexico_eval (rpo_eval rpo_infos n) (Term f1 l1) (Term f1 l2) l1 l2 = Some Greater_than *)
case_eq (beq_nat (length l1) (length l2)); simpl.
assert (Sf2: status Prec f2 = Lex).
 assert (H3:= prec_eq_status). assert (H3':= H3 symbol Prec f1 f2). assert (H4: status Prec f1 = status Prec f2). apply H3'; trivial. rewrite <- H4; trivial. trivial.
intro L; apply (@Top_eq_lex rpo_infos.(bb) f2 f1 l1 l2 Sf2). trivial. apply prec_eq_sym; trivial.
left; apply beq_nat_true; assumption.
destruct H' as [[H1 H2] | [[ll [t1 [l1' [ _ [H1 H2]]]]] | [ll [t1 [t2 [l1' [l2' [Hll [Ht [H' [H1 H2]]]]]]]]]]].
destruct l1 as [ | a1 l1]; [apply False_rect; apply H1; apply eq_refl | subst l2; discriminate].
subst l1 l2; rewrite length_app in L; do 2 rewrite length_map in L.
apply False_rect; generalize (beq_nat_true _ _ L); clear L; induction ll as [ | [u1 u2] ll].
discriminate.
intro L; injection L; clear L; intro L; apply IHll; assumption.
clear L H'; subst l1 l2; induction ll as [ | [u1 u2] ll].
simpl; constructor 1; generalize (IHn t1 t2); rewrite Ht; intro; assumption.
simpl; constructor 2.
symmetry; generalize (IHn u1 u2); rewrite (Hll _ _ (or_introl _ (eq_refl _))); intro; assumption.
apply IHll; intros; apply Hll; right; assumption.
destruct H' as [[H1 H2] | [[ll [t1 [l1' [_ [H1 H2]]]]] | [ll [t1 [t2 [l1' [l2' [Hll [Ht [H' [H1 H2]]]]]]]]]]].
intros; subst l2; contradiction.
subst l1 l2; rewrite length_app in L; do 2 rewrite length_map in L.
apply False_rect; generalize (beq_nat_true _ _ L); clear L; induction ll as [ | [u1 u2] ll].
discriminate.
intro L; injection L; clear L; intro L; apply IHll; assumption.
intros u u_in_l2; rewrite mem_in_eq in u_in_l2; destruct u_in_l2 as [u' [u_eq_u' u'_in_l2]].
destruct (H' _ u'_in_l2) as [ [u1 [u1_in_l1 u'_le_u1]] | H''].
apply Subterm with u1.
apply in_impl_mem; trivial.
intros; apply Eq.
destruct u'_le_u1 as [u'_eq_u1 | u'_lt_u1].
left; transitivity u'; trivial.
symmetry; generalize (IHn u1 u'); rewrite u'_eq_u1; intro; assumption.
right; rewrite (equiv_rpo_equiv_2 _ u_eq_u'); generalize (IHn u1 u'); rewrite u'_lt_u1; intro; assumption.
rewrite (equiv_rpo_equiv_2 _ u_eq_u'); generalize (IHn (Term f1 l1) u'); rewrite H''; intro; assumption.
intros _; generalize (leb_complete (length l1) (rpo_infos.(bb))); case (leb (length l1) rpo_infos.(bb)); [idtac | simpl; trivial].
generalize (leb_complete (length l2) (rpo_infos.(bb))); case (leb (length l2) (bb rpo_infos)); simpl; [idtac | trivial].
 assert (H3:= prec_eq_status). assert (H3':= H3 symbol Prec f1 f2). assert (H4: status Prec f1 = status Prec f2). apply H3'; trivial. assert (Sf2: status Prec f2 = Lex). rewrite <- H4; trivial.
intros L2 L1; apply (@Top_eq_lex rpo_infos.(bb) f2 f1 l1 l2 Sf2). trivial. apply prec_eq_sym;
trivial.
right; split; [apply L2 | apply L1]; apply eq_refl.
clear L1 L2; destruct H' as [[H1 H2] | [[ll [t1 [l2' [Hll [H1 H2]]]]] | [ll [t1 [t2 [l1' [l2' [Hll [Ht [H' [H1 H2]]]]]]]]]]].
subst l2; destruct l1 as [ | a1 l2]; [apply False_rect; apply H1; apply eq_refl | constructor 3].
subst l1 l2; induction ll as [ | [u1 u2] ll].
simpl; constructor 3.
simpl; constructor 2.
symmetry; generalize (IHn u1 u2); rewrite (Hll _ _ (or_introl _ (eq_refl _))); intro; assumption.
apply IHll; intros; apply Hll; right; assumption.
clear H'; subst l1 l2; induction ll as [ | [u1 u2] ll].
simpl; constructor 1; generalize (IHn t1 t2); rewrite Ht; intro; assumption.
simpl; constructor 2.
symmetry; generalize (IHn u1 u2); rewrite (Hll _ _ (or_introl _ (eq_refl _))); intro; assumption.
apply IHll; intros; apply Hll; right; assumption.
clear L1 L2; destruct H' as [[H1 H2] | [[ll [t1 [l1' [Hll [H1 H2]]]]] | [ll [t1 [t2 [l1' [l2' [Hll [Ht [H' [H1 H2]]]]]]]]]]].
intros; subst l2; contradiction.
intros u u_in_l2; rewrite mem_in_eq in u_in_l2; destruct u_in_l2 as [u' [u_eq_u' u'_in_l2]].
subst l2; rewrite in_map_iff in u'_in_l2; destruct u'_in_l2 as [[u1 u2] [K1 K2]].
apply Subterm with u1.
subst l1; rewrite <- mem_or_app; left; apply in_impl_mem.
apply Eq.
rewrite in_map_iff; exists (u1,u2); split; trivial.
simpl in K1; subst u2; left; transitivity u'; trivial.
symmetry; generalize (IHn u1 u'); rewrite (Hll _ _ K2); intro; assumption.
intros u u_in_l2; rewrite mem_in_eq in u_in_l2; destruct u_in_l2 as [u' [u_eq_u' u'_in_l2]].
destruct (H' _ u'_in_l2) as [ [u1 [u1_in_l1 u'_le_u1]] | H''].
apply Subterm with u1.
apply in_impl_mem; trivial.
intros; apply Eq.
destruct u'_le_u1 as [u'_eq_u1 | u'_lt_u1].
left; transitivity u'; trivial.
symmetry; generalize (IHn u1 u'); rewrite u'_eq_u1; intro; assumption.
right; rewrite (equiv_rpo_equiv_2 _ u_eq_u'); generalize (IHn u1 u'); rewrite u'_lt_u1; intro; assumption.
rewrite (equiv_rpo_equiv_2 _ u_eq_u'); generalize (IHn (Term f1 l1) u'); rewrite H''; intro; assumption.
(* 1/9 lexico_eval (rpo_eval rpo_infos n) (Term f1 l1) (Term f1 l2) l1 l2 = Some Uncomparable *)
case (beq_nat (length l1) (length l2)
      || leb (length l1) (bb rpo_infos) && leb (length l2) (bb rpo_infos)); trivial.
(* 1/8 lexico_eval (rpo_eval rpo_infos n) (Term f1 l1) (Term f1 l2) l1 l2 = None *)
case (beq_nat (length l1) (length l2)
      || leb (length l1) (bb rpo_infos) && leb (length l2) (bb rpo_infos)); trivial.
(* 1/7 f1 has a Mul status *)
 assert (H3:= prec_eq_status). assert (H3':= H3 symbol Prec f1 f2). assert (H4: status Prec f1 = status Prec f2). apply H3'; trivial. assert (Sf2: status Prec f2 = Mul). rewrite <- H4; trivial. 
simpl; assert (H' := remove_equiv_eval_list_is_sound (equiv_eval rpo_infos n) l1 l2).
rewrite Sf1.
destruct (remove_equiv_eval_list (equiv_eval rpo_infos n) l1 l2) as [ [[ | t1' l1'] [ | t2' l2']] | ].
destruct H' as [ll [E_ll [P1 [P2 _]]]]. apply (@Eq_mul f1 f2 l1 l2 Sf1); trivial.
simpl in P1; simpl in P2. 
apply permut0_trans with (map (fun st : term * term => fst st) ll); trivial. apply equiv_equiv.
apply permut_impl with (@eq term); trivial; intros; subst; reflexivity.
apply permut0_trans with (map (fun st : term * term => snd st) ll); trivial. apply equiv_equiv.
assert (E_ll' : forall t1 t2, In (t1,t2) ll -> equiv t1 t2).
intros t1 t2 t1t2_in_ll; 
assert (H' := equiv_eval_is_sound_weak rpo_infos n t1 t2);
rewrite (E_ll t1 t2 t1t2_in_ll) in H'; apply H'; trivial.
clear E_ll P1 P2; induction ll as [ | [t1 t2] ll].
reflexivity.
simpl; rewrite <- permut0_cons.
apply IHll.
intros; apply E_ll'; right; trivial. apply equiv_equiv.
apply E_ll'; left; trivial.
symmetry; 
apply permut_impl with (@eq term); trivial; intros; subst; reflexivity.
destruct H' as [ll [E_ll [P1 [P2 _]]]].
apply Top_eq_mul; trivial.
apply (@List_mul _ t2' l2' nil l1); trivial.
reflexivity.
transitivity ((t2' :: l2') ++ (map (fun st : term * term => snd st) ll)).
apply permut_impl with (@eq term); trivial; intros; subst; reflexivity.
rewrite app_comm_cons; rewrite <- permut_app1.
transitivity (map (fun st : term * term => fst st) ll).
symmetry.
assert (E_ll' : forall t1 t2, In (t1,t2) ll -> equiv t1 t2).
intros t1 t2 t1t2_in_ll; 
assert (H' := equiv_eval_is_sound_weak rpo_infos n t1 t2);
rewrite (E_ll t1 t2 t1t2_in_ll) in H'; apply H'; trivial.
clear E_ll P1 P2; induction ll as [ | [t1 t2] ll].
reflexivity.
simpl; rewrite <- permut0_cons.
apply IHll.
intros; apply E_ll'; right; trivial. apply equiv_equiv.
apply E_ll'; left; trivial.
symmetry; 
apply permut_impl with (@eq term); trivial; intros; subst; reflexivity. apply equiv_equiv.
intros; contradiction.
destruct H' as [ll [E_ll [P1 [P2 _]]]].
apply Top_eq_mul; trivial. apply prec_eq_sym; trivial.
apply (@List_mul _ t1' l1' nil l2); trivial.
reflexivity.
transitivity ((t1' :: l1') ++ (map (fun st : term * term => fst st) ll)).
apply permut_impl with (@eq term); trivial; intros; subst; reflexivity.
rewrite app_comm_cons; rewrite <- permut_app1.
transitivity (map (fun st : term * term => snd st) ll).
assert (E_ll' : forall t1 t2, In (t1,t2) ll -> equiv t1 t2).
intros t1 t2 t1t2_in_ll; 
assert (H' := equiv_eval_is_sound_weak rpo_infos n t1 t2);
rewrite (E_ll t1 t2 t1t2_in_ll) in H'; apply H'; trivial.
clear E_ll P1 P2; induction ll as [ | [t1 t2] ll].
reflexivity.
simpl; rewrite <- permut0_cons.
apply IHll.
intros; apply E_ll'; right; trivial. apply equiv_equiv.
apply E_ll'; left; trivial.
symmetry; 
apply permut_impl with (@eq term); trivial; intros; subst; reflexivity.  apply equiv_equiv.
intros; contradiction.
assert (H'' := mult_eval_is_sound_weak (rpo_eval rpo_infos n) (t1' :: l1') (t2' :: l2')).
destruct (mult_eval (rpo_eval rpo_infos n) (t1' :: l1') (t2' :: l2')) as [ [ | | | ] | ].
contradiction.
destruct H' as [ll [E_ll [P1 [P2 _]]]].
assert (E_ll' : forall t1 t2, In (t1,t2) ll -> equiv t1 t2).
intros t1 t2 t1t2_in_ll; 
assert (H' := equiv_eval_is_sound_weak rpo_infos n t1 t2);
rewrite (E_ll t1 t2 t1t2_in_ll) in H'; apply H'; trivial.
apply Top_eq_mul; trivial.
apply (@List_mul _ t2' l2' (t1' :: l1') (map (fun st : term * term => fst st) ll)); trivial.
apply permut_impl with (@eq term); trivial; intros; subst; reflexivity.
transitivity ((t2' :: l2') ++ map (fun st : term * term => snd st) ll).
apply permut_impl with (@eq term); trivial; intros; subst; reflexivity.
rewrite app_comm_cons; rewrite <- permut_app1.
clear E_ll P1 P2; induction ll as [ | [t1 t2] ll].
reflexivity.
simpl; rewrite <- permut0_cons.
apply IHll.
intros; apply E_ll'; right; trivial. apply equiv_equiv.
symmetry; apply E_ll'; left; trivial. apply equiv_equiv.
intros u1 u1_mem_l1'.
destruct (mem_split_set _ _ equiv_bool_ok _ _ u1_mem_l1') as [u1' [k1 [k1' [u1_eq_u1' [H' _]]]]].
simpl in u1_eq_u1'; simpl in H'.
assert (u1'_in_l1' : In u1' (t1' :: l1')).
rewrite H'; apply in_or_app; right; left; trivial.
destruct (H'' _ u1'_in_l1') as [u2 [u2_in_l2' u1_lt_u2]];
exists u2; split.
apply in_impl_mem; trivial.
exact Eq.
assert (H''' := IHn u2 u1').
rewrite u1_lt_u2 in H'''.
rewrite (equiv_rpo_equiv_2 _ u1_eq_u1'); trivial.
destruct H' as [ll [E_ll [P1 [P2 _]]]].
assert (E_ll' : forall t1 t2, In (t1,t2) ll -> equiv t1 t2).
intros t1 t2 t1t2_in_ll; 
assert (H' := equiv_eval_is_sound_weak rpo_infos n t1 t2);
rewrite (E_ll t1 t2 t1t2_in_ll) in H'; apply H'; trivial.
(* destruct (equiv_swap _ equiv ll E_ll') as [ll' [E_ll'' [H1 [H2 H3]]]]. *)
apply Top_eq_mul; trivial. apply prec_eq_sym; trivial.
apply (@List_mul _ t1' l1' (t2' :: l2') (map (fun st : term * term => fst st) ll)); trivial.
transitivity ((t2' :: l2') ++ map (fun st : term * term => snd st) ll).
apply permut_impl with (@eq term); trivial; intros; subst; reflexivity.
rewrite <- permut_app1.
clear E_ll P1 P2; induction ll as [ | [t1 t2] ll].
reflexivity.
simpl; rewrite <- permut0_cons.
apply IHll.
intros; apply E_ll'; right; trivial. apply equiv_equiv.
symmetry; apply E_ll'; left; trivial. apply equiv_equiv.
apply permut_impl with (@eq term); trivial; intros; subst; reflexivity.
intros u2 u2_mem_l2'.
destruct (mem_split_set _ _ equiv_bool_ok _ _ u2_mem_l2') as [u2' [k2 [k2' [u2_eq_u2' [H' _]]]]].
simpl in u2_eq_u2'; simpl in H'.
assert (u2'_in_l2' : In u2' (t2' :: l2')).
rewrite H'; apply in_or_app; right; left; trivial.
destruct (H'' _ u2'_in_l2') as [u1 [u1_in_l1' u2_lt_u1]];
exists u1; split.
apply in_impl_mem; trivial.
exact Eq.
assert (H''' := IHn u1 u2').
rewrite u2_lt_u1 in H'''.
rewrite (equiv_rpo_equiv_2 _ u2_eq_u2'); trivial.
trivial.
trivial.
trivial.
(* 1/6 f1 < f2 *)
intro f1_lt_f2; simpl.
generalize (list_forall_option_is_sound
      (fun t : term =>
       match rpo_eval rpo_infos n t (Term f2 l2) with
       | Some Equivalent => Some false
       | Some Less_than => Some true
       | Some Greater_than => Some false
       | Some Uncomparable => Some false
       | None => None (A:=bool)
       end) l1);
destruct (list_forall_option
      (fun t : term =>
       match rpo_eval rpo_infos n t (Term f2 l2) with
       | Some Equivalent => Some false
       | Some Less_than => Some true
       | Some Greater_than => Some false
       | Some Uncomparable => Some false
       | None => None (A:=bool)
       end) l1) as [ [ | ] | ].
intros l1_lt_s2; apply Top_gt; trivial.
intros t1 t1_mem_l1;
destruct (mem_split_set _ _ equiv_bool_ok _ _ t1_mem_l1) as [t1' [k1 [k1' [t1_eq_t1' [H' _]]]]].
simpl in t1_eq_t1'; simpl in H'.
assert (t1'_in_l1 : In t1' l1).
rewrite H'; apply in_or_app; right; left; trivial.
rewrite (equiv_rpo_equiv_2 _ t1_eq_t1').
assert (H'' := l1_lt_s2 t1' t1'_in_l1).
assert (H''' := IHn t1' (Term f2 l2));
destruct (rpo_eval rpo_infos n t1' (Term f2 l2)) as [ [ | | | ] | ]; trivial; discriminate.
trivial.
trivial.
(* 1/5 f2 < f1 *)
intro f2_lt_f1; simpl.
generalize (list_forall_option_is_sound
      (fun t : term =>
       match rpo_eval rpo_infos n (Term f1 l1) t with
       | Some Equivalent => Some false
       | Some Less_than => Some false
       | Some Greater_than => Some true
       | Some Uncomparable => Some false
       | None => None (A:=bool)
       end) l2); 
destruct (list_forall_option
      (fun t : term =>
       match rpo_eval rpo_infos n (Term f1 l1) t with
       | Some Equivalent => Some false
       | Some Less_than => Some false
       | Some Greater_than => Some true
       | Some Uncomparable => Some false
       | None => None (A:=bool)
       end) l2) as [ [ | ] | ].
intros s1_gt_l2; apply Top_gt; trivial.
intros t2 t2_mem_l2; 
destruct (mem_split_set _ _ equiv_bool_ok _ _ t2_mem_l2) as [t2' [k2 [k2' [t2_eq_t2' [H' _]]]]].
simpl in t2_eq_t2'; simpl in H'.
assert (t2'_in_l2 : In t2' l2).
rewrite H'; apply in_or_app; right; left; trivial.
rewrite (equiv_rpo_equiv_2 _ t2_eq_t2').
assert (H'' := s1_gt_l2 t2' t2'_in_l2).
assert (H''' := IHn (Term f1 l1) t2');
destruct (rpo_eval rpo_infos n (Term f1 l1) t2') as [ [ | | | ] | ]; trivial; discriminate.
trivial.
trivial.
simpl; trivial.
simpl; trivial.
simpl; trivial.
trivial.
(*SLOW*)Qed.

Lemma lexico_eval_fully_evaluates :
  forall p s1 s2 l1 l2, 
  (forall t1, In t1 l1 -> p s2 t1 <> None) ->
  (forall t2, In t2 l2 -> p s1 t2 <> None) ->
  (forall t1 t2, In t1 l1 -> In t2 l2 -> p t1 t2 <> None) ->
  lexico_eval p s1 s2 l1 l2 <> None.
Proof.
intros p s1 s2 l1; induction l1 as [ | t1 l1]; intros [ | t2 l2] Es2 Es1 E;
simpl; try discriminate.
assert (H := E t1 t2 (or_introl _ (eq_refl _)) (or_introl _ (eq_refl _)));
destruct (p t1 t2) as [ [ | | | ] | ].
(* 1/5 p t1 t2 = Some Equivalent *)
apply IHl1; intros; [apply Es2 | apply Es1 | apply E]; right; trivial.
(* 1/4 p t1 t2 = Some Less_than *)
unfold term_gt_list; simpl.
generalize (list_forall_option_is_sound
      (fun t : term =>
         match p s2 t with
         | Some Equivalent => Some false
         | Some Less_than => Some false
         | Some Greater_than => Some true
         | Some Uncomparable => Some false
         | None => None
         end) l1);
destruct (list_forall_option
       (fun t : term =>
         match p s2 t with
         | Some Equivalent => Some false
         | Some Less_than => Some false
         | Some Greater_than => Some true
         | Some Uncomparable => Some false
         | None => None
         end) l1) as [ [ | ] | ].
(* 1/6 all terms in l1 are smaller than s2 *)
clear H; assert (H := Es2 t1 (or_introl _ (eq_refl _))).
destruct (p s2 t1) as [ [ | | | ] | ].
intros _; discriminate.
intros _; discriminate.
intros _; discriminate.
intros _; discriminate.
intros _; apply H; trivial.
(* 1/5 NOT all terms in l1 are smaller than s2 *)
clear H; assert (H := Es2 t1 (or_introl _ (eq_refl _))).
destruct (p s2 t1) as [ [ | | | ] | ].
intros _; discriminate.
intros _; discriminate.
intros _; discriminate.
intros _; discriminate.
intros _; apply H; trivial.
(* 1/4 at least one evaluation does not yield a result *) 
intros [u1 [u1_in_l1 pt1s2_eq_none]].
assert (H' := Es2 _ (or_intror _ u1_in_l1)). 
destruct (p s2 u1) as [ [ | | | ] | ]; trivial.
discriminate.
discriminate.
discriminate.
discriminate.
absurd (@None comp = None); trivial.
(* 1/3 p t1 t2 = Some Greater_than *)
unfold term_gt_list; simpl.
generalize (list_forall_option_is_sound
        (fun t : term =>
         match p s1 t with
         | Some Equivalent => Some false
         | Some Less_than => Some false
         | Some Greater_than => Some true
         | Some Uncomparable => Some false
         | None => None
         end) l2);
destruct (list_forall_option
        (fun t : term =>
         match p s1 t with
         | Some Equivalent => Some false
         | Some Less_than => Some false
         | Some Greater_than => Some true
         | Some Uncomparable => Some false
         | None => None
         end) l2) as [ [ | ] | ].
(* 1/5 all terms in l2 are smaller than s1 *)
clear H; assert (H := Es1 t2 (or_introl _ (eq_refl _))).
destruct (p s1 t2) as [ [ | | | ] | ].
intros _; discriminate.
intros _; discriminate.
intros _; discriminate.
intros _; discriminate.
intros _; apply H; trivial.
(* 1/4 NOT all terms in l2 are smaller than s1 *)
clear H; assert (H := Es1 t2 (or_introl _ (eq_refl _))).
destruct (p s1 t2) as [ [ | | | ] | ].
intros _; discriminate.
intros _; discriminate.
intros _; discriminate.
intros _; discriminate.
intros _; apply H; trivial.
(* 1/3 at least one evaluation does not yield a result *) 
intros [u2 [u2_in_l2 ps1u2_eq_none]].
assert (H' := Es1 _ (or_intror _ u2_in_l2)). 
destruct (p s1 u2) as [ [ | | | ] | ]; trivial.
discriminate.
discriminate.
discriminate.
discriminate.
absurd (@None comp = None); trivial.
(* 1/2 p t1 t2 = Some Uncomparable *)
discriminate.
(* 1/1 p t1 t2 = None *)
trivial.
Qed.

Lemma mult_eval_fully_evaluates :
  forall p l1 l2, 
  (forall t1 t2, In t1 l1 -> In t2 l2 -> p t1 t2 <> None) ->
  (forall t1 t2, In t1 l1 -> In t2 l2 -> p t2 t1 <> None) ->
  mult_eval p l1 l2 <> None.
Proof.
intros p [ | t1 l1] l2 E E'; unfold mult_eval, list_gt_list.
simpl; clear E; induction l2 as [ | t2 l2]; simpl.
discriminate.
destruct (list_forall_option (fun _ : term => Some false) l2) as [ [ | ] | ].
discriminate.
discriminate.
apply IHl2; intros; contradiction.
generalize (list_forall_option_is_sound
    (fun s : term =>
     list_exists_option
       (fun g : term =>
        match p g s with
        | Some Equivalent => Some false
        | Some Less_than => Some false
        | Some Greater_than => Some true
        | Some Uncomparable => Some false
        | None => None
        end) (t1 :: l1)) l2); 
destruct (list_forall_option
    (fun s : term =>
     list_exists_option
       (fun g : term =>
        match p g s with
        | Some Equivalent => Some false
        | Some Less_than => Some false
        | Some Greater_than => Some true
        | Some Uncomparable => Some false
        | None => None
        end) (t1 :: l1)) l2) as [ [ | ] | ].
intros _; discriminate.
intros _;
generalize (list_forall_option_is_sound
    (fun s : term =>
     list_exists_option
       (fun g : term =>
        match p g s with
        | Some Equivalent => Some false
        | Some Less_than => Some false
        | Some Greater_than => Some true
        | Some Uncomparable => Some false
        | None => None
        end) l2) (t1 :: l1));
destruct (list_forall_option
    (fun s : term =>
     list_exists_option
       (fun g : term =>
        match p g s with
        | Some Equivalent => Some false
        | Some Less_than => Some false
        | Some Greater_than => Some true
        | Some Uncomparable => Some false
        | None => None
        end) l2) (t1 :: l1)) as [ [ | ] | ].
intros _; discriminate.
intros _; discriminate.
intros [u1 [u1_in_l1 H]].
assert (H' := list_exists_option_is_sound
      (fun g : term =>
       match p g u1 with
       | Some Equivalent => Some false
       | Some Less_than => Some false
       | Some Greater_than => Some true
       | Some Uncomparable => Some false
       | None => None
       end) l2); rewrite H in H'. 
destruct H' as [ [u2 [u2_in_l2 pu1u2_eq_none]] _].
assert (H' := E' u1 u2 u1_in_l1 u2_in_l2);
destruct (p u2 u1) as [ [ | | | ] | ]; trivial; discriminate.
intros [u2 [u2_in_l2 H]].
assert (H' := list_exists_option_is_sound
      (fun g : term =>
       match p g u2 with
       | Some Equivalent => Some false
       | Some Less_than => Some false
       | Some Greater_than => Some true
       | Some Uncomparable => Some false
       | None => None
       end) (t1 :: l1)); rewrite H in H'. 
destruct H' as [ [u1 [u1_in_l1 pu1u2_eq_none]] _].
assert (H' := E u1 u2 u1_in_l1 u2_in_l2);
destruct (p u1 u2) as [ [ | | | ] | ]; trivial; discriminate.
Qed.

Lemma rpo_eval_terminates :
  forall rpo_infos n t1 t2, size t1 + size t2 <= n -> rpo_eval rpo_infos n t1 t2 <> None.
Proof.
intros rpo_infos n; induction n as [ | n].
(* Base case *)
intros t1 t2 St1; 
absurd (1 <= 0); auto with arith; 
apply le_trans with (size t1 + size t2); trivial;
apply le_trans with (1 + size t2);
[apply le_plus_l | apply plus_le_compat_r; apply size_ge_one].
(* Induction step *)
intros t1 t2 St; rewrite rpo_eval_equation.
case (mem_bool eq_tt_bool (t1, t2) (rpo_l rpo_infos)).
intro;discriminate.
case (mem_bool eq_tt_bool (t2, t1) (rpo_l rpo_infos)).
intro;discriminate.
case (mem_bool eq_tt_bool (t1, t2) (equiv_l rpo_infos)).
intro;discriminate.
case (mem_bool eq_tt_bool (t2, t1) (equiv_l rpo_infos)).
intro;discriminate.
assert (T := @equiv_eval_terminates rpo_infos (S n) t1 t2 St); 
destruct (equiv_eval rpo_infos (S n) t1 t2) as [ [ | ] | ]; try discriminate.
destruct t1 as [v1 | f1 l1]; destruct t2 as [v2 | f2 l2].
discriminate.
destruct (var_in_term_list v1 l2); discriminate.
destruct (var_in_term_list v2 l1); discriminate.
generalize (list_exists_option_is_sound 
  (fun t : term =>
      match rpo_eval rpo_infos n t (Term f2 l2) with
      | Some Equivalent => Some true
      | Some Less_than => Some false
      | Some Greater_than => Some true
      | Some Uncomparable => Some false
      | None => None
      end) l1);
destruct (list_exists_option
  (fun t : term =>
      match rpo_eval rpo_infos n t (Term f2 l2) with
      | Some Equivalent => Some true
      | Some Less_than => Some false
      | Some Greater_than => Some true
      | Some Uncomparable => Some false
      | None => None
      end) l1) as [ [ | ] | ].
intros _; simpl; discriminate.
intros _.
generalize (list_exists_option_is_sound 
  (fun t : term =>
          match rpo_eval rpo_infos n (Term f1 l1) t with
          | Some Equivalent => Some true
          | Some Less_than => Some true
          | Some Greater_than => Some false
          | Some Uncomparable => Some false
          | None => None
          end) l2);
destruct (list_exists_option
        (fun t : term =>
          match rpo_eval rpo_infos n (Term f1 l1) t with
          | Some Equivalent => Some true
          | Some Less_than => Some true
          | Some Greater_than => Some false
          | Some Uncomparable => Some false
          | None => None
          end) l2) as [ [ | ] | ].
intros _; simpl; discriminate.
intros _; simpl; destruct (prec_eval f1 f2); try discriminate.
destruct (status Prec f1).
case (beq_nat (length l1) (length l2)
    || leb (length l1) (bb rpo_infos) && leb (length l2) (bb rpo_infos)).
apply lexico_eval_fully_evaluates.
intros t1 t1_in_l1; apply IHn.
rewrite plus_comm.
apply le_S_n; refine (le_trans _ _ _ _ St).
replace (S (size t1 + size (Term f2 l2))) with 
                (S (size t1) + size (Term f2 l2)); trivial.
apply plus_le_compat_r; apply size_direct_subterm; trivial.
intros t2 t2_in_l2; apply IHn.
apply le_S_n; refine (le_trans _ _ _ _ St); rewrite plus_comm;
replace (S (size t2 + size (Term f1 l1))) with 
                (S (size t2) + size (Term f1 l1)); trivial; rewrite plus_comm;
apply plus_le_compat_l; apply size_direct_subterm; trivial.
intros t1 t2 t1_in_l1 t2_in_l2; apply IHn.
apply le_S_n; refine (le_trans _ _ _ _ St);
replace (S (size t1 + size t2)) with  (S (size t1) + size t2); trivial;
apply plus_le_compat.
apply size_direct_subterm; trivial.
apply lt_le_weak; apply size_direct_subterm; trivial.
discriminate.
generalize (remove_equiv_eval_list_is_sound (equiv_eval rpo_infos n) l1 l2);
destruct (remove_equiv_eval_list (equiv_eval rpo_infos n) l1 l2) as [ [[ | t1' l1'] [ | t2' l2']] | ].
intros _; discriminate.
intros _; discriminate.
intros _; discriminate.
intros [ll [H [P1 [P2 H']]]]. 
apply mult_eval_fully_evaluates.
intros t1 t2 t1_in_l1' t2_in_l2'; apply IHn.
apply le_S_n; refine (le_trans _ _ _ _ St);
replace (S (size t1 + size t2)) with  (S (size t1) + size t2); trivial;
apply plus_le_compat.
apply size_direct_subterm; simpl;
rewrite (in_permut_in P1); apply in_or_app; left; trivial.
apply lt_le_weak; apply size_direct_subterm; simpl;
rewrite (in_permut_in P2); apply in_or_app; left; trivial.
intros t1 t2 t1_in_l1' t2_in_l2'; apply IHn.
apply le_S_n; refine (le_trans _ _ _ _ St);
replace (S (size t2 + size t1)) with  (S (size t2) + size t1); trivial.
rewrite plus_comm; apply plus_le_compat.
apply lt_le_weak; apply size_direct_subterm; simpl;
rewrite (in_permut_in P1); apply in_or_app; left; trivial.
apply size_direct_subterm; simpl;
rewrite (in_permut_in P2); apply in_or_app; left; trivial.
intros [t1 [t2 [t1_in_l1 [t2_in_l2 H]]]];
assert (H' := @equiv_eval_terminates rpo_infos n t1 t2);
destruct (equiv_eval rpo_infos n t1 t2) as [ [ | ] | ].
discriminate.
discriminate.
intros _; apply H'; trivial.
apply le_S_n; refine (le_trans _ _ _ _ St);
replace (S (size t1 + size t2)) with  (S (size t1) + size t2); trivial;
apply plus_le_compat.
apply size_direct_subterm; trivial.
apply lt_le_weak; apply size_direct_subterm; trivial.
generalize (list_forall_option_is_sound
    (fun t : term =>
     match rpo_eval rpo_infos n t (Term f2 l2) with
     | Some Equivalent => Some false
     | Some Less_than => Some true
     | Some Greater_than => Some false
     | Some Uncomparable => Some false
     | None => None (A:=bool)
     end) l1);
destruct (list_forall_option
    (fun t : term =>
     match rpo_eval rpo_infos n t (Term f2 l2) with
     | Some Equivalent => Some false
     | Some Less_than => Some true
     | Some Greater_than => Some false
     | Some Uncomparable => Some false
     | None => None (A:=bool)
     end) l1) as [ [ | ] | ].
intros _; discriminate.
intros _; discriminate.
intros [u1 [u1_in_l1 H]]; assert (H' := IHn u1 (Term f2 l2)); 
destruct (rpo_eval rpo_infos n u1 (Term f2 l2)) as [ [ | | | ] | ].
discriminate.
discriminate.
discriminate.
discriminate.
apply H'.
apply le_S_n; refine (le_trans _ _ _ _ St);
replace (S (size u1 + size (Term f2 l2))) with 
                (S (size u1) + size (Term f2 l2)); trivial;
apply plus_le_compat_r; apply size_direct_subterm; trivial.
generalize  (list_forall_option_is_sound
    (fun t : term =>
     match rpo_eval rpo_infos n (Term f1 l1) t with
     | Some Equivalent => Some false
     | Some Less_than => Some false
     | Some Greater_than => Some true
     | Some Uncomparable => Some false
     | None => None (A:=bool)
     end) l2);
destruct (list_forall_option
    (fun t : term =>
     match rpo_eval rpo_infos n (Term f1 l1) t with
     | Some Equivalent => Some false
     | Some Less_than => Some false
     | Some Greater_than => Some true
     | Some Uncomparable => Some false
     | None => None (A:=bool)
     end) l2) as [ [ | ] | ].
intros _; discriminate.
intros _; discriminate.
intros [u2 [u2_in_l2 H]]; assert (H' := IHn (Term f1 l1) u2); 
destruct (rpo_eval rpo_infos n (Term f1 l1) u2) as [ [ | | | ] | ].
discriminate.
discriminate.
discriminate.
discriminate.
apply H'.
apply le_S_n; refine (le_trans _ _ _ _ St); rewrite plus_comm;
replace (S (size u2 + size (Term f1 l1))) with 
                (S (size u2) + size (Term f1 l1)); trivial; rewrite plus_comm;
apply plus_le_compat_l; apply size_direct_subterm; trivial.
intros [[u2 [u2_in_l2 H]] _]; assert (H' := IHn (Term f1 l1) u2); 
destruct (rpo_eval rpo_infos n (Term f1 l1) u2) as [ [ | | | ] | ].
discriminate.
discriminate.
discriminate.
discriminate.
apply H'.
apply le_S_n; refine (le_trans _ _ _ _ St); rewrite plus_comm;
replace (S (size u2 + size (Term f1 l1))) with 
                (S (size u2) + size (Term f1 l1)); trivial; rewrite plus_comm;
apply plus_le_compat_l; apply size_direct_subterm; trivial.
intros [[u1 [u1_in_l1 H]] _]; assert (H' := IHn u1 (Term f2 l2)); 
destruct (rpo_eval rpo_infos n u1 (Term f2 l2)) as [ [ | | | ] | ].
discriminate.
discriminate.
discriminate.
discriminate.
apply H'.
apply le_S_n; refine (le_trans _ _ _ _ St);
replace (S (size u1 + size (Term f2 l2))) with 
                (S (size u1) + size (Term f2 l2)); trivial;
apply plus_le_compat_r; apply size_direct_subterm; trivial.
intros _; apply T; trivial.
Qed.

Lemma rpo_eval_is_complete_equivalent :
  forall rpo_infos n t1 t2, size t1 + size t2 <= n -> equiv t1 t2 ->
        rpo_eval rpo_infos n t1 t2 = Some Equivalent.
Proof.
intros rpo_infos n t1 t2 St t1_eq_t2; 
rewrite rpo_eval_equation.
case_eq (mem_bool eq_tt_bool (t1, t2) (rpo_l rpo_infos)).
intro abs.
generalize (find_is_sound (rpo rpo_infos.(bb)) _ (rpo_l_valid rpo_infos) _ _ abs).
intro h;absurd (rpo rpo_infos.(bb) t1 t1).
intro;apply rpo_antirefl with (1:=H).
rewrite <- (equiv_rpo_equiv_1 _ t1_eq_t2) in h. assumption.
intro h1.
case_eq (mem_bool eq_tt_bool (t2, t1) (rpo_l rpo_infos)).
intro abs.
generalize (find_is_sound (rpo rpo_infos.(bb)) _ (rpo_l_valid rpo_infos) _ _ abs).
intro h;absurd (rpo rpo_infos.(bb) t2 t2).
intro;apply rpo_antirefl with (1:=H).
rewrite (equiv_rpo_equiv_1 _ t1_eq_t2) in h. assumption.
intro h2.
case_eq (mem_bool eq_tt_bool (t1, t2) (equiv_l rpo_infos)).
trivial.
intro h3.
case_eq (mem_bool eq_tt_bool (t2, t1) (equiv_l rpo_infos)).
trivial.
intro h4.

assert (H := @equiv_eval_is_sound  rpo_infos _ _ _ St).

destruct (equiv_eval rpo_infos n t1 t2) as [ [ | ] | ].
trivial.
absurd (equiv t1 t2); trivial.
contradiction.
Qed.

Lemma var_case2 : 
  forall n v f l, rpo n (Var v) (Term f l) -> var_in_term_list v l = true .
Proof.
intros m v f l v_lt_t; 
inversion v_lt_t as [ f2 l2 u s s_in_l v_le_s | | | ]; subst.
generalize s s_in_l v_le_s; clear v_lt_t s s_in_l v_le_s; 
pattern l; apply (list_rec3 size); clear l.
intro n; induction n as [ | n]; intros [ | t l] Sl s s_in_l v_le_s.
contradiction.
simpl in Sl; absurd (1 <= 0); auto with arith.
refine (le_trans _ _ _ _ Sl); apply le_trans with (size t).
apply size_ge_one.
apply le_plus_l.
contradiction.
simpl in s_in_l; destruct s_in_l as [s_eq_t | s_in_l].
rewrite (@equiv_rpo_equiv_3 _ _ _ s_eq_t) in v_le_s.
inversion v_le_s; subst.
inversion H; subst;
rewrite var_in_term_list_equation; simpl;
rewrite eq_var_bool_refl; trivial.
inversion H as [g k u1 s' s'_in_k v_le_s' | | |]; subst;
rewrite var_in_term_list_equation; simpl.
assert (Sk : list_size size k <= n).
apply le_S_n; refine (le_trans _ _ _ _ Sl); simpl; apply le_n_S;
rewrite (list_size_fold size k); auto with arith.
rewrite (IHn k Sk s' s'_in_k v_le_s'); simpl; trivial.
assert (Sl' : list_size size l <= n).
apply le_S_n; refine (le_trans _ _ _ _ Sl); simpl;
apply (plus_le_compat_r 1 (size t) (list_size size l));
apply size_ge_one.
rewrite var_in_term_list_equation; 
rewrite (IHn l Sl' s s_in_l v_le_s); destruct t as [v' | g k].
case (X.eq_bool v v'); trivial.
case (var_in_term_list v k); trivial.
Qed.

Lemma rpo_eval_is_complete_less_greater :
  forall rpo_infos n t1 t2, size t1 + size t2 <= n -> 
        rpo rpo_infos.(bb) t1 t2 ->
        rpo_eval rpo_infos n t1 t2 = Some Less_than /\
        rpo_eval rpo_infos n t2 t1 = Some Greater_than.
Proof.
intros rpo_infos n; induction n as [ | n]; intros t1 t2 St t1_lt_t2. 
absurd (1 <= 0); auto with arith; 
apply le_trans with (size t1 + size t2); trivial;
apply le_trans with (1 + size t2);
[apply le_plus_l | apply plus_le_compat_r; apply size_ge_one].
assert (TE := @equiv_eval_terminates rpo_infos _ _ _ St);
assert (R := rpo_eval_is_sound_weak rpo_infos (S n) t1 t2);
assert (T := @rpo_eval_terminates rpo_infos (S n) t1 t2 St).
rewrite plus_comm in St;
assert (TE' := @equiv_eval_terminates rpo_infos _ _ _ St);
assert (R' := rpo_eval_is_sound_weak rpo_infos (S n) t2 t1);
assert (T' := @rpo_eval_terminates rpo_infos (S n) t2 t1 St).
do 2 rewrite rpo_eval_equation;
rewrite rpo_eval_equation in R; 
rewrite rpo_eval_equation in T;
rewrite rpo_eval_equation in R'; 
rewrite rpo_eval_equation in T'.
revert R T R' T'.
(*SLOW*)case_eq (mem_bool eq_tt_bool (t1, t2) (rpo_l rpo_infos)); intro Heq_1;
case_eq (mem_bool eq_tt_bool (t2, t1) (rpo_l rpo_infos)); intro Heq_2;
case_eq (mem_bool eq_tt_bool (t1, t2) (equiv_l rpo_infos)); intro Heq_3;
case_eq (mem_bool eq_tt_bool (t2, t1) (equiv_l rpo_infos)); intro Heq_4; intros R T R' T'; try
(absurd (rpo rpo_infos.(bb) t1 t1);[
intro; apply (@rpo_antirefl rpo_infos.(bb) t1); trivial|
apply rpo_trans with t2;assumption]); try (solve[intuition]);
try (absurd (rpo rpo_infos.(bb) t1 t1);
[intro; apply (@rpo_antirefl rpo_infos.(bb) t1); trivial |
rewrite (@equiv_rpo_equiv_1 _ _ _ R') in t1_lt_t2; trivial]).
clear Heq_1 Heq_2 Heq_3 Heq_4.
(*SLOW*)destruct (equiv_eval rpo_infos (S n) t1 t2) as [ [ | ] | ];
destruct (equiv_eval rpo_infos (S n) t2 t1) as [ [ | ] | ];
try (absurd (rpo rpo_infos.(bb) t1 t1); [
intro; apply (@rpo_antirefl rpo_infos.(bb) t1); trivial |
rewrite <- (equiv_rpo_equiv_1 _ R) in t1_lt_t2; trivial]); try solve[intuition];
try (absurd (rpo rpo_infos.(bb) t1 t1);
[intro; apply (@rpo_antirefl rpo_infos.(bb) t1); trivial|
rewrite (equiv_rpo_equiv_1 _ R') in t1_lt_t2; trivial]).
clear TE TE'.
destruct t1 as [v1 | f1 l1]; destruct t2 as [v2 | f2 l2]. 
inversion t1_lt_t2.
rewrite (@var_case2 _ _ _ _ t1_lt_t2); split; trivial.
inversion t1_lt_t2.
assert (Sl : forall t1 t2, In t1 l1 -> In t2 l2 -> size t1 + size t2 <= n).
intros t1 t2 t1_in_l1 t2_in_l2; apply le_S_n; refine (le_trans _ _ _ _ St);
replace (S (size t1 + size t2)) with (S (size t1) + size t2); trivial;
rewrite plus_comm; apply plus_le_compat.
apply lt_le_weak; apply size_direct_subterm; trivial.
apply size_direct_subterm; trivial.
assert (IHl1l2 : forall t1 t2, In t1 l1 -> In t2 l2 -> rpo rpo_infos.(bb) t1 t2 ->
     rpo_eval rpo_infos n t1 t2 = Some Less_than /\
      rpo_eval rpo_infos n t2 t1 = Some Greater_than).
intros; apply IHn; trivial.
apply Sl; trivial.
assert (IHl2l1 : forall t1 t2, In t1 l1 -> In t2 l2 -> rpo rpo_infos.(bb) t2 t1 ->
     rpo_eval rpo_infos n t2 t1 = Some Less_than /\
      rpo_eval rpo_infos n t1 t2 = Some Greater_than).
intros; apply IHn; trivial.
rewrite plus_comm; apply Sl; trivial.
assert (IHl1s2 : forall t1, In t1 l1 -> rpo rpo_infos.(bb) t1 (Term f2 l2) ->
     rpo_eval rpo_infos n t1 (Term f2 l2) = Some Less_than /\
      rpo_eval rpo_infos n (Term f2 l2) t1 = Some Greater_than).
intros; apply IHn; trivial.
apply le_S_n; refine (le_trans _ _ _ _ St);
replace (S (size t1 + size (Term f2 l2))) with (S (size t1) + size (Term f2 l2)); trivial;
rewrite plus_comm; apply plus_le_compat_l.
apply size_direct_subterm; trivial.
assert (IHs2l1 : forall t1, In t1 l1 -> rpo rpo_infos.(bb) (Term f2 l2) t1 ->
     rpo_eval rpo_infos n (Term f2 l2) t1 = Some Less_than /\
      rpo_eval rpo_infos n t1 (Term f2 l2) = Some Greater_than).
intros; apply IHn; trivial.
rewrite plus_comm; apply le_S_n; refine (le_trans _ _ _ _ St);
replace (S (size t1 + size (Term f2 l2))) with (S (size t1) + size (Term f2 l2)); trivial;
rewrite plus_comm; apply plus_le_compat_l.
apply size_direct_subterm; trivial.
assert (IHs1l2 : forall t2, In t2 l2 -> rpo rpo_infos.(bb) (Term f1 l1) t2 ->
     rpo_eval rpo_infos n (Term f1 l1) t2 = Some Less_than /\
      rpo_eval rpo_infos n t2 (Term f1 l1) = Some Greater_than).
intros; apply IHn; trivial.
rewrite plus_comm;
apply le_S_n; refine (le_trans _ _ _ _ St);
replace (S (size t2 + size (Term f1 l1))) with (S (size t2) + size (Term f1 l1)); trivial;
apply plus_le_compat_r.
apply size_direct_subterm; trivial.
assert (IHl2s1 : forall t2, In t2 l2 -> rpo rpo_infos.(bb) t2 (Term f1 l1) ->
     rpo_eval rpo_infos n t2 (Term f1 l1) = Some Less_than /\
      rpo_eval rpo_infos n (Term f1 l1) t2 = Some Greater_than).
intros; apply IHn; trivial.
apply le_S_n; refine (le_trans _ _ _ _ St);
replace (S (size t2 + size (Term f1 l1))) with (S (size t2) + size (Term f1 l1)); trivial;
apply plus_le_compat_r.
apply size_direct_subterm; trivial.
inversion t1_lt_t2 as
[ f2' l2' u1 s2 s2_in_l2 u1_le_s2
| f2' f1' l2' l1' f1_lt_f2 H
| f g l2' l1' Sf Sg f_eq_g L l1_lt_l2 H
| f g l2' l1' Sf Sg f_eq_g l1_lt_l2]; subst.
(* 1/4 Subterm *)
split.
destruct (list_exists_option
           (fun t : term =>
            match rpo_eval rpo_infos n t (Term f2 l2) with
            | Some Equivalent => Some true
            | Some Less_than => Some false
            | Some Greater_than => Some true
            | Some Uncomparable => Some false
            | None => None (A:=bool)
            end) l1) as [ [ | ] | ].
simpl in R; 
destruct (rpo_closure rpo_infos.(bb) (Term f1 l1) (Term f2 l2) (Term f2 l2)) as [_ [Antisym _]].
apply False_rect; apply Antisym; trivial.
assert (t1_lt_l2 : list_exists_option
          (fun t : term =>
           match rpo_eval rpo_infos n (Term f1 l1) t with
           | Some Equivalent => Some true
           | Some Less_than => Some true
           | Some Greater_than => Some false
           | Some Uncomparable => Some false
           | None => None (A:=bool)
           end) l2 = Some true).
apply list_exists_option_is_complete_true.
destruct (mem_split_set _ _ equiv_bool_ok _ _ s2_in_l2) as [s2' [l2' [l2'' [s2_eq_s2' [H _]]]]].
simpl in s2_eq_s2'; simpl in H.
assert (s2'_in_l2 : In s2' l2).
subst l2; apply in_or_app; right; left; trivial.
exists s2'; split; trivial.
rewrite (equiv_rpo_equiv_3  _ s2_eq_s2') in u1_le_s2.
inversion u1_le_s2; subst.
rewrite (@rpo_eval_is_complete_equivalent rpo_infos n (Term f1 l1) s2'); trivial.
rewrite plus_comm;
apply le_S_n; refine (le_trans _ _ _ _ St);
replace (S (size s2' + size (Term f1 l1))) with (S (size s2') + size (Term f1 l1)); trivial;
apply plus_le_compat_r.
apply size_direct_subterm; simpl; trivial.
destruct (IHs1l2 s2' s2'_in_l2 H0) as [H1 _]; rewrite H1; trivial.
rewrite t1_lt_l2; simpl; trivial.
absurd (@None comp = None); trivial.
assert (l2_gt_t1 : list_exists_option
            (fun t : term =>
             match rpo_eval rpo_infos n t (Term f1 l1) with
             | Some Equivalent => Some true
             | Some Less_than => Some false
             | Some Greater_than => Some true
             | Some Uncomparable => Some false
             | None => None (A:=bool)
             end) l2 = Some true).
apply list_exists_option_is_complete_true.
destruct (mem_split_set _ _ equiv_bool_ok _ _ s2_in_l2) as [s2' [l2' [l2'' [s2_eq_s2' [H _]]]]].
simpl in s2_eq_s2'; simpl in H.
assert (s2'_in_l2 : In s2' l2).
subst l2; apply in_or_app; right; left; trivial.
exists s2'; split; trivial.
inversion u1_le_s2; subst.
rewrite (@rpo_eval_is_complete_equivalent rpo_infos n s2' (Term f1 l1)); trivial.
apply le_S_n; refine (le_trans _ _ _ _ St);
replace (S (size s2' + size (Term f1 l1))) with (S (size s2') + size (Term f1 l1)); trivial;
apply plus_le_compat_r.
apply size_direct_subterm; trivial.
symmetry; transitivity s2; trivial.
rewrite (equiv_rpo_equiv_1 _ s2_eq_s2') in H0.
destruct (IHs1l2 s2' s2'_in_l2 H0) as [_ H2]; rewrite H2; trivial.
rewrite l2_gt_t1; simpl; trivial.
(* 1/3 Top_gt *)
split; [clear R' T' | clear R T].
destruct (list_exists_option
           (fun t : term =>
            match rpo_eval rpo_infos n t (Term f2 l2) with
            | Some Equivalent => Some true
            | Some Less_than => Some false
            | Some Greater_than => Some true
            | Some Uncomparable => Some false
            | None => None (A:=bool)
            end) l1) as [ [ | ] | ].
simpl in R.
destruct (rpo_closure rpo_infos.(bb) (Term f1 l1) (Term f2 l2) (Term f2 l2)) as [_ [Antisym _]].
apply False_rect; apply Antisym; trivial.
destruct (list_exists_option
               (fun t : term =>
                match rpo_eval rpo_infos n (Term f1 l1) t with
                | Some Equivalent => Some true
                | Some Less_than => Some true
                | Some Greater_than => Some false
                | Some Uncomparable => Some false
                | None => None (A:=bool)
                end) l2) as [ [ | ] | ].
trivial.
generalize (prec_eval_is_sound f1 f2); destruct (prec_eval f1 f2). 
intro. apply False_rect; apply (prec_antisym Prec  f2); trivial. assert (H5: False). apply prec_not_prec_eq with symbol Prec f1 f2; trivial. contradict H5.
intros _; assert (H' : list_forall_option
    (fun t : term =>
     match rpo_eval rpo_infos n t (Term f2 l2) with
     | Some Equivalent => Some false
     | Some Less_than => Some true
     | Some Greater_than => Some false
     | Some Uncomparable => Some false
     | None => None (A:=bool)
     end) l1 = Some true).
apply list_forall_option_is_complete_true.
intros u1 u1_in_l1; destruct (IHl1s2 u1 u1_in_l1) as [H1 _].
apply H; apply in_impl_mem; trivial.
exact Eq.
rewrite H1; trivial.
rewrite H'; trivial.
intro f2_lt_f1; apply False_rect; apply (prec_antisym Prec f1); apply prec_transitive with f2; trivial.
intros [_ [not_f1_lt_f2 _]]; absurd (prec Prec f1 f2); trivial.
absurd (@None comp = None); trivial.
absurd (@None comp = None); trivial.
destruct (list_exists_option
             (fun t : term =>
             match rpo_eval rpo_infos n t (Term f1 l1) with
             | Some Equivalent => Some true
             | Some Less_than => Some false
             | Some Greater_than => Some true
             | Some Uncomparable => Some false
             | None => None (A:=bool)
             end) l2) as [ [ | ] | ].
trivial.
destruct (list_exists_option
         (fun t : term =>
          match rpo_eval rpo_infos n (Term f2 l2) t with
          | Some Equivalent => Some true
          | Some Less_than => Some true
          | Some Greater_than => Some false
          | Some Uncomparable => Some false
          | None => None (A:=bool)
          end) l1) as [ [ | ] | ].
simpl in R'.
destruct (rpo_closure rpo_infos.(bb) (Term f1 l1) (Term f2 l2) (Term f2 l2)) as [_ [Antisym _]].
apply False_rect; apply Antisym; trivial.
generalize (prec_eval_is_sound f2 f1); destruct (prec_eval f2 f1).
intro; apply False_rect; apply (prec_antisym Prec f1); trivial.  assert (H5: False). apply prec_not_prec_eq with symbol Prec f1 f2; trivial. apply prec_eq_sym; trivial. contradict H5.
intro f2_lt_f1; apply False_rect; apply (prec_antisym Prec f1); apply prec_transitive with f2; trivial.
intros _; assert (H' : list_forall_option
    (fun t : term =>
     match rpo_eval rpo_infos n (Term f2 l2) t with
     | Some Equivalent => Some false
     | Some Less_than => Some false
     | Some Greater_than => Some true
     | Some Uncomparable => Some false
     | None => None (A:=bool)
     end) l1 = Some true).
apply list_forall_option_is_complete_true.
intros u1 u1_in_l1; destruct (IHl1s2 u1 u1_in_l1) as [_ H2].
apply H; apply in_impl_mem; trivial.
exact Eq.
rewrite H2; trivial.
rewrite H'; trivial.
intros [_ [_ not_f1_lt_f2]]; absurd (prec Prec f1 f2); trivial.
absurd (@None comp = None); trivial.
absurd (@None comp = None); trivial.
(* 1/2 @Top_eq_lex *)
split; [clear R' T' | clear R T].
case_eq (beq_nat (length l1) (length l2)
    || leb (length l1) (bb rpo_infos) && leb (length l2) (bb rpo_infos)).
clear L; intros L; rewrite L in R, T; clear L.
set (s1 := Term f1 l1) in *; clearbody s1.
set (s2 := Term f2 l2) in *; clearbody s2.
destruct (list_exists_option
     (fun t : term =>
      match rpo_eval rpo_infos n t s2 with
      | Some Equivalent => Some true
      | Some Less_than => Some false
      | Some Greater_than => Some true
      | Some Uncomparable => Some false
      | None => None (A:=bool)
      end) l1) as [ [ | ] | ].
simpl in R.
destruct (rpo_closure rpo_infos.(bb) s1 s2 s2) as [_ [Antisym _]].
apply False_rect; apply Antisym; trivial.
destruct (list_exists_option
         (fun t : term =>
          match rpo_eval rpo_infos n s1 t with
          | Some Equivalent => Some true
          | Some Less_than => Some true
          | Some Greater_than => Some false
          | Some Uncomparable => Some false
          | None => None (A:=bool)
          end) l2) as [ [ | ] | ].
trivial.
simpl; generalize (prec_eval_is_sound f1 f2); destruct (prec_eval f1 f2).
intros _; rewrite Sf; rewrite Sf in R; rewrite Sf in T; simpl in R; simpl in T.
revert t1_lt_t2 H St IHl1l2 IHl2l1 IHl1s2 IHs2l1 IHs1l2 IHl2s1 R T l1_lt_l2 Sl.
clear; revert s1 s2 l2; induction l1 as [ | t1 l1]; intros s1 s2 [ | t2 l2]; intros.
inversion l1_lt_l2.
apply eq_refl.
inversion l1_lt_l2.
inversion l1_lt_l2; subst.
simpl; rewrite (proj1 (IHl1l2 _ _ (or_introl _ (eq_refl _)) (or_introl _ (eq_refl _)) H1)).
unfold term_gt_list.
assert (H' : list_forall_option
    (fun t : term =>
     match rpo_eval rpo_infos n s2 t with
     | Some Equivalent => Some false
     | Some Less_than => Some false
     | Some Greater_than => Some true
     | Some Uncomparable => Some false
     | None => None
     end) (t1 :: l1) = Some true).
apply list_forall_option_is_complete_true.
intros u1 u1_in_t1l1.
assert (u1_lt_s2 : rpo rpo_infos.(bb) u1 s2).
apply H; apply in_impl_mem; trivial; exact Eq.
rewrite (proj2 (IHl1s2 _ u1_in_t1l1 u1_lt_s2)); apply eq_refl.
rewrite H'; apply eq_refl.
simpl.
assert (H' := @rpo_eval_is_complete_equivalent rpo_infos n t1 t2).
generalize (H' (Sl _ _ (or_introl _ (eq_refl _))
                        (or_introl _ (eq_refl _))) H3);
clear H'; intro H'; rewrite H'.
apply IHl1; trivial.
intros; apply H; right; assumption.
intros; apply IHl1l2; trivial; right; assumption.
intros; apply IHl2l1; trivial; right; assumption.
intros; apply IHl1s2; trivial; right; assumption.
intros; apply IHs2l1; trivial; right; assumption.
intros; apply IHs1l2; trivial; right; assumption.
intros; apply IHl2s1; trivial; right; assumption.
simpl in R; rewrite H' in R; assumption.
simpl in T; rewrite H' in T; assumption.
intros; apply Sl; right; assumption.
intro. assert (H4: False). apply prec_not_prec_eq with symbol Prec f1 f2; trivial. contradict H4. 
intro. assert (H4: False). apply prec_not_prec_eq with symbol Prec f2 f1; trivial. apply prec_eq_sym; trivial. contradict H4. 
intros [f2_diff_f2 _]; absurd (f2 = f2); trivial.
simpl in T; absurd (@None comp = None); trivial.
simpl in T; absurd (@None comp = None); trivial.
contradict f2_diff_f2; trivial. 
simpl in T; absurd (@None comp = None); trivial.
simpl in T; absurd (@None comp = None); trivial.
destruct L as [L | [L1 L2]].
rewrite L; rewrite <- beq_nat_refl; intro; discriminate.
rewrite (leb_correct _ _ L1); rewrite (leb_correct _ _ L2); rewrite orb_true_r; intro; discriminate.
case_eq (beq_nat (length l2) (length l1)
    || leb (length l2) (bb rpo_infos) && leb (length l1) (bb rpo_infos)).
clear L; intros L; rewrite L in R', T'; clear L.
set (s1 := Term f1 l1) in *; clearbody s1.
set (s2 := Term f2 l2) in *; clearbody s2.
destruct (list_exists_option
     (fun t : term =>
      match rpo_eval rpo_infos n t s1 with
      | Some Equivalent => Some true
      | Some Less_than => Some false
      | Some Greater_than => Some true
      | Some Uncomparable => Some false
      | None => None (A:=bool)
      end) l2) as [ [ | ] | ].
trivial.
destruct (list_exists_option
         (fun t : term =>
          match rpo_eval rpo_infos n s2 t with
          | Some Equivalent => Some true
          | Some Less_than => Some true
          | Some Greater_than => Some false
          | Some Uncomparable => Some false
          | None => None (A:=bool)
          end) l1) as [ [ | ] | ].
simpl in R'.
destruct (rpo_closure rpo_infos.(bb) s2 s1 s2) as [_ [Antisym _]].
apply False_rect; apply Antisym; trivial.
simpl; generalize (prec_eval_is_sound f2 f1); destruct (prec_eval f2 f1).
intros _; rewrite Sg; rewrite Sg in R'; rewrite Sg in T'; simpl in R'; simpl in T'.
revert t1_lt_t2 H St IHl1l2 IHl2l1 IHl1s2 IHs2l1 IHs1l2 IHl2s1 R' T' l1_lt_l2 Sl.
clear; revert s1 s2 l1; induction l2 as [ | t2 l2]; intros s1 s2 [ | t1 l1]; intros.
inversion l1_lt_l2.
inversion l1_lt_l2.
apply eq_refl.
inversion l1_lt_l2; subst.
simpl; rewrite (proj2 (IHl1l2 _ _ (or_introl _ (eq_refl _)) (or_introl _ (eq_refl _)) H1)).
unfold term_gt_list.
assert (H' : list_forall_option
    (fun t : term =>
     match rpo_eval rpo_infos n s2 t with
     | Some Equivalent => Some false
     | Some Less_than => Some false
     | Some Greater_than => Some true
     | Some Uncomparable => Some false
     | None => None
     end) (t1 :: l1) = Some true).
apply list_forall_option_is_complete_true.
intros u1 u1_in_t1l1.
assert (u1_lt_s2 : rpo rpo_infos.(bb) u1 s2).
apply H; apply in_impl_mem; trivial; exact Eq.
rewrite (proj2 (IHl1s2 _ u1_in_t1l1 u1_lt_s2)); apply eq_refl.
rewrite H'; apply eq_refl.
simpl.
assert (H' := @rpo_eval_is_complete_equivalent rpo_infos n t2 t1).
rewrite plus_comm in H'; generalize (H' (Sl _ _ (or_introl _ (eq_refl _))
                        (or_introl _ (eq_refl _))) (@Equivalence_Symmetric _ _ equiv_equiv _ _ H3));
clear H'; intro H'; rewrite H'.
apply IHl2; trivial.
intros; apply H; right; assumption.
intros; apply IHl1l2; trivial; right; assumption.
intros; apply IHl2l1; trivial; right; assumption.
intros; apply IHl1s2; trivial; right; assumption.
intros; apply IHs2l1; trivial; right; assumption.
intros; apply IHs1l2; trivial; right; assumption.
intros; apply IHl2s1; trivial; right; assumption.
simpl in R'; rewrite H' in R'; assumption.
simpl in T'; rewrite H' in T'; assumption.
intros; apply Sl; right; assumption.
intro. assert (H4: False). apply prec_not_prec_eq with symbol Prec f2 f1; trivial. apply prec_eq_sym; trivial. contradict H4. 
intro. assert (H4: False). apply prec_not_prec_eq with symbol Prec f1 f2; trivial.  contradict H4. 
intros [f2_diff_f2 _]; absurd (f2 = f2); trivial. contradict f2_diff_f2. apply prec_eq_sym; trivial.
simpl in T'; absurd (@None comp = None); trivial.
simpl in T'; absurd (@None comp = None); trivial.
destruct L as [L | [L1 L2]].
rewrite L; rewrite <- beq_nat_refl; intro; discriminate.
rewrite (leb_correct _ _ L1); rewrite (leb_correct _ _ L2); rewrite orb_true_r; intro; discriminate.
(* 1/1 Top_eq_mul *)
set (s1 := Term f1 l1) in *.
set (s2 := Term f2 l2) in *.
split; [clear R' T' | clear R T].
(* 1/2 *)
destruct (list_exists_option
     (fun t : term =>
      match rpo_eval  rpo_infos n t s2 with
      | Some Equivalent => Some true
      | Some Less_than => Some false
      | Some Greater_than => Some true
      | Some Uncomparable => Some false
      | None => None (A:=bool)
      end) l1) as [ [ | ] | ].
(* 1/4 *)
simpl in R;  destruct (rpo_closure rpo_infos.(bb) s1 s2 s2) as [_ [Antisym _]].
apply False_rect; apply Antisym; trivial.
(* 1/3 *)
destruct (list_exists_option
         (fun t : term =>
          match rpo_eval rpo_infos n s1 t with
          | Some Equivalent => Some true
          | Some Less_than => Some true
          | Some Greater_than => Some false
          | Some Uncomparable => Some false
          | None => None (A:=bool)
          end) l2) as [ [ | ] | ].
(* 1/5 *)
trivial.
(* 1/4 *)
simpl; generalize (prec_eval_is_sound f1 f2); destruct (prec_eval f1 f2).
(* 1/7 *)
intros _; rewrite Sf; rewrite Sf in R; rewrite Sf in T; simpl in R; simpl in T.
assert (H' := remove_equiv_eval_list_is_sound (equiv_eval rpo_infos n) l1 l2).
case_eq (remove_equiv_eval_list (equiv_eval rpo_infos n) l1 l2).
intros [l1' l2'] H; rewrite H in R, T, H'.
assert (H'' : rpo_mul (bb rpo_infos) l1' l2').
destruct H' as [ll [Ell [P1 [P2 _]]]].
assert (Ell' : forall t1 t2, In (t1,t2) ll -> equiv t1 t2).
intros t1 t2 t1t2_in_ll.
generalize (equiv_eval_is_sound_weak rpo_infos n t1 t2).
rewrite (Ell _ _ t1t2_in_ll); intro t1_eq_t2; apply t1_eq_t2; apply eq_refl.
revert Ell' l1_lt_l2 P1 P2; clear; revert l1 l2 l1' l2'; induction ll as [ | [t1 t2] ll];
intros l1 l2 l1' l2' Ell l1_lt_l2 P1 P2.
rewrite <- app_nil_end in P1.
rewrite <- app_nil_end in P2.
inversion l1_lt_l2; subst.
apply (@List_mul _ a lg ls lc); trivial.
transitivity l1; [symmetry; apply permut_impl with eq | idtac]; trivial.
intros a' b a_eq_b; subst a'; apply Eq.
transitivity l2; [symmetry; apply permut_impl with eq | idtac]; trivial.
intros a' b a_eq_b; subst a'; apply Eq.
apply (@rpo_mul_remove_equiv_aux rpo_infos.(bb) l1' l2' t1 t2).
intros t _; apply (@rpo_antirefl rpo_infos.(bb) t); trivial.
apply Ell; left; apply eq_refl.
apply IHll with l1 l2; trivial.
intros; apply Ell; right; assumption.
refine (list_permut.permut_trans _ P1 _).
intros; subst; apply eq_refl.
apply list_permut.permut_sym.
intros; subst; apply eq_refl.
simpl; apply Pcons; [trivial | apply list_permut.permut_refl; intros; trivial].
refine (list_permut.permut_trans _ P2 _).
intros; subst; apply eq_refl.
apply list_permut.permut_sym.
intros; subst; apply eq_refl.
simpl; apply Pcons; [trivial | apply list_permut.permut_refl; intros; trivial].
destruct l1' as [ | t1' l1']; destruct l2' as [ | t2' l2'].
(* 1/11 *)
absurd (rpo rpo_infos.(bb) s1 s1).
intro; apply (@rpo_antirefl rpo_infos.(bb) s1); trivial.
rewrite <- (equiv_rpo_equiv_1 _ R) in t1_lt_t2; trivial.
(* 1/10 *)
trivial.
(* 1/9 *)
absurd (rpo rpo_infos.(bb) s1 s1).
intro; apply (@rpo_antirefl rpo_infos.(bb) s1); trivial.
apply rpo_trans with s2; trivial.
(* 1/8 *)
unfold mult_eval, list_gt_list; unfold mult_eval, list_gt_list in R,T.
destruct (list_forall_option
          (fun t2 : term =>
           list_exists_option
             (fun t1 : term =>
              match rpo_eval rpo_infos n t1 t2 with
              | Some Equivalent => Some false
              | Some Less_than => Some false
              | Some Greater_than => Some true
              | Some Uncomparable => Some false
              | None => None (A:=bool)
              end) (t1' :: l1')) (t2' :: l2')) as [ [ | ] | ].
(* 1/10 *)
absurd (rpo rpo_infos.(bb) s1 s1).
intro; apply (@rpo_antirefl rpo_infos.(bb) s1); trivial.
apply rpo_trans with s2; trivial.
(* 1/9 *)
assert (K : list_forall_option
    (fun t1 : term =>
     list_exists_option
       (fun t2 : term =>
        match rpo_eval rpo_infos n t2 t1 with
        | Some Equivalent => Some false
        | Some Less_than => Some false
        | Some Greater_than => Some true
        | Some Uncomparable => Some false
        | None => None (A:=bool)
        end) (t2' :: l2')) (t1' :: l1') = Some true).
apply list_forall_option_is_complete_true.
intros u1 u1_in_l1'; apply list_exists_option_is_complete_true.
inversion H''; subst.
assert (u1_in_l1 : In u1 l1).
destruct H' as [ll [ _ [P1 _]]].
rewrite (in_permut_in P1); apply in_or_app; left; trivial.
assert (u1_mem_ls_lc : mem equiv u1 (ls ++ lc)).
rewrite <- (mem_permut0_mem equiv_equiv u1 H0); apply in_impl_mem; trivial.
exact Eq.
rewrite <- mem_or_app in u1_mem_ls_lc.
destruct u1_mem_ls_lc as [u1_mem_ls | u1_mem_lc].
destruct (H2 _ u1_mem_ls) as [a' [a'_in_lg u1_lt_a']].
assert (a'_in_tl2' : mem equiv a' (t2' :: l2')).
rewrite (mem_permut0_mem equiv_equiv a' H1).
rewrite app_comm_cons; rewrite <- mem_or_app; left; assumption.
rewrite mem_in_eq in a'_in_tl2'; destruct a'_in_tl2' as [a'' [a''_eq_a' a''_in_tl2']].
exists a''; split.
assumption.
assert (u1_lt_a'' : rpo (bb rpo_infos) u1 a'').
rewrite <- (equiv_rpo_equiv_1 _ a''_eq_a'); trivial.
assert (a''_in_l2 : In a'' l2).
destruct H' as [ll [ _ [_ [P2 _]]]].
rewrite (in_permut_in P2); apply in_or_app; left; trivial.
(* bug, rewrite passe avec _ a la place de u1_in_l1 a''_in_l2 *)
rewrite (proj2 (IHl1l2 u1 a'' u1_in_l1 a''_in_l2 u1_lt_a'')); apply eq_refl.
assert (u1_mem_tl2' : exists u2, equiv u1 u2 /\ In u2 (t2' :: l2')).
rewrite <- (mem_in_eq equiv).
rewrite (mem_permut0_mem equiv_equiv u1 H1).
rewrite app_comm_cons; rewrite <- mem_or_app; right; assumption.
destruct u1_mem_tl2' as [u2 [u1_eq_u2 u2_in_tl2']].
destruct H' as [ll [ _ [_ [P2 H']]]].
assert (K := H' _ _ u1_in_l1' u2_in_tl2').
assert (Su : size u1 + size u2 <= n).
apply Sl; [idtac | rewrite (in_permut_in P2); apply in_or_app; left]; assumption.
apply False_rect; generalize (@equiv_eval_is_sound rpo_infos n u1 u2 Su); rewrite K; intro E; apply E; assumption.
rewrite K; apply eq_refl.
(* 1/8 *)
apply False_rect; apply T; apply eq_refl.
(* 1/7 *)
intros H; rewrite H in T; apply False_rect; apply T; apply eq_refl.
(* 1/6 *)
intro; apply False_rect; apply (prec_antisym Prec f2); trivial. assert (H4: False). apply prec_not_prec_eq with symbol Prec f1 f2; trivial.  contradict H4. 
(* 1/5 *)
intro; apply False_rect; apply (prec_antisym Prec f1); trivial. assert (H4: False). apply prec_not_prec_eq with symbol Prec f2 f1; trivial. apply prec_eq_sym; trivial. contradict H4. 
(* 1/4 *)
intros [f2_diff_f2 _]; absurd (f2 = f2); trivial.
(* 1/3 *)
contradict f2_diff_f2; trivial.
apply False_rect; apply T; apply eq_refl.
(* 1/2 *)
apply False_rect; apply T; apply eq_refl.
(* 1/1 *)
destruct (list_exists_option
     (fun t : term =>
      match rpo_eval  rpo_infos n t s1 with
      | Some Equivalent => Some true
      | Some Less_than => Some false
      | Some Greater_than => Some true
      | Some Uncomparable => Some false
      | None => None (A:=bool)
      end) l2) as [ [ | ] | ].
(* 1/3 *)
trivial.
(* 1/2 *)
destruct (list_exists_option
         (fun t : term =>
          match rpo_eval rpo_infos n s2 t with
          | Some Equivalent => Some true
          | Some Less_than => Some true
          | Some Greater_than => Some false
          | Some Uncomparable => Some false
          | None => None (A:=bool)
          end) l1) as [ [ | ] | ].
(* 1/4 *)
simpl in R'; destruct (rpo_closure rpo_infos.(bb) s1 s2 s2) as [_ [Antisym _]].
apply False_rect; apply Antisym; trivial.
(* 1/3 *)
simpl; generalize (prec_eval_is_sound f2 f1); destruct (prec_eval f2 f1).
(* 1/6 *)
intros _; rewrite Sg; rewrite Sg in R'; rewrite Sg in T'; simpl in R'; simpl in T'.
assert (H' := remove_equiv_eval_list_is_sound (equiv_eval rpo_infos n) l2 l1).
case_eq (remove_equiv_eval_list (equiv_eval rpo_infos n) l2 l1).
intros [l2' l1'] H; rewrite H in R', T', H'.
assert (H'' : rpo_mul (bb rpo_infos) l1' l2').
destruct H' as [ll [Ell [P2 [P1 _]]]].
assert (Ell' : forall t1 t2, In (t1,t2) ll -> equiv t1 t2).
intros t1 t2 t1t2_in_ll.
generalize (equiv_eval_is_sound_weak rpo_infos n t1 t2).
rewrite (Ell _ _ t1t2_in_ll); intro t1_eq_t2; apply t1_eq_t2; apply eq_refl.
revert Ell' l1_lt_l2 P1 P2; clear; revert l1 l2 l1' l2'; induction ll as [ | [t2 t1] ll];
intros l1 l2 l1' l2' Ell l1_lt_l2 P1 P2.
rewrite <- app_nil_end in P1.
rewrite <- app_nil_end in P2.
inversion l1_lt_l2; subst.
apply (@List_mul _ a lg ls lc); trivial.
transitivity l1; [symmetry; apply permut_impl with eq | idtac]; trivial.
intros a' b a_eq_b; subst a'; apply Eq.
transitivity l2; [symmetry; apply permut_impl with eq | idtac]; trivial.
intros a' b a_eq_b; subst a'; apply Eq.
apply (@rpo_mul_remove_equiv_aux rpo_infos.(bb) l1' l2' t1 t2).
intros t _; apply (@rpo_antirefl rpo_infos.(bb) t); trivial.
symmetry; apply Ell; left; apply eq_refl.
apply IHll with l1 l2; trivial.
intros; apply Ell; right; assumption.
refine (list_permut.permut_trans _ P1 _).
intros; subst; apply eq_refl.
apply list_permut.permut_sym.
intros; subst; apply eq_refl.
simpl; apply Pcons; [trivial | apply list_permut.permut_refl; intros; trivial].
refine (list_permut.permut_trans _ P2 _).
intros; subst; apply eq_refl.
apply list_permut.permut_sym.
intros; subst; apply eq_refl.
simpl; apply Pcons; [trivial | apply list_permut.permut_refl; intros; trivial].
destruct l1' as [ | t1' l1']; destruct l2' as [ | t2' l2'].
(* 1/10 *)
absurd (rpo rpo_infos.(bb) s2 s2).
intro; apply (@rpo_antirefl rpo_infos.(bb) s2); trivial.
rewrite <- (equiv_rpo_equiv_2 _ R') in t1_lt_t2; trivial.
(* 1/9 *)
trivial.
(* 1/8 *)
absurd (rpo rpo_infos.(bb) s2 s2).
intro; apply (@rpo_antirefl rpo_infos.(bb) s2); trivial.
apply rpo_trans with s1; trivial.
(* 1/7 *)
unfold mult_eval, list_gt_list; unfold mult_eval, list_gt_list in R', T'.
assert (K : list_forall_option
          (fun t2 : term =>
           list_exists_option
             (fun t1 : term =>
              match rpo_eval rpo_infos n t1 t2 with
              | Some Equivalent => Some false
              | Some Less_than => Some false
              | Some Greater_than => Some true
              | Some Uncomparable => Some false
              | None => None (A:=bool)
              end) (t2' :: l2')) (t1' :: l1') = Some true).
apply list_forall_option_is_complete_true.
intros u1 u1_in_l1'; apply list_exists_option_is_complete_true.
inversion H''; subst.
assert (u1_in_l1 : In u1 l1).
destruct H' as [ll [ _ [_ [P1 _]]]].
rewrite (in_permut_in P1); apply in_or_app; left; trivial.
assert (u1_mem_ls_lc : mem equiv u1 (ls ++ lc)).
rewrite <- (mem_permut0_mem equiv_equiv u1 H0); apply in_impl_mem; trivial.
exact Eq.
rewrite <- mem_or_app in u1_mem_ls_lc.
destruct u1_mem_ls_lc as [u1_mem_ls | u1_mem_lc].
destruct (H2 _ u1_mem_ls) as [a' [a'_in_lg u1_lt_a']].
assert (a'_in_tl2' : mem equiv a' (t2' :: l2')).
rewrite (mem_permut0_mem equiv_equiv a' H1).
rewrite app_comm_cons; rewrite <- mem_or_app; left; assumption.
rewrite mem_in_eq in a'_in_tl2'; destruct a'_in_tl2' as [a'' [a''_eq_a' a''_in_tl2']].
exists a''; split.
assumption.
assert (u1_lt_a'' : rpo (bb rpo_infos) u1 a''). 
rewrite <- (equiv_rpo_equiv_1 _ a''_eq_a'); trivial.
assert (a''_in_l2 : In a'' l2).
destruct H' as [ll [ _ [P2 _]]].
rewrite (in_permut_in P2); apply in_or_app; left; trivial.
(* bug, rewrite passe avec _ a la place de u1_in_l1 a''_in_l2 *)
rewrite (proj2 (IHl1l2 u1 a'' u1_in_l1 a''_in_l2 u1_lt_a'')); apply eq_refl.
assert (u1_mem_tl2' : exists u2, equiv u1 u2 /\ In u2 (t2' :: l2')).
rewrite <- (mem_in_eq equiv).
rewrite (mem_permut0_mem equiv_equiv u1 H1).
rewrite app_comm_cons; rewrite <- mem_or_app; right; assumption.
destruct u1_mem_tl2' as [u2 [u1_eq_u2 u2_in_tl2']].
destruct H' as [ll [ _ [P2 [_ H']]]].
assert (K := H' _ _ u2_in_tl2' u1_in_l1').
assert (Su : size u2 + size u1 <= n).
rewrite plus_comm; apply Sl; [idtac | rewrite (in_permut_in P2); apply in_or_app; left]; assumption.
apply False_rect; generalize (@equiv_eval_is_sound rpo_infos n u2 u1 Su); rewrite K; intro E; apply E.
symmetry; assumption.
rewrite K; apply eq_refl.
(* 1/6 *)
intros H; rewrite H in T'; apply False_rect; apply T'; apply eq_refl.
(* 1/5 *)
intro. assert (H4: False). apply prec_not_prec_eq with symbol Prec f2 f1; trivial.  apply prec_eq_sym; trivial. contradict H4. 
(* 1/4 *)
intro; apply False_rect; apply (prec_antisym Prec f2); trivial.
assert (H4: False). apply prec_not_prec_eq with symbol Prec f1 f2; trivial. contradict H4. 
(* 1/3 *)
intros [f2_diff_f2 _]; absurd (f2 = f2); trivial.
contradict f2_diff_f2. apply prec_eq_sym; trivial.
(* 1/2 *)
apply False_rect; apply T'; apply eq_refl.
(* 1/1 *)
apply False_rect; apply T'; apply eq_refl.
(*SLOW*)Qed.

Lemma rpo_eval_is_complete :
  forall rpo_infos n t1 t2, size t1 + size t2 <= n -> 
        match rpo_eval rpo_infos n t1 t2 with
        | Some Equivalent => equiv t1 t2
        | Some Less_than => rpo rpo_infos.(bb) t1 t2
        | Some Greater_than => rpo rpo_infos.(bb) t2 t1
        | Some Uncomparable => ~equiv t1 t2 /\ ~ rpo rpo_infos.(bb) t1 t2 /\ ~rpo rpo_infos.(bb) t2 t1
        | None => False
        end.
intros rpo_infos n t1 t2 St;
generalize (rpo_eval_is_sound_weak rpo_infos n t1 t2)
(@rpo_eval_is_complete_equivalent rpo_infos n t1 t2 St)
(@rpo_eval_is_complete_less_greater rpo_infos n t1 t2 St)
(@rpo_eval_terminates rpo_infos n t1 t2 St);
rewrite plus_comm in St;
generalize (@rpo_eval_is_complete_less_greater rpo_infos n t2 t1 St).
destruct (rpo_eval rpo_infos n t1 t2) as [ [ | | | ] | ]; trivial.
intros not_t2_lt_t1 _ t1_diff_t2 not_t1_lt_t2 T; repeat split; intro H.
generalize (t1_diff_t2 H); discriminate.
destruct (not_t1_lt_t2 H); discriminate.
destruct (not_t2_lt_t1 H); discriminate.
intros _ _ _ _ H; apply H; trivial.
Qed.

Definition empty_rpo_infos : forall (n : nat), rpo_inf.
Proof. 
intro n;  constructor 1 with n (@nil (term*term)) (@nil (term*term)) (@nil (term*term));simpl;tauto.
Defined.

Definition add_equiv : forall (rpo_infos:rpo_inf) t1 t2 (H:equiv t1 t2), rpo_inf.
Proof.  
  intros rpo_infos t1 t2 H.
  case rpo_infos.
  clear rpo_infos. 
  intros bb0 rpo_l0 rpo_eq_l0 equiv_l0 rpo_l_valid0 rpo_eq_valid0 equiv_l_valid0.
  constructor 1 with bb0 rpo_l0 rpo_eq_l0 ((t1,t2)::equiv_l0).
  exact rpo_l_valid0.
  exact rpo_eq_valid0.
  simpl.
  intros t t' H0.
  case H0;  intros H1.
  injection H1.
  intros H2 H3.
  rewrite <- H2;rewrite <- H3;exact H.
  exact (equiv_l_valid0 _ _ H1).
Defined.


(* Sorin's contribution *)


Definition rpo_mult_eval rpo_infos n l1 l2 :=
                                match remove_equiv_eval_list (equiv_eval rpo_infos n) l1 l2 with
                                | None =>  mult_eval (rpo_eval rpo_infos n) l1 l2
                                | Some (nil, nil) => Some Equivalent
                                | Some (nil, _ :: _) => Some Less_than
                                | Some (_ :: _,nil) => Some Greater_than
                                | Some (l, l') => mult_eval (rpo_eval rpo_infos n) l l'
                                end.
 
Theorem rpo_mul_subst : forall A B: (list term), forall bb:nat,  rpo_mul bb A B -> 
  forall sigma,  rpo_mul bb (map (apply_subst sigma) A) (map (apply_subst sigma) B).
Proof. (* inspired from the proof of rpo_subst *)
intros l' l bb0 Rmul sigma.
inversion Rmul as [ a lg ls lc l0 k0 Pk Pl ls_lt_alg]; subst.
apply (@List_mul bb0 (apply_subst sigma a) (map (apply_subst sigma) lg)
(map (apply_subst sigma) ls) (map (apply_subst sigma) lc)).
rewrite <- map_app; apply permut_map with equiv; trivial.
intros b b' _ _ b_eq_b'; apply equiv_subst; trivial.
rewrite <- map_app.
refine (@permut_map term term term term equiv 
                    equiv (apply_subst sigma) _ _ (a :: lg ++ lc) _ _); trivial.
intros b b' b_in_l _ b_eq_b'; apply equiv_subst; trivial.
intros b b_mem_ls_sigma; 
destruct (mem_split_set _ _ equiv_bool_ok _ _ b_mem_ls_sigma) as [b' [ls1 [ls2 [b_eq_b' [H _]]]]];
simpl in b_eq_b'; simpl in H.
assert (b'_in_ls_sigma : In b' (map (apply_subst sigma) ls)).
rewrite H; apply in_or_app; right; left; trivial.
rewrite in_map_iff in b'_in_ls_sigma.
destruct b'_in_ls_sigma as [b'' [b''_sigma_eq_b' b''_in_ls]].
destruct (ls_lt_alg b'') as [a' [a'_mem_alg b''_lt_a']].
apply in_impl_mem; trivial.
exact Eq.
destruct (mem_split_set _ _ equiv_bool_ok _ _ a'_mem_alg) as [a'' [alg' [alg'' [a'_eq_a'' [H' _]]]]];
simpl in a'_eq_a''; simpl in H'.
exists (apply_subst sigma a''); split; trivial.
apply in_impl_mem.
exact Eq.
rewrite (in_map_iff (apply_subst sigma) (a :: lg)).
exists a''; split; trivial.
rewrite H'; apply in_or_app; right; left; trivial.
rewrite (equiv_rpo_equiv_2 _ b_eq_b').
rewrite <- b''_sigma_eq_b'.
apply rpo_subst.
rewrite <- (equiv_rpo_equiv_1 _ a'_eq_a''); trivial.
Qed.

Lemma rpo_mul_dec: forall bb k l, {rpo_mul bb k l}+{~ rpo_mul bb k l}.
Proof. (* inspired from the proof of rpo_dec *)
intros.
assert (H' := remove_equiv_list_is_sound k l).
revert H'; destruct (remove_equiv_list k l) as [k' l']; intro H'.
destruct H' as [lc [Pk [Pl D]]].
assert (Rem : rpo_mul bb0 k l -> rpo_mul bb0 k' l').
generalize l k l' k' Pk Pl; clear l k l' k' Pk Pl D.
induction lc as [ | c lc]; intros l k l' k' Pk Pl k_lt_l.
inversion k_lt_l as [a lg ls lc' k'' l'' Rk Rl ls_lt_alg]; subst.
apply (@List_mul bb0 a lg ls lc'); trivial.
transitivity k; trivial; symmetry; rewrite <- app_nil_end in Pk; trivial.
transitivity l; trivial; symmetry; rewrite <- app_nil_end in Pl; trivial.
assert (H := IHlc l k (l' ++ c :: nil) (k' ++ c :: nil)).
do 2 rewrite <- ass_app in H; simpl in H.
generalize (H Pk Pl k_lt_l); clear H; intro H.
apply (@rpo_mul_remove_equiv_aux bb0 k' l' c c).
intros t _; apply rpo_antirefl.
reflexivity.
inversion H as [a lg ls lc' k'' l'' Rk Rl ls_lt_alg]; subst.
apply (@List_mul bb0 a lg ls lc'); trivial.
rewrite <- Rk; rewrite <- permut0_cons_inside;[|apply equiv_equiv|reflexivity].
rewrite <- app_nil_end; reflexivity || auto.
rewrite <- Rl; rewrite <- permut0_cons_inside;[|apply equiv_equiv|reflexivity].
rewrite <- app_nil_end; reflexivity || auto.

let P := constr:(forall u, mem equiv u k' -> exists v,  mem equiv v l' /\ rpo bb0 u v) in
assert (H' : {P} + {~ P}).
assert (IH' : forall u v, mem equiv u k' -> mem equiv v l' -> {rpo bb0 u v}+{~rpo bb0 u v}).

intros u v u_mem_k' v_mem_l'. apply rpo_dec.
generalize l' IH'; clear l k  l' lc Pk Pl D IH' Rem.
induction k' as [ | u' k']; intros l' IH'.
left; intros; contradiction.
let P:=constr:(forall v, mem equiv v l' -> ~rpo bb0 u' v) in
assert (H : {v | mem equiv v l' /\ rpo bb0 u' v}+{P}).
assert (IH'' : forall v, mem equiv v l' -> {rpo bb0 u' v}+{~rpo bb0 u' v}).
intros v v_mem_l'; apply (IH' u' v); trivial.
left; reflexivity.
clear IHk' IH'; induction l' as [ | v' l'].
right; intros; contradiction.


destruct IHl' as [Ok | Ko].
intros; apply IH''; right; trivial.
destruct Ok as [v [v_mem_l' u'_lt_v]]; left; exists v; split; trivial.
right; trivial.
destruct (IH'' v') as [Ok' | Ko'].
left; reflexivity.
left; exists v'; split; trivial.
left; reflexivity.
right; intros v [v'_eq_v | v_mem_l'].
intros u'_lt_v; apply Ko'.
rewrite <- (equiv_rpo_equiv_1 _ v'_eq_v); trivial.
apply Ko; trivial.
destruct H as [[v [v_mem_l' u'_lt_v]] | Ko].
destruct (IHk' l') as [Ok' | Ko'].
intros u v' u_mem_k' v'_mem_l'; apply IH'; trivial; right; trivial.

left; intros u [u'_eq_u | u_mem_k'].
exists v; split; trivial.
rewrite (equiv_rpo_equiv_2 _ u'_eq_u); trivial.
apply Ok'; trivial.
right; intro H; apply Ko'.
intros u u_mem_k'; apply H; right; trivial.
right; intro H.
destruct (H u') as [v [v_mem_l' u'_lt_v]].
left; reflexivity.
apply (Ko v); trivial.
destruct l' as [ | v' l'].
right; intro fk_lt_fl.
assert (rpo_mul bb0 k' []).
apply Rem. trivial.
inversion H.
inversion H1.

destruct H' as [Ok | Ko].
left; apply (@List_mul bb0 v' l' k' lc); trivial.
right. intro.
contradict Ko.
assert (rpo_mul bb0 k' (v' :: l')).
apply Rem. trivial.

 
inversion H0 as [a lg ls lc' k'' l'' Rk Rl ls_lt_alg]; subst.
intro u. rewrite Rk. rewrite <- mem_or_app.
intros [u_mem_ls | u_mem_lc'].
destruct (ls_lt_alg _ u_mem_ls) as [a' [a'_mem_alg u_lt_a']];
exists a'; split; trivial.
rewrite Rl; rewrite app_comm_cons;
rewrite <- mem_or_app; left; trivial.
assert False.
apply (D u u).
rewrite Rk; rewrite <- mem_or_app; right; trivial.
rewrite Rl; rewrite app_comm_cons;
rewrite <- mem_or_app; right; trivial.
reflexivity.
contradiction.
Qed.

Theorem rpo_mul_rest_dec: forall bb k l,  well_founded (prec Prec) -> {rpo_mul_rest bb k l}+{~ rpo_mul_rest bb k l}.
Proof.
intros.
assert (H2:= @rpo_mul_dec bb0 k l).
assert (H3:=wf_rpo). assert (well_founded (rpo bb0)).
apply H3. trivial.
destruct H2.
left. apply Rpo_mul_rest.
intros. apply H0. intros. apply H0. trivial.
right. intro.
contradict n.
inversion H1. trivial.
Qed.

Lemma permut0_eq_equiv: forall A B, permut0 eq A B -> permut0 equiv A B.
Proof.
intros A B H.
assert (H':=permut_impl).
assert (H1:= H' term term eq equiv A B); clear H'. 
apply H1.
intros a b H'.
rewrite H'.
reflexivity.
assumption.
Qed.
  

Lemma equiv_eval_lists: forall A ll n rpo_infos, 
  (forall t1 t2, In (t1, t2) ll -> equiv_eval rpo_infos n t1 t2 = Some true) -> 
      permut0 equiv (A ++ map (fun st : term * term => fst st) ll) (A ++ map (fun st : term * term => snd st) ll).
Proof.
intro H.
induction ll. 
intros n rpo_infos H1. 
simpl. apply permut_refl. intros a H'.
reflexivity.

intros.
assert (H':= IHll n rpo_infos); clear IHll.
assert (H1:  permut0 equiv (H ++ map (fun st : term * term => fst st) ll)
         (H ++ map (fun st : term * term => snd st) ll)).
apply H'. intros t1 t2 H3.
assert (H0':= H0 t1 t2).
apply H0'. simpl. right; assumption.
assert (H0':= H0 (fst a) (snd a)); clear H0.
assert (equiv_eval rpo_infos n (fst a) (snd a) = Some true).
apply H0'. simpl; left. destruct a. simpl. trivial.
simpl.

apply permut_strong.
assert (H1':= equiv_eval_is_sound_weak).
assert (H2:= H1' rpo_infos n (fst a) (snd a)).
apply H2; trivial.
trivial.
Qed.

Lemma equiv_rpo_eval: forall  n rpo_infos t s u, size t + size u <= n -> size t + size s <= n -> equiv u s -> rpo_eval rpo_infos n t u = rpo_eval rpo_infos n t s.
Proof.
intros n rpo_infos t s u tu ts H.

assert (H1:= equiv_rpo_equiv_1).
assert (H2:= rpo_eval_is_complete_less_greater).
assert (H3:= rpo_eval_is_complete).
assert (H2':= H2 rpo_infos n t u).
assert (H2'':= H2 rpo_infos n t s); clear H2. 
assert (H3':= H3 rpo_infos n t u).
assert (H3'':= H3 rpo_infos n t s); clear H3.
assert (H31: match rpo_eval rpo_infos n t s with
         | Some Equivalent => equiv t s
         | Some Less_than => rpo (bb rpo_infos) t s
         | Some Greater_than => rpo (bb rpo_infos) s t
         | Some Uncomparable =>
             ~ equiv t s /\
             ~ rpo (bb rpo_infos) t s /\ ~ rpo (bb rpo_infos) s t
         | None => False
         end). 
apply H3''; trivial.
assert (H32: match rpo_eval rpo_infos n t u with
        | Some Equivalent => equiv t u
        | Some Less_than => rpo (bb rpo_infos) t u
        | Some Greater_than => rpo (bb rpo_infos) u t
        | Some Uncomparable =>
            ~ equiv t u /\
            ~ rpo (bb rpo_infos) t u /\ ~ rpo (bb rpo_infos) u t
        | None => False
        end).
apply H3'; trivial. 
clear H3'' H3'.
destruct (rpo_eval rpo_infos n t u) as [[ | | | ] | ].
destruct (rpo_eval rpo_infos n t s) as [[ | | | ] | ].
trivial.
assert (H':= @Equivalence_Transitive _ _ equiv_equiv t u s).
assert (H1': equiv t s).
auto.
assert (H2: rpo_eval rpo_infos n s t = Some Greater_than).
tauto.
assert (H3:= rpo_eval_is_complete_equivalent).
assert (H3':= H3 rpo_infos n s t).
assert (H4': size s + size t <=n).
lia.
assert (H4: rpo_eval rpo_infos n s t = Some Equivalent).
rewrite H2 in H3'.
assert (H5':= @Equivalence_Symmetric _ _ equiv_equiv t s).
assert (H5: equiv s t). apply H5'; assumption. auto.
rewrite H2 in H4. discriminate.

assert (H':= @Equivalence_Transitive _ _ equiv_equiv t u s).
assert (H1': equiv t s).
auto.
clear H2' H2''.
assert (H4: rpo_eval rpo_infos n s t = Some Less_than).
assert (H3:= rpo_eval_is_complete_less_greater).
assert (H6:= H3 rpo_infos n s t). apply H6. lia. assumption.


assert (H3:= rpo_eval_is_complete_equivalent).
assert (H3':= H3 rpo_infos n s t).
assert (H5':= @Equivalence_Symmetric _ _ equiv_equiv t s).
assert (H6: equiv s t). auto.
assert (H4': size s + size t <=n).
lia.
rewrite H4 in H3'.
assert (Some Less_than = Some Equivalent).
auto.
discriminate.

clear H2' H2''.
destruct H31.
assert (H':= @Equivalence_Transitive _ _ equiv_equiv t u s).
tauto.
contradict H31.


destruct (rpo_eval rpo_infos n t s) as [[ | | | ] | ].
trivial.

assert (H5':= @Equivalence_Symmetric _ _ equiv_equiv u s).
assert (H5'': equiv s u).
auto.
assert (H':= @Equivalence_Transitive _ _ equiv_equiv t s u). 
assert (H1': equiv t u).
auto.
assert (H2: rpo_eval rpo_infos n u t = Some Greater_than).
tauto.
assert (H3:= rpo_eval_is_complete_equivalent).
assert (H3':= H3 rpo_infos n u t).
assert (H4': size u + size t <=n).
lia.
assert (H4: rpo_eval rpo_infos n u t = Some Equivalent).
rewrite H2 in H3'.
assert (H6':= @Equivalence_Symmetric _ _ equiv_equiv t u).
assert (H5: equiv u t). apply H6'; assumption. auto.
rewrite H2 in H4.
discriminate.
trivial.
 
rewrite  (equiv_rpo_equiv_1 _ H) in H32.
assert (H2:= rpo_eval_is_complete_less_greater); clear H2' H2''.
assert (H2':= H2 rpo_infos n t s).
assert (H2'':= H2 rpo_infos n s t).
assert (H4': size s + size t <=n).
lia.
assert (H5: rpo_eval rpo_infos n t s = Some Less_than).
tauto.
assert (H5': rpo_eval rpo_infos n t s = Some Greater_than).
tauto.
rewrite H5 in H5'; discriminate.

destruct H31 as (H41, (H42, H43)).
rewrite (equiv_rpo_equiv_1 _ H) in H32.
contradiction.
contradiction.

destruct (rpo_eval rpo_infos n t s) as [[ | | | ] | ].
trivial.

assert (H5':= @Equivalence_Symmetric _ _ equiv_equiv t s).
assert (H5'': equiv s t).
auto.
assert (H':= @Equivalence_Transitive _ _ equiv_equiv u s t). 
assert (H1': equiv u t).
auto.
assert (H3:= rpo_eval_is_complete_equivalent).
assert (H3':= H3 rpo_infos n u t).
assert (H4': size u + size t <=n).
lia.
assert (H4: rpo_eval rpo_infos n u t = Some Equivalent).
auto.
assert (H2:= rpo_eval_is_complete_less_greater); clear H2' H2''.
assert (H2':= H2 rpo_infos n u t).
assert (rpo_eval rpo_infos n u t = Some Less_than).
tauto.
rewrite H0 in H4.
discriminate.

rewrite <- (equiv_rpo_equiv_1 _ H) in H31.
assert (H2:= rpo_eval_is_complete_less_greater); clear H2' H2''.
assert (H2':= H2 rpo_infos n t u).
assert (H2'':= H2 rpo_infos n u t).
assert (H4': size u + size t <=n).
lia.
assert (H5: rpo_eval rpo_infos n t u = Some Less_than).
tauto.
assert (H5': rpo_eval rpo_infos n t u = Some Greater_than).
tauto.
rewrite H5 in H5'; discriminate.
trivial.


destruct H31 as (H41, (H42, H43)).
rewrite -> (equiv_rpo_equiv_2 _ H) in H32.
contradiction.
contradiction.


destruct (rpo_eval rpo_infos n t s) as [[ | | | ] | ].
trivial.

destruct H32 as (H41, (H42, H43)).
assert (H5':= @Equivalence_Symmetric _ _ equiv_equiv u s).
assert (H5'': equiv s u).
auto.
assert (H':= @Equivalence_Transitive _ _ equiv_equiv t s u). 
tauto.

destruct H32 as (H41, (H42, H43)).
rewrite <- (equiv_rpo_equiv_1 _ H) in H31.
contradiction.

destruct H32 as (H41, (H42, H43)).
rewrite <- (equiv_rpo_equiv_2 _ H) in H31.
contradiction.
trivial.
contradiction.

destruct (rpo_eval rpo_infos n t s) as [[ | | | ] | ]; contradiction.
Qed.


Lemma list_gt_list_is_sound_mem_equiv :
  forall rpo_infos n lg ls, (forall t t' :term, mem equiv t ls -> mem equiv t' lg -> size t + size t' <= n) ->
   match list_gt_list (rpo_eval rpo_infos n) lg ls with
   | Some true => forall s, mem equiv s ls -> exists g, mem equiv g lg /\  rpo_eval rpo_infos n g s = Some Greater_than
   | _ => True
   end.
Proof.
intros rpo_infos n lg ls H0. 
assert (forall t t' : term,
      mem equiv t ls -> mem equiv t' lg -> size t' + size t <= n).
intros.
assert (H0':= H0 t t').  assert (size t + size t' <= n). tauto. lia. 

induction ls as [ | s ls].

simpl; intros; contradiction.
unfold list_gt_list; simpl. 
assert (match list_gt_list (rpo_eval rpo_infos n) lg ls with
         | Some true =>
             forall s : term,
             mem equiv s ls ->
             exists g : term,
               mem equiv g lg /\ rpo_eval rpo_infos n g s = Some Greater_than
         | Some false => True
         | None => True
         end).
apply IHls.
intros t t' H'. apply H0. simpl. tauto. clear IHls.  intros.
apply H. simpl. right. trivial. simpl. trivial. clear IHls.

generalize (list_exists_option_is_sound
  ( fun g : term =>
       match rpo_eval rpo_infos n g s with
       | Some Equivalent => Some false
       | Some Less_than => Some false
       | Some Greater_than => Some true
       | Some Uncomparable => Some false
       | None => None
       end) lg). 
destruct
(list_exists_option
    (fun g : term =>
     match rpo_eval rpo_infos n g s with
     | Some Equivalent => Some false
     | Some Less_than => Some false
     | Some Greater_than => Some true
     | Some Uncomparable => Some false
     | None => None
     end) lg) as [[ | ] | ].
intros [g [g_in_ls H']]. 
 
generalize H1. unfold list_gt_list.
destruct ( list_forall_option
       (fun s0 : term =>
        list_exists_option
          (fun g0 : term =>
           match rpo_eval rpo_infos n g0 s0 with
           | Some Equivalent => Some false
           | Some Less_than => Some false
           | Some Greater_than => Some true
           | Some Uncomparable => Some false
           | None => None
           end) lg) ls) as [[ | ] | ].

intros H0' u [s_eq_u | u_in_ls]. 

 
exists g; split.
apply in_mem.
assumption.
assert (H1':= in_mem g lg).
assert (H2': mem equiv g lg).
auto.
assert (H3':= equiv_rpo_eval).
assert (H3:= H3' n rpo_infos g s u); clear H3'.
assert (H4':= H0' s).
assert (H5: rpo_eval rpo_infos n g u = rpo_eval rpo_infos n g s).
assert (H6:= equiv_same_size).
assert (H6':= H6 u s); clear H6.
assert (size u = size s).
auto.
apply H3. apply H. 
simpl.
tauto. assumption.
apply H.
simpl. 
left. reflexivity. assumption.
assumption.
rewrite H5.

generalize H'.
destruct (rpo_eval rpo_infos n g s) as [[ | | | ] | ]; intros. discriminate.
discriminate. trivial. discriminate. discriminate. 
assert (H10':= H0' u); clear H0'.
assert (H0': exists g : term,
           mem equiv g lg /\ rpo_eval rpo_infos n g u = Some Greater_than).
apply H10'. trivial. trivial. trivial. trivial.
intros _;
destruct
(list_forall_option
    (fun s0 : term =>
     list_exists_option
       (fun g0 : term =>
        match rpo_eval rpo_infos n g0 s0 with
        | Some Equivalent => Some false
        | Some Less_than => Some false
        | Some Greater_than => Some true
        | Some Uncomparable => Some false
        | None => None
        end) lg) ls) as [[ | ] | ]; trivial.
trivial.
Qed.


Lemma mult_eval_is_sound_weak_equiv :
  forall rpo_infos n l1 l2, (forall t t' :term, mem equiv t l1 -> mem equiv t' l2 -> size t + size t' <= n) ->
   match mult_eval (rpo_eval rpo_infos n)  l1 l2 with
     | Some Equivalent => False
     | Some Less_than =>  
       forall t1, mem equiv t1 l1 -> exists t2,  mem equiv t2 l2 /\ (size t2 + size t1 <= n -> rpo_eval rpo_infos n t2 t1 = Some Greater_than)
     | Some Greater_than =>  
       forall t2, mem equiv t2 l2 -> exists t1, mem equiv t1 l1 /\ (size t1 + size t2 <= n -> rpo_eval rpo_infos n t1 t2 = Some Greater_than)
     | _ => True
     end.
Proof.
intros rpo_infos n l1 l2 H; unfold mult_eval.
assert (forall t t' : term,
      mem equiv t l2 -> mem equiv t' l1 -> size t + size t' <= n).
intros t t'.
assert (mem equiv t' l1 -> mem equiv t l2 -> size t' + size t <= n).
apply H.
intros H1' H2.
assert (size t' + size t <= n).
auto.
lia. 
generalize (list_gt_list_is_sound_mem_equiv rpo_infos l1 l2 H0). destruct (list_gt_list (rpo_eval rpo_infos n) l1 l2) as [[ | ] | ]. trivial. intros H' t2 H1.
assert (H2':= H' t2); clear H'. 
assert (H3: exists g : term,
          mem equiv g l1 /\ rpo_eval rpo_infos n g t2 = Some Greater_than).
auto.
destruct H3.
exists x.
assert (H': size x + size t2 <= n).
apply H. apply H2. assumption.
split. apply H2. intro; apply H2.

intros.
generalize (list_gt_list_is_sound_mem_equiv rpo_infos l2 l1 H).
destruct (list_gt_list (rpo_eval rpo_infos n) l2 l1) as [[ | ] | ].
 intros H' t2 H1'. 
assert (H2':= H' t2); clear H'. 
assert (H3: exists g : term,
          mem equiv g l2 /\ rpo_eval rpo_infos n g t2 = Some Greater_than).
auto.
destruct H3.
exists x.
assert (H': size x + size t2 <= n).
apply H0. apply H2. assumption.
split. apply H2. intro; apply H2.
trivial. trivial. trivial.
Qed.
 


Lemma permut0_mem : forall A X L b, permut0 eq A (X ++ L) -> mem equiv b X -> mem equiv b A.
Proof. 
intros.
assert (H1:= permut_impl).
assert (H1':= H1 term term eq equiv A (X ++ L)); clear H1.
assert (permut0 equiv A (X++L)).
apply H1'.
intros a b0 H2.
rewrite H2. reflexivity.
trivial.

assert (H2:=mem_permut0_mem).
assert (H2':= H2 term equiv).
assert (forall (l1 l2 : list term) (a : term),
        permut0 equiv l1 l2 -> (mem equiv a l1 <-> mem equiv a l2)).
apply H2'.
apply equiv_equiv.
assert (H3':= H3 A (X ++ L) b).
assert (mem equiv b A <-> mem equiv b (X ++ L)).
apply H3'. assumption.
 
apply H4; clear H H1 H1' H2 H3 H4.
generalize H0. generalize X.
induction X0.
intros.
contradiction.
simpl. intros. destruct H1. left; trivial. right. apply IHX0; trivial.
Qed. 
 

Theorem rpo_mult_eval_rpo_mul_less: forall rpo_infos n A B,  (forall t t' :term, mem equiv t B -> mem equiv t' A -> size t + size t' <= n) ->  rpo_mult_eval rpo_infos n A B =  Some Less_than -> rpo_mul rpo_infos.(bb) A B.
Proof.
intros rpo_infos n A B H1 H.
unfold rpo_mult_eval in H.
assert (H':= remove_equiv_eval_list_is_sound). 
case_eq (remove_equiv_eval_list (equiv_eval rpo_infos n) A B).
intros p H3.
rewrite H3 in H.
destruct p.
destruct l.
destruct l0.
discriminate.
assert (H2':= H' (equiv_eval rpo_infos n) A B); clear H' H.
rewrite H3 in H2'.
destruct  H2' as (l, (H01, (H02, (H03, H4)))).
apply (@List_mul _ t l0 nil (map (fun st : term * term => fst st) l)).
apply permut0_eq_equiv.
assumption.
apply permut0_trans with (t :: l0 ++ map (fun st : term * term => snd st) l).
apply equiv_equiv.
apply permut0_eq_equiv.
assumption.
assert (H2':= equiv_eval_lists (t::l0) l n rpo_infos H01). 
apply permut0_sym.
apply equiv_equiv.
auto.
intros b H'. 
contradict H'.
destruct l0. 
discriminate.
assert (H3':= H' (equiv_eval rpo_infos n) A B); clear H'.
rewrite H3 in H3'.
destruct H3' as (ll, (H01, (H02, (H03, H4)))). 
apply (@List_mul _ t0 l0 (t :: l) ( map (fun st : term * term => fst st) ll)).
apply permut0_eq_equiv.
assumption.
assert (H2':= equiv_eval_lists (t0::l0) ll n rpo_infos H01).
apply permut0_trans with ((t0 :: l0) ++ map (fun st : term * term => snd st) ll).
apply equiv_equiv.
apply permut0_eq_equiv.
auto.
apply permut0_sym.
apply equiv_equiv.
auto.
intros b H'.
assert (H1':= mult_eval_is_sound_weak_equiv).
assert (H1'':= H1' rpo_infos n (t :: l) (t0 :: l0)); clear H1'.
assert (H6: (forall t1 t' : term,
          mem equiv t' (t :: l) ->
          mem equiv t1 (t0 :: l0) -> size t1 + size t' <= n)).

intros t1 t2 H1' H2.  clear H1''.


apply H1. 
apply permut0_mem with (t0 :: l0) (map (fun st : term * term => snd st) ll).
assumption. assumption.
apply permut0_mem with (t :: l) (map (fun st : term * term => fst st) ll).
assumption. assumption.


assert (H1':  match mult_eval (rpo_eval rpo_infos n) (t :: l) (t0 :: l0) with
         | Some Equivalent => False
         | Some Less_than =>
             forall t1 : term,
             mem equiv t1 (t :: l) ->
             exists t2 : term,
               mem equiv t2 (t0 :: l0) /\
               (size t2 + size t1 <= n ->
                rpo_eval rpo_infos n t2 t1 = Some Greater_than)
         | Some Greater_than =>
             forall t2 : term,
             mem equiv t2 (t0 :: l0) ->
             exists t1 : term,
               mem equiv t1 (t :: l) /\
               (size t1 + size t2 <= n ->
                rpo_eval rpo_infos n t1 t2 = Some Greater_than)
         | Some Uncomparable => True
         | None => True
         end).
apply H1''.
assert (forall t1 t' : term,
       mem equiv t' (t :: l) ->
       mem equiv t1 (t0 :: l0) -> size t' + size t1 <= n).

intros t2 t'.
assert (mem equiv t' (t :: l) -> mem equiv t2 (t0 :: l0) -> size t' + size t2 <= n).
intros H1' H2.
assert (H6':= H6 t2 t').
assert (size t2 + size t' <= n).
auto.
lia. 

assert (H1': match mult_eval (rpo_eval rpo_infos n) (t :: l) (t0 :: l0) with
         | Some Equivalent => False
         | Some Less_than =>
             forall t1 : term,
             mem equiv t1 (t :: l) ->
             exists t2 : term,
               mem equiv t2 (t0 :: l0) /\
               (size t2 + size t1 <= n ->
                rpo_eval rpo_infos n t2 t1 = Some Greater_than)
         | Some Greater_than =>
             forall t2 : term,
             mem equiv t2 (t0 :: l0) ->
             exists t1 : term,
               mem equiv t1 (t :: l) /\
               (size t1 + size t2 <= n ->
                rpo_eval rpo_infos n t1 t2 = Some Greater_than)
         | Some Uncomparable => True
         | None => True
         end).
apply H1''.

intros t1' t2'.
assert (H6':= H6 t2' t1').
intros.
assert (size t2' + size t1' <= n).
auto.
lia. 

intros. apply H0. assumption. assumption.
intros. apply H0. assumption. assumption.

clear H1''; rewrite H in H1' .
assert (H11 := H1' b). clear H1'.
assert (H11': exists t2 : term,
          mem equiv t2 (t0 :: l0) /\
          rpo_eval rpo_infos n t2 b = Some Greater_than).
assert (exists t2 : term,
          size t2 + size b <= n ->
          mem equiv t2 (t0 :: l0) /\
          rpo_eval rpo_infos n t2 b = Some Greater_than).
auto.

assert (H11': exists t2 : term,
          mem equiv t2 (t0 :: l0) /\
          (size t2 + size b <= n ->
           rpo_eval rpo_infos n t2 b = Some Greater_than)).
apply H11. assumption. clear H11.

destruct H11'.
exists x.
tauto.

assert (H11': exists t2 : term,
          mem equiv t2 (t0 :: l0) /\
          (size t2 + size b <= n ->
           rpo_eval rpo_infos n t2 b = Some Greater_than)).
apply H11. assumption. clear H11.
destruct H11'.
exists x.
split.
apply H2.
destruct H2.
apply H5.

apply H6. assumption. assumption.

destruct H11'.
exists x.
split.
apply H0.
destruct H0.
 
assert (H6'':= rpo_eval_is_complete).
assert (H6':= H6'' rpo_infos n x b); clear H6''.
rewrite H2 in H6'.
apply H6'. 
apply H6. assumption. assumption.
intro. 
 
rewrite H0 in H.
assert (H'':= H' (equiv_eval rpo_infos n) A B); clear H'.
rewrite H0 in H''.
destruct H0. 
destruct H'' as (t1, (t2, (In_t1_A, (In_t2_B, H4)))). 
assert (H2:=  mult_eval_is_sound_weak_equiv).
assert (H2':= H2 rpo_infos n A B); clear H2.
rewrite H in H2'. 
assert (forall t1 : term,
        mem equiv t1 A ->
        exists t2 : term,
          mem equiv t2 B /\
          (size t2 + size t1 <= n ->
           rpo_eval rpo_infos n t2 t1 = Some Greater_than)).
apply H2';trivial.
intros.
assert (size t' + size t <= n).
apply H1.
trivial. trivial.
lia.
clear H2'.

destruct B.
unfold In in In_t2_B.
contradict In_t2_B.
apply (@List_mul _ t B A [] (t::B) A).
rewrite <- app_nil_end.
apply permut_refl.
intros.
reflexivity.
rewrite <- app_nil_end.
apply permut_refl.
intros.
reflexivity.
intros.
assert (H0':= H0 b); clear H0.
assert (exists t2 : term,
          mem equiv t2 (t :: B) /\
          (size t2 + size b <= n ->
           rpo_eval rpo_infos n t2 b = Some Greater_than)).
apply H0'; trivial.
destruct H0.
exists x.
split.
destruct H0.
trivial.
destruct H0.
assert (H1':= H1 x b).
assert  (size x + size b <= n).
apply H1'; trivial.
assert (rpo_eval rpo_infos n x b = Some Greater_than).
apply H3; trivial.
assert (H7:= rpo_eval_is_sound_weak rpo_infos n x b ).
rewrite H6 in H7.
trivial. 
Qed.

Lemma rpo_mul_trans : forall bb u t s, rpo_mul bb u t -> rpo_mul bb t s ->  rpo_mul bb u s.
Proof.  (* inspired from the proof of rpo_trans *)
intros.
destruct H0 as [a lg ls lc l l' P' P ls_lt_alg].
destruct H as [a' lg' ls' lc' l' l'' Q' Q ls'_lt_alg'].
rewrite P' in Q; rewrite app_comm_cons in Q.
destruct (@ac_syntactic _ _ equiv_equiv _ equiv_bool_ok _ _ _ _ Q) as [k1 [k2 [k3 [k4 [P1 [P2 [P3 P4]]]]]]].
apply (@List_mul bb0 a (lg ++ k2) (ls' ++ k3) k1).
rewrite Q'.
rewrite <- ass_app.
rewrite <- permut_app1.
rewrite list_permut0_app_app; trivial. apply equiv_equiv. apply equiv_equiv.
rewrite P.
rewrite <- permut0_cons;[|apply equiv_equiv|reflexivity].
rewrite <- ass_app.
rewrite <- permut_app1.
rewrite list_permut0_app_app; trivial.  apply equiv_equiv. apply equiv_equiv.
intros b b_mem_ls'_k3; rewrite <- mem_or_app in b_mem_ls'_k3.
destruct b_mem_ls'_k3 as [b_mem_ls' | b_mem_k3].
destruct (ls'_lt_alg'  _ b_mem_ls') as [a'' [a''_in_a'lg' b_lt_a'']].
rewrite (mem_permut0_mem equiv_equiv a'' P4) in a''_in_a'lg'.
rewrite <- mem_or_app in a''_in_a'lg'.
destruct a''_in_a'lg' as [a''_mem_k2 | a''_mem_k4].
exists a''; split; trivial.
rewrite app_comm_cons; rewrite <- mem_or_app; right; trivial.
destruct (ls_lt_alg a'') as [a3 [a3_in_alg a''_lt_a3]].
rewrite (mem_permut0_mem equiv_equiv a'' P2).
rewrite <- mem_or_app; right; trivial.
exists a3; split.
rewrite app_comm_cons; rewrite <- mem_or_app; left; trivial.
apply rpo_trans with (a''). trivial. trivial.
destruct (ls_lt_alg b) as [a'' [a''_in_alg b_lt_a'']].
rewrite (mem_permut0_mem equiv_equiv b P2); rewrite <- mem_or_app; left; trivial.
exists a''; split; trivial.
rewrite app_comm_cons; rewrite <- mem_or_app; left; trivial.
Qed.
 
Theorem rpo_mul_rest_trans: forall bb l1 l2 l3, well_founded (prec Prec) -> rpo_mul_rest bb l1 l2 -> rpo_mul_rest bb l2 l3 -> rpo_mul_rest bb l1 l3.
Proof.
intros.
assert (H2:= @rpo_mul_trans bb0 l1 l2 l3).
assert (H3:=wf_rpo). assert (well_founded (rpo bb0)).
apply H3. trivial.
apply Rpo_mul_rest.
intros.
unfold well_founded in H4.
apply H4.
intros.
unfold well_founded in H4.
apply H4.
apply H2.
destruct H0; trivial.
destruct H1; trivial.
Qed.

(* some useful lemmas *)

Lemma rpo_mul_remove_equiv_aux1 :
  forall bb l l' s s',  equiv s s' -> rpo_mul bb (s :: l) (s' :: l') -> rpo_mul bb l l'. 
Proof.
intros.
apply rpo_mul_remove_equiv_aux with s s'.
intros H1 H2.
apply rpo_antirefl.
trivial. trivial.
Qed.   

Theorem rpo_mul_antirefl : forall rpo_infos l, rpo_mul (bb rpo_infos) l l -> False. 
Proof.
induction l.
intros.
inversion H.
inversion H1.
intros. 
apply IHl. 
apply rpo_mul_remove_equiv_aux1 with a a. reflexivity. trivial.
Qed.
  
(* other interesting lemmas *)
 
Lemma eq_equiv: forall t1 t2, eq t1 t2 -> equiv t1 t2.
Proof.
intros t1 t2 H.
rewrite H.
reflexivity; trivial.
Qed.

Lemma rpo_mul_dickson: forall bb l l', rpo_mul_rest bb l l' -> clos_trans (list term) (rpo_mul_step_rest bb) l l'.
Proof.
intros.
assert (H1:=  (rpo_mul_rest_trans_clos)).
assert (H2:= H1 bb0).
unfold inclusion in H2.
assert (H2':= H2 l l').
assert ( clos_trans (list term) (rpo_mul_step_rest bb0) l l').
apply H2'; trivial.
trivial.
Qed.

 
Lemma mem_in_1: forall t: term, forall A,  mem eq t A -> In t A.
Proof.
intro t.
induction A.
intros.
unfold mem in H.
contradiction.
unfold mem.
unfold In.
intro H.
destruct H.
left.
rewrite H. trivial.
right.
assert (In t A).
apply IHA.
assumption.
assumption.
Qed.


Lemma mem_in_2: forall t: term, forall A,  In t A -> mem eq t A.
Proof.
intro t.
induction A.
intros.
unfold In in  H.
contradiction.
unfold In.
unfold mem.
intro H.
destruct H.
left.
rewrite H. trivial.
right.
assert (mem eq t A).
apply IHA.
assumption.
assumption.
Qed.

 
Theorem rpo_mult_eval_rpo_mul_greater: forall rpo_infos n A B,  (forall t t' :term, mem equiv t B -> mem equiv t' A -> size t + size t' <= n) ->  rpo_mult_eval rpo_infos n A B =  Some Greater_than -> rpo_mul rpo_infos.(bb) B A.
Proof.
intros rpo_infos n A B H1 H. 
unfold rpo_mult_eval in H.
assert (H':= remove_equiv_eval_list_is_sound). 
case_eq (remove_equiv_eval_list (equiv_eval rpo_infos n) A B).
intros p H3.
rewrite H3 in H.
destruct p.
destruct l.
destruct l0.
discriminate.
discriminate.
destruct l0.
assert (H2':= H' (equiv_eval rpo_infos n) A B); clear H' H.
rewrite H3 in H2'.
destruct  H2' as (l', (H01, (H02, (H03, H4)))).
apply (@List_mul _ t l nil (map (fun st : term * term => snd st) l')).
apply permut0_eq_equiv.
assumption.
apply permut0_trans with (t :: l ++ map (fun st : term * term => fst st) l').
apply equiv_equiv.
apply permut0_eq_equiv.
assumption.
assert (H2':= equiv_eval_lists (t::l) l' n rpo_infos H01). trivial. 
intros b H'. 
contradict H'.

assert (H3':= H' (equiv_eval rpo_infos n) A B); clear H'.
rewrite H3 in H3'.
destruct H3' as (ll, (H01, (H02, (H03, H4)))). 
apply (@List_mul _ t l (t0 :: l0) ( map (fun st : term * term => snd st) ll)). 
apply permut0_eq_equiv.
assumption.
assert (H2':= equiv_eval_lists (t::l) ll n rpo_infos H01).
apply permut0_trans with ((t :: l) ++ map (fun st : term * term => fst st) ll).
apply equiv_equiv.
apply permut0_eq_equiv.
auto.
auto.

intros b H'.
assert (H1':= mult_eval_is_sound_weak_equiv).
assert (H1'':= H1' rpo_infos n (t :: l) (t0 :: l0)); clear H1'.
assert (H6: (forall t1 t' : term,
          mem equiv t' (t :: l) ->
          mem equiv t1 (t0 :: l0) -> size t1 + size t' <= n)).

intros t1 t2 H1' H2.  clear H1''.


apply H1. 
apply permut0_mem with (t0 :: l0) (map (fun st : term * term => snd st) ll).
assumption. assumption.
apply permut0_mem with (t :: l) (map (fun st : term * term => fst st) ll).
assumption. assumption.


assert (H1': match mult_eval (rpo_eval rpo_infos n) (t :: l) (t0 :: l0) with
         | Some Equivalent => False
         | Some Less_than =>
             forall t1 : term,
             mem equiv t1 (t :: l) ->
             exists t2 : term,
               mem equiv t2 (t0 :: l0) /\
               (size t2 + size t1 <= n ->
                rpo_eval rpo_infos n t2 t1 = Some Greater_than)
         | Some Greater_than =>
             forall t2 : term,
             mem equiv t2 (t0 :: l0) ->
             exists t1 : term,
               mem equiv t1 (t :: l) /\
               (size t1 + size t2 <= n ->
                rpo_eval rpo_infos n t1 t2 = Some Greater_than)
         | Some Uncomparable => True
         | None => True
         end).
apply H1''. 
assert (forall t1 t' : term,
       mem equiv t' (t :: l) ->
       mem equiv t1 (t0 :: l0) -> size t' + size t1 <= n).

intros t2 t'.
assert (mem equiv t' (t :: l) -> mem equiv t2 (t0 :: l0) -> size t' + size t2 <= n).
intros H1' H2.
assert (H6':= H6 t' t2).
assert (H0: size t2 + size t' <= n).
auto.
lia. 
assumption.  intros. apply H0; trivial.
clear H1''.
rewrite H in H1'.
assert (H1'':= H1' b); clear H1'.
assert ( exists t1 : term,
           mem equiv t1 (t :: l) /\
           (size t1 + size b <= n ->
            rpo_eval rpo_infos n t1 b = Some Greater_than)).

apply H1''; trivial. clear H1''.
destruct H0. destruct H0.
exists x.
split.
trivial.
assert (rpo_eval rpo_infos n x b = Some Greater_than).
apply H2. 
assert (H6':= H6 b x).
assert (size b + size x <= n).
apply H6'. trivial. trivial.
lia.

assert (H6'':= rpo_eval_is_complete).
assert (H6':= H6'' rpo_infos n x b); clear H6''.
rewrite H2 in H6'.
apply H6'.
assert (H6'':= H6 b x). 
assert (size b + size x <= n).
apply H6''. trivial. trivial.
lia.

assert (H6'':= H6 b x). 
assert (size b + size x <= n).
apply H6''. trivial. trivial.
lia.

intro. 
rewrite H0 in H.

assert (H'':= H' (equiv_eval rpo_infos n) A B); clear H'.
rewrite H0 in H''.
destruct H0. 
destruct H'' as (t1, (t2, (In_t1_A, (In_t2_B, H4)))). 
assert (H2:=  mult_eval_is_sound_weak_equiv).
assert (H2':= H2 rpo_infos n A B); clear H2.
rewrite H in H2'. 
assert ( forall t2 : term,
        mem equiv t2 B ->
        exists t1 : term,
          mem equiv t1 A /\
          (size t1 + size t2 <= n ->
           rpo_eval rpo_infos n t1 t2 = Some Greater_than)).
apply H2';trivial.
intros.
assert (size t' + size t <= n).
apply H1.
trivial. trivial.
lia.
clear H2'.
 
destruct A.
unfold In in In_t1_A.
contradict In_t1_A.
apply (@List_mul _ t A B [] (t::A) B).
rewrite <- app_nil_end.
apply permut_refl.
intros.
reflexivity.
rewrite <- app_nil_end.
apply permut_refl.
intros.
reflexivity.
intros.
assert (H0':= H0 b); clear H0.
assert (exists t1 : term,
          mem equiv t1 (t :: A) /\
          (size t1 + size b <= n ->
           rpo_eval rpo_infos n t1 b = Some Greater_than)).
apply H0'; trivial.
destruct H0.
exists x.
split.
destruct H0.
trivial. 
destruct H0.
assert (H1':= H1 b x).
assert  (size b + size x <= n).
apply H1'; trivial.
assert (size x + size b <= n).
lia.
assert (rpo_eval rpo_infos n x b = Some Greater_than).
apply H3; trivial.
assert (H8:= rpo_eval_is_sound_weak rpo_infos n x b ).
rewrite H7 in H8.
trivial. 
Qed.
 
 
Lemma permut0_rpo_mul_antirefl: forall l1 l2 rpo_infos, permut0 equiv l1 l2 -> rpo_mul (bb rpo_infos) l1 l2 -> False. 
Proof.
  induction l1.
  (* l1 = nil *)
  induction l2.
  (* l2 = nil *)
  intros. apply rpo_mul_antirefl with rpo_infos []. trivial.
  (* l2 = cons *)
  intros. inversion H.
  (* l1 = cons *)
  induction l2.
  (* l2 = nil *)
  intros. inversion H. apply app_eq_nil in H3. destruct H3. discriminate.
  (* l2 = cons *)
  intros. inversion H0. apply (rpo_mul_antirefl rpo_infos (l:=a::l1)).
  eapply List_mul.
  apply H1.
  apply permut0_trans with (a0::l2). apply equiv_equiv. trivial. apply H2.
  trivial.
Qed.

Lemma rpo_mul_permut0_right:  forall rpo_infos l0 l1 l2, permut0 equiv l0 l1 -> rpo_mul (bb rpo_infos)  l2 l0 -> rpo_mul (bb rpo_infos) l2 l1.
Proof.
intros.
inversion H0.
apply List_mul with a lg ls lc. trivial.
apply permut0_trans with l0. apply equiv_equiv.
apply permut0_sym. apply equiv_equiv. trivial. trivial.
trivial.
Qed.

  
Lemma rpo_mul_inclusion_left : forall rpo_infos l1 l2 l3, rpo_mul (bb rpo_infos) (l1++ l2) (l1 ++ l3) -> rpo_mul (bb rpo_infos) l2 l3.
Proof.
induction l1.
simpl. intros. trivial.
intros.
apply IHl1.
assert (((a:: l1) ++ l2) = a :: (l1 ++ l2)).
simpl. trivial.
assert (((a :: l1) ++ l3) = a:: (l1 ++ l3)). 
simpl. trivial.
rewrite H0 in H. rewrite H1 in H.
apply rpo_mul_remove_equiv_aux1 with a a. reflexivity. trivial.
Qed.

Lemma rpo_mul_inclusion_right : forall rpo_infos l1 l2 l3, rpo_mul (bb rpo_infos) (l2++ l1) (l3 ++ l1) -> rpo_mul (bb rpo_infos) l2 l3.
Proof.
induction l1.
intros.
rewrite <- app_nil_end in H. rewrite <- app_nil_end in H. trivial.

intros.
apply IHl1.
assert (rpo_mul (bb rpo_infos) (a:: (l2 ++ l1)) (a :: (l3 ++ l1))).
inversion H.
apply List_mul with a0 lg ls lc.
assert (permut0 equiv (a :: l2 ++ l1) (l2 ++ a :: l1)).
rewrite <- permut0_cons_inside.
apply permut0_refl. auto with typeclass_instances.
auto with typeclass_instances. reflexivity.
apply permut0_trans with (l2 ++ a :: l1). auto with typeclass_instances.
trivial. trivial.
assert (permut0 equiv (a :: l3 ++ l1) (l3 ++ a :: l1)).
rewrite <- permut0_cons_inside. 
apply permut0_refl. auto with typeclass_instances.
auto with typeclass_instances. reflexivity.
apply permut0_trans with (l3 ++ a :: l1). auto with typeclass_instances.
trivial. trivial. trivial.
apply rpo_mul_remove_equiv_aux1 with a a. reflexivity. trivial.
Qed.

Lemma rpo_mul_inclusion_permut0_left : forall rpo_infos l0 l1 l2 l3, permut0 equiv l0 l1 -> rpo_mul (bb rpo_infos) (l0++ l2) (l1 ++ l3) -> rpo_mul (bb rpo_infos) l2 l3.
Proof.
intros.
inversion H0.
assert (permut0 equiv (l1 ++ l2) (ls ++ lc)).
apply permut0_trans with (l0 ++ l2). apply equiv_equiv.
rewrite <- permut0_app2. apply permut0_sym. apply equiv_equiv. trivial. apply equiv_equiv. trivial.
assert (rpo_mul (bb rpo_infos) (l1 ++ l2) (l1 ++ l3)).
apply List_mul with a lg ls lc. trivial. trivial. trivial. 

apply rpo_mul_inclusion_left with l1.  trivial.
Qed. 

Lemma rpo_mul_inclusion_permut0_right : forall rpo_infos l0 l1 l2 l3, permut0 equiv l0 l1 -> rpo_mul (bb rpo_infos) (l2++ l0) (l3 ++ l1) -> rpo_mul (bb rpo_infos) l2 l3.
Proof.
intros.
inversion H0.
assert (permut0 equiv (l2 ++ l1) (ls ++ lc)).
apply permut0_trans with (l2 ++ l0). apply equiv_equiv.
rewrite <- permut0_app1. apply permut0_sym. apply equiv_equiv. trivial. apply equiv_equiv. trivial.
assert (rpo_mul (bb rpo_infos) (l2 ++ l1) (l3 ++ l1)).
apply List_mul with a lg ls lc. trivial. trivial. trivial. 

apply rpo_mul_inclusion_right with l1.  trivial.
Qed. 
  
Lemma list_forall_option_decomposed: forall (A: Type) (f : A -> option bool) (l: list A) (t: A),  f t = Some true  -> (list_forall_option f (t :: l) = Some true <-> list_forall_option f l = Some true).
Proof.
  intros. simpl.
rewrite H. reflexivity.
Qed.

Lemma list_exists_option_decomposed: forall (A: Type) (f : A -> option bool) (l: list A) (t: A),  f t = Some false -> (list_exists_option f (t :: l) = Some true <-> list_exists_option f l = Some true).
Proof.
  intros. simpl.
rewrite H. reflexivity.
Qed.
    
 Lemma list_forall_exists_option_true : forall (A: Type) (f: A -> A -> option bool) (l1 l2 : list A), list_forall_option (fun t2: A => list_exists_option (fun t1: A =>
f t1 t2) l1) l2 = Some true -> (forall t2, In t2 l2 ->  exists t1, In t1 l1 /\ f t1 t2 = Some true).
Proof.
intros.
assert (H1:= @list_forall_option_is_sound A (fun t2 : A => list_exists_option (fun t1 : A => f t1 t2) l1) l2).
rewrite H in H1.
assert (forall a : A,
       In a l2 -> exists t1, In t1 l1 /\ f t1 a = Some true).
intros.
assert (H1':= H1 a).
assert ( list_exists_option (fun t1 : A => f t1 a) l1 = Some true).
apply H1'; trivial.
 
assert (H5:= @list_exists_option_is_sound A (fun t1 : A => f t1 a) l1).
rewrite H3 in H5.
destruct H5.
destruct H4.
exists x.
intros.
split.
assumption. assumption.

assert (H2':= H2 t2).
assert ( exists t1 : A, In t1 l1 /\ f t1 t2 = Some true).
apply H2'; trivial.
destruct H3.
exists x.
intros.
assumption.
Qed.
  
 
Lemma list_forall_exists_option_false : forall (A: Type) (f: A -> A -> option bool) (l1 l2 : list A), list_forall_option (fun t2: A => list_exists_option (fun t1: A =>
f t1 t2) l1) l2 = Some false -> (forall t2, In t2 l2 ->  exists t1, In t1 l1 -> f t1 t2 = Some false) \/ (forall t2 : A,
       In t2 l2 -> exists t1 : A, In t1 l1 -> f t1 t2 = None -> False).
Proof.
intros.
assert (H1:= @list_forall_option_is_sound A (fun t2 : A => list_exists_option (fun t1 : A => f t1 t2) l1) l2).
rewrite H in H1.
destruct H1.
assert (exists a : A,
       In a l2 /\ exists t1, In t1 l1 -> f t1 a = Some false).
destruct H0. destruct H0.
exists x.
split. trivial.
assert (H4:= @list_exists_option_is_sound A (fun t1 : A => f t1 x) l1).
rewrite H2 in H4.
exists x. apply H4.
 
assert (forall a : A, In a l2 -> exists t1, In t1 l1 -> f t1 a = None -> False).
intros.
assert (H2':= H1 a).
assert ( list_exists_option (fun t1 : A => f t1 a) l1 = None -> False).
apply H2'; trivial.
 
assert (H6:= @list_exists_option_is_sound A (fun t1 : A => f t1 a) l1).
case_eq (list_exists_option (fun t1 : A => f t1 a) l1).
intros. destruct b.
rewrite H5 in H6.
destruct H6. destruct H6.
exists x.
intros.
rewrite H9 in H7. discriminate.
rewrite H5 in H6. exists a.
intros.
assert (H6':= H6 a).
assert (f a a =  Some false).
apply H6'; trivial.
rewrite H9 in H8. discriminate.

intros.
rewrite H5 in H6. destruct H6.
destruct H6.
exists x.
intros.
apply H4. trivial.

right. assumption. 
Qed.


Lemma exists_rpo_eval_less_greater: forall rpo_infos n a l2, (forall a'', In a'' l2 -> size a + size a'' <= n) -> (exists a' : term,
         mem equiv a' l2 /\ rpo_eval rpo_infos n a a' = Some Less_than) -> exists a'', In a'' l2 /\ rpo_eval rpo_infos n a'' a = Some Greater_than.
Proof.
intros rpo_infos n a l2 size_a H.
destruct H.
destruct H.
destruct (mem_split_set _ _ equiv_bool_ok _ _ H) as [s'' [lc' [lc'' [s_eq_s'' [H5 _]]]]].
exists s''.
assert (H2:=@rpo_eval_is_sound_weak rpo_infos n a x).
rewrite H0 in H2.
rewrite (equiv_rpo_equiv_1 (bb rpo_infos) s_eq_s'') in H2. 
split. rewrite H5. apply in_or_app. right. simpl. left. trivial.
assert (size_a_s'':= size_a s'').
assert (size a + size s'' <= n).
apply size_a_s''.
rewrite H5. apply in_or_app. right. simpl. left. trivial.
assert (H3:= rpo_eval_is_complete_less_greater rpo_infos H1). apply H3. trivial.
Qed.

Lemma distribute_disj_imply: forall P Q R: Prop, ((P -> Q) /\ (R -> Q)) -> ((P \/ R) -> Q).
Proof.
intros.

destruct H.
destruct H0.
apply H. trivial.
apply H1. trivial.
Qed.

Lemma distribute_impl_conj: forall P Q R: Prop, ((P -> Q) /\ (P -> R)) -> (P -> (Q /\ R)).
Proof.
intros.
destruct H.
split.
apply H. assumption.
apply H1. assumption.
Qed.


Lemma list_gt_list_is_sound_true :
  forall p lg ls, list_gt_list p lg ls = Some true -> (forall s, In s ls -> exists g, In g lg /\ p g s = Some Greater_than).
Proof.
intros.
assert (H1:=@list_gt_list_is_sound p lg ls).
rewrite H in H1.
assert (H1':= H1 s).
apply H1'. trivial.
Qed.
 
Lemma list_gt_list_is_sound_false :
  forall p lg ls,  list_gt_list p lg ls = Some false -> exists s, In s ls /\ forall g, In g lg -> (p  g s = Some Less_than \/ p g s = Some Equivalent \/ p g s = Some Uncomparable).
Proof.

intros p lg ls; revert lg; induction ls as [ | s ls]; intro lg.
unfold list_gt_list; simpl.
intros. 
compute in H. discriminate.


unfold list_gt_list; simpl.
generalize (list_exists_option_is_sound 
  (fun g : term =>
       match p g s with
       | Some Equivalent => Some false
       | Some Less_than => Some false
       | Some Greater_than => Some true
       | Some Uncomparable => Some false
       | None => None
       end) lg).

destruct 
(list_exists_option
    (fun g : term =>
     match p g s with
     | Some Equivalent => Some false
     | Some Less_than => Some false
     | Some Greater_than => Some true
     | Some Uncomparable => Some false
     | None => None
     end) lg) as [[ | ] | ].
intros [g [g_in_ls H]].
generalize (IHls lg); unfold list_gt_list;
destruct 
(list_forall_option
    (fun s0 : term =>
     list_exists_option
       (fun g0 : term =>
        match p g0 s0 with
        | Some Equivalent => Some false
        | Some Less_than => Some false
        | Some Greater_than => Some true
        | Some Uncomparable => Some false
        | None => None
        end) lg) ls) as [[ | ] | ].
intros. discriminate.
intros.
 
destruct (p g s) as [[ | | | ] | ]. discriminate. discriminate.
assert (exists s : term,
         In s ls /\
         (forall g : term,
          In g lg ->
          (p g s = Some Less_than \/
           p g s = Some Equivalent \/ p g s = Some Uncomparable))).
apply H0; trivial.
destruct H2.
exists x.
destruct H2.
split.
right. trivial. assumption. discriminate. discriminate.

intros. discriminate.

destruct 
(list_forall_option
    (fun s0 : term =>
     list_exists_option
       (fun g0 : term =>
        match p g0 s0 with
        | Some Equivalent => Some false
        | Some Less_than => Some false
        | Some Greater_than => Some true
        | Some Uncomparable => Some false
        | None => None
        end) lg) ls) as [[ | ] | ].
intros.

exists s.
split. left; trivial.
intros.
assert (H':= H g). assert (match p g s with
       | Some Equivalent => Some false
       | Some Less_than => Some false
       | Some Greater_than => Some true
       | Some Uncomparable => Some false
       | None => None
       end = Some false).
apply H'; trivial.
case_eq (p g s).
destruct c.
intros. rewrite H3 in H2.
right. left; trivial.
intros. rewrite H3 in H2. left; trivial. 
intros. rewrite H3 in H2. discriminate.
intros. rewrite H3 in H2. right. right. trivial.
intros.  rewrite H3 in H2. discriminate.

intros.

exists s.
split. left; trivial.
intros.
assert (H':= H g). assert (match p g s with
       | Some Equivalent => Some false
       | Some Less_than => Some false
       | Some Greater_than => Some true
       | Some Uncomparable => Some false
       | None => None
       end = Some false).
apply H'; trivial.
case_eq (p g s).
destruct c.
intros. rewrite H3 in H2.
right. left; trivial.
intros. rewrite H3 in H2. left; trivial. 
intros. rewrite H3 in H2. discriminate.
intros. rewrite H3 in H2. right. right. trivial.
intros.  rewrite H3 in H2. discriminate.

intros. discriminate.

intros. discriminate.
Qed.


Lemma list_gt_list_is_sound_none:   forall p lg ls,  list_gt_list p lg ls = None -> (exists t1: term, In t1 ls /\ ((exists t2:term, In t2 lg /\ p t2 t1 = None) /\
       (forall t2, In t2 lg -> p t2 t1 = Some Greater_than -> False))).
Proof.
intros.
case_eq (list_gt_list p lg ls).
intros.
destruct b. rewrite H in H0. discriminate.
rewrite H in H0. discriminate.
intros.
unfold list_gt_list in H0.
assert (H1 := @list_forall_option_is_sound term (fun s : term =>
          list_exists_option
            (fun g : term =>
             match p g s with
             | Some Equivalent => Some false
             | Some Less_than => Some false
             | Some Greater_than => Some true
             | Some Uncomparable => Some false
             | None => None
             end) lg) ls).
rewrite H0 in H1.
destruct H1.
destruct H1.
assert (H3:= @list_exists_option_is_sound term (fun g : term =>
          match p g x with
          | Some Equivalent => Some false
          | Some Less_than => Some false
          | Some Greater_than => Some true
          | Some Uncomparable => Some false
          | None => None
          end) lg).
rewrite H2 in H3.
destruct H3. 
exists x. split. trivial.
split.
destruct H3.
exists x0.
case_eq (p x0 x).
intros. destruct c.
rewrite H5 in H3.
destruct H3.
discriminate. rewrite H5 in H3. destruct H3. discriminate.
rewrite H5 in H3. destruct H3. discriminate.
rewrite H5 in H3. destruct H3. discriminate.
intros. rewrite H5 in H3. destruct H3. split. assumption. trivial.
intros.
assert (H4' := H4 t2).
rewrite H6 in H4'.
apply H4'. trivial. trivial.
Qed.

Lemma list_gt_list_is_complete_true:
  forall p lg ls, ( forall s, In s ls -> exists g, In g lg /\ p g s = Some Greater_than) ->  list_gt_list p lg ls = Some true.
Proof.   
induction ls.
intros.
compute.
trivial.
intros.
unfold list_gt_list.
apply list_forall_option_is_complete_true.
intros.
apply list_exists_option_is_complete_true.
assert (H1:= H a0).
assert (exists g : term, In g lg /\ p g a0 = Some Greater_than).
apply H1; trivial.
destruct H2.
destruct H2.
exists x.
split; trivial.
rewrite H3.
trivial.
Qed.
  
Lemma list_gt_list_is_complete_false: 
  forall p lg ls, (forall g s, In g lg -> In s ls -> p g s <> None) -> (exists s, In s ls /\ forall g, In g lg -> (p  g s = Some Less_than \/ p g s = Some Equivalent \/ p g s = Some Uncomparable)) ->  list_gt_list p lg ls = Some false.
Proof.
induction ls.
intros. 
simpl in H.
destruct H0. destruct H0.
contradiction.

intros.
unfold list_gt_list.
apply list_forall_option_is_complete_false.
destruct H0.
exists x.
destruct H0.
split. trivial.
apply list_exists_option_is_complete_false.
intros.
assert (H3:= H1 a0).
assert ( p a0 x = Some Less_than \/
       p a0 x = Some Equivalent \/ p a0 x = Some Uncomparable).
apply H3; trivial.
destruct H4. 
rewrite H4. trivial.
destruct H4; rewrite H4; trivial.
intros.
assert (H3:= @list_exists_option_is_sound term (fun g : term =>
          match p g a0 with
          | Some Equivalent => Some false
          | Some Less_than => Some false
          | Some Greater_than => Some true
          | Some Uncomparable => Some false
          | None => None
          end) lg).
rewrite H2 in H3.
destruct H3.
destruct H3. destruct H3.
assert (H4':= H4 x).
assert (match p x a0 with
        | Some Equivalent => Some false
        | Some Less_than => Some false
        | Some Greater_than => Some true
        | Some Uncomparable => Some false
        | None => None
        end = Some true -> False).
apply H4'; trivial.
apply H6.
case_eq (p x a0).
intros. destruct c.
rewrite H7 in H5. discriminate.
rewrite H7 in H5. discriminate.
trivial.
rewrite H7 in H5. discriminate.
intros.
rewrite H7 in H5. 
assert (H8:= H x a0).
apply H8 in H7. contradiction.
trivial. trivial.
Qed.

Lemma list_gt_list_cons_right_true: forall p lg ls a, list_gt_list p lg (a::ls) = Some true -> list_gt_list p lg ls = Some true.
Proof.
unfold list_gt_list.
intros.
apply list_gt_list_is_complete_true.
assert (H1:= @list_forall_option_is_sound term (fun s : term =>
         list_exists_option
           (fun g : term =>
            match p g s with
            | Some Equivalent => Some false
            | Some Less_than => Some false
            | Some Greater_than => Some true
            | Some Uncomparable => Some false
            | None => None
            end) ( lg)) (a:: ls) ).
rewrite H in H1. clear H.
intros.
assert (H1':= H1 s). clear H1.
assert (list_exists_option
          (fun g : term =>
           match p g s with
           | Some Equivalent => Some false
           | Some Less_than => Some false
           | Some Greater_than => Some true
           | Some Uncomparable => Some false
           | None => None
           end) ( lg) = Some true).
apply H1'. simpl. right. trivial.
assert (H0':= @list_exists_option_is_sound term (fun g : term =>
          match p g s with
          | Some Equivalent => Some false
          | Some Less_than => Some false
          | Some Greater_than => Some true
          | Some Uncomparable => Some false
          | None => None
          end) (lg)).
rewrite H0 in H0'. destruct H0'. destruct H1.
exists x.
split. trivial.
case_eq (p x s).
intros. destruct c.
rewrite H3 in H2. discriminate.
rewrite H3 in H2. discriminate.
trivial.
rewrite H3 in H2. discriminate.
intros. rewrite H3 in H2. discriminate.
Qed.

Lemma list_gt_list_cons_right_true_1: forall p lg ls a, (exists a', In a' lg /\ p a' a = Some Greater_than) -> list_gt_list p lg ls = Some true -> list_gt_list p lg (a :: ls) = Some true.
Proof.
intros.
apply list_gt_list_is_complete_true.
unfold list_gt_list in H0.
intros.
assert (H0':= @list_forall_option_is_sound term (fun s : term =>
          list_exists_option
            (fun g : term =>
             match p g s with
             | Some Equivalent => Some false
             | Some Less_than => Some false
             | Some Greater_than => Some true
             | Some Uncomparable => Some false
             | None => None
             end) lg) ls).
rewrite H0 in H0'.
simpl in H1.
destruct H1. clear H0.
rewrite <- H1. clear H1 s.
assumption.
clear H0.
assert (H0'':= H0' s).
clear H0'. assert ( list_exists_option
           (fun g : term =>
            match p g s with
            | Some Equivalent => Some false
            | Some Less_than => Some false
            | Some Greater_than => Some true
            | Some Uncomparable => Some false
            | None => None
            end) lg = Some true).
apply H0''. trivial. clear H0''.
assert (H2:= @list_exists_option_is_sound term (fun g : term =>
          match p g s with
          | Some Equivalent => Some false
          | Some Less_than => Some false
          | Some Greater_than => Some true
          | Some Uncomparable => Some false
          | None => None
          end) lg ). 
rewrite H0 in H2.
destruct H2.
destruct H2.
exists x.
split. trivial.
case_eq (p x s).
intros. destruct c.
rewrite H4 in H3. discriminate.
rewrite H4 in H3. discriminate.
trivial.
rewrite H4 in H3. discriminate.
intros. rewrite H4 in H3. discriminate.
Qed.


   
Lemma  list_gt_list_cons_left_true: forall p lg ls a, list_gt_list p lg ls = Some true -> list_gt_list p (a::lg) ls = Some true.
Proof.
unfold list_gt_list.
intros.
apply list_gt_list_is_complete_true.
assert (H1:= @list_forall_option_is_sound term (fun s : term =>
         list_exists_option
           (fun g : term =>
            match p g s with
            | Some Equivalent => Some false
            | Some Less_than => Some false
            | Some Greater_than => Some true
            | Some Uncomparable => Some false
            | None => None
            end) lg) ls).
rewrite H in H1. clear H.
intros.
assert (H1':= H1 s). clear H1.
assert (list_exists_option
          (fun g : term =>
           match p g s with
           | Some Equivalent => Some false
           | Some Less_than => Some false
           | Some Greater_than => Some true
           | Some Uncomparable => Some false
           | None => None
           end) lg = Some true).
apply H1'; trivial. clear H1'.
assert (H1:=@list_exists_option_is_sound term (fun g : term =>
          match p g s with
          | Some Equivalent => Some false
          | Some Less_than => Some false
          | Some Greater_than => Some true
          | Some Uncomparable => Some false
          | None => None
          end) lg).
rewrite H0 in H1. clear H0.
destruct H1. destruct H0.
exists x. split.
simpl. right. trivial.

case_eq (p x s).
intros. destruct c.
rewrite H2 in H1. discriminate.
rewrite H2 in H1. discriminate.
trivial.
rewrite H2 in H1. discriminate.
intros. rewrite H2 in H1. discriminate.
Qed.

  
Lemma  list_gt_list_cons_left_true_1: forall p lg ls a, (forall a', In a' ls -> p a a' <> Some Greater_than) -> list_gt_list p (a::lg) ls = Some true -> list_gt_list p lg ls = Some true.
Proof.
intros.
apply list_gt_list_is_complete_true.
unfold list_gt_list in H0.
intros.
assert (H0':= @list_forall_option_is_sound term (fun s : term =>
          list_exists_option
            (fun g : term =>
             match p g s with
             | Some Equivalent => Some false
             | Some Less_than => Some false
             | Some Greater_than => Some true
             | Some Uncomparable => Some false
             | None => None
             end) (a::lg)) ls).
rewrite H0 in H0'.
simpl in H1.
assert (H2:= H0' s).

assert (list_exists_option
         (fun g : term =>
          match p g s with
          | Some Equivalent => Some false
          | Some Less_than => Some false
          | Some Greater_than => Some true
          | Some Uncomparable => Some false
          | None => None
          end) (a :: lg) = Some true).
apply H2; trivial. clear H0' H2 H0.
assert (H4 := @list_exists_option_is_sound term (fun g : term =>
          match p g s with
          | Some Equivalent => Some false
          | Some Less_than => Some false
          | Some Greater_than => Some true
          | Some Uncomparable => Some false
          | None => None
          end) (a :: lg)). 
rewrite H3 in H4. clear H3.
destruct H4. destruct H0.
simpl in H0. destruct H0.
rewrite H0 in H.
assert (H':= H s).
case_eq (p x s).
intros. destruct c.
rewrite H3 in H2. discriminate.
rewrite H3 in H2. discriminate.
rewrite H3 in H2. rewrite H3 in H'.
assert (Some Greater_than <> Some Greater_than).
apply H'; trivial. contradict H4. trivial.
rewrite H3 in H2. discriminate.
intros. rewrite H3 in H2. discriminate.
exists x.
split.
trivial.
case_eq (p x s).
intros. destruct c.
rewrite H3 in H2. discriminate.
rewrite H3 in H2. discriminate.
trivial.
rewrite H3 in H2. discriminate.
intros. rewrite H3 in H2. discriminate.
Qed. 
 
Lemma mult_eval_greater_less: forall p lg ls, mult_eval p lg ls = Some Greater_than /\ (list_gt_list p ls lg = Some false) -> mult_eval p ls lg = Some Less_than.
Proof.
intros.  
unfold mult_eval in H.
case_eq (list_gt_list p lg ls). intros. destruct b. rewrite H0 in H. 
unfold mult_eval. rewrite H0.
destruct H.
case_eq (list_gt_list p ls lg). destruct b.
intros.
rewrite H2 in H1. discriminate.
intros. trivial.
intros. rewrite H2 in H1. discriminate.
rewrite H0 in H.
destruct H. rewrite H1 in H. discriminate.
destruct H.
intros.
rewrite H0 in H.
rewrite H1 in H. discriminate.
Qed.
 

Lemma list_forall_option_is_complete_none :
  forall (A : Type) f l, (exists a, In a l /\ f a = None) ->
    @list_forall_option A f l = None.
Proof.
intros A f l; induction l as [ | a l].
simpl. intros. destruct H. destruct H. contradiction.
intros.
simpl in H.
assert ((exists a0, a = a0 /\ f a0 = None) \/ (exists a0, In a0 l /\ f a0 = None)).
destruct H.
destruct H.
destruct H.
left.
exists x.
split; trivial.
right. exists x.
split;trivial.
destruct H0.
destruct H0.
destruct H0.
simpl.
rewrite H0.
rewrite H1. trivial.

simpl.
case_eq (f a).
intros. destruct b.
apply IHl. assumption.

case_eq (list_forall_option f l). intros.
assert (list_forall_option f l = None).
apply IHl. assumption.
rewrite H2 in H3. discriminate.
intros. trivial.
intros. 
trivial.
Qed.
  
 
Lemma list_gt_list_is_complete_none_1: 
  forall p lg ls, list_gt_list p lg ls <> Some true -> list_gt_list p lg ls <> Some false ->  list_gt_list p lg ls =  None.
Proof.
intros.
case_eq (list_gt_list p lg ls).
intros.
destruct b.
contradict H.
trivial.
contradict H0.
trivial.
intros.
trivial. 
Qed.

Lemma list_gt_list_is_complete_none: 
  forall p lg ls, (exists t1: term, In t1 ls /\ ((exists t2:term, In t2 lg /\ p t2 t1 = None) /\
       (forall t2, In t2 lg -> p t2 t1 = Some Greater_than -> False)))  ->  list_gt_list p lg ls =  None.
Proof.
intros.
unfold list_gt_list.
apply list_forall_option_is_complete_none.
destruct H.
exists x.
split.
destruct H. trivial.
destruct H.
destruct H0.
destruct H0.
destruct H0.
apply list_exists_option_is_complete_none.
exists x0.
split. trivial.
rewrite H2. trivial.
intros.
assert (H1':= H1 a).
apply H1'.
trivial.
case_eq (p a x).
intros.
destruct c.
rewrite H5 in H4. discriminate.
rewrite H5 in H4. discriminate.
trivial.
rewrite H5 in H4. discriminate.
intros.
rewrite H5 in H4. discriminate.
Qed. 
  
  
Lemma forall_not :
   forall (V: Type) (P : V -> Prop),  ~ (exists x : V, P x) -> forall x : V, ~ P x.
Proof.
firstorder.
Qed.
 


Lemma not_forall: forall (V:Type)(P : V -> Prop), (exists x : V,  ~ P x) -> ~ (forall x : V,  P x). 
Proof.
intros.
unfold not.
intros.
firstorder.
Qed.

Lemma exists_not_impl: forall l2 a1 l1 n rpo_infos, (exists x,  (In x l2) /\
      ~ (exists g : term,
        In g (a1 :: l1) /\ rpo_eval rpo_infos n g x = Some Greater_than))->(exists x : term,
     ~
     (In x l2 ->
      exists g : term,
        In g (a1 :: l1) /\ rpo_eval rpo_infos n g x = Some Greater_than)).
Proof.
(*SLOW*)firstorder.
Qed.

Lemma exists_exists_not :  forall l2 a1 l1 n rpo_infos, 
  (exists x,  (In x l2) /\
      (forall g : term,
       ~ In g (a1 :: l1) \/ rpo_eval rpo_infos n g x <> Some Greater_than)) ->
  (exists x,  (In x l2) /\
      ~ (exists g : term,
        In g (a1 :: l1) /\ rpo_eval rpo_infos n g x = Some Greater_than)).
Proof.
(*SLOW*)firstorder.
Qed.
 
 
Lemma list_gt_list_cons_commute_right_true:  forall  p l1 l2 a1 a2, list_gt_list p l2 (a1:: a2 :: l1) = Some true -> list_gt_list p l2 (a2 :: a1 :: l1)  = Some true.
Proof.
intros.
apply list_gt_list_is_complete_true.
assert (H1':= @list_gt_list_is_sound_true p  l2 (a1 :: a2 :: l1)).
assert (forall s : term,
        In s (a1 :: a2 :: l1) ->
        exists g : term, In g l2 /\ p g s = Some Greater_than).
apply H1'; trivial.
intros.
assert (H0':= H0 s).
apply H0'.
simpl.
simpl in H1.
tauto.
Qed.
 
 

Theorem antisym_rpo: forall rpo_infos n a b, size a + size b <= n -> (rpo rpo_infos.(bb) a b) /\ (rpo rpo_infos.(bb) b a) -> False.
Proof.
intros.
destruct H0. 
assert (H2:= rpo_eval_is_complete_less_greater).
assert (H3:= H2 rpo_infos n a b).
assert (H4:= H2 rpo_infos n b a).
assert (size b + size a <= n).
lia.
assert (rpo_eval rpo_infos n a b = Some Less_than
           /\ rpo_eval rpo_infos n b a =
             Some Greater_than).
apply H3; trivial.
assert (rpo_eval rpo_infos n b a = Some Less_than
           /\ rpo_eval rpo_infos n a b =
             Some Greater_than).
apply H4; trivial.
destruct H6.
destruct H7.
rewrite H6 in H9.
contradict H9.
discriminate.
Qed.

Lemma mem_concat: forall a ls lc, mem equiv a (ls ++ lc) -> mem equiv a ls \/ mem equiv a lc.
Proof. 
induction ls.
simpl.
intros.
right; trivial.
intros.
simpl.
simpl in H.
destruct H.
left; left; trivial.
assert (H1:= IHls lc).
assert (mem equiv a ls \/ mem equiv a lc).
apply H1; trivial.
tauto.
Qed.

Lemma mem_concat_1: forall a ls lc, mem equiv a ls -> mem equiv a (ls ++ lc).
Proof.
induction ls.
intros.
simpl in H.
contradiction.
intros.
simpl. simpl in H.
destruct H.
left; trivial.
assert (H0:= IHls lc).
right.
apply H0; trivial.
Qed.
 
 
End S.
End Make.
