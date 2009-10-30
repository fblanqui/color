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


Require Import Bool.
Require Import List.
Require Import closure.
Require Import more_list.
Require Import equiv_list.
Require Import list_permut.
Require Import dickson.
Require Import Relations.
Require Import Wellfounded.
Require Import Arith.
Require Import Wf_nat.
Require Import term_spec.
Require Import term.
Require Import decidable_set.
Require Import ordered_set.
Require Import Recdef.
Require Import Program.
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
  prec_bool : A -> A -> bool;
  prec_bool_ok : forall a1 a2, match prec_bool a1 a2 with true => prec a1 a2 | false => ~prec a1 a2 end;
  prec_antisym : forall s, prec s s -> False;
  prec_transitive : transitive A prec
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
      forall f l1 l2, status P f = Lex -> equiv_list_lex l1 l2 -> 
        equiv (Term f  l1) (Term f l2) 
    | Eq_mul :
      forall f l1 l2,  status P f = Mul -> permut0 equiv l1 l2 ->
        equiv (Term f l1) (Term f l2)

    with equiv_list_lex : list term -> list term -> Prop :=
    | Eq_list_nil : equiv_list_lex nil nil
    | Eq_list_cons : 
      forall t1 t2 l1 l2, equiv t1 t2 -> equiv_list_lex l1 l2 ->
        equiv_list_lex (t1 :: l1) (t2 :: l2).

    Parameter equiv_in_list : 
      forall f (f_stat : status P f= Lex) l1 l2, length l1 = length l2 ->
        (forall t1 t2, In (t1, t2) (combine l1 l2) -> equiv  t1  t2) -> 
        equiv (Term f l1) (Term f l2).

(* equiv is actually an equivalence *)
    Parameter equiv_equiv  : equivalence term equiv.

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
      forall f l l', status P f = Lex -> (length l = length l' \/ (length l' <= bb /\ length l <= bb)) -> rpo_lex bb l' l -> 
        (forall s', mem equiv s' l' -> rpo bb s' (Term f l)) ->
        rpo bb (Term f l') (Term f l)
    | Top_eq_mul : 
      forall f l l', status P f = Mul -> rpo_mul bb l' l -> 
        rpo bb (Term f l') (Term f l)

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
     forall f l1 l2, status Prec f = Lex -> equiv_list_lex l1 l2 -> 
     equiv (Term f  l1) (Term f l2) 
  | Eq_mul :
     forall f l1 l2,  status Prec f = Mul -> permut0 equiv l1 l2 ->
     equiv (Term f l1) (Term f l2)

with equiv_list_lex : list term -> list term -> Prop :=
   | Eq_list_nil : equiv_list_lex nil nil
   | Eq_list_cons : 
       forall t1 t2 l1 l2, equiv t1 t2 -> equiv_list_lex l1 l2 ->
       equiv_list_lex (t1 :: l1) (t2 :: l2).

Lemma equiv_same_top :
  forall f g l l', equiv (Term f l) (Term g l') -> f = g.
Proof.
intros f g l l' H; inversion H; subst; trivial.
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
intros f1 f2 l1 l2 t1_eq_t2; 
inversion t1_eq_t2 as [ | f l1' l2' _ l1_eq_l2 | f l1' l2' _ P]; clear t1_eq_t2; 
subst.
trivial.
apply equiv_list_lex_same_length; assumption.
apply (@permut_length _ equiv); trivial.
Qed.

Lemma equiv_same_size :
  forall t t', equiv t t' -> size t = size t'.
Proof.
intros t; pattern t; apply term_rec2; clear t.
intro n; induction n as [ | n]; intros t1 St1 t2 t1_eq_t2.
absurd (1 <= 0); auto with arith; apply le_trans with (size t1); trivial;
apply size_ge_one.
inversion t1_eq_t2 as [ | f l1' l2' _ l1_eq_l2 | f l1' l2' _ P]; clear t1_eq_t2; 
subst.
trivial.
(* Lex case *)
do 2 rewrite size_unfold; apply (f_equal (fun n => 1 + n)).
generalize l2' l1_eq_l2; clear l2' l1_eq_l2; 
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
    forall f (f_stat : status Prec f= Lex) l1 l2, length l1 = length l2 ->
      (forall t1 t2, In (t1, t2) (combine l1 l2) -> equiv  t1  t2) -> 
      equiv (Term f l1) (Term f l2).
Proof.
intros f f_stat l1 l2 L E; apply (Eq_lex f f_stat).
clear f f_stat; revert l1 l2 L E; fix 1; intro l1; case l1; clear l1.
intros l2; case l2; clear l2.
intros _ _; apply Eq_list_nil.
intros a2 l2 L _; discriminate.
intros a1 l1 l2; case l2; clear l2.
intro L; discriminate.
intros a2 l2 L E; apply Eq_list_cons.
apply E; left; apply refl_equal.
apply (equiv_in_list l1 l2).
injection L; intros; assumption.
intros t1 t2 H; apply E; right; assumption.
Qed.

(* equiv is actually an equivalence *)
Lemma equiv_equiv  : equivalence term equiv.
Proof.
split.
(* Reflexivity *)
intro t; apply Eq.
(* Transitivity *)
intros t1; pattern t1; apply term_rec3.
(* 1/3 variable case *)
intros v t2 t3 t1_eq_t2 t2_eq_t3; inversion t1_eq_t2; subst; trivial.
(* 1/2 compound case *)
intros f l1 E_l1 t2 t3 t1_eq_t2 t2_eq_t3; 
inversion t1_eq_t2 as [ | f' l1' l2 Sf l1_eq_l2 H2 H' | f' l1' l2 Sf P]; subst; trivial;
inversion t2_eq_t3 as [ | f' l2' l3 Sf' l2_eq_l3 H2 H'' | f' l2' l3 Sf' P' ]; subst; trivial.
(* 1/5 Lex case *)
apply Eq_lex; trivial.
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
rewrite Sf in Sf'; discriminate.
(* 1/3 absurd case *)
rewrite Sf in Sf'; discriminate.
(* 1/2 Mul case *)
apply Eq_mul; trivial.
apply permut_trans with l2; trivial.
intros a b c a_in_l1 _ _; apply E_l1; trivial.
(* Symmetry *)
intros t1; pattern t1; apply term_rec3; clear t1.
intros v t2 t1_eq_t2; inversion t1_eq_t2; subst; trivial.
intros f l1 IHl t2 t1_eq_t2; 
inversion t1_eq_t2 as 
  [ 
  | f' l1' l2 Sf l1_eq_l2 
  | f' l1' l2 Sf P]; clear t1_eq_t2; subst.
apply Eq.
apply Eq_lex; trivial.
generalize l2 l1_eq_l2; clear l2 l1_eq_l2; 
induction l1 as [ | t1 l1]; intros l2 l1_eq_l2;
inversion l1_eq_l2 as [ | s1 s2 l1' l2' s1_eq_s2 l1'_eq_l2']; subst; trivial.
apply Eq_list_cons.
apply IHl; trivial; left; trivial.
apply IHl1; trivial.
intros t t_in_l1; apply IHl; right; trivial.
apply Eq_mul; trivial.
apply permut_sym; trivial.
intros a b a_in_l1 _; apply IHl; trivial.
Qed.

  Add Relation term equiv 
  reflexivity proved by (Relation_Definitions.equiv_refl _ _ equiv_equiv)
    symmetry proved by (Relation_Definitions.equiv_sym _ _ equiv_equiv)
      transitivity proved by (Relation_Definitions.equiv_trans _ _ equiv_equiv) as EQUIV_RPO.


Definition equiv_bool_F := 
(fun (equiv_bool : term -> term -> bool) (t1 t2 : term) =>
match t1, t2 with
| Var v1, Var v2 => X.eq_bool v1 v2
| Var _, Term _ _ => false
| Term _ _, Var _ => false
| Term f1 l1, Term f2 l2 =>
    if F.Symb.eq_bool f1 f2
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
exact (refl_equal _).

exists false; intros [ | p] p_lt_k def.
apply False_ind; exact (gt_irrefl 0 p_lt_k).
exact (refl_equal _).

exists false; intros [ | p] p_lt_k def.
apply False_ind; exact (le_Sn_O _ p_lt_k).
exact (refl_equal _).

rewrite size_unfold.
assert ({v : bool |
  forall k : nat,
  list_size size l1 <= k ->
  forall def : term -> term -> bool,
  iter (term -> term -> bool) (S k) equiv_bool_F def (Term f1 l1) (Term f2 l2) = v}).
unfold iter; simpl.
case (F.Symb.eq_bool f1 f2).
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
exists true; intros k p_lt_k def; exact (refl_equal _).
exists false; intros k p_lt_k def; exact (refl_equal _).
intros a1 k1 IHl1 l2; case l2.
exists false; intros k p_lt_k def; exact (refl_equal _).
intros a2 k2; case (equiv_lex_bool k1 (tail_set _ IHl1) k2); intros bl IH'.
case (IHl1 a1 (or_introl _ (refl_equal _)) a2); intros ba IH''.
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
exists true; intros k p_lt_k def; exact (refl_equal _).
exists false; intros k p_lt_k def; exact (refl_equal _).
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
case (IH a1 (or_introl _ (refl_equal _)) a2); intro v; case v; intro Ha1.
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

exists false; intros _ _ _; exact (refl_equal _).

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
    if F.Symb.eq_bool f1 f2
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
case (F.Symb.eq_bool f1 f2); [idtac | reflexivity].
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
rewrite (H' g1 g2 (IH a1 (or_introl _ (refl_equal _)))).
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
generalize (F.Symb.eq_bool_ok f1 f2); case (F.Symb.eq_bool f1 f2).
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
intros a2 l2; simpl; generalize (IH a1 (or_introl _ (refl_equal _)) a2).
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
intro l1_eq_l2; rewrite <- f1_eq_f2; apply Eq_lex; assumption.
intros l1_diff_l2 t1_eq_t2; inversion t1_eq_t2; subst l2.
apply l1_diff_l2; generalize l1; intro l; induction l as [ | a l].
apply Eq_list_nil.
apply Eq_list_cons; [apply Eq | assumption].
apply l1_diff_l2; assumption.
subst f2; rewrite Lex_f1 in H2; discriminate.
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
generalize (IH a1 (or_introl _ (refl_equal _)) a2); case (equiv_bool a1 a2).
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
intro P; rewrite <- f1_eq_f2; apply Eq_mul; assumption.
rewrite <- f1_eq_f2; intros not_P t1_eq_t2.
inversion t1_eq_t2; subst l2.
apply not_P; apply permut_refl; intros; reflexivity.
rewrite Mul_f1 in H2; discriminate.
apply not_P; assumption.
intros f1_diff_f2 t1_eq_t2; apply f1_diff_f2; inversion t1_eq_t2; reflexivity.
Defined.

Lemma equiv_dec :
  forall t1 t2, {equiv t1 t2}+{~equiv t1 t2}.
Proof.
intros t1 t2; generalize (equiv_bool_ok t1 t2); case (equiv_bool t1 t2).
left; assumption.
right; assumption.
Defined.

(*
Module Term_equiv_dec : 
   decidable_set.ES with Definition A:= term 
                             with Definition eq_A := equiv
                             with Definition eq_bool := equiv_bool
                             with Definition eq_bool_ok := equiv_bool_ok.
                             
Definition A := term.
Definition eq_A := equiv.
Definition eq_proof := equiv_equiv.
Definition eq_bool := equiv_bool.
Definition eq_bool_ok := equiv_bool_ok.

  Add Relation A eq_A 
  reflexivity proved by (Relation_Definitions.equiv_refl _ _ eq_proof)
    symmetry proved by (Relation_Definitions.equiv_sym _ _ eq_proof)
      transitivity proved by (Relation_Definitions.equiv_trans _ _ eq_proof) as EQA.

End Term_equiv_dec.

Module Import LP := list_permut.Make (Term_equiv_dec).
*)

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
        forall f l l', status Prec f = Lex -> (length l = length l' \/ (length l' <= bb /\ length l <= bb)) -> rpo_lex bb l' l -> 
        (forall s', mem equiv s' l' -> rpo bb s' (Term f l)) ->
        rpo bb (Term f l') (Term f l)
  | Top_eq_mul : 
        forall f l l', status Prec f = Mul -> rpo_mul bb l' l -> 
        rpo bb (Term f l') (Term f l)

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
inversion t_eq_t' as [ t'' | f  l1 l2 Stat H | f l1 l2 Stat P]; subst.
(* 1/4 equivalence is syntactic identity *)
trivial.
(* 1/3 equivalence with Lex top symbol *)
inversion s_lt_t as  [g l t'' t' t'_mem_l t''_le_t'
                            | g g' l l' g_prec_f l'_lt_t
                            | g l l' Stat' L l'_lt_ll1 l'_lt_t
                            | g l l' Stat' l'_lt_ll1 ]; subst.
(* 1/6 equivalence with Lex top symbol , Subterm *)
destruct t''_le_t' as [t'' t' t''_eq_t' | t'' t' t''_lt_t'];
apply Subterm with t'; trivial.
rewrite <- (mem_mem t' H); trivial.
apply Equiv; trivial.
rewrite <- (mem_mem t' H); trivial.
apply Lt; trivial.
(* 1/5 equivalence with Lex top symbol,  Top_gt *)
apply Top_gt; trivial.
intros s' s'_mem_l'.
apply (IH (s',(Term f l1))); trivial.
apply size2_lex1_mem; trivial.
apply l'_lt_t; trivial.
(* 1/4 equivalence with Lex top symbol,  Top_eq_lex *)
apply Top_eq_lex; trivial.
rewrite <- (equiv_list_lex_same_length H); assumption.
clear t_eq_t' l'_lt_t s_lt_t L; revert l2 l' l'_lt_ll1 IH H. 
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
rewrite Stat in Stat'; discriminate.
(* 1/2 equivalence with Mul top symbol *)
inversion s_lt_t as  [g l t'' t' t'_mem_l t''_le_t'
                            | g g' l l' g_prec_f l'_lt_t
                            | g l l' Stat' L' l'_lt_l1 l'_lt_t
                            | g l l' Stat' l'_lt_l1 ]; subst.
(* 1/5 equivalence with Mul top symbol , Subterm *)
destruct t''_le_t' as [t'' t' t''_eq_t' | t'' t' t''_lt_t'];
apply Subterm with t'; trivial.
rewrite <- (mem_permut0_mem equiv_equiv  t' P); trivial.
apply Equiv; trivial.
rewrite <- (mem_permut0_mem equiv_equiv t' P); trivial.
apply Lt; trivial.
(* 1/4 equivalence with Mul top symbol,  Top_gt *)
apply Top_gt; trivial.
intros s' s'_mem_l2.
apply (IH (s', Term f l1)); trivial.
apply size2_lex1_mem; trivial.
apply l'_lt_t; trivial.
(* 1/3 equivalence with Mul top symbol,  Top_eq_lex *)
rewrite Stat in Stat'; discriminate.
(* 1/2 equivalence with Mul top symbol,  Top_eq_mul *)
apply Top_eq_mul; trivial.
inversion l'_lt_l1 as [a lg ls lc l'' l''' Q1 Q2 ls_lt_alg]; subst.
apply (@List_mul bb a lg ls lc); trivial.
apply (permut0_trans equiv_equiv) with l1.
apply (permut0_sym equiv_equiv). trivial. 
exact Q2.

intros t t' t_eq_t' s; split.
apply (H (s,t)); trivial.
apply (H (s,t')); trivial.
apply (Relation_Definitions.equiv_sym _ _ equiv_equiv); trivial.
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
inversion t_eq_t' as [ t'' | g l1 l2 Stat l1_eq_l2 | g l1 l2 Stat P]; subst.
(* 1/4 equivalence is syntactic identity *)
trivial.
(* 1/3 equivalence with Lex top symbol *)
inversion t_lt_s as  [f l t'' t' t'_mem_l t''_le_t'
                            | f f' l l' g_prec_f l'_lt_s
                            | f l l' Stat' L ll1_lt_l ll_lt_s
                            | f l l' Stat' ll1_lt_l ]; subst.
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
intros s' s'_mem_l2; apply l'_lt_s.
rewrite (@mem_mem s' l1 l2); trivial.
(* 1/4 equivalence with Lex top symbol,  Top_eq_lex *)
apply Top_eq_lex; trivial.
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
rewrite Stat in Stat'; discriminate.
(* 1/2 equivalence with Mul top symbol *)
inversion t_lt_s as  [f l t'' t' t'_mem_l t''_le_t'
                            | f f' l l' g_prec_f l'_lt_s
                            | f l l' Stat' L ll1_lt_l ll_lt_s
                            | f l l' Stat' ll1_lt_l ]; subst.
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
intros s' s'_mem_l2; apply l'_lt_s.
rewrite (mem_permut0_mem equiv_equiv s' P); trivial.
(* 1/3 equivalence with Mul top symbol,  Top_eq_lex *)
rewrite Stat in Stat'; discriminate.
(* 1/3 equivalence with Mul top symbol,  Top_eq_mul *)
apply Top_eq_mul; trivial.
inversion ll1_lt_l as [a lg ls lc l' l'' Q1 Q2 ls_lt_alg]; subst.
apply (@List_mul bb a lg ls lc); trivial. 
apply permut0_trans with l1.
exact equiv_equiv.
apply (permut0_sym equiv_equiv). assumption. assumption.

intros t t' t_eq_t' s; split.
apply (H (s,t)); trivial.
apply (H (s,t')); trivial.
apply (Relation_Definitions.equiv_sym _ _ equiv_equiv); trivial.
Qed.

Lemma equiv_rpo_equiv_3 :
  forall bb t t', equiv t t' -> (forall s, rpo_eq bb s t <-> rpo_eq bb s t').
Proof.
intro bb.
assert (H: forall t t', equiv t t' -> (forall s, rpo_eq bb s t -> rpo_eq bb s t')).
intros t t' t_eq_t' s s_le_t; inversion s_le_t; subst.
apply Equiv; apply (equiv_trans _ _ equiv_equiv) with t; trivial.
apply Lt; rewrite <- (equiv_rpo_equiv_1 _ t_eq_t'); trivial.
intros t t' t_eq_t' s; split; apply H; trivial.
apply (Relation_Definitions.equiv_sym _ _ equiv_equiv); trivial.
Qed.

Lemma equiv_rpo_equiv_4 :
  forall bb t t', equiv t t' -> (forall s, rpo_eq bb t s <-> rpo_eq bb t' s).
Proof.
intro bb.
assert (H: forall t t', equiv t t' -> (forall s, rpo_eq bb t s -> rpo_eq bb t' s)).
intros t t' t_eq_t' s t_le_s; inversion t_le_s; subst.
apply Equiv; apply (equiv_trans _ _ equiv_equiv) with t; trivial;
apply (equiv_sym _ _ equiv_equiv); trivial.
apply Lt; rewrite <- (equiv_rpo_equiv_2 _ t_eq_t'); trivial.
intros t t' t_eq_t' s; split; apply H; trivial.
apply (equiv_sym _ _ equiv_equiv); trivial.
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
                               | f' k k' Sf' L k'_lt_k H
                               | f' k k' Sf' k'_lt_k ].
(* 1/4 Subterm *)
subst; inversion t'_le_s' as [ t'' s'' t'_eq_s' | t'' s'' t'_lt_s']; clear t'_le_s'; subst.
apply (@Subterm bb f' l' tj s'); trivial;
apply Lt; apply rpo_subterm_equiv with (Term f l); trivial.
apply (@Subterm bb f' l' tj s'); trivial.
apply Lt; apply (IH (s', Term f l)); trivial.
apply size2_lex1_mem; trivial.
(* 1/3 Top_gt *)
subst; apply H2; apply in_impl_mem; trivial.
intros; apply Eq.
(* 1/2 Top_eq_lex *)
subst; apply H2; apply in_impl_mem; trivial.
intros; apply Eq.
(* Top_eq_mul *)
inversion k'_lt_k as [a lg ls lc l1 l2 P1 P2 H]; subst.
assert (tj_mem_l := in_impl_mem equiv Eq tj l tj_in_l).
rewrite (mem_permut0_mem equiv_equiv tj P1) in tj_mem_l.
rewrite <- mem_or_app in tj_mem_l.
destruct tj_mem_l as [tj_mem_ls | tj_mem_llc].
destruct (H _ tj_mem_ls) as [a' [a'_mem_a_lg tj_lt_a']].
apply (@Subterm bb f k tj a').
rewrite (mem_permut0_mem equiv_equiv a' P2); rewrite app_comm_cons.
rewrite <- mem_or_app; left; trivial.
apply Lt; trivial.
apply (@Subterm bb f k tj tj).
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

Add Relation term equiv 
  reflexivity proved by (Relation_Definitions.equiv_refl _ _ equiv_equiv)
    symmetry proved by (Relation_Definitions.equiv_sym _ _ equiv_equiv)
      transitivity proved by (Relation_Definitions.equiv_trans _ _ equiv_equiv) as EQA.

Add Relation (list term) (permut0 equiv) 
  reflexivity proved by (permut0_refl equiv_equiv) 
  symmetry proved by (permut0_sym equiv_equiv) 
    transitivity proved by (permut0_trans equiv_equiv)
  as LP.

Add Morphism (mem equiv)
  with signature equiv ==> permut0 equiv ==> iff
    as mem_morph2.
  exact (mem_morph2 equiv_equiv).
Qed.
  
 Add Morphism (List.app (A:=term)) 
	with signature permut0 equiv ==> permut0 equiv ==> permut0 equiv
	as app_morph.
   exact (app_morph equiv_equiv).
Qed.

 Add Morphism (List.cons (A:=term)) 
	with signature equiv ==> permut0 equiv ==> permut0 equiv
	as add_A_morph.
   exact (add_A_morph equiv_equiv).
Qed.

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
                               | f'' k'' l' Sf L l'_lt_l H H1 H2 
                               | f'' k'' l' Sf l'_lt_l ]; subst.
(* 1/4 Subterm *)
apply Subterm with t'; trivial; apply Lt;
inversion t_le_t' as [t'' t''' t_eq_t' | t'' t''' t_lt_t']; subst.
rewrite <- (equiv_rpo_equiv_1  _ t_eq_t'); trivial.
apply (IH (t',(t,u))); trivial.
apply size3_lex1_mem; trivial.
(* 1/3 Top_gt *)
inversion u_lt_t as [ f'' l'' s' t' t'_in_l' u_le_t'
                               | g'' f'' k'' l'' f''_prec_f' H'''
                               | g'' k'' l'' Sf' L l''_lt_l' H H1 H2 
                               | g'' k'' l'' Sf' l''_lt_l' ]; subst.
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
apply Top_gt; trivial.
intros u u_in_l''; apply (IH (Term f l, (Term f' l', u))); trivial.
apply size3_lex3_mem; trivial.
apply H0; trivial.
(* 1/3 Top_gt, Top_eq_mul *)
apply Top_gt; trivial.
intros u u_in_l''; apply (IH (Term f l, (Term f' l', u))); trivial.
apply size3_lex3_mem; trivial.
apply rpo_subterm_mem with f' l''; trivial.
(* 1/2 Top_eq_lex *)
inversion u_lt_t as [ f'' l'' s' t' t'_in_l' u_le_t'
                               | g'' f'' k'' l'' f''_prec_f' H'''
                               | g'' k'' l'' Sf' L' l''_lt_l' H H1 H2 
                               | g'' k'' l'' Sf' l''_lt_l' ]; subst.
(* 1/5 Top_eq_lex, Subterm *)
inversion u_le_t' as [t'' t''' u_eq_t' | t'' t''' u_lt_t']; subst.
rewrite (equiv_rpo_equiv_2 _ u_eq_t');
apply rpo_subterm_mem with f l'; trivial.
apply (IH (Term f l, (t', u))); trivial.
apply size3_lex2_mem; trivial.
apply H0; trivial.
(* 1/4 Top_eq_lex, Top_gt *)
apply Top_gt; trivial.
intros u u_in_l''; apply (IH (Term f l, (Term f l', u))); trivial.
apply size3_lex3_mem; trivial.
apply H'''; trivial.
(* 1/3 Top_eq_lex, Top_eq_lex *)
apply Top_eq_lex; trivial.
destruct L as [L | [L1 L2]].
rewrite L; assumption.
destruct L' as [L' | [L1' L2']].
rewrite <- L'; right; split; assumption.
right; split; assumption.
generalize l' l'' l'_lt_l l''_lt_l' IH; clear l' l'' l'_lt_l l''_lt_l' IH H0 H3 t_lt_fl u_lt_t L L';
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
intros u u_in_l''; apply (IH (Term f l, (Term f l', u))); trivial.
apply size3_lex3_mem; trivial.
apply H3; trivial.
(* 1/2 Top_eq_lex, Top_eq_mul *)
rewrite Sf in Sf'; discriminate.
(* 1/1 Top_eq_mul *)
inversion u_lt_t as [ f'' l'' s' t' t'_in_l' u_le_t'
                               | g'' f'' k'' l'' f''_prec_f' H'''
                               | g'' k'' l'' Sf' L l''_lt_l' H H1 H2 
                               | g'' k'' l'' Sf' l''_lt_l' ]; subst.
(* 1/4 Top_mul_lex, Subterm *)
inversion u_le_t' as [t'' t''' u_eq_t' | t'' t''' u_lt_t']; subst.
rewrite (equiv_rpo_equiv_2 _ u_eq_t');
apply rpo_subterm_mem with f l'; trivial.
apply (IH (Term f l, (t', u))); trivial.
apply size3_lex2_mem; trivial.
apply rpo_subterm_mem with f l'; trivial.
(* 1/3 Top_eq_mul, Top_gt *)
apply Top_gt; trivial.
intros u u_in_l''; apply (IH (Term f l, (Term f l', u))); trivial.
apply size3_lex3_mem; trivial.
apply H'''; trivial.
(* 1/2 Top_eq_mul, Top_eq_lex *)
rewrite Sf in Sf'; discriminate.
(* 1/1 Top_eq_mul, Top_eq_mul *)
apply Top_eq_mul; trivial.
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
rewrite <- permut0_cons;[|apply equiv_equiv|apply (Relation_Definitions.equiv_refl _ _ equiv_equiv)].
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
                               | f' l' l'' Sf L l_lt_l H H1 H2
                               | f' l' l'' Sf l_lt_l ]; clear t_lt_t; subst.
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
clear H0; induction l as [ | t l];
inversion l_lt_l as [ s t' l' l'' s_lt_t | s t' l' l'' s_eq_t l'_lt_l'' | s l']; subst.
apply IHl with t; trivial; left; reflexivity.
apply IHl0; trivial.
intros s s_in_l; apply IHl; right; trivial.
left; apply refl_equal.
(* 1/1 Antirefl, Top_eq_mul *)
clear f Sf; induction l as [ | s l].
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
apply (equiv_sym _ _ equiv_equiv); trivial.
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
apply (equiv_trans _ _ equiv_equiv) with s'; trivial.
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
apply (equiv_trans _ _ equiv_equiv) with s'; trivial.
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
contradiction.
contradiction.
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
simpl; rewrite <- permut0_cons;[|apply equiv_equiv|apply (Relation_Definitions.equiv_refl _ _ equiv_equiv)].
rewrite <- permut0_cons_inside;[reflexivity|apply equiv_equiv|apply (Relation_Definitions.equiv_refl _ _ equiv_equiv)].  
rewrite <- permut0_cons_inside;[reflexivity|apply equiv_equiv|apply (Relation_Definitions.equiv_refl _ _ equiv_equiv)].  
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
contradiction.
contradiction.
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
rewrite <- permut0_cons;[|apply equiv_equiv|apply (Relation_Definitions.equiv_refl _ _ equiv_equiv)]. 
simpl; rewrite <- permut0_cons_inside;[reflexivity|apply equiv_equiv|apply (Relation_Definitions.equiv_refl _ _ equiv_equiv)].
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
rewrite <- permut0_cons_inside;[|apply equiv_equiv|apply (Relation_Definitions.equiv_refl _ _ equiv_equiv)]. 
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
        forall f l l', status Prec f = Lex -> (length l = length l' \/ length l' <= bb /\ length l <= bb) -> rpo_lex bb l' l -> 
        (forall s, mem equiv s l -> Acc (rpo bb) s) -> (forall s, mem equiv s l' -> Acc (rpo bb) s) ->
        rpo_rest bb (f, l') (f, l)
  | Top_eq_mul_rest : 
        forall f l l', status Prec f = Mul -> rpo_mul bb l' l -> 
        (forall s, mem equiv s l -> Acc (rpo bb) s) -> (forall s, mem equiv s l' -> Acc (rpo bb) s) ->
        rpo_rest bb (f, l') (f, l).

Lemma wf_rpo_rest : well_founded (prec Prec) -> forall bb, well_founded (rpo_rest bb).
Proof.
intros wf_prec bb; unfold well_founded; intros [f l]; generalize l; clear l; 
pattern f; apply (well_founded_induction_type wf_prec); clear f.
intros f IHf l; assert (Sf : forall f', f' = f -> status Prec f' = status Prec f).
intros; subst; trivial.
destruct (status Prec f); generalize (Sf _ (refl_equal _)); clear Sf; intro Sf.
pattern l; apply (well_founded_induction_type (wf_rpo_lex_rest bb bb)); clear l.
intros l IHl; apply Acc_intro; intros [g l'] H. 
inversion H as [ f' g' k k' g_prec_f Acc_l Acc_l' 
                      | f' k k' Sf' L H' Acc_l Acc_l'
                      | f' k k' Sf' H' Acc_l Acc_l' ]; subst.
apply IHf; trivial.
apply IHl; apply Rpo_lex_rest; trivial.
absurd (Lex = Mul); [discriminate | apply trans_eq with (status Prec f); auto].
pattern l; apply (well_founded_induction_type (wf_rpo_mul_rest bb)); clear l.
intros l IHl; apply Acc_intro; intros [g l'] H; 
inversion H as [ f' g' k k' g_prec_f Acc_l Acc_l' 
                         | f' k k' Sf' L H' Acc_l Acc_l'
                         | f' k k' Sf' H' Acc_l Acc_l' ]; subst.
apply IHf; trivial.
absurd (Lex = Mul); [discriminate | apply trans_eq with (status Prec f); auto].
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
                               | f' k' l' Sf L H' H''
                               | f' k' l' Sf H']; subst.
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
apply H0; trivial.
apply (IH (g,k)); trivial.
apply Top_gt_rest; trivial.
(* 1/2 Top_eq_lex *)
assert (Acc_k : forall s, mem equiv s k -> Acc (rpo bb) s).
intros s s_mem_k; apply IHl; trivial.
apply H''; trivial.
apply (IH (f,k)); trivial.
apply Top_eq_lex_rest; trivial.
(* 1/1 Top_eq_mul *)
assert (Acc_k : forall s, mem equiv s k -> Acc (rpo bb) s).
intros s s_mem_k; apply IHl; trivial.
apply rpo_trans with (Term f k); trivial; apply Subterm with s; trivial; 
apply Equiv; apply Eq.
apply (IH (f,k)); trivial.
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
                               | f' l1 l2 Sf l1_eq_l2
                               | f' l1 l2 Sf P ]; subst.
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
                       | f l l' f_lex L Rlex R' H2 H3
                       | f l l' f_mul Rmul R' H2 ]; subst.
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
apply (IH (u, Term f l)).
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
destruct (status Prec f); generalize (Status f (refl_equal _)); clear Status; 
intro Status.
(* 1/2 Lex case *)
apply Eq_lex; trivial.
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
destruct (status Prec f); generalize (Status f (refl_equal _)); clear Status; 
intro Status.
(* 1/2 Lex case *)
apply Top_eq_lex; trivial.
left; clear; revert l; induction i as [ | i]; intros [ | a l]; simpl; trivial.
rewrite IHi; apply refl_equal.
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
destruct (IHl l'' (refl_equal _)) as [t' [t_eq_t' P]].
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
generalize (F.Symb.eq_bool_ok g f); case (F.Symb.eq_bool g f); [intro g_eq_f | intro g_diff_f].
(* 1/2 g = f *)
assert (Sf := f_equal (fun h => status Prec h) g_eq_f); simpl in Sf.
destruct (status Prec f); subst g.
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
apply o_size2_trans with (Term f l, Term f k); trivial.
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
apply size2_lex2_bis.
left; intros s' [s_eq_s' | s'_mem_k].
rewrite (equiv_rpo_equiv_2 _ s_eq_s'); trivial.
apply Ok; trivial.
right; intro H; apply Ko.
intros s' s'_mem_k; apply H; right; trivial.
right; intro H; apply not_s_lt_fl; apply H; left; reflexivity.
destruct H'' as [Ok | Ko].
destruct (eq_nat_dec (length l) (length k)).
left; apply Top_eq_lex; trivial; left; trivial.
destruct (le_lt_dec (length k) bb).
destruct (le_lt_dec (length l) bb).
left; apply Top_eq_lex; trivial; right; split; assumption.
right; intro fk_lt_fl; inversion fk_lt_fl; subst.
apply H; exists s; split; assumption.
apply (prec_antisym Prec f); trivial.
destruct H4 as [H4 | [H4 H4']].
apply n; assumption.
apply lt_irrefl with bb.
apply lt_le_trans with (length l); assumption.
rewrite H3 in Sf; discriminate.
right; intro fk_lt_fl; inversion fk_lt_fl; subst.
apply H; exists s; split; assumption.
apply (prec_antisym Prec f); trivial.
destruct H4 as [H4 | [H4 H4']].
apply n; assumption.
apply lt_irrefl with bb.
apply lt_le_trans with (length k); assumption.
rewrite H3 in Sf; discriminate.
right;  intro fk_lt_fl; inversion fk_lt_fl; subst.
apply Ko; intros s' s'_mem_k; apply rpo_trans with (Term f k); trivial.
apply Subterm with s'; trivial.
apply Equiv; reflexivity.
apply (prec_antisym Prec f); trivial.
apply Ko; trivial.
rewrite H3 in Sf; discriminate.
right ; intro fk_lt_fl; inversion fk_lt_fl; subst.
apply H; exists s; split; trivial.
apply (prec_antisym Prec f); trivial.
apply not_k_lt_l; trivial.
rewrite H3 in Sf; discriminate.
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
                            | f' k'' l'' Sf' L k''_lt_l'' l'_lt_t
                            | f' k'' l'' Sf' k_lt_l ]; subst.
apply H; exists t'; split; trivial.
apply (prec_antisym Prec f f_prec_f).
rewrite Sf in Sf'; discriminate.
assert (k'_lt_nil := Rem k_lt_l).
inversion k'_lt_nil as [a lg ls lc' k'' l'' Rk Rl ls_lt_alg]; subst.
assert (L := permut_length Rl); discriminate.
destruct H' as [Ok | Ko].
left; apply Top_eq_mul; trivial.
apply (@List_mul bb v' l' k' lc); trivial.
right; intro fk_lt_fl.
inversion fk_lt_fl as [f' l'' t'' t' t'_mem_l fk_le_t'
                            | f' f'' k'' l'' f_prec_f k''_lt_fl
                            | f' k'' l'' Sf' L k''_lt_l'' l'_lt_t
                            | f' k'' l'' Sf' k_lt_l ]; subst.
rewrite Pl in t'_mem_l; rewrite <- mem_or_app in t'_mem_l.
destruct t'_mem_l as [t'_mem_vl' | t'_mem_lc].
apply Ko; intros u u_mem_k'; exists t'; split; trivial.
inversion fk_le_t'; subst.
rewrite <- (@equiv_rpo_equiv_1 _ (Term f k) t'); trivial.
apply Subterm with u.
rewrite Pk; rewrite <- mem_or_app; left; trivial.
apply Equiv; apply Eq.
apply rpo_trans with (Term f k); trivial.
apply Subterm with u.
rewrite Pk; rewrite <- mem_or_app; left; trivial.
apply Equiv; apply Eq.
apply (@rpo_antirefl bb (Term f k)).
inversion fk_le_t'; subst.
rewrite (@equiv_rpo_equiv_2 _ (Term f k) t'); trivial.
apply Subterm with t'.
rewrite Pk; rewrite <- mem_or_app; right; trivial.
apply Equiv; apply Eq.
apply rpo_trans with t'; trivial.
apply Subterm with t'.
rewrite Pk; rewrite <- mem_or_app; right; trivial.
apply Equiv; apply Eq.
apply (prec_antisym Prec f); trivial.
rewrite Sf in Sf'; discriminate.
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
clear H; revert IH; induction k as [ | s k IHk]; intro IH.
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
                            | f' k'' l'' Sf' L k''_lt_l'' l'_lt_t
                            | f' k'' l'' Sf' k_lt_l ]; subst.
apply H; exists t'; split; trivial.
apply Ko; trivial.
apply (prec_antisym Prec f); trivial.
apply (prec_antisym Prec f); trivial.
right; intro gk_lt_fl;
inversion gk_lt_fl as [f' l'' t'' t' t'_mem_l fk_le_t'
                            | f' f'' k'' l'' f_prec_f k''_lt_fl
                            | f' k'' l'' Sf' L k''_lt_l'' l'_lt_t
                            | f' k'' l'' Sf' k_lt_l ]; subst.
apply H; exists t'; split; trivial.
absurd (prec Prec g f); trivial.
absurd (f=f); trivial.
absurd (f=f); trivial.
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
  if (F.Symb.eq_bool f1 f2) 
  then Equivalent
  else 
     if prec_bool Prec f1 f2 then Less_than
     else 
        if prec_bool Prec f2 f1 then Greater_than
        else Uncomparable.

Lemma prec_eval_is_sound :  
  forall f1 f2, 
  match prec_eval f1 f2 with
  | Equivalent => f1 = f2
  | Less_than => prec Prec f1 f2
  | Greater_than => prec Prec f2 f1 
  | Uncomparable => f1 <> f2 /\ ~prec Prec f1 f2 /\ ~prec Prec f2 f1
  end.
Proof.
intros f1 f2; unfold prec_eval;
generalize (F.Symb.eq_bool_ok f1 f2); case (F.Symb.eq_bool f1 f2); [intro f1_eq_f2; trivial | intro f1_diff_f2].
generalize (prec_bool_ok Prec f1 f2); case (prec_bool Prec f1 f2); [intro f1_lt_f2; trivial | intro f1_not_lt_f2].
generalize (prec_bool_ok Prec f2 f1); case (prec_bool Prec f2 f1); [intro f2_lt_f1; trivial | intro f2_not_lt_f1].
repeat split; trivial.
Qed.

Inductive result (A : Type) : Type := 
  | Not_found : result A
  | Not_finished : result A
  | Found : A -> result A.


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
     | nil => @Not_found _
     | a :: l => 
            match p t a with
            | Some true => (Found l)
            | Some false =>
               match remove_equiv_eval p t l  with
               | Found l' => Found (a :: l')
               | Not_found => @Not_found _
               | Not_finished => @Not_finished _
               end
             | None => @Not_finished _
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
           if F.Symb.eq_bool f1 f2 
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
           if F.Symb.eq_bool f1 f2 
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
destruct (p t1 t2) as [ [ | ] | ]; generalize (H _ (refl_equal _)); clear H; intro H.
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
apply list_permut.permut_refl; intro; trivial.
(* 1/5 *)
destruct l2 as [ | t2 l2].
contradiction.
exists (@nil (term * term)); simpl; intuition; intros.
apply list_permut.permut_refl; intro; trivial.
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
apply list_permut.permut_trans with (t2' :: l2'); trivial.
intros a b c _ a_eq_b b_eq_c; transitivity b; trivial.
simpl; apply Pcons; trivial.
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
simpl; apply (Pcons (R := @eq term) t1 t1 (l := l1) nil
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
generalize (F.Symb.eq_bool_ok f1 f2); case (F.Symb.eq_bool f1 f2); [intro f1_eq_f2 | intro f1_diff_f2].
assert (Sf1 := f_equal (status Prec) f1_eq_f2); 
destruct (status Prec f2); subst f2; rewrite Sf1.
intro H; apply Eq_lex; trivial.
generalize l1 l2 H; clear l1 l2 H;
intro l; induction l as [ | t l]; intros [ | t' l'] H.
apply Eq_list_nil.
discriminate.
discriminate.
simpl in H; apply Eq_list_cons.
apply IHn; destruct (equiv_eval rpo_infos n t t') as [ [ | ] | ]; 
trivial; discriminate.
apply IHl; destruct (equiv_eval rpo_infos n t t') as [ [ | ] | ]; 
trivial; discriminate.

intro H; assert (H' := remove_equiv_eval_list_is_sound (equiv_eval rpo_infos n) l1 l2);
destruct (remove_equiv_eval_list (equiv_eval rpo_infos n) l1 l2) as [ [l1' l2'] | ].
destruct H' as [ll [E_ll [P1 [P2 H']]]];
apply Eq_mul; trivial.
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
| H1 H2 t1 l1 H3 t2 l2 H4 H IH
| H1 H2 t1 l1 H3 t2 l2 H4 H IH
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
assert (H' := E _ (or_introl _ (refl_equal _)) H); contradiction.
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
assert (K := remove_equiv_eval_is_sound p t1 l2); rewrite H in K;
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
assert (K := remove_equiv_eval_fully_evaluates p t1 l2);
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
case (eq_symb_bool f1 f2); [idtac | discriminate].
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
| f l1 l2 Sf
| f l1 l2 Sf P1 P2]; subst.
(* 1/3 syntactic equality *)
destruct t2 as [v2 | f2 l2]; simpl.
generalize (X.eq_bool_ok v2 v2); case (X.eq_bool v2 v2); [intros _ | intro v2_diff_v2; absurd (v2 = v2)]; trivial.
case (mem_bool eq_tt_bool (Term f2 l2, Term f2 l2) (equiv_l rpo_infos)); [reflexivity | idtac].
generalize (F.Symb.eq_bool_ok f2 f2); case (F.Symb.eq_bool f2 f2); [intros _ | intro f2_diff_f2; absurd (f2 = f2); trivial].
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
(* 1/2 Eq_lex *)
rewrite equiv_eval_equation.
case (mem_bool eq_tt_bool (Term f l1, Term f l2) (equiv_l rpo_infos)); [reflexivity | idtac].
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
trivial.
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
case (mem_bool eq_tt_bool (Term f l1, Term f l2) (equiv_l rpo_infos)); [reflexivity | idtac].
generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); [intros _ | intro f_diff_f; absurd (f = f)]; trivial.
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
intros p s1 s2 [ | t1 l1] [ | t2 l2]; apply refl_equal.
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
simpl; left; split; [apply refl_equal | discriminate].
simpl; left; split; [discriminate | apply refl_equal].
simpl; case_eq (p t1 t2); [idtac | trivial].
intros [ | | | ] Ht; generalize (IHl1 l2).
(* 1/4 p t1 t2 = Some Equivalent *)
case_eq (lexico_eval p s1 s2 l1 l2); [intros [ | | | ] Hl | trivial].
(* 1/7 lexico_eval p s1 s2 l1 l2 = Some Equivalent *)
intros [ll [Hll [H1 H2]]]; exists ((t1,t2) :: ll); split.
simpl; intros u1 u2 [u1u2_eq_t1t2 | u1u2_in_ll]; [injection u1u2_eq_t1t2; intros; subst | apply Hll]; assumption.
simpl; split; subst; apply refl_equal.
(* 1/6 lexico_eval p s1 s2 l1 l2 = Some Less_than *)
intros [[H1 H2] | [[ll [a2 [l2' [Hll [H1 H2]]]]] | [ll [a1 [a2 [l1' [l2' [Hll [Ha [H [H1 H2]]]]]]]]]]].
right; left; subst; destruct l2 as [ | a2 l2].
discriminate.
exists ((t1,t2) :: nil); exists a2; exists l2; split.
simpl; intros u1 u2 [u1u2_eq_t1t2 | u1u2_in_nil]; [injection u1u2_eq_t1t2; intros; subst; assumption | contradiction].
split; apply refl_equal.
right; left; exists ((t1,t2) :: ll); exists a2; exists l2'; split.
simpl; intros u1 u2 [u1u2_eq_t1t2 | u1u2_in_ll]; [injection u1u2_eq_t1t2; intros; subst | apply Hll]; assumption.
split; subst; apply refl_equal.
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
split; subst; apply refl_equal.
(* 1/5 lexico_eval p s1 s2 l1 l2 = Some Greater_than *)
intros [[H1 H2] | [[ll [a1 [l1' [Hll [H1 H2]]]]] | [ll [a1 [a2 [l1' [l2' [Hll [Ha [H [H1 H2]]]]]]]]]]].
right; left; subst; destruct l1 as [ | a1 l1].
discriminate.
exists ((t1,t2) :: nil); exists a1; exists l1; split.
simpl; intros u1 u2 [u1u2_eq_t1t2 | u1u2_in_nil]; [injection u1u2_eq_t1t2; intros; subst; assumption | contradiction].
split; apply refl_equal.
right; left; exists ((t1,t2) :: ll); exists a1; exists l1'; split.
simpl; intros u1 u2 [u1u2_eq_t1t2 | u1u2_in_ll]; [injection u1u2_eq_t1t2; intros; subst | apply Hll]; assumption.
split; subst; apply refl_equal.
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
split; subst; apply refl_equal.
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
simpl; split; subst; apply refl_equal.
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
split; apply refl_equal.
intros; contradiction.
split.
assumption.
split.
intros u u_in_t1l1; right; apply H'; assumption.
split; apply refl_equal.
intros; contradiction.
split.
assumption.
split.
intros u u_in_t1l1; right; apply H'; assumption.
split; apply refl_equal.
(* 1/5 lexico_eval p s1 s2 l1 l2 = Some Greater_than *)
intros _.
generalize (term_gt_list_is_sound p s2 (t1 :: l1)); destruct (term_gt_list p s2 (t1 :: l1)) as [[ | ] | ]; intro H'; trivial.
do 2 right; exists (@nil (term * term)); exists t1; exists t2; exists l1; exists l2; split.
intros; contradiction.
split.
assumption.
split.
intros u u_in_t1l1; right; apply H'; assumption.
split; apply refl_equal.
(* 1/4 lexico_eval p s1 s2 l1 l2 = Some  Some Uncomparable *)
intros _.
generalize (term_gt_list_is_sound p s2 (t1 :: l1)); destruct (term_gt_list p s2 (t1 :: l1)) as [[ | ] | ]; intro H'; trivial.
do 2 right; exists (@nil (term * term)); exists t1; exists t2; exists l1; exists l2; split.
intros; contradiction.
split.
assumption.
split.
intros u u_in_t1l1; right; apply H'; assumption.
split; apply refl_equal.
(* 1/3 lexico_eval p s1 s2 l1 l2 = None *)
intros _.
generalize (term_gt_list_is_sound p s2 (t1 :: l1)); destruct (term_gt_list p s2 (t1 :: l1)) as [[ | ] | ]; intro H'; trivial.
do 2 right; exists (@nil (term * term)); exists t1; exists t2; exists l1; exists l2; split.
intros; contradiction.
split.
assumption.
split.
intros u u_in_t1l1; right; apply H'; assumption.
split; apply refl_equal.
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
simpl; split; subst; apply refl_equal.
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
split; apply refl_equal.
intros; contradiction.
split.
assumption.
split.
intros u u_in_t2l2; right; apply H'; assumption.
split; apply refl_equal.
intros; contradiction.
split.
assumption.
split.
intros u u_in_t2l2; right; apply H'; assumption.
split; apply refl_equal.
(* 1/4 lexico_eval p s1 s2 l1 l2 = Some Greater_than *)
intros _.
generalize (term_gt_list_is_sound p s1 (t2 :: l2)); destruct (term_gt_list p s1 (t2 :: l2)) as [[ | ] | ]; intro H'; trivial.
do 2 right; exists (@nil (term * term)); exists t1; exists t2; exists l1; exists l2; split.
intros; contradiction.
split.
assumption.
split.
intros u u_in_t2l2; right; apply H'; assumption.
split; apply refl_equal.
(* 1/3 lexico_eval p s1 s2 l1 l2 = Some  Some Uncomparable *)
intros _.
generalize (term_gt_list_is_sound p s1 (t2 :: l2)); destruct (term_gt_list p s1 (t2 :: l2)) as [[ | ] | ]; intro H'; trivial.
do 2 right; exists (@nil (term * term)); exists t1; exists t2; exists l1; exists l2; split.
intros; contradiction.
split.
assumption.
split.
intros u u_in_t2l2; right; apply H'; assumption.
split; apply refl_equal.
(* 1/2 lexico_eval p s1 s2 l1 l2 = None *)
intros _.
generalize (term_gt_list_is_sound p s1 (t2 :: l2)); destruct (term_gt_list p s1 (t2 :: l2)) as [[ | ] | ]; intro H'; trivial.
do 2 right; exists (@nil (term * term)); exists t1; exists t2; exists l1; exists l2; split.
intros; contradiction.
split.
assumption.
split.
intros u u_in_t2l2; right; apply H'; assumption.
split; apply refl_equal.
(* 1/1 p t1 t2 = Some Uncomparable *)
trivial.
Qed.

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
destruct (p g s) as [[ | | | ] | ]; (apply refl_equal || discriminate).
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

Lemma mult_eval_is_sound_weak :
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
intros Hfind; apply equiv_sym.
apply equiv_equiv.
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
intros Hfind; apply equiv_sym.
apply equiv_equiv.
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
intro H; destruct (H (refl_equal _)) as [v_in_l' | [t [t_in_l' H']]].
right; exists (Term f' l'); split.
left; trivial.
left; trivial.
right; exists (Term f' l'); split.
left; trivial.
apply trans_clos_is_trans with t; trivial; left; trivial.
intros _; generalize (IHm _ Sl); destruct (var_in_term_list v l).
intro H; destruct (H (refl_equal _)) as [v_in_l' | [t [t_in_l' H']]].
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
intro H1; apply Equiv; apply (equiv_sym _ _ equiv_equiv); trivial.
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
intro f1_eq_f2; assert (Sf1 := f_equal (status Prec) f1_eq_f2);
destruct (status Prec f2); subst f2; rewrite Sf1.
(* 1/8 f1 has a Lex status *)
simpl; assert (H' := lexico_eval_is_sound (rpo_eval rpo_infos n) (Term f1 l1)
                                (Term f1 l2) l1 l2).
destruct (lexico_eval (rpo_eval rpo_infos n) (Term f1 l1) (Term f1 l2) l1 l2) as [ [ | | | ] | ].
(* 1/12 lexico_eval (rpo_eval rpo_infos n) (Term f1 l1) (Term f1 l2) l1 l2 = Some Equivalent *)
destruct H' as [ll [E_ll [H1 H2]]].
rewrite (f_equal (@length _) H1); rewrite (f_equal (@length _) H2); do 2 rewrite length_map.
rewrite <- beq_nat_refl; simpl.
apply (@Eq_lex f1 l1 l2 Sf1); trivial.
subst l1 l2; induction ll as [ | [t1 t2] ll]; simpl.
apply Eq_list_nil.
apply Eq_list_cons.
generalize (IHn t1 t2); rewrite (E_ll _ _ (or_introl _ (refl_equal _))); intro; assumption.
apply IHll; intros; apply E_ll; right; assumption.
(* 1/11 lexico_eval (rpo_eval rpo_infos n) (Term f1 l1) (Term f1 l2) l1 l2 = Some Less_than *)
case_eq (beq_nat (length l1) (length l2)); simpl.
intro L; apply (@Top_eq_lex rpo_infos.(bb) f1 l2 l1 Sf1).
left; apply sym_eq; apply beq_nat_true; assumption.
destruct H' as [[H1 H2] | [[ll [t2 [l2' [ _ [H1 H2]]]]] | [ll [t1 [t2 [l1' [l2' [Hll [Ht [H' [H1 H2]]]]]]]]]]].
destruct l2 as [ | a2 l2]; [apply False_rect; apply H2; apply refl_equal | subst l1; discriminate].
subst l1 l2; rewrite length_app in L; do 2 rewrite length_map in L.
apply False_rect; generalize (beq_nat_true _ _ L); clear L; induction ll as [ | [u1 u2] ll].
discriminate.
intro L; injection L; clear L; intro L; apply IHll; assumption.
clear L H'; subst l1 l2; induction ll as [ | [u1 u2] ll].
simpl; constructor 1; generalize (IHn t1 t2); rewrite Ht; intro; assumption.
simpl; constructor 2.
generalize (IHn u1 u2); rewrite (Hll _ _ (or_introl _ (refl_equal _))); intro; assumption.
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
left; apply (equiv_trans _ _ equiv_equiv) with u'; trivial.
generalize (IHn u' u2); rewrite u'_eq_u2; intro; assumption.
right; rewrite (equiv_rpo_equiv_2 _ u_eq_u'); generalize (IHn u' u2); rewrite u'_lt_u2; intro; assumption.
rewrite (equiv_rpo_equiv_2 _ u_eq_u'); generalize (IHn (Term f1 l2) u'); rewrite H''; intro; assumption.
intros _; generalize (leb_complete (length l1) (rpo_infos.(bb))); case (leb (length l1) rpo_infos.(bb)); [idtac | simpl; trivial].
generalize (leb_complete (length l2) (rpo_infos.(bb))); case (leb (length l2) (bb rpo_infos)); simpl; [idtac | trivial].
intros L2 L1; apply (@Top_eq_lex rpo_infos.(bb) f1 l2 l1 Sf1).
right; split; [apply L1 | apply L2]; apply refl_equal.
clear L1 L2; destruct H' as [[H1 H2] | [[ll [t2 [l2' [Hll [H1 H2]]]]] | [ll [t1 [t2 [l1' [l2' [Hll [Ht [H' [H1 H2]]]]]]]]]]].
subst l1; destruct l2 as [ | a2 l2]; [apply False_rect; apply H2; apply refl_equal | constructor 3].
subst l1 l2; induction ll as [ | [u1 u2] ll].
simpl; constructor 3.
simpl; constructor 2.
generalize (IHn u1 u2); rewrite (Hll _ _ (or_introl _ (refl_equal _))); intro; assumption.
apply IHll; intros; apply Hll; right; assumption.
clear H'; subst l1 l2; induction ll as [ | [u1 u2] ll].
simpl; constructor 1; generalize (IHn t1 t2); rewrite Ht; intro; assumption.
simpl; constructor 2.
generalize (IHn u1 u2); rewrite (Hll _ _ (or_introl _ (refl_equal _))); intro; assumption.
apply IHll; intros; apply Hll; right; assumption.
clear L1 L2; destruct H' as [[H1 H2] | [[ll [t2 [l2' [Hll [H1 H2]]]]] | [ll [t1 [t2 [l1' [l2' [Hll [Ht [H' [H1 H2]]]]]]]]]]].
intros; subst l1; contradiction.
intros u u_in_l1; rewrite mem_in_eq in u_in_l1; destruct u_in_l1 as [u' [u_eq_u' u'_in_l1]].
subst l1; rewrite in_map_iff in u'_in_l1; destruct u'_in_l1 as [[u1 u2] [H1 K2]].
apply Subterm with u2.
subst l2; rewrite <- mem_or_app; left; apply in_impl_mem.
apply Eq.
rewrite in_map_iff; exists (u1,u2); split; trivial.
simpl in H1; subst u1; left; apply (equiv_trans _ _ equiv_equiv) with u'; trivial.
generalize (IHn u' u2); rewrite (Hll _ _ K2); intro; assumption.
intros u u_in_l1; rewrite mem_in_eq in u_in_l1; destruct u_in_l1 as [u' [u_eq_u' u'_in_l1]].
destruct (H' _ u'_in_l1) as [ [u2 [u2_in_l2 u'_le_u2]] | H''].
apply Subterm with u2.
apply in_impl_mem; trivial.
intros; apply Eq.
destruct u'_le_u2 as [u'_eq_u2 | u'_lt_u2].
left; apply (equiv_trans _ _ equiv_equiv) with u'; trivial.
generalize (IHn u' u2); rewrite u'_eq_u2; intro; assumption.
right; rewrite (equiv_rpo_equiv_2 _ u_eq_u'); generalize (IHn u' u2); rewrite u'_lt_u2; intro; assumption.
rewrite (equiv_rpo_equiv_2 _ u_eq_u'); generalize (IHn (Term f1 l2) u'); rewrite H''; intro; assumption.
(* 1/10 lexico_eval (rpo_eval rpo_infos n) (Term f1 l1) (Term f1 l2) l1 l2 = Some Greater_than *)
case_eq (beq_nat (length l1) (length l2)); simpl.
intro L; apply (@Top_eq_lex rpo_infos.(bb) f1 l1 l2 Sf1).
left; apply beq_nat_true; assumption.
destruct H' as [[H1 H2] | [[ll [t1 [l1' [ _ [H1 H2]]]]] | [ll [t1 [t2 [l1' [l2' [Hll [Ht [H' [H1 H2]]]]]]]]]]].
destruct l1 as [ | a1 l1]; [apply False_rect; apply H1; apply refl_equal | subst l2; discriminate].
subst l1 l2; rewrite length_app in L; do 2 rewrite length_map in L.
apply False_rect; generalize (beq_nat_true _ _ L); clear L; induction ll as [ | [u1 u2] ll].
discriminate.
intro L; injection L; clear L; intro L; apply IHll; assumption.
clear L H'; subst l1 l2; induction ll as [ | [u1 u2] ll].
simpl; constructor 1; generalize (IHn t1 t2); rewrite Ht; intro; assumption.
simpl; constructor 2.
apply (equiv_sym _ _ equiv_equiv); generalize (IHn u1 u2); rewrite (Hll _ _ (or_introl _ (refl_equal _))); intro; assumption.
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
left; apply (equiv_trans _ _ equiv_equiv) with u'; trivial.
apply (equiv_sym _ _ equiv_equiv); generalize (IHn u1 u'); rewrite u'_eq_u1; intro; assumption.
right; rewrite (equiv_rpo_equiv_2 _ u_eq_u'); generalize (IHn u1 u'); rewrite u'_lt_u1; intro; assumption.
rewrite (equiv_rpo_equiv_2 _ u_eq_u'); generalize (IHn (Term f1 l1) u'); rewrite H''; intro; assumption.
intros _; generalize (leb_complete (length l1) (rpo_infos.(bb))); case (leb (length l1) rpo_infos.(bb)); [idtac | simpl; trivial].
generalize (leb_complete (length l2) (rpo_infos.(bb))); case (leb (length l2) (bb rpo_infos)); simpl; [idtac | trivial].
intros L2 L1; apply (@Top_eq_lex rpo_infos.(bb) f1 l1 l2 Sf1).
right; split; [apply L2 | apply L1]; apply refl_equal.
clear L1 L2; destruct H' as [[H1 H2] | [[ll [t1 [l2' [Hll [H1 H2]]]]] | [ll [t1 [t2 [l1' [l2' [Hll [Ht [H' [H1 H2]]]]]]]]]]].
subst l2; destruct l1 as [ | a1 l2]; [apply False_rect; apply H1; apply refl_equal | constructor 3].
subst l1 l2; induction ll as [ | [u1 u2] ll].
simpl; constructor 3.
simpl; constructor 2.
apply (equiv_sym _ _ equiv_equiv); generalize (IHn u1 u2); rewrite (Hll _ _ (or_introl _ (refl_equal _))); intro; assumption.
apply IHll; intros; apply Hll; right; assumption.
clear H'; subst l1 l2; induction ll as [ | [u1 u2] ll].
simpl; constructor 1; generalize (IHn t1 t2); rewrite Ht; intro; assumption.
simpl; constructor 2.
apply (equiv_sym _ _ equiv_equiv); generalize (IHn u1 u2); rewrite (Hll _ _ (or_introl _ (refl_equal _))); intro; assumption.
apply IHll; intros; apply Hll; right; assumption.
clear L1 L2; destruct H' as [[H1 H2] | [[ll [t1 [l1' [Hll [H1 H2]]]]] | [ll [t1 [t2 [l1' [l2' [Hll [Ht [H' [H1 H2]]]]]]]]]]].
intros; subst l2; contradiction.
intros u u_in_l2; rewrite mem_in_eq in u_in_l2; destruct u_in_l2 as [u' [u_eq_u' u'_in_l2]].
subst l2; rewrite in_map_iff in u'_in_l2; destruct u'_in_l2 as [[u1 u2] [K1 K2]].
apply Subterm with u1.
subst l1; rewrite <- mem_or_app; left; apply in_impl_mem.
apply Eq.
rewrite in_map_iff; exists (u1,u2); split; trivial.
simpl in K1; subst u2; left; apply (equiv_trans _ _ equiv_equiv) with u'; trivial.
apply (equiv_sym _ _ equiv_equiv); generalize (IHn u1 u'); rewrite (Hll _ _ K2); intro; assumption.
intros u u_in_l2; rewrite mem_in_eq in u_in_l2; destruct u_in_l2 as [u' [u_eq_u' u'_in_l2]].
destruct (H' _ u'_in_l2) as [ [u1 [u1_in_l1 u'_le_u1]] | H''].
apply Subterm with u1.
apply in_impl_mem; trivial.
intros; apply Eq.
destruct u'_le_u1 as [u'_eq_u1 | u'_lt_u1].
left; apply (equiv_trans _ _ equiv_equiv) with u'; trivial.
apply (equiv_sym _ _ equiv_equiv); generalize (IHn u1 u'); rewrite u'_eq_u1; intro; assumption.
right; rewrite (equiv_rpo_equiv_2 _ u_eq_u'); generalize (IHn u1 u'); rewrite u'_lt_u1; intro; assumption.
rewrite (equiv_rpo_equiv_2 _ u_eq_u'); generalize (IHn (Term f1 l1) u'); rewrite H''; intro; assumption.
(* 1/9 lexico_eval (rpo_eval rpo_infos n) (Term f1 l1) (Term f1 l2) l1 l2 = Some Uncomparable *)
case (beq_nat (length l1) (length l2)
      || leb (length l1) (bb rpo_infos) && leb (length l2) (bb rpo_infos)); trivial.
(* 1/8 lexico_eval (rpo_eval rpo_infos n) (Term f1 l1) (Term f1 l2) l1 l2 = None *)
case (beq_nat (length l1) (length l2)
      || leb (length l1) (bb rpo_infos) && leb (length l2) (bb rpo_infos)); trivial.
(* 1/7 f1 has a Mul status *)
simpl; assert (H' := remove_equiv_eval_list_is_sound (equiv_eval rpo_infos n) l1 l2);
destruct (remove_equiv_eval_list (equiv_eval rpo_infos n) l1 l2) as [ [[ | t1' l1'] [ | t2' l2']] | ].
destruct H' as [ll [E_ll [P1 [P2 _]]]]; apply (@Eq_mul f1 l1 l2 Sf1); trivial.
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
apply Top_eq_mul; trivial.
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
apply Top_eq_mul; trivial.
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
Qed.

Lemma well_formed_equiv :
  forall t1 t2, well_formed t1 -> equiv t1 t2 -> well_formed t2.
Proof.
intro t1; pattern t1; apply term_rec3; clear t1.
intros v t2 _ v_eq_t2; inversion v_eq_t2; subst; unfold well_formed; simpl; trivial.
intros f l IH t2 Wfl fl_eq_t2; 
inversion fl_eq_t2; subst; trivial.
assert (L' := equiv_same_length  fl_eq_t2).
destruct (well_formed_unfold Wfl) as [Wl L].
apply well_formed_fold; split.
assert (IH' : forall t t2, In t l -> equiv t t2 -> well_formed t2).
intros t t2 t_in_l; apply IH; trivial.
apply Wl; trivial.
generalize l2 H3; clear l2 IH H3 H1 L' L fl_eq_t2 Wfl; 
induction l as [ | t l]; intros l2 l_eq_l2; inversion l_eq_l2; subst.
contradiction.
intros u [u_eq_t2 | u_in_l2]; subst.
apply IH' with t; trivial.
left; trivial.
apply IHl with l0; trivial.
intros; apply Wl; right; trivial.
intros u1 u2 u1_in_l; apply IH'; right; trivial.
rewrite <- L'; trivial.
assert (L' := equiv_same_length fl_eq_t2).
destruct (well_formed_unfold Wfl) as [Wl L].
apply well_formed_fold; split.
assert (IH' : forall t t2, In t l -> equiv t t2 -> well_formed t2).
intros t t2 t_in_l; apply IH; trivial.
apply Wl; trivial.
generalize l2 H3; clear l2 IH H3 H1 L' L fl_eq_t2 Wfl; 
induction l as [ | t l]; intros l2 l_eq_l2; inversion l_eq_l2; subst.
contradiction.
intros u u_in_l2; 
destruct (in_app_or _ _ _ u_in_l2) as [u_in_l1 | [u_eq_b | u_in_l3]].
apply IHl with (l1 ++ l3); trivial.
intros; apply Wl; right; trivial.
intros u1 u2 u1_in_l; apply IH'; right; trivial.
apply in_or_app; left; trivial.
subst u; apply IH' with t; trivial; left; trivial.
apply IHl with (l1 ++ l3); trivial.
intros; apply Wl; right; trivial.
intros u1 u2 u1_in_l; apply IH'; right; trivial.
apply in_or_app; right; trivial.
rewrite <- L'; trivial.
Qed.

Lemma lexico_eval_fully_evaluates :
  forall p s1 s2 l1 l2, 
  (forall t1, In t1 l1 -> p s2 t1 <> None) ->
  (forall t2, In t2 l2 -> p s1 t2 <> None) ->
  (forall t1 t2, In t1 l1 -> In t2 l2 -> p t1 t2 <> None) ->
  lexico_eval p s1 s2 l1 l2 <> None.
Proof.
intros p s1 s2 l1; induction l1 as [ | t1 l1]; intros [ | t2 l2] Es2 Es1 E;
simpl; try discriminate.
assert (H := E t1 t2 (or_introl _ (refl_equal _)) (or_introl _ (refl_equal _)));
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
clear H; assert (H := Es2 t1 (or_introl _ (refl_equal _))).
destruct (p s2 t1) as [ [ | | | ] | ].
intros _; discriminate.
intros _; discriminate.
intros _; discriminate.
intros _; discriminate.
intros _; apply H; trivial.
(* 1/5 NOT all terms in l1 are smaller than s2 *)
clear H; assert (H := Es2 t1 (or_introl _ (refl_equal _))).
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
clear H; assert (H := Es1 t2 (or_introl _ (refl_equal _))).
destruct (p s1 t2) as [ [ | | | ] | ].
intros _; discriminate.
intros _; discriminate.
intros _; discriminate.
intros _; discriminate.
intros _; apply H; trivial.
(* 1/4 NOT all terms in l2 are smaller than s1 *)
clear H; assert (H := Es1 t2 (or_introl _ (refl_equal _))).
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
case_eq (mem_bool eq_tt_bool (t1, t2) (rpo_l rpo_infos)); intro Heq_1;
case_eq (mem_bool eq_tt_bool (t2, t1) (rpo_l rpo_infos)); intro Heq_2;
case_eq (mem_bool eq_tt_bool (t1, t2) (equiv_l rpo_infos)); intro Heq_3;
case_eq (mem_bool eq_tt_bool (t2, t1) (equiv_l rpo_infos)); intro Heq_4; intros R T R' T'; try
(absurd (rpo rpo_infos.(bb) t1 t1);[
intro; apply (@rpo_antirefl rpo_infos.(bb) t1); trivial|
apply rpo_trans with t2;assumption]);try complete intuition;
try (absurd (rpo rpo_infos.(bb) t1 t1);
[intro; apply (@rpo_antirefl rpo_infos.(bb) t1); trivial |
rewrite (@equiv_rpo_equiv_1 _ _ _ R') in t1_lt_t2; trivial]).
clear Heq_1 Heq_2 Heq_3 Heq_4.
destruct (equiv_eval rpo_infos (S n) t1 t2) as [ [ | ] | ];
destruct (equiv_eval rpo_infos (S n) t2 t1) as [ [ | ] | ];
try (absurd (rpo rpo_infos.(bb) t1 t1); [
intro; apply (@rpo_antirefl rpo_infos.(bb) t1); trivial |
rewrite <- (equiv_rpo_equiv_1 _ R) in t1_lt_t2; trivial]);try complete intuition;
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
| f l2' l1' Sf L l1_lt_l2 H
| f l2' l1' Sf l1_lt_l2]; subst.
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
intro; subst f1; apply False_rect; apply (prec_antisym Prec  f2); trivial.
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
apply H0; apply in_impl_mem; trivial.
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
intro; subst f2; apply False_rect; apply (prec_antisym Prec f1); trivial.
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
apply H0; apply in_impl_mem; trivial.
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
set (s1 := Term f2 l1) in *; clearbody s1.
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
simpl; generalize (prec_eval_is_sound f2 f2); destruct (prec_eval f2 f2).
intros _; rewrite Sf; rewrite Sf in R; rewrite Sf in T; simpl in R; simpl in T.
revert t1_lt_t2 H0 St IHl1l2 IHl2l1 IHl1s2 IHs2l1 IHs1l2 IHl2s1 R T l1_lt_l2 Sl.
clear; revert s1 s2 l2; induction l1 as [ | t1 l1]; intros s1 s2 [ | t2 l2]; intros.
inversion l1_lt_l2.
apply refl_equal.
inversion l1_lt_l2.
inversion l1_lt_l2; subst.
simpl; rewrite (proj1 (IHl1l2 _ _ (or_introl _ (refl_equal _)) (or_introl _ (refl_equal _)) H1)).
unfold term_gt_list.
assert (H : list_forall_option
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
apply H0; apply in_impl_mem; trivial; exact Eq.
rewrite (proj2 (IHl1s2 _ u1_in_t1l1 u1_lt_s2)); apply refl_equal.
rewrite H; apply refl_equal.
simpl.
assert (H' := @rpo_eval_is_complete_equivalent rpo_infos n t1 t2).
generalize (H' (Sl _ _ (or_introl _ (refl_equal _)) 
                        (or_introl _ (refl_equal _))) H3);
clear H'; intro H'; rewrite H'.
apply IHl1; trivial.
intros; apply H0; right; assumption.
intros; apply IHl1l2; trivial; right; assumption.
intros; apply IHl2l1; trivial; right; assumption.
intros; apply IHl1s2; trivial; right; assumption.
intros; apply IHs2l1; trivial; right; assumption.
intros; apply IHs1l2; trivial; right; assumption.
intros; apply IHl2s1; trivial; right; assumption.
simpl in R; rewrite H' in R; assumption.
simpl in T; rewrite H' in T; assumption.
intros; apply Sl; right; assumption.
intro; apply False_rect; apply (prec_antisym Prec f2); assumption.
intro; apply False_rect; apply (prec_antisym Prec f2); assumption.
intros [f2_diff_f2 _]; absurd (f2 = f2); trivial.
simpl in T; absurd (@None comp = None); trivial.
simpl in T; absurd (@None comp = None); trivial.
destruct L as [L | [L1 L2]].
rewrite L; rewrite <- beq_nat_refl; intro; discriminate.
rewrite (leb_correct _ _ L1); rewrite (leb_correct _ _ L2); rewrite orb_true_r; intro; discriminate.
case_eq (beq_nat (length l2) (length l1)
    || leb (length l2) (bb rpo_infos) && leb (length l1) (bb rpo_infos)).
clear L; intros L; rewrite L in R', T'; clear L.
set (s1 := Term f2 l1) in *; clearbody s1.
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
simpl; generalize (prec_eval_is_sound f2 f2); destruct (prec_eval f2 f2).
intros _; rewrite Sf; rewrite Sf in R'; rewrite Sf in T'; simpl in R'; simpl in T'.
revert t1_lt_t2 H0 St IHl1l2 IHl2l1 IHl1s2 IHs2l1 IHs1l2 IHl2s1 R' T' l1_lt_l2 Sl.
clear; revert s1 s2 l1; induction l2 as [ | t2 l2]; intros s1 s2 [ | t1 l1]; intros.
inversion l1_lt_l2.
inversion l1_lt_l2.
apply refl_equal.
inversion l1_lt_l2; subst.
simpl; rewrite (proj2 (IHl1l2 _ _ (or_introl _ (refl_equal _)) (or_introl _ (refl_equal _)) H1)).
unfold term_gt_list.
assert (H : list_forall_option
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
apply H0; apply in_impl_mem; trivial; exact Eq.
rewrite (proj2 (IHl1s2 _ u1_in_t1l1 u1_lt_s2)); apply refl_equal.
rewrite H; apply refl_equal.
simpl.
assert (H' := @rpo_eval_is_complete_equivalent rpo_infos n t2 t1).
rewrite plus_comm in H'; generalize (H' (Sl _ _ (or_introl _ (refl_equal _)) 
                        (or_introl _ (refl_equal _))) (equiv_sym _ _ equiv_equiv _ _ H3));
clear H'; intro H'; rewrite H'.
apply IHl2; trivial.
intros; apply H0; right; assumption.
intros; apply IHl1l2; trivial; right; assumption.
intros; apply IHl2l1; trivial; right; assumption.
intros; apply IHl1s2; trivial; right; assumption.
intros; apply IHs2l1; trivial; right; assumption.
intros; apply IHs1l2; trivial; right; assumption.
intros; apply IHl2s1; trivial; right; assumption.
simpl in R'; rewrite H' in R'; assumption.
simpl in T'; rewrite H' in T'; assumption.
intros; apply Sl; right; assumption.
intro; apply False_rect; apply (prec_antisym Prec f2); assumption.
intro; apply False_rect; apply (prec_antisym Prec f2); assumption.
intros [f2_diff_f2 _]; absurd (f2 = f2); trivial.
simpl in T'; absurd (@None comp = None); trivial.
simpl in T'; absurd (@None comp = None); trivial.
destruct L as [L | [L1 L2]].
rewrite L; rewrite <- beq_nat_refl; intro; discriminate.
rewrite (leb_correct _ _ L1); rewrite (leb_correct _ _ L2); rewrite orb_true_r; intro; discriminate.
(* 1/1 Top_eq_mul *)
set (s1 := Term f2 l1) in *.
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
simpl; generalize (prec_eval_is_sound f2 f2); destruct (prec_eval f2 f2).
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
rewrite (Ell _ _ t1t2_in_ll); intro t1_eq_t2; apply t1_eq_t2; apply refl_equal.
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
apply Ell; left; apply refl_equal.
apply IHll with l1 l2; trivial.
intros; apply Ell; right; assumption.
refine (list_permut.permut_trans _ P1 _).
intros; subst; apply refl_equal.
apply list_permut.permut_sym.
intros; subst; apply refl_equal.
simpl; apply Pcons; [trivial | apply list_permut.permut_refl; intros; trivial].
refine (list_permut.permut_trans _ P2 _).
intros; subst; apply refl_equal.
apply list_permut.permut_sym.
intros; subst; apply refl_equal.
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
rewrite (proj2 (IHl1l2 u1 a'' u1_in_l1 a''_in_l2 u1_lt_a'')); apply refl_equal.
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
rewrite K; apply refl_equal.
(* 1/8 *)
apply False_rect; apply T; apply refl_equal.
(* 1/7 *)
intros H; rewrite H in T; apply False_rect; apply T; apply refl_equal.
(* 1/6 *)
intro; apply False_rect; apply (prec_antisym Prec f2); trivial.
(* 1/5 *)
intro; apply False_rect; apply (prec_antisym Prec f2); trivial.
(* 1/4 *)
intros [f2_diff_f2 _]; absurd (f2 = f2); trivial.
(* 1/3 *)
apply False_rect; apply T; apply refl_equal.
(* 1/2 *)
apply False_rect; apply T; apply refl_equal.
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
simpl; generalize (prec_eval_is_sound f2 f2); destruct (prec_eval f2 f2).
(* 1/6 *)
intros _; rewrite Sf; rewrite Sf in R'; rewrite Sf in T'; simpl in R'; simpl in T'.
assert (H' := remove_equiv_eval_list_is_sound (equiv_eval rpo_infos n) l2 l1).
case_eq (remove_equiv_eval_list (equiv_eval rpo_infos n) l2 l1).
intros [l2' l1'] H; rewrite H in R', T', H'.
assert (H'' : rpo_mul (bb rpo_infos) l1' l2').
destruct H' as [ll [Ell [P2 [P1 _]]]].
assert (Ell' : forall t1 t2, In (t1,t2) ll -> equiv t1 t2).
intros t1 t2 t1t2_in_ll.
generalize (equiv_eval_is_sound_weak rpo_infos n t1 t2).
rewrite (Ell _ _ t1t2_in_ll); intro t1_eq_t2; apply t1_eq_t2; apply refl_equal.
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
apply (equiv_sym _ _ equiv_equiv); apply Ell; left; apply refl_equal.
apply IHll with l1 l2; trivial.
intros; apply Ell; right; assumption.
refine (list_permut.permut_trans _ P1 _).
intros; subst; apply refl_equal.
apply list_permut.permut_sym.
intros; subst; apply refl_equal.
simpl; apply Pcons; [trivial | apply list_permut.permut_refl; intros; trivial].
refine (list_permut.permut_trans _ P2 _).
intros; subst; apply refl_equal.
apply list_permut.permut_sym.
intros; subst; apply refl_equal.
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
rewrite (proj2 (IHl1l2 u1 a'' u1_in_l1 a''_in_l2 u1_lt_a'')); apply refl_equal.
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
apply (equiv_sym _ _ equiv_equiv); assumption.
rewrite K; apply refl_equal.
(* 1/6 *)
intros H; rewrite H in T'; apply False_rect; apply T'; apply refl_equal.
(* 1/5 *)
intro; apply False_rect; apply (prec_antisym Prec f2); trivial.
(* 1/4 *)
intro; apply False_rect; apply (prec_antisym Prec f2); trivial.
(* 1/3 *)
intros [f2_diff_f2 _]; absurd (f2 = f2); trivial.
(* 1/2 *)
apply False_rect; apply T'; apply refl_equal.
(* 1/1 *)
apply False_rect; apply T'; apply refl_equal.
Qed.

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

Definition empty_rpo_infos (n : nat) : rpo_inf.
Proof. 
intro n;  constructor 1 with n (@nil (term*term)) (@nil (term*term)) (@nil (term*term));simpl;tauto.
Defined.


Definition add_equiv (rpo_infos:rpo_inf) t1 t2 (H:equiv t1 t2) : rpo_inf.
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

(*
Notation "{ ( x , z ) : a | P }" := ({ p : a | let (x,z) := p in P}) (x ident, z ident).

Obligations Tactic := idtac.

Program Fixpoint russell_equiv_dec (t1 t2 : term) : {equiv t1 t2}+{~equiv t1 t2} :=
  match (t1,t2) with
  | (Var x1, Var x2) => 
       if X.eq_dec x1 x2 then left _ _ else right _ _
  | (Term f1 l1, Term f2 l2) =>
     if F.Symb.eq_dec f1 f2
     then
       match status f1 with
       | Lex => 
            if russell_equiv_list_lex_dec l1 l2
            then left _ _
            else right _ _
       | Mul => 
           match russell_remove_equiv_list l1 l2 with
           | (nil, nil) => left _ _
           | _ => right _ _
           end
        end
     else right _ _
  | _ => right _ _
  end

with russell_equiv_list_lex_dec l1 l2 : {equiv_list_lex l1 l2}+{~equiv_list_lex l1 l2} :=
  match (l1,l2) with
  | (nil, nil) => left _ _
  | (t1 :: l1, t2 :: l2) =>
      if russell_equiv_dec t1 t2
      then 
         if russell_equiv_list_lex_dec l1 l2
         then left _ _
         else right _ _
      else right _ _
  | _ => right _ _
  end

with russell_remove_equiv (t : term) (l : list term) {struct l} : 
    { o : option (list term) | match o with 
                                          | None => forall t', In t' l -> ~equiv t t'
                                          | Some l' => 
                                              exists t', In t' l /\ equiv t t' /\ list_permut.permut equiv l (t' :: l')
                                         end} :=
  match l with
     | nil => @None _
     | a :: l => 
         if  russell_equiv_dec t a
         then Some l
         else
            match russell_remove_equiv t l with
            | None => @ None _
            | Some l' => Some (a :: l')
            end
    end

with  russell_remove_equiv_list (l1 l2 : list term) {struct l1} : 
    { (l1',l2')  : (list term) * (list term) | exists l, list_permut.permut equiv l1 (l1' ++ l) /\
                                                                       list_permut.permut equiv l2 (l2' ++ l) /\
                                                         (forall t1 t2, In t1 l1' -> In t2 l2' -> ~equiv t1 t2)}:=
    match (l1, l2) with
    | (_, nil) => (l1,l2)
    | (nil, _) => (l1,l2)
    | (a1 :: l1, l2) =>
          match russell_remove_equiv a1 l2 with
          | Some l2' =>  russell_remove_equiv_list l1 l2' 
          | None =>
               match russell_remove_equiv_list l1 l2 with
                      | (l1',l2') => (a1 :: l1', l2')
               end
          end
   end.
(*Obligations of russell_remove_equiv_list.
 Obligations of russell_equiv_dec. *)
(* 1/ 12 *)
Next Obligation of russell_equiv_dec.
simpl; intros t1 t2 v1 v2 H; injection H; clear H; 
intros; subst; apply Eq.
Defined.
(* 2/ 12 *)
Next Obligation of russell_equiv_dec.
simpl; intros t1 t2 v1 v2 H v1_diff_v2 t1_eq_t2; injection H; clear H; 
intros; subst; apply v1_diff_v2; inversion t1_eq_t2; subst; trivial.
Defined.
(* 3/ 12 *)
Next Obligation of russell_equiv_dec.
simpl.
intros t1 t2 f1 l1 f2 l2 H f1_eq_f2 Sf1 l1_eq_l2; injection H; clear H;
intros; subst; apply Eq_lex; trivial.
symmetry; trivial.
Defined.
(* 4/12 *)
Next Obligation of russell_equiv_dec.
simpl.
intros t1 t2 f1 l1 f2 l2 H f1_eq_f2 Sf1 l1_diff_l2 t1_eq_t2; injection H; clear H;
intros; subst.
apply l1_diff_l2; inversion t1_eq_t2 as [ | | g2 l1' l2' Sf2 P]; subst; trivial.
generalize l2; intro l; induction l as [ | t l].
apply Eq_list_nil.
apply Eq_list_cons; trivial.
apply Eq.
absurd (Lex = Mul).
discriminate.
rewrite Sf1; trivial.
Defined.
(* 5/12 *)
Next Obligation of russell_equiv_dec.
simpl.
intros russell_equiv_dec russell_equiv_list_lex_dec russell_remove_equiv russell_remove_equiv_list.
intros t1 t2 f1 l1 f2 l2 H f1_eq_f2 Sf1 H'; injection H; clear H;
intros; subst.
apply @Eq_mul.
symmetry; trivial.
destruct_call russell_remove_equiv_list as [[l1' l2'] [l [P1 [P2 H]]]]; simpl in *.
injection H'; intros; subst.
apply list_permut.permut_trans with l; trivial.
intros a b c _ _ _; apply (equiv_trans _ _ equiv_equiv).
apply list_permut.permut_sym; trivial.
intros a b _ _ ; apply (equiv_sym _ _ equiv_equiv).
Defined.
(* 6/12 *)
Next Obligation of russell_equiv_dec.
simpl.
intros russell_equiv_dec russell_equiv_list_lex_dec russell_remove_equiv russell_remove_equiv_list.
intros t1 t2 f1 l1 f2 l2 H f1_eq_f2 Sf1 [l1' l2'] H' H'' t1_eq_t2; injection H; clear H;
intros; subst.
inversion t1_eq_t2 as [ | f l1'' l2'' Sf2 | f l1'' l2'' Sf2 P]; subst.
destruct_call russell_remove_equiv_list as [[l1'' l2''] y]; simpl in *.
injection H''; clear H''; intros; subst l1'' l2''.
destruct y as [l [P1 [P2 H]]]; simpl in *.
assert (H'' : list_permut.permut equiv  l1' l2').
rewrite (list_permut.permut_app2 equiv_equiv l).
apply list_permut.permut_trans with l2; trivial. 
intros a b c _ _ _ ; apply (equiv_trans _ _ equiv_equiv).
apply list_permut.permut_sym; trivial. 
intros a b _ _ ; apply (equiv_sym _ _ equiv_equiv).
inversion H'' as [ | a b l1'' l2'' l2''']; subst.
apply H'; trivial.
apply (H a b); trivial.
left; trivial.
apply in_or_app; right; left; trivial.
absurd (Lex = Mul).
discriminate.
rewrite Sf1; trivial; symmetry; trivial.
destruct_call russell_remove_equiv_list as [[l1'' l2''] [l' [P1 [P2 H]]]]; simpl in *.
injection H''; clear H''; intros; subst l1'' l2''.
assert (H'' : list_permut.permut equiv  l1' l2').
rewrite (list_permut.permut_app2 equiv_equiv l').
apply list_permut.permut_trans with l2; trivial. 
intros a b c _ _ _ ; apply (equiv_trans _ _ equiv_equiv).
apply list_permut.permut_trans with l1; trivial. 
intros a b c _ _ _; apply (equiv_trans _ _ equiv_equiv).
apply list_permut.permut_sym; trivial. 
intros a b _ _ ; apply (equiv_sym _ _ equiv_equiv).
inversion H'' as [ | a b l1'' l2'' l2''']; subst.
apply H'; trivial.
apply (H a b); trivial.
left; trivial.
apply in_or_app; right; left; trivial.
Defined.
(* 7/12 *)
Next Obligation of russell_equiv_dec.
simpl.
simpl; intros _ _ _ _ _ _ _ _ _ _ _ _ _.
intros;  discriminate.
Defined.
(* 8/12 *)
Next Obligation of russell_equiv_dec.
simpl; intros; discriminate.
Defined.
(* 9/12 *)
Next Obligation of russell_equiv_dec.
simpl.
intros t1 t2 f1 l1 f2 l2 H f1_diff_f2 t1_eq_t2; injection H; clear H;
intros; subst; apply f1_diff_f2; inversion t1_eq_t2; subst; trivial.
Defined.
(* 10/12 *)
Next Obligation of russell_equiv_dec.
simpl.
intros t1 t2 [u1 u2] [H H'] H'' t1_eq_t2; injection H''; clear H'';
intros; subst; inversion t1_eq_t2; subst.
destruct t2 as [v2 | f2 l2].
apply (H' v2 v2); trivial.
apply (H f2 l2 f2 l2); trivial.
apply (H f l1 f l2); trivial.
apply (H f l1 f l2); trivial.
Defined.
(* 11/12 *)
Next Obligation of russell_equiv_dec.
simpl; intros; intuition; discriminate.
Defined.
(* 12/12 *)
Next Obligation of russell_equiv_dec.
simpl; intros; intuition; discriminate.
Defined.

(* 1/7 *)
Next Obligation of russell_equiv_list_lex_dec.
simpl; intros l1 l2 H; injection H; clear H; 
intros; subst; apply Eq_list_nil.
Defined.
(* 2/7 *)
Next Obligation of russell_equiv_list_lex_dec.
simpl; intros k1 k2 t1 l1 t2 l2 H t1_eq_t2 l1_eq_l2; injection H; clear H;
intros; subst; apply Eq_list_cons; trivial.
Defined.
(* 3/7 *)
Next Obligation of russell_equiv_list_lex_dec.
simpl; intros k1 k2 t1 l1 t2 l2 H t1_eq_t2 l1_diff_l2 k1_eq_k2; injection H; clear H;
intros; subst; apply l1_diff_l2; inversion k1_eq_k2; trivial.
Defined.
(* 4/7 *)
Next Obligation of russell_equiv_list_lex_dec.
simpl; intros k1 k2 t1 l1 t2 l2 H t1_diff_t2 k1_eq_k2; injection H; clear H;
intros; subst; apply t1_diff_t2; inversion k1_eq_k2; trivial.
Defined.
(* 5/7 *)
Next Obligation of russell_equiv_list_lex_dec.
simpl; intros k1 k2 [l1 l2] [H H'] H'' k1_eq_k2; injection H''; clear H'';
intros; subst; inversion k1_eq_k2 as [ | t1 t2 l1 l2]; subst.
apply H'; trivial.
apply (H t1 l1 t2 l2); trivial.
Defined.
(* 6/7 *)
Next Obligation of russell_equiv_list_lex_dec.
simpl; intros; intuition; discriminate.
Defined.
(* 7/7 *)
Next Obligation of russell_equiv_list_lex_dec.
simpl; intros; intuition; discriminate.
Defined.

(* 1/4 *)
Next Obligation of russell_remove_equiv.
simpl; intros t l H t' t'_in_l; subst; contradiction.
Defined.
(* 2/4 *)
Next Obligation of russell_remove_equiv.
simpl; intros t k a l H t_eq_a; subst.
exists a; repeat split; trivial.
left; trivial.
apply list_permut.permut_refl; trivial. 
intros a' _; apply (equiv_refl _ _ equiv_equiv).
Defined.
(* 3/4 *)
Next Obligation of russell_remove_equiv.
simpl.
intros russell_equiv_dec russell_equiv_list_lex_dec russell_remove_equiv russell_remove_equiv_list.
intros t k a l H; subst; simpl.
intros t_diff_a H t' [t'_eq_a | t'_in_l]; subst; trivial.
destruct_call russell_remove_equiv as [[l' | ] H']; simpl in *.
discriminate.
apply H'; trivial.
Defined.
(* 4/4 *)
Next Obligation of russell_remove_equiv.
simpl.
intros russell_equiv_dec russell_equiv_list_lex_dec russell_remove_equiv russell_remove_equiv_list.
intros t k a l H; subst; simpl.
intros t_diff_a l' H.
destruct_call russell_remove_equiv as [[ k' | ] y]; simpl in *.
injection H; clear H; intros; subst.
destruct y as [t' [t'_in_l [t_eq_t' P]]].
exists t'; repeat split; trivial.
right; trivial.
apply (@Pcons _ _ equiv a a l (t' :: nil) k'); trivial.
apply (equiv_refl _ _ equiv_equiv).
discriminate.
Defined.

(* 1/6 *)
Next Obligation of russell_remove_equiv_list.
simpl; intros l1 l2 l H; injection H; clear H; 
intros; subst; exists (@nil term); repeat split.
rewrite <- app_nil_end; apply list_permut.permut_refl.
intros a _; apply (equiv_refl _ _ equiv_equiv).
simpl; apply Pnil.
intros; contradiction.
Defined.
(* 2/6 *)
Next Obligation of russell_remove_equiv_list.
simpl; intros l1 l2 l H H'; injection H'; clear H';
intros; subst; exists (@nil term); repeat split.
simpl; apply Pnil.
rewrite <- app_nil_end; apply list_permut.permut_refl.
intros a _; apply (equiv_refl _ _ equiv_equiv).
intros; contradiction.
Defined.
(* 3/6 *)
Next Obligation of russell_remove_equiv_list.
simpl.
intros russell_equiv_dec russell_equiv_list_lex_dec russell_remove_equiv russell_remove_equiv_list.
intros k1 l2 a1 l1 k2 H H' l2' H''; injection H'; clear H'; intros; subst.
destruct_call russell_remove_equiv_list as [x y]; simpl in *.
destruct x as [l1' l2'']; simpl in *.
destruct y as [l [P1 [P2 H']]].
destruct_call russell_remove_equiv as [[ k2' | ] y]; simpl in *.
injection H''; clear H''; intros; subst k2'.
destruct y as [t' [t'_in_l2 [a1_eq_t' P]]].
exists (a1 :: l); repeat split.
apply Pcons; trivial.
apply Eq.
apply list_permut.permut_trans with (t' :: l2'); trivial.
intros a b c _ _ _ ; apply (equiv_trans _ _ equiv_equiv).
apply Pcons; trivial.
apply (equiv_sym _ _ equiv_equiv); trivial.
trivial.
discriminate.
Defined.
(* 4/6 *)
Next Obligation of russell_remove_equiv_list.
simpl.
intros russell_equiv_dec russell_equiv_list_lex_dec russell_remove_equiv russell_remove_equiv_list.
intros k1 l2 a1 l1 k2 H H' H'' l1' l2' H'''; injection H'; clear H'; intros; subst.
destruct_call russell_remove_equiv_list as [[l1'' l2''] [l' [P1 [P2 H']]]]; simpl in *.
injection H'''; clear H'''; intros; subst l1'' l2''.
destruct_call russell_remove_equiv as [[ l2'' | ] H''']; simpl in *.
discriminate.
exists l'; repeat split; trivial.
apply (@Pcons _ _ equiv a1 a1 l1 (@nil term) (l1' ++ l')); trivial.
apply Eq.
intros t1 t2 [a1_eq_t1 | t1_in_l1'] t2_in_l2'.
subst; intro t1_eq_t2.
assert (H'''' : exists t2', In t2' l2 /\ equiv t2 t2').
destruct (In_split _ _ t2_in_l2') as [k2' [k2'' H'''']]; subst l2'.
rewrite <- ass_app in P2; simpl in P2.
destruct (@permut_inv_right_strong _ _ equiv _ _ _ _ P2) as [t2' [k1' [k1'' [t2_eq_t2' [H'''' _]]]]].
exists t2'; split.
subst l2; apply in_or_app; right; left; trivial.
apply (equiv_sym _ _ equiv_equiv); trivial.
destruct H'''' as [t2' [t2'_in_l2 t2_eq_t2']].
apply (H''' t2'); trivial.
apply (equiv_trans _ _ equiv_equiv) with t2; trivial.
apply H'; trivial.
Defined.
(*5/6 *)
Next Obligation of russell_remove_equiv_list.
simpl.
intros russell_equiv_dec russell_equiv_list_lex_dec russell_remove_equiv russell_remove_equiv_list.
intros _ _ _ _ t1 t2 l2; discriminate.
Defined.
(* 6/6 *)
Next Obligation of russell_remove_equiv_list.
simpl.
intros russell_equiv_dec russell_equiv_list_lex_dec russell_remove_equiv russell_remove_equiv_list.
intros _ _ _ _ t1 l1 t2 l2 l; discriminate.
Defined.
*)
End S.
End Make.
(*
Module MakeExt (T1: Term).

Module Fext <: Signature.
Module Symb <: decidable_set.S.
Inductive B : Type :=
| Original : forall f : T1.symbol, B
| Bottom : B.

Definition A := B.
Definition eq_bool (ff : A)  (gg : A) : bool :=
match ff, gg with
| Original f, Original g =>  T1.F.Symb.eq_bool f g
| Original _, Bottom =>  false
| Bottom, Original g =>  false
| Bottom, Bottom => true
end.

Lemma eq_bool_ok : forall a1 a2, match eq_bool a1 a2 with true => a1 = a2 | false => ~ a1 = a2 end.
Proof.
intros [f | ] [g | ]; simpl.
generalize (T1.eq_symb_bool_ok f g); case (T1.eq_symb_bool f g).
intros; subst; apply refl_equal.
intros f_diff_g f_eq_g; apply f_diff_g; injection f_eq_g; intros; assumption.
discriminate.
discriminate.
apply refl_equal.
Defined.

End Symb.

Definition arity (ff : Symb.A) : arity_type :=
match ff with
| Symb.Original f => T1.F.arity f
| Bottom => Free 0
end.

End Fext.

Module T1Ext := term.Make (Fext) (T1.X). 

Module P1Ext <: Precedence with Definition A := T1Ext.symbol.

Definition A := T1Ext.symbol.
Definition status (ff : A) : status_type :=
  match ff with
  | Fext.Symb.Original f => P1.status f
  | Bottom => Lex
  end.

Definition prec_bool (ff gg : A) : bool :=
  match ff, gg with
 | Fext.Symb.Original f,  Fext.Symb.Original g  => P1.prec_bool f g
 | Fext.Symb.Original f, Fext.Symb.Bottom => false
 | Fext.Symb.Bottom, Fext.Symb.Original g  => false
 | Fext.Symb.Bottom, Fext.Symb.Bottom => false
end.

Definition prec ff gg := prec_bool ff gg = true.

Lemma prec_bool_ok : forall a1 a2, match prec_bool a1 a2 with true => prec a1 a2 | false => ~prec a1 a2 end.
Proof.
unfold prec; intros [f | ] [g | ]; simpl.
case (P1.prec_bool f g).
apply refl_equal.
discriminate.
discriminate.
discriminate.
discriminate.
Qed.

Lemma prec_antisym : forall s, prec s s -> False.
Proof.
unfold prec; intros [f | ]; simpl.
generalize (P1.prec_bool_ok f f); case (P1.prec_bool f f).
intros P _; apply (P1.prec_antisym f P).
intros _; discriminate.
discriminate.
Qed.

Lemma prec_transitive : transitive A prec.
Proof.
unfold prec; intros [f | ] [g | ] [h | ]; simpl; intros H1 H2; try discriminate.
assert (K1 := P1.prec_bool_ok f g); rewrite H1 in K1.
assert (K2 := P1.prec_bool_ok g h); rewrite H2 in K2.
generalize (P1.prec_bool_ok f h).
case (P1.prec_bool f h).
intros _; apply refl_equal.
intro K3; apply False_rect; apply K3.
apply (P1.prec_transitive _ _ _ K1 K2).
Qed.

End P1Ext.

Module RPOExt := Make (T1Ext) (P1Ext).

Section Rpo_ext.
Parameter rep : T1.F.Symb.A -> T1.F.Symb.A.
Parameter rep_ok : forall f, P1.status f = P1.status (rep f).
Parameter rep_max : forall f n m, T1.F.arity f = Free n -> T1.F.arity (rep f) = Free m -> n <= m.

Fixpoint same_list (n : nat) : list T1Ext.term :=
match n with 
| 0 => nil
| S n => (T1Ext.Term Fext.Symb.Bottom nil) :: (same_list n)
end.

Fixpoint translate (t : T1.term) : T1Ext.term :=
match t with
| T1.Var x => T1Ext.Var x
| T1.Term f l => 
       let trans_list :=
         (fix trans_list (l : list T1.term) {struct l} : list T1Ext.term :=
            match l with
            | nil => nil
            | t :: lt => (translate t) :: (trans_list lt)
            end) in
        T1Ext.Term (Fext.Symb.Original (rep f)) ((trans_list l) ++ 
        (same_list ((match T1.F.arity f with Free n => n | _ => 2 end) -  
                            (match T1.F.arity (rep f) with Free n => n | _ => 2 end))))
   end.


Definition rpo n (s t : T1.term) := RPOExt.rpo n (translate s) (translate t).
Definition rpo_eq n (s t : T1.term) := RPOExt.rpo_eq n (translate s) (translate t).
Definition equiv (s t : T1.term) := RPOExt.equiv (translate s) (translate t).

Lemma rpo_trans : forall bb s t u, rpo bb s t -> rpo bb t u -> rpo bb s u.
Proof.
exact (fun bb s t u H1 H2 => RPOExt.rpo_trans _ _ _ _ H1 H2).
Qed.

Lemma rpo_rpo_eq : forall bb s t u, rpo bb s t -> rpo_eq bb t u -> rpo bb s u.
Proof.
intros bb s t u H1 H2; inversion H2 as [a b H3 | a b H3]; subst.
unfold rpo; rewrite <- (RPOExt.equiv_rpo_equiv_1 _ H3); assumption.
apply RPOExt.rpo_trans with (translate t); assumption.
Qed.

Lemma wf_rpo : well_founded P1.prec -> forall bb, well_founded (rpo bb).
Proof.
intros Wp bb; apply wf_inverse_image.
apply RPOExt.wf_rpo.
intros [f |].
assert (Acc_f := Wp f).
induction Acc_f as [f Acc_f IH]; apply Acc_intro; intros [g | ] H;
unfold P1Ext.prec in H; simpl in H.
apply IH; generalize (P1.prec_bool_ok g f); rewrite H; intro; assumption.
discriminate.
apply Acc_intro; intros [g | ] H; unfold P1Ext.prec in H; simpl in H; discriminate.
Qed.

Definition rpo_eval n s t := 
  RPOExt.rpo_eval (RPOExt.empty_rpo_infos n) (T1Ext.size (translate s) + T1Ext.size (translate t))
    (translate s) (translate t).

Definition equiv_eval n s t := 
  RPOExt.equiv_eval (RPOExt.empty_rpo_infos n) (T1Ext.size (translate s) + T1Ext.size (translate t))
    (translate s) (translate t).

End Rpo_ext.

End MakeExt.
*)

(* 
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../basis/" "-I" "../list_extensions/" "-I" "../term_algebra/") ***
*** End: ***
 *)
 

