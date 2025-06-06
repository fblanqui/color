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


From Stdlib Require Import Relations List.
From CoLoR Require Import list_sort term_spec.

Set Implicit Arguments.

(** ** Module Type Term_ordering, 
** Definition of a total and decidable ordering on terms from a total and decidable ordering on symbols and variables. *)
Module Type Term_ordering.

Declare Module Import T : term_spec.Term.
Declare Module OF : ordered_set.S with Definition A := T.symbol.
Declare Module OX : ordered_set.S with Definition A := T.variable.

Definition A := term.
Definition eq_bool := eq_bool.
Definition eq_bool_ok := eq_bool_ok.

(** *** Definition of the ordering. *)
Fixpoint o_bool (t1 t2:term) {struct t1} : bool :=
  match t1, t2 with
  | Var v1, Var v2 => OX.o_bool v1 v2
  | Var _, Term _ _ => false
  | Term _ _, Var _ => true
  | Term f1 l1, Term f2 l2 =>
      if F.Symb.eq_bool f1 f2
      then
         let o_term_list :=
           (fix o_term_list (l1:list term) : list term -> bool :=
              fun l2 =>
                match l1, l2 with
                | nil, nil => true
                |  _ :: _, nil => true
                | nil, _ :: _ => false
                | h1 :: tl1, h2 :: tl2 =>
                    if eq_bool h1 h2
                    then o_term_list tl1 tl2
                    else o_bool h1 h2
                end) in
         o_term_list l1 l2
      else OF.o_bool f1 f2
  end.

Definition o t1 t2 := o_bool t1 t2 = true.

(** *** Properties of the ordering. *)
Axiom o_bool_ok : forall t1 t2, match o_bool t1 t2 with true => o t1 t2 | false => ~o t1 t2 end.
Axiom o_total : forall t1 t2 : term, {o t1 t2} + {o t2 t1}.
Axiom o_proof : order term o.

End Term_ordering.


(** ** A functor building a Module Term_ordering from a term algebra
**  and total and decidable orderings on symbols and variables. *)
Module Make (T1: term_spec.Term) 
(OF1 : ordered_set.S with Definition A := T1.symbol) 
(OX1 : ordered_set.S with Definition A := T1.variable) <:
  Term_ordering with Module T := T1 
                          with Module OF := OF1
                          with Module OX := OX1
	                  with Definition A := T1.term.

Module Import T := T1.
Module OF := OF1.
Module OX := OX1.

Definition A := term.
Definition eq_bool := T1.eq_bool.
Definition eq_bool_ok := T1.eq_bool_ok.

(** *** Definition of the ordering. *)
Fixpoint o_bool (t1 t2:term) {struct t1} : bool :=
  match t1, t2 with
  | Var v1, Var v2 => OX.o_bool v1 v2
  | Var _, Term _ _ => false
  | Term _ _, Var _ => true
  | Term f1 l1, Term f2 l2 =>
      if F.Symb.eq_bool f1 f2
      then
         let o_term_list :=
           (fix o_term_list (l1:list term) : list term -> bool :=
              fun l2 =>
                match l1, l2 with
                | nil, nil => true
                |  _ :: _, nil => true
                | nil, _ :: _ => false
                | h1 :: tl1, h2 :: tl2 =>
                    if eq_bool h1 h2
                    then o_term_list tl1 tl2
                    else o_bool h1 h2
                end) in
         o_term_list l1 l2
      else OF.o_bool f1 f2
  end.

Definition o t1 t2 := o_bool t1 t2 = true.

(** Decidability. *)
Lemma o_bool_ok : forall t1 t2, match o_bool t1 t2 with true => o t1 t2 | false => ~o t1 t2 end.
intros t1 t2; unfold o; case (o_bool t1 t2).
reflexivity.
discriminate.
Defined.

(** *** Properties of the ordering.
 Totality. *)
Definition o_term_list :=
  (fix o_term_list (l1:list term) : list term -> bool :=
     fun l2 =>
       match l1, l2 with
       | nil, nil => true
       | _ :: _, nil => true
       | nil, _ :: _ => false
       | h1 :: tl1, h2 :: tl2 =>
           if T1.eq_bool h1 h2
           then o_term_list tl1 tl2
           else o_bool h1 h2
       end).

Theorem o_total : 
  forall t1 t2 : term, {o t1 t2} + {o t2 t1}.
Proof.
unfold o;
apply term_rec7 with
(P2:= fun t1 t2 => {o_bool t1 t2 = true} + {o_bool t2 t1 = true})
(Pl2 := fun l1 l2 => {o_term_list l1 l2 = true} + {o_term_list l2 l1 = true}).
intros x1 t2; destruct t2 as [x2 | f2 l2]; simpl.
destruct (OX1.o_total x1 x2) as [x1_le_x2 | x2_le_x1]; [left | right].
generalize (OX1.o_bool_ok x1 x2); case (OX1.o_bool x1 x2).
intros _; reflexivity.
intro x1_not_le_x2; absurd (OX1.o x1 x2); assumption.
generalize (OX1.o_bool_ok x2 x1); case (OX1.o_bool x2 x1).
intros _; reflexivity.
intro x2_not_le_x1; absurd (OX1.o x2 x1); assumption.
right; reflexivity.
intros t1 x2; destruct t1 as [ x1 | f1 l1].
destruct (OX.o_total x1 x2) as [o_x1_x2 | o_x2_x1]; [left | right].
simpl; generalize (OX1.o_bool_ok x1 x2); case (OX1.o_bool x1 x2).
intros _; reflexivity.
intro x1_not_le_x2; absurd (OX1.o x1 x2); assumption.
simpl; generalize (OX1.o_bool_ok x2 x1); case (OX1.o_bool x2 x1).
intros _; reflexivity.
intro x2_not_le_x1; absurd (OX1.o x2 x1); assumption.
simpl; left; reflexivity.
intros f1 f2 l1 l2 Hrec; simpl.
generalize (F.Symb.eq_bool_ok f1 f2); case (F.Symb.eq_bool f1 f2); [intro f1_eq_f2 | intro f1_diff_f2];
(generalize (F.Symb.eq_bool_ok f2 f1); case (F.Symb.eq_bool f2 f1); [intro f2_eq_f1 | intro f2_diff_f1]).
elim Hrec; intro o_l1_l2; [ left | right ]; trivial.
absurd (f2 = f1); auto.
absurd (f1 = f2); auto.
destruct (OF.o_total f1 f2) as [f1_le_f2 | f2_le_f1]; [left | right].
generalize (OF.o_bool_ok f1 f2); case (OF.o_bool f1 f2).
intros _; reflexivity.
intro f1_not_le_f2; absurd (OF.o f1 f2); assumption.
generalize (OF.o_bool_ok f2 f1); case (OF.o_bool f2 f1).
intros _; reflexivity.
intro f2_not_le_f1; absurd (OF.o f2 f1); assumption.
intro l1; induction l1 as [ | a1 l1].
destruct l2 as [ | a2 l2 ] ; [left | right]; simpl; trivial.
destruct l2 as [ | a2 l2 ].
left; simpl; trivial.
intro Hrec.
simpl; generalize (T1.eq_bool_ok a1 a2); case (T1.eq_bool a1 a2); [intro a1_eq_a2 | intro a1_diff_a2]; 
(generalize (T1.eq_bool_ok a2 a1); case (T1.eq_bool a2 a1); [intro a2_eq_a1 | intro a2_diff_a1]).
apply IHl1; intros; apply Hrec; right; trivial.
absurd (a2 = a1); auto.
absurd (a1 = a2); auto.
apply Hrec; left; trivial.
Qed.

Lemma o_term_list_is_o_term_list :
  forall l1 l2,
  o_term_list l1 l2 = 
  ((fix o_term_list (l : list term) : list term -> bool :=
    fun l' : list term =>
    match l with
    | nil => match l' with
             | nil => true
             | _ :: _ => false
             end
    | h :: tl =>
        match l' with
        | nil => true
        | h' :: tl' => if T1.eq_bool h h' then o_term_list tl tl' else o_bool h h'
        end
   end)) l1 l2. 
Proof.
induction l1; induction l2; trivial.
Qed.



(** Antisymmetry *)
Theorem o_anti_sym :
 forall t1 t2, o t1 t2 -> o t2 t1 -> t1 = t2.
Proof.
elim OX.o_proof; intros Rv Tv Av;
elim OF.o_proof; intros Rs Ts As;
apply (term_rec7 
(fun t1 t2 => o t1 t2 -> o t2 t1 -> t1 = t2)
 (fun l1 l2 => o_term_list l1 l2 = true -> o_term_list l2 l1 = true -> l1 = l2)).
intros x1; destruct t2 as [ x2 | f2 l2 ].
unfold o; simpl; intros H1 H2.
generalize (OX1.o_bool_ok x1 x2); rewrite H1; clear H1; intro H1.
generalize (OX1.o_bool_ok x2 x1); rewrite H2; clear H2; intro H2.
rewrite (Av x1 x2 H1 H2); trivial.
intros; discriminate.
intros t1 x2; destruct t1 as [ x1 | f1 l1 ].
unfold o; simpl; intros H1 H2.
generalize (OX1.o_bool_ok x1 x2); rewrite H1; clear H1; intro H1.
generalize (OX1.o_bool_ok x2 x1); rewrite H2; clear H2; intro H2.
rewrite (Av x1 x2 H1 H2); trivial.
intros; discriminate.
intros f1 f2 l1 l2 Hrec; simpl.
unfold o; simpl;
generalize (F.Symb.eq_bool_ok f1 f2); case (F.Symb.eq_bool f1 f2); [intro f1_eq_f2 | intro f1_diff_f2];
(generalize (F.Symb.eq_bool_ok f2 f1); case (F.Symb.eq_bool f2 f1); [intro f2_eq_f1 | intro f2_diff_f1]).
intros H1 H2; subst f1; rewrite (Hrec H1 H2); trivial.
absurd (f2 =f1); auto.
absurd (f1 =f2); auto.
intros H1 H2; absurd (f1 = f2); trivial; apply As.
generalize (OF1.o_bool_ok f1 f2); rewrite H1; intro; assumption.
generalize (OF1.o_bool_ok f2 f1); rewrite H2; intro; assumption.
fix o_anti_sym 1; intro l1; case l1; clear l1; [idtac | intros a1 l1].
intros l2 _; case l2; clear l2; [trivial | intros a2 l2]; intros; discriminate.
intros l2; case l2; clear l2; [intros; discriminate | intros a2 l2 Hrec; simpl].
generalize (T1.eq_bool_ok a1 a2); case (T1.eq_bool a1 a2); [intro a1_eq_a2 | intro a1_diff_a2];
(generalize (T1.eq_bool_ok a2 a1); case (T1.eq_bool a2 a1); [intro a2_eq_a1 | intro a2_diff_a1]).
intros; apply f_equal2; [assumption | apply o_anti_sym; trivial].
intros; apply Hrec; trivial; right; assumption.
absurd (a2 = a1); subst; trivial.
absurd (a1 = a2); subst; trivial.
intros H3 H4; absurd (a1 = a2); trivial.
apply Hrec; trivial; left; trivial.
Qed.

(** [o_term] is an order. *)
Theorem o_proof : order term o.
Proof.
elim OX.o_proof; intros Rv Tv Av; 
elim OF.o_proof; intros Rs Ts As.
unfold o; repeat split.
unfold reflexive; intro t; pattern t;
apply term_rec4 with (fun l => o_term_list l l = true); clear t.
intros v; simpl; generalize (OX1.o_bool_ok v v); case (OX1.o_bool v v).
intros _; reflexivity.
intros v_not_le_v; apply False_rect; apply v_not_le_v; apply Rv.
intros f l l_le_l; simpl.
generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); 
[intros _ | intro f_diff_f; apply False_rect; apply f_diff_f; reflexivity].
rewrite <- o_term_list_is_o_term_list; assumption.
fix o_proof 1; intro l; case l; clear l.
intros _; reflexivity.
intros t l H; simpl.
generalize (T1.eq_bool_ok t t); case (T1.eq_bool t t); [intros _ | intro t_diff_t; apply False_rect; apply t_diff_t; reflexivity].
apply o_proof.
intros; apply H; right; trivial.

unfold transitive; intro t; pattern t; 
apply term_rec4 with (fun l1 => forall l2 l3, 
o_term_list l1 l2 = true -> o_term_list l2 l3 = true -> o_term_list l1 l3 = true); clear t.
intros x1 t2 t3; destruct t2 as [ x2 | f2 l2 ]; 
destruct t3 as [ x3 | f3 l3 ]; simpl.
intros x1_le_x2 x2_le_x3; 
assert (x1_le_x2' := OX1.o_bool_ok x1 x2); rewrite x1_le_x2 in x1_le_x2';
assert (x2_le_x3' := OX1.o_bool_ok x2 x3); rewrite x2_le_x3 in x2_le_x3'.
generalize (OX1.o_bool_ok x1 x3); case (OX1.o_bool x1 x3).
intros _; reflexivity.
intro x1_not_le_x3; apply False_rect; apply x1_not_le_x3; apply Tv with x2; assumption.
intros; discriminate.
intros; discriminate.
intros; discriminate.
intros f1 l1 Hrec t2 t3; destruct t2 as [ x2 | f2 l2 ];
destruct t3 as [ x3 | f3 l3 ]; simpl.
intros _ _; reflexivity.
intros; discriminate.
intros _ _; reflexivity.
generalize (F.Symb.eq_bool_ok f1 f2); case (F.Symb.eq_bool f1 f2); [intro f1_eq_f2; subst f1 | intro f1_diff_f2];
(generalize (F.Symb.eq_bool_ok f2 f3); case (F.Symb.eq_bool f2 f3); [intro f2_eq_f3; subst f2 | intro f2_diff_f3]).
rewrite <- o_term_list_is_o_term_list.
intro l1_le_l2; rewrite <- o_term_list_is_o_term_list.
intro l2_le_l3; rewrite <- o_term_list_is_o_term_list.
apply Hrec with l2; assumption.
intros _ f2_le_f3; assumption.
intros f1_le_f3; rewrite <- o_term_list_is_o_term_list.
intros l2_le_l3; rewrite <- o_term_list_is_o_term_list.
generalize (F.Symb.eq_bool_ok f1 f3); case (F.Symb.eq_bool f1 f3); [intro f1_eq_f3; apply False_rect; apply f1_diff_f2 | intros _]; assumption.
intros f1_le_f2 f2_le_f3; generalize (F.Symb.eq_bool_ok f1 f3); case (F.Symb.eq_bool f1 f3); [intro f1_eq_f3 | intro f1_diff_f3].
subst f3; apply False_rect; apply f1_diff_f2; apply As.
generalize (OF1.o_bool_ok f1 f2); rewrite f1_le_f2; intro; assumption.
generalize (OF1.o_bool_ok f2 f1); rewrite f2_le_f3; intro; assumption.
generalize (OF1.o_bool_ok f1 f3); case (OF1.o_bool f1 f3); [intro f1_le_f3 | intros f1_not_le_f3].
reflexivity.
apply False_rect; apply f1_not_le_f3; apply Ts with f2.
generalize (OF1.o_bool_ok f1 f2); rewrite f1_le_f2; intro; assumption.
generalize (OF1.o_bool_ok f2 f3); rewrite f2_le_f3; intro; assumption.
fix o_proof 1; intro l1; case l1; clear l1.
intros _ l2; case l2; clear l2.
intros l3; case l3; clear l3.
intros _ _; reflexivity.
intros t2 l2 _; intros; discriminate.
intros t2 l2 l3; intros; discriminate.
intros t1 l1 Hrec l2; case l2; clear l2; [idtac | intros t2 l2];
(intros l3; case l3; clear l3; [idtac | intros t3 l3]; simpl).
intros _ _; reflexivity.
intros; discriminate.
intros _ _; reflexivity.
generalize (T1.eq_bool_ok t1 t2); case (T1.eq_bool t1 t2); [intro t1_eq_t2; subst t1 | intro t1_diff_t2];
(generalize (T1.eq_bool_ok t2 t3); case (T1.eq_bool t2 t3); [intro t2_eq_t3; subst t2 | intro t2_diff_t3]).
apply o_proof; intros t t_in_l1; apply Hrec; right; assumption.
intros _ t2_le_t3; assumption.
intros t1_le_t3 l2_le_l3; generalize (T1.eq_bool_ok t1 t3); case (T1.eq_bool t1 t3); 
[intro t1_eq_t3; apply False_rect; apply t1_diff_t2; apply t1_eq_t3 | intros _; assumption].
intros t1_le_t2 t2_le_t3; generalize (T1.eq_bool_ok t1 t3); case (T1.eq_bool t1 t3); [intro t1_eq_t3 | intros t1_diff_t3].
subst t3; apply False_rect; apply t1_diff_t2.
apply o_anti_sym; assumption.
apply Hrec with t2; trivial; left; reflexivity.
intros t1 t2; apply o_anti_sym.
Qed.

End Make.
