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

(** * Term algebra defined as functor from a Module Signature and a Module Variable.*)


From Coq Require Import Recdef List Arith Setoid.
From CoLoR Require Import closure more_list list_permut list_set decidable_set term_spec.

Set Implicit Arguments.


(** * A functor building a Term Module from a Signature and a set of Variables.*)

Module Make' (F1 : Signature) (X1 : decidable_set.S) <: 
     Term with Module F := F1 with Module X := X1.

Module F := F1.
Import F1.

Module X := X1.
Import X1.

Notation symbol := Symb.A.
Notation eq_symb_bool := Symb.eq_bool.

Notation variable := X.A.
Notation eq_var_bool := X.eq_bool.

Module EX := decidable_set.Convert (X).
Module VSet : 
   list_set.S with Definition EDS.A := X.A
                 with Definition EDS.eq_A := @eq X.A := list_set.Make (EX).

Lemma eq_symb_bool_refl : forall f, eq_symb_bool f f = true.
Proof.
intro f.
generalize (Symb.eq_bool_ok f f); case (eq_symb_bool f f).
intros _; reflexivity.
intro f_diff_f; apply False_rect; apply f_diff_f; reflexivity.
Qed.

Lemma eq_var_bool_refl : forall v, eq_var_bool v v = true.
Proof.
intro v.
generalize (X.eq_bool_ok v v); case (eq_var_bool v v).
intros _; reflexivity.
intro v_diff_v; apply False_rect; apply v_diff_v; reflexivity.
Qed.

(** Definition of terms. 
Arity is not taken into account, and terms may be hill-formed. *)

Inductive term : Type :=
  | Var : variable -> term
  | Term : symbol -> list term -> term.

(** Definition and a few properties of the size of a term.*)
Fixpoint size (t:term) : nat :=
  match t with
  | Var v => 1
  | Term _ l =>
       let size_list :=
         (fix size_list (l : list term) {struct l} : nat :=
            match l with
            | nil => 0
            | t :: lt => size t + size_list lt
            end) in
        1 + size_list l
   end.

Definition size_unfold :
 forall t,
 size t = match t with
          | Var _ => 1
          | Term f l => 1 + list_size size l
          end.
Proof.
intro t; case t; clear t.
intro v; reflexivity.
intros f l; simpl; apply f_equal.
revert l; fix size_unfold 1.
intro l; case l; clear l.
reflexivity.
intros t l; simpl; rewrite size_unfold; reflexivity.
Defined.

Lemma size_ge_one : forall t, 1 <= size t.
Proof.
intro t; case t; clear t.
intro v; apply le_n.
intros f l; rewrite size_unfold; apply le_n_S; apply Nat.le_0_l.
Qed.

Function var_in_term_list (x : variable) (l : list term) 
{ measure (list_size size) l } : bool :=
  match l with
    | nil => false
    | (Var y) :: l => orb (eq_var_bool x y) (var_in_term_list x l) 
    | (Term _ ll) :: l => orb (var_in_term_list x ll) (var_in_term_list x l)
end.
Proof.
intros _ l t l' y H1 H2;  simpl; auto with arith.
intros _ l t l' f ll H1 H2; simpl; auto with arith.
intros _ l t l' f ll H1 H2; simpl; apply Nat.lt_le_trans with (size (Term f ll)).
rewrite size_unfold; simpl; auto with arith.
simpl; auto with arith.
Defined.

Definition var_in_term (v : variable) (t : term) : bool :=
	match t with
	| Var x =>  (eq_var_bool x v) 
        | Term _ l => var_in_term_list v l
        end.

Fixpoint var_list (t : term) : list variable :=
  match t with
  | Var x => (x :: nil)
  | Term _ l =>
       let var_list_list :=
         (fix var_list_list (l : list term) {struct l} : list variable :=
            match l with
            | nil => nil
            | t :: lt => var_list t ++ var_list_list lt
            end) in
        var_list_list l
   end.

Function var_list_list (l : list term) {struct l} : list variable :=
            match l with
            | nil => nil
            | t :: lt => var_list t ++ var_list_list lt
            end.

Lemma var_list_list_app : forall l1 l2, var_list_list (l1 ++ l2) = (var_list_list l1) ++ var_list_list l2.
Proof.
fix var_list_list_app 1; intros l1 l2; case l1; clear l1.
reflexivity.
intros t1 l1; simpl; rewrite <- ass_app; rewrite var_list_list_app; reflexivity.
Qed.

Lemma in_var_list_list : forall l v, In v (var_list_list l) -> exists t, In t l /\ In v (var_list t).
Proof.
fix in_var_list_list 1; intro l; case l; clear l.
intros v v_in_nil; contradiction.
simpl; intros t l v v_in_tl; destruct (in_app_or _ _ _ v_in_tl) as [v_in_t | v_in_l].
exists t; split; [left; apply eq_refl | assumption].
destruct (in_var_list_list l v v_in_l) as [u [u_in_l v_in_u]].
exists u; split; [right | idtac]; assumption.
Qed.

Lemma mem_var_list_list : forall l v, mem (@eq _) v (var_list_list l) -> exists t, In t l /\ mem (@eq _) v (var_list t).
Proof.
fix mem_var_list_list 1; intro l; case l; clear l.
intros v v_in_nil; contradiction.
simpl; intros t l v v_in_tl; rewrite <- mem_or_app in v_in_tl; destruct v_in_tl as [v_in_t | v_in_l].
exists t; split; [left; apply eq_refl | assumption].
destruct (mem_var_list_list l v v_in_l) as [u [u_in_l v_in_u]].
exists u; split; [right | idtac]; assumption.
Qed.

Lemma var_in_term_list_is_sound : forall x l, var_in_term_list x l = true <-> In x (var_list_list l).
Proof.
intros x l; functional induction (var_in_term_list x l) as [ | x' y l H1 IH | x' f ll l H1 IHll IHl].
simpl; intuition.
simpl; rewrite <- IH.
generalize (X.eq_bool_ok x y); case (eq_var_bool x y); simpl.
intro x_eq_y; split.
intros _; left; apply sym_eq; assumption.
intros _; apply eq_refl.
intro x_diff_y; split.
intro x_in_l; right; assumption.
intros [y_eq_x | x_in_l]; [apply False_rect; apply x_diff_y; apply sym_eq | idtac]; assumption.
split; intro x_in_ll_l.
destruct (Bool.orb_prop _ _ x_in_ll_l) as [x_in_ll | x_in_l].
apply in_or_app; left; rewrite <- IHll; assumption.
apply in_or_app; right; rewrite <- IHl; assumption.
case (in_app_or _ _ _ x_in_ll_l); [intro x_in_ll | intro x_in_l].
rewrite <- IHll in x_in_ll; rewrite x_in_ll; apply eq_refl.
rewrite <- IHl in x_in_l; rewrite x_in_l; case (var_in_term_list x ll); apply eq_refl.
Qed.

Lemma var_in_term_is_sound : forall x t, var_in_term x t = true <-> In x (var_list t).
Proof.
intros x t; case t; clear t.
intro y; simpl; split; generalize (X.eq_bool_ok y x); case (eq_var_bool y x).
intros y_eq_x _; left; assumption.
intros _ Abs; discriminate.
intros _ _; reflexivity.
intros y_diff_x y_in_x; case y_in_x; clear y_in_x.
intro y_eq_x; absurd (y = x); assumption.
intro Abs; elim Abs.
intros f l; simpl.
apply var_in_term_list_is_sound.
Qed.

Lemma var_list_unfold :
 forall t,
 var_list t = match t with
          | Var x => (x :: nil)
          | Term _ l => var_list_list l
          end.
Proof.
intro t; case t; clear t; intros; reflexivity.
Qed.

Definition direct_subterm t1 t2 : Prop :=
  match t2 with
  | Var _ => False
  | Term _ l => In t1 l
  end.

Definition size_direct_subterm :
 forall t1 t2, direct_subterm t1 t2 -> size t1 < size t2.
Proof.
intros t1 t2; unfold direct_subterm; case t2; clear t2.
intros a Abs; elim Abs.
intros f l; rewrite (size_unfold (Term f l)).
revert t1 l; clear f; fix size_direct_subterm 2.
intros t1 l; case l; clear l; simpl.
intro Abs; elim Abs.
intros t l t1_in_tl; case t1_in_tl; clear t1_in_tl.
intro t_eq_t1; subst t1; apply le_n_S; apply Nat.le_add_r.
intro t_in_l; apply Nat.lt_le_trans with (1 + list_size size l).
apply size_direct_subterm; assumption.
apply le_n_S; apply Nat.le_add_l.
Defined.

Fixpoint symb_in_term (f : symbol) (t:term) : bool :=
  match t with
  | Var _ => false
  | Term g l => 
       let symb_in_term_list :=
         (fix symb_in_term_list f (l : list term) {struct l} : bool :=
            match l with
            | nil => false
            | t :: lt => orb (symb_in_term f t) (symb_in_term_list f lt)
            end) in
                 orb (eq_symb_bool f g) (symb_in_term_list f l)
   end.

Fixpoint symb_in_term_list f (l : list term) {struct l} : bool :=
            match l with
            | nil => false
            | t :: lt => orb (symb_in_term f t) (symb_in_term_list f lt)
            end.

Fixpoint symb_list (t : term) : list symbol :=
  match t with
  | Var x => nil
  | Term f l =>
       let symb_list_list :=
         (fix symb_list_list (l : list term) {struct l} : list symbol :=
            match l with
            | nil => nil
            | t :: lt => symb_list t ++ symb_list_list lt
            end) in
        f :: (symb_list_list l)
   end.

Function symb_list_list (l : list term) {struct l} : list symbol :=
            match l with
            | nil => nil
            | t :: lt => symb_list t ++ symb_list_list lt
            end.

Lemma symb_list_list_app : forall l1 l2, symb_list_list (l1 ++ l2) = (symb_list_list l1) ++ symb_list_list l2.
Proof.
fix symb_list_list_app 1; intros l1 l2; case l1; clear l1.
reflexivity.
intros t1 l1; simpl; rewrite <- ass_app; rewrite symb_list_list_app; reflexivity.
Qed.

Lemma in_symb_list_list : forall l f, In f (symb_list_list l) -> exists t, In t l /\ In f (symb_list t).
Proof.
fix in_symb_list_list 1; intro l; case l; clear l.
intros v v_in_nil; contradiction.
simpl; intros t l v v_in_tl; destruct (in_app_or _ _ _ v_in_tl) as [v_in_t | v_in_l].
exists t; split; [left; apply eq_refl | assumption].
destruct (in_symb_list_list l v v_in_l) as [u [u_in_l v_in_u]].
exists u; split; [right | idtac]; assumption.
Qed.

Lemma symb_in_term_unfold :
 forall f t,  symb_in_term f t = match t with
                             | Var _ => false
                             | Term g l =>  orb (eq_symb_bool f g) (symb_in_term_list f l)
                           end.
Proof.
intros g t; case t; intros; reflexivity.
Qed.

Lemma symb_in_term_list_app :
  forall f l1 l2, symb_in_term_list f (l1 ++ l2) = 
                     orb (symb_in_term_list f l1) (symb_in_term_list f l2).
Proof.
fix symb_in_term_list_app 2.
intros f l1 l2; case l1; clear l1; simpl.
reflexivity.
intros t l1; rewrite <- Bool.orb_assoc.
apply (f_equal (fun b => orb (symb_in_term f t) b)).
apply symb_in_term_list_app.
Qed.

Lemma symb_in_direct_subterm :
  forall f l t g, In t l -> symb_in_term g t = true -> symb_in_term g (Term f l) = true.
Proof.
intros f l s g s_in_l g_in_s; rewrite symb_in_term_unfold.
case (eq_symb_bool g f).
reflexivity.
simpl; revert l s_in_l; fix symb_in_direct_subterm 1.
intro l; case l; clear l.
intro Abs; elim Abs.
simpl In; intros t l s_in_tl; case s_in_tl; clear s_in_tl.
intros t_eq_s; subst t; simpl; rewrite g_in_s; reflexivity.
intros s_in_l; simpl; case (symb_in_term g t).
reflexivity.
rewrite (symb_in_direct_subterm _ s_in_l); reflexivity.
Qed.

Fixpoint eq_bool (t1 t2 :term) : bool :=
  match t1, t2 with
  | Var v1, Var v2 => eq_var_bool v1 v2
  | Var _, Term _ _ => false
  | Term _ _, Var _ => false  
  | Term f1 l1, Term f2 l2 =>
       if eq_symb_bool f1 f2 
       then
       let eq_bool_list :=
         (fix eq_bool_list (l1 l2: list term) {struct l1} : bool :=
            match l1, l2 with
            | nil, nil => true
            | nil, (_ :: _) => false
            | (_::_), nil => false
            | t1 :: k1, t2 :: k2 => if eq_bool t1 t2 then eq_bool_list k1 k2 else false
            end) in
        eq_bool_list l1 l2
        else false
   end.

Lemma eq_bool_ok : forall t1 t2, match eq_bool t1 t2 with true => t1 = t2 | false => t1<> t2 end.
fix eq_bool_ok0 1.
intro t1; case t1; [intro v1 | intros f1 l1]; (intro t2; case t2; [intro v2 | intros f2 l2]); simpl.
generalize (X.eq_bool_ok v1 v2); case (eq_var_bool v1 v2).
intros v1_eq_v2; rewrite v1_eq_v2; reflexivity.
intros v1_diff_v2 v1_eq_v2; apply v1_diff_v2; injection v1_eq_v2; intro; assumption.
discriminate.
discriminate.
generalize (F.Symb.eq_bool_ok f1 f2); case (eq_symb_bool f1 f2).
intros f1_eq_f2; rewrite f1_eq_f2.
assert (eq_bool_list_ok : match (fix eq_bool_list (l0 l3 : list term) : bool :=
      match l0 with
      | nil => match l3 with
               | nil => true
               | _ :: _ => false
               end
      | t3 :: k1 =>
          match l3 with
          | nil => false
          | t4 :: k2 => if eq_bool t3 t4 then eq_bool_list k1 k2 else false
          end
      end) l1 l2 with true => l1 = l2 | false => l1 <> l2 end).
revert l1 l2; clear - eq_bool_ok0.
fix eq_bool_list_ok 1.
intro l1; case l1; [idtac | intros t1 k1]; (intro l2; case l2; [idtac | intros t2 k2]).
reflexivity.
discriminate.
discriminate.
generalize (eq_bool_ok0 t1 t2); case (eq_bool t1 t2).
intro t1_eq_t2; rewrite t1_eq_t2.
generalize (eq_bool_list_ok k1 k2); 
case ((fix eq_bool_list (l0 l3 : list term) : bool :=
      match l0 with
      | nil => match l3 with
               | nil => true
               | _ :: _ => false
               end
      | t3 :: k3 =>
          match l3 with
          | nil => false
          | t4 :: k4 => if eq_bool t3 t4 then eq_bool_list k3 k4 else false
          end
      end) k1 k2).
intro k1_eq_k2; rewrite k1_eq_k2; reflexivity.
intros k1_diff_k2 tk1_eq_tk2; apply k1_diff_k2; injection tk1_eq_tk2; intro; assumption.
intros t1_diff_t2 tk1_eq_tk2; apply t1_diff_t2; injection tk1_eq_tk2; intros; assumption.
revert eq_bool_list_ok;
case ((fix eq_bool_list (l0 l3 : list term) : bool :=
                        match l0 with
                        | nil =>
                            match l3 with
                            | nil => true
                            | _ :: _ => false
                            end
                        | t3 :: k1 =>
                            match l3 with
                            | nil => false
                            | t4 :: k2 =>
                                if eq_bool t3 t4
                                then eq_bool_list k1 k2
                                else false
                            end
                        end) l1 l2).
intro l1_eq_l2; rewrite l1_eq_l2; reflexivity.
intros l1_diff_l2 fl1_eq_fl2; apply l1_diff_l2; injection fl1_eq_fl2; intros; assumption.
intros f1_diff_f2 fl1_eq_fl2; apply f1_diff_f2; injection fl1_eq_fl2; intros; assumption.
Defined.

Definition eq_term_dec : forall t t':term, {t=t'}+{t<>t'}.
intros t t'; generalize (eq_bool_ok t t').
case (eq_bool t t').
intro t_eq_t'; left; assumption.
intro t_diff_t'; right; assumption.
Defined.

Definition term_term_dec : forall x y:term*term, {x=y}+{~x=y}.
intros [a b] [a' b'].
case (eq_term_dec a a').
case (eq_term_dec b b').
intros Heq1 Heq2;left;f_equal;assumption.
intros abs _;right;intro Heq;elim abs;injection Heq;intros;assumption.
intros abs;right;intro Heq;elim abs;injection Heq;intros;assumption.
Defined.

Lemma rel_dec : 
  forall (P : relation term) Plist, (forall u v, P v u <-> In (u,v) Plist) ->
  forall r l, {P r l}+{~P r l}.
Proof.
intros P Plist Plist_ok r l; revert P Plist_ok.
induction Plist as [ | [u v] Plist]; intros P Plist_ok.
right; intro H; rewrite Plist_ok in H; contradiction.
generalize (eq_bool_ok r v); destruct (eq_bool r v).
generalize (eq_bool_ok l u); destruct (eq_bool l u).
intros; subst l r; left; rewrite Plist_ok; left; apply eq_refl.
intros l_diff_u _; destruct (IHPlist (fun v' u' => P v' u' /\ In (u',v') Plist)) as [[Ok _] | Ko].
intros s t; split.
intros [_ H]; exact H.
intros H; split; [rewrite Plist_ok; right | ]; assumption.
left; assumption.
right; intro H; rewrite Plist_ok in H; simpl in H; destruct H as [H | H].
apply l_diff_u; injection H; intros; apply sym_eq; assumption.
apply Ko; split; [rewrite Plist_ok; right | ]; assumption.
intros r_diff_v; destruct (IHPlist (fun v' u' => P v' u' /\ In (u',v') Plist)) as [[Ok _] | Ko].
intros s t; split.
intros [_ H]; exact H.
intros H; split; [rewrite Plist_ok; right | ]; assumption.
left; assumption.
right; intro H; rewrite Plist_ok in H; simpl in H; destruct H as [H | H].
apply r_diff_v; injection H; intros; apply sym_eq; assumption.
apply Ko; split; [rewrite Plist_ok; right | ]; assumption.
Defined.

Module Term_eq_dec : decidable_set.S with Definition A:= term 
                                                             with Definition eq_bool := eq_bool
                                                             with Definition eq_bool_ok := eq_bool_ok.
Definition A := term.
Definition eq_bool := eq_bool.
Definition eq_bool_ok := eq_bool_ok.
End Term_eq_dec.

(** ** Recursion on terms. *)
Section Recursion.
Variable P : term -> Type.
Variable Pl : list term -> Type.

Definition term_rec2 : (forall n t, size t <= n -> P t) -> forall t, P t.
Proof.
intros H t; apply (H (size t) t); apply le_n.
Defined.

Definition term_rec3 :
  (forall v, P (Var v)) -> (forall f l, (forall t, In t l -> P t) -> P (Term f l)) -> forall t, P t.
Proof.

intros Hv Halg. 
fix term_rec3 1.
intro t;case t.
exact Hv.
intro a.

intro l. apply Halg.
revert l.
fix term_list_rec_3 1  .
intro l;case l.
simpl;intros t0 abs;elim abs.
intros t0 l0 t1 .
simpl.
intros H. 
case (eq_term_dec t0 t1).
intros t_eq_t1.
rewrite <- t_eq_t1.
apply term_rec3.
intro t_eq_t1. assert (In t1 l0).
case H. intro abs;elim t_eq_t1;exact abs.
intro h;exact h.
apply term_list_rec_3 with l0.
exact H0.

Defined.

Definition term_rec4 :
  (forall v, P (Var v)) -> (forall f l, Pl l -> P (Term f l)) ->
  (forall l, (forall t, In t l -> P t) -> Pl l) -> forall t, P t.
Proof.
intros Hvar Hterm Hlist; apply term_rec2; 
induction n; intros t Size_t.
absurd (1<=0); auto with arith;
apply Nat.le_trans with (size t); trivial; apply size_ge_one.
destruct t as [ x | f l ]; trivial;
apply Hterm; apply Hlist; intros t In_t; apply IHn.
apply Nat.lt_succ_r;
apply Nat.lt_le_trans with (size (Term f l)); trivial;
apply size_direct_subterm; trivial.
Defined.
End Recursion.

(** ** Double recursion on terms. *)
Section DoubleRecursion.
Variable P2 : term -> term -> Type.
Variable Pl2 : list term -> list term -> Type.

Definition term_rec7 :
  (forall v1 t2, P2 (Var v1) t2) ->
               (forall t1 v2, P2 t1 (Var v2)) ->
               (forall f1 f2 l1 l2, Pl2 l1 l2 -> P2 (Term f1 l1) (Term f2 l2)) ->
               (forall l1 l2, (forall t1 t2, In t1 l1 -> In t2 l2 -> P2 t1 t2) -> Pl2 l1 l2) ->
               forall t1 t2, P2 t1 t2.
Proof.
intros Hvt Htv Hterm Hlist.
intro t1; pattern t1; apply term_rec2; induction n; clear t1;
intros t1 Size_t1.
absurd (1<=0); auto with arith;
apply Nat.le_trans with (size t1); trivial; apply size_ge_one.
destruct t1 as [ x1 | f1 l1 ]; trivial. 
destruct t2 as [ x2 | f2 l2 ]; trivial.
apply Hterm; apply Hlist; intros t1 t2 In_t1 In_t2; apply IHn;
apply Nat.lt_succ_r;
apply Nat.lt_le_trans with (size (Term f1 l1)); trivial;
apply size_direct_subterm; trivial.
Defined.

Definition term_rec8 :
  (forall v1 t2, P2 (Var v1) t2) ->
               (forall t1 v2, P2 t1 (Var v2)) ->
               (forall f1 f2 l1 l2, Pl2 l1 l2 -> P2 (Term f1 l1) (Term f2 l2)) ->
               (forall l1 l2, (forall t1 t2, In t1 l1 -> In t2 l2 -> P2 t1 t2) -> Pl2 l1 l2) ->
               forall l1 l2, Pl2 l1 l2.
Proof.
intros Hvt Htv Hterm Hlist l1 l2;
apply Hlist;
intros; apply term_rec7; trivial.
Defined.
End DoubleRecursion.

(** ** Well-formedness of terms, according to the arity. *)
Fixpoint well_formed_bool (t:term) : bool :=
  match t with
  | Var _ => true
  | Term f l =>
     let well_formed_list :=
       (fix well_formed_list (l:list term) : bool :=
       match l with
       | nil => true
       | h :: tl => andb (well_formed_bool h)  (well_formed_list tl)
       end) in
       andb (well_formed_list l)
     (match arity f with
     | Free n => Nat.eqb (length l) n 
     | _ => Nat.eqb (length l) 2
     end)
  end.

Definition well_formed t := well_formed_bool t = true.

Lemma well_formed_unfold :
 forall t, well_formed t ->
 match t with 
 | Var _ => True
 | Term f l =>
    (forall u, In u l -> well_formed u) /\
    (match arity f with
    | Free n => length l = n
    | _ => length l = 2
    end)
 end.
Proof.
unfold well_formed.
intros t; destruct t as [ x | f l ]; trivial.
simpl; rewrite Bool.andb_true_iff.
intros [Wl Ar]; split.
clear Ar; induction l as [ | t l].
intros u Abs; elim Abs.
rewrite Bool.andb_true_iff in Wl.
destruct Wl as [Wa Wl]; intros u [Eq_u_a | In_u].
subst u; trivial.
apply IHl; trivial.
revert Ar; case (arity f); intros; apply Nat.eqb_eq; assumption.
Qed.

Lemma well_formed_fold :
 forall t,
 match t with 
 | Var _ => True
 | Term f l =>
    (forall u, In u l -> well_formed u) /\
    (match arity f with
    | Free n => length l = n
    | _ => length l = 2
    end)
 end -> well_formed t.
Proof.
unfold well_formed.
intros t; destruct t as [ x | f l ]; simpl; trivial.
intros [Wl Ar]; rewrite Bool.andb_true_iff.
split.
clear Ar; induction l as [ | t l]; trivial.
rewrite Bool.andb_true_iff; split.
apply Wl; left; trivial.
apply IHl; intros; apply Wl; right; trivial.
revert Ar; case (arity f).
intro Ar; rewrite Ar; apply Nat.eqb_refl; assumption.
intro Ar; rewrite Ar; apply Nat.eqb_refl; assumption.
intros n Ar; rewrite Ar; apply Nat.eqb_refl; assumption.
Qed.

(** ** Substitutions. *)
Definition substitution := list (variable * term).

Fixpoint apply_subst (sigma : substitution) (t : term) {struct t} : term :=
  match t with
  | Var v => 
    match find eq_var_bool v sigma with
    | None => t
    | Some v_sigma => v_sigma
    end
  | Term f l => Term f (map (apply_subst sigma) l)
    end.

Lemma empty_subst_is_id : forall t, apply_subst nil t = t.
Proof.
intro t; pattern t; apply term_rec3; clear t; trivial.
intros f l IH; simpl; apply (f_equal (fun l => Term f l));
induction l as [ | t l]; trivial; simpl; rewrite (IH t).
rewrite IHl; trivial.
intros; apply IH; right; trivial.
left; trivial.
Qed.

Lemma empty_subst_is_id_list : forall l, map (apply_subst nil) l = l.
Proof.
intro l; induction l as [ | t l]; simpl; 
[idtac | rewrite empty_subst_is_id; rewrite IHl];
trivial.
Qed.

(** Composition of substitutions. *)
Definition map_subst (f : variable -> term -> term) sigma :=
  map (fun x =>
            match (x : variable * term) with
            | (v, v_sigma) => (v, f v v_sigma)
            end)
            sigma.

Definition subst_comp sigma1 sigma2 :=
  (map_subst (fun _ t => apply_subst sigma1 t) sigma2)
  ++ 
  (map_subst (fun v t =>
                        match find eq_var_bool v sigma2 with
                        | None => t
                        | Some v_sigma2 => apply_subst sigma1 v_sigma2
                        end)
                      sigma1).

Lemma subst_comp_is_subst_comp_aux1 :
  forall v sigma f,
  find eq_var_bool v (map_subst f sigma) =
   match find eq_var_bool v sigma with
   | None => None
   | Some t => Some (f v t)
  end.
Proof.
intros v sigma f; induction sigma as [ | [v1 a1] sigma]; simpl.
reflexivity.
generalize (X.eq_bool_ok v v1); case (eq_var_bool v v1).
intro v_eq_v1; subst v1; reflexivity.
intros _; apply IHsigma.
Qed.

Lemma subst_comp_is_subst_comp_aux2 :
  forall v sigma1 sigma2,
  find (B:= term) eq_var_bool v (sigma1 ++ sigma2)  =
  match find eq_var_bool v sigma1 with
  | Some _ => find eq_var_bool v sigma1
  | None => find eq_var_bool v sigma2
  end.
Proof.
fix subst_comp_is_subst_comp_aux2 2.
intros v sigma1 sigma2; case sigma1; clear sigma1.
reflexivity.
intros p sigma; case p; clear p; intros v1 a1; simpl.
case (eq_var_bool v v1).
reflexivity.
apply subst_comp_is_subst_comp_aux2.
Qed.

Theorem subst_comp_is_subst_comp :
  forall sigma1 sigma2 t,
   apply_subst (subst_comp sigma1 sigma2) t =
   apply_subst sigma1 (apply_subst sigma2 t).
Proof.
intros sigma1 sigma2 t; pattern t; apply term_rec3; clear t.
intro v; unfold subst_comp;
simpl; rewrite subst_comp_is_subst_comp_aux2;
do 2 rewrite subst_comp_is_subst_comp_aux1;
destruct (find eq_var_bool v sigma2); trivial; simpl;
destruct (find eq_var_bool v sigma1); trivial.
intros f l IH; simpl; apply (f_equal (fun l => Term f l));
induction l as [ | a l]; trivial.
simpl; rewrite (IH a).
rewrite IHl; trivial.
intros; apply IH; right; trivial.
left; trivial.
Qed.

Lemma instantiated_subterm :
  forall u u' sigma, trans_clos direct_subterm u u' ->
      trans_clos direct_subterm (apply_subst sigma u) (apply_subst sigma u').
Proof.
intros u u' sigma; apply trans_incl2.
intros s [ | f l] s_in_l.
contradiction.
simpl; rewrite in_map_iff; exists s; split; trivial.
Qed.

(** Well-formed substitutions. *)
Definition well_formed_subst sigma :=
  forall v, match find eq_var_bool v sigma with
            | None => True
            | Some t => well_formed t 
            end.

Theorem well_formed_apply_subst :
  forall sigma, well_formed_subst sigma -> 
  forall t, well_formed t -> well_formed (apply_subst sigma t).
Proof.
unfold well_formed.
intros sigma W_sigma t; pattern t; 
apply term_rec3.
intros v _; simpl; generalize (W_sigma v); 
destruct (find eq_var_bool v sigma); trivial.
intros f l Hrec; simpl; rewrite Bool.andb_true_iff; intros [Wl Ar].
rewrite Bool.andb_true_iff; split.
clear Ar; induction l as [ | a l]; simpl; trivial.
rewrite Bool.andb_true_iff in Wl; destruct Wl as [Wa Wl'].
rewrite Bool.andb_true_iff; split.
apply Hrec; trivial; left; trivial.
apply IHl; trivial; intros; apply Hrec; trivial; right; trivial.
rewrite length_map; trivial.
Qed.

Lemma well_formed_apply_subst_strong :
  forall sigma t, (forall x, var_in_term x t = true -> well_formed (apply_subst sigma (Var x))) -> 
  well_formed t -> well_formed (apply_subst sigma t).
Proof.
intros sigma t; pattern t; apply term_rec3; clear t.
intros v W_sigma _; apply W_sigma; simpl.
rewrite eq_var_bool_refl; apply eq_refl.
intros f l IHl W_sigma Wfl.
destruct (well_formed_unfold Wfl) as [Wl Af]; clear Wfl.
apply well_formed_fold; split.
intros u u_in_mapl; rewrite in_map_iff in u_in_mapl; destruct u_in_mapl as [t [H t_in_l]].
subst u; apply IHl; trivial.
intros v v_in_t; apply W_sigma; rewrite var_in_term_is_sound.
destruct (in_split_set _ eq_bool_ok _ _ t_in_l) as [l' [l'' H]]; subst l.
rewrite var_list_unfold; rewrite var_list_list_app; apply in_or_app; right.
apply in_or_app; left; rewrite <- var_in_term_is_sound; assumption.
apply Wl; assumption.
rewrite map_length; assumption.
Qed.

Lemma well_formed_remove_subst :
  forall sigma t, well_formed (apply_subst sigma t) -> well_formed t.
Proof.
intros sigma t; pattern t; apply term_rec3; clear t.
intros v _; apply eq_refl.
intros f l Hrec Wfl; destruct (well_formed_unfold Wfl) as [Wl Af]; clear Wfl.
rewrite length_map in Af.
apply well_formed_fold; split.
intros u u_in_l; apply (Hrec u u_in_l).
apply Wl; rewrite in_map_iff; exists u; split.
apply eq_refl.
assumption.
assumption.
Qed.

Lemma well_formed_remove_term :
  forall sigma t, well_formed (apply_subst sigma t) ->
  forall x, var_in_term x t = true -> well_formed (apply_subst sigma (Var x)).
Proof.
intros sigma t; pattern t; apply term_rec3; clear t.
intros v W x; simpl; generalize (X.eq_bool_ok v x); case (X.eq_bool v x).
intros v_eq_x _; subst v; exact W.
intros; discriminate.
intros f l Hrec Wfl; simpl apply_subst in Wfl; destruct (well_formed_unfold Wfl) as [Wl _]; clear Wfl.
intros v; rewrite var_in_term_is_sound; rewrite var_list_unfold.
induction l as [ | t l].
contradiction.
intros v_in_tl; destruct (in_app_or _ _ _ v_in_tl) as [v_in_t | v_in_l].
apply (Hrec t).
left; reflexivity.
apply Wl; rewrite in_map_iff; exists t; split.
reflexivity.
left; reflexivity.
rewrite var_in_term_is_sound; assumption.
apply IHl.
apply (tail_prop _ Hrec).
apply (tail_prop _ Wl).
assumption.
Qed.

(** ** Positions in a term.*)
Fixpoint is_a_pos (t : term) (p : list nat) {struct p}: bool :=
  match p with
  | nil => true
  | i :: q =>
    match t with
    | Var _ => false
    | Term _ l => 
         match nth_error l i with
          | Some ti => is_a_pos ti q
          | None => false
          end
     end
  end.

Function subterm_at_pos (t : term) (p : list nat) {struct p}: option term :=
  match p with
  | nil => Some t
  | i :: q =>
    match t with
    | Var _ => None
    | Term _ l => 
         match nth_error l i with
          | Some ti => subterm_at_pos ti q
          | None => None
          end
    end
  end.

Fixpoint is_subterm (s t : term) : bool  :=
 match t with 
 | Var x => match s with Var y => eq_var_bool x y | _ => false end
 | Term f l => 
      let fix is_subterm_list (l : list term) : bool :=
         match l with
         | nil => false
         | t :: l => orb (is_subterm s t) (is_subterm_list l)
         end in
         orb (eq_bool t s) (is_subterm_list l)
 end.

Lemma is_subterm_ok_true : 
  forall s t, is_subterm s t = true -> {p : list nat | subterm_at_pos t p = Some s}.
Proof.
intros s t; pattern t; apply term_rec3; clear t.
destruct s as [y | ]; simpl; intros x H; [ | discriminate].
exists nil; simpl; do 2 apply f_equal; 
generalize (X.eq_bool_ok x y); rewrite H; exact (fun H => H).
destruct s as [x | g k]; intros f l IHl H.
revert IHl H. induction l as [ | t l IHl0]; intros IHl H.
discriminate.
case_eq (is_subterm (Var x) t).
intro Sub; destruct (IHl _ (or_introl _ (eq_refl _)) Sub) as [p Sub'].
exists (0 :: p); assumption.
intro nSub; simpl in H; rewrite nSub in H; destruct IHl0 as [p Sub].
intros; apply IHl; [right | ]; assumption.
assumption.
destruct p as [ | i p].
discriminate.
exists (S i :: p); simpl; assumption.
case_eq (eq_bool (Term f l) (Term g k)).
intro s_eq_t; exists nil.
generalize (eq_bool_ok (Term f l) (Term g k)); rewrite s_eq_t; intro s_eq_t'; simpl; apply f_equal; assumption.
intro s_diff_t; generalize (eq_bool_ok (Term f l) (Term g k)); rewrite s_diff_t.
simpl in H; simpl in s_diff_t; rewrite s_diff_t in H; simpl in H.
clear s_diff_t; intros _.
assert (H' : {i : nat & {p : list nat | subterm_at_pos (Term f l) (i :: p) = Some (Term g k)}}).
simpl; revert IHl H; induction l as [ | t l IHl0]; intros IHl H.
discriminate.
case_eq (is_subterm (Term g k) t).
intro Sub; destruct (IHl _ (or_introl _ (eq_refl _)) Sub) as [p Sub'].
exists 0; exists p; assumption.
intro nSub; simpl in H; rewrite nSub in H.
destruct IHl0 as [i [p Sub]].
intros; apply IHl; [right | ]; assumption.
assumption.
exists (S i); exists p; simpl; assumption.
destruct H' as [i [p Sub]]; exists (i :: p); assumption.
Defined.

Lemma is_subterm_ok_false : 
  forall s t, is_subterm s t = false -> forall p, subterm_at_pos t p <> Some s.
Proof.
intros s t; pattern t; apply term_rec3; clear t.
destruct s as [y | ]; simpl; intros x H [ | i p]; simpl.
intro Sub; generalize (X.eq_bool_ok x y); rewrite H; intro x_diff_y; apply x_diff_y; injection Sub; exact (fun H => H).
discriminate.
discriminate.
discriminate.
destruct s as [x | g k]; intros f l IHl H.
intros [ | i p] Sub.
discriminate.
simpl in H, Sub.
revert i Sub; induction l as [ | t l].
intros [ | i] Sub ; discriminate.
intros i Sub; case_eq (is_subterm (Var x) t).
intro Sub'; rewrite Sub' in H; discriminate.
intro nSub; rewrite nSub in H; destruct i as [ | i]; simpl in H.
apply (IHl _ (or_introl _ (eq_refl _)) nSub p Sub).
simpl in Sub.
apply IHl0 with i; trivial.
intros; apply IHl; [right | ]; trivial.
intros [ | i p].
simpl; intro t_eq_s'; assert (t_eq_s : Term g k = Term f l).
injection t_eq_s'; intros; subst; apply eq_refl.
clear t_eq_s'; generalize (eq_bool_ok (Term f l) (Term g k)); case_eq (eq_bool (Term f l) (Term g k));
intros H1 H2; simpl in H; simpl in H1; rewrite H1 in H.
discriminate.
apply H2; rewrite t_eq_s; apply eq_refl.
simpl; simpl in H.
destruct (if eq_symb_bool f g
      then
       (fix eq_bool_list (l1 l2 : list term) : bool :=
          match l1 with
          | nil => match l2 with
                   | nil => true
                   | _ :: _ => false
                   end
          | t1 :: k1 =>
              match l2 with
              | nil => false
              | t2 :: k2 =>
                  if eq_bool t1 t2 then eq_bool_list k1 k2 else false
              end
          end) l k
      else false).
discriminate.
revert i; simpl in H; induction l as [ | t l].
intros [ | i]; discriminate.
intros [ | i]; simpl.
apply IHl.
left; apply eq_refl.
destruct (is_subterm (Term g k) t); [discriminate | apply eq_refl].
apply IHl0.
intros; apply IHl; [right | ]; assumption.
destruct (is_subterm (Term g k) t); [discriminate | assumption].
Qed.

Lemma subterm_at_pos_dec :
  forall t s, {p : list nat | subterm_at_pos t p = Some s}+{forall p, subterm_at_pos t p <> Some s}.
Proof.
fix subterm_at_pos_dec 1.
intros t; case t; clear t.
intros x s; case s; clear s; [intro x'| intros f' l'].
generalize (X.eq_bool_ok x x'); case (eq_var_bool x x').
intro x_eq_x'; left; exists nil; rewrite x_eq_x'; reflexivity.
intro x_diff_x'; right; intros p; case p; clear p.
intro H; apply x_diff_x'; injection H; clear H; intro H; exact H.
intros n p H; discriminate.

right; intros p; case p; clear p.
intro H; discriminate.
intros n p H; discriminate.

intros f l s; generalize (eq_bool_ok (Term f l) s); case (eq_bool (Term f l) s).
intro t_eq_s; left; exists nil; rewrite <- t_eq_s; reflexivity.
intros t_diff_s;
assert (IH : forall t, In t l -> forall s,  {p : list nat | subterm_at_pos t p = Some s} +
                       {(forall p : list nat, subterm_at_pos t p <> Some s)}).
clear - subterm_at_pos_dec.
revert l; fix subterm_at_pos_dec_list 1.
intro l; case l; clear l.
intros t Abs; elim Abs.
intros t1 l t t_in_t1l; generalize (eq_bool_ok t t1); case (eq_bool t t1).
intros t_eq_t1 s; rewrite t_eq_t1; apply subterm_at_pos_dec.
intros t_diff_t1 s; apply (subterm_at_pos_dec_list l t).
simpl in t_in_t1l; case t_in_t1l; clear t_in_t1l.
intro t1_eq_t; apply False_rect; apply t_diff_t1; rewrite t1_eq_t; reflexivity.
intro t_in_l; exact t_in_l.

assert (IH' : forall s, {n :nat & {t : term & {p | (nth_error l n) = Some t /\ subterm_at_pos t p = Some s}}} + 
                        {(forall t, In t l -> forall p, subterm_at_pos t p <> Some s)}).
clear -IH.
revert l IH; fix subterm_at_pos_dec 1.
intro l; case l; clear l.
intros _ s; right; intros t Abs; elim Abs.
intros t l IH s.
case (IH t (or_introl _ (eq_refl _)) s).
intro s_in_t; case s_in_t; intros p Sub; left; exists 0; exists t; exists p; split.
reflexivity.
assumption.
intro s_not_in_t; case (subterm_at_pos_dec l (tail_set _ IH) s).
intro s_in_l; case s_in_l; intros n H; case H; clear H; intros tn H; case H; clear H; intros p H; case H; clear H; intros E Sub.
left; exists (S n); exists tn; exists p; split; assumption.
intro s_not_in_l; right.
intros t' t'_in_tl; simpl in t'_in_tl; case t'_in_tl.
intro t_eq_t'; rewrite <- t_eq_t'; exact s_not_in_t.
exact (s_not_in_l t').
case (IH' s); intro H.
case H; clear H; intros n H; case H; clear H; intros t H; case H; clear H; intros p H; case H; clear H; intros E Sub.
left; exists (n :: p); simpl; rewrite E; assumption.
right; intro p; case p; clear p.
simpl; intro t_eq_s; apply t_diff_s; injection t_eq_s; intro t_eq_s'; exact t_eq_s'.
intros n p; simpl.
generalize (nth_error_ok_in n l); case (nth_error l n).
intros tn H'; case (H' tn (eq_refl _)); clear H'.
intros l1 H'; case H'; clear H'.
intros l2 H'; case H'; clear H'.
intros L H'.
apply (H tn); rewrite H'; apply in_or_app; right; left; reflexivity.
intros _; discriminate.
Defined.

Definition subterm_at_pos_dec_alt :
  forall t s, {p : list nat | subterm_at_pos t p = Some s}+ {~exists p, subterm_at_pos t p = Some s}.
Proof.
  intros t s.
  case (subterm_at_pos_dec t s).
  intro H;left;exact H.

  intro not_Sub.
  right;intro abs.
  case abs. intros p H.
  apply (not_Sub _ H).  
Defined.

Lemma subterm_subterm : 
	forall t p s, subterm_at_pos t p = Some s -> (t=s) \/ (trans_clos direct_subterm s t).
Proof.
intros t p; generalize t; clear t; induction p as [ | i p]; intros t s Sub; simpl in Sub.
injection Sub; intros; subst; left; trivial.
destruct t as [v | f l].
discriminate.
right; assert (H := nth_error_ok_in i l); 
destruct (nth_error l i) as [ti | ].
destruct (H _ (eq_refl _)) as [l1 [l2 [L H']]].
destruct (IHp _ _ Sub) as [ti_eq_s | Subi].
subst; apply t_step; simpl; apply in_or_app; right; left; trivial.
apply trans_clos_is_trans with ti; trivial.
subst; apply t_step; simpl; apply in_or_app; right; left; trivial.
discriminate.
Qed.



Lemma size_subterm_at_pos :
  forall t i p, match subterm_at_pos t (i :: p) with
	           | Some u => size u < size t
	           | None => True
	           end.
Proof.
intros t i p; generalize t i; clear t i; induction p as [ | j p].
intros [ v | f l ] j; simpl subterm_at_pos; cbv iota beta; trivial.
generalize (nth_error_ok_in j l); destruct (nth_error l j) as [tj | ]; [idtac | trivial].
intro H; apply size_direct_subterm.
destruct (H tj (eq_refl _)) as [l1 [l2 [_ H']]]; subst l; simpl;
apply in_or_app; right; left; trivial. 
intros [ v | f l ] i; simpl subterm_at_pos; cbv iota beta; trivial.
generalize (nth_error_ok_in i l); destruct (nth_error l i) as [ti | ]; [idtac | trivial].
intro ti_in_l; generalize (IHp ti j); simpl subterm_at_pos; 
destruct ti as [vi | fi li]; trivial.
generalize (nth_error_ok_in j li); destruct (nth_error li j) as [tij | ]; [idtac | trivial].
intro tij_in_li; destruct (subterm_at_pos tij p) as [ u | ]; trivial.
intro H; apply Nat.lt_trans with (size (Term fi li)); trivial.
apply size_direct_subterm.
destruct (ti_in_l _ (eq_refl _)) as [l1 [l2 [_ H']]]; subst l; simpl;
apply in_or_app; right; left; trivial. 
Qed.

Lemma size_strict_subterm : forall s t, trans_clos direct_subterm s t -> size s < size t.
Proof.
intros s t Sub; induction Sub as [ s t H | s u t H1 H2].
apply size_direct_subterm; assumption.
apply Nat.lt_trans with (size u); trivial.
apply size_direct_subterm; assumption.
Qed.

Lemma subterm_subterm_non_nil : 
	forall t p s, subterm_at_pos t p = Some s -> p <> nil -> (trans_clos direct_subterm s t).
Proof.
  intros t p s H H0.
  generalize (subterm_subterm t p H).
  destruct 1;[|assumption].
  subst.
  destruct p.
  elim H0;reflexivity.
  generalize (size_subterm_at_pos s n p).
  rewrite H.
  intros h;apply False_ind;apply (Nat.lt_irrefl _ h).
Qed.


Lemma var_in_subterm :
  forall v s t p, subterm_at_pos t p = Some s -> In v (var_list s)  -> In v (var_list t).
Proof.
intros v s t p; generalize s t; clear s t; induction p as [ | i p]; intros s t H v_in_s.
simpl in H; injection H; clear H; intros; subst; trivial.
simpl in H; destruct t as [ | g l].
discriminate.
assert (H' := nth_error_ok_in i l).
destruct (nth_error l i) as [ti | ].
destruct (H' _ (eq_refl _)) as [l1 [l2 [L H'']]]; subst l.
rewrite var_list_unfold.
clear H' L; induction l1 as [ | t1 l].
simpl; apply in_or_app; left; apply (IHp s ti); trivial.
simpl; apply in_or_app; right; apply IHl.
discriminate.
Qed.

Lemma var_in_subterm2 :
  forall v t, mem (@eq _) v (var_list t) -> {p : list nat | subterm_at_pos t p = Some (Var v)}.
Proof.
intros v t; pattern t; apply term_rec3; clear t.
intros x v_in_x; exists (@nil nat); simpl; destruct v_in_x as [v_eq_x | v_in_nil]; [subst; apply eq_refl | contradiction].
intros f l; rewrite var_list_unfold; simpl.
induction l as [ | t l]; intros IH v_in_l.
contradiction.
simpl in v_in_l.
generalize (mem_bool_ok _ _ X.eq_bool_ok v (var_list t)); case (mem_bool X.eq_bool v (var_list t)); [intro v_in_t | intro v_not_in_t].
destruct (IH t (or_introl _ (eq_refl _)) v_in_t) as [p Sub].
exists (0 :: p); simpl; trivial.
assert (v_in_l' : mem (@eq _) v (var_list_list l)).
rewrite <- mem_or_app in v_in_l; destruct v_in_l as [v_in_t | v_in_l].
absurd (mem (@eq _) v (var_list t)); trivial.
assumption.
destruct (IHl (tail_set _ IH) v_in_l') as [p Sub]; trivial.
destruct p as [ | i p]; simpl in Sub.
discriminate.
exists (S(i) :: p); simpl; trivial.
Qed.

Lemma symb_in_subterm :
  forall f s t p, subterm_at_pos t p = Some s -> symb_in_term f s = true -> symb_in_term f t = true.
Proof.
fix symb_in_subterm 4.
intros f s t p; case p; clear p; simpl.
intro H; injection H; clear H; intro H; rewrite H; intro H'; exact H'.
intros n p; case t; clear t.
intros v Abs; discriminate.
intros g l; generalize (nth_error_ok_in n l); case (nth_error l n).
intros tn H; case (H tn (eq_refl _)).
intros l1 H'; case H'; clear H'.
intros l2 H'; case H'; clear H'.
intros L H' Sub f_in_s.
rewrite symb_in_term_unfold.
case (eq_symb_bool f g).
reflexivity.
simpl; rewrite H'; rewrite symb_in_term_list_app.
case (symb_in_term_list f l1).
reflexivity.
simpl.
rewrite (symb_in_subterm f s tn p Sub f_in_s); reflexivity.
intros _ Abs; discriminate.
Qed.

Lemma symb_list_ok : forall f t, In f (symb_list t) <-> symb_in_term f t = true.
Proof.
intros f t; pattern t; apply term_rec3; clear t.
intros v; simpl; split; intro H; [contradiction H | discriminate H].
intros g l IH; simpl.
generalize (F.Symb.eq_bool_ok f g); destruct (eq_symb_bool f g); [intro f_eq_g | intro f_diff_g]; simpl.
split; [intros _; apply eq_refl | intros _; left; apply sym_eq; assumption].
split; [intros [H | H] | intro H].
apply False_rect; apply f_diff_g; apply sym_eq; assumption.
induction l as [ | t l].
contradiction H.
destruct (in_app_or _ _ _ H) as [f_in_t | f_in_l].
rewrite (IH _ (or_introl _ (eq_refl _))) in f_in_t; rewrite f_in_t; apply eq_refl.
rewrite IHl.
destruct (symb_in_term f t); apply eq_refl.
intros; apply IH; right; assumption.
assumption.
right.
induction l as [ | t l].
discriminate H.
case_eq (symb_in_term f t); [intro f_in_t | intro f_not_in_t].
apply in_or_app; left; rewrite IH; [assumption | left; apply eq_refl].
apply in_or_app; right; apply IHl.
intros; apply IH; right; assumption.
rewrite f_not_in_t in H; assumption.
Qed.

Lemma symb_list_list_ok : forall f l, In f (symb_list_list l) <-> symb_in_term_list f l = true.
Proof.
intros f l; induction l as [ | t l]; split; intro H.
contradiction.
discriminate.
simpl; simpl in H; destruct (in_app_or _ _ _ H) as [Ht | Hl].
rewrite symb_list_ok in Ht; rewrite Ht; apply eq_refl.
rewrite IHl in Hl; rewrite Hl; case (symb_in_term f t); apply eq_refl.
simpl; simpl in H.
case_eq (symb_in_term f t); [intro f_in_t | intro f_not_in_t].
apply in_or_app; left; rewrite symb_list_ok; assumption.
apply in_or_app; right; rewrite IHl; rewrite f_not_in_t in H; assumption.
Qed.

Lemma is_a_pos_exists_subterm :
  forall t p, is_a_pos t p = true <-> exists u, subterm_at_pos t p = Some u.
Proof.
intros t p; revert t; induction p as [ | i q ].
intros t; split.
intros _; exists t; trivial.
intros _; trivial.
intros t; destruct t as [ x | f l ]; simpl; split.
intros; discriminate.
intros [u Abs]; discriminate.
destruct (nth_error l i) as [ ti | ].
intro; rewrite <- IHq; trivial.
intros; discriminate.
intros [u Sub]; destruct (nth_error l i).
rewrite IHq; exists u; trivial.
discriminate.
Qed.

Lemma well_formed_subterm :
  forall t p s, well_formed t -> subterm_at_pos t p = Some s -> well_formed s.
Proof.
fix well_formed_subterm 2; intros t p; case p; clear p.
intros s Wt Sub; injection Sub; intros; subst; assumption.
intros i p s; simpl; case t; clear t.
intros; discriminate.
intros f l Wt Sub; case_eq (nth_error l i); [intros ti F | intros F]; rewrite F in Sub.
apply (well_formed_subterm ti p). 
apply (proj1 (well_formed_unfold Wt)).
destruct (nth_error_ok_in i l F) as [l' [l'' [_ H]]]; subst l; apply in_or_app; right; left; reflexivity.
assumption.
discriminate.
Qed.

Fixpoint replace_at_pos (t u : term) (p : list nat) {struct p} : term :=
  match p with
  | nil => u
  | i :: q =>
     match t with
     | Var _ => t
     | Term f l =>
        let replace_at_pos_list :=
         (fix replace_at_pos_list j (l : list term) {struct l}: list term :=
            match l with
            | nil => nil
            | h :: tl =>
                 match j with
                 | O => (replace_at_pos h u q) :: tl
                 | S k => h :: (replace_at_pos_list k tl)
                 end
            end) in
    Term f (replace_at_pos_list i l)
    end
  end.

Fixpoint replace_at_pos_list (l : list term) (u : term) (i : nat) (p : list nat) 
 {struct l}: list term :=
  match l with
  | nil => nil
  | h :: tl =>
     match i with
     | O => (replace_at_pos h u p) :: tl
     | S j => h :: (replace_at_pos_list tl  u j p)
     end
  end.

Lemma replace_at_pos_unfold :
  forall f l u i q,
   replace_at_pos (Term f l) u (i :: q) = Term f (replace_at_pos_list l u i q).
Proof.
intros f l u i q; simpl; apply (f_equal (fun l => Term f l)); 
generalize u i q; clear u i q; 
induction l as [| t l]; intros u i q; trivial.
simpl; destruct i as [ | i ]; trivial.
rewrite <- IHl; trivial.
Qed.

Lemma replace_at_pos_is_replace_at_pos1 :
  forall t u p, is_a_pos t p = true ->
  subterm_at_pos (replace_at_pos t u p) p = Some u.
Proof.
intro t; pattern t; apply term_rec3; clear t.
intros x u p; destruct p as [ | i q ]; trivial;
intros; discriminate.
intros f l IHl u p; destruct p as [ | i q ]; trivial.
rewrite replace_at_pos_unfold; simpl; generalize i q; clear i q; 
induction l as [ | t l ]; intros i q.
destruct i as [ | i ]; simpl; intros; discriminate.
destruct i as [ | i ]; simpl.
intros; apply (IHl t); trivial; left; trivial.
intros; apply IHl0; intros; trivial; apply IHl; trivial; right; trivial.
Qed.


Lemma replace_at_pos_is_replace_at_pos2 :
  forall t p u, subterm_at_pos t p = Some u -> replace_at_pos t u p = t. 
Proof.
intro t; pattern t; apply term_rec3; clear t.
intros v p u; destruct p as [ | i q ]; intro H; inversion_clear H; trivial.
intros f l IHl p; destruct p as [ | i q ]. 
intros u H; inversion_clear H; trivial.
intros u H; rewrite replace_at_pos_unfold; 
apply (f_equal (fun l => Term f l)); generalize i q u H; clear i q u H;
induction l as [ | t l ]; intros i q u H.
destruct i as [ | i ]; simpl; intros; discriminate.
destruct i as [ | i ]; simpl.
rewrite IHl; trivial; left; trivial.
rewrite IHl0; trivial; intros; apply IHl; trivial; right; trivial.
Qed.

Lemma subterm_at_pos_apply_subst_apply_subst_subterm_at_pos :
  forall t p sigma, 
  match subterm_at_pos t p with
  | Some u =>
        subterm_at_pos (apply_subst sigma t) p = Some (apply_subst sigma u)
  | None => True
end.
Proof.
intro t; pattern t; apply term_rec3; clear t.
intros v p; destruct p as [ | i q ]; simpl; trivial.
intros f l IHl p; destruct p as [ | i q ]; simpl; trivial.
assert (H : forall (l : list term) i, 
                     match nth_error l i with
                                | Some li => In li l
                                | None => True end).
clear IHl l i; intro l;
induction l as [ | t l ]; intro i; destruct i as [ | i ]; simpl; trivial.
left; trivial.
generalize (IHl i); destruct (nth_error l i); trivial; intros; right; trivial.
generalize i; clear i; induction l as [ | l ll ]; 
intros i; destruct i as [ | i ]; simpl; trivial.
intros; apply IHl; left; trivial.
intro sigma; apply IHll; intros; apply IHl; right; trivial.
Qed.

Lemma replace_at_pos_list_replace_at_pos_in_subterm :
forall l1 ui l2 u i p, length l1 = i ->
 replace_at_pos_list (l1 ++ ui :: l2) u i p = 
 l1 ++ (replace_at_pos ui u p) :: l2.
Proof.
intros l1; induction l1 as [ | u1 l1 ]; intros ui l2 u i p L; simpl in L.
subst i; trivial.
destruct i as [ | i ].
discriminate.
simpl; rewrite IHl1; trivial.
inversion L; trivial.
Qed.

Lemma well_formed_replace_at_pos :
   forall p t u, well_formed t -> well_formed u -> well_formed (replace_at_pos t u p).
Proof.
intro p; induction p as [ | i p]; intros t u Wt Wu.
simpl; assumption.
destruct t as [ x | f l].
simpl; trivial.
rewrite replace_at_pos_unfold.
destruct (well_formed_unfold Wt) as [Wl L]; clear Wt.
apply well_formed_fold; split.
clear L; revert i; induction l as [ | t l].
intros; contradiction.
intros i; case i; clear i.
simpl; intros v [H | H].
subst v; apply IHp; trivial.
apply Wl; left; apply eq_refl.
apply Wl; right; assumption.
simpl; intros i v [H | H].
subst v; apply Wl; left; apply eq_refl.
apply IHl with i; trivial.
intros; apply Wl; right; assumption.
replace (length (replace_at_pos_list l u i p)) with (length l); trivial.
clear; revert i; induction l as [ | t l]; simpl; trivial.
intros [ | n]; simpl; trivial.
rewrite <- IHl; trivial.
Qed.

Lemma subst_replace_at_pos : 
	forall t u p sigma, is_a_pos t p = true -> apply_subst sigma (replace_at_pos t u p) =
	replace_at_pos (apply_subst sigma t) (apply_subst sigma u) p.
Proof.
intros t u p; revert t u; induction p as [ | i p]; intros t u sigma Hpos; trivial.
destruct t as [x | f l].
discriminate.
rewrite replace_at_pos_unfold.
simpl apply_subst.
rewrite replace_at_pos_unfold.
apply f_equal.
simpl in Hpos.
clear f.
revert i u sigma Hpos; induction l as [ | t l]; intros [ | n] u sigma Hpos; simpl; trivial.
apply (f_equal (fun t => t :: map (apply_subst sigma) l)).
apply IHp; trivial.
apply f_equal.
apply IHl; trivial.
Qed.

Lemma subterm_in_instantiated_term :
  forall p s t sigma, subterm_at_pos (apply_subst sigma t) p = Some s ->
                    match subterm_at_pos t p with
		    | Some u' => s = apply_subst sigma u'
	            | None => exists v, exists q, exists q', p = q ++ q' /\
                                          In v (var_list t)  /\
                                         subterm_at_pos t q = Some (Var v) /\
	                                 subterm_at_pos (apply_subst sigma (Var v)) q' = Some s
	            end.	
Proof. 
intro p; induction p as [ | i p]; intros s t sigma Sub. 
simpl in Sub; injection Sub; clear Sub; intros; subst; simpl; trivial.
simpl; simpl in Sub; destruct t as [v | f l].
exists v.
simpl in Sub; destruct (find eq_var_bool v sigma) as [v_sigma | ].
exists (@nil nat); exists (i :: p); repeat split; trivial.
left; trivial.
discriminate.
simpl in Sub.
assert (H := nth_error_map (apply_subst sigma) l i).
destruct (nth_error (map (apply_subst sigma) l) i) as [ti_sigma | ].
assert (H' := nth_error_ok_in i l).
destruct (nth_error l i) as [ti | ].
destruct (H' _ (eq_refl _)) as [l1 [l2 [L H''']]]; clear H'; subst;
generalize (IHp _ _ _ Sub).
destruct (subterm_at_pos ti p) as [u | ]; trivial.
intros [v [q [q' [p_eq_qq' [v_in_ti [Sub' Sub'']]]]]].
exists v; exists (length l1 :: q); exists q'; repeat split; trivial.
subst p; trivial.
apply  var_in_subterm with ti (length l1 :: nil); trivial.
simpl; rewrite nth_error_at_pos; trivial.
simpl; rewrite nth_error_at_pos; trivial.
contradiction.
discriminate.
Qed.

Lemma subterm_in_subterm :
  forall p q s t u, subterm_at_pos t p = Some s -> subterm_at_pos s q = Some u ->
                          subterm_at_pos t (p ++ q) = Some u.
Proof.
intro p; induction p as [ | i p]; intros q s t u Sub1 Sub2.
simpl in Sub1; injection Sub1; clear Sub1; intros; subst; trivial.
simpl in Sub1; simpl; destruct t as [v | f l].
discriminate.
destruct (nth_error l i) as [ti | ].
apply IHp with s; trivial.
discriminate.
Qed.

Lemma subterm_in_subterm2 :
  forall p q s t, subterm_at_pos t (p ++ q) = Some s ->
                      exists u, subterm_at_pos t p = Some u /\ subterm_at_pos u q = Some s.
Proof.
intro p; induction p as [ | i p]; intros q s t Sub.
exists t; split; trivial.
simpl in Sub; destruct t as [v | f l].
discriminate.
generalize (nth_error_ok_in i l); destruct (nth_error l i) as [ti | ].
intro H; destruct (H _ (eq_refl _)) as [l1 [l2 [L H']]]; clear H.
destruct (IHp q s ti Sub) as [u [Sub' H'']].
exists u; subst; simpl; rewrite nth_error_at_pos; split; trivial.
discriminate.
Qed.

Lemma subterm_subterm_alt : 
 forall t s, refl_trans_clos direct_subterm s t -> {p : list nat | subterm_at_pos t p = Some s}.
Proof.
assert (H : forall t s, refl_trans_clos direct_subterm s t -> exists p, subterm_at_pos t p = Some s).
intros s t H; inversion H as [u | t' s' H'].
subst; exists nil; apply eq_refl.
subst s' t'; clear H; induction H' as [s t H | s t u H1 H2].
destruct t as [x | f l].
contradiction.
simpl in H.
destruct (in_split _ _ H) as [l1 [l2 H']].
exists (length l1 :: nil); subst l; simpl; rewrite nth_error_at_pos; apply eq_refl.
destruct t as [x | f l].
contradiction.
simpl in H1.
destruct (in_split _ _ H1) as [l1 [l2 H']].
destruct IHH2 as [p Sub]; exists (p ++ (length l1) :: nil).
apply subterm_in_subterm with (Term f l); trivial.
subst l; simpl; rewrite nth_error_at_pos; apply eq_refl.
intros t s H'; destruct (subterm_at_pos_dec t s) as [Sub | not_Sub].
assumption.
apply False_rect.
destruct (H _ _ H') as [p Sub]; apply (not_Sub p Sub).
Qed.

Lemma var_in_replace_at_pos :
  forall s p u x, In x (var_list (replace_at_pos s u p)) -> In x (var_list s) \/ In x (var_list u).
Proof.
intros s p; revert s; induction p as [ | i p].
simpl; intros s u x x_in_u; right; assumption.
intros s u x; destruct s as [v | f l].
left; trivial.
rewrite replace_at_pos_unfold; do 2 rewrite var_list_unfold.
clear f; revert i u x; induction l as [ | t l]; intros i u x.
contradiction.
simpl replace_at_pos_list; destruct i as [ | i].
simpl; intro H; destruct (in_app_or _ _ _ H) as [H1 | H1]; clear H.
destruct (IHp _ _ _ H1) as [H2 | H2]; clear H1.
left; apply in_or_app; left; assumption.
right; assumption.
left; apply in_or_app; right; assumption.
simpl; intro H; destruct (in_app_or _ _ _ H) as [H1 | H1]; clear H.
left; apply in_or_app; left; assumption.
destruct (IHl _ _ _ H1) as [H2 | H2]; clear H1.
left; apply in_or_app; right; assumption.
right; assumption.
Qed.

Lemma remove_garbage_subst :
  forall sigma : substitution, 
    {sigma' : substitution | (forall x, find eq_var_bool x sigma = find eq_var_bool x sigma') /\
	                                 (forall x val, In (x,val) sigma' -> find eq_var_bool x sigma' = Some val) /\
                                  (forall x y val val' (tau tau' tau'' : substitution), 
                                     sigma' = tau ++ (x,val) :: tau' ++ (y,val') :: tau'' ->
                                     x <> y)}.
Proof.
fix remove_garbage_subst 1.
intro sigma; case sigma; clear sigma.
exists nil; repeat split.
intros x val Abs; elim Abs.
intros x y val val' tau tau' tau''; case tau; clear tau.
intro Abs; discriminate.
intros p tau Abs; discriminate.

intros p sigma; case p; clear p; intros x val.
destruct (remove_garbage_subst sigma) as [sigma' [H1 [H2 H3]]].
case_eq (find eq_var_bool x sigma').

(* 1/2 *)
intros val' H; destruct (find_mem _ _ X.eq_bool_ok _ _ H) as [x' [sigma1 [sigma2 [H' H'']]]].
exists ((x,val) :: sigma1 ++ sigma2); subst x'; repeat split.
(* 1/4 *)
intros y; simpl; case_eq (eq_var_bool y x); [intro y_eq_x | intro x_diff_y]; [trivial | idtac].
rewrite (H1 y); rewrite H''; clear sigma' H1 H2 H3 H H'';
induction sigma1 as [ | [x1 val1] sigma1]; simpl.
rewrite x_diff_y; reflexivity.
case_eq (eq_var_bool y x1); [intro y_eq_x1 | intro y_diff_x1]; [idtac | apply IHsigma1]; trivial.
(* 1/3 *)
simpl; intros y val'' [H4 | H4].
injection H4; clear H4; intros; subst.
rewrite eq_var_bool_refl; reflexivity.
case_eq (eq_var_bool y x); [intro y_eq_x | intro y_diff_x].
destruct (in_app_or _ _ _ H4) as [H5 | H5];
destruct (In_split _ _ H5) as [tau1 [tau2 H6]]; subst.
absurd (y = x).
apply (H3 y x val'' val' tau1 tau2 sigma2); rewrite <- ass_app; trivial.
generalize (X.eq_bool_ok y x); rewrite y_eq_x; intro y_eq_x'; exact y_eq_x'.
absurd (x = y).
apply (H3 x y val' val'' sigma1 tau1 tau2); trivial.
generalize (X.eq_bool_ok y x); rewrite y_eq_x; intro y_eq_x'; rewrite y_eq_x'; reflexivity.
rewrite <- (H2 y val''); subst sigma'.
rewrite (find_diff (@eq variable)).
reflexivity.
exact X.eq_bool_ok.
exact y_diff_x.
apply in_insert; trivial.
clear sigma H1 H2.
(* 1/2 *)
intros x1 y val1 valy [ | [z zval] tau] tau' tau''; simpl; intro H''';
simpl in H'''; injection H'''; clear H'''; intros; subst.
assert (yvaly_in_sigma12 : In (y,valy) (sigma1 ++ sigma2)).
rewrite H0; apply in_or_app; right; left; trivial.
destruct (in_app_or _ _ _ yvaly_in_sigma12) as [yvaly_in_sigma1 | yvaly_in_sigma2].
destruct (In_split _ _ yvaly_in_sigma1) as [tau1 [tau2 H']].
intro x1_eq_y; apply (H3 y x1 valy val' tau1 tau2 sigma2); subst; trivial.
rewrite <- ass_app; trivial.
destruct (In_split _ _ yvaly_in_sigma2) as [tau1 [tau2 H']].
apply (H3 x1 y val' valy sigma1 tau1 tau2); subst; trivial.
destruct (insert_2 _ _ _ _ _ (z,val') _ _ H0) as [tau1 [tau2 [tau3 H4]]].
apply (H3 _ _ _ _ _ _ _ H4).
(* 1/1 *)
intro H4; exists ((x,val) :: sigma'); repeat split.
(* 1/3 *)
intros y; simpl; case_eq (eq_var_bool y x); [intro y_eq_x | intro y_diff_x]; [idtac | apply H1]; trivial.
(* 1/2 *)
simpl; intros y valy  [H | H].
injection H; clear H; intros; subst.
rewrite eq_var_bool_refl; reflexivity.
case_eq (eq_var_bool y x); [intro y_eq_x | intro y_diff_x].
absurd (In (y,valy) sigma').
apply find_not_found with eq_var_bool x.
assumption.
generalize (X.eq_bool_ok x y) (X.eq_bool_ok y x); rewrite y_eq_x.
case (eq_var_bool x y).
intros _ _; reflexivity.
intros x_diff_y y_eq_x'; apply False_rect; apply x_diff_y; rewrite y_eq_x'; reflexivity.
assumption.
apply H2; trivial.
(* 1/1 *)
intros y z valy valz [ | [u valu] tau] tau' tau'' H; simpl in H; injection H; clear H; intros; subst.
intro y_eq_z; subst y; apply (find_not_found eq_var_bool _ z valz _ H4).
apply eq_var_bool_refl.
apply in_or_app; right; left; trivial.
apply (H3 _ _ _ _ _ _ _ (eq_refl _)).
Defined.

Lemma subst_eq_vars :
  forall t sigma sigma', (forall v, In v (var_list t) -> apply_subst sigma (Var v) = apply_subst sigma' (Var v)) 
   <-> apply_subst sigma t = apply_subst sigma' t.
Proof.
intros t sigma sigma'; split.
pattern t; apply term_rec3; clear t.
intros v H; apply H; left; trivial.
intros f l IHl H.
simpl; apply (f_equal (fun l => Term f l)).
apply map_eq; intros t t_in_l; apply IHl; trivial.
intros v v_in_t; apply H.
destruct (In_split _ _ t_in_l) as [l1 [l2 H']]; subst.
apply var_in_subterm with t (length l1 :: nil); trivial.
simpl; rewrite nth_error_at_pos; trivial.
pattern t; apply term_rec3; clear t.
intros v H; simpl; intros x [x_eq_v | F]; [subst; trivial | contradiction].
intros f l IHl H; simpl in H; injection H; clear H; intro H.
intros v v_in_l; rewrite var_list_unfold in v_in_l; induction l as [ | t l].
contradiction.
simpl in H; injection H; clear H; intros H H'.
simpl in v_in_l.
destruct (in_app_or _ _ _  v_in_l) as [v_in_t | v_in_l'].
apply IHl with t; trivial.
left; trivial.
apply IHl0; trivial.
intros s s_in_l H'' x x_in_s; apply (IHl s); trivial.
right; trivial.
Qed.

Fixpoint subst_rest vars sigma : substitution :=
match sigma with
| nil => nil
| (x,u) :: sigma => 
          if mem_bool eq_var_bool x vars 
          then (x,u) :: (subst_rest vars sigma)
          else subst_rest vars sigma
end.

Lemma subst_rest_ok :
  forall vars sigma v, In v vars -> apply_subst (subst_rest vars sigma) (Var v) = apply_subst sigma (Var v).
Proof.
fix subst_rest_ok 2.
intros vars sigma; case sigma; clear sigma.
intros v _; apply eq_refl.
intros p sigma; case p; clear p.
intros z t v v_in_vars; simpl.
generalize (mem_bool_ok _ _ X.eq_bool_ok z vars);
case (mem_bool eq_var_bool z vars); [intro z_in_vars | intro z_not_in_vars].
simpl.
destruct (eq_var_bool v z).
apply eq_refl.
apply subst_rest_ok; trivial.
generalize (X.eq_bool_ok v z); case (eq_var_bool v z); [intro v_eq_z | intro v_diff_z].
apply False_rect; apply z_not_in_vars; subst v; apply in_impl_mem.
intros; apply eq_refl.
assumption.
apply subst_rest_ok; trivial.
Qed.

Lemma subst_rest_rest :
  forall vars sigma v t, In (v,t) (subst_rest vars sigma) -> In v vars.
Proof.
fix subst_rest_rest 2.
intros vars sigma; case sigma; clear sigma.
intros v t; contradiction.
intros p sigma; case p; clear p.
intros z t v u; simpl.
generalize (mem_bool_ok _ _ X.eq_bool_ok z vars);
case (mem_bool eq_var_bool z vars); [intro z_in_vars | intro z_not_in_vars].
simpl.
intros [zt_eq_vu | vu_in_rest].
injection zt_eq_vu; intros; subst v; apply mem_impl_in with (@eq _).
intros; assumption.
assumption.
apply (subst_rest_rest vars sigma v u vu_in_rest).
apply subst_rest_rest.
Qed.

Lemma subst_rest_subst :
  forall vars sigma v t, In (v,t) (subst_rest vars sigma) -> In (v,t) sigma.
Proof.
fix subst_rest_subst 2.
intros vars sigma; case sigma; clear sigma.
intros v t; contradiction.
intros p sigma; case p; clear p.
intros z t v u; simpl.
generalize (mem_bool_ok _ _ X.eq_bool_ok z vars);
case (mem_bool eq_var_bool z vars); [intro z_in_vars | intro z_not_in_vars].
simpl.
intros [zt_eq_vu | vu_in_rest].
left; assumption.
right; apply (subst_rest_subst vars); assumption.
intros vu_in_rest; right; apply (subst_rest_subst vars); assumption.
Qed.

Lemma subst_rest_subst_rest :
  forall vars sigma v t, In v vars -> In (v,t) sigma -> In (v,t) (subst_rest vars sigma).
Proof.
fix subst_rest_subst_rest 2; intros vars sigma; case sigma; clear sigma.
intros; contradiction.
intros p sigma; case p; clear p.
simpl; intros x u v t x_in_vars.
intros [xu_eq_vt | vt_in_sigma].
injection xu_eq_vt; clear xu_eq_vt; intros; subst v t.
generalize (mem_bool_ok _ _ X.eq_bool_ok x vars); case (mem_bool X.eq_bool x vars); [intros _ | intro x_not_in_vars].
left; apply eq_refl.
apply False_rect; apply x_not_in_vars; apply in_impl_mem; trivial.
case (mem_bool X.eq_bool x vars).
right; apply subst_rest_subst_rest; assumption.
apply subst_rest_subst_rest; assumption.
Qed.

Definition extend_with_id vars sigma :=
  (map (fun x => (x,Var x)) 
                                 (filter (fun x =>  negb (mem_bool X.eq_bool x (map (@fst _ _) sigma))) vars))
  ++ sigma.

Lemma subst_trivial_ext :
forall vars sigma t, apply_subst (extend_with_id vars sigma) t = apply_subst sigma t.
Proof.
unfold extend_with_id.
intros vars sigma t; rewrite <- subst_eq_vars.
intros v _; simpl; rewrite find_app.
case_eq (mem_bool X.eq_bool v
        (map (fun st : variable * term => fst st)
           (map (fun x : variable => (x, Var x))
              (filter
                 (fun x : variable =>
                  negb (mem_bool X.eq_bool x (map (@fst _ _) sigma))) vars))));
  [intro v_in | intros _; apply eq_refl].
case_eq (find X.eq_bool v
    (map (fun x : variable => (x, Var x))
       (filter
          (fun x : variable => negb (mem_bool X.eq_bool x (map (@fst _ _) sigma))) vars)));
           [intros x' F | intro F].
destruct (find_mem _ _ X.eq_bool_ok _ _ F) as [v' [l1 [l2 [v_eq_v' H]]]]; subst v'.
assert (v_in' : In (v,x') (l1 ++ (v,x') :: l2)).
apply in_or_app; right; left; apply eq_refl.
rewrite <- H in v_in'.
rewrite in_map_iff in v_in'.
destruct v_in' as [v' [v_eq_v' v_in']]; injection v_eq_v'; clear v_eq_v'; do 2 intros; subst v' x'.
rewrite filter_In in v_in'.
destruct v_in' as [_ v_in'].
case_eq (find X.eq_bool v sigma); [intros v_val v_sigma | intros _; apply eq_refl].
apply False_rect.
destruct (find_mem _ _ X.eq_bool_ok _ _ v_sigma) as [v' [sig1 [sig2 [v_eq_v' H']]]]; subst v'.
rewrite H' in v_in'; clear - v_in'; induction sig1 as [ | [u u'] sig1]; simpl in v_in'.
rewrite eq_var_bool_refl in v_in'; discriminate.
destruct (eq_var_bool v u); [discriminate | apply IHsig1 ; assumption].
assert (v_mem := mem_bool_ok _ _ X.eq_bool_ok v
(map (fun st : variable * term => fst st)
            (map (fun x : variable => (x, Var x))
               (filter
                  (fun x : variable =>
                   negb (mem_bool eq_var_bool x (map (@fst _ _) sigma))) vars)))); rewrite v_in in v_mem.
assert (v_in'' := mem_impl_in (@eq variable) (fun a b P => P) _ _ v_mem).
rewrite in_map_iff in v_in''; destruct v_in'' as [[v' u] [v_eq_v' v_in3]]; simpl in v_eq_v'; subst v'.
apply False_rect; refine (find_not_found  X.eq_bool v v _ _ F (eq_var_bool_refl v) v_in3).
Qed.

Definition o_list_size pb1 pb2 := 
    list_size (fun st => size (fst (B:=term) st)) pb1 < 
    list_size (fun st => size (fst (B:=term) st)) pb2. 

Lemma wf_size : well_founded o_list_size.
Proof.
unfold well_founded, o_list_size.
intros pb; apply Acc_intro.
generalize (list_size (fun st : term * term => size (fst st)) pb); clear pb. 
intro n; induction n as [ | n].
intros y Abs; absurd (list_size (fun st : term * term => size (fst st)) y < 0); auto with arith.
intros y Sy; inversion Sy; subst.
apply Acc_intro; intros x Sx; apply IHn; trivial.
apply IHn; trivial.
Defined.

Lemma matching_call1 :
  forall patt subj pb, o_list_size pb ((patt, subj) :: pb).
Proof.
intros patt sibj pb;
unfold o_list_size; simpl.
pattern (list_size (fun st : term * term => size (fst st)) pb); rewrite <- plus_O_n.
apply Nat.add_lt_mono_r.
unfold lt; apply size_ge_one; trivial.
Qed.

Lemma matching_call2 :
  forall pat sub f lpat g lsub pb, 
     o_list_size ((pat,sub) :: nil) ((Term f (pat :: lpat), Term g (sub :: lsub)) :: pb).
Proof.
intros pat sub f lpat g lsub pb; unfold o_list_size; simpl.
auto with arith.
Qed.

Lemma matching_call3 :
  forall pat sub f lpat g lsub pb, 
     o_list_size ((Term f lpat, Term g lsub):: pb) ((Term f (pat :: lpat), Term g (sub :: lsub)) :: pb).
Proof.
intros pat sub f lpat g lsub pb; unfold o_list_size; simpl.
apply ->Nat.succ_lt_mono.
rewrite <- Nat.add_assoc.
 pattern ((fix size_list (l : list term) : nat :=
   match l with
   | nil => 0
   | t :: lt => size t + size_list lt
   end) lpat + list_size (fun st : term * term => size (fst st)) pb);
rewrite <- plus_O_n.
apply Nat.add_lt_mono_r.
unfold lt; apply size_ge_one; trivial.
Qed.

(** *** Definition of a step of matching. *)
Definition F_matching:
   forall pb (mrec : forall p, o_list_size p pb -> option substitution),
   option substitution.
Proof.
intros [ | [patt subj] pb] mrec.
exact (Some nil).
assert (Size := matching_call1 patt subj pb).
destruct patt as [x | f l].
set (o_subst := mrec _ Size).
destruct o_subst as [subst |].
exact (merge eq_var_bool eq_bool ((x,subj) :: nil) subst).
exact None.
destruct subj as [x | g m].
exact None.
case_eq (eq_symb_bool f g); [intro f_eq_g | intro f_diff_g].
destruct l as [ | pat lpat]; destruct m as [ | sub lsub].
set (o_subst := mrec _ Size).
destruct o_subst as [subst |].
exact (Some subst).
exact None.
exact None.
exact None.
assert (Size1 := matching_call2 pat sub f lpat g lsub pb).
set (o_subst1 := mrec _ Size1).
destruct o_subst1 as [subst1 | ]. 
assert (Size2 :=matching_call3 pat sub f lpat g lsub pb).
set (o_subst2 := mrec _ Size2).
destruct o_subst2 as [subst2 | ]. 
exact (merge eq_var_bool eq_bool subst1 subst2).
exact None.
exact None.
exact None.
Defined.

(** *** Definition of matching. *)
Definition matching : list (term * term) -> option substitution :=
Fix wf_size (fun l => option substitution) F_matching.

(** *** A more practical equivalent definition of matching. *)
Lemma matching_unfold : 
  forall l : list (term*term), matching l = @F_matching l (fun y _ => matching y).
Proof.
intros lpb; unfold matching.
refine (Fix_eq _ _ _ _ lpb).
clear lpb; intros lpb F G H.
unfold F_matching; destruct lpb as [ | [patt subj] lpb]; simpl; auto.
destruct patt as [x | f l]; destruct subj as [y | g m]; simpl; auto.
rewrite H; trivial.
rewrite H; trivial.
case (eq_symb_bool f g); trivial.
destruct l as [ | pat lpat]; destruct m as [ | sub lsub]; trivial.
rewrite H; trivial.
do 2 rewrite H; trivial.
Qed.

Lemma matching_unfold2 : forall pb,
  matching pb =
  match pb with
   | nil => Some nil
   | (patt, subj) :: pb =>
        match patt with
        | Var x => 
               match matching pb with
               | Some subst => merge eq_var_bool eq_bool ((x,subj) :: nil) subst
               | None => None
               end
         | Term f l => 
             match subj with
               | Var _ => None
               | Term g m => 
                   if eq_symb_bool f g
                  then
                      match l with
                      | nil =>
                          match m with
                          | nil => matching pb
                          | sub1 :: lsub => None
                          end
                      | pat1 :: lpat => 
                           match m with
                           | nil => None
                           | sub1 :: lsub => 
                             match (matching ((pat1, sub1) :: nil)) with
                              | Some subst1 => 
                                  match  (matching ((Term f lpat, Term g lsub) :: pb)) with
                                  | Some subst => merge eq_var_bool eq_bool subst1 subst
                                  | None => None
                                  end 
                              | None => None
                              end
                           end
                      end
                  else None
               end
         end
    end.
Proof.
intros pb; rewrite matching_unfold; unfold F_matching; simpl.
destruct pb as [ | [patt subj] pb]; trivial.
destruct patt as [ x | f l]; trivial.
destruct subj as [x | g m]; trivial.
case (eq_symb_bool f g); trivial.
destruct l as [ | pat1 lpat]; destruct m as [ | sub1 lsub]; trivial.
destruct (matching pb); trivial.
Qed.

Lemma matching_correct_aux :
  forall pb sigma, matching pb = Some sigma ->
           ((forall v t1, In (v,t1) sigma <-> find eq_var_bool v sigma = Some t1) /\
            (forall v p s, In v (var_list p) -> In (p,s) pb -> find eq_var_bool v sigma <> None) /\
            (forall v, find eq_var_bool v sigma <> None -> 
                                 exists p, exists s, In (p,s) pb /\ In v (var_list p)) /\
            (forall p s, In (p,s) pb -> apply_subst sigma p = s)).
Proof.
assert (Rt : reflexive _ (@eq term)).
intro a; reflexivity.
assert (change_hyp : forall sigma, (forall v t1, In (v,t1) sigma <-> find eq_var_bool v sigma = Some t1)  ->
  (forall a1 a1' b1 c1, In (a1,b1) sigma -> In (a1',c1) sigma -> eq_var_bool a1 a1' = true -> eq_bool b1 c1 =true)).
intros sigma H v v' t1 t2 H1 H2; generalize (X.eq_bool_ok v v') (eq_bool_ok t1 t2).
case (eq_var_bool v v').
case (eq_bool t1 t2).
intros _ _ _; reflexivity.
intros v_eq_v' t1_diff_t2; apply False_rect; apply t1_diff_t2.
subst v'; rewrite H in H1; rewrite H in H2; rewrite H1 in H2; injection H2; intro H3; exact H3.
intros _ _ Abs; discriminate.

intro pb; pattern pb; apply (well_founded_ind wf_size); clear pb.
intros [ | [patt subj] pb] IH sigma H; rewrite matching_unfold2 in H.
injection H; clear H; intros; subst; repeat split; trivial;
intros; try contradiction.
simpl in H; discriminate.
destruct patt as [ x | f l].
(* 1/2 the pattern is a variable *)
assert (H' := IH _ (matching_call1 _ _ _)).
destruct (matching pb) as [subst | ].
(* 1/3 the rest of the problem has subst as solution *)
generalize (H' _ (eq_refl _)) ; clear H'; intros [IH1 [IH2 [IH4 IH3]]].
assert (H' := merge_correct _ X.eq_bool_ok _ eq_bool_ok EX.eq_proof Rt ((x,subj) :: nil) subst).
rewrite H in H'; destruct H' as [H1 [H2 H3]].
split.
(* 1/4 first invariant unicity *)
intros v t1; split; intro Ht1.
assert (H'' := merge_inv _ X.eq_bool_ok _ eq_bool_ok EX.eq_proof Rt ((x,subj) :: nil) subst).
rewrite H in H''.
generalize (find_not_found eq_var_bool v v t1 sigma).
case_eq (find eq_var_bool v sigma).
intros t2 F _; apply f_equal; symmetry.
assert (t1_eq_t2 : eq_bool t1 t2 = true).
apply H'' with v v; trivial.
intros w w' u1 u2 [wu1_eq_xs | wu1_in_nil] [wu2_eq_xs | wu2_in_nil]; try contradiction.
injection wu1_eq_xs; intros; subst; 
injection wu2_eq_xs; intros; subst; trivial.
generalize (eq_bool_ok u2 u2); case (eq_bool u2 u2).
intros _; reflexivity.
intro u2_diff_u2; apply False_rect; apply u2_diff_u2; reflexivity.
apply change_hyp; assumption.
destruct (find_mem _ _ X.eq_bool_ok _ _ F) as [v' [l1 [l2 [K1 K2]]]]; subst; apply in_or_app; right; left; reflexivity.
apply eq_var_bool_refl.
generalize (eq_bool_ok t1 t2); rewrite t1_eq_t2; intro Eq; exact Eq.
intros _ Abs; apply False_rect; apply (Abs (eq_refl _) (eq_var_bool_refl v) Ht1).
destruct (find_mem _ _ X.eq_bool_ok _ _ Ht1) as [v' [l1 [l2 [K1 K2]]]]; subst; apply in_or_app; right; left; reflexivity.
split.
(* 1/4 second invariant domain of solution *)
intros v p s v_in_p [ps_eq_xsubj | ps_in_pb].
injection ps_eq_xsubj; clear ps_eq_xsubj; intros; subst; simpl.
destruct v_in_p as [v_eq_x | v_in_nil]; [subst v | contradiction].
rewrite (H1 x s).
discriminate.
simpl; rewrite eq_var_bool_refl; reflexivity.
assert (K2 := IH2 v p s v_in_p ps_in_pb).
case_eq (find eq_var_bool v subst).
intros v_subst H'.
destruct (H2 _ _ H') as [b' [H'' _]]; rewrite H''; discriminate.
intros H'; rewrite H' in K2; absurd (@None term = None); trivial.
split.
(* 1/4  third invariant domain of solution again *)
intros v H'; assert (H3v := H3 v).
destruct (find eq_var_bool v sigma) as [v_sigma | ].
destruct (H3v v_sigma (eq_refl _)) as [case1 | case2].
simpl in case1; revert case1; generalize (X.eq_bool_ok v x); case (eq_var_bool v x); [intro v_eq_x | intro v_diff_x].
subst v; exists (Var x); exists subj; split; left; trivial.
intro; discriminate.
destruct (IH4 v) as [p [s [ps_in_pb v_in_p]]].
rewrite (proj2 case2); discriminate.
exists p; exists s; split; trivial; right; trivial.
absurd (@None term = None); trivial.
(* 1/3  fourth invariant correctness *)
intros p s [ps_eq_xsubj | ps_in_pb].
assert (K1 := H1 x subj).
injection ps_eq_xsubj; clear ps_eq_xsubj; intros; subst; simpl.
rewrite K1; trivial.
simpl; rewrite eq_var_bool_refl; reflexivity.
assert (K2 : forall v, In v (var_list p) -> find eq_var_bool v subst <> None).
intros v v_in_p; apply IH2 with p s; trivial.
assert (KK2 : forall v, In v (var_list p) -> apply_subst subst (Var v) = apply_subst sigma (Var v)).
intros v v_in_p; generalize (K2 v v_in_p) (H2 v); simpl.
destruct (find eq_var_bool v subst) as [v_subst | ].
clear K2; intros _ K2; destruct (K2 _ (eq_refl _)) as [b [K3 K4]].
rewrite K3.
generalize (eq_bool_ok v_subst b); rewrite K4; intro K5; exact K5.
intro; absurd (@None term = None); trivial.
rewrite <- (IH3 _ _ ps_in_pb).
symmetry.
generalize KK2; clear s ps_in_pb K2 KK2; pattern p; apply term_rec3; clear p.
intros v KK2; apply KK2; left; trivial.
intros f l IHl KK2.
assert (IHl' : forall t, In t l -> apply_subst subst t = apply_subst sigma t).
intros t t_in_l; apply IHl; trivial.
intros v v_in_t; apply KK2.
destruct (In_split _ _ t_in_l) as [l1 [l2 H']]; subst l.
apply (@var_in_subterm v t (Term f (l1 ++ t :: l2)) (length l1 :: nil)); trivial.
simpl; rewrite nth_error_at_pos; trivial.
simpl; apply (f_equal (fun l => Term f l)).
apply map_eq; trivial.
(* 1/2 the rest of the problem has no solution *)
discriminate.

(* 1/1 the pattern is a compound term Term f l *)
destruct subj as [x | g m].
discriminate.
(* 1/1 the subject is a compound term Term g l *)
generalize (F.Symb.eq_bool_ok f g); revert H; case (eq_symb_bool f g); [intros H f_eq_g | intros H f_diff_g].
(* 1/2 both terms have the same top symbol *)
destruct l as [ | pat1 lpat]; destruct m as [ | sub1 lsub].
(* 1/5 patt = Term f nil, subj = Term f nil *)
destruct (IH _ (matching_call1 _ _ _) sigma H) as [H1 [H2 [H4 H3]]].
split; trivial.
split.
intros v p s v_in_p [ps_eq_ff | ps_in_pb].
injection ps_eq_ff; intros; subst.
contradiction.
apply H2 with p s; trivial.
split.
intros v H'; destruct (H4 _ H') as [p [s [ps_in_pb v_in_p]]].
exists p; exists s; split; trivial; right; trivial.
intros p s [ps_eq_ff | ps_in_pb].
injection ps_eq_ff; intros; subst; simpl; trivial.
apply H3; trivial.
(* 1/4 patt = Term f nil, subj = Term f (sub1 :: lsub) *)
discriminate.
(* 1/3 patt = Term f (pat1 :: lpat), subj = Term f nil *)
discriminate.
(* 1/2 patt = Term f (pat1 :: lpat), subj = Term f (sub1 :: lsub) *)
assert (H' := IH _ (matching_call2 pat1 sub1 f lpat g lsub pb)).
destruct (matching ((pat1,sub1) :: nil)) as [subst1 | ].
(* 1/3 pat1 = sub1 has subst1 as solution *)
generalize (H' _ (eq_refl _)); clear H'; intros [IH1 [IH2 [IH4 IH3]]].
assert (H' := IH _ (matching_call3 pat1 sub1 f lpat g lsub pb)).
destruct (matching ((Term f lpat, Term g lsub) :: pb)) as [subst | ].
(* 1/4 the rest of the problem has subst as solution *)
generalize (H' _ (eq_refl _)); clear H'; intros [IH1' [IH2' [IH4' IH3']]].
assert (H' := merge_correct _ X.eq_bool_ok _ eq_bool_ok EX.eq_proof Rt subst1 subst).
rewrite H in H'; destruct H' as [H1 [H2 H3]].
split.
(* 1/5 first invariant unicity *)
intros v t1; split; intro Ht1.
assert (H'' := merge_inv _ X.eq_bool_ok _ eq_bool_ok EX.eq_proof Rt subst1 subst).
rewrite H in H''.
generalize (find_not_found eq_var_bool v v t1 sigma).
case_eq (find eq_var_bool v sigma).
intros t2 F _; apply f_equal; symmetry.
assert (t1_eq_t2 : eq_bool t1 t2 = true).
apply H'' with v v; trivial.
apply change_hyp; assumption.
apply change_hyp; assumption.
destruct (find_mem _ _ X.eq_bool_ok _ _ F) as [v' [l1 [l2 [K1 K2]]]]; subst; apply in_or_app; right; left; reflexivity.
apply eq_var_bool_refl.
generalize (eq_bool_ok t1 t2); rewrite t1_eq_t2; intro Eq; exact Eq.
intros _ Abs; apply False_rect; apply (Abs (eq_refl _) (eq_var_bool_refl v) Ht1).
destruct (find_mem _ _ X.eq_bool_ok _ _ Ht1) as [v' [l1 [l2 [K1 K2]]]]; subst; apply in_or_app; right; left; reflexivity.
split.
(* 1/5 second invariant domain of solution *)
intros v p s v_in_p [ps_eq_patsub | ps_in_pb].
injection ps_eq_patsub; clear ps_eq_patsub; intros; subst; simpl.
simpl in v_in_p; destruct (in_app_or _ _ _ v_in_p) as [v_in_pat1 | v_in_lpat].
assert (K2 := IH2 v pat1 sub1 v_in_pat1 (or_introl _ (eq_refl _))).
case_eq (find eq_var_bool v subst1).
intros v_subst H'.
rewrite (H1 _ _ H'); discriminate.
intros H'; rewrite H' in K2; absurd (@None term = None); trivial.
assert (K2 := IH2' v (Term g lpat) (Term g lsub) v_in_lpat (or_introl _ (eq_refl _))).
case_eq (find eq_var_bool v subst).
intros v_subst H'.
destruct (H2 _ _ H') as [b [K3 _]]; rewrite K3; discriminate.
intros H'; rewrite H' in K2; absurd (@None term = None); trivial.
assert (K2 := IH2' v p s v_in_p (or_intror _ ps_in_pb)).
case_eq (find eq_var_bool v subst).
intros v_subst H'.
destruct (H2 _ _ H') as [b [K3 _]]; rewrite K3; discriminate.
intros H'; rewrite H' in K2; absurd (@None term = None); trivial.
split.
(* 1/5 second invariant domain of solution *)
intros v H'; assert (H3v := H3 v).
destruct (find eq_var_bool v sigma) as [v_sigma | ].
destruct (H3v v_sigma (eq_refl _)) as [case1 | case2].
destruct (IH4 v) as [p [s [ps_in_pb v_in_p]]].
rewrite case1; discriminate.
exists (Term f (pat1 :: lpat)); exists (Term g (sub1 :: lsub)); split.
left; trivial.
destruct ps_in_pb as [ps_eq_pat1sub1 | ps_in_nil].
injection ps_eq_pat1sub1; clear ps_eq_pat1sub1; intros; subst p s.
simpl; apply in_or_app; left; trivial.
contradiction.
destruct (IH4' v) as [p [s [ps_in_pb v_in_p]]].
rewrite (proj2 case2); discriminate.
destruct ps_in_pb as [ps_eq_patsub | ps_in_pb].
exists (Term f (pat1 :: lpat)); exists (Term g (sub1 :: lsub)); split.
left; trivial.
injection ps_eq_patsub; clear ps_eq_patsub; intros; subst p s.
simpl; apply in_or_app; right; trivial.
exists p; exists s; split; trivial; right; trivial.
absurd (@None term = None); trivial.
(* 1/4  third invariant correctness *)
intros p s [ps_eq_patsub | ps_in_pb].
injection ps_eq_patsub; clear ps_eq_patsub; intros; subst; simpl.
replace (apply_subst sigma pat1) with sub1.
apply (f_equal (fun l => Term g (sub1 :: l))).
assert (K := IH3' _ _ (or_introl _ (eq_refl _))).
simpl in K; injection K; clear K; intro K.
rewrite <- K; symmetry; apply map_eq.
intros p p_in_lpat.
rewrite <- subst_eq_vars.
assert (K2 : forall v, In v (var_list p) -> find eq_var_bool v subst <> None).
intros v v_in_p; apply IH2' with (Term g lpat) (Term g lsub); trivial.
destruct (In_split _ _ p_in_lpat) as [lpat1 [lpat2 H']]; subst lpat.
apply (@var_in_subterm v p (Term g (lpat1 ++ p :: lpat2)) (length lpat1 :: nil)); trivial.
simpl; rewrite nth_error_at_pos; trivial.
left; trivial.
intros v v_in_p; generalize (K2 v v_in_p) (H2 v); simpl.
destruct (find eq_var_bool v subst) as [v_subst | ].
clear K2; intros _ K2.
destruct (K2 _ (eq_refl _)) as [b [K3 K4]]; rewrite K3;  trivial.
generalize (eq_bool_ok v_subst b); rewrite K4; intro K5; exact K5.
intro; absurd (@None term = None); trivial.
assert (K := IH3 _ _ (or_introl _ (eq_refl _))).
rewrite <- K; symmetry.
rewrite <- subst_eq_vars.
assert (K2 : forall v, In v (var_list pat1) -> find eq_var_bool v subst1 <> None).
intros v v_in_pat1; apply IH2 with pat1 sub1; trivial.
left; trivial.
intros v v_in_pat1; generalize (K2 v v_in_pat1) (H1 v); simpl.
destruct (find eq_var_bool v subst1) as [v_subst1 | ].
clear K2; intros _ K2; rewrite (K2 _ (eq_refl _)); trivial.
intro; absurd (@None term = None); trivial.
rewrite <- (IH3' _ _ (or_intror _ ps_in_pb)).
symmetry; rewrite <- subst_eq_vars.
assert (K2 : forall v, In v (var_list p) -> find eq_var_bool v subst <> None).
intros v v_in_p; apply IH2' with p s; trivial; right; trivial.
intros v v_in_p; generalize (K2 v v_in_p) (H2 v); simpl.
destruct (find eq_var_bool v subst) as [v_subst | ].
clear K2; intros _ K2; destruct (K2 _ (eq_refl _)) as [b [K3 K4]]; rewrite K3.
generalize (eq_bool_ok v_subst b); rewrite K4; intro K5; exact K5.
intro; absurd (@None term = None); trivial.

(* 1/3 the rest of the problem has subst as solution *)
discriminate.
(* 1/2 pat1 = sub1 has no solution *)
discriminate.
(* 1/1 the terms do not have the same top symbol *)
discriminate.
Qed.

Lemma matching_correct :
  forall pb sigma, matching pb = Some sigma ->
            ((forall v p s, In v (var_list p) -> In (p,s) pb -> find eq_var_bool v sigma <> None) /\
           (forall v, find eq_var_bool v sigma <> None -> 
                                 exists p, exists s, In (p,s) pb /\ In v (var_list p)) /\
            (forall p s, In (p,s) pb -> apply_subst sigma p = s)).
Proof.
intros pb sigma H; generalize (matching_correct_aux pb H); intuition.
Qed.

Lemma matching_complete :
  forall pb sigma, (forall p s, In (p,s) pb -> apply_subst sigma p = s) ->
  match matching pb with
  | Some tau => forall v p s, In v (var_list p) -> In (p,s) pb -> 
                                    apply_subst tau (Var v) = apply_subst sigma (Var v)
  | None => False
  end.
Proof.
assert (Rt : reflexive _ (@eq term)).
intro a; reflexivity.
intro pb; pattern pb; apply (well_founded_ind wf_size); clear pb.
intros [ | [patt subj] pb] IH sigma H;
rewrite matching_unfold2.
intros; contradiction.
assert (tailH : forall p s : term, In (p, s) pb -> apply_subst sigma p = s).
intros; apply H; right; assumption.
assert (Hsigma := IH _ (matching_call1 _ _ _) sigma tailH).
destruct patt as [ x | f l].
(* 1/2 the pattern is a variable *)
case_eq (matching pb).
intros subst matching_pb_eq_subst; rewrite matching_pb_eq_subst in Hsigma.
destruct (matching_correct_aux pb matching_pb_eq_subst) as [C1 [C2 [C4 C3]]].
(* 1/3 the rest of the problem has subst as solution *)
assert (H'' := merge_correct _ X.eq_bool_ok _ eq_bool_ok EX.eq_proof Rt ((x,subj) :: nil) subst).
case_eq (merge eq_var_bool eq_bool ((x, subj) :: nil) subst).
(* 1/4 the merging of substitutions succeeded *)
intros tau matching_pb_eq_tau; rewrite matching_pb_eq_tau in H''.
destruct H'' as [H1 [H2 H3]].
intros v p s v_in_p [ps_eq_xsubj | ps_in_pb].
injection ps_eq_xsubj; clear ps_eq_xsubj; intros; subst.
destruct v_in_p as [v_eq_x | v_in_nil]; [idtac | contradiction].
subst v; rewrite (H (Var x) s (or_introl _ (eq_refl _))).
simpl; rewrite (H1 x s); trivial.
simpl; rewrite eq_var_bool_refl; reflexivity.
rewrite <- (Hsigma v p s v_in_p ps_in_pb).
simpl; assert (K2 := C2 v p s v_in_p ps_in_pb).
case_eq (find eq_var_bool v subst).
intros v_subst H''; destruct (H2 _ _ H'') as [b [K3 K4]]; rewrite K3; trivial.
symmetry; generalize (eq_bool_ok v_subst b); rewrite K4; intro K5; exact K5.
intros H''; rewrite H'' in K2; absurd (@None term = None); trivial.
(* 1/3  the merging of substitutions failed *)
intro matching_pb_eq_none; rewrite matching_pb_eq_none in H''.
destruct H'' as [v [v' [t1 [t2 [H1 [H2 [v_eq_v' t1_diff_t2]]]]]]].
generalize (X.eq_bool_ok v v'); rewrite v_eq_v'; intro v_eq_v''; subst v'.
generalize (eq_bool_ok t2 t1); rewrite t1_diff_t2; clear t1_diff_t2; intro t1_diff_t2.
rewrite C1 in H1; rewrite C1 in H2.
case H1; clear H1; intro H1.
destruct (C4 v) as [p [s [ps_in_pb v_in_p]]].
rewrite H2; discriminate.
simpl in H1; generalize (X.eq_bool_ok v x); destruct (eq_var_bool v x); 
[intros v_eq_x | intros v_diff_x; discriminate].
subst v; injection H1; clear H1; intros; subst subj.
assert (Hv := Hsigma x p s v_in_p ps_in_pb).
assert (Hv' := H (Var x) t1 (or_introl _ (eq_refl _))).
rewrite Hv' in Hv; simpl in Hv; rewrite H2 in Hv; absurd (t2 = t1); assumption.
rewrite H1 in H2; apply t1_diff_t2; symmetry; injection H2; intro H3; exact H3.
(* 1/2 the rest of the problem has no solution *)
intro matching_pb_eq_none; rewrite matching_pb_eq_none in Hsigma.
elim Hsigma.

(* 1/1 the pattern is a compound term Term f l *)
destruct subj as [x | g m].
assert (H' := H (Term f l) (Var x) (or_introl _ (eq_refl _))); simpl in H'.
discriminate.
(* 1/1 the subject is a compound term Term g l *)
case_eq (eq_symb_bool f g); [intro f_eq_g | intro f_diff_g].
(* 1/2 both terms have the same top symbol *)
destruct l as [ | pat1 lpat]; destruct m as [ | sub1 lsub].
(* 1/5 patt = Term f nil, subj = Term f nil *)
destruct (matching pb) as [tau | ]. 
intros v p s v_in_p [ps_eq_ff | ps_in_pb].
injection ps_eq_ff; intros; subst; simpl in v_in_p; contradiction.
apply Hsigma with p s; trivial.
contradiction.
(* 1/4 patt = Term f nil, subj = Term f (sub1 :: lsub) *)
assert (H' := H (Term f nil) (Term g (sub1 :: lsub)) (or_introl _ (eq_refl _))); simpl in H'.
discriminate.
(* 1/3 patt = Term f (pat1 :: lpat), subj = Term f nil *)
assert (H' := H (Term f (pat1 :: lpat)) (Term g nil) (or_introl _ (eq_refl _))); simpl in H'.
discriminate.
(* 1/2 patt = Term f (pat1 :: lpat), subj = Term f (sub1 :: lsub) *)
assert (H' := IH _ (matching_call2 pat1 sub1 f lpat g lsub pb)).
assert (Correct := matching_correct_aux ((pat1,sub1) :: nil)).
case_eq (matching ((pat1,sub1) :: nil)).
(* 1/3 pat1 = sub1 has subst1 as solution *)
intros subst1 matching_pat1sub1_eq_subst1.
destruct (Correct _ matching_pat1sub1_eq_subst1) as  [C1 [C2 [C4 C3]]]; clear Correct.
assert (H'' := IH _ (matching_call3 pat1 sub1 f lpat g lsub pb)).
assert (Correct' := matching_correct_aux ((Term f lpat, Term g lsub) :: pb)).
case_eq (matching ((Term f lpat, Term g lsub) :: pb)).
(* 1/4 the rest of the problem has subst as solution *)
intros subst matching_pb_eq_subst.
destruct (Correct' _ matching_pb_eq_subst) as  [C1' [C2' [C4' C3']]]; clear Correct'.
assert (H''' := merge_correct _ X.eq_bool_ok _ eq_bool_ok EX.eq_proof Rt subst1 subst).
assert (headH : forall p s, In (p,s) ((pat1,sub1) :: nil) -> apply_subst sigma p = s).
intros p s [ps_eq_pat1sub1 | ps_in_nil]; [idtac | contradiction].
injection ps_eq_pat1sub1; clear ps_eq_pat1sub1; intros; subst p s.
assert (K := H _ _ (or_introl _ (eq_refl _))).
simpl in K; injection K; intros; subst; trivial.
assert (Hsigma1 := IH _ (matching_call2  pat1 sub1 f lpat g lsub pb) sigma headH).
rewrite matching_pat1sub1_eq_subst1 in Hsigma1.
clear tailH; assert (tailH : forall p s, In (p,s) ((Term f lpat, Term g lsub) :: pb) -> apply_subst sigma p = s).
intros p s [ps_eq_patsub | ps_in_pb].
injection ps_eq_patsub; clear ps_eq_patsub; intros; subst p s.
assert (K := H _ _ (or_introl _ (eq_refl _))).
simpl in K; injection K; intros; subst; trivial.
apply H; right; trivial.
clear Hsigma; assert (Hsigma := IH _ (matching_call3  pat1 sub1 f lpat g lsub pb) sigma tailH).
rewrite matching_pb_eq_subst in Hsigma.
case_eq (merge eq_var_bool eq_bool subst1 subst).
(* 1/5 the merging of substitutions succeeded *)
intros tau matching_pb_eq_tau; rewrite matching_pb_eq_tau in H'''.
destruct H''' as [H1 [H2 H3]].
intros v p s v_in_p [ps_eq_pat_sub | ps_in_pb].
injection ps_eq_pat_sub; clear ps_eq_pat_sub; intros; subst p s.
rewrite var_list_unfold in v_in_p; simpl in v_in_p.
destruct (in_app_or _ _ _ v_in_p) as [v_in_pat1 | v_in_lpat]; clear v_in_p.
rewrite <- (Hsigma1 v _ _ v_in_pat1 (or_introl _ (eq_refl _))).
simpl; assert (K2 := C2 v _ _ v_in_pat1 (or_introl _ (eq_refl _))).
case_eq (find eq_var_bool v subst1).
intros v_subst1 H'''; rewrite (H1 _ _ H'''); trivial.
intros H'''; rewrite H''' in K2; absurd (@None term = None); trivial.
assert (K := Hsigma v (Term f lpat) (Term g lsub)).
simpl in K; generalize (K v_in_lpat (or_introl _ (eq_refl _))); clear K; intro K.
simpl; assert (K2 := C2' v (Term f lpat) (Term g lsub)).
simpl in K2; generalize (K2 v_in_lpat (or_introl _ (eq_refl _))); clear K2; intro K2.
case_eq (find eq_var_bool v subst); [idtac | intro H'''; rewrite H''' in K2; apply False_rect; apply K2; reflexivity].
intros v_subst H'''; destruct (H2 _ _ H''') as [b [K3 K4]].
generalize (eq_bool_ok v_subst b); rewrite K4; clear K4; intro K4; subst b.
rewrite H''' in K; rewrite K3; assumption.
assert (K := Hsigma v p s v_in_p (or_intror _ ps_in_pb)).
simpl; assert (K2 := C2' v p s v_in_p (or_intror _ ps_in_pb)).
simpl in K; case_eq (find eq_var_bool v subst).
intros v_subst H'''; destruct (H2 _ _ H''') as [b [K3 K4]].
generalize (eq_bool_ok v_subst b); rewrite K4; clear K4; intro K4; subst b.
rewrite H''' in K; rewrite K3; assumption.
intros H'''; rewrite H''' in K2; absurd (@None term = None); trivial.
(* 1/4 the merging of substitutions failed *)
intro matching_pb_eq_none; rewrite matching_pb_eq_none in H'''.
destruct H''' as [v [v' [t1 [t2 [H1 [H2 [v_eq_v' t1_diff_t2]]]]]]].
generalize (X.eq_bool_ok v v'); rewrite v_eq_v'; intro v_eq_v''; subst v'.
generalize (eq_bool_ok t2 t1); rewrite t1_diff_t2; clear t1_diff_t2; intro t1_diff_t2.
case H1; clear H1; intro H1.
destruct (C4 v) as [p [s [ps_in_pb v_in_p]]].
rewrite H1; discriminate.
assert (H1v := Hsigma1 v p s v_in_p ps_in_pb); simpl in H1v.
rewrite H1 in H1v.
destruct (C4' v) as [p' [s' [ps'_in_pb v_in_p']]].
rewrite C1' in H2; rewrite H2; discriminate.
assert (H2v := Hsigma v p' s' v_in_p' ps'_in_pb); simpl in H2v.
rewrite <- H2v in H1v.
rewrite C1' in H2; rewrite H2 in H1v; apply t1_diff_t2; symmetry; assumption.
apply t1_diff_t2; symmetry; rewrite C1' in H1; rewrite C1' in H2; rewrite H1 in H2; injection H2; intro H3; exact H3.
(* 1/3 the rest of the problem has no solution *)
intro matching_pb_eq_none; rewrite matching_pb_eq_none in H''.
apply (H'' sigma).
intros p s [ps_eq_patsub | ps_in_pb].
injection ps_eq_patsub; clear ps_eq_patsub; intros; subst p s.
assert (K := H _ _ (or_introl _ (eq_refl _))).
simpl in K; injection K; intros; subst; trivial.
apply H; right; trivial.

(* 1/2 pat1 = sub1 has no solution *)
intro matching_pb_eq_none; rewrite matching_pb_eq_none in H'.
apply (H' sigma).
intros p s [ps_eq_patsub | ps_in_pb].
injection ps_eq_patsub; clear ps_eq_patsub; intros; subst p s.
assert (K := H _ _ (or_introl _ (eq_refl _))).
simpl in K; injection K; intros; subst; trivial.
contradiction.
(* 1/1 the terms do not have the same top symbol *)
absurd (f=g).
generalize (F.Symb.eq_bool_ok f g); rewrite f_diff_g; intro H3; exact H3.
assert (K := H _ _ (or_introl _ (eq_refl _))).
simpl in K; injection K; intros; subst; trivial.
Qed.

End Make'.

Module Make (F1 : Signature) (X1 : decidable_set.S) : 
     Term with Module F := F1 with Module X := X1 := Make' F1 X1.
