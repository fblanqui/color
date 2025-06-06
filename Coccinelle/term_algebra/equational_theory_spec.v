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


(** * Equational theory on a term algebra *)

From Stdlib Require Import List Relations Wellfounded Arith Setoid.
From CoLoR Require Import closure more_list weaved_relation dickson term_spec.

Notation " T '-[' R ']->' U " := (R U T) (at level 80) : term_scope .

(** ** Module Type EqTh, an equational theory over a term algebra. *)

Module Type EqTh.

  Declare Module T : Term.

  Import T.

 Inductive defined (R : relation term) : symbol -> Prop :=
  | Def : forall f l t, R t (Term f l) -> defined R f.

 Inductive constructor (R : relation term) : symbol -> Prop :=
  | Const : forall f, (forall l t, ~ (R t (Term f l))) -> constructor R f.

Inductive module (R1 R2 : relation term) : Prop :=
  | Mod : 
      (forall f2 s t, defined R2 f2 ->  R1 s t -> symb_in_term_list f2 (s :: t :: nil) = false) ->
      module R1 R2.

  (** *** One step at top. *)
  Inductive axiom (R : relation term) : term -> term -> Prop :=
    | instance : 
        forall t1 t2 sigma, R t1 t2 -> axiom R (apply_subst sigma t1) (apply_subst sigma t2).

  (** *** One step at any position. *)
  Inductive one_step (R : relation term) : term -> term -> Prop :=
  | at_top : forall t1 t2, axiom R t1 t2 -> one_step R t1 t2
  | in_context : forall f l1 l2, one_step_list (one_step R) l1 l2 -> one_step R (Term f l1) (Term f l2).

  (** *** Equational Theory as reflexive, symetric 
      and transitive closure of an equational step. *)
  
  (** *** Rewriting Theory as transitive closure of an equational step. *)
  Definition rwr (R : relation term) := trans_clos (one_step R).

  Parameter one_step_one_rule :
    forall R s t, one_step R t s -> 
    exists r, exists l, R r l /\ one_step (fun r' l' => In (r',l') ((r,l) :: nil)) t s.

Notation " T '-[' R '+]->' U " := (rwr R T U) (at level 80) : term_scope .


  Parameter no_need_of_instance' : forall (R : relation term) t1 t2, R t1 t2 -> axiom R t1 t2.

  Parameter context_in :
    forall R t1 t2, rwr R t1 t2 -> forall f l l', rwr R (Term f (l ++ t1  :: l')) (Term f (l ++ t2 :: l')).

  Parameter general_context :
    forall R f l1 l2, rwr_list (one_step R) l1 l2 -> rwr R (Term f l1) (Term f l2).

  Parameter one_step_apply_subst :
     forall R t1 t2 sigma , one_step R t1 t2 ->
	one_step R (apply_subst sigma t1) (apply_subst sigma t2).

 Parameter one_step_subterm_subst :
   forall R s t sigma, 
   refl_trans_clos (union _ (one_step R) (direct_subterm)) s t ->
   refl_trans_clos (union _ (one_step R) (direct_subterm)) (apply_subst sigma s) (apply_subst sigma t).

  Parameter  rwr_apply_subst :
    forall R t1 t2 sigma, rwr R t1 t2 -> 
      rwr R (apply_subst sigma t1) (apply_subst sigma t2).

  Parameter rwr_inv : 
    forall A R (eq : A -> A -> Prop) (f : term -> A), 
      (forall a1 a2 a3, eq a1 a2 -> eq a2 a3 -> eq a1 a3) ->
      (forall t1 t2, one_step R t1 t2 -> eq (f t1) (f t2)) ->
      forall t1 t2, rwr R t1 t2 -> eq (f t1) (f t2).

  Parameter one_step_incl :
    forall (R1 R2 : term -> term -> Prop) , 
      (forall t1 t2, R1 t1 t2 -> R2 t1 t2) ->
      forall t1 t2, one_step R1 t1 t2 -> one_step R2 t1 t2.

  Parameter rwr_incl :
    forall (R1 R2 : term -> term -> Prop), 
      (forall t1 t2, R1 t1 t2 -> R2 t1 t2) ->
      forall t1 t2, rwr R1 t1 t2 -> rwr R2 t1 t2.

 Parameter rwr_list_incl :
    forall (R1 R2 : term -> term -> Prop), 
      (forall t1 t2, R1 t1 t2 -> R2 t1 t2) ->
      forall l1 l2, rwr_list (one_step R1) l1 l2 -> rwr_list (one_step R2) l1 l2.

  Parameter th_eq_closure_one_step :
    forall (R : term -> term -> Prop), 
      forall t1 t2, one_step (rwr R) t1 t2 -> rwr R t1 t2.

  Parameter th_eq_closure :
    forall t1 t2 (R : term -> term -> Prop),
      rwr (rwr R) t1 t2 -> rwr R t1 t2.

  Parameter  R_in_rwr_R : 
  forall t1 t2 (R : term -> term -> Prop),
   R t1 t2 -> rwr R t1 t2.

 Parameter split_rel :
  forall R1 R2 s t, one_step (union _ R1 R2) t s <->
  (one_step R1 t s \/ one_step R2 t s).

  Parameter  no_need_of_instance_is_modular :
    forall (R1 R2 : term -> term -> Prop), 
      (forall t1 t2, axiom R1 t1 t2 -> R1 t1 t2) ->
      (forall t1 t2, axiom R2 t1 t2 -> R2 t1 t2) ->
      (forall t1 t2, axiom (union term R1 R2) t1 t2 -> (union term R1 R2) t1 t2).

Definition non_overlapping (R : relation term) := 
  forall l1 r1 l2 r2 sigma tau, R r1 l1 -> R r2 l2 -> 
  forall f l p, subterm_at_pos l1 p = Some (Term f l) ->
  apply_subst sigma (Term f l) = apply_subst tau l2 -> p = nil /\ l1 = l2 /\ r1 = r2.

Definition overlay (R : relation term) := 
  forall l1 r1 l2 r2 sigma tau, R r1 l1 -> R r2 l2 -> 
  forall f l p, subterm_at_pos l1 p = Some (Term f l) ->
  apply_subst sigma (Term f l) = apply_subst tau l2 -> p = nil.

  Definition sym_refl R (t1 t2 : term) := R t1 t2 \/ R t2 t1 \/ t1 = t2.
  Definition th_eq R := rwr (sym_refl R).

Notation " T '<-[' R '*]->' U " := (th_eq R T U) (at level 80) : term_scope .

  Parameter th_refl : forall R t, th_eq R t t.

  Parameter th_sym : forall R t1 t2, th_eq R t1 t2 -> th_eq R t2 t1.

Parameter rwr_at_pos :
 forall R p t sigma u v t', subterm_at_pos t p = Some (apply_subst sigma u) -> 
  rwr R u v -> t' = (replace_at_pos t (apply_subst sigma v) p) -> rwr R t t'.

(** *** Accessibility of the rewriting relation. *)
Parameter acc_one_step :  forall R t, Acc (one_step R) t <-> Acc (rwr R) t.

Parameter rwr_sub_acc_sub_acc_sub :
  forall R l1 l2, refl_trans_clos (one_step_list (one_step R)) l2 l1 -> 
  (forall s, In s l1 -> Acc (one_step R) s) -> (forall s, In s l2 -> Acc (one_step R) s).

Parameter acc_subterms :
  forall R, (forall x t, ~ (R t (Var x))) -> 
  forall f l, (forall t, In t l -> Acc (one_step R) t) -> constructor R f ->
                   Acc (one_step R) (Term f l).

Parameter acc_subterms_1 : 
   forall R t s, Acc (one_step R) t -> direct_subterm s t -> Acc (one_step R) s.

Parameter acc_subterms_3 : 
   forall R p t s, Acc (one_step R) t -> subterm_at_pos t p = Some s -> 
   Acc (one_step R) s.

Parameter acc_with_subterm_subterms :
  forall R t, Acc (union _ (one_step R) direct_subterm) t ->
                 forall s, direct_subterm s t ->
                   Acc (union _ (one_step R) direct_subterm) s.

Parameter acc_with_subterm :
  forall R t, Acc (one_step R) t <-> Acc (union _ (one_step R) direct_subterm) t.

Parameter var_acc : 
   forall R l x sigma, In x (var_list_list l) -> 
   (forall t, In t (map (apply_subst sigma) l) -> Acc (one_step R) t) ->
   Acc (one_step R) (apply_subst sigma (Var x)).

Parameter term_acc_subst :
  forall R t sigma, Acc (one_step R) (apply_subst sigma t) -> Acc (one_step R) t.

Parameter nf_one_step_subterm:
  forall R t, nf (one_step R) t -> forall s, direct_subterm s t -> nf (one_step R) s.

Parameter compute_red : list (term * term) -> term -> list term.

Parameter compute_red_is_correct :
   forall rule_list : list (term * term),
   (forall l r : term, In (l, r) rule_list -> forall v : variable, In v (var_list r) -> In v (var_list l)) ->
   forall R : term -> term -> Prop,
   (forall l r : term, R r l <-> In (l, r) rule_list) ->
   forall t s : term, In s (compute_red rule_list t) <-> one_step R s t.

Parameter well_formed_rwr : 
  forall (R : relation term), (forall s t, R s t -> forall x, In x (var_list s) -> In x (var_list t)) ->
  (forall r l, R r l -> well_formed r /\ well_formed l) -> 
  forall s t, rwr R t s -> well_formed s -> well_formed t.

Parameter Acc_var :
      forall R : relation term, (forall v t, ~ R t (Var v)) -> forall x, Acc (one_step R) (Var x).

Parameter acc_well_formed_acc_all :
      forall R : relation term,
       (forall s t, R s t -> forall x : variable, In x (var_list s) -> In x (var_list t)) ->
       (forall v t, ~ R t (Var v)) ->
       (forall s t, R s t -> well_formed s /\ well_formed t) ->
       forall (inject : nat -> variable) (inject_inv : variable -> nat),
       (forall n : nat, inject_inv (inject n) = n) ->
       (forall t : term, well_formed t -> Acc (one_step R) t) ->
       forall t : term, Acc (one_step R) t.

Parameter are_constructors_of_R :
  forall R, (forall v t, ~ R t (Var v)) -> 
  forall  f l t', (refl_trans_clos (one_step R) t' (Term f l)) ->
  (~defined R f) ->
  exists l', t' = Term f l' /\ refl_trans_clos (one_step_list (one_step R)) l' l.

End EqTh.
