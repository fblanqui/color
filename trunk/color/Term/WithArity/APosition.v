(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui & Wang Qian & Zhang Lianyi, 2009-05-06

positions in a term and related functions and relations:
subterm at some position, replacement of a subterm at some position,
context corresponding to a position, position of the Hole of a context,
definition of rewriting based on positions
*)

Set Implicit Arguments.

Require Import ATrs.
Require Import List.
Require Import NatUtil.
Require Import VecUtil.
Require Import LogicUtil.
Require Import ExcUtil.

(***********************************************************************)
(** positions are lists of natural numbers *)

Notation position := (list nat).

Section S.

Variable Sig : Signature.

Notation term := (term Sig). Notation context := (context Sig).

(***********************************************************************)
(** context corresponding to a position *)

Fixpoint context_pos (t : term) (ps : position) {struct t} : option context :=
  match t, ps with
    | _, nil => Some Hole
    | Var x, _ :: _ => None
    | Fun f ts, p :: ps => 
      match lt_ge_dec p (arity f) with 
        | left h =>
          match context_pos (Vnth ts h) ps with
            | None => None
            | Some x =>
              Some (Cont f (Veq_app_cons_aux3 h)
                (Vsub ts (Veq_app_cons_aux1 h))
                x (Vsub ts (Veq_app_cons_aux2 h)))
          end
        | right _ => None
      end
  end.

(***********************************************************************)
(** subterm at some position *)

Fixpoint subterm_pos (t : term) (ps : position) {struct ps} : option term :=
  match t, ps with
    | _ , nil => Some t
    | Var x , _ :: _ => None
    | Fun f ts, p :: ps' => 
      match lt_ge_dec p (arity f) with 
        | left h => subterm_pos (Vnth ts h) ps'
        | right _ => None
      end
  end.

Lemma subterm_pos_elim : forall p t u, subterm_pos t p = Some u ->
  exists C, context_pos t p = Some C /\  t = fill C u.

Proof.
induction p; simpl; intros.
(* nil *)
exists Hole. simpl. destruct t; inversion H; auto.
(* cons *)
destruct t. discr. gen H. simpl.
destruct (lt_ge_dec a (arity f)); intros. 2: discr.
destruct (IHp _ _ H). destruct H0. rewrite H0.
exists (Cont f (Veq_app_cons_aux3 l)
  (Vsub v (Veq_app_cons_aux1 l)) x (Vsub v (Veq_app_cons_aux2 l))).
intuition. simpl. apply args_eq. rewrite <- H1. apply Veq_app_cons_aux.
Qed.

(***********************************************************************)
(** replace subterm at some position *)

Fixpoint replace_pos (t : term) (ps : position) (u : term) {struct t}
  : option term :=
  match t, ps with
    | _, nil => Some u
    | Var x, _ :: _ => None
    | Fun f ts, p :: ps' =>
      match lt_ge_dec p (arity f) with
        | left h =>
          match replace_pos (Vnth ts h) ps' u with
            | None => None
            | Some v => Some (Fun f (Vreplace ts h v))
          end
        | right _ => None
      end
  end.

Lemma replace_pos_elim : forall p t u t', replace_pos t p u = Some t' ->
  exists C, context_pos t p = Some C /\ t' = fill C u.

Proof.
induction p; intros.
(* nil *)
exists Hole. simpl. destruct t; inversion H; auto.
(* cons *)
destruct t; destruct t'.
(* Var, Var *)
discr.
(* Var, Fun *)
discr.
(* Fun, Var *)
gen H. simpl. destruct (lt_ge_dec a (arity f)); intro.
destruct (replace_pos (Vnth v l) p u); inversion H. discr.
(* Fun, Fun *)
generalize H. simpl. destruct (lt_ge_dec a (arity f)); intro. 2: discr.
destruct (replace_pos (Vnth v l) p u). 2: discr.
apply Some_eq in H0. Funeqtac. subst v0.
destruct (IHp (Vnth v l) u t). gen H. simpl.
destruct (lt_ge_dec a (arity f)); intro. 2: discr.
assert (l0 = l). apply lt_unique. subst l0.
destruct (replace_pos (Vnth v l) p u). 2: discr.
apply (f_equal Some). apply Some_eq in H. Funeqtac.
apply Vreplace_eq_elim in H0. hyp. destruct H0. rewrite H0.
exists (Cont f (Veq_app_cons_aux3 l) (Vsub v (Veq_app_cons_aux1 l)) x
  (Vsub v (Veq_app_cons_aux2 l))). intuition. simpl. apply args_eq.
assert (fill x u = Vnth (Vreplace v l t) l). rewrite <- H1.
rewrite Vnth_replace. refl. rewrite H2.
rewrite (Veq_app_cons_aux (Vreplace v l t) (Veq_app_cons_aux1 l)
  l (Veq_app_cons_aux2 l) (Veq_app_cons_aux3 l)).
apply Vcast_eq. apply Vapp_eq. rewrite Vsub_replace_l. refl. omega.
apply Vcons_eq. rewrite Vnth_cast. rewrite Vnth_app_cons. refl.
rewrite Vsub_replace_r. refl. omega.
Qed.

Implicit Arguments replace_pos_elim [p t u t'].

(***********************************************************************)
(** position of the Hole in a context *)

Fixpoint pos_context (C : context) : position :=
  match C with
    | Hole => nil
    | Cont _ i _ _ _ C _ => i :: pos_context C
  end.

Lemma subterm_fill_pos_context : forall c u,
  subterm_pos (fill c u) (pos_context c) = Some u.

Proof.
induction c; intros; simpl.
destruct u; auto.
case (lt_ge_dec i (arity f)); intro. 2: absurd_arith.
rewrite Vnth_cast. rewrite Vnth_app_cons. apply IHc.
Qed.

Lemma replace_fill_pos_context : forall c u v,
  replace_pos (fill c u) (pos_context c) v = Some (fill c v).

Proof.
induction c; intros; simpl.
(* nil *)
destruct u; auto.
(* cons *)
case (lt_ge_dec i (arity f)); intro. rewrite Vnth_cast. rewrite Vnth_app_cons.
2: absurd_arith. rewrite (IHc u v1). apply (f_equal Some). apply args_eq.
apply Veq_nth; intros. rewrite Vnth_cast.
destruct (eq_nat_dec i i0).
subst i0. rewrite Vnth_replace. rewrite Vnth_app_cons. refl.
rewrite Vnth_replace_neq. 2: hyp. rewrite Vnth_cast.
apply Vnth_app_cons_neq. auto.
Qed. 

(***********************************************************************)
(** definition of rewriting based on positions *)

Definition red_pos R u v := exists p, exists l, exists r, exists s,
  In (mkRule l r) R
  /\ subterm_pos u p = Some (sub s l)
  /\ replace_pos u p (sub s r) = Some v.

Lemma red_pos_ok : forall R t u, red R t u <-> red_pos R t u.

Proof.
split; intro.
(* red << red_pos *)
redtac. unfold red_pos. exists (pos_context c). exists l. exists r. exists s.
intuition; rewrite xl. apply subterm_fill_pos_context.
rewrite yr. apply replace_fill_pos_context.
(* red_pos << red *)
unfold red. unfold red_pos in H. decomp H.
exists x0. exists x1. apply subterm_pos_elim in H1. decomp H1.
exists x3. exists x2. intuition. ded (replace_pos_elim H3). decomp H.
rewrite H2 in H5. inversion H5. subst x4. hyp.
Qed.

End S.
