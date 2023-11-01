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

From CoLoR Require Import ATrs ListUtil NatUtil VecUtil LogicUtil OptUtil.

(***********************************************************************)
(** positions are lists of natural numbers *)

Notation position := (list nat).

Section S.

Variable Sig : Signature.

Notation term := (term Sig). Notation context := (context Sig).
Notation terms := (vector term).

(***********************************************************************)
(** context corresponding to a position *)

Fixpoint context_pos (t : term) (ps : position) : option context :=
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
  {C | context_pos t p = Some C /\  t = fill C u}.

Proof.
induction p; simpl; intros.
(* nil *)
exists Hole. simpl. destruct t; inversion H; auto.
(* cons *)
destruct t. discr. revert H. simpl.
destruct (lt_ge_dec a (arity f)); intros. 2: discr.
destruct (IHp _ _ H). destruct a0. rewrite H0.
exists (Cont f (Veq_app_cons_aux3 l)
  (Vsub t (Veq_app_cons_aux1 l)) x (Vsub t (Veq_app_cons_aux2 l))).
intuition. simpl. apply args_eq. rewrite <- H1. apply Veq_app_cons_aux.
Defined.

Lemma subterm_pos_sub : forall s u p t,
  subterm_pos t p = Some u -> subterm_pos (sub s t) p = Some (sub s u).

Proof.
induction p; destruct t; simpl; intros.
inversion H. simpl. destruct (s n); refl.
inversion H. rewrite sub_fun. refl.
discr. revert H. destruct (lt_ge_dec a (arity f)); intro.
rewrite Vnth_map. apply IHp. hyp. discr.
Qed.

(***********************************************************************)
(** replace subterm at some position *)

Fixpoint replace_pos (t : term) (ps : position) (u : term)
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

Lemma subterm_pos_replace_eq_Some : forall p u v t,
  subterm_pos t p = Some u -> {w | replace_pos t p v = Some w}.

Proof.
induction p; simpl; intros.
(* nil *)
destruct t; exists v; simpl; refl.
(* cons *)
destruct t. discr. simpl.
case_eq (lt_ge_dec a (arity f)); intros l H0; rewrite H0 in H; clear H0.
destruct (IHp _ v _ H). rewrite e. exists (Fun f (Vreplace t l x)). refl.
discr.
Defined.

Lemma subterm_pos_replace_neq_None : forall p u v t,
  subterm_pos t p = Some u -> replace_pos t p v <> None.

Proof.
intros. destruct (subterm_pos_replace_eq_Some p v t H). rewrite e. discr.
Qed.

Lemma replace_pos_elim : forall p t u t', replace_pos t p u = Some t' ->
  {C | context_pos t p = Some C /\ t' = fill C u}.

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
revert H. simpl. destruct (lt_ge_dec a (arity f)); intro.
destruct (replace_pos (Vnth t l) p u); inversion H. discr.
(* Fun, Fun *)
gen H. simpl. destruct (lt_ge_dec a (arity f)); intro. 2: discr.
destruct (replace_pos (Vnth t l) p u). 2: discr.
apply Some_eq in H0. Funeqtac. subst t0.
destruct (IHp (Vnth t l) u t1). revert H. simpl.
destruct (lt_ge_dec a (arity f)); intro. 2: discr.
assert (l0 = l). apply lt_unique. subst l0.
destruct (replace_pos (Vnth t l) p u). 2: discr.
f_equal. apply Some_eq in H. Funeqtac.
apply Vreplace_eq_elim in H0. hyp. destruct a0. rewrite H0.
exists (Cont f (Veq_app_cons_aux3 l) (Vsub t (Veq_app_cons_aux1 l)) x
  (Vsub t (Veq_app_cons_aux2 l))). intuition. simpl. apply args_eq.
assert (fill x u = Vnth (Vreplace t l t1) l). rewrite <- H1.
rewrite Vnth_replace. refl. rewrite H2.
rewrite (Veq_app_cons_aux (Vreplace t l t1) (Veq_app_cons_aux1 l)
  l (Veq_app_cons_aux2 l) (Veq_app_cons_aux3 l)).
apply Vcast_eq_intro. apply Vapp_eq_intro. rewrite Vsub_replace_l. refl. lia.
apply Vcons_eq_intro. rewrite Vnth_cast. rewrite Vnth_app_cons. refl.
rewrite Vsub_replace_r. refl. lia.
Defined.

Arguments replace_pos_elim [p t u t'] _.

(***********************************************************************)
(** position of the Hole in a context *)

Fixpoint pos_context (C : context) : position :=
  match C with
    | Hole => nil
    | @Cont _ _ i _ _ _ C _ => i :: pos_context C
  end.

Lemma subterm_fill_pos_context : forall c u,
  subterm_pos (fill c u) (pos_context c) = Some u.

Proof.
induction c; intros; simpl.
destruct u; auto.
case (lt_ge_dec i (arity f)); intro. 2: lia.
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
2: lia. rewrite (IHc u v). f_equal. apply args_eq.
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
exists x0. exists x1. apply subterm_pos_elim in H1. destruct H1. destruct a.
exists x3. exists x2. intuition. ded (replace_pos_elim H3). destruct X.
destruct a. rewrite H in H2. inversion H2. subst x4. hyp.
Qed.

(***********************************************************************)
(** position of a variables *)

Lemma in_vars_subterm : forall x t, In x (vars t) ->
  exists ps, subterm_pos t ps = Some (Var x).

Proof.
intros x t; pattern t; apply term_ind with (Q := fun n (ts : terms n) =>
  In x (vars_vec ts) -> exists i, exists h:i<n, exists ps,
    subterm_pos (Vnth ts h) ps = Some (Var x)); clear t.
intro y. simpl. intuition. subst. exists nil. refl.
intros f ts IH h. rewrite vars_fun in h. destruct (IH h). do 2 destruct H.
exists (x0::x2). simpl. case (lt_ge_dec x0 (arity f)); intro.
rewrite (lt_unique l x1). hyp. lia.
simpl. tauto.
intros t n ts ht hts. simpl vars_vec. rewrite in_app. intros [h|h].
destruct (ht h). exists 0. exists (Nat.lt_0_succ n). exists x0. simpl. hyp.
destruct (hts h). do 2 destruct H. exists (S x0). exists (NatCompat.lt_n_S x1).
exists x2. simpl. rewrite (lt_unique (NatCompat.lt_S_n (NatCompat.lt_n_S x1)) x1). hyp.
Qed.

End S.

Arguments subterm_pos_elim [Sig p t u] _.
Arguments in_vars_subterm [Sig x t] _.
Arguments subterm_pos_sub [Sig] _ [u p t] _.
