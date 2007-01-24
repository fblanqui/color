(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-01-27
- Sebastien Hinderer, 2004-02-10

substitutions
*)

(* $Id: ASubstitution.v,v 1.8 2007-01-24 11:52:35 blanqui Exp $ *)

Set Implicit Arguments.

Section S.

Require Export ASignature.

Variable Sig : Signature.

Require Export ATerm.

Notation term := (term Sig).
Notation terms := (vector term).

Notation "'args' f" := (terms (arity f)) (at level 70).

Notation Var := (@Var Sig).

(***********************************************************************)
(** definition of substitutions as interpretations in terms *)

Require Export AInterpretation.

Definition I0 := (mkInterpretation (Var 0) (@Fun Sig)).

Definition substitution := valuation I0.

Definition id x := Var x.

(***********************************************************************)
(** application of a substitution *)

Definition app := @term_int Sig I0.

Lemma app_fun : forall s f (v : args f),
  app s (Fun f v) = Fun f (Vmap (app s) v).

Proof.
intros. unfold app. rewrite term_int_fun. reflexivity.
Qed.

Lemma app_id : forall t, app id t = t.

Proof.
set (P := fun t => app id t = t). change (forall t, P t).
apply term_ind_forall; intros; unfold P. reflexivity.
rewrite app_fun. apply f_equal with (f := Fun f). apply Vmap_eq_id. assumption.
Qed.

Lemma fun_eq_app : forall f ts s u, Fun f ts = app s u ->
  {exists us, u = Fun f us} + {exists x, u = Var x}.

Proof.
intros f ts s u H.
destruct u.
right. exists n. reflexivity.
left. case (eq_symb_dec f f0).
intro E. rewrite E. exists v. reflexivity.
intro E. simpl in H. simplify_eq H. contradiction.
Qed.

(***********************************************************************)
(** composition *)

Definition comp (s1 s2 : substitution) x := app s1 (s2 x).

Lemma app_app : forall s1 s2 t, app s1 (app s2 t) = app (comp s1 s2) t.

Proof.
intros. set (P := fun t => app s1 (app s2 t) = app (comp s1 s2) t).
change (P t). apply term_ind_forall with (P := P); intros; unfold P.
reflexivity. repeat rewrite app_fun. apply f_equal with (f := Fun f).
rewrite Vmap_map. apply Vmap_eq. assumption.
Qed.

Lemma comp_assoc : forall (s1 s2 s3 : substitution) x,
  comp (comp s1 s2) s3 x = comp s1 (comp s2 s3) x.

Proof.
intros. unfold comp. rewrite app_app. refl.
Qed.

(***********************************************************************)
(** substitution lemma for interpretations *)

Section substitution_lemma.

Variable I : interpretation Sig.

Definition beta (xint : valuation I) (s : substitution) x :=
  term_int xint (s x).

Lemma substitutionLemma : forall xint s t,
  term_int xint (app s t) = term_int (beta xint s) t.

Proof.
intros xint s t. pattern t.
eapply term_ind with (Q := fun n (ts : terms n) =>
  Vmap (term_int xint) (Vmap (app s) ts) = Vmap (term_int (beta xint s)) ts).
intro x. simpl. refl.
intros f ts.
rewrite term_int_fun. rewrite app_fun. rewrite term_int_fun.
intro H. apply (f_equal (fint I f)). exact H.
simpl. refl.
intros. simpl. rewrite H. rewrite <- H0. refl.
Qed.

End substitution_lemma.

(***********************************************************************)
(** substitutions preserve variables *)

Section vars.

Variable s : substitution.

Fixpoint svars (l : variables) : variables :=
  match l with
    | nil => nil
    | x :: l' => vars (s x) ++ svars l'
  end.

Lemma in_svars_intro : forall x y l,
  In x (vars (s y)) -> In y l -> In x (svars l).

Proof.
induction l; simpl; intros. contradiction. destruct H0.
subst a. apply in_appl. exact H.
deduce (IHl H H0). apply in_appr. exact H1.
Qed.

Lemma in_svars_elim : forall x l,
  In x (svars l) -> exists y, In y l /\ In x (vars (s y)).

Proof.
induction l; simpl; intros. contradiction. deduce (in_app_or H). destruct H0.
exists a. auto. deduce (IHl H0). do 2 destruct H1. exists x0. auto.
Qed.

Implicit Arguments in_svars_elim [x l].

Lemma svars_app : forall l2 l1, svars (l1 ++ l2) = svars l1 ++ svars l2.

Proof.
induction l1; simpl; intros. refl. rewrite IHl1. rewrite app_ass. refl.
Qed.

Lemma incl_svars : forall l1 l2, incl l1 l2 -> incl (svars l1) (svars l2).

Proof.
intros. unfold incl. intros. deduce (in_svars_elim H0). do 2 destruct H1.
eapply in_svars_intro. apply H2. apply H. exact H1.
Qed.

Lemma vars_app : forall t, vars (app s t) = svars (vars t).

Proof.
apply term_ind with (Q := fun n (v : terms n) =>
  vars_vec (Vmap (app s) v) = svars (vars_vec v)).
simpl. intro. rewrite <- app_nil_end. refl.
intros. rewrite app_fun. repeat rewrite vars_fun. exact H.
simpl. refl.
intros. simpl. rewrite H. rewrite svars_app.
apply (f_equal (List.app (svars (vars t)))). exact H0.
Qed.

Lemma incl_vars_app : forall l r,
  incl (vars r) (vars l) -> incl (vars (app s r)) (vars (app s l)).

Proof.
intros. repeat rewrite vars_app. apply incl_svars. exact H.
Qed.

End vars.

(***********************************************************************)
(** domain of a substitution *)

Notation Inb_var := (Inb eq_nat_dec).

Definition dom_incl s l := forall x, Inb_var x l = false -> s x = Var x.

(***********************************************************************)
(** when two substitutions are equal on some domain *)

Require Export ListForall.

Definition sub_eq_dom (s1 s2 : substitution) :=
  lforall (fun x : variable => s1 x = s2 x).

Lemma sub_eq_dom_incl : forall s1 s2 l1 l2,
  sub_eq_dom s1 s2 l2 -> incl l1 l2 -> sub_eq_dom s1 s2 l1.

Proof.
intros. unfold sub_eq_dom. eapply lforall_incl. apply H0. assumption.
Qed.

Lemma sub_eq_dom_incl_app : forall s1 s2 l, sub_eq_dom s1 s2 l
  -> forall t, incl (vars t) l -> app s1 t = app s2 t.

Proof.
intros until t. unfold sub_eq_dom in H.
set (P := fun t => incl (vars t) l -> app s1 t = app s2 t).
set (Q := fun n (ts : terms n) =>
  incl (vars_vec ts) l -> Vmap (app s1) ts = Vmap (app s2) ts).
apply (term_ind P Q).
(* var *)
unfold P. simpl. intros. generalize (incl_cons_in H0). intro.
pattern x. eapply lforall_in. apply H. assumption.
(* fun *)
unfold P. intros. do 2 rewrite app_fun. apply (f_equal (Fun f)).
apply H0. rewrite vars_fun in H1. assumption.
(* nil *)
unfold Q. intro. reflexivity.
(* cons *)
intros. unfold Q. simpl. intro. apply Vcons_eq. apply H0.
eapply incl_appr_incl. apply H2. apply H1. eapply incl_appl_incl. apply H2.
Qed.

Lemma sub_eq_vars_app : forall s1 s2 t, sub_eq_dom s1 s2 (vars t)
  -> app s1 t = app s2 t.

Proof.
intros. eapply sub_eq_dom_incl_app. apply H. apply List.incl_refl.
Qed.

Lemma sub_eq_dom_app : forall s1 s2 t,
  sub_eq_dom s1 s2 (vars t) -> app s1 t = app s2 t.

Proof.
intros until t.
set (P := fun t => sub_eq_dom s1 s2 (vars t) -> app s1 t = app s2 t).
set (Q := fun n (ts : terms n) => sub_eq_dom s1 s2 (vars_vec ts)
  -> Vmap (app s1) ts = Vmap (app s2) ts). change (P t). apply (term_ind P Q).
(* var *)
unfold P. simpl. intuition.
(* fun *)
intros. unfold P. rewrite vars_fun. intro. do 2 rewrite app_fun.
apply (f_equal (Fun f)). apply H. assumption.
(* nil *)
unfold Q. simpl. auto.
(* cons *)
intros. unfold Q. simpl. intro. apply Vcons_eq. apply H.
eapply sub_eq_dom_incl. apply H1. apply incl_appl. apply List.incl_refl.
apply H0. eapply sub_eq_dom_incl. apply H1. apply incl_appr.
apply List.incl_refl.
Qed.

(***********************************************************************)
(** restriction of a substitution *)

Definition restrict s l x := if Inb_var x l then s x else Var x.

Lemma restrict_var : forall s l x, In x l -> restrict s l x = s x.

Proof.
intros. unfold restrict. assert (Inb_var x l = true).
apply Inb_intro. assumption. rewrite H0. reflexivity.
Qed.

Lemma dom_incl_restrict : forall s l, dom_incl (restrict s l) l.

Proof.
unfold dom_incl, restrict. induction l; simpl. auto.
intro. case (eq_nat_dec x a). intros. discriminate.
intros. rewrite H. reflexivity.
Qed.

Lemma sub_eq_restrict : forall s l, sub_eq_dom (restrict s l) s l.

Proof.
unfold sub_eq_dom. induction l; simpl. exact I. split.
unfold restrict. simpl. case (eq_nat_dec a a). auto.
intro. absurd (a = a); auto. apply lforall_intro. intros.
unfold restrict. simpl. case (eq_nat_dec x a). intro. reflexivity.
assert (Inb_var x l = true). apply Inb_intro. assumption. intro.
pattern x. eapply lforall_in. apply IHl. assumption.
Qed.

Lemma app_restrict : forall s t, app s t = app (restrict s (vars t)) t.

Proof.
intros. apply sym_eq. apply sub_eq_dom_app. apply sub_eq_restrict.
Qed.

Lemma app_restrict_incl : forall s (l r : term),
  incl (vars r) (vars l) -> app s r = app (restrict s (vars l)) r.

Proof.
intros. rewrite app_restrict. apply sub_eq_dom_app. unfold sub_eq_dom.
apply lforall_intro. intros. unfold restrict.
assert (Inb_var x (vars r) = true). apply Inb_intro. assumption.
assert (Inb_var x (vars l) = true). apply Inb_intro. apply H. assumption.
rewrite H1. rewrite H2. reflexivity.
Qed.

(***********************************************************************)
(** substitution on contexts *)

Require Export AContext.

Notation context := (context Sig).

Fixpoint appc (s : substitution) (c : context) {struct c} : context :=
  match c with
    | Hole => Hole
    | Cont f _ _ H v1 c' v2 =>
      Cont f H (Vmap (app s) v1) (appc s c') (Vmap (app s) v2)
  end.

Lemma app_fill : forall s u C, app s (fill C u) = fill (appc s C) (app s u).

Proof.
induction C; intros. refl. simpl appc. simpl fill. rewrite app_fun.
apply (f_equal (Fun f)). rewrite Vmap_cast. rewrite Vmap_app. simpl Vmap.
rewrite IHC. refl.
Qed.

Lemma subterm_app : forall u t s,
  subterm_eq u t -> subterm_eq (app s u) (app s t).

Proof.
unfold subterm_eq. intros. destruct H as [C]. subst t. exists (appc s C).
apply app_fill.
Qed.

(***********************************************************************)
(** function generating the sequence of variables x0, .., x0+n-1 *)

Fixpoint fresh (x0 n : nat) {struct n} : terms n :=
  match n as n return terms n with
    | 0 => Vnil
    | S n' => Vcons (Var x0) (fresh (S x0) n')
  end.

Lemma Vbreak_fresh : forall n1 n2 x0,
  fresh x0 (n1+n2) = Vapp (fresh x0 n1) (fresh (x0+n1) n2).

Proof.
induction n1; simpl; intros. rewrite plus_0_r. reflexivity.
apply Vcons_eq_tail. rewrite IHn1.
assert (S x0 + n1 = x0 + S n1). omega. rewrite H. reflexivity.
Qed.

Lemma fresh_tail : forall x0 n, fresh (S x0) n = Vtail (fresh x0 (S n)).

Proof.
induction n; simpl; intros; reflexivity.
Qed.

Lemma Vnth_fresh : forall n i (h : i < n) x0, Vnth (fresh x0 n) h = Var (x0+i).

Proof.
induction n; simpl. intros. absurd (i<0); omega. intro. destruct i. auto.
intros. assert (x0+S i=(S x0)+i). omega. rewrite H. apply IHn.
Qed.

(***********************************************************************)
(** given a variable [x0] and a vector [v] of [n] terms, [fsub x0 n v]
is the substitution {x0 -> v1, .., x0+n-1 -> vn} *)

Definition fsub x0 n (ts : terms n) x :=
  match le_lt_dec x x0 with
    | left _ => Var x (* x <= x0 *)
    | right h1 => (* x0 < x *)
      match le_lt_dec x (x0+n) with
	| left h2 => Vnth ts (lt_pm h1 h2) (* x <= x0+n *)
	| _ => Var x (* x0+n < x *)
      end
  end.

Lemma fsub_inf : forall x0 n (ts : terms n) x, x <= x0 -> fsub x0 ts x = Var x.

Proof.
intros. unfold fsub. case (le_lt_dec x x0). auto. intro. absurd (n<x); omega.
Qed.

Lemma fsub_sup : forall x0 n (ts : terms n) x, x > x0+n -> fsub x0 ts x = Var x.

Proof.
intros. unfold fsub. case (le_lt_dec x x0). auto. intro.
case (le_lt_dec x (x0+n)). intro. absurd (x>x0+n); omega. auto.
Qed.

Lemma fsub_nth : forall x0 n (ts : terms n) x (h1 : x0 < x) (h2 : x <= x0+n),
  fsub x0 ts x = Vnth ts (lt_pm h1 h2).

Proof.
intros. unfold fsub. case (le_lt_dec x x0). intro. absurd (n<x); omega.
case (le_lt_dec x (x0+n)); intros. apply Vnth_eq. reflexivity.
absurd (n<x); omega.
Qed.

Lemma fsub_cons : forall x0 t n (ts : terms n) x,
 x = x0+1 -> fsub x0 (Vcons t ts) x = t.

Proof.
intros. subst x. unfold fsub. case (le_lt_dec (x0+1) x0); intros.
absurd (x0+1<=x0); omega. case (le_lt_dec (x0+1) (x0+S n)); intros.
rewrite Vnth_head. reflexivity. omega. absurd (x0+S n<x0+1); omega.
Qed.

Lemma fsub_cons_rec : forall x0 t n (ts : terms n) x k,
  x = x0+2+k -> fsub x0 (Vcons t ts) x = fsub (x0+1) ts x.

Proof.
intros. subst x. unfold fsub.
case (le_lt_dec (x0+2+k) x0). intro. absurd (x0+2+k <= x0); omega.
case (le_lt_dec (x0+2+k) (x0+1)). intro. absurd (x0+2+k <= x0+1); omega.
case (le_lt_dec (x0+2+k) (x0+S n)); case (le_lt_dec (x0+2+k) (x0+1+n)); intros.
set (H1 := lt_pm l2 l0). set (H2 := lt_pm l1 l).
assert (H1' : S k < S n). rewrite (misc1 x0 k). assumption.
assert (Vnth (Vcons t ts) H1 = Vnth (Vcons t ts) H1').
apply Vnth_eq. rewrite (misc1 x0 k). reflexivity. rewrite H.
assert (H2' : k < n). rewrite (misc2 x0 k). assumption.
assert (Vnth ts H2 = Vnth ts H2').
apply Vnth_eq. apply sym_eq. apply (misc2 x0 k). rewrite H0.
apply Vnth_cons.
absurd (x0+1+n < x0+2+k); omega. absurd (x0+1+n < x0+2+k); omega.
reflexivity.
Qed.

Lemma fsub_cons_rec0 : forall x0 t n (ts : terms n) x,
 x = x0+2 -> fsub x0 (Vcons t ts) x = fsub (x0+1) ts x.

Proof.
intros. eapply fsub_cons_rec with (k := 0). omega.
Qed.

Lemma fsub_nil : forall x0 x, fsub x0 Vnil x = Var x.

Proof.
intros. unfold fsub. case (le_lt_dec x x0). auto.
case (le_lt_dec x (x0+0)); intros. absurd (x0<x); omega. reflexivity.
Qed.

Lemma app_fsub_inf : forall n (ts : terms n) m t,
  maxvar t <= m -> app (fsub m ts) t = t.

Proof.
intros n ts m. set (P := fun t => maxvar t <= m -> app (fsub m ts) t = t).
change (forall t, P t). apply term_ind_forall.
(* var *)
unfold P, fsub. simpl. intros. case (le_lt_dec v m). auto.
intro. case (le_lt_dec v (m+n)). intro. absurd (v <= m); omega. auto.
(* fun *)
intros. unfold P. intro. rewrite app_fun. apply f_equal with (f := Fun f).
apply Vmap_eq_id. eapply Vforall_imp. apply H. intros. apply H2.
eapply maxvar_le_arg with (f := f). apply H0. assumption.
Qed.

Lemma Vmap_fsub_fresh : forall x0 n (ts : terms n),
  Vmap (app (fsub x0 ts)) (fresh (S x0) n) = ts.

Proof.
intros. apply Vmap_eq_nth. intros. rewrite Vnth_fresh. simpl.
set (x := S(x0+i)). assert (h1 : x0<x). unfold x. omega.
assert (h2 : x<=x0+n). unfold x. omega.
assert (fsub x0 ts x = Vnth ts (lt_pm h1 h2)). apply fsub_nth.
rewrite H. apply Vnth_eq. unfold x. omega.
Qed.

Fixpoint freshl (x0 n : nat) {struct n} : list variable :=
  match n with
    | 0 => nil
    | S n' => x0 :: freshl (S x0) n'
  end.

Lemma in_freshl : forall x n x0,
  Inb_var x (freshl x0 n) = false -> x < x0 \/ x >= x0 + n.

Proof.
induction n; simpl. intros. omega.
intro. case (eq_nat_dec x x0). intros. discriminate.
intros. deduce (IHn (S x0) H). omega.
Qed.

Implicit Arguments in_freshl [x n x0].

Lemma fsub_dom : forall x0 n (ts : terms n),
  dom_incl (fsub x0 ts) (freshl (x0+1) n).

Proof.
induction ts; simpl; intros; unfold dom_incl; simpl.
intros. apply fsub_nil.
intro. case (eq_nat_dec x (x0+1)). intros. discriminate.
intros. deduce (in_freshl H). destruct H0.
apply fsub_inf. omega. apply fsub_sup. omega.
Qed.

End S.

Implicit Arguments fun_eq_app [Sig f ts s u].
Implicit Arguments lt_pm [n k x].