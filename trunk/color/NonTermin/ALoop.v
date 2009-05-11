(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui & Wang Qian & Zhang Lianyi, 2009-05-11

non-termination from loops
*)

Set Implicit Arguments.

Require Import NatUtil.
Require Import ATrs.
Require Import List.
Require Import ListDec.
Require Import APosition.
Require Import LogicUtil.
Require Import AMatching.

Section S.

Variable Sig : Signature.

Notation term := (term Sig). Notation context := (context Sig).
Notation rule := (rule Sig). Notation rules := (list rule).

Variable R : rules.

(***********************************************************************)
(** predicates saying that [t::us] is in a sequence of rewriting steps *)

Fixpoint FS t us {struct us} :=
  match us with
    | nil => True
    | u :: us' => red R t u /\ FS u us'
  end.

Definition terms_of_reduc : forall t, {us| FS t us} -> list term.

Proof.
intros t x. destruct x. exact x.
Defined.

Implicit Arguments terms_of_reduc [t].

Definition proof_of_reduc :
  forall t, forall x : {us| FS t us}, FS t (terms_of_reduc x).

Proof.
intros t x. destruct x. exact f.
Defined.

(***********************************************************************)
(** data necessary for a sequence of rewrite steps *)

Notation data := (position * rule)%type.

Definition rewrite (d : data) t : option {u | red R t u}.

Proof.
intros [p [l r]] t.
case_eq (mem (@beq_rule Sig) (mkRule l r) R); [idtac|exact None].
case_eq (subterm_pos t p); [idtac|exact None]. rename t0 into tp.
case_eq (matches l tp); [idtac|exact None]. rename t0 into s.
case_eq (replace_pos t p (sub s r)). apply Some. exists  t0.
rewrite red_pos_ok. exists p. exists l. exists r. exists s.
intuition. rewrite mem_ok in H. hyp. apply beq_rule_ok. rewrite H0.
ded (matches_correct H1). rewrite H3. refl.
ded (subterm_pos_replace_neq_None _ (sub s r) _ H0). rewrite H2 in H3. irrefl.
Defined.

Definition rewrites (ds : list data) t : option {us| FS t us}.

Proof.
induction 1.
(* nil *)
intro t. apply Some. exists nil. exact I.
(* cons *)
intro t. destruct (rewrite a t); [idtac|exact None].
destruct s. destruct (IHds x); [idtac|exact None]. destruct s.
apply Some. exists (x :: x0). simpl. intuition.
Defined.

Lemma FS_red : forall ts t, FS t ts -> forall i,
  i < length ts -> red R (nth i (t::ts) (Var 0)) (nth (S i) (t::ts) (Var 0)).

Proof.
induction ts; simpl; intros. absurd_arith. destruct H. destruct i. hyp.
ded (IHts _ H1 i (lt_S_n H0)). hyp.
Qed.

(***********************************************************************)
(** assumptions for non-termination *)

Variables (t : term) (r : {us|FS t us}).

Definition list_terms := terms_of_reduc r.

Definition k := length list_terms.

Definition nth i := nth i list_terms (Var 0).

Definition last_term := nth (k-1).

Variables (h0 : k > 0).

Lemma FS_red' : forall i, i < k - 1 -> red R (nth i) (nth (S i)).

Proof.
intros. unfold nth, list_terms.
change (red R (List.nth (S i) (t :: terms_of_reduc r) (Var 0))
  (List.nth (S (S i)) (t :: terms_of_reduc r) (Var 0))).
apply FS_red. destruct r. hyp. unfold k, list_terms in *. omega.
Qed.

Variables (ds : list data) (h1 : rewrites ds t = Some r)
  (p : position) (u : term) (h2 : subterm_pos last_term p = Some u)
  (s : substitution Sig) (h3 : matches t u = Some s).
Definition c : context.

Proof.
destruct (subterm_pos_elim h2). exact x.
Defined.

Definition g t := fill c (sub s t).

Lemma last_term_g : last_term = g t.

Proof.
unfold g, c. destruct (subterm_pos_elim h2). destruct a.
rewrite H0. ded (matches_correct h3). subst u. refl.
Qed.

Lemma red_g : forall a b, red R a b -> red R (g a) (g b).

Proof.
intros. redtac. unfold red. unfold g.
exists l. exists r0. exists (AContext.comp c (subc s c0)). exists (comp s s0).
subst. repeat rewrite sub_fill. repeat rewrite fill_comp.
repeat rewrite sub_sub. intuition.
Qed.

Lemma red_iter_g : forall a b, red R a b ->
  forall i, red R (iter g i a) (iter g i b).

Proof.
induction i; simpl; intros. hyp. repeat rewrite iter_com.
destruct i. simpl. apply red_g. hyp. apply red_g. apply IHi.
Qed.

Require Import Euclid.

Definition f (n : nat) : term.

Proof.
intro n. destruct (eucl_dev k h0 n). exact (iter g q (nth r0)).
Defined.

Require Import RelUtil.
Require Import Wf_nat.

Lemma IS_f : IS (red R) f.

Proof.
intro n; pattern n; apply lt_wf_ind; clear n; intros. unfold f at -2 .
destruct (eucl_dev k h0 n); simpl. destruct (le_gt_dec (k-1) r0).
(* r0 = k-1 *)
assert (r0 = k-1). omega. assert (S n = (S q)*k + 0). rewrite mult_succ_l.
omega. rewrite H1. unfold f. destruct (eucl_dev k h0 (S q * k + 0)).
destruct (eucl_div_unique h0 g1 e0). rewrite <- H3. rewrite <- H2. simpl.
apply red_iter_g. rewrite H0. fold last_term. rewrite last_term_g.
apply red_g. unfold nth, list_terms.
change (red R (List.nth 0 (t :: terms_of_reduc r) (Var 0))
  (List.nth 1 (t :: terms_of_reduc r) (Var 0))).
apply FS_red. destruct r. hyp. hyp.
(* r0 < k-1 *)
assert (S n = q*k + S r0). omega. rewrite H0. unfold f.
destruct (eucl_dev k h0 (q * k + S r0)). assert (k>S r0). omega.
destruct (eucl_div_unique H1 g2 e0). rewrite <- H3. rewrite <- H2.
apply red_iter_g. apply FS_red'. omega.
Qed.

Require Import IS_NotSN.
Require Import SN.
Require Import AReduct.

Variable (h5 : rules_preserv_vars R).

Lemma loop : ~WF (red R).

Proof.
unfold not. intro. eapply WF_notIS. apply fin_branch. apply h5. hyp.
apply IS_f.
Qed.

End S.
