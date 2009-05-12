(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui & Wang Qian & Zhang Lianyi, 2009-05-11

non-termination from loops
*)

Set Implicit Arguments.

Require Import NatUtil.
Require Import ATrs.
Require Import ListUtil.
Require Import ListDec.
Require Import APosition.
Require Import LogicUtil.
Require Import AMatching.

Section S.

Variable Sig : Signature.

Notation term := (term Sig). Notation context := (context Sig).
Notation substitution := (substitution Sig).
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

Definition data := (position * rule)%type.

Definition rewrite (t : term) (d : data) : option term :=
  let (p,a) := d in let (l,r) := a in
    if mem (@beq_rule Sig) (mkRule l r) R then
      match subterm_pos t p with
        | None => None
        | Some u =>
          match matches l u with
            | None => None
            | Some s => replace_pos t p (sub s r)
          end
      end
      else None.

Lemma rewrite_correct : forall t d u, rewrite t d = Some u -> red R t u.

Proof.
intros t [p [l r]] u. unfold rewrite.
case_eq (mem (@beq_rule Sig) (mkRule l r) R). 2: discr.
gen H0. case_eq (subterm_pos t p). 2: discr.
gen H1. case_eq (matches l t0). rename t1 into s. 2: discr.
rewrite red_pos_ok. exists p. exists l. exists r. exists s. intuition.
rewrite mem_ok in H. hyp. apply beq_rule_ok.
ded (matches_correct H1). rewrite H3. hyp.
Qed.

Implicit Arguments rewrite_correct [t d u].

Fixpoint rewrites t (ds : list data) {struct ds} : option (list term) :=
  match ds with
    | nil => Some nil
    | d :: ds' =>
      match rewrite t d with
        | None => None
        | Some u =>
          match rewrites u ds' with
            | None => None
            | Some us => Some (u::us)
          end
      end
  end.

Lemma rewrites_correct : forall ds t us, rewrites t ds = Some us -> FS t us.

Proof.
induction ds; simpl; intros. inversion H. exact I.
gen H. case_eq (rewrite t a). 2: discr.
gen H0. case_eq (rewrites t0 ds). 2: discr.
inversion H1. simpl. ded (rewrite_correct H). intuition.
Qed.

Implicit Arguments rewrites_correct [ds t us].

Lemma FS_red : forall ts t, FS t ts -> forall i,
  i < length ts -> red R (nth i (t::ts) (Var 0)) (nth (S i) (t::ts) (Var 0)).

Proof.
induction ts; simpl; intros. absurd_arith. destruct H. destruct i. hyp.
ded (IHts _ H1 i (lt_S_n H0)). hyp.
Qed.

(***********************************************************************)
(** assumptions for non-termination *)

Section loop.

Variables (t : term) (ds : list data)
  (us : list term) (h1 : rewrites t ds = Some us).

Definition k := length us.

Definition nth i := nth i us (Var 0).

Definition last_term := nth (k-1).

Variables (h0 : k > 0).

Lemma FS_red' : forall i, i < k - 1 -> red R (nth i) (nth (S i)).

Proof.
intros. unfold nth.
change (red R (List.nth (S i) (t :: us) (Var 0))
  (List.nth (S (S i)) (t :: us) (Var 0))).
apply FS_red. eapply rewrites_correct. apply h1. unfold k in *. omega.
Qed.

Variables (p : position) (u : term) (h2 : subterm_pos last_term p = Some u)
  (s : substitution) (h3 : matches t u = Some s).

(***********************************************************************)
(** proof of non-termination *)

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
exists l. exists r. exists (AContext.comp c (subc s c0)). exists (comp s s0).
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
intro n. destruct (eucl_dev k h0 n). exact (iter g q (nth r)).
Defined.

Require Import RelUtil.
Require Import Wf_nat.

Lemma IS_f : IS (red R) f.

Proof.
intro n; pattern n; apply lt_wf_ind; clear n; intros. unfold f at -2 .
destruct (eucl_dev k h0 n); simpl. destruct (le_gt_dec (k-1) r).
(* r = k-1 *)
assert (r = k-1). omega. assert (S n = (S q)*k + 0). rewrite mult_succ_l.
omega. rewrite H1. unfold f. destruct (eucl_dev k h0 (S q * k + 0)).
destruct (eucl_div_unique h0 g1 e0). rewrite <- H3. rewrite <- H2. simpl.
apply red_iter_g. rewrite H0. fold last_term. rewrite last_term_g.
apply red_g. unfold nth.
change (red R (List.nth 0 (t :: us) (Var 0)) (List.nth 1 (t :: us) (Var 0))).
apply FS_red. apply (rewrites_correct h1). hyp.
(* r < k-1 *)
assert (S n = q*k + S r). omega. rewrite H0. unfold f.
destruct (eucl_dev k h0 (q * k + S r)). assert (k>S r). omega.
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

End loop.

(***********************************************************************)
(** boolean function testing non-termination *)

Definition is_loop t ds p :=
  match rewrites t ds with
    | None => false
    | Some us =>
      match us with
        | nil => false
        | _ =>
          let u := last us (Var 0) in
            match subterm_pos u p with
              | None => false
              | Some v =>
                match matches t v with
                  | None => false
                  | Some _ => true
                end
            end
      end
  end.

Lemma is_loop_correct : rules_preserv_vars R ->
  forall t ds p, is_loop t ds p = true -> ~WF (red R).

Proof.
intros HR t ds p. unfold is_loop. coq_case_eq (rewrites t ds). 2: discr.
destruct l. discr. set (us := t0::l). set (u := last us (Var 0)).
coq_case_eq (subterm_pos u p). 2: discr. intro v. case_eq (matches t v).
2: discr. eapply loop. apply H1. unfold k, us. simpl. omega.
unfold last_term, k, nth. rewrite <- last_nth. fold u. apply H0. apply H. hyp.
Qed.

End S.

(***********************************************************************)
(** tactics *)

Ltac loop t' ds' p' :=
  rewrite red_mod_empty;
  apply is_loop_correct with (t:=t') (ds:=ds') (p:=p');
    [rules_preserv_vars | vm_compute; refl].
