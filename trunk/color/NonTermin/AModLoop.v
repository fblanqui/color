(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-05-20

definition and correctness proof of a boolean function checking that
there is a loop in a relative TRS
*)

Set Implicit Arguments.

Require Import ATrs.
Require Import LogicUtil.
Require Import ALoop.
Require Import ListUtil.

Section S.

Variable Sig : Signature.

Notation term := (term Sig). Notation context := (context Sig).
Notation substitution := (substitution Sig). Notation data := (data Sig).
Notation rule := (rule Sig). Notation rules := (list rule).

Variable E R : rules.

(***********************************************************************)
(** predicates saying that [t::us] is in a sequence of rewriting steps *)

Fixpoint mod_FS t us {struct us} :=
  match us with
    | nil => True
    | u :: us' => red_mod E R t u /\ mod_FS u us'
  end.

Definition mod_terms_of_reduc : forall t, {us| mod_FS t us} -> list term.

Proof.
intros t x. destruct x. exact x.
Defined.

Implicit Arguments mod_terms_of_reduc [t].

Definition mod_proof_of_reduc :
  forall t, forall x : {us| mod_FS t us}, mod_FS t (mod_terms_of_reduc x).

Proof.
intros t x. destruct x. exact m.
Defined.

(***********************************************************************)
(** data necessary for a sequence of red_mod steps *)

Definition mod_data := (list data * data)%type.

Definition mod_rewrite (t : term) (dm : mod_data) : option term :=
  let (ds,d) := dm in
    match rewrites E t ds with
      | None => None
      | Some ts => rewrite R (last ts t) d
    end.

Lemma mod_rewrite_correct : forall t dm u,
  mod_rewrite t dm = Some u -> red_mod E R t u.

Proof.
intros t [ds d] u. unfold mod_rewrite. case_eq (rewrites E t ds). 2: discr.
ded (rewrites_correct H). ded (rewrite_correct H0). exists (last l t); split.
apply FS_rtc. hyp. hyp.
Qed.

Implicit Arguments mod_rewrite_correct [t dm u].

Fixpoint mod_rewrites t (mds : list mod_data) {struct mds}
  : option (list term) :=
  match mds with
    | nil => Some nil
    | md :: mds' =>
      match mod_rewrite t md with
        | None => None
        | Some u =>
          match mod_rewrites u mds' with
            | None => None
            | Some us => Some (u::us)
          end
      end
  end.

Lemma mod_rewrites_correct : forall ds t us,
  mod_rewrites t ds = Some us -> mod_FS t us.

Proof.
induction ds; simpl; intros. inversion H. exact I.
gen H. case_eq (mod_rewrite t a). 2: discr.
gen H0. case_eq (mod_rewrites t0 ds). 2: discr.
inversion H1. simpl. ded (mod_rewrite_correct H). intuition.
Qed.

Implicit Arguments mod_rewrites_correct [ds t us].

Require Import NatUtil.

Lemma mod_FS_red : forall ts t, mod_FS t ts -> forall i, i < length ts ->
  red_mod E R (nth i (t::ts) (Var 0)) (nth (S i) (t::ts) (Var 0)).

Proof.
induction ts; simpl; intros. absurd_arith. destruct H. destruct i. hyp.
ded (IHts _ H1 i (lt_S_n H0)). hyp.
Qed.

(***********************************************************************)
(** assumptions for non-termination *)

Section loop.

Variables (t : term) (ds : list mod_data)
  (us : list term) (h1 : mod_rewrites t ds = Some us).

Definition k := length us.

Definition nth i := nth i us (Var 0).

Definition last_term := nth (k-1).

Variables (h0 : k > 0).

Lemma FS_red_mod' : forall i, i < k - 1 -> red_mod E R (nth i) (nth (S i)).

Proof.
intros. unfold nth.
change (red_mod E R (List.nth (S i) (t :: us) (Var 0))
  (List.nth (S (S i)) (t :: us) (Var 0))).
apply mod_FS_red. eapply mod_rewrites_correct. apply h1. unfold k in *. omega.
Qed.

Require Import APosition.
Require Import AMatching.

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

Lemma red_mod_g : forall a b, red_mod E R a b -> red_mod E R (g a) (g b).

Proof.
intros. unfold g. apply red_mod_fill. apply red_mod_sub. hyp.
Qed.

Lemma red_mod_iter_g : forall a b, red_mod E R a b ->
  forall i, red_mod E R (iter g i a) (iter g i b).

Proof.
induction i; simpl; intros. hyp. repeat rewrite iter_com.
destruct i. simpl. apply red_mod_g. hyp. apply red_mod_g. apply IHi.
Qed.

Require Import Euclid.

Definition seq (n : nat) : term.

Proof.
intro n. destruct (eucl_dev k h0 n). exact (iter g q (nth r)).
Defined.

Require Import RelUtil.
Require Import Wf_nat.

Lemma IS_seq : IS (red_mod E R) seq.

Proof.
intro n; pattern n; apply lt_wf_ind; clear n; intros. unfold seq at -2 .
destruct (eucl_dev k h0 n); simpl. destruct (le_gt_dec (k-1) r).
(* r = k-1 *)
assert (r = k-1). omega. assert (S n = (S q)*k + 0). rewrite mult_succ_l.
omega. rewrite H1. unfold seq. destruct (eucl_dev k h0 (S q * k + 0)).
destruct (eucl_div_unique h0 g1 e0). rewrite <- H3. rewrite <- H2. simpl.
apply red_mod_iter_g. rewrite H0. fold last_term. rewrite last_term_g.
apply red_mod_g. unfold nth.
change (red_mod E R (List.nth 0 (t :: us) (Var 0))
  (List.nth 1 (t :: us) (Var 0))).
apply mod_FS_red. apply (mod_rewrites_correct h1). hyp.
(* r < k-1 *)
assert (S n = q*k + S r). omega. rewrite H0. unfold seq.
destruct (eucl_dev k h0 (q * k + S r)). assert (k>S r). omega.
destruct (eucl_div_unique H1 g2 e0). rewrite <- H3. rewrite <- H2.
apply red_mod_iter_g. apply FS_red_mod'. omega.
Qed.

Lemma loop : non_terminating (red_mod E R).

Proof.
exists seq. apply IS_seq.
Qed.

End loop.

(***********************************************************************)
(** boolean function testing non-termination *)

Definition is_mod_loop t mds p :=
  match mod_rewrites t mds with
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

Lemma is_mod_loop_correct : forall t ds p,
  is_mod_loop t ds p = true -> non_terminating (red_mod E R).

Proof.
intros t mds p. unfold is_mod_loop. coq_case_eq (mod_rewrites t mds). 2: discr.
destruct l. discr. set (us := t0::l). set (u := last us (Var 0)).
coq_case_eq (subterm_pos u p). 2: discr. intro v. case_eq (matches t v).
2: discr. assert (h0 : k us > 0). unfold k, us. simpl. omega.
assert (h : u = last_term us). unfold last_term, k, nth. rewrite <- last_nth.
refl. rewrite h in H0. exists (seq us h0 p H0 t1). eapply IS_seq. apply H1.
hyp.
Qed.

End S.

(***********************************************************************)
(** tactics *)

Ltac check_mod_loop t' ds' p' :=
  apply is_mod_loop_correct with (t:=t') (ds:=ds') (p:=p'); vm_compute; refl.

Ltac loop t' ds' p' :=
  match goal with
    | |- non_terminating (red _) => check_loop t' ds' p'
    | |- non_terminating (red_mod ?E _) =>
      (remove_relative_rules E; check_loop t' ds' p')
      || check_mod_loop t' ds' p'
  end.
