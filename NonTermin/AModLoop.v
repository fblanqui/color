(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-05-20

definition and correctness proof of a boolean function checking that
there is a loop in a relative TRS
*)

Set Implicit Arguments.

From Stdlib Require Import Euclid Wf_nat.
From CoLoR Require Import ATrs LogicUtil ALoop ListUtil RelUtil NatUtil
     APosition AMatching ARelation.

Section S.

  Variable Sig : Signature.

  Notation term := (term Sig). Notation data := (data Sig).

  Variable E R : rules Sig.

(***********************************************************************)
(** predicates saying that [t::us] is in a sequence of rewriting steps *)

  Fixpoint mod_FS t us :=
    match us with
      | nil => True
      | u :: us' => red_mod E R t u /\ mod_FS u us'
    end.

  Definition mod_terms_of_reduc : forall t, {us| mod_FS t us} -> list term.

  Proof.
    intros t x. destruct x. exact x.
  Defined.

  Arguments mod_terms_of_reduc [t] _.

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
    intros t [ds d] u. unfold mod_rewrite.
    case_eq (rewrites E t ds); intros. 2: discr.
    ded (rewrites_correct H). exists (last l t). split. apply FS_rtc. hyp.
    apply rewrite_correct with (d:=d). hyp.
  Qed.

  Arguments mod_rewrite_correct [t dm u] _.

  Fixpoint mod_rewrites t (mds : list mod_data) : option (list term) :=
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
    revert H. case_eq (mod_rewrite t a); intros. 2: discr.
    revert H0. case_eq (mod_rewrites t0 ds); intros. 2: discr.
    inversion H1. simpl. ded (mod_rewrite_correct H). intuition.
  Qed.

  Arguments mod_rewrites_correct [ds t us] _.

  Notation default := (Var 0).

  Lemma mod_FS_red : forall ts t, mod_FS t ts -> forall i, i < length ts ->
    red_mod E R (nth i (t::ts) default) (nth (S i) (t::ts) default).

  Proof.
    induction ts; simpl; intros. lia. destruct H. destruct i. hyp.
    ded (IHts _ H1 i (NatCompat.lt_S_n H0)). hyp.
  Qed.

(***********************************************************************)
(** hyps for non-termination *)

  Section loop.

    Variables (t : term) (mds : list mod_data)
      (us : list term) (h1 : mod_rewrites t mds = Some us).

    Definition k := length us.

    Variable h0 : k > 0.

    Definition nth i := nth i us default.

    Definition last_term := nth (k-1).

    Lemma red_mod_nth : forall i, i < k-1 -> red_mod E R (nth i) (nth (S i)).

    Proof.
      intros. unfold nth.
      change (red_mod E R (List.nth (S i) (t :: us) default)
        (List.nth (S (S i)) (t :: us) default)).
      apply mod_FS_red. eapply mod_rewrites_correct. apply h1. unfold k in *.
      lia.
    Qed.

    Variables (ds : list data) (us' : list term)
      (h1' : rewrites E last_term ds = Some us').

    Definition last_term' := last us' last_term.

    Variables (p : position) (u : term) (h2 : subterm_pos last_term' p = Some u)
      (s : substitution Sig) (h3 : matches t u = Some s).

(***********************************************************************)
(** proof of non-termination *)

    Definition c : context Sig.

    Proof.
      destruct (subterm_pos_elim h2). exact x.
    Defined.

    Definition g t := fill c (sub s t).

    Lemma last_term'_g : last_term' = g t.

    Proof.
      unfold g, c. destruct (subterm_pos_elim h2). destruct a. rewrite H0.
      ded (matches_correct h3). subst u. refl.
    Qed.

    Lemma red_last_term_g : red E # last_term (g t).

    Proof.
      rewrite <- last_term'_g. unfold last_term'. apply FS_rtc.
      apply (rewrites_correct h1').
    Qed.

    Lemma red_mod_g : forall a b, red_mod E R a b -> red_mod E R (g a) (g b).

    Proof.
      intros. apply red_mod_fill. apply red_mod_sub. hyp.
    Qed.

    Definition seq : nat -> term.

    Proof.
      intro n. destruct (eucl_dev k h0 n). exact (iter (nth r) g q).
    Defined.

    Lemma IS_seq : IS (red_mod E R) seq.

    Proof.
      intro n; pattern n; apply lt_wf_ind; clear n; intros. unfold seq at -2 .
      destruct (eucl_dev k h0 n); simpl. destruct (le_gt_dec (k-1) r).
      (* r = k-1 *)
      assert (r = k-1). lia. assert (S n = (S q)*k + 0). rewrite Nat.mul_succ_l.
      lia. rewrite H1. unfold seq. destruct (eucl_dev k h0 (S q * k + 0)).
      destruct (eucl_div_unique h0 g1 e0). rewrite <- H3, <- H2. simpl.
      rewrite <- iter_com. apply red_iter. apply red_mod_g.
      rewrite H0. fold last_term.
      cut (red_mod E R (g t) (g (nth 0))). intro. destruct H4. exists x.
      intuition. apply rt_trans with (g t). apply red_last_term_g. hyp.
      apply red_mod_g. unfold nth.
      change (red_mod E R (List.nth 0 (t :: us) default)
        (List.nth 1 (t :: us) default)).
      apply mod_FS_red. apply (mod_rewrites_correct h1). hyp.
      (* r < k-1 *)
      assert (S n = q*k + S r). lia. rewrite H0. unfold seq.
      destruct (eucl_dev k h0 (q * k + S r)). assert (k>S r). lia.
      destruct (eucl_div_unique H1 g2 e0). rewrite <- H3, <- H2.
      apply red_iter. apply red_mod_g. apply red_mod_nth. lia.
    Qed.

    Lemma loop : EIS (red_mod E R).

    Proof.
      exists seq. apply IS_seq.
    Qed.

  End loop.

(***********************************************************************)
(** boolean function testing non-termination *)

  Definition is_mod_loop t mds ds p :=
    match mod_rewrites t mds with
      | None => false
      | Some us =>
        match us with
          | nil => false
          | _ =>
            let u := last us default in
              match rewrites E u ds with
                | None => false
                | Some us' =>
                  let u' := last us' u in
                    match subterm_pos u' p with
                      | None => false
                      | Some v =>
                        match matches t v with
                          | None => false
                          | Some _ => true
                        end
                    end
              end
        end
    end.

  Lemma is_mod_loop_correct : forall t mds ds p,
    is_mod_loop t mds ds p = true -> EIS (red_mod E R).

  Proof.
    intros t mds ds p. unfold is_mod_loop. case_eq (mod_rewrites t mds).
    2: discr. destruct l. discr. set (us := t0::l). set (u := last us default).
    case_eq (rewrites E u ds). 2: discr. intro us'. set (u' := last us' u).
    case_eq (subterm_pos u' p). 2: discr. intro v.
    case_eq (matches t v); intros.
    2: discr. assert (h0 : k us > 0). unfold k, us. simpl. lia.
    assert (h : u = last_term us). unfold last_term, k, nth.
    rewrite <- last_nth.
    refl. unfold u' in H0. rewrite h in H0. exists (seq us h0 us' p H0 t1).
    eapply IS_seq. apply H2. rewrite h in H1. apply H1. hyp.
  Qed.

End S.

(***********************************************************************)
(** tactics *)

Ltac loop t' mds' ds' p' :=
  apply is_mod_loop_correct with (t:=t') (mds:=mds') (ds:=ds') (p:=p');
    (check_eq || fail 10 "not a loop").
