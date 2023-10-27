(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui & Wang Qian & Zhang Lianyi, 2009-05-11

definition and correctness proof of a boolean function checking that
there is a loop in a TRS
*)

Set Implicit Arguments.

From Coq Require Import Euclid Wf_nat.
From CoLoR Require Import LogicUtil ATrs ListUtil RelUtil AMatching ListDec
     APosition NatUtil.

Section S.

  Variable Sig : Signature.

  Notation term := (term Sig). Notation beq_rule := (@beq_rule Sig).

  Variable R : rules Sig.

(***********************************************************************)
(** predicates saying that [t::us] is in a sequence of rewriting steps *)

  Fixpoint FS t us :=
    match us with
      | nil => True
      | u :: us' => red R t u /\ FS u us'
    end.

  Definition terms_of_reduc : forall t, {us| FS t us} -> list term.

  Proof.
    intros t x. destruct x. exact x.
  Defined.

  Arguments terms_of_reduc [t] _.

  Definition proof_of_reduc :
    forall t, forall x : {us| FS t us}, FS t (terms_of_reduc x).

  Proof.
    intros t x. destruct x. exact f.
  Defined.

  Lemma FS_rtc : forall us t, FS t us -> red R # t (last us t).

  Proof.
    induction us. simpl. intros. apply rt_refl. simpl FS. intuition.
    apply rt_trans with a. apply rt_step. hyp. simpl. destruct us.
    apply rt_refl. rewrite last_default with (d2:=a). apply IHus. hyp. discr.
  Qed.

(***********************************************************************)
(** data necessary for a sequence of rewrite steps *)

  Definition data := (position * rule Sig)%type.

  Definition rewrite (t : term) (d : data) : option term :=
    let (p,a) := d in let (l,r) := a in
      if mem beq_rule (mkRule l r) R then
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
    case_eq (mem beq_rule (mkRule l r) R); intros. 2: discr.
    revert H0. case_eq (subterm_pos t p); intros. 2: discr.
    revert H1. case_eq (matches l t0); intros. rename t1 into s. 2: discr.
    rewrite red_pos_ok. ex p l r s. split_all.
    rewrite mem_ok in H. hyp. apply beq_rule_ok.
    ded (matches_correct H1). rewrite H3. hyp.
  Qed.

  Arguments rewrite_correct [t d u] _.

  Fixpoint rewrites t (ds : list data) : option (list term) :=
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
    revert H. case_eq (rewrite t a); intros. 2: discr.
    revert H0. case_eq (rewrites t0 ds); intros. 2: discr.
    inversion H1. simpl. ded (rewrite_correct H). intuition.
  Qed.

  Arguments rewrites_correct [ds t us] _.

  Notation default := (Var 0).

  Lemma FS_red : forall ts t, FS t ts -> forall i, i < length ts ->
    red R (nth i (t::ts) default) (nth (S i) (t::ts) default).

  Proof.
    induction ts; simpl; intros. lia. destruct H. destruct i. hyp.
    ded (IHts _ H1 i (lt_S_n H0)). hyp.
  Qed.

(***********************************************************************)
(** hyps for non-termination *)

  Section loop.

    Variables (t : term) (ds : list data)
      (us : list term) (h1 : rewrites t ds = Some us).

    Definition k := length us.

    Definition nth i := nth i us default.

    Definition last_term := nth (k-1).

    Variable h0 : k > 0.

    Lemma FS_red' : forall i, i < k - 1 -> red R (nth i) (nth (S i)).

    Proof.
      intros. unfold nth.
      change (red R (List.nth (S i) (t :: us) default)
        (List.nth (S (S i)) (t :: us) default)).
      apply FS_red. eapply rewrites_correct. apply h1. unfold k in *. lia.
    Qed.

    Variables (p : position) (u : term) (h2 : subterm_pos last_term p = Some u)
      (s : substitution Sig) (h3 : matches t u = Some s).

(***********************************************************************)
(** proof of non-termination *)

    Definition c : context Sig.

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
      intros. apply red_fill. apply red_sub. hyp.
    Qed.

    Definition seq : nat -> term.

    Proof.
      intro n. destruct (eucl_dev k h0 n). exact (iter (nth r) g q).
    Defined.

    Lemma IS_seq : IS (red R) seq.

    Proof.
      intro n; pattern n; apply lt_wf_ind; clear n; intros. unfold seq at -2 .
      destruct (eucl_dev k h0 n); simpl. destruct (le_gt_dec (k-1) r).
      (* r = k-1 *)
      assert (r = k-1). lia. assert (S n = (S q)*k + 0). rewrite Nat.mul_succ_l.
      lia. rewrite H1. unfold seq. destruct (eucl_dev k h0 (S q * k + 0)).
      destruct (eucl_div_unique h0 g1 e0). rewrite <- H3, <- H2. simpl.
      rewrite <- iter_com. apply red_iter. apply red_g.
      rewrite H0. fold last_term. rewrite last_term_g.
      apply red_g. unfold nth.
      change (red R (List.nth 0 (t :: us) default)
        (List.nth 1 (t :: us) default)).
      apply FS_red. apply (rewrites_correct h1). hyp.
      (* r < k-1 *)
      assert (S n = q*k + S r). lia. rewrite H0. unfold seq.
      destruct (eucl_dev k h0 (q * k + S r)). assert (k>S r). lia.
      destruct (eucl_div_unique H1 g2 e0). rewrite <- H3, <- H2.
      apply red_iter. apply red_g. apply FS_red'. lia.
    Qed.

    Lemma loop : EIS (red R).

    Proof.
      exists seq. apply IS_seq.
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
            let u := last us default in
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

  Lemma is_loop_correct : forall t ds p, is_loop t ds p = true -> EIS (red R).

  Proof.
    intros t ds p. unfold is_loop. case_eq (rewrites t ds). 2: discr.
    destruct l. discr. set (us := t0::l). set (u := last us default).
    case_eq (subterm_pos u p). 2: discr. intro v.
    case_eq (matches t v); intros.
    2: discr. assert (h0 : k us > 0). unfold k, us. simpl. lia.
    assert (h : u = last_term us). unfold last_term, k, nth.
    rewrite <- last_nth.
    refl. rewrite h in H0. exists (seq us h0 p H0 t1). eapply IS_seq. apply H1.
    hyp.
  Qed.

End S.

Arguments rewrite_correct [Sig R t d u] _.
Arguments rewrites_correct [Sig R ds t us] _.

(***********************************************************************)
(** tactics *)

Ltac check_loop t' ds' p' :=
  apply is_loop_correct with (t:=t') (ds:=ds') (p:=p');
    (check_eq || fail 10 "not a loop").

Ltac loop t' ds' p' :=
  match goal with
    | |- EIS (red_mod ?E _) =>
      remove_relative_rules E; check_loop t' ds' p'
    | |- EIS (red _) => check_loop t' ds' p'
  end.
