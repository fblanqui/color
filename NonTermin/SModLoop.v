(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-05-22

definition and correctness proof of a boolean function checking that
there is a loop in a relative SRS
*)

Set Implicit Arguments.

From Stdlib Require Import Euclid Wf_nat.
From CoLoR Require Import Srs LogicUtil SLoop ListUtil NatUtil RelUtil.

Section S.

  Variable Sig : Signature.

  Notation letter := (symbol Sig). Notation string := (string Sig).
  Notation data := (data Sig).

  Variables E R : rules Sig.

(***********************************************************************)
(** predicates saying that [t::us] is in a sequence of rewriting steps *)

  Fixpoint mod_FS t us :=
    match us with
      | nil => True
      | u :: us' => red_mod E R t u /\ mod_FS u us'
    end.

  Definition mod_strings_of_reduc : forall t, {us| mod_FS t us} -> list string.

  Proof.
    intros t x. destruct x. exact x.
  Defined.

  Arguments mod_strings_of_reduc [t] _.

  Definition mod_proof_of_reduc :
    forall t, forall x : {us| mod_FS t us}, mod_FS t (mod_strings_of_reduc x).

  Proof.
    intros t x. destruct x. exact m.
  Defined.

(***********************************************************************)
(** data necessary for a sequence of red_mod steps *)

  Definition mod_data := (list data * data)%type.

  Definition mod_rewrite (t : string) (mds : mod_data) : option string :=
    let (ds,d) := mds in
      match rewrites E t ds with
        | None => None
        | Some ts => rewrite R (last ts t) d
      end.

  Lemma mod_rewrite_correct : forall t mds u,
    mod_rewrite t mds = Some u -> red_mod E R t u.

  Proof.
    intros t [ds d] u. unfold mod_rewrite.
    case_eq (rewrites E t ds); intros.
    2: discr. ded (rewrites_correct H). ded (rewrite_correct H0).
    exists (last l t); split. apply FS_rtc. hyp. hyp.
  Qed.

  Arguments mod_rewrite_correct [t mds u] _.

  Fixpoint mod_rewrites t (mds : list mod_data) : option (list string) :=
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

  Lemma mod_rewrites_correct : forall mds t us,
    mod_rewrites t mds = Some us -> mod_FS t us.

  Proof.
    induction mds; simpl; intros. inversion H. exact I.
    revert H. case_eq (mod_rewrite t a); intros. 2: discr.
    revert H0. case_eq (mod_rewrites s mds); intros. 2: discr.
    inversion H1. simpl. ded (mod_rewrite_correct H). intuition.
  Qed.

  Arguments mod_rewrites_correct [mds t us] _.

  Notation default := (@nil letter).

  Lemma red_mod_nth : forall ts t, mod_FS t ts -> forall i, i < length ts ->
    red_mod E R (List.nth i (t::ts) default) (List.nth (S i) (t::ts) default).

  Proof.
    induction ts; simpl; intros. lia. destruct H. destruct i. hyp.
    ded (IHts _ H1 i (NatCompat.lt_S_n H0)). hyp.
  Qed.

(***********************************************************************)
(** hyps for non-termination *)

  Section loop.

    Variables (t : string) (mds : list mod_data)
      (us : list string) (h1 : mod_rewrites t mds = Some us).

    Definition k := length us.

    Definition nth i := List.nth i us default.

    Definition last_string := nth (k-1).

    Variable h0 : k > 0.

    Lemma FS_red_mod' : forall i, i < k - 1 -> red_mod E R (nth i) (nth (S i)).

    Proof.
      intros. unfold nth.
      change (red_mod E R (List.nth (S i) (t :: us) default)
        (List.nth (S (S i)) (t :: us) default)).
      apply red_mod_nth. eapply mod_rewrites_correct. apply h1. unfold k in *.
      lia.
    Qed.

    Variables (ds : list data) (us' : list string)
      (h1' : rewrites E last_string ds = Some us').

    Definition last_string' := last us' last_string.

    Variables (p : nat) (u v : string) (h2 : split last_string' p = Some (u,v))
      (s : string) (h3 : matches t v = Some s).

(***********************************************************************)
(** proof of non-termination *)

    Definition c := mkContext u s.

    Definition g t := fill c t.

    Lemma last_string'_g : last_string' = g t.

    Proof.
      unfold g, c. ded (split_correct h2). rewrite H. ded (matches_correct h3).
      subst. refl.
    Qed.

    Lemma red_last_string_g : red E # last_string (g t).

    Proof.
      rewrite <- last_string'_g. unfold last_string'. apply FS_rtc.
      apply (rewrites_correct h1').
    Qed.

    Definition seq : nat -> string.

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
      rewrite <- iter_com. apply red_iter. apply red_mod_fill.
      rewrite H0. fold last_string.
      cut (red_mod E R (g t) (g (nth 0))). intro. destruct H4. exists x.
      intuition. apply rt_trans with (g t). apply red_last_string_g. hyp.
      apply red_mod_fill. unfold nth.
      change (red_mod E R (List.nth 0 (t :: us) default)
        (List.nth 1 (t :: us) default)).
      apply red_mod_nth. apply (mod_rewrites_correct h1). hyp.
      (* r < k-1 *)
      assert (S n = q*k + S r). lia. rewrite H0. unfold seq.
      destruct (eucl_dev k h0 (q * k + S r)). assert (k>S r). lia.
      destruct (eucl_div_unique H1 g2 e0). rewrite <- H3, <- H2.
      apply red_iter. apply red_mod_fill. apply FS_red_mod'. lia.
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
                    match split u' p with
                      | None => false
                      | Some (_,w) =>
                        match matches t w with
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
    2: discr. destruct l. discr. set (us := s::l). set (u := last us default).
    case_eq (rewrites E u ds). 2: discr. intro us'. set (u' := last us' u).
    case_eq (split u' p). 2: discr. intros [v w].
    case_eq (matches t w); intros.
    2: discr. assert (h0 : k us > 0). unfold k, us. simpl. lia.
    assert (h : u = last_string us). unfold last_string, k, nth.
    rewrite <- last_nth. refl. exists (seq us h0 v s0). eapply IS_seq. apply H2.
    rewrite <- h. apply H1. unfold last_string'. rewrite <- h. fold u'.
    apply H0. hyp.
  Qed.

End S.

(***********************************************************************)
(** tactics *)

Ltac loop t' mds' ds' p' :=
  apply is_mod_loop_correct with (t:=t') (mds:=mds') (ds:=ds') (p:=p');
    (check_eq || fail 10 "not a loop").
