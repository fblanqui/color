(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui & Wang Qian & Zhang Lianyi, 2009-05-11

definition and correctness proof of a boolean function checking that
there is a loop in an SRS
*)

Set Implicit Arguments.

From Coq Require Import Euclid Wf_nat.
From CoLoR Require Import LogicUtil Srs ListUtil EqUtil RelUtil ListDec NatUtil.
    
Section S.

  Variable Sig : Signature.

  Notation letter := (symbol Sig). Notation string := (string Sig).

  Ltac case_beq_symb := VSignature.case_beq_symb Sig.

  Variable R : rules Sig.

(***********************************************************************)
(** predicates saying that [t::us] is in a sequence of rewriting steps *)

  Fixpoint FS t us :=
    match us with
      | nil => True
      | u :: us' => red R t u /\ FS u us'
    end.

  Definition strings_of_reduc : forall t, {us| FS t us} -> list string.

  Proof.
    intros t x. destruct x. exact x.
  Defined.

  Arguments strings_of_reduc [t] _.

  Definition proof_of_reduc :
    forall t, forall x : {us| FS t us}, FS t (strings_of_reduc x).

  Proof.
    intros t x. destruct x. exact f.
  Defined.

  Lemma FS_rtc : forall us t, FS t us -> red R # t (last us t).

  Proof.
    induction us. simpl. intros. apply rt_refl. simpl FS. intuition.
    apply rt_trans with a. apply rt_step. hyp. simpl. destruct us.
    apply rt_refl.
    rewrite last_default with (d2:=a). apply IHus. hyp. discr.
  Qed.

(***********************************************************************)
(** matching *)

  Fixpoint matches (p t : string) : option string :=
    match p, t with
      | nil, _ => Some t
      | a :: p', b :: t' => if beq_symb a b then matches p' t' else None
      | _, _ => None
    end.

  Lemma matches_correct : forall p t u, matches p t = Some u -> t = p ++ u.

  Proof.
    induction p; simpl; intros. inversion H. refl.
    destruct t. discr. revert H. case_beq_symb a s. 2: discr. intro.
    rewrite (IHp _ _ H). refl.
  Qed.

  Arguments matches_correct [p t u] _.

  Lemma matches_complete : forall p t u, t = p ++ u -> matches p t = Some u.

  Proof.
    induction p; simpl; intros; subst. refl.
    rewrite (beq_refl (@beq_symb_ok Sig)). apply IHp. refl.
  Qed.

(***********************************************************************)
(** data necessary for a sequence of rewrite steps *)

  Definition data := (nat * rule Sig)%type.

  Definition rewrite (t : string) (d : data) : option string :=
    let (p,a) := d in let (l,r) := a in
      if mem (@beq_rule Sig) (mkRule l r) R then
        match split t p with
          | None => None
          | Some (u,v) =>
            match matches l v with
              | None => None
              | Some w => Some (u ++ r ++ w)
            end
        end
        else None.

  Lemma rewrite_correct : forall t d s, rewrite t d = Some s -> red R t s.

  Proof.
    intros t [p [l r]] s. unfold rewrite.
    case_eq (mem (@beq_rule Sig) (mkRule l r) R); intros. 2: discr.
    revert H0. case_eq (split t p); intros. destruct p0 as [u v]. 2: discr.
    revert H1. case_eq (matches l v); intros. rename s0 into w. 2: discr.
    exists l. exists r. exists (mkContext u w). unfold fill. simpl.
    inversion H2. intuition. rewrite mem_ok in H. hyp. apply beq_rule_ok.
    ded (matches_correct H1). ded (split_correct H0). subst. refl.
  Qed.

  Arguments rewrite_correct [t d s] _.

  Fixpoint rewrites t (ds : list data) : option (list string) :=
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
    revert H0. case_eq (rewrites s ds); intros. 2: discr.
    inversion H1. simpl. ded (rewrite_correct H). intuition.
  Qed.

  Arguments rewrites_correct [ds t us] _.

  Notation default := (@nil letter).

  Lemma FS_red : forall ts t, FS t ts -> forall i, i < length ts ->
    red R (nth i (t::ts) default) (nth (S i) (t::ts) default).

  Proof.
    induction ts; simpl; intros. lia. destruct H. destruct i. hyp.
    ded (IHts _ H1 i (lt_S_n H0)). hyp.
  Qed.

(***********************************************************************)
(** hyps for non-termination *)

  Section loop.

    Variables (t : string) (ds : list data)
      (us : list string) (h1 : rewrites t ds = Some us).

    Definition k := length us.

    Definition nth i := nth i us default.

    Definition last_string := nth (k-1).

    Variable h0 : k > 0.

    Lemma FS_red' : forall i, i < k - 1 -> red R (nth i) (nth (S i)).

    Proof.
      intros. unfold nth.
      change (red R (List.nth (S i) (t :: us) default)
        (List.nth (S (S i)) (t :: us) default)).
      apply FS_red. eapply rewrites_correct. apply h1. unfold k in *. lia.
    Qed.

    Variables (p : nat) (u v : string) (h2 : split last_string p = Some (u,v))
      (s : string) (h3 : matches t v = Some s).

(***********************************************************************)
(** proof of non-termination *)

    Definition c := mkContext u s.

    Definition g t := fill c t.

    Lemma last_string_g : last_string = g t.

    Proof.
      unfold g, c. ded (split_correct h2). rewrite H. ded (matches_correct h3).
      subst. refl.
    Qed.

    Definition seq : nat -> string.

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
      rewrite <- iter_com. apply red_iter. apply red_fill.
      rewrite H0. fold last_string. rewrite last_string_g. apply red_fill.
      unfold nth. change (red R (List.nth 0 (t :: us) default)
        (List.nth 1 (t :: us) default)).
      apply FS_red. apply (rewrites_correct h1). hyp.
      (* r < k-1 *)
      assert (S n = q*k + S r). lia. rewrite H0. unfold seq.
      destruct (eucl_dev k h0 (q * k + S r)). assert (k>S r). lia.
      destruct (eucl_div_unique H1 g2 e0). rewrite <- H3, <- H2.
      apply red_iter. apply red_fill. apply FS_red'. lia.
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
              match split u p with
                | None => false
                | Some (_,w) =>
                  match matches t w with
                    | None => false
                    | Some _ => true
                  end
              end
        end
    end.

  Lemma is_loop_correct : forall t ds p, is_loop t ds p = true -> EIS (red R).

  Proof.
    intros t ds p. unfold is_loop. case_eq (rewrites t ds). 2: discr.
    destruct l. discr. set (us := s::l). set (u := last us default).
    case_eq (split u p). 2: discr. intros [v w].
    case_eq (matches t w); intros.
    2: discr. assert (h0 : k us > 0). unfold k, us. simpl. lia.
    assert (h : u = last_string us). unfold last_string, k, nth.
    rewrite <- last_nth. refl. rewrite h in H0. exists (seq us h0 v s0).
    eapply IS_seq. apply H1. apply H0. hyp.
  Qed.

End S.

Arguments rewrite_correct [Sig R t d s] _.
Arguments rewrites_correct [Sig R ds t us] _.
Arguments matches [Sig] _ _.
Arguments matches_correct [Sig p t u] _.
Arguments matches_complete [Sig p t u] _.

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
