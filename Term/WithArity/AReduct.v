(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-05-06

list of reducts of a term and proof that rewriting is finitely branching
*)

Set Implicit Arguments.

From CoLoR Require Import LogicUtil ATrs RelUtil ListUtil VecUtil AMatching
     NatUtil.

Section S.

  Variable Sig : Signature.

  Notation term := (term Sig). Notation terms := (vector term).
  Notation rule := (rule Sig). Notation rules := (list rule).

(***********************************************************************)
(** top reducts *)

  Definition top_reduct (t : term) lr :=
    match matches (lhs lr) t with
      | Some s => Some (sub s (rhs lr))
      | None => None
    end.

  Lemma top_reduct_correct : forall R lr t u,
    In lr R -> top_reduct t lr = Some u -> hd_red R t u.

  Proof.
    intros R0 lr t u hlr. unfold top_reduct. destruct lr as [l r]. simpl.
    case_eq (matches l t); intros t0 H.
    intro H0. ded (matches_correct H). subst. inversion H0.
    apply hd_red_rule. hyp. discr.
  Qed.

  Definition top_reducts R t := filter_opt (top_reduct t) R.

  Lemma top_reducts_correct : forall t u R,
    In u (top_reducts R t) -> hd_red R t u.

  Proof.
    induction R; simpl. contr.
    assert (h : List.incl R (a::R)). unfold List.incl. simpl. auto.
    case_eq (top_reduct t a); intros t0 H.
    intro H0. simpl in H0. split_all. subst.
    eapply top_reduct_correct with (lr := a). simpl. auto. hyp.
    eapply incl_elim. apply hd_red_incl with (x := R). hyp. tauto.
    eapply incl_elim. apply hd_red_incl with (x := R). hyp. tauto.
  Qed.

  Arguments top_reducts_correct [t u R] _.

  Lemma top_reducts_correct_red : forall t u R,
    In u (top_reducts R t) -> red R t u.

  Proof.
    intros. ded (top_reducts_correct H).
    eapply incl_elim. apply hd_red_incl_red. hyp.
  Qed.

  Lemma top_reducts_complete : forall t u R,
    rules_preserve_vars R -> hd_red R t u -> In u (top_reducts R t).

  Proof.
    induction R; intros; redtac. hyp. simpl in lr.
    assert (h0 : rules_preserve_vars R). eapply rules_preserve_vars_incl.
    2: apply H. apply incl_tl. refl. split_all.
    (* In (mkRule l r) R *)
    2:{ simpl. assert (h1 : hd_red R t u). subst. apply hd_red_rule. hyp.
    case (top_reduct t a). right. apply IHR; hyp. apply IHR; hyp. }
    (* a = mkRule l r *)
    subst a. simpl. unfold top_reduct. simpl.
    case_eq (matches l t).
    intros t0 H0. ded (matches_correct H0). left. subst u. apply sub_eq. intros.
    eapply subeq_inversion. rewrite xl in H1. apply H1.
    unfold rules_preserve_vars in H. unfold List.incl in H. eapply H. simpl.
    auto. hyp.
    intro H0. symmetry in xl. ded (matches_complete xl). congruence.
  Qed.

(***********************************************************************)
(** list of reducts of a term *)

  Variable R : rules.

  Lemma reducts_aux1 : forall k n, S k <= n -> k <= n.

  Proof. lia. Qed.

  Lemma reducts_aux2 : forall k n, S k <= n -> n - S k < n.

  Proof. lia. Qed.

  Fixpoint reducts t :=
    match t with
      | Var _ => top_reducts R t
      | Fun f ts =>
        let fix reducts_vec k (us : terms k) : k <= arity f -> list term :=
          match us in vector _ k return k <= arity f -> list term with
            | Vnil => fun _ => nil
            | Vcons u1 us' => fun h =>
              map (fun x => Fun f (Vreplace ts (reducts_aux2 h) x)) (reducts u1)
              ++ reducts_vec _ us' (reducts_aux1 h)
          end
          in top_reducts R t ++ reducts_vec (arity f) ts (Nat.le_refl (arity f))
    end.

  Fixpoint reducts_vec f ts k (us : terms k) : k <= arity f -> list term :=
    match us in vector _ k return k <= arity f -> list term with
      | Vnil => fun _ => nil
      | Vcons u1 us' => fun h =>
        map (fun x => Fun f (Vreplace ts (reducts_aux2 h) x)) (reducts u1)
        ++ reducts_vec f ts us' (reducts_aux1 h)
    end.

  Lemma fix_reducts_vec : forall f ts k us h,
    (fix reducts_vec (k : nat) (us : terms k) : k <= arity f -> list term :=
      match us in (vector _ k0) return (k0 <= arity f -> list term) with
        | Vnil => fun _ => nil
        | Vcons u1 us' => fun h =>
          map (fun x => Fun f (Vreplace ts (reducts_aux2 h) x)) (reducts u1)
          ++ reducts_vec _ us' (reducts_aux1 h)
      end) k us h = reducts_vec f ts us h.

  Proof.
    induction us; simpl; intros. refl. apply app_eq. refl. apply IHus.
  Qed.

  Lemma reducts_fun : forall f ts, reducts (Fun f ts)
    = top_reducts R (Fun f ts) ++ reducts_vec f ts ts (Nat.le_refl (arity f)).

  Proof. intros. simpl. rewrite <- fix_reducts_vec. refl. Qed.

(***********************************************************************)
(** properties *)

  Lemma reducts_vec_pi : forall f ts k (us : terms k) h h',
    reducts_vec f ts us h = reducts_vec f ts us h'.

  Proof. intros. assert (h=h'). apply le_unique. subst h'. refl. Qed.

  Lemma reducts_vec_cast : forall f ts k (us : terms k) h k' (e : k = k') h',
    reducts_vec f ts (Vcast us e) h' = reducts_vec f ts us h.

  Proof.
    induction us; intros; destruct k'; try discr. rewrite Vcast_refl. refl.
    rewrite Vcast_cons. simpl. inversion e. subst k'.
    apply app_eq. apply map_eq. intros. apply args_eq. apply Vreplace_pi.
    lia. apply IHus.
  Qed.

  (*Arguments reducts_vec_cast [f ts k us] _ [k' e h'].*)

  Lemma In_reducts_vec_elim_aux : forall v' f ts k (us : terms k),
    (forall i (p : i < k), exists r : arity f - k + i < arity f,
      Vnth us p = Vnth ts r) -> forall h, In v' (reducts_vec f ts us h) ->
    exists i, exists p : i < arity f, exists u',
      In u' (reducts (Vnth ts p)) /\ v' = Fun f (Vreplace ts p u').

  Proof.
    induction us.
    (* Vnil *)
    contr.
    (* Vcons *)
    intros E g H. simpl in H. rewrite in_app in H. split_all.
    (* case 1 *)
    ded (in_map_elim H). decomp H0. destruct (E 0 (Nat.lt_0_succ n)). simpl in H0.
    ex (arity f - S n + 0) x0 x. rewrite <- H0. split_all.
    rewrite H3. apply args_eq. apply Vreplace_pi. lia.
    (* case 2 *)
    assert (E' : forall (i : nat) (p : i < n),
      exists r : arity f - n + i < arity f, Vnth us p = Vnth ts r). intros.
    assert (p' : S i < S n). lia. destruct (E (S i) p'). simpl in H.
    assert (lt_S_n p' = p). apply lt_unique. simpl in H0. rewrite H1 in H0.
    rewrite H0.
    assert (r : arity f - n + i < arity f). lia. exists r. apply Vnth_eq.
    lia.
    assert (h' : n <= arity f). lia.
    rewrite reducts_vec_pi with (h':=h') in H.
    apply IHus with (h:=h'); hyp.
  Qed.

  Arguments In_reducts_vec_elim_aux [v' f ts k us] _ [h] _.

  Lemma In_reducts_vec_elim : forall v' f ts,
    In v' (reducts_vec f ts ts (Nat.le_refl (arity f))) ->
    exists i, exists p : i < arity f, exists u',
      In u' (reducts (Vnth ts p)) /\ v' = Fun f (Vreplace ts p u').

  Proof.
    intros. apply In_reducts_vec_elim_aux
    with (k := arity f) (us := ts) (h := Nat.le_refl (arity f)).
    intros. assert (r : arity f - arity f + i < arity f). lia. exists r.
    apply Vnth_eq. lia. hyp.
  Qed.

  Arguments In_reducts_vec_elim [v' f ts] _.

  Lemma In_reducts_vec_intro_aux : forall f ts k (us : terms k)
    (h : k <= arity f) t i (p : i < k) (q : arity f - k + i < arity f),
    In t (reducts (Vnth us p)) ->
    In (Fun f (Vreplace ts q t)) (reducts_vec f ts us h).

  Proof.
    induction us.
    (* Vnil *)
    intros. lia.
    (* Vcons *)
    intros g t. simpl.
    set (F := fun x : term => Fun f (Vreplace ts (reducts_aux2 g) x)).
    destruct i; intros p q; rewrite in_app.
    (* i = 0 *)
    left. assert (e : arity f - S n + 0 = arity f - S n). lia.
    rewrite (Vreplace_pi ts q (reducts_aux2 g) t e).
    apply in_map with (f:=F). hyp.
    (* i > 0 *)
    right. assert (q' : arity f - n + i < arity f). lia.
    assert (Vreplace ts q t = Vreplace ts q' t). apply Vreplace_pi. lia.
    rewrite H0. apply IHus with (p := lt_S_n p). hyp.
  Qed.

  Arguments In_reducts_vec_intro_aux _ _ [k us] _ _ [i p] _ _.

  Lemma In_reducts_vec_intro : forall f ts t i (p : i < arity f),
    In t (reducts (Vnth ts p)) ->
    In (Fun f (Vreplace ts p t)) (reducts_vec f ts ts (Nat.le_refl (arity f))).

  Proof.
    intros. assert (q : arity f - arity f + i < arity f). lia.
    assert (Vreplace ts p t = Vreplace ts q t). apply Vreplace_pi. lia.
    rewrite H0. apply In_reducts_vec_intro_aux with (p := p). hyp.
  Qed.

(***********************************************************************)
(** alternative definition (Pierre-Yves Strub) *)

  Fixpoint reducts2 t :=
    match t with
      | Var _ => top_reducts R t
      | Fun f ts =>
        let fix reducts2_vec k (us : terms k) : list (terms k) :=
          match us with
            | Vnil => nil
            | Vcons u1 us' => map (fun x => Vcons x us') (reducts2 u1)
              ++ map (fun x => Vcons u1 x) (reducts2_vec _ us')
          end
          in top_reducts R t ++ map (Fun f) (reducts2_vec (arity f) ts)
    end.

  Fixpoint reducts2_vec k (us : terms k) : list (terms k) :=
    match us with
      | Vnil => nil
      | Vcons u1 us' => map (fun x => Vcons x us') (reducts2 u1)
        ++ map (fun x => Vcons u1 x) (reducts2_vec us')
    end.

  Lemma reducts2_fun : forall f ts, reducts2 (Fun f ts)
    = top_reducts R (Fun f ts) ++ map (Fun f) (reducts2_vec ts).

  Proof. auto. Qed.

  Lemma In_reducts2_vec_elim : forall n (vs ts : terms n),
    In vs (reducts2_vec ts) -> exists i, exists p : i < n, exists u,
      In u (reducts2 (Vnth ts p)) /\ vs = Vreplace ts p u.

  Proof.
    induction ts; intros.
    (* Vnil *)
    contr.
    (* Vcons *)
    simpl in H. rewrite in_app in H.
    split_all; ded (in_map_elim H); clear H; decomp H0.
    (* case 1 *)
    set (p := Nat.lt_0_succ n). ex 0 p x. simpl. auto.
    (* case 2 *)
    ded (IHts x H1); clear IHts. decomp H. assert (p : S x0<S n). lia.
    ex (S x0) p x2. simpl. assert (lt_S_n p = x1). apply lt_unique.
    rewrite H. subst x. auto. 
  Qed.

  Arguments In_reducts2_vec_elim [n vs ts] _.

  Lemma In_reducts2_vec_intro : forall n (ts : terms n) t i (p : i < n),
    In t (reducts2 (Vnth ts p)) -> In (Vreplace ts p t) (reducts2_vec ts).

  Proof.
    induction ts.
    (* Vnil *)
    intros. lia.
    (* Vcons *)
    destruct i; simpl; intro; rewrite in_app.
    left. apply in_map with (f := fun x => Vcons x ts). hyp.
    right. apply in_map with (f := fun x => Vcons h x). apply IHts. hyp.
  Qed.

(***********************************************************************)
(** correctness *)

  Lemma reducts_correct : forall t u, In u (reducts t) -> red R t u.

  Proof.
    intro t. pattern t; apply term_ind_forall; clear t.
    (* Var *)
    intros. apply top_reducts_correct_red. hyp.
    (* Fun *)
    intros f ts IH u. rewrite reducts_fun, in_app. split_all.
    apply hd_red_incl_red. apply top_reducts_correct. hyp.
    rename H into h. ded (In_reducts_vec_elim h). decomp H.
    ded (Vforall_nth x0 IH _ H1). redtac. unfold red. ex l r.
    assert (h1 : 0+x<=arity f). lia. set (v1 := Vsub ts h1).
    assert (h2 : S x+(arity f-S x)<=arity f). lia. set (v2 := Vsub ts h2).
    assert (e : x+S(arity f-S x)=arity f). lia.
    exists (Cont f e v1 c v2). exists s. split_all. simpl. apply args_eq.
    rewrite <- xl. unfold v2. rewrite Vcons_nth. unfold v1.
    apply Veq_app_cons_aux.
    simpl. rewrite H2. apply args_eq. apply Veq_nth; intros.
    rewrite Vnth_cast, Vnth_app. destruct (le_gt_dec x i).
    (* 1) x <= i *)
    destruct (eq_nat_dec x i).
    (* a) x = i *)
    set (q := Vnth_app_aux (S (arity f - S x)) (Vnth_cast_aux e ip) l0).
    gen q. assert (i - x = 0). subst; clear; lia. rewrite H. intro. simpl.
    trans (Vnth (Vreplace ts x0 x1) x0). apply Vnth_eq. auto.
    rewrite Vnth_replace. hyp.
    (* b) x <> i *)
    rewrite Vnth_replace_neq. 2: hyp.
    rewrite (Veq_app_cons ts x0), Vnth_cast, Vnth_app. destruct (le_gt_dec x i).
    2: lia.
    rewrite !Vnth_cons. destruct (lt_ge_dec 0 (i-x)). unfold v2.
    rewrite !Vnth_sub. apply Vnth_eq. refl. lia.
    (* 2) x > i *)
    rewrite Vnth_replace_neq. 2: lia.
    rewrite (Veq_app_cons ts x0), Vnth_cast, Vnth_app. destruct (le_gt_dec x i).
    lia.
    assert (g0 = g). apply lt_unique. subst g0.
    assert (Vsub ts (Veq_app_cons_aux1 x0) = v1). unfold v1.
    f_equal. apply le_unique. rewrite H. refl.
  Qed.

(***********************************************************************)
(** completeness *)

  Lemma reducts_complete : rules_preserve_vars R ->
    forall t u, red R t u -> In u (reducts t).

  Proof.
    intros H t; pattern t; apply term_ind_forall; clear t; intros.
    (* Var *)
    ded (red_case H0). split_all.
    simpl. apply top_reducts_complete; hyp.
    decomp H2. discr.
    (* Fun *)
    rewrite reducts_fun, in_app. ded (red_case H1). split_all.
    left. apply top_reducts_complete; hyp.
    right. Funeqtac. subst x0. ded (Vforall_nth x2 H0). subst u.
    apply In_reducts_vec_intro. apply H2. hyp.
  Qed.

(***********************************************************************)
(** rewriting is finitely branching *)

  Lemma fin_branch : rules_preserve_vars R -> finitely_branching (red R).

  Proof.
    unfold finitely_branching. intros. exists (reducts x). split_all.
    apply reducts_complete; hyp. apply reducts_correct. hyp.
  Qed.

End S.
