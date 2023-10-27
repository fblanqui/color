(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sidi Ould-Biha, 2010-04-27

Properties of the subterm relation.
*)

Set Implicit Arguments.

From CoLoR Require Import AContext VecUtil ListUtil LogicUtil NatUtil RelUtil
     ASN.

Section S.

  Variable Sig : Signature.

  Notation term := (term Sig). Notation terms := (vector term).

(***********************************************************************)
(** list of immediate subterms *)

  Fixpoint subterm_lst t :=
    match t with
      | Var _ => nil
      | Fun f ts =>
        let fix subterm_lst_vec k (us : terms k) {struct us} : list term :=
          match us with
            | Vnil => nil
            | Vcons u1 us' => subterm_lst u1 ++ subterm_lst_vec _ us'
          end
          in list_of_vec ts ++ subterm_lst_vec (arity f) ts
    end.

  Fixpoint subterm_lst_vec k (us : terms k) : list term :=
    match us with
      | Vnil => nil
      | Vcons u1 us' => subterm_lst u1 ++ subterm_lst_vec us'
    end.

  Lemma subterm_lst_fun : forall F ts,
    subterm_lst (Fun F ts) = list_of_vec ts ++ subterm_lst_vec ts.

  Proof.
    refl.
  Qed.

(***********************************************************************)
(** list of immediate subterms *)

  Lemma In_subterm_lst_vec_elim : forall v n (ts : terms n),
    In v (subterm_lst_vec ts) ->
    exists i, exists p : i < n, In v (subterm_lst (Vnth ts p)).

  Proof.
    induction ts. contr.
    intros In_v; simpl in In_v. rewrite in_app in In_v. intuition.
    exists 0. exists (Nat.lt_0_succ n). simpl. hyp.
    destruct H0 as [i H0]. destruct H0 as [p H0].
    assert (p' : S i < S n). lia. exists (S i). exists p'. simpl.
    assert (H1 : (lt_S_n p') = p). apply lt_unique. rewrite H1. hyp.
  Qed.

  Lemma In_subterm_lst_vec_intro : forall n (ts : terms n) v i (p : i < n),
    In v (subterm_lst (Vnth ts p)) -> In v (subterm_lst_vec ts).

  Proof.
    induction ts. intros. lia.
    destruct i; simpl; intros; rewrite in_app.
    left; hyp. right. apply (IHts _ _ (lt_S_n p)); auto.
  Qed.

(***********************************************************************)
(** the supterm relation is finitely branching *)

  Notation supterm := (@supterm Sig).

  Lemma fin_branch_supterm : finitely_branching supterm.

  Proof.
    intros x. exists (subterm_lst x). pattern x; apply term_ind_forall; clear x.
    simpl. intros v y. split; try tauto. intro HS; destruct HS as [c Hc].
    destruct (var_eq_fill (proj2 Hc)) as [Hc' _]; intuition.
    intros f ts Hts y. split; rewrite subterm_lst_fun, in_app.
    2:{ intuition. gen (in_list_of_vec H0). apply subterm_fun.
    ded (In_subterm_lst_vec_elim _ _ H0). decomp H.
    ded (Vforall_nth x0 Hts y). apply (@subterm_trans _ _ (Vnth ts x0)).
    apply H. hyp. apply subterm_fun. apply Vnth_in. }
    intros. destruct H as [c Hc]. destruct (fun_eq_fill (proj2 Hc)). intuition.
    destruct H as [i H]. destruct H as [j H]. destruct H as [r H].
    destruct H as [ti H]. destruct H as [c0 H]. destruct H as [tj Hc0].
    destruct Hc as [Hc Hf]. rewrite Hc0 in Hf. simpl in Hf. Funeqtac.
    destruct c0. simpl in H. left. rewrite H. apply list_of_vec_in.
    apply Vin_cast_intro. apply Vin_appr. simpl. left; refl.
    right. assert (p : i < arity f). rewrite <- r. lia.
    assert (Hs : supterm (Vnth ts p) y).
    rewrite H, Vnth_cast, Vnth_app.
    destruct (le_gt_dec i i). 2: lia.
    set (q := (Vnth_app_aux (S j) (Vnth_cast_aux r p) l)).
    rewrite (Vnth_eq _ q (Nat.lt_0_succ j)); try lia. simpl.
    exists (Cont f0 e t c0 t0). simpl. intuition. discr.
    ded (Vforall_nth p Hts y). apply (In_subterm_lst_vec_intro _ _ p).
    apply (proj1 H0). auto.
  Qed.

End S.
