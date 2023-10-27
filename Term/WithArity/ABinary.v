(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sidi Ould-Biha, 2010-05-04

properties of signatures with a symbol of arity 2
*)

Set Implicit Arguments.

From CoLoR Require Import ATrs VecUtil ListUtil LogicUtil NatUtil RelUtil.

Record BinSignature : Type := Make {
  Sig :> Signature;
  Cons : Sig;
  _ : arity Cons = 2
}.

Section BinSignatureTheory.

  Variable Sig : BinSignature.

  Notation term := (term Sig). Notation terms := (vector term).
  Notation rule := (rule Sig). Notation rules := (list rule).

  Lemma cons_arity : 2 = arity (Cons Sig).

  Proof. case Sig. auto. Qed.

  (* Building a new term with Cons as root symbol *)
  Fixpoint cons_term (t : term) n (v : terms n) : term :=
    match v with 
      | Vnil => t
      | Vcons t' v' => Fun (Cons Sig)
        (Vcast (Vcons t (Vcons (cons_term t' v') Vnil)) cons_arity)
    end.

  Lemma cons_term_cons : forall t t' n (v : terms n),
    cons_term t (Vcons t' v)
    = Fun (Cons Sig) (Vcast (Vcons t (Vcons (cons_term t' v) Vnil)) cons_arity).

  Proof. intros. auto. Qed.

  (* Projection TRS associated to Cons *)
  Definition proj_cons : rules :=
    let Vxy := Vcast (Vcons (Var 0) (Vcons (Var 1) Vnil)) cons_arity in
      mkRule (Fun (Cons Sig) Vxy) (Var 0)
      :: mkRule (Fun (Cons Sig) Vxy) (Var 1) :: nil.

  Lemma proj_cons_l : forall n (v : terms n) t a,
    red proj_cons (cons_term t (Vcons a v)) t.

  Proof.
    pose (Vxy := (Vcast (Vcons (Var 0) (Vcons (@Var Sig 1) Vnil)) cons_arity)).
    intros. exists (Fun (Cons Sig) Vxy). exists (Var 0). exists Hole.
    pose (s := fun i => match i with | 0 => t | S j => match j with
      | 0 => (cons_term a v) | S k => t end end).
    exists s. split. unfold proj_cons. rewrite In_cons. left. refl.
    split. 2: simpl; auto. rewrite cons_term_cons. unfold Vxy.
    apply args_eq. apply Veq_nth. intros i Hi. rewrite Vnth_map, !Vnth_cast.
    destruct i. simpl; refl. rewrite !Vnth_cons. destruct i. simpl; refl.
    cut (S (S i) < 2). intro; lia. rewrite cons_arity; auto.
  Qed.

  Lemma proj_cons_r : forall n (v : terms n) t a,
    red proj_cons (cons_term t (Vcons a v)) (cons_term a v).

  Proof.
    pose (Vxy := (Vcast (Vcons (Var 0) (Vcons (@Var Sig 1) Vnil)) cons_arity)).
    intros. exists (Fun (Cons Sig) Vxy). exists (Var 1). exists Hole.
    pose (s := fun i => match i with | 0 => t | S j => match j with
      | 0 => (cons_term a v) | S k => t end end). exists s. split.
    unfold proj_cons. rewrite In_cons. right. rewrite In_cons. left; refl.
    split. 2: simpl; auto. rewrite cons_term_cons. unfold Vxy.
    apply args_eq. apply Veq_nth. intros i Hi. rewrite Vnth_map, !Vnth_cast.
    destruct i. simpl; refl. rewrite !Vnth_cons. destruct i. simpl; refl.
    cut (S (S i) < 2). intro; lia. rewrite cons_arity; auto.
  Qed.

  Lemma proj_cons_rtc_l : forall t n (v : terms n),
    red proj_cons # (cons_term t v) t.

  Proof.
    intros. case v. simpl. apply rt_refl.
    intros t' n' v'. apply rt_step. apply proj_cons_l.
  Qed.

  Lemma proj_cons_tc_r : forall n (v : terms n) t x,
    Vin x v -> red proj_cons ! (cons_term t v) x.

  Proof.
    intro n. induction v; intros. simpl in H. tauto.
    apply tc_merge. exists (cons_term h v). split. apply proj_cons_r.
    destruct H. rewrite H. apply proj_cons_rtc_l.
    apply tc_incl_rtc. apply IHv; auto.
  Qed.

  Lemma proj_cons_fun_aux1 : forall f n m (Emn : n + S m = arity f) v1 v2 x y,
    red proj_cons # x y ->
      red proj_cons # (Fun f (Vcast (Vapp v1 (Vcons x v2)) Emn))
                      (Fun f (Vcast (Vapp v1 (Vcons y v2)) Emn)).

  Proof.
    intros f m n. induction 1. 2: apply rt_refl. apply rt_step.
    destruct H as [l H]; destruct H as [r H]; destruct H as [c H].
    destruct H as [s H]. exists l. exists r.
    exists (Cont _ Emn v1 c v2). exists s. split. destruct H; auto. simpl.
    destruct H as [_ H]. destruct H as [H3 H4]. rewrite <- H3, <- H4. auto.
    apply rt_trans with (y := Fun f (Vcast (Vapp v1 (Vcons y v2)) Emn)); auto.
  Qed.

  Lemma proj_cons_fun_aux2 : forall f n m (Emn : n + m = arity f) v v1 v2,
    (forall i (Hi : i < n), red proj_cons # (Vnth v1 Hi) (Vnth v2 Hi))
    -> red proj_cons # (Fun f (Vcast (Vapp v1 v) Emn))
                       (Fun f (Vcast (Vapp v2 v) Emn)).

  Proof.
    intro f. induction n; intros m Emn v v1 v2 Hin.
    rewrite (VO_eq v1), (VO_eq v2). simpl. apply rt_refl.
    assert (H0 : n < S n + m). lia. assert (H1 : m = S n + m - S n). lia.
    rewrite (Veq_app_cons (Vapp v1 v) H0), (Veq_app_cons (Vapp v2 v) H0).
    assert (Ve1 : forall x,
      Vsub (Vapp x v) (Veq_app_cons_aux2 H0) = (Vcast v H1)).
    intro x; pattern v at 2.
    rewrite <- (Vsub_app_r x v (Nat.le_refl (S n + m))), Vcast_sub. apply Vsub_pi.
    assert (Ve2 : forall x, Vsub (Vapp x v) (Veq_app_cons_aux1 H0) =
      (Vsub x (Veq_app_aux1 (Nat.le_succ_diag_r n)))). intro x.
    apply Veq_nth; intros. rewrite !Vnth_sub, Vnth_app.
    case (le_gt_dec (S n) (0 + i)); intro. lia. apply Vnth_eq; auto.
    rewrite (Ve1 v1), (Ve1 v2), (Ve2 v1), (Ve2 v2), !Vnth_app, !Vcast_cast.
    case (le_gt_dec (S n) n); intro H2. lia.
    set (v' := Vcast v H1); set (x := Vnth v1 H2); set (y := Vnth v2 H2).
    set (v1' := Vsub v1 (Veq_app_aux1 (Nat.le_succ_diag_r n))).
    set (v2' := Vsub v2 (Veq_app_aux1 (Nat.le_succ_diag_r n))).
    set (H3 := trans_eq (Veq_app_cons_aux3 H0) Emn).
    apply rt_trans with (y := Fun f (Vcast (Vapp v2' (Vcons x v')) H3)).
    apply IHn. intros. unfold v1', v2'. rewrite !Vnth_sub. apply Hin.
    apply proj_cons_fun_aux1. apply Hin.
  Qed.

  Lemma proj_cons_fun : forall f v1 v2,
    (forall i (Hi : i < arity f), red proj_cons # (Vnth v1 Hi) (Vnth v2 Hi))
    -> red proj_cons # (Fun f v1) (Fun f v2).

  Proof.
    intros. gen (proj_cons_fun_aux2 f (Nat.add_0_r (arity f)) Vnil v1 v2 H).
    rewrite !Vapp_nil, !Vcast_cast, !Vcast_refl; auto.
  Qed.

End BinSignatureTheory.

(***********************************************************************)
(** extend a signature with a binary symbol *)

Section MakeExtSig.

  Variable Sig : Signature.

  Inductive ext_symb : Type := Symb : Sig -> ext_symb | Pair : ext_symb.

  Definition ext_arity f :=
    match f with
      | Symb f => arity f
      | Pair => 2
    end.

  Definition beq_ext_symb f g :=
    match f, g with
      | Symb f', Symb g' => beq_symb f' g'
      | Pair, Pair => true
      | _, _ => false
    end.

  Lemma beq_ext_symb_ok : forall f g, beq_ext_symb f g = true <-> f = g.

  Proof.
    destruct f; destruct g; simpl.
    rewrite beq_symb_ok. intuition. subst s0. refl. inversion H. refl.
    intuition. discr. intuition. discr. tauto.
  Qed.

  Definition ext_sig := mkSignature ext_arity beq_ext_symb_ok.

  Definition ext := Make ext_sig Pair (eq_refl 2).

End MakeExtSig.
