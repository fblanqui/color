(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-01-27
- Sebastien Hinderer, 2004-02-10
- Pierre-Yves Strub, 2009-04-13

substitutions
*)

Set Implicit Arguments.

From CoLoR Require Import AInterpretation AContext VecUtil NatUtil LogicUtil
  ListUtil EqUtil.

Section S.

  Variable Sig : Signature.

  Notation term := (term Sig). Notation terms := (vector term).

(***********************************************************************)
(** definition of substitutions as interpretations in terms *)

  Definition I0 := mkInterpretation (Var 0) (@Fun Sig).

  Definition substitution := valuation I0.

  Definition id : substitution := fun x => Var x.

  Definition single x t : substitution :=
    fun y => if beq_nat x y then t else Var y.

(***********************************************************************)
(** application of a substitution *)

  Definition sub : substitution -> term -> term := @term_int Sig I0.

  Lemma sub_fun s f v : sub s (Fun f v) = Fun f (Vmap (sub s) v).

  Proof. refl. Qed.

  Lemma sub_id : forall t, sub id t = t.

  Proof.
    set (P := fun t => sub id t = t). change (forall t, P t).
    apply term_ind_forall; intros; unfold P. refl.
    simpl. f_equal. apply Vmap_eq_id. hyp.
  Qed.

  Lemma fun_eq_sub f ts s u : Fun f ts = sub s u ->
    {exists us, u = Fun f us} + {exists x, u = Var x}.

  Proof.
    intro H. destruct u.
    right. exists n. refl.
    left. case (eq_symb_dec f f0); intro E.
    rewrite E. exists t. refl.
    simpl in H. simplify_eq H. contr.
  Qed.

  Lemma vars_eq_sub n s u : Var n = sub s u -> exists m, u = Var m.

  Proof. intro. destruct u. exists n0. refl. simpl in H. discr. Qed.

  Lemma sub_eq s1 s2 t :
    (forall x, In x (vars t) -> s1 x = s2 x) -> sub s1 t = sub s2 t.

  Proof. intro. unfold sub. rewrite (term_int_eq I0 s1 s2 t H). refl. Qed.

  Lemma sub_eq_id s t :
    (forall x, In x (vars t) -> s x = Var x) -> sub s t = t.

  Proof. intro. trans (sub id t). apply sub_eq. hyp. apply sub_id. Qed.

  Lemma Vmap_sub_eq s1 s2 n (ts : terms n) :
    (forall x, In x (vars_vec ts) -> s1 x = s2 x) ->
    Vmap (sub s1) ts = Vmap (sub s2) ts.

  Proof.
    intro. apply Vmap_eq. apply Vforall_intro. intros. apply sub_eq. intros.
    apply H. eapply vars_vec_in. apply H1. hyp.
  Qed.

  Lemma subeq_inversion :
    forall u θ θ', sub θ u = sub θ' u -> forall x, In x (vars u) -> θ x = θ' x.

  Proof.
    intros u; pattern u; apply term_ind with
      (Q :=
        fun nu (us : terms nu) =>
          forall θ θ', Vmap (sub θ) us = Vmap (sub θ') us ->
            forall x, In x (vars_vec us) -> θ x = θ' x).
    (* var *)
    intros x θ θ'; simpl; intros Hθθ' y H.
    by case H; [intros Hxy; subst x|idtac]; tauto.

    (* fun *)
    intros f ts IHs θ θ'. simpl sub. intros Hθθ' y.
    rewrite vars_fun; intros Hvars; apply IHs; try done.
    by rewrite (fun_eq Hθθ').

    (* nil *)
    by intros θ θ' _ x; simpl; tauto.

    (* cons *)
    intros t nt ts IH IHs θ θ'; simpl; intros H; Veqtac.
    intros x Hx; case (in_app_or Hx); clear Hx; intros Hx.
    by apply IH. by apply IHs.
  Qed.

  Lemma sub_single_not_var x u t : ~In x (vars t) -> sub (single x u) t = t.

  Proof.
    pattern t; apply term_ind with (Q := fun n (ts : terms n) =>
      ~In x (vars_vec ts) -> Vmap (sub (single x u)) ts = ts); intros.
    simpl in *. unfold single. case_beq_nat x x0. tauto. refl.
    simpl. rewrite vars_fun in H0. rewrite H. refl. hyp.
    refl. simpl. simpl in H1. rewrite notin_app in H1. destruct H1.
    rewrite H. 2: hyp. rewrite H0. 2: hyp. refl.
  Qed.

(***********************************************************************)
(** composition *)

  Definition sub_comp (s1 s2 : substitution) : substitution :=
    fun x => sub s1 (s2 x).

  Lemma sub_sub s1 s2 t : sub s1 (sub s2 t) = sub (sub_comp s1 s2) t.

  Proof.
    set (P := fun t => sub s1 (sub s2 t) = sub (sub_comp s1 s2) t).
    change (P t). apply term_ind_forall with (P := P); intros; unfold P.
    refl. simpl. f_equal. rewrite Vmap_map. apply Vmap_eq. hyp.
  Qed.

  Lemma sub_comp_assoc s1 s2 s3 x :
    sub_comp (sub_comp s1 s2) s3 x = sub_comp s1 (sub_comp s2 s3) x.

  Proof. unfold sub_comp. rewrite sub_sub. refl. Qed.

(***********************************************************************)
(** extension of a substitution *)

  Definition extend (s : substitution) x v : substitution :=
    fun y => if beq_nat y x then v else s y.

  Lemma sub_extend_notin s x v u :
    ~In x (vars u) -> sub (extend s x v) u = sub s u.

  Proof.
    set (s' := extend s x v). pattern u.
    apply term_ind with (Q := fun n (us : terms n) =>
      ~In x (vars_vec us) -> Vmap (sub s') us = Vmap (sub s) us); clear u.
    intro. simpl. split_all. unfold s', extend.
    case_beq_nat x0 x; congruence.
    intros f us. rewrite vars_fun. simpl. intros. apply args_eq.
    auto. refl.
    intros u n us. simpl. rewrite in_app. split_all.
    apply Vcons_eq_intro; intuition.
  Qed.

  Lemma sub_comp_single_extend s x v (t : term) :
    sub (sub_comp s (single x v)) t = sub (extend s x (sub s v)) t.

  Proof.
    apply sub_eq. intros. unfold sub_comp, single, extend.
    case_beq_nat x x0. rewrite Nat.eqb_refl. refl.
    rewrite (beq_com beq_nat_ok) in H0. rewrite H0. refl.
  Qed.

  Lemma sub_comp_single s x (u : term) : s x = sub s u ->
    forall t, sub (sub_comp s (single x u)) t = sub s t.

  Proof.
    intros. set (s' := sub_comp s (single x u)). pattern t.
    apply term_ind with (Q := fun n (ts : terms n) =>
      Vmap (sub s') ts = Vmap (sub s) ts); clear t.
    intro. unfold s', sub_comp, single. simpl. case_beq_nat x x0; auto.
    intros f v IH. rewrite !sub_fun. f_equal. hyp.
    refl. intros. simpl. apply Vcons_eq_intro; hyp.
  Qed.

(***********************************************************************)
(** substitution lemma for interpretations *)

  Section substitution_lemma.

    Variable I : interpretation Sig.

    Definition beta (xint : valuation I) (s : substitution) x :=
      term_int xint (s x).

    Lemma substitution_lemma xint s t :
      term_int xint (sub s t) = term_int (beta xint s) t.

    Proof.
      pattern t; eapply term_ind with (Q := fun n (ts : terms n) =>
        Vmap (term_int xint) (Vmap (sub s) ts)
        = Vmap (term_int (beta xint s)) ts).
      intro x. simpl. refl.
      intros f ts. simpl. intro H. f_equal. hyp.
      simpl. refl.
      intros. simpl. rewrite H, <- H0. refl.
    Qed.

  End substitution_lemma.

(***********************************************************************)
(** variables of a substitution *)

  Section vars.

    Variable s : substitution.

    Fixpoint svars (l : variables) : variables :=
      match l with
      | nil => nil
      | x :: l' => vars (s x) ++ svars l'
      end.

    Lemma in_svars_intro x y :
      forall l, In x (vars (s y)) -> In y l -> In x (svars l).

    Proof.
      induction l; simpl; intros. contr. destruct H0.
      subst a. apply in_appl. exact H.
      ded (IHl H H0). apply in_appr. exact H1.
    Qed.

    Lemma in_svars_elim x :
      forall l, In x (svars l) -> exists y, In y l /\ In x (vars (s y)).

    Proof.
      induction l; simpl; intros. contr. ded (in_app_or H). destruct H0.
      exists a. auto. ded (IHl H0). do 2 destruct H1. exists x0. auto.
    Qed.

    Arguments in_svars_elim [x l] _.

    Lemma svars_app l2 : forall l1, svars (l1 ++ l2) = svars l1 ++ svars l2.

    Proof.
      induction l1; simpl; intros. refl. rewrite IHl1, app_ass. refl.
    Qed.

    Lemma incl_svars l1 l2 : incl l1 l2 -> incl (svars l1) (svars l2).

    Proof.
      intros. unfold incl. intros. ded (in_svars_elim H0). do 2 destruct H1.
      eapply in_svars_intro. apply H2. apply H. exact H1.
    Qed.

    Lemma vars_sub : forall t, vars (sub s t) = svars (vars t).

    Proof.
      apply term_ind with (Q := fun n (v : terms n) =>
        vars_vec (Vmap (sub s) v) = svars (vars_vec v)).
      simpl. intro. rewrite <- app_nil_end. refl.
      intros. simpl sub. rewrite !vars_fun. hyp.
      refl.
      intros. simpl. rewrite H, svars_app. f_equal. hyp.
    Qed.

    Lemma incl_vars_sub l r :
      incl (vars r) (vars l) -> incl (vars (sub s r)) (vars (sub s l)).

    Proof. intros. rewrite !vars_sub. apply incl_svars. hyp. Qed.

  End vars.

(***********************************************************************)
(** domain of a substitution *)

  Definition dom_incl (s : substitution) (l : variables) :=
    forall x, ~In x l -> s x = Var x.

  Definition sub_eq_dom (s1 s2 : substitution) (l : variables) :=
    forall x, In x l -> s1 x = s2 x.

  Lemma sub_eq_dom_incl s1 s2 l1 l2 :
    sub_eq_dom s1 s2 l2 -> incl l1 l2 -> sub_eq_dom s1 s2 l1.

  Proof. unfold sub_eq_dom. auto. Qed.

  Lemma sub_eq_dom_incl_sub s1 s2 l : sub_eq_dom s1 s2 l ->
    forall t, incl (vars t) l -> sub s1 t = sub s2 t.

  Proof.
    intros until t. unfold sub_eq_dom in H. apply term_ind with
      (P := fun t => incl (vars t) l -> sub s1 t = sub s2 t)
      (Q := fun n (ts : terms n) =>
              incl (vars_vec ts) l -> Vmap (sub s1) ts = Vmap (sub s2) ts).
    (* var *)
    unfold incl. simpl. intuition.
    (* fun *)
    intros. rewrite !sub_fun. f_equal. apply H0. rewrite vars_fun in H1. hyp.
    (* nil *)
    refl.
    (* cons *)
    intros. rewrite vars_vec_cons in H2. unfold incl in H2.
    ded (incl_app_elim H2). destruct H3. simpl. apply Vcons_eq_intro; auto.
  Qed.

  Lemma sub_eq_vars_sub s1 s2 t :
    sub_eq_dom s1 s2 (vars t) -> sub s1 t = sub s2 t.

  Proof. intro. eapply sub_eq_dom_incl_sub. apply H. refl. Qed.

(***********************************************************************)
(** union of 2 substitutions ordered by the domain of the first:
union s1 s2 x = s1 x if s1 x <> x, and s2 x otherwise *)

  Section union.

    Variables s1 s2 : substitution.

    Definition union : substitution := fun x =>
      match eq_term_dec (s1 x) (Var x) with
      | left _ => s2 x
      | right _ => s1 x
      end.

    Variables l1 l2 : variables.

    Definition compat := forall x : variable, In x l1 -> In x l2 -> s1 x = s2 x.

    Variables (hyp1 : dom_incl s1 l1) (hyp2 : dom_incl s2 l2) (hyp : compat).

    Lemma union_correct1 : sub_eq_dom union s1 l1.

    Proof.
      unfold sub_eq_dom, union. intros.
      case (eq_term_dec (s1 x) (Var x)); intros.
      case (In_dec eq_nat_dec x l2); intro. apply sym_eq. auto.
      ded (hyp2 _ n). rewrite e, H0. refl. refl.
    Qed.

    Lemma union_correct2 : sub_eq_dom union s2 l2.

    Proof.
      unfold sub_eq_dom, union. intros.
      case (eq_term_dec (s1 x) (Var x)); intros.
      refl. case (In_dec eq_nat_dec x l1); intro. auto.
      ded (hyp1 _ n0). contr.
    Qed.

    Lemma sub_union1 t : incl (vars t) l1 -> sub union t = sub s1 t.

    Proof. intro. eapply sub_eq_dom_incl_sub. apply union_correct1. hyp. Qed.

    Lemma sub_union2 t : incl (vars t) l2 -> sub union t = sub s2 t.

    Proof. intro. eapply sub_eq_dom_incl_sub. apply union_correct2. hyp. Qed.

  End union.

(***********************************************************************)
(** union of 2 substitutions ordered by some index n:
maxvar_union n s1 s2 x = s1 x if x < n, and s2 x otherwise *)

  Section maxvar_union.

    Variables (n : nat) (s1 s2 : substitution).

    Definition maxvar_union : substitution := fun x =>
      match lt_ge_dec x n with
      | left _ => s1 x
      | _ => s2 x
      end.

  End maxvar_union.

(***********************************************************************)
(** restriction of a substitution *)

  Notation Inb := (Inb eq_nat_dec).

  Definition restrict (s : substitution) (l : variables) : substitution :=
    fun x => if Inb x l then s x else Var x.

  Lemma restrict_var s l x : In x l -> restrict s l x = s x.

  Proof.
    intro. unfold restrict. assert (Inb x l = true).
    apply Inb_intro. hyp. rewrite H0. refl.
  Qed.

  Lemma dom_incl_restrict s l : dom_incl (restrict s l) l.

  Proof.
    unfold dom_incl. intros. ded (Inb_elim eq_nat_dec _ _ H). unfold restrict.
    rewrite H0. refl.
  Qed.

  Lemma sub_eq_restrict s : forall l, sub_eq_dom (restrict s l) s l.

  Proof.
    unfold sub_eq_dom, restrict. induction l; simpl. intros. contr.
    intro. case (eq_nat_dec x a); intuition.
  Qed.

  Lemma sub_restrict s t : sub s t = sub (restrict s (vars t)) t.

  Proof. apply sym_eq. apply sub_eq_vars_sub. apply sub_eq_restrict. Qed.

  Lemma sub_restrict_incl s (l r : term) :
    incl (vars r) (vars l) -> sub s r = sub (restrict s (vars l)) r.

  Proof.
    intro. rewrite sub_restrict. apply sub_eq_vars_sub. unfold sub_eq_dom.
    intros. unfold restrict.
    assert (Inb x (vars r) = true). apply Inb_intro. hyp.
    assert (Inb x (vars l) = true). apply Inb_intro. apply H. hyp.
    rewrite H1, H2. refl.
  Qed.

(***********************************************************************)
(** substitution on contexts *)

  Notation context := (context Sig).

  Fixpoint subc (s : substitution) (c : context) : context :=
    match c with
    | Hole => Hole
    | Cont f H v1 c' v2 =>
      Cont f H (Vmap (sub s) v1) (subc s c') (Vmap (sub s) v2)
    end.

  Lemma sub_fill s u : forall C, sub s (fill C u) = fill (subc s C) (sub s u).

  Proof.
    induction C; intros. refl. simpl subc. simpl fill. simpl sub.
    f_equal. rewrite Vmap_cast, Vmap_app. simpl Vmap. rewrite IHC. refl.
  Qed.

(***********************************************************************)
(** relation wrt subterm *)

  Lemma subterm_eq_sub u t s :
    subterm_eq u t -> subterm_eq (sub s u) (sub s t).

  Proof.
    unfold subterm_eq. intro. destruct H as [C]. subst t. exists (subc s C).
    apply sub_fill.
  Qed.

  Lemma subterm_sub u t s : subterm u t -> subterm (sub s u) (sub s t).

  Proof.
    unfold subterm. intro. destruct H as [C]. intuition. destruct C. intuition.
    subst t. exists (subc s (Cont f e t0 C t1)). split_all. discr.
    apply sub_fill.
  Qed.

  Lemma subterm_eq_sub_elim : forall u t s, subterm_eq t (sub s u) ->
    exists v, subterm_eq v u
              /\ match v with
                 | Var x => subterm_eq t (s x)
                 | Fun f ts => t = sub s v
                 end.

  Proof.
    intro u; pattern u; apply term_ind_forall; clear u.
    (* var *)
    intros x t s ht. exists (Var x). intuition.
    (* fun *)
    intros f ts IH t s ht. destruct (subterm_eq_split ht).
    exists (Fun f ts). intuition.
    destruct (subterm_fun_elim H) as [v [hv1 hv2]].
    change (Vin v (Vmap (sub s) ts)) in hv1.
    destruct (Vin_map hv1) as [w [hw1 hw2]]. subst.
    destruct (Vforall_in IH hw1 t s hv2) as [x [hx1 hx2]]. exists x. split.
    trans w. hyp. apply subterm_strict. apply subterm_fun. hyp. hyp.
  Qed.

(***********************************************************************)
(** function generating the sequence of terms Var 0, .., Var (n-1) *)

  (*COQ: cannot be declared of type (terms n),
    otherwise (apply Vnth_vec_of_val) does not work in Lemma Vnth_fresh_vars*)
  Definition fresh_vars n := @vec_of_val _ I0 (@Var Sig) n.

  Lemma Vnth_fresh_vars n i (h : i<n) : Vnth (fresh_vars n) h = Var i.

  Proof. unfold fresh_vars. apply Vnth_vec_of_val. Qed.

  Definition sub_vars n (ts : terms n) : substitution := val_of_vec I0 ts.

  Lemma sub_fresh_vars n (ts : terms n) :
    ts = Vmap (sub (sub_vars ts)) (fresh_vars n).

  Proof.
    apply Veq_nth. intros. rewrite Vnth_map, Vnth_fresh_vars.
    simpl. unfold sub_vars. rewrite val_of_vec_eq with (h:=ip). refl.
  Qed.

(***********************************************************************)
(** function generating the sequence of terms Var x0, .., Var (x0+n-1) *)

  Fixpoint fresh (x0 n : nat) : terms n :=
    match n as n return terms n with
    | 0 => Vnil
    | S n' => Vcons (Var x0) (fresh (S x0) n')
    end.

  Lemma fresh_plus :
    forall n1 n2 x0, fresh x0 (n1+n2) = Vapp (fresh x0 n1) (fresh (x0+n1) n2).

  Proof.
    induction n1; simpl; intros. rewrite Nat.add_0_r. refl.
    apply Vtail_eq. rewrite IHn1.
    assert (S x0 + n1 = x0 + S n1). lia. rewrite H. refl.
  Qed.

  Lemma fresh_tail x0 : forall n, fresh (S x0) n = Vtail (fresh x0 (S n)).

  Proof. induction n; simpl; intros; refl. Qed.

  Lemma Vnth_fresh :
    forall n i (h : i < n) x0, Vnth (fresh x0 n) h = Var (x0+i).

  Proof.
    induction n; simpl. intros. absurd (i<0); lia. intro. destruct i. auto.
    intros. assert (x0+S i=(S x0)+i). lia. rewrite H. apply IHn.
  Qed.

  Lemma Vbreak_fresh p :
    forall n k, Vbreak (fresh k (n+p)) = (fresh k n, fresh (k+n) p).

  Proof.
    induction n; simpl; intros. rewrite Nat.add_0_r. refl.
    rewrite IHn. simpl. rewrite Nat.add_succ_r. refl.
  Qed.

(***********************************************************************)
(** generates a list of variables *)

  Fixpoint freshl (x0 n : nat) : list variable :=
    match n with
    | 0 => nil
    | S n' => x0 :: freshl (S x0) n'
    end.

  Lemma in_freshl x :
    forall n x0, ~In x (freshl x0 n) -> x < x0 \/ x >= x0 + n.

  Proof. induction n; simpl; intuition. lia. ded (IHn (S x0) H1). lia. Qed.

  Arguments in_freshl [x n x0] _.

(***********************************************************************)
(** given a variable [x0] and a vector [v] of [n] terms, [fsub x0 n v]
is the substitution {x0+1 -> v1, .., x0+n -> vn} *)

  (*COQ: cannot be declared as substitution,
  otherwise we get problems when trying to apply Lemma fsub_inf*)
  Definition fsub x0 n (ts : terms n) x :=
    match le_lt_dec x x0 with
    | left _ => (* x <= x0 *) Var x
    | right h1 => (* x0 < x *)
      match le_lt_dec x (x0+n) with
      | left h2 => (* x <= x0+n *) Vnth ts (lt_pm h1 h2)
      | _ => Var x (* x0+n < x *)
      end
    end.

  Lemma fsub_inf x0 n (ts : terms n) x : x <= x0 -> fsub x0 ts x = Var x.

  Proof.
    intro. unfold fsub. case (le_lt_dec x x0). auto. intro. absurd (n<x); lia.
  Qed.

  Lemma fsub_sup x0 n (ts : terms n) x : x > x0+n -> fsub x0 ts x = Var x.

  Proof.
    intro. unfold fsub. case (le_lt_dec x x0). auto. intro.
    case (le_lt_dec x (x0+n)). intro. absurd (x>x0+n); lia. auto.
  Qed.

  Lemma fsub_nth x0 n (ts : terms n) x (h1 : x0 < x) (h2 : x <= x0+n) :
    fsub x0 ts x = Vnth ts (lt_pm h1 h2).

  Proof.
    unfold fsub. case (le_lt_dec x x0); intro. lia.
    case (le_lt_dec x (x0+n)); intro. apply Vnth_eq. refl. lia.
  Qed.

  Lemma fsub_cons x0 t n (ts : terms n) x :
    x = x0+1 -> fsub x0 (Vcons t ts) x = t.

  Proof.
    intro. subst x. unfold fsub. case (le_lt_dec (x0+1) x0); intro.
    lia. case (le_lt_dec (x0+1) (x0+S n)); intro. rewrite Vnth_cons_head.
    refl. lia. lia.
  Qed.

  Lemma fsub_cons_rec x0 t n (ts : terms n) x k :
    x = x0+2+k -> fsub x0 (Vcons t ts) x = fsub (x0+1) ts x.

  Proof.
    intro. subst x. unfold fsub.
    destruct (le_lt_dec (x0+2+k) x0). lia.
    destruct (le_lt_dec (x0+2+k) (x0+1)). lia.
    destruct (le_lt_dec (x0+2+k) (x0+S n));
      destruct (le_lt_dec (x0+2+k) (x0+1+n)); try lia.
    rewrite Vnth_cons. destruct (lt_ge_dec 0 (x0+2+k-x0-1)).
    apply Vnth_eq. clear. lia. lia. refl.
  Qed.

  Lemma fsub_cons_rec0 x0 t n (ts : terms n) x :
    x = x0+2 -> fsub x0 (Vcons t ts) x = fsub (x0+1) ts x.

  Proof. intro. eapply fsub_cons_rec with (k := 0). lia. Qed.

  Lemma fsub_nil x0 x : fsub x0 Vnil x = Var x.

  Proof.
    unfold fsub. case (le_lt_dec x x0); intro. refl.
    case (le_lt_dec x (x0+0)); intro. lia. refl.
  Qed.

  Lemma sub_fsub_inf n (ts : terms n) m :
    forall t, maxvar t <= m -> sub (fsub m ts) t = t.

  Proof.
    set (P := fun t => maxvar t <= m -> sub (fsub m ts) t = t).
    change (forall t, P t). apply term_ind_forall.
    (* var *)
    unfold P, fsub. simpl. intros. case (le_lt_dec v m); intro. refl.
    case (le_lt_dec v (m+n)); intro. lia. refl.
    (* fun *)
    intros. unfold P. intro. simpl sub. f_equal.
    apply Vmap_eq_id. eapply Vforall_impl. apply H. intros. apply H2.
    eapply maxvar_le_arg with (f := f). apply H0. hyp.
  Qed.

  Lemma Vmap_fsub_fresh x0 n (ts : terms n) :
    Vmap (sub (fsub x0 ts)) (fresh (S x0) n) = ts.

  Proof.
    intros. apply Vmap_eq_nth. intros. rewrite Vnth_fresh. simpl.
    set (x := S(x0+i)). assert (h1 : x0<x). unfold x. lia.
    assert (h2 : x<=x0+n). unfold x. lia.
    assert (fsub x0 ts x = Vnth ts (lt_pm h1 h2)). apply fsub_nth.
    rewrite H. apply Vnth_eq. unfold x. lia.
  Qed.

  Lemma fsub_dom x0 n :
    forall ts : terms n, dom_incl (fsub x0 ts) (freshl (x0+1) n).

  Proof.
    unfold dom_incl. induction ts; simpl; intros. apply fsub_nil.
    split_all. ded (in_freshl H0). destruct H1.
    apply fsub_inf. lia. apply fsub_sup. lia.
  Qed.

  Lemma fill_sub n f i vi j vj e s l : n >= maxvar l ->
    fill (Cont f e vi Hole vj) (sub s l)
    = sub (maxvar_union (S n) s (fsub n (Vapp vi vj)))
          (fill (Cont f e (fresh (S n) i) Hole (fresh (S n+i) j)) l).

  Proof.
    intro. rename H into Hn. simpl. apply args_eq. rewrite Vmap_cast, Vmap_app.
    simpl. apply Vcast_eq_intro. apply Vapp_eq_intro.
    (* vi *)
    apply Veq_nth; intros. rewrite Vnth_map, Vnth_fresh. simpl.
    unfold maxvar_union. case (lt_ge_dec (S(n+i0)) (S n)); intro. lia.
    unfold fsub. case (le_lt_dec (S(n+i0)) n); intro. lia.
    case (le_lt_dec (S(n+i0)) (n+(i+j))); intro.
    rewrite Vnth_app. case (le_gt_dec i (S(n+i0)-n-1)); intro. lia.
    apply Vnth_eq. clear; lia. lia.
    (* cons *)
    apply Vcons_eq_intro. apply sub_eq. intros. ded (vars_max H).
    unfold maxvar_union. case (lt_ge_dec x (S n)); intro. refl. lia.
    (* v2 *)
    apply Veq_nth; intros. rewrite Vnth_map, Vnth_fresh. simpl.
    unfold maxvar_union. case (lt_ge_dec (S(n+i+i0)) (S n)); intro.
    lia. unfold fsub. case (le_lt_dec (S(n+i+i0)) n); intro. lia.
    case (le_lt_dec (S(n+i+i0)) (n+(i+j))); intro. rewrite Vnth_app.
    case (le_gt_dec i (S(n+i+i0)-n-1)); intro. apply Vnth_eq.
    clear; lia. lia. lia.
  Qed.

(***********************************************************************)
(** renamings *)

  Section sub_inv.

    Variables (s1 s2 : substitution)
              (hyp : forall x, sub s1 (sub s2 (Var x)) = Var x).

    Lemma sub_inv : forall t, sub s1 (sub s2 t) = t.

    Proof.
      intro t; pattern t; apply term_ind with (Q := fun n (ts : terms n) =>
        Vmap (sub s1) (Vmap (sub s2) ts) = ts); simpl; intros.
      apply hyp. rewrite H. refl. refl. rewrite H, H0. refl.
    Qed.

  End sub_inv.

  Section swap.

    Definition swap x y := single x (Var y).

    Lemma swap_intro s x y t : ~In y (vars t) ->
      sub s t = sub (sub_comp s (swap y x)) (sub (swap x y) t).

    Proof.
      pattern t; apply term_ind with (Q := fun n (ts : terms n) =>
        ~In y (vars_vec ts) ->
        Vmap (sub s) ts
        = Vmap (sub (sub_comp s (swap y x))) (Vmap (sub (swap x y)) ts));
      clear t; intros.
      simpl. unfold swap, single, sub_comp. case_beq_nat x x0. simpl.
      rewrite (beq_refl beq_nat_ok). refl. simpl. case_beq_nat y x0.
      simpl in H. tauto. refl. rewrite !sub_fun, H. refl.
      rewrite vars_fun in H0. hyp. refl. simpl in *. rewrite in_app in H1.
      rewrite H0, H. refl. tauto. tauto.
    Qed.

    Lemma swap_id x t : sub (swap x x) t = t.

    Proof.
      apply sub_eq_id. intros. unfold swap, single. case_beq_nat x x0; refl.
    Qed.

  End swap.

End S.

Arguments swap [Sig] _ _ _.
Arguments sub_inv [Sig s1 s2] _ _.
Arguments fun_eq_sub [Sig f ts s u] _.
Arguments sub_restrict_incl [Sig] _ [l r] _.
Arguments fresh_vars [Sig] _.
Arguments fresh [Sig] _ _.
Arguments subterm_eq_sub_elim [Sig u t0 s] _ : rename.

(***********************************************************************)
(** tactics *)

(* to prove a goal of the form: sub (single x t) (Var x) = t. *)

Ltac single := simpl; unfold single; rewrite Nat.eqb_refl; refl.

(* to prove a goal of the form: exists s, sub s (Var x) = t. *)

Ltac exists_single x t := exists (single x t); single.
