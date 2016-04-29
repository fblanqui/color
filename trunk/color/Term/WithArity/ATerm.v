(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-02-09
- Frederic Blanqui, 2005-02-17

algebraic terms with fixed arity
*)

Set Implicit Arguments.

From Coq Require Export Vector.
From CoLoR Require Export ASignature.
From Coq Require Import Max.
From CoLoR Require Import ListUtil LogicUtil EqUtil BoolUtil NatUtil VecUtil
     VecMax ListMax.

Notation variables := (list variable) (only parsing).

Section S.

  Variable Sig : Signature.

(***********************************************************************)
(** terms *)

  (*COQ: we do not use the induction principle generated by Coq since it
     is not good because the argument of Fun is a vector *)

  Unset Elimination Schemes.

  Inductive term : Type :=
  | Var : variable -> term
  | Fun : forall f : Sig, vector term (arity f) -> term.

  Set Elimination Schemes.

  Notation terms := (vector term).

(***********************************************************************)
(** induction principles *)

  Section term_rect.

    Variables
      (P : term -> Type)
      (Q : forall n, terms n -> Type).

    Hypotheses
      (H1 : forall x, P (Var x))
      (H2 : forall f v, Q v -> P (Fun f v))
      (H3 : Q Vnil)
      (H4 : forall t n (v : terms n), P t -> Q v -> Q (Vcons t v)).

    Fixpoint term_rect t : P t :=
      match t as t return P t with
        | Var x => H1 x
        | Fun f v =>
          let fix terms_rect n (v : terms n) : Q v :=
            match v as v return Q v with
              | Vnil => H3
              | Vcons t' v' => H4 (term_rect t') (terms_rect _ v')
            end
	    in H2 f (terms_rect (arity f) v)
      end.

  End term_rect.

  Definition term_ind (P : term -> Prop) (Q : forall n, terms n -> Prop) :=
    term_rect P Q.

  Section term_ind_comb.

    Variables
      (Pt : term -> Prop)
      (Ps : forall n, terms n -> Prop).

    Hypotheses
      (Hvar : forall x, Pt (Var x))
      (Hfun : forall f ts, Ps ts -> Pt (Fun f ts))
      (Hnil : Ps Vnil)
      (Hcns : forall t n (ts : terms n), Pt t -> Ps ts -> Ps (Vcons t ts)).

    Lemma term_ind_comb : (forall t, Pt t) /\ (forall n (ts : terms n), Ps ts).

    Proof.
      split; [by apply term_ind with (Q := Ps) | intros n ts].
      induction ts; [exact Hnil | apply Hcns; [idtac | hyp]].
      by apply term_ind with (Q := Ps) .
    Qed.

  End term_ind_comb.

  Lemma term_ind_forall : forall (P : term -> Prop)
    (H1 : forall v, P (Var v))
    (H2 : forall f v, Vforall P v -> P (Fun f v)),
    forall t, P t.

  Proof.
    intros. apply term_ind with (Q := Vforall P). exact H1. exact H2.
    exact I. intros. simpl. split; hyp.
  Qed.

  Lemma term_ind_forall_cast : forall (P : term -> Prop)
    (Hvar : forall x, P (Var x))
    (Hfun : forall f n (ts : terms n) (h : n = arity f),
      Vforall P ts -> P (Fun f (Vcast ts h))),
    forall t, P t.

  Proof.
    intros. apply term_ind_forall. hyp. intros.
    rewrite <- (Vcast_refl v (refl_equal (arity f))). apply Hfun. hyp.
  Qed.

  Lemma term_ind_forall2 : forall (P : term -> Prop)
    (H1 : forall v, P (Var v))
    (H2 : forall f v, (forall t, Vin t v -> P t) -> P (Fun f v)),
    forall t, P t.

  Proof.
    intros. apply term_ind
    with (Q := fun n (ts : terms n) => forall t, Vin t ts -> P t).
    exact H1. exact H2. contr. simpl. intuition. subst t1. exact H.
  Qed.

(***********************************************************************)
(** equality *)

  Lemma var_eq : forall x x', x = x' -> Var x = Var x'.

  Proof. intros. rewrite H. refl. Qed.

  Lemma args_eq : forall f v v', v = v' -> Fun f v = Fun f v'.

  Proof. intros. rewrite H. refl. Qed.

  Lemma fun_eq : forall f v w, Fun f v = Fun f w -> v = w.

  Proof.
    intros. inversion H. apply (inj_existT (@eq_symb_dec _) H1).
  Qed.

  Lemma symb_eq : forall f us g vs, Fun f us = Fun g vs -> f = g.

  Proof.
    intros. inversion H. refl.
  Qed.

  Lemma fun_eq_cast : forall f g m (ts : terms m) n (us : terms n)
    (p : m = arity f) (q : n = arity g) (r : m=n), f = g ->
    us = Vcast ts r -> Fun f (Vcast ts p) = Fun g (Vcast us q).

  Proof.
    destruct ts; intros.
    (* Vnil *)
    subst g. apply args_eq. destruct n. 2: discr. VOtac. assert (p=q).
    apply eq_unique. subst q. apply Vcast_eq_intro. auto.
    (* Vcons *)
    subst g. apply args_eq. destruct n0. discr. rewrite H0, Vcast_cast.
    assert (trans_eq r q = p). apply eq_unique. rewrite H. refl.
  Qed.

  Lemma fun_eq_intro : forall f ts g us (h : f = g),
    us = Vcast ts (f_equal (@arity Sig) h) -> Fun f ts = Fun g us.

  Proof.
    intros. rewrite <- (Vcast_refl ts (refl_equal (arity f))),
            <- (Vcast_refl us (refl_equal (arity g))).
    eapply fun_eq_cast. hyp. apply H.
  Qed.

  Lemma symb_arg_eq :  forall f us g vs (h : f = g),
    Fun f us = Fun g vs -> vs = Vcast us (f_equal (@arity Sig) h).

  Proof.
    intros.
    assert (q' : arity f = arity g). rewrite h; auto.
    assert (H1 : (Vcast us q') = (Vcast us (f_equal (@arity Sig) h))).
    apply Vcast_pi.
    gen (fun_eq_intro us h H1). intro. rewrite H0 in H.
    gen (fun_eq H). intro T; rewrite <- T. apply Vcast_pi.
  Qed.

(***********************************************************************)
(** decidability of equality *)

  Fixpoint beq_term (t u : term) :=
    match t, u with
      | Var x, Var y => beq_nat x y
      | Fun f ts, Fun g us =>
        let fix beq_terms n (ts : terms n) p (us : terms p) :=
          match ts, us with
            | Vnil, Vnil => true
            | Vcons t ts', Vcons u us' =>
              beq_term t u && beq_terms _ ts' _ us'
            | _, _ => false
          end
          in beq_symb f g && beq_terms _ ts _ us
      | _, _ => false
    end.

  Lemma beq_terms : forall n (ts : terms n) p (us : terms p),
    (fix beq_terms n (ts : terms n) p (us : terms p) :=
      match ts, us with
        | Vnil, Vnil => true
        | Vcons t ts', Vcons u us' => beq_term t u && beq_terms _ ts' _ us'
        | _, _ => false
      end) _ ts _ us = beq_vec beq_term ts us.

  Proof.
    induction ts; destruct us; refl.
  Qed.

  Lemma beq_fun : forall f ts g us,
    beq_term (Fun f ts) (Fun g us) = beq_symb f g && beq_vec beq_term ts us.

  Proof. intros. rewrite <- beq_terms. refl. Qed.

  Lemma beq_term_ok : forall t u, beq_term t u = true <-> t = u.

  Proof.
    intro t. pattern t. apply term_ind_forall2; destruct u.
    simpl. rewrite beq_nat_ok. intuition. inversion H. refl.
    intuition; discr. intuition; discr.
    rewrite beq_fun. split; intro. destruct (andb_elim H0).
    rewrite beq_symb_ok in H1. subst f0. apply args_eq.
    ded (beq_vec_ok_in1 H H2). rewrite <- H1. rewrite Vcast_refl. refl.
    inversion H0 as [[h0 h1]]. clear h1. subst f0. simpl.
    apply andb_intro. apply (beq_refl (@beq_symb_ok Sig)).
    apply beq_vec_ok_in2. exact H. refl.
  Qed.

  Definition eq_term_dec := dec_beq beq_term_ok.

(* old version using Eqdep's axiom: *)

(*Lemma eq_term_dec : forall t u : term, {t=u}+{~t=u}.

Proof.
intro. pattern t. apply term_rect with
  (Q := fun n (ts : terms n) => forall u, {ts=u}+{~ts=u}); clear t.
(* var *)
intros. destruct u. case (eq_nat_dec x n); intro. subst n. auto.
right. unfold not. intro. injection H. auto.
right. unfold not. intro. discr.
(* fun *)
intros f ts H u. destruct u. right. unfold not. intro. discr.
case (eq_symbol_dec f f0); intro. subst f0. case (H v); intro. subst ts. auto.
right. intro. injection H0. intro. assert (ts=v).
(* FIXME: can be removed ? *) From CoLoR Require Import Eqdep.
apply (inj_pair2 Sig (fun f => terms (arity f))). hyp. auto.
right. unfold not. intro. injection H0. intros. auto.
(* nil *)
intro. VOtac. auto.
(* cons *)
intros. VSntac u. case (X (Vhead u)); intro. rewrite e.
case (X0 (Vtail u)); intro. rewrite e0. auto.
right. unfold not. intro. injection H0. intro. assert (v = Vtail u).
apply (inj_pair2 nat (fun n => terms n)). hyp. auto.
right. unfold not. intro. injection H0. intros. auto.
Defined.*)

(***********************************************************************)
(** maximal variable index in a term *)

  Fixpoint maxvar (t : term) : nat :=
    match t with
      | Var x => x
      | Fun f v => Vmax (Vmap maxvar v)
    end.

  Definition maxvars n (ts : terms n) := Vmax (Vmap maxvar ts).

  Lemma maxvars_cons : forall t n (ts : terms n),
    maxvars (Vcons t ts) = max (maxvar t) (maxvars ts).

  Proof. refl. Qed.

  Lemma maxvar_fun : forall f ts, maxvar (Fun f ts) = maxvars ts.

  Proof. refl. Qed.

  Lemma maxvar_var : forall k x, maxvar (Var x) <= k -> x <= k.

  Proof.
    intros. simpl. intuition.
  Qed.

  Definition maxvar_le k t := maxvar t <= k.

  Lemma maxvar_le_fun : forall m f ts,
    maxvar (Fun f ts) <= m -> Vforall (maxvar_le m) ts.

  Proof.
    intros until ts. rewrite maxvar_fun. intro. gen (Vmax_forall H).
    clear H. intro H. gen (Vforall_map_elim H). intuition.
  Qed.

  Lemma maxvar_le_arg : forall f ts m t,
    maxvar (Fun f ts) <= m -> Vin t ts -> maxvar t <= m.

  Proof.
    intros. assert (Vforall (maxvar_le m) ts). apply maxvar_le_fun. hyp.
    change (maxvar_le m t). eapply Vforall_in with (n := arity f). apply H1.
    hyp.
  Qed.

  Lemma maxvars_cast : forall n (ts : terms n) p (e : n=p),
    maxvars (Vcast ts e) = maxvars ts.

  Proof.
    induction ts; destruct p; intros; try omega.
    rewrite Vcast_refl. refl.
    rewrite Vcast_cons, !maxvars_cons, IHts. refl.
  Qed.

(***********************************************************************)
(** list of variables in a term:
a variable occurs in the list as much as it has occurrences in t *)

  Fixpoint vars (t : term) : variables :=
    match t with
      | Var x => x :: nil
      | Fun f v =>
        let fix vars_vec n (ts : terms n) : variables :=
          match ts with
            | Vnil => nil
            | Vcons t' ts' => vars t' ++ vars_vec _ ts'
          end
          in vars_vec (arity f) v
    end.

  Fixpoint vars_vec n (ts : terms n) : variables :=
    match ts with
      | Vnil => nil
      | Vcons t' ts' => vars t' ++ vars_vec ts'
    end.

  Lemma vars_fun : forall f ts, vars (Fun f ts) = vars_vec ts.

  Proof. auto. Qed.

  Lemma vars_vec_cast : forall n (ts : terms n) m (h : n=m),
    vars_vec (Vcast ts h) = vars_vec ts.

  Proof.
    induction ts; intros; destruct m; simpl; try discr.
    rewrite Vcast_refl. refl.
    rewrite Vcast_cons. apply (f_equal (fun l => vars h ++ l)). apply IHts.
  Qed.

  Lemma vars_vec_app : forall n1 (ts1 : terms n1) n2 (ts2 : terms n2),
    vars_vec (Vapp ts1 ts2) = vars_vec ts1 ++ vars_vec ts2.

  Proof.
    induction ts1; intros; simpl. refl. rewrite app_ass. f_equal. apply IHts1.
  Qed.

  Lemma vars_vec_cons : forall t n (ts : terms n),
    vars_vec (Vcons t ts) = vars t ++ vars_vec ts.

  Proof. refl. Qed.

  Lemma in_vars_vec_elim : forall x n (ts : terms n),
    In x (vars_vec ts) -> exists t, Vin t ts /\ In x (vars t).

  Proof.
    induction ts; simpl; intros. contr. gen (in_app_or H). intro.
    destruct H0. exists h. intuition. gen (IHts H0). intro.
    destruct H1 as [t].
    exists t. intuition.
  Qed.

  Lemma vars_vec_in : forall x t n (ts : terms n),
    In x (vars t) -> Vin t ts -> In x (vars_vec ts).

  Proof.
    induction ts; simpl; intros. contr. destruct H0. subst t.
    apply in_appl. hyp. apply in_appr. apply IHts; hyp.
  Qed.

  Lemma vars_max : forall x t, In x (vars t) -> x <= maxvar t.

  Proof.
    intros x t. pattern t. apply term_ind with (Q := fun n (ts : terms n) =>
    In x (vars_vec ts) -> x <= maxvars ts); clear t; intros.
    simpl in *. intuition. rewrite maxvar_fun. rewrite vars_fun in H0. auto.
    contr. simpl in *.
    destruct (in_app_or H1); unfold maxvars; simpl. apply le_max_intro_l. auto.
    apply le_max_intro_r. auto.
  Qed.

  Lemma maxvar_in : forall x t n (v : terms n),
    x <= maxvar t -> Vin t v -> x <= maxvars v.

  Proof.
    induction v; unfold maxvars; simpl; intros. contr. destruct H0.
    subst t. apply le_max_intro_l. hyp. apply le_max_intro_r. apply IHv; hyp.
  Qed.

  Lemma maxvar_lmax : forall t, maxvar t = lmax (vars t).

  Proof.
    intro t. pattern t.
    set (Q := fun n (ts : terms n) => maxvars ts = lmax (vars_vec ts)).
    apply term_ind with (Q := Q); clear t.
    intro. simpl. apply (sym_equal (max_l (le_O_n x))).
    intros f ts H. rewrite maxvar_fun, vars_fun. hyp.
    unfold Q. auto.
    intros t n ts H1 H2. unfold Q. simpl. rewrite lmax_app.
    unfold Q in H2. rewrite maxvars_cons, H1, H2. refl.
  Qed.

(***********************************************************************)
(** boolean function testing if a variable occurs in a term *)

  Section var_occurs_in.

    Variable x : variable.

    Fixpoint var_occurs_in t :=
      match t with
        | Var y => beq_nat x y
        | Fun f ts =>
          let fix var_occurs_in_terms n (ts : terms n) :=
            match ts with
              | Vnil => false
              | Vcons t ts' => var_occurs_in t || var_occurs_in_terms _ ts'
            end
            in var_occurs_in_terms _ ts
      end.

    Fixpoint var_occurs_in_terms n (ts : terms n) :=
      match ts with
        | Vnil => false
        | Vcons t ts' => var_occurs_in t || var_occurs_in_terms ts'
      end.

    Lemma var_occurs_in_fun :
      forall f ts, var_occurs_in (Fun f ts) = var_occurs_in_terms ts.

    Proof. auto. Qed.

    Lemma var_occurs_in_ok : forall t,
      var_occurs_in t = true <-> In x (vars t).

    Proof.
      apply term_ind_forall. intro n; simpl. rewrite (beq_nat_ok x n).
      intuition.
      intros f v Rfv. rewrite var_occurs_in_fun, vars_fun.
      induction v. simpl. intuition.
      simpl in Rfv. destruct Rfv as [Rfa Rfv]. simpl. rewrite orb_eq.
      split; intros H. apply in_or_app. rewrite <- Rfa, <- IHv; auto.
      rewrite Rfa, IHv; auto. apply in_app_or. auto.
    Qed.

  End var_occurs_in.

(***********************************************************************)
(** number of symbol occurrences in a term *)

  Fixpoint nb_symb_occs t :=
    match t with
      | Var x => 0
      | Fun f ts =>
        let fix nb_symb_occs_terms n (ts : terms n) :=
          match ts with
            | Vnil => 0
            | Vcons u us => nb_symb_occs u + nb_symb_occs_terms _ us
          end
          in 1 + nb_symb_occs_terms _ ts
    end.

  Fixpoint nb_symb_occs_terms n (ts : terms n) :=
    match ts with
      | Vnil => 0
      | Vcons u us => nb_symb_occs u + nb_symb_occs_terms us
    end.

  Lemma nb_symb_occs_fix : forall n (ts : terms n),
    (fix nb_symb_occs_terms n (ts : terms n) :=
      match ts with
        | Vnil => 0
        | Vcons u us => nb_symb_occs u + nb_symb_occs_terms _ us
      end) _ ts = nb_symb_occs_terms ts.

  Proof. induction ts; simpl; intros. refl. rewrite IHts. refl. Qed.

  Lemma nb_symb_occs_fun : forall f ts,
    nb_symb_occs (Fun f ts) = 1 + nb_symb_occs_terms ts.

  Proof. intros. simpl. rewrite nb_symb_occs_fix. refl. Qed.

  Lemma Vin_nb_symb_occs_terms_ge : forall n (ts : terms n) t,
    Vin t ts -> nb_symb_occs_terms ts >= nb_symb_occs t.

  Proof.
    induction ts; simpl; intros. contr. destruct H. subst h. omega.
    ded (IHts _ H). omega.
  Qed.

(***********************************************************************)
(** list of symbols occurring in a term *)

  Fixpoint symbs (t : term) : list Sig :=
    match t with
      | Var x => nil
      | Fun f v =>
        let fix symbs_vec n (ts : terms n) : list Sig :=
          match ts with
            | Vnil => nil
            | Vcons t' ts' => symbs t' ++ symbs_vec _ ts'
          end
          in f :: symbs_vec (arity f) v
    end.

  Fixpoint symbs_vec n (ts : terms n) : list Sig :=
    match ts with
      | Vnil => nil
      | Vcons t' ts' => symbs t' ++ symbs_vec ts'
    end.

  Lemma symbs_fun : forall f ts, symbs (Fun f ts) = f :: symbs_vec ts.

  Proof. auto. Qed.

  Lemma symbs_vec_cast : forall n (ts : terms n) m (h : n=m),
    symbs_vec (Vcast ts h) = symbs_vec ts.

  Proof.
    induction ts; intros; destruct m; simpl; try discr.
    rewrite Vcast_refl. refl.
    rewrite Vcast_cons. apply (f_equal (fun l => symbs h ++ l)). apply IHts.
  Qed.

  Lemma symbs_vec_app : forall n1 (ts1 : terms n1) n2 (ts2 : terms n2),
    symbs_vec (Vapp ts1 ts2) = symbs_vec ts1 ++ symbs_vec ts2.

  Proof.
    induction ts1; intros; simpl. refl. rewrite app_ass. f_equal. apply IHts1.
  Qed.

  Lemma symbs_vec_cons : forall t n (ts : terms n),
    symbs_vec (Vcons t ts) = symbs t ++ symbs_vec ts.

  Proof. refl. Qed.

  Lemma in_symbs_vec_elim : forall x n (ts : terms n),
    In x (symbs_vec ts) -> exists t, Vin t ts /\ In x (symbs t).

  Proof.
    induction ts; simpl; intros. contr. gen (in_app_or H). intro.
    destruct H0. exists h. intuition. gen (IHts H0). intro.
    destruct H1 as [t]. exists t. intuition.
  Qed.

  Lemma symbs_vec_in : forall x t n (ts : terms n),
    In x (symbs t) -> Vin t ts -> In x (symbs_vec ts).

  Proof.
    induction ts; simpl; intros. contr. destruct H0. subst t.
    apply in_appl. hyp. apply in_appr. apply IHts; hyp.
  Qed.

(***********************************************************************)
(** size of a term *)

  Fixpoint size t :=
    match t with
      | Var x => 1
      | Fun f ts =>
        let fix size_terms n (ts : terms n) :=
          match ts with
            | Vnil => 0
            | Vcons u us => size u + size_terms _ us
          end
          in 1 + size_terms _ ts
    end.

  Fixpoint size_terms n (ts : terms n) :=
    match ts with
      | Vnil => 0
      | Vcons u us => size u + size_terms us
    end.

  Lemma size_fix : forall n (ts : terms n),
    (fix size_terms n (ts : terms n) :=
      match ts with
        | Vnil => 0
        | Vcons u us => size u + size_terms _ us
      end) _ ts = size_terms ts.

  Proof. induction ts; simpl; intros. refl. rewrite IHts. refl. Qed.

  Lemma size_fun : forall f ts, size (Fun f ts) = 1 + size_terms ts.

  Proof. intros. simpl. rewrite size_fix. refl. Qed.

  Lemma size_non_zero : forall t, size t > 0.

  Proof.
    intro. pattern t. apply term_ind with (Q := fun n (ts : terms n) =>
    size_terms ts >= 0); clear t.
    intro. simpl. omega.
    intros. rewrite size_fun. omega.
    simpl. omega.
    intros. simpl. omega.
  Qed.

  Lemma Vin_size_terms_ge : forall n (ts : terms n) t,
    Vin t ts -> size_terms ts >= size t.

  Proof.
    induction ts; simpl; intros. contr. destruct H. subst h. omega.
    ded (IHts _ H). omega.
  Qed.

  Arguments Vin_size_terms_ge [n ts t] _.

  Lemma Vin_size_terms_gt : forall n (ts : terms n) t,
    Vin t ts -> n > 1 -> size_terms ts > size t.

  Proof.
    intro. destruct n. omega. destruct n. omega. intros.
    VSntac ts. rewrite H1 in H. VSntac (Vtail ts). rewrite H2 in H. simpl in *.
    ded (size_non_zero (Vhead ts)). ded (size_non_zero (Vhead (Vtail ts))).
    destruct H. subst t. omega. destruct H. subst t. omega.
    ded (Vin_size_terms_ge H). omega.
  Qed.

  Lemma size_terms_cast : forall n (ts : terms n) m (h : n=m),
    size_terms (Vcast ts h) = size_terms ts.

  Proof.
    induction ts; intro m.
    (* Vnil *)
    destruct m; intro h.
    rewrite Vcast_refl. refl.
    discr.
    (* Vcons *)
    destruct m; intro h0.
    discr.
    rewrite Vcast_cons. simpl. rewrite IHts. refl.
  Qed.

  Lemma size_terms_app : forall n (ts : terms n) m (us : terms m),
    size_terms (Vapp ts us) = size_terms ts + size_terms us.

  Proof. induction ts; simpl; intros. refl. rewrite IHts. omega. Qed.

  Lemma term_ind_size : forall (P : term -> Prop),
    (forall n, (forall t, size t <= n -> P t) -> forall t, size t <= S n -> P t)
    -> forall t, P t.

  Proof.
    intro P. set (Q := fun n => forall t, size t <= n -> P t).
    change ((forall n, Q n -> Q (S n)) -> forall t, P t). intro IH.
    cut (forall t, Q t). intros. unfold Q in H. eapply H. apply le_refl.
    induction t. unfold Q. destruct t; simpl; intros; omega.
    apply IH. hyp.
  Qed.

(***********************************************************************)
(** direct subterms of a term *)

  Definition direct_subterms (t : term) : list term :=
    match t with
      | Var x => nil
      | Fun f fs => list_of_vec fs
    end.

End S.

(***********************************************************************)
(** implicit arguments *)

Arguments Var [Sig] _.
Arguments maxvar_var [Sig k x] _.
Arguments maxvar_le_fun [Sig m f ts] _.
Arguments maxvar_le_arg [Sig f ts m t] _ _.
Arguments in_vars_vec_elim [Sig x n ts] _.
Arguments vars_vec_in [Sig x t0 n ts] _ _.
Arguments in_symbs_vec_elim [Sig x n ts] _.
Arguments symbs_vec_in [Sig x t0 n ts] _ _.
Arguments vars_max [Sig x t] _.
Arguments Vin_nb_symb_occs_terms_ge [Sig n ts t] _.
Arguments Vin_size_terms_ge [Sig n ts t] _.
Arguments Vin_size_terms_gt [Sig n ts t] _ _.

(***********************************************************************)
(** tactics *)

Ltac Funeqtac :=
  match goal with
    | H : @Fun _ ?f _ = @Fun _ ?f _ |- _ => ded (fun_eq H); clear H
    | H : @Fun _ ?f _ = @Fun _ ?g _ |- _ =>
      ded (symb_eq H); try ((subst g || subst f); ded (fun_eq H); clear H)
  end.
