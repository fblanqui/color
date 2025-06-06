(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-02-09
- Frederic Blanqui, 2005-02-17

one-hole contexts
*)

Set Implicit Arguments.

From Stdlib Require Import Setoid.
From CoLoR Require Import LogicUtil VecUtil ListUtil BoolUtil NatUtil RelUtil.
From CoLoR Require Export ATerm.

Section S.

  Variable Sig : Signature.

  Notation term := (term Sig). Notation terms := (vector term).

(***********************************************************************)
(** contexts *)

  Inductive context : Type :=
  | Hole : context
  | Cont : forall (f : Sig) (i j : nat), i + S j = arity f ->
    terms i -> context -> terms j -> context.

  Arguments Cont [f i j] _ _ _ _.

  Lemma cont_eq_intro : forall f f', f = f' -> forall c c', c = c' ->
    forall i v1 i' v1' (h1 : i'=i) j v2 (e : i+S j=arity f) j' v2' (h2 : j'=j)
      (e' : i'+S j'=arity f'), v1 = Vcast v1' h1 -> v2 = Vcast v2' h2 ->
      Cont e v1 c v2 = Cont e' v1' c' v2'.

  Proof.
    intros f f' hf. subst f'. intros c c' hc. subst c'. destruct v1.
    (* v1=Vnil *)
    destruct i'; intros v1' h1. 2: discr. VOtac. rewrite Vcast_refl. clear h1.
    destruct v2; intros; clear H; destruct j'; try discr.
    (* v2=Vnil *)
    VOtac. assert (e'=e). apply eq_unique. subst e'. refl.
    (* v2=Vcons *)
    inversion h2. subst j'. rewrite Vcast_refl in H0. rewrite <- H0.
    assert (e'=e). apply eq_unique. subst e'. refl.
    (* v1=Vcons *)
    destruct i'; intros v1' h1. discr. inversion h1. subst i'.
    rewrite Vcast_refl. clear h1.
    destruct v2; destruct j'; try discr; intros; rewrite <- H; clear H.
    (* v2=Vnil *)
    VOtac. assert (e'=e). apply eq_unique. subst e'. refl.
    (* v2=Vcons *)
    inversion h2. subst n0. rewrite Vcast_refl in H0. rewrite <- H0.
    assert (e'=e). apply eq_unique. subst e'. refl.
  Qed.

(***********************************************************************)
(** replacement of the hole *)

  Fixpoint fill (c : context) (t : term) : term :=
    match c with
      | Hole => t
      | Cont H v1 c' v2 =>
        Fun _ (Vcast (Vapp v1 (Vcons (fill c' t) v2)) H)
    end.

(***********************************************************************)
(** context composition *)

  Fixpoint comp (C : context) : context -> context :=
    match C with
      | Hole => fun E => E
      | Cont H ts1 D ts2 => fun E => Cont H ts1 (comp D E) ts2
    end.

  Lemma fill_fill : forall C D u, fill C (fill D u) = fill (comp C D) u.

  Proof. induction C; simpl; intros. refl. rewrite (IHC D u). refl. Qed.

  Lemma comp_comp : forall C D E, comp (comp C D) E = comp C (comp D E).

  Proof. induction C; simpl; intros. refl. rewrite IHC. refl. Qed.

  Lemma cont_case : forall c, c = Hole \/ exists d, exists f,
    exists i, exists vi, exists j, exists vj, exists e : i + S j = arity f,
      c = comp d (Cont e vi Hole vj).

  Proof.
    induction c. auto. right. destruct IHc. subst. exists Hole. exists f.
    exists i. exists t. exists j. exists t0. exists e. refl.
    decomp H. subst. exists (Cont e t x t0). exists x0. exists x1. exists x2.
    exists x3. exists x4. exists x5. refl.
  Qed.

(***********************************************************************)
(** properties of fill *)

  Lemma var_eq_fill : forall x c t, Var x = fill c t -> c = Hole /\ t = Var x.

  Proof. intros. destruct c; simpl in H. auto. discr. Qed.

  Lemma fun_eq_fill : forall f ts c u, Fun f ts = fill c u ->
    c = Hole \/ exists i, exists j, exists H : i + S j = arity f,
      exists ti, exists d, exists tj, c = Cont H ti d tj.

  Proof.
    intros. destruct c. auto. right.
    simpl in H. injection H. intros. subst f0.
    exists i. exists j. exists e. exists t. exists c. exists t0.
    refl.
  Qed.

  Lemma fun_eq_nth_fill : forall f v i (h : i < arity f),
    let v1 := Vsub v (Veq_app_cons_aux1 h) in
      let v2 := Vsub v (Veq_app_cons_aux2 h) in 
        let H := Veq_app_cons_aux3 h in
          let c := Cont H v1 Hole v2 in Fun f v = fill c (Vnth v h).

  Proof.
    intros. simpl. apply args_eq. apply Veq_nth; intros j Hj.
    rewrite Vnth_cast, Vnth_app. case (le_gt_dec i j); intros.
    2:{ unfold v1. rewrite Vnth_sub. apply Vnth_eq. refl. }
    rewrite Vnth_cons. destruct (lt_ge_dec 0 (j-i)).
    unfold v2. rewrite Vnth_sub. apply Vnth_eq. lia.
    apply Vnth_eq. lia.
  Qed.

  Lemma fill_eq : forall t u c, fill c t = fill c u <-> t = u.

  Proof.
    split. induction c; simpl; intros. hyp. Funeqtac.
    rewrite Vcast_eq, Vapp_eq in H0. decomp H0. rewrite Vcons_eq in H1.
    intuition. intro. subst. refl.
  Qed.

  Lemma comp_eq : forall c d e, comp c d = comp c e <-> d = e.

  Proof.
    split. induction c; simpl; intros. hyp. inversion H. auto.
    intro. subst. refl.
  Qed.

  Lemma size_fill : forall t c, size (fill c t) >= size t.

  Proof.
    induction c. simpl. lia. simpl fill.
    rewrite size_fun, size_terms_cast, size_terms_app. simpl. lia.
  Qed.

  Lemma wf_term : forall (t : term) c, t = fill c t -> c = Hole.

  Proof.
    intros. destruct c. refl. assert (size (fill (Cont e t0 c t1) t) > size t).
    simpl fill. rewrite size_fun, size_terms_cast, size_terms_app. simpl.
    ded (size_fill t c). lia. rewrite <- H in H0. lia.
  Qed.

(***********************************************************************)
(** subterm ordering *)

  Definition subterm_eq u t := exists C, t = fill C u.

  Definition subterm u t := exists C, C <> Hole /\ t = fill C u.

  Definition supterm := transp subterm.

  Definition supterm_eq := transp subterm_eq.

  Global Instance subterm_eq_refl : Reflexive subterm_eq.

  Proof. intro t. exists Hole. refl. Qed.

  Global Instance supterm_eq_refl : Reflexive supterm_eq.

  Proof. intro t. exists Hole. refl. Qed.

  Lemma subterm_eq_var : forall u x, subterm_eq u (Var x) -> u = Var x.

  Proof.
    intros. unfold subterm_eq in H. destruct H as [C].
    assert (C = Hole /\ u = Var x).
    apply var_eq_fill. exact H. destruct H0. exact H1.
  Qed.

  Lemma subterm_fun_elim : forall u f ts,
    subterm u (Fun f ts) -> exists t, Vin t ts /\ subterm_eq u t.

  Proof.
    intros. unfold subterm in H. destruct H as [C]. destruct H.
    destruct C. cong.
    clear H. simpl in H0. Funeqtac. subst ts. exists (fill C u). split.
    apply Vin_cast_intro. apply Vin_app_cons. unfold subterm_eq. exists C. refl.
  Qed.

  Lemma subterm_fun : forall f ts u, Vin u ts -> subterm u (Fun f ts).

  Proof.
    intros. unfold subterm.
    assert (exists n1, exists v1 : terms n1, exists n2, exists v2 : terms n2,
      exists H : n1 + S n2 = arity f, ts = Vcast (Vapp v1 (Vcons u v2)) H).
    apply Vin_elim. hyp.
    destruct H0 as [n1]. destruct H0 as [ts1].
    destruct H0 as [n2]. destruct H0 as [ts2]. destruct H0 as [H1].
    exists (Cont H1 ts1 Hole ts2). split. discr.
    rewrite H0. refl.
  Qed.

  Lemma subterm_size : forall t u : term, subterm t u -> size t < size u.

  Proof.
    intros t u [C [hC e]]. subst u. destruct C. cong.
    simpl fill. rewrite size_fun, size_terms_cast, size_terms_app. simpl.
    ded (size_fill t C). lia.
  Qed.

  Lemma subterm_strict : forall u t, subterm u t -> subterm_eq u t.

  Proof.
    unfold subterm_eq, subterm. intros. destruct H. destruct H. exists x. hyp.
  Qed.

  Lemma subterm_noteq : forall u t, subterm_eq u t -> u <> t -> subterm u t.

  Proof.
    unfold subterm_eq, subterm. intros. destruct H as [C]. destruct C.
    subst t. simpl in H0. cong.
    exists (Cont e t0 C t1). split. discr. subst t. refl.
  Qed.

  Lemma rc_subterm : subterm_eq == subterm%.

  Proof.
    rewrite rel_eq. intros t u. split; intro h.
    destruct h. destruct x. left. auto.
    right. exists (Cont e t0 x t1). intuition. discr.
    destruct h. exists Hole. auto. apply subterm_strict. hyp.
  Qed.

  Lemma rc_supterm : supterm_eq == supterm%.

  Proof.
    rewrite rel_eq. intros t u. split; intro h.
    destruct h. destruct x. left. auto.
    right. exists (Cont e t0 x t1). intuition. discr.
    destruct h. exists Hole. auto. apply subterm_strict. hyp.
  Qed.

  Lemma subterm_eq_split : forall t u, subterm_eq t u -> t = u \/ subterm t u.

  Proof.
    intros t u tu. destruct tu as [c hu]. destruct c.
    auto. right. exists (Cont e t0 c t1). intuition. discr.
  Qed.

(***********************************************************************)
(** transitivity of the subterm ordering *)

  Global Instance subterm_trans : Transitive subterm.

  Proof.
    intros t u v tu uv. destruct tu as [c [hc hu]]. destruct uv as [d [hd hv]].
    subst. rewrite fill_fill. exists (comp d c). intuition.
    destruct d. auto. discr.
  Qed.

  Global Instance subterm_eq_trans : Transitive subterm_eq.

  Proof.
    intros t u v [c hu] [d hv]. subst. rewrite fill_fill. exists (comp d c).
    refl.
  Qed.

  Global Instance supterm_trans : Transitive supterm.

  Proof.
    intros t u v. unfold supterm, transp. intros tu uv. trans u; hyp.
  Qed.

  Global Instance supterm_eq_trans : Transitive supterm_eq.

  Proof.
    intros t u v. unfold supterm_eq, transp. intros tu uv. trans u; hyp.
  Qed.

  Lemma subterm_trans_eq1 : forall t u v,
    subterm_eq t u -> subterm u v -> subterm t v.

  Proof.
    unfold subterm, subterm_eq. intros. destruct H. destruct H0. destruct H0.
    subst u. subst v. rewrite (fill_fill x0 x t). exists (comp x0 x).
    split. destruct x0. cong. simpl. discr. refl.
  Qed.

  Lemma subterm_trans_eq2 : forall t u v,
    subterm t u -> subterm_eq u v -> subterm t v.

  Proof.
    unfold subterm, subterm_eq. intros. destruct H. destruct H. destruct H0.
    subst u. subst v. rewrite (fill_fill x0 x t). exists (comp x0 x).
    split. destruct x. cong.
    destruct x0; simpl; discr. refl.
  Qed.

(***********************************************************************)
(** subterm-based induction principle *)

  Lemma forall_subterm_eq : forall (P : term -> Prop) t,
    (forall u, subterm_eq u t -> P u) -> P t.

  Proof. intros. apply H. unfold subterm. exists Hole. auto. Qed.

  Lemma subterm_ind_sub : forall (P : term -> Prop)
    (IH : forall t, (forall u, subterm u t -> P u) -> P t),
    forall t u, subterm_eq u t -> P u.

  Proof.
    intros P IH. set (P' := fun t => forall u, subterm_eq u t -> P u).
    change (forall t, P' t). apply term_ind_forall.
    (* var *)
    unfold P'. intros. assert (u = Var v). apply subterm_eq_var. hyp.
    subst u. apply IH. unfold subterm. intros. destruct H0. destruct H0.
    destruct x. cong. discr.
    (* fun *)
    intros. unfold P'. intros. apply IH. intros.
    assert (subterm u0 (Fun f v)). eapply subterm_trans_eq2. apply H1. hyp.
    assert (exists t, Vin t v /\ subterm_eq u0 t). apply subterm_fun_elim.
    hyp.
    destruct H3. destruct H3.
    assert (P' x). eapply Vforall_in with (n := arity f). apply H. hyp.
    apply H5. hyp.
  Qed.

  Lemma subterm_ind : forall (P : term -> Prop)
    (IH : forall t, (forall u, subterm u t -> P u) -> P t),
    forall t, P t.

  Proof. intros. apply forall_subterm_eq. apply subterm_ind_sub. hyp. Qed.

(***********************************************************************)
(** boolean function deciding subterm_eq *)

  Fixpoint bsubterm_eq (t u : term) : bool :=
    match u with
      | Var _ => beq_term t u
      | Fun _ us => beq_term t u || bVexists (bsubterm_eq t) us
    end.

  Lemma bsubterm_eq_ok : forall t u, bsubterm_eq t u = true <-> subterm_eq t u.

  Proof.
    intros t u. pattern u; apply term_ind_forall; clear u; simpl.
    (* Var *)
    intro. rewrite beq_term_ok. split; intro. subst. refl.
    apply subterm_eq_var in H. hyp.
    (* Fun *)
    split; rewrite orb_eq, beq_term_ok; intros. destruct H0.
    subst. refl. rewrite (bVexists_ok_Vin (subterm_eq t)) in H0.
    2:{ intros. pattern x. apply Vforall_in with (v:=v). apply H. hyp. }
    rewrite Vexists_eq in H0. decomp H0. apply subterm_eq_trans with x.
    hyp. apply subterm_strict. apply subterm_fun. hyp.
    destruct H0. destruct x. auto. right.
    rewrite (bVexists_ok_Vin (subterm_eq t)).
    2:{ intros. pattern x0. apply Vforall_in with (v:=v). apply H. hyp. }
    rewrite Vexists_eq. exists (fill x t). split.
    simpl in H0. Funeqtac. rewrite H1, Vin_cast. apply Vin_app_cons.
    exists x. refl.
  Qed.

  Definition bsupterm_eq t u := bsubterm_eq u t.

(***********************************************************************)
(** boolean function deciding subterm *)

  Definition bsubterm (t u : term) : bool :=
    match u with
      | Var x => false
      | Fun _ us => bVexists (bsubterm_eq t) us
    end.

  Lemma bsubterm_ok : forall t u, bsubterm t u = true <-> subterm t u.

  Proof.
    destruct u; simpl. intuition auto with *. destruct H. destruct H. destruct x.
    cong. simpl in H0. discr.
    rewrite (bVexists_ok (subterm_eq t)), Vexists_eq. split; intro.
    decomp H. apply subterm_trans_eq1 with x.
    hyp. apply subterm_fun. hyp. apply subterm_fun_elim in H. hyp.
    apply bsubterm_eq_ok.
  Qed.

  Definition bsupterm t u := bsubterm u t.

(***********************************************************************)
(** subterms and variables *)

  Lemma subterm_eq_vars : forall u t x,
    subterm_eq u t -> List.In x (vars u) -> List.In x (vars t).

  Proof.
    unfold subterm_eq. intros. destruct H as [C]. subst t. elim C; clear C.
    simpl. hyp. intros. simpl fill.
    rewrite vars_fun, vars_vec_cast, vars_vec_app, vars_vec_cons.
    apply in_appr. apply in_appl. hyp.
  Qed.

  Lemma in_vars_subterm_eq : forall x t,
    List.In x (vars t) -> subterm_eq (Var x) t.

  Proof.
    intros x t. pattern t. apply term_ind_forall; clear t; simpl; intros.
    intuition. rewrite H0. refl.
    gen (in_vars_vec_elim H0). intro.
    destruct H1 as [t]. destruct H1. gen (Vforall_in H H1). intro.
    gen (H3 H2). intro. apply subterm_strict. eapply subterm_trans_eq1.
    apply H4.
    apply subterm_fun. hyp.
  Qed.

  Lemma in_vars_fun : forall x f ts,
    List.In x (vars (Fun f ts)) -> exists t, Vin t ts /\ subterm_eq (Var x) t.

  Proof.
    intros. apply subterm_fun_elim. ded (in_vars_subterm_eq _ _ H).
    apply subterm_noteq. hyp. discr.
  Qed.

(***********************************************************************)
(** variables of a context *)

  Fixpoint cvars (c : context) : variables :=
    match c with
      | Hole => List.nil
      | Cont H v1 c' v2 => vars_vec v1 ++ cvars c' ++ vars_vec v2
    end.

  Lemma vars_fill_elim : forall t c, vars (fill c t) [= cvars c ++ vars t.

  Proof.
    induction c. simpl. refl. simpl fill. rewrite vars_fun. simpl.
    unfold List.incl. intros. ded (in_vars_vec_elim H). do 2 destruct H0.
    ded (Vin_cast_elim H0). ded (Vin_app H2). destruct H3.
    repeat apply in_appl. apply (vars_vec_in H1 H3).
    simpl in H3. destruct H3. subst x. ded (IHc _ H1).
    rewrite app_ass. apply in_appr. apply in_app_com. apply in_appl. exact H3.
    apply in_appl. repeat apply in_appr. apply (vars_vec_in H1 H3).
  Qed.

  Lemma vars_fill_intro : forall t c, cvars c ++ vars t [= vars (fill c t).

  Proof.
    induction c. simpl. refl.
    simpl cvars. simpl fill.
    rewrite vars_fun, vars_vec_cast, vars_vec_app, vars_vec_cons, app_ass.
    apply appl_incl. apply app_com_incl. apply appr_incl. exact IHc.
  Qed.

(***********************************************************************)
(** symbols of a context *)

  Fixpoint csymbs (c : context) : list Sig :=
    match c with
      | Hole => List.nil
      | @Cont f _ _ _ v1 c' v2 =>
        f :: (symbs_vec v1 ++ csymbs c' ++ symbs_vec v2)
    end.

  Lemma symbs_fill_elim : forall t c, symbs (fill c t) [= csymbs c ++ symbs t.

  Proof.
    induction c. simpl. refl. simpl fill. rewrite symbs_fun. simpl.
    intro x. simpl; intro H. destruct H. subst. left. refl. right.
    ded (in_symbs_vec_elim H). do 2 destruct H0. ded (Vin_cast_elim H0).
    ded (Vin_app H2). destruct H3. repeat apply in_appl.
    apply (symbs_vec_in H1 H3). simpl in H3. destruct H3. subst x0.
    ded (IHc _ H1).
    rewrite app_ass. apply in_appr. apply in_app_com. apply in_appl. exact H3.
    apply in_appl. repeat apply in_appr. apply (symbs_vec_in H1 H3).
  Qed.

  Lemma symbs_fill_intro : forall t c, csymbs c ++ symbs t [= symbs (fill c t).

  Proof.
    induction c. simpl. refl. simpl csymbs. simpl fill.
    rewrite symbs_fun, symbs_vec_cast, symbs_vec_app, symbs_vec_cons,
      <- app_comm_cons, app_ass. intro x. simpl. intro H. destruct H.
    subst. left. refl. right. revert x H. apply appl_incl.
    apply app_com_incl. apply appr_incl. exact IHc.
  Qed.

End S.

(***********************************************************************)
(** declarations of implicit arguments *)

Arguments Hole {Sig}.
Arguments in_vars_subterm_eq [Sig x t] _.
Arguments in_vars_fun [Sig x f ts] _.
Arguments vars_fill_elim [Sig t c] _ _.
Arguments var_eq_fill [Sig x c t] _.
Arguments fun_eq_fill [Sig f ts c u] _.
Arguments wf_term [Sig t c] _.
Arguments subterm_fun [Sig] _ [ts u] _.
