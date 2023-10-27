(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-06-22

semantic labelling (with ordered labels)
(Zantema, Fundamenta Informaticae, 1995, volume 24, pages 89-105)
*)

Set Implicit Arguments.

From CoLoR Require Import ATrs AInterpretation BoolUtil LogicUtil EqUtil
     VecUtil SN RelUtil AWFMInterpretation NaryFunction NatUtil ARelation
     ARules SetUtil FunUtil VecMax AMorphism.
From Coq Require Import List.

Section S.

  Variable Sig : Signature.

  Notation term := (term Sig). Notation terms := (vector term).
  Notation rule := (rule Sig). Notation rules := (rules Sig).

(***********************************************************************)
(** labels *)

  Variable L : Sig -> Type.
  Variable beq : forall f g, L f -> L g -> bool.
  Variable beq_ok : forall f (l m : L f), beq l m = true <-> l = m.

(***********************************************************************)
(** labelled signature *)

  Variable I : interpretation Sig.

  Notation int := (@term_int _ I).

  Record lab_symb : Type := mk {
    l_symb : Sig;
    l_lab : L l_symb }.

  Notation eq_symb_dec := (@eq_symb_dec Sig).

  Ltac Leqtac := repeat
    match goal with
      | H : @mk ?x _ = @mk ?x _ |- _ =>
        let h1 := fresh in
          (injection H; intro h1; ded (inj_existT eq_symb_dec h1);
            clear h1; clear H)
      | H : @mk _ _ = @mk _ _ |- _ =>
        let h1 := fresh in let h2 := fresh in
          (injection H; clear H; intros h1 h2; subst;
            ded (inj_existT eq_symb_dec h1); clear h1; subst)
    end.

  Definition beq_lab_symb (fl1 fl2 : lab_symb) :=
    let (f1,l1) := fl1 in let (f2,l2) := fl2 in beq_symb f1 f2 && beq l1 l2.

  Lemma beq_lab_symb_ok : forall fl1 fl2,
    beq_lab_symb fl1 fl2 = true <-> fl1 = fl2.

  Proof.
    intros [f1 l1] [f2 l2]. simpl. split; intro. rewrite andb_eq in H.
    destruct H.
    rewrite beq_symb_ok in H. subst. rewrite beq_ok in H0. subst. refl.
    Leqtac. rewrite andb_eq, (beq_refl (@beq_symb_ok Sig)), beq_ok. auto.
  Qed.

  Definition lab_arity (fl : lab_symb) := let (f,_) := fl in arity f.

  Definition lab_sig := mkSignature lab_arity beq_lab_symb_ok.

  Notation Sig' := lab_sig. Notation Fun' := (@Fun Sig').
  Notation term' := (ATerm.term Sig'). Notation terms' := (vector term').
  Notation rule' := (ATrs.rule Sig'). Notation rules' := (rules Sig').

(***********************************************************************)
(** labelling *)

  Variable pi : forall f : Sig, vector I (arity f) -> L f.

  Fixpoint lab v t :=
    match t with
      | Var x => Var x
      | Fun f ts => Fun' (mk (pi f (Vmap (int v) ts))) (Vmap (lab v) ts)
    end.

  Definition lab_rule v (a : rule) :=
    let (l,r) := a in mkRule (lab v l) (lab v r).

  Definition lab_rules R a := exists b, exists v, R b /\ a = lab_rule v b.

  Definition lab_sub v s (x : variable) := lab v (s x).

  Lemma lab_sub_eq : forall v s t,
    lab v (sub s t) = sub (lab_sub v s) (lab (beta v s) t).

  Proof.
    intros v s t. pattern t; apply term_ind with (Q := fun n (ts : terms n) =>
    Vmap (lab v o sub s) ts = Vmap (sub (lab_sub v s) o lab (beta v s)) ts);
    clear t; intros; simpl.
    (* Var *)
    unfold lab_sub. refl.
    (* Fun *)
    rewrite !Vmap_map, Vmap_eq_ext with (g := int (beta v s)).
    2: apply substitution_lemma. apply args_eq. hyp.
    (* Vnil *)
    refl.
    (* Vcons *)
    apply Vcons_eq_intro; hyp.
  Qed.

  Lemma lab_fval : forall v t n, n > maxvar t -> lab (fval v n) t = lab v t.

  Proof.
    intros v t. pattern t; apply term_ind with (Q := fun n (ts : terms n) =>
    forall n, n > maxvars ts -> Vmap (lab v) ts = Vmap (lab (fval v n)) ts);
    clear t; simpl; intros.
    (* Var *)
    refl.
    (* Fun *)
    rewrite (H n). assert (Vmap (int v) v0 = Vmap (int (fval v n)) v0).
    apply Vmap_eq. apply Vforall_intro. intros. apply term_int_eq_fval_lt.
    apply Nat.le_lt_trans with (Vmax (Vmap (@maxvar Sig) v0)). apply Vmax_in.
    apply Vin_map_intro. hyp. hyp. rewrite H1. refl. unfold maxvars. lia.
    (* Vnil *)
    refl.
    (* Vcons *)
    rewrite maxvars_cons, gt_max in H1. destruct H1.
    rewrite (H0 n0). 2: hyp. rewrite (H n0). 2: hyp. refl.
  Qed.

  Lemma lab_rule_fval : forall v a n,
    n > maxvar_rule a -> lab_rule (fval v n) a = lab_rule v a.

  Proof.
    intros v [l r] n. simpl. rewrite gt_max. intuition.
    rewrite lab_fval. 2: hyp. rewrite lab_fval. 2: hyp. refl.
  Qed.

  Notation fold_max := (@fold_max Sig).

  Lemma map_lab_rule_fval : forall v R n, n > maxvar_rules R ->
    map (lab_rule (fval v n)) R = map (lab_rule v) R.

  Proof.
    induction R; simpl; intros. refl. unfold maxvar_rules in H. simpl in H.
    rewrite lab_rule_fval, IHR. refl.
    apply Nat.le_lt_trans with (fold_left fold_max R (fold_max 0 a)).
    apply maxvar_rules_init_mon. apply Nat.le_max_l. hyp.
    apply Nat.le_lt_trans with (fold_left fold_max R (fold_max 0 a)).
    apply maxvar_rules_init. hyp.
  Qed.

(***********************************************************************)
(** ordering of labels *)

  Variable Lgt : forall f, relation (L f). Infix ">L" := Lgt (at level 50).

  Let Lge f := @Lgt f %. Infix ">=L" := Lge (at level 50).

  Definition Fun'_vars f (a : L f) := Fun' (mk a) (fresh_vars (arity f)).

  Definition decr f (a b : L f) := mkRule (Fun'_vars a) (Fun'_vars b).

  Definition Decr (rho : rule') :=
    exists f, exists a : L f, exists b, a >L b /\ rho = decr a b.

  Lemma Lge_Decr : forall f (ts : terms' (arity f)) (a b : L f),
    a >=L b -> red Decr # (Fun' (mk a) ts) (Fun' (mk b) ts).

  Proof.
    intros. destruct H. subst. apply rt_refl. apply rt_step.
    exists (Fun'_vars a). exists (Fun'_vars b). exists Hole.
    exists (sub_vars ts). simpl. intuition.
    exists f. exists a. exists b. intuition.
    apply args_eq. apply sub_fresh_vars.
    apply args_eq. apply sub_fresh_vars.
  Qed.

(***********************************************************************)
(** unlabelling *)

  Definition F (f' : Sig') := let (f,_) := f' in f.

  Lemma HF : forall f', arity f' = arity (F f').

  Proof. intros (f,l). refl. Qed.

  Definition unlab := Ft HF.
  Definition unlab_rules := Frs HF.
  Definition unlab_rules_fin := Fl HF.

  Lemma Ft_epi : forall v t, unlab (lab v t) = t.

  Proof.
    intros v t; pattern t; apply term_ind
      with (Q := fun n (ts : terms n) => Vmap (unlab o lab v) ts = ts);
      clear t; intros; simpl. refl.
    apply args_eq. unfold comp in H. rewrite Vmap_map, H.
    apply Vcast_refl. refl.
    rewrite H0. unfold comp. rewrite H. refl.
  Qed.

  Lemma Frs_iso : forall R, unlab_rules (lab_rules R) [=] R.

  Proof.
    intros R [l r]. split.
    (* [= *)
    intros [[l' r'] [h1 h2]]. destruct h1 as [[x y] [v [h h']]]. inversion h'.
    inversion h2. subst. rewrite !Ft_epi. hyp.
    (* =] *)
    unfold Frs. intro. set (v := fun x : variable => some_elt I).
    exists (mkRule (lab v l) (lab v r)). split.
    unfold lab_rules. exists (mkRule l r). exists v. intuition.
    simpl. rewrite !Ft_epi. refl.
  Qed.

  Lemma red_Frs_Decr : red (unlab_rules Decr) << @eq term.

  Proof.
    intros t u h. redtac. subst. destruct lr as [[l' r'] [h1 h2]].
    destruct h1 as [f [a [b [ab h]]]]. inversion h. subst. inversion h2.
    assert (HF (mk a) = HF (mk b)). apply UIP. apply eq_nat_dec. rewrite H.
    refl.
  Qed.

  Lemma rt_red_Frs_Decr : red (unlab_rules Decr) # << @eq term.

  Proof.
    intros t u. induction 1. apply red_Frs_Decr. hyp. refl. trans y; hyp.
  Qed.

  Lemma red_mod_Frs_Decr : forall E,
    red (unlab_rules (union Decr (lab_rules E))) << red E %.

  Proof.
    intros E t u h. redtac. subst. apply Frs_app in lr. destruct lr.
    left. eapply rt_red_Frs_Decr. apply rt_step. apply red_rule. hyp.
    right. apply red_rule. do 2 destruct H. rewrite H0. clear H0.
    do 3 destruct H.
    subst. destruct x0. simpl. rewrite !Ft_epi. hyp.
  Qed.

  Lemma rt_red_mod_Frs_Decr : forall E,
    red (unlab_rules (union Decr (lab_rules E))) # << red E #.

  Proof.
    intro E. trans (red E % #). rewrite red_mod_Frs_Decr. refl.
    rewrite rc_incl_rtc, rtc_invol. refl.
  Qed.

(***********************************************************************)
(** main theorem *)

  Variable Dge : relation I. Infix ">=D" := Dge (at level 50).

  Let Ige := IR I Dge. Infix ">=I" := Ige (at level 70).

  Variable pi_mon : forall f, Vmonotone (pi f) Dge (@Lge f).
  Variable I_mon : forall f, Vmonotone1 (fint I f) Dge.

  Section red.

    Variable R : set rule. Notation R' := (lab_rules R).

    Variable ge_compat : forall l r, R (mkRule l r) -> l >=I r.

    Lemma hd_red_lab : forall v t u,
      hd_red R t u -> hd_red_mod Decr R' (lab v t) (lab v u).

    Proof.
      intros. redtac. subst. exists (lab v (sub s l)). split. apply rt_refl.
      rewrite !lab_sub_eq. exists (lab (beta v s) l).
      exists (lab (beta v s) r). exists (lab_sub v s). intuition.
      exists (mkRule l r). exists (beta v s). intuition.
    Qed.

    Lemma red_lab : forall v t u,
      red R t u -> red_mod Decr R' (lab v t) (lab v u).

    Proof.
      intros. redtac. subst. elim c; clear c.
      (* Hole *)
      simpl. exists (lab v (sub s l)). split. apply rt_refl.
      rewrite !lab_sub_eq. exists (lab (beta v s) l).
      exists (lab (beta v s) r). exists Hole. exists (lab_sub v s). intuition.
      exists (mkRule l r). exists (beta v s). intuition.
      (* Cont *)
      intros. simpl. rewrite !Vmap_cast, !Vmap_app. simpl.
      set (v0' := Vmap (int v) t). set (l1 := fill c (sub s l)). fold l1 in H.
      set (v1' := Vmap (int v) t0). set (r1 := fill c (sub s r)). fold r1 in H.
      assert (int v l1 >=D int v r1). assert (IR I Dge l1 r1).
      apply IR_context_closed. hyp. apply IR_substitution_closed.
      apply ge_compat.
      hyp. apply H0.
      set (a := pi f (Vcast (Vapp v0' (Vcons (int v l1) v1')) e)).
      set (b := pi f (Vcast (Vapp v0' (Vcons (int v r1) v1')) e)).
      assert (a >=L b). apply pi_mon. hyp.
      set (w0 := Vmap (lab v) t). set (w1 := Vmap (lab v) t0).
      set (ts := Vcast (Vapp w0 (Vcons (lab v l1) w1)) e). ded (Lge_Decr ts H1).
      set (us := Vcast (Vapp w0 (Vcons (lab v r1) w1)) e).
      do 2 destruct H. set (vs := Vcast (Vapp w0 (Vcons x w1)) e).
      exists (Fun' (mk b) vs). split. apply rt_trans with (Fun' (mk b) ts). hyp.
      apply context_closed_fun with (R := red Decr #).
      apply context_closed_rtc. apply context_closed_red. hyp.
      apply context_closed_fun with (R := red R'). apply context_closed_red.
      hyp.
    Qed.

    Lemma rt_red_lab : forall v t u,
      red R # t u -> red_mod Decr R' # (lab v t) (lab v u).

    Proof.
      induction 1. apply rt_step. apply red_lab. hyp. apply rt_refl.
      apply rt_trans with (lab v y); hyp.
    Qed.

    Lemma WF_red_lab : WF (red R) <-> WF (red_mod Decr R').

    Proof.
      split; intro.
      (* -> *)
      apply Fred_mod_WF with (S2:=Sig) (F:=F) (HF:=HF).
      apply WF_incl with (red R).
      2: hyp. intros t u h. redtac. ded (rt_red_Frs_Decr H0). subst t0. subst.
      apply red_rule. eapply Frs_iso. hyp.
      (* <- *)
      set (v := fun x : variable => some_elt I).
      apply WF_incl with (Rof (red_mod Decr R') (lab v)).
      intros t u h. unfold Rof. apply red_lab. hyp.
      apply WF_inverse. hyp.
    Qed.

  End red.

(***********************************************************************)
(** rewriting modulo *)

  Section red_mod.

    Variables E R : set rule.

    Variable ge_compatE : forall l r, E (mkRule l r) -> l >=I r.
    Variable ge_compatR : forall l r, R (mkRule l r) -> l >=I r.

    Notation E' := (lab_rules E). Notation R' := (lab_rules R).

    Lemma red_mod_lab : forall v t u,
      red_mod E R t u -> red_mod (union Decr E') R' (lab v t) (lab v u).

    Proof.
      intros. do 2 destruct H. ded (rt_red_lab ge_compatE v H).
      ded (red_lab ge_compatR v H0). do 2 destruct H2. exists x0. intuition.
      apply rt_trans with (lab v x).
      eapply incl_elim. apply rt_red_mod_union. hyp.
      eapply incl_elim. eapply rtc_incl. eapply red_incl.
      apply subset_union_l. hyp.
    Qed.

    Lemma hd_red_mod_lab : forall v t u,
      hd_red_mod E R t u -> hd_red_mod (union Decr E') R' (lab v t) (lab v u).

    Proof.
      intros. do 2 destruct H. ded (rt_red_lab ge_compatE v H).
      ded (hd_red_lab v H0). do 2 destruct H2. exists x0. intuition.
      apply rt_trans with (lab v x).
      eapply incl_elim. apply rt_red_mod_union. hyp.
      eapply incl_elim. eapply rtc_incl. eapply red_incl.
      apply subset_union_l. hyp.
    Qed.

    Lemma WF_red_mod_lab : WF (red_mod E R) <-> WF (red_mod (union Decr E') R').

    Proof.
      split; intro.
      (* -> *)
      apply Fred_mod_WF with (S2:=Sig) (F:=F) (HF:=HF).
      apply WF_incl with (red_mod E R). 2: hyp. intros t u h. destruct h.
      destruct H0. apply rt_red_mod_Frs_Decr in H0. exists x.
      (*rewrite Frs_iso in H1. auto. *)
      intuition. apply incl_elim with (R:=red (Frs HF R')).
      rewrite Frs_iso. refl. hyp.
      (* <- *)
      set (v := fun x : variable => some_elt I).
      apply WF_incl with (Rof (red_mod (union Decr E') R') (lab v)).
      intros t u h. unfold Rof. eapply red_mod_lab. hyp.
      apply WF_inverse. hyp.
    Qed.

    Lemma WF_hd_red_mod_lab :
      WF (hd_red_mod E R) <-> WF (hd_red_mod (union Decr E') R').

    Proof.
      split; intro.
      (* -> *)
      apply Fhd_red_mod_WF with (S2:=Sig) (F:=F) (HF:=HF).
      apply WF_incl with (hd_red_mod E R). 2: hyp. intros t u h. destruct h.
      destruct H0. apply rt_red_mod_Frs_Decr in H0. exists x.
      (*rewrite Frs_iso in H1. auto. *)
      intuition. apply incl_elim with (R:=hd_red (Frs HF R')).
      rewrite Frs_iso. refl. hyp.
      (* <- *)
      set (v := fun x : variable => some_elt I).
      apply WF_incl with (Rof (hd_red_mod (union Decr E') R') (lab v)).
      intros t u h. unfold Rof. apply hd_red_mod_lab. hyp.
      apply WF_inverse. hyp.
    Qed.

  End red_mod.

(***********************************************************************)
(** enumeration of labelled rules for a finite domain *)

  Section enum.

    Variable Is : list I.
    Variable Is_ok : forall x : I, In x Is.

    Fixpoint enum_tuple n : list (vector I n) :=
      match n with
        | 0 => cons Vnil nil
        | S p =>
          flat_map (fun ds => map (fun d => Vcons d ds) Is) (enum_tuple p)
      end.

    Lemma enum_tuple_complete : forall n (ds : vector I n),
      In ds (enum_tuple n).

    Proof.
      induction n; simpl; intros. VOtac. auto. rewrite in_flat_map.
      exists (Vtail ds). split. apply IHn.
      set (f := fun d : I => Vcons d (Vtail ds)).
      VSntac ds. change (In (f (Vhead ds)) (map f Is)). apply in_map.
      apply Is_ok.
    Qed.

(*REMARK: define a more efficient function?
Fixpoint enum_tuple2 n : list (vector I n) :=
  match n with
    | 0 => nil
    | S p =>
      fold_left (fun e ds => fold_left (fun e d => Vcons d ds :: e) Is e)
      (enum_tuple2 p) nil
  end.*)

    Definition enum R :=
      flat_map (fun ds => map (lab_rule (val_of_vec I ds)) R)
      (enum_tuple (S (maxvar_rules R))).

    Lemma enum_correct : forall R a, In a (enum R) -> lab_rules (of_list R) a.

    Proof.
      intros. unfold enum in H. rewrite in_flat_map in H. do 2 destruct H.
      rewrite in_map_iff in H0. do 2 destruct H0. exists x0.
      exists (val_of_vec I x). intuition.
    Qed.

    Lemma enum_complete : forall R a, lab_rules (of_list R) a -> In a (enum R).

    Proof.
      intros. do 3 destruct H. set (n := maxvar_rules R).
      unfold enum. rewrite in_flat_map. exists (vec_of_val x0 (S n)). split.
      apply enum_tuple_complete. subst.
      change (In (lab_rule x0 x) (map (lab_rule (fval x0 (S n))) R)).
      rewrite map_lab_rule_fval. apply in_map. hyp. unfold n. lia.
    Qed.

    Infix "[=]" := equiv.

    Lemma lab_rules_enum : forall R, lab_rules (of_list R) [=] of_list (enum R).

    Proof. split. apply enum_complete. apply enum_correct. Qed.

(*REMARK: define a more efficient function?
Definition enum2 R :=
  let n := S (maxvar_rules R) in
    fold_left (fun e ds =>
      let v := val_of_vec I ds in
        fold_left (fun e (a : rule) => let (l,r) := a in
          mkRule (lab v l) (lab v r) :: e)
        R e)
    (enum_tuple n) nil.*)

(***********************************************************************)
(** enumeration of labelled symbols *)

    Variable Fs : list Sig.
    Variable Fs_ok : forall x, In x Fs.

    Variable Ls : forall f, list (L f).
    Variable Ls_ok : forall f (x : L f), In x (Ls f).

    Definition Fs_lab := flat_map (fun f => map (@mk f) (Ls f)) Fs.

    Lemma Fs_lab_ok : forall f : Sig', In f Fs_lab.

    Proof.
      intros [f l]. unfold Fs_lab. rewrite in_flat_map. exists f. split.
      apply Fs_ok. rewrite in_map_iff. exists l. intuition.
    Qed.

(***********************************************************************)
(** enumeration of Decr rules *)

    Variable L2s : forall f, list (L f * L f).
    Variable L2s_ok : forall f (x y : L f), x >L y <-> In (x,y) (L2s f).

    Definition enum_Decr := flat_map (fun f =>
      map (fun x : L f * L f => let (a,b) := x in decr a b) (L2s f)) Fs.

    Notation D' := enum_Decr.

    Lemma enum_Decr_correct : forall x, In x D' -> Decr x.

    Proof.
      intros. unfold enum_Decr in H. rewrite in_flat_map in H.
      destruct H as [f]. destruct H. rewrite in_map_iff in H0.
      destruct H0 as [[a b]]. destruct H0. exists f. exists a. exists b.
      rewrite L2s_ok. auto.
    Qed.

    Lemma enum_Decr_complete : forall x, Decr x -> In x D'.

    Proof.
      intros. destruct H as [f [a [b [h]]]]. unfold enum_Decr.
      rewrite in_flat_map.
      exists f. split. apply Fs_ok. rewrite in_map_iff. exists (a,b).
      rewrite <- L2s_ok. auto.
    Qed.

    Lemma Rules_enum_Decr : of_list D' [=] Decr.

    Proof.
      unfold equiv. split; intro. apply enum_Decr_correct. hyp.
      apply enum_Decr_complete. hyp.
    Qed.

(***********************************************************************)
(** main theorems (finite versions) *)

    Import ATrs List. Notation rules := (rules Sig). Notation term := S.term.

    Variable bge : term -> term -> bool.
    Variable bge_ok : rel_of_bool bge << Ige.

    Section bge.

      Variable R : rules.
      Variable bge_compat : forallb (brule bge) R = true.

      Lemma ge_compat : forall l r, In (mkRule l r) R -> l >=I r.

      Proof.
        intros. apply bge_ok. unfold rel.
        change (brule bge (mkRule l r) = true).
        rewrite forallb_forall in bge_compat. apply bge_compat. hyp.
      Qed.

    End bge.

    Arguments ge_compat [R] _ _ _ _ _.

    Section red_mod.

      Variables E R : rules.

      Notation E' := (enum E). Notation R' := (enum R).

      Variable bge_compatE : forallb (brule bge) E = true.
      Variable bge_compatR : forallb (brule bge) R = true.

      Notation ge_compatE := (ge_compat bge_compatE).
      Notation ge_compatR := (ge_compat bge_compatR).

      Lemma WF_red_lab_fin : WF (red R) <-> WF (red_mod D' R').

      Proof.
        rewrite <- red_Rules, <- red_mod_Rules, WF_red_lab.
        2: apply ge_compatR. apply WF_same.
        rewrite Rules_enum_Decr, lab_rules_enum. refl.
      Qed.

      Import List.

      Lemma WF_red_mod_lab_fin :
        WF (red_mod E R) <-> WF (red_mod (D' ++ E') R').

      Proof.
        rewrite <- !red_mod_Rules, WF_red_mod_lab.
        2: apply ge_compatE. 2: apply ge_compatR. apply WF_same.
        rewrite of_app, Rules_enum_Decr, !lab_rules_enum. refl.
      Qed.

      Lemma WF_hd_red_mod_lab_fin :
        WF (hd_red_mod E R) <-> WF (hd_red_mod (D' ++ E') R').

      Proof.
        rewrite <- !hd_red_mod_Rules, WF_hd_red_mod_lab.
        2: apply ge_compatE. apply WF_same.
        rewrite of_app, Rules_enum_Decr, !lab_rules_enum. refl.
      Qed.

    End red_mod.

    Lemma WF_red_unlab_fin : forall R,
      WF (red (unlab_rules_fin R)) -> WF (red R).

    Proof. intros. apply Fred_WF_fin with (S2:=Sig) (F:=F) (HF:=HF). hyp. Qed.

    Lemma WF_red_mod_unlab_fin : forall E R,
      WF (red_mod (unlab_rules_fin E) (unlab_rules_fin R)) -> WF (red_mod E R).

    Proof.
      intros. apply Fred_mod_WF_fin with (S2:=Sig) (F:=F) (HF:=HF). hyp.
    Qed.

    Lemma WF_hd_red_mod_unlab_fin : forall E R,
      WF (hd_red_mod (unlab_rules_fin E) (unlab_rules_fin R))
      -> WF (hd_red_mod E R).

    Proof.
      intros. apply Fhd_red_mod_WF_fin with (S2:=Sig) (F:=F) (HF:=HF). hyp.
    Qed.

  End enum.

End S.

Arguments lab_sig _ [L beq] _.
Arguments Decr [Sig L beq] _ _ _.
Arguments lab_rules [Sig L beq] _ [I] _ _ _.
Arguments enum [Sig L beq] _ [I] _ _ _.
Arguments enum_Decr [Sig L beq] _ _ _.
Arguments Fs_lab [Sig L] _ _.
Arguments Fs_lab_ok [Sig L beq] _ [Fs] _ [Ls] _ _.
Arguments unlab_rules_fin _ [L beq] _ _.
Arguments WF_red_unlab_fin [Sig L beq] _ _ _ _.
Arguments WF_red_mod_unlab_fin [Sig L beq] _ _ _ _ _.
Arguments WF_hd_red_mod_unlab_fin [Sig L beq] _ _ _ _ _.
Arguments enum_tuple_complete [Sig] _ [Is] _ [n] _.

(***********************************************************************)
(** basic module type for semantic labellings *)

Module Type Base.

  Parameter Sig : Signature.

  Parameter L : Sig -> Type.
  Parameter beq : forall f g, L f -> L g -> bool.
  Parameter beq_ok : forall f (l m : L f), beq l m = true <-> l = m.

  Parameter I : interpretation Sig.

  Parameter pi : forall f : Sig, vector I (arity f) -> L f.

End Base.

(***********************************************************************)
(** module type for semantic labellings with unordered labels *)

Module Type SemLab.

  Include Base.

  Parameter beqI : term Sig -> term Sig -> bool.
  Parameter beqI_ok : rel_of_bool beqI << IR I (@eq I).

End SemLab.

(***********************************************************************)
(** module type for semantic labellings with ordered labels *)

Module Type OrdSemLab.

  Include SemLab.

  Parameter Dge : relation I.
  Parameter bge : term Sig -> term Sig -> bool.
  Parameter bge_ok : rel_of_bool bge << IR I Dge.
  Parameter I_mon : forall f, Vmonotone1 (fint I f) Dge.

  Notation "t '>=I' u" := (IR I Dge t u) (at level 70).

  Parameter Lgt : forall f, relation (L f).

  Infix ">L" := Lgt (at level 50).

  Parameter pi_mon : forall f, Vmonotone (pi f) Dge (@Lgt f%).

End OrdSemLab.

(***********************************************************************)
(** functor providing equality-ordered labels *)

Module Ord (SL : SemLab) <: OrdSemLab.

  Include SL.

  Definition Dge := @eq I.
  Definition bge := beqI.
  Definition bge_ok := beqI_ok.

  Lemma I_mon : forall f, Vmonotone1 (fint I f) Dge.

  Proof.
    unfold Vmonotone1, Vmonotone, Vmonotone_i, RelUtil.monotone. intros.
    rewrite H0. refl.
  Qed.

  Definition Lgt (f : Sig) (_ _ : L f) := False.

  Lemma Lge_is_eq : forall f a b, (@Lgt f%) a b <-> a = b.

  Proof. fo. Qed.

  Lemma pi_mon : forall f, Vmonotone (pi f) Dge (@Lgt f%).

  Proof.
    unfold Vmonotone, Vmonotone_i, RelUtil.monotone. intros.
    rewrite Lge_is_eq, H0. refl.
  Qed.

  Notation "t '>=I' u" := (IR I Dge t u) (at level 70).

  Notation Sig' := (lab_sig Sig beq_ok).

  Lemma Decr_empty : Decr beq_ok Lgt [=] empty.

  Proof. fo. Qed.

End Ord.

(***********************************************************************)
(** module type for finite semantic labellings with unordered labels *)

Module Type FinSemLab.

  Include SemLab.

  Parameter Fs : list Sig.
  Parameter Fs_ok : forall x : Sig, In x Fs.

  Parameter Is : list I.
  Parameter Is_ok : forall x : I, In x Is.

  Parameter Ls : forall f, list (L f).
  Parameter Ls_ok : forall f (x : L f), In x (Ls f).

End FinSemLab.

(***********************************************************************)
(** module type for finite semantic labellings with ordered labels *)

Module Type FinOrdSemLab.

  Include OrdSemLab.

  Parameter Fs : list Sig.
  Parameter Fs_ok : forall x : Sig, In x Fs.

  Parameter Is : list I.
  Parameter Is_ok : forall x : I, In x Is.

  Parameter Ls : forall f, list (L f).
  Parameter Ls_ok : forall f (x : L f), In x (Ls f).

  Parameter L2s : forall f, list (L f * L f).
  Parameter L2s_ok : forall f (x y : L f), x >L y <-> In (x,y) (L2s f).

End FinOrdSemLab.

(***********************************************************************)
(** functor providing equality-ordered labels *)

Module FinOrd (Import FSL : FinSemLab) <: FinOrdSemLab.

  Include (Ord FSL).

  Definition Fs := Fs.
  Definition Fs_ok := Fs_ok.

  Definition Is := Is.
  Definition Is_ok := Is_ok.

  Definition Ls := Ls.
  Definition Ls_ok := Ls_ok.

  Definition L2s : forall f, list (L f * L f) := fun _ => nil.

  Lemma L2s_ok : forall f (x y : L f), Lgt x y <-> In (x,y) (L2s f).

  Proof. fo. Qed.

  Lemma enum_Decr_empty : enum_Decr beq_ok Fs L2s = nil.

  Proof.
    unfold enum_Decr. unfold L2s. simpl. induction Fs. refl. simpl. hyp.
  Qed.

End FinOrd.

(***********************************************************************)
(** functor providing the properties of a semantic labelling
with ordered labels *)

Import ARules.

Module OrdSemLabProps (Import OSL : OrdSemLab).

  Notation Decr := (Decr beq_ok Lgt).
  Notation lab_rules := (lab_rules beq_ok pi).
 
  Section props.

    Variables E R : set (rule Sig).

    Variable ge_compatE : forall l r, E (mkRule l r) -> l >=I r.
    Variable ge_compatR : forall l r, R (mkRule l r) -> l >=I r.

    Lemma WF_red_mod_lab : WF (red_mod E R)
      <-> WF (red_mod (union Decr (lab_rules E)) (lab_rules R)).

    Proof.
      rewrite WF_red_mod_lab. refl. apply pi_mon. apply I_mon.
      apply ge_compatE. apply ge_compatR.
    Qed.

    Lemma WF_hd_red_mod_lab : WF (hd_red_mod E R)
      <-> WF (hd_red_mod (union Decr (lab_rules E)) (lab_rules R)).

    Proof.
      rewrite WF_hd_red_mod_lab. refl. apply pi_mon. apply I_mon.
      apply ge_compatE.
    Qed.

    Lemma WF_red_lab : WF (red R) <-> WF (red_mod Decr (lab_rules R)).

    Proof.
      rewrite WF_red_lab. refl. apply pi_mon. apply I_mon. apply ge_compatR.
    Qed.

  End props.

End OrdSemLabProps.

(***********************************************************************)
(** functor providing the properties of a semantic labelling
with unordered labels *)

Module SemLabProps (SL : SemLab).

  Module Import OSL := Ord SL.

  Module Import Props := OrdSemLabProps OSL.

  Section props.

    Variables E R : set (rule Sig).

    Variable ge_compatE : forall l r, E (mkRule l r) -> l >=I r.
    Variable ge_compatR : forall l r, R (mkRule l r) -> l >=I r.

    Lemma WF_red_mod_lab : WF (red_mod E R)
      <-> WF (red_mod (lab_rules E) (lab_rules R)).

    Proof.
      rewrite WF_red_mod_lab. 2: apply ge_compatE. 2: apply ge_compatR.
      rewrite Decr_empty, union_empty_l. refl.
    Qed.

    Lemma WF_hd_red_mod_lab : WF (hd_red_mod E R)
      <-> WF (hd_red_mod (lab_rules E) (lab_rules R)).

    Proof.
      rewrite WF_hd_red_mod_lab. 2: apply ge_compatE.
      rewrite Decr_empty, union_empty_l. refl.
    Qed.

    Lemma WF_red_lab : WF (red R) <-> WF (red (lab_rules R)).

    Proof.
      rewrite WF_red_lab. 2: apply ge_compatR.
      rewrite Decr_empty, red_mod_empty. refl.
    Qed.

  End props.

End SemLabProps.

(***********************************************************************)
(** functor providing the properties of a finite semantic labelling
with ordered labels *)

Import ATrs. Infix "++" := app. (*COQ: why Import List does not work?*)

Module FinOrdSemLabProps (Import FOSL : FinOrdSemLab).

  Module LabSig.

    Definition Sig := lab_sig Sig beq_ok.
    Definition Fs := Fs_lab Fs Ls.
    Definition Fs_ok := Fs_lab_ok beq_ok Fs_ok Ls_ok.

    Notation unlab_rules := (unlab_rules_fin Sig beq_ok).

    Ltac unlab :=
      match goal with
        | |- WF (red_mod _ _) => apply (WF_red_mod_unlab_fin beq_ok)
        | |- WF (hd_red_mod _ _) => apply (WF_hd_red_mod_unlab_fin beq_ok)
        | |- WF (red _) => apply (WF_red_unlab_fin beq_ok)
      end.

  End LabSig.

  Notation Decr := (enum_Decr beq_ok Fs L2s).
  Notation lab_rules := (enum beq_ok pi Is).

  Section props.

    Variables E R : rules Sig.

    Variable bge_compatE : forallb (brule bge) E = true.
    Variable bge_compatR : forallb (brule bge) R = true.

    Lemma WF_red_mod_lab : WF (red_mod E R)
      <-> WF (red_mod (Decr ++ lab_rules E) (lab_rules R)).

    Proof.
      rewrite WF_red_mod_lab_fin. refl. apply pi_mon. apply I_mon.
      apply Is_ok. apply Fs_ok. apply L2s_ok. apply bge_ok.
      apply bge_compatE. apply bge_compatR.
    Qed.

    Lemma WF_hd_red_mod_lab : WF (hd_red_mod E R)
      <-> WF (hd_red_mod (Decr ++ lab_rules E) (lab_rules R)).

    Proof.
      rewrite WF_hd_red_mod_lab_fin. refl. apply pi_mon. apply I_mon.
      apply Is_ok. apply Fs_ok. apply L2s_ok. apply bge_ok. apply bge_compatE.
    Qed.

    Lemma WF_red_lab : WF (red R) <-> WF (red_mod Decr (lab_rules R)).

    Proof.
      rewrite WF_red_lab_fin. refl. apply pi_mon. apply I_mon.
      apply Is_ok. apply Fs_ok. apply L2s_ok. apply bge_ok. apply bge_compatR.
    Qed.

  End props.

  Ltac semlab :=
    match goal with
      | |- WF (red_mod _ _) => rewrite WF_red_mod_lab;
        [ idtac
        | check_eq || fail 10 "some relative rule is not in the model"
        | check_eq || fail 10 "some rule is not in the model"]
      | |- WF (hd_red_mod _ _) => rewrite WF_hd_red_mod_lab;
        [ idtac
        | check_eq || fail 10 "some relative rule is not in the model"]
      | |- WF (red _) => rewrite WF_red_lab;
        [ idtac
        | check_eq || fail 10 "some rule is not in the model"]
    end.

End FinOrdSemLabProps.

(***********************************************************************)
(** functor providing the properties of a finite semantic labelling
with unordered labels *)

Module FinSemLabProps (FSL : FinSemLab).

  Module Import FOSL := FinOrd FSL.

  Module Import Props := FinOrdSemLabProps FOSL.

  Module LabSig := LabSig.

  Import FSL.

  Section props.

    Variables E R : rules Sig.

    Variable bge_compatE : forallb (brule bge) E = true.
    Variable bge_compatR : forallb (brule bge) R = true.

    Lemma WF_red_mod_lab : WF (red_mod E R)
      <-> WF (red_mod (lab_rules E) (lab_rules R)).

    Proof.
      rewrite WF_red_mod_lab. 2: apply bge_compatE. 2: apply bge_compatR.
      rewrite enum_Decr_empty. refl.
    Qed.

    Lemma WF_hd_red_mod_lab : WF (hd_red_mod E R)
      <-> WF (hd_red_mod (lab_rules E) (lab_rules R)).

    Proof.
      rewrite WF_hd_red_mod_lab. 2: apply bge_compatE.
      rewrite enum_Decr_empty. refl.
    Qed.

    Lemma WF_red_lab : WF (red R) <-> WF (red (lab_rules R)).

    Proof.
      rewrite WF_red_lab. 2: apply bge_compatR.
      rewrite enum_Decr_empty, red_mod_empty. refl.
    Qed.

  End props.

  Ltac semlab :=
    match goal with
      | |- WF (red_mod _ _) => rewrite WF_red_mod_lab;
        [ idtac
        | check_eq || fail 10 "some relative rule is not in the model"
        | check_eq || fail 10 "some rule is not in the model"]
      | |- WF (hd_red_mod _ _) => rewrite WF_hd_red_mod_lab;
        [ idtac
        | check_eq || fail 10 "some relative rule is not in the model"]
      | |- WF (red _) => rewrite WF_red_lab;
        [idtac
        | check_eq || fail 10 "some rule is not in the model"]
    end.

End FinSemLabProps.
