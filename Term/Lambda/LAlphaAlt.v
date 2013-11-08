(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2013-09-24

* Other definitions of alpha-equivalence
*)

Set Implicit Arguments.

Require Import LogicUtil LAlpha RelUtil Morphisms BoolUtil.

(***********************************************************************)
(** * Other definitions of alpha-equivalence. *)

Module Export Def.

  Section aeq.

    (** We assume given decidable sets [F] and [X] for function
    symbols and variables respectively. *)

    Variables (F X : Type)
      (eq_fun_dec : forall f g : F, {f=g}+{~f=g})
      (eq_var_dec : forall x y : X, {x=y}+{~x=y}).

    Notation Te := (@Te F X).
    Notation Var := (@Var F X).
    Notation Fun := (@Fun F X).
    Notation rename1 := (@rename1 F X eq_var_dec).

    (** We assume given a structure for finite sets on [X]. *)

    Variable ens_X : Ens X.

    Notation In := (@Ens_In X ens_X).
    Notation fv := (@fv F X ens_X).
    Notation bv := (@bv F X ens_X).

    (** We assume that [X] is infinite. *)

    Variable var_notin : Ens_type ens_X -> X.

    Notation rename := (@rename F X eq_fun_dec eq_var_dec ens_X var_notin).

(***********************************************************************)
(** Replace every occurrence of a variable [x] by [y], including
binding occurrences. *)

    Definition replace_var x y z :=
      match eq_var_dec z x with left _ => y | _ => z end.

    Fixpoint replace_all x y u :=
      match u with
        | Def.Var z => Var (replace_var x y z)
        | Def.Fun _ => u
        | Def.App u1 u2 => App (replace_all x y u1) (replace_all x y u2)
        | Def.Lam z v => Lam (replace_var x y z) (replace_all x y v)
      end.

    Lemma size_replace_all : forall x y t, size (replace_all x y t) = size t.

    Proof.
      intros x y. induction t; simpl. refl. refl.
      rewrite IHt1, IHt2. refl. rewrite IHt. refl.
    Qed.

(***********************************************************************)
(** ** Church's definition (1932)

in his first paper on lambda-calculus, "A set of postulates for the
foundations of logic", Annals of Mathematics, 33(2):346–366, 1932. *)

    Inductive aeq_ch_top : relation Te :=
    | aeq_ch_top_intro : forall L x y, ~In x (fv L) -> ~In y (fv L) ->
      ~In y (bv L) -> aeq_ch_top L (replace_all x y L).

    Definition aeq_ch : relation Te := clos_refl_trans (clos_mon aeq_ch_top).

(***********************************************************************)
(** ** Krivine's definition (1993)

in his book (in French) "Lambda-calcul, types et modèles", Ellis
Horwood, 1993. English translation due to René Cori available on
http://cel.archives-ouvertes.fr/cel-00574575/fr/ . *)

    Inductive aeq_kr : relation Te :=
    | aeq_kr_fun : forall f, aeq_kr (Fun f) (Fun f)
    | aeq_kr_var : forall x, aeq_kr (Var x) (Var x)
    | aeq_kr_app : forall u v u' v',
      aeq_kr u u' -> aeq_kr v v' -> aeq_kr (App u v) (App u' v')
    | aeq_kr_lam : forall x u x' u' xs,
      (forall y, ~In y xs -> aeq_kr (rename1 x y u) (rename1 x' y u')) ->
      aeq_kr (Lam x u) (Lam x' u').

  End aeq.

End Def.

(***********************************************************************)
(** * Properties of and relations between these different definitions. *)

Module Make (Export L : L_Struct).

  Module Export A := LAlpha.Make L.

  Notation replace_var := (@replace_var X XOrd.eq_dec).
  Notation replace_all := (@replace_all F X XOrd.eq_dec).
  Notation aeq_ch_top := (@aeq_ch_top F X XOrd.eq_dec ens_X).
  Notation aeq_ch := (@aeq_ch F X XOrd.eq_dec ens_X).
  Notation aeq_kr := (@aeq_kr F X XOrd.eq_dec ens_X).

(***********************************************************************)
(** ** Properties of [replace_var]. *)

  Lemma replace_var_eq x y : replace_var x y x = y.

  Proof. unfold Def.replace_var. eq_dec x x; fo. Qed.

  Lemma replace_var_id x y : replace_var x x y = y.

  Proof. unfold Def.replace_var. eq_dec y x; fo. Qed.

  Lemma replace_var2 x y z :
    x = z \/ y <> z -> replace_var y x (replace_var x y z) = z.

  Proof.
    intro h. unfold Def.replace_var. eq_dec z x.
    subst. eq_dec y y. refl. irrefl.
    eq_dec z y. subst. fo. refl.
  Qed.

(***********************************************************************)
(** ** Properties of [replace_all]. *)

  Lemma replace_all_id x : forall u, replace_all x x u = u.

  Proof.
    induction u; simpl.
    rewrite replace_var_id. refl.
    refl.
    rewrite IHu1, IHu2. refl.
    rewrite replace_var_id, IHu. refl.
  Qed.

  Lemma replace_all2 x y : forall u, ~In y (fv u) -> ~In y (bv u) ->
    replace_all y x (replace_all x y u) = u.

  Proof.
    induction u; simpl; set_iff; intros h1 h2.
    rewrite replace_var2. refl. fo.
    refl. apply (f_equal2 App); fo. apply (f_equal2 Lam).
    rewrite replace_var2. refl. fo. fo.
  Qed.

  Lemma notin_fv_replace_all x y : x <> y ->
    forall u, ~In x (fv (replace_all x y u)).

  Proof.
    intro n.
    induction u; simpl; set_iff; unfold Def.replace_var; eq_dec x0 x; fo.
  Qed.

  Lemma notin_bv_replace_all x y : x <> y ->
    forall u, ~In x (bv (replace_all x y u)).

  Proof.
    intro n.
    induction u; simpl; set_iff; unfold Def.replace_var; eq_dec x0 x; fo.
  Qed.

  Lemma fv_replace_all x y : forall u,
    ~In y (bv u) -> ~In y (fv u) -> fv (replace_all x y u)
      [=] if mem x (fv u) then add y (remove x (fv u)) else fv u.

  Proof.
    induction u; simpl; set_iff; intros h1 h2; mem.
    (* var *)
    unfold Def.replace_var, eqb. eq_dec x0 x. subst. fset. refl.
    (* fun *)
    refl.
    (* app *)
    rewrite IHu1; [idtac|fo|fo]. rewrite IHu2; [idtac|fo|fo].
    case_eq (mem x (fv u1)); case_eq (mem x (fv u2)); simpl;
      try (rewrite <- mem_iff); try (rewrite <- not_mem_iff); intros i1 i2.
    rewrite remove_union, !add_union_singleton, union_assoc,
      <- union_assoc with (s:=remove x (fv u1)),
      union_sym with (s:=remove x (fv u1)), union_assoc, union_idem_1. refl.
    rewrite remove_union, remove_equal with (s:=fv u2), union_add; fo.
    rewrite remove_union, remove_equal with (s:=fv u1),
      union_sym, union_add, union_sym; fo.
    refl.
    (* lam *)
    rewrite IHu; [idtac|fo|fo]. unfold Def.replace_var, eqb.
    eq_dec x0 x; simpl; bool.
    subst. case_eq (mem x (fv u)); try (rewrite <- mem_iff);
      try (rewrite <- not_mem_iff); intro h.
    rewrite remove_add. refl. set_iff. fo.
    rewrite !remove_equal. refl. fo. fo.
    case_eq (mem x (fv u)); try (rewrite <- mem_iff);
      try (rewrite <- not_mem_iff); intro h.
    rewrite <- remove_add_com, remove_com; fo.
    refl.
  Qed.

  Lemma replace_all_aeq_rename x y : forall u,
    ~In y (fv u) -> ~In y (bv u) -> replace_all x y u ~~ rename x y u.

  Proof.
    induction u; simpl; set_iff; intros h1 h2.
    (* var *)
    rewrite rename_var. unfold Def.replace_var, eqb. eq_dec x0 x; refl.
    (* fun *)
    refl.
    (* app *)
    rewrite rename_app, IHu1, IHu2; fo.
    (* lam *)
    rewrite IHu; [idtac|fo|fo]. unfold Def.replace_var. eq_dec x0 x.
    subst x0. rewrite rename_notin_fv with (u:=Lam x u). 2: simpl; set_iff; fo.
    sym. apply aeq_alpha. fo.
    rewrite rename_lam. unfold eqb at 2. eq_dec y x0. fo. bool.
    unfold eqb. eq_dec x0 x. fo. refl.
  Qed.

(***********************************************************************)
(** ** Properties of Church's definition. *)

  (** [aeq_ch] is a congruence relation. *)

  Instance aeq_ch_refl : Reflexive aeq_ch.

  Proof. unfold Def.aeq_ch. class. Qed.

  Instance aeq_ch_trans : Transitive aeq_ch.

  Proof. unfold Def.aeq_ch. class. Qed.

  Instance aeq_ch_top_sym : Symmetric aeq_ch_top.

  Proof.
    intros u v uv. inversion uv; clear uv; subst; unfold Ens_In in *.
    rewrite not_mem_iff in H. set (v := replace_all x y u).
    rewrite <- replace_all2 with (x:=x) (y:=y); auto.    
    apply aeq_ch_top_intro; ens.
    rewrite fv_replace_all; [idtac|fo|fo]. rewrite H. hyp.
    rewrite fv_replace_all; [idtac|fo|fo]. rewrite H, not_mem_iff. hyp.
    eq_dec x y. subst y. rewrite replace_all_id. hyp.
    apply notin_bv_replace_all. hyp.
  Qed.

  Instance aeq_ch_sym : Symmetric aeq_ch.

  Proof. apply rtc_sym. apply clos_mon_sym. class. Qed.

  Instance aeq_ch_mon : Monotone aeq_ch.

  Proof. unfold Def.aeq_ch. class. Qed.

  (** [aeq_ch] is equivalent to [aeq]. *)

  Lemma aeq_ch_le_aeq : aeq_ch << aeq.

  Proof.
    apply rtc_min. constructor; class. apply clos_mon_min. class.
    intros u v uv; inversion uv; clear uv; subst.
    rewrite replace_all_aeq_rename; [idtac|fo|fo]. rewrite rename_notin_fv; fo.
  Qed.

  Lemma aeq_le_aeq_ch : aeq << aeq_ch.

  Proof.
    intro u; revert u.
    ind_size1 u; intros u' uu'; inv_aeq uu'; subst; ens. refl. refl.
    trans (App u v).
    apply mon_app_l. class. fo. fo. apply mon_app_r. class. fo. fo.
    rename x0 into y. rename u0 into v.
    set (xs := union
      (add x (union (fv u) (bv u))) (add y (union (fv v) (bv v)))).
    gen (var_notin_ok xs). set (z := var_notin xs).
    unfold xs. set_iff. intro hz.
    trans (replace_all x z (Lam x u)).
    apply rt_step. apply m_step. apply aeq_ch_top_intro; simpl; set_iff; fo.
    trans (replace_all y z (Lam y v)).
    Focus 2. sym. apply rt_step. apply m_step.
    apply aeq_ch_top_intro; simpl; set_iff; fo.
    simpl. rewrite !replace_var_eq. apply mon_lam. class. refl.
    apply hu. rewrite size_replace_all. refl.
    rewrite !replace_all_aeq_rename, i0, rename2; fo.
  Qed.

(***********************************************************************)
(** ** Properties of Krivine's definition. *)

  (** [aeq_kr] is an equivalence relation. *)

  Instance aeq_kr_refl : Reflexive aeq_kr.

  Proof.
    intro u; revert u. ind_size1 u.
    apply aeq_kr_var.
    apply aeq_kr_fun.
    apply aeq_kr_app; hyp.
    apply aeq_kr_lam with (xs:=empty); simpl.
    intros y hy. apply hu. rewrite size_rename1. refl.
  Qed.

  Instance aeq_kr_sym : Symmetric aeq_kr.

  Proof.
    intro u; revert u. ind_size1 u; intros t' h; inversion h; clear h; subst.
    refl. refl. apply aeq_kr_app; fo.
    apply aeq_kr_lam with (xs:=xs). intros y hy. apply hu.
    rewrite size_rename1. refl. fo.
  Qed.

  Instance aeq_kr_trans : Transitive aeq_kr.

  Proof.
    intro u; revert u. ind_size1 u; intros b c tb bc;
      inversion tb; clear tb; subst; inversion bc; clear bc; subst.
    refl. refl. apply aeq_kr_app; fo.
    apply aeq_kr_lam with (xs:=union xs xs0). intro y. set_iff. intro hy.
    apply hu with (y:=rename1 x' y u'). rewrite size_rename1; refl. fo. fo.
  Qed.

  (** [aeq_kr] is equivalent to [aeq]. *)

  Lemma aeq_le_aeq_kr : aeq << aeq_kr.

  Proof.
    intro u; revert u. ind_size1 u; intros t' tt'; inv_aeq tt'; subst.
    refl. refl. apply aeq_kr_app; fo. clear tt'.
    pose (xs := union (bv u) (bv u0)).
    apply aeq_kr_lam with (xs := xs); ens. intro y.
    unfold xs. set_iff. intro hy.
    apply hu. rewrite size_rename1. refl.
    rewrite <- !rename1_no_alpha, i0, rename2. refl. hyp. fo. fo.
  Qed.

  Lemma aeq_kr_le_aeq : aeq_kr << aeq.

  Proof.
    intro u; revert u; induction 1.
    refl. refl. rewrite IHaeq_kr1, IHaeq_kr2. refl.
    pose (xs' := union xs (union (bv u) (union (bv u') (union (fv u)
      (fv u'))))). gen (var_notin_ok xs'). set (y := var_notin xs').
    unfold xs'. set_iff. intro hy.
    rewrite aeq_alpha with (y:=y), aeq_alpha with (x:=x') (y:=y). 2: fo. 2: fo.
    apply Lam_aeq. refl. rewrite !rename1_no_alpha. fo.
    right. right. fo. right. right. fo.
  Qed.

End Make.
