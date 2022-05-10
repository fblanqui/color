(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2013-09-24

* Alternative definitions of alpha-equivalence
*)

Set Implicit Arguments.

From CoLoR Require Import LogicUtil LAlpha RelUtil BoolUtil.
From Coq Require Import Morphisms.

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
    Notation add := (@Ens_add X ens_X).
    Notation union := (@Ens_union X ens_X).
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
(** Action of a function on variables, including binding occurrences. *)

  Fixpoint action (f : X -> X) u :=
    match u with
      | Def.Var x => Var (f x)
      | Def.Fun f => Fun f
      | Def.App u1 u2 => App (action f u1) (action f u2)
      | Def.Lam x v => Lam (f x) (action f v)
    end.

(***********************************************************************)
(** Permutation of x and y. *)

    Definition transpose_var x y z :=
      match eq_var_dec z x with
        | left _ => y
        | _ => match eq_var_dec z y with left _ => x | _ => z end
      end.

    Definition transpose x y := action (transpose_var x y).

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

(***********************************************************************)
(** ** Gabbay and Pitts's definition (1999)

in their paper "A New Approach to Abstract Syntax Involving Binders",
Proceedings of the 14th IEEE Symposium on Logic in Computer Science
(LICS), 1999. *)

    Inductive aeq_gp : relation Te :=
    | aeq_gp_refl_fun : forall f, aeq_gp (Fun f) (Fun f)
    | aeq_gp_refl_var : forall x, aeq_gp (Var x) (Var x)
    | aeq_gp_app : forall u v u' v',
      aeq_gp u u' -> aeq_gp v v' -> aeq_gp (App u v) (App u' v')
    | aeq_gp_lam : forall x u x' u' z,
      ~In z (union (add x (union (fv u) (bv u)))
                   (add x' (union (fv u') (bv u')))) ->
      aeq_gp (transpose z x u) (transpose z x' u') ->
      aeq_gp (Lam x u) (Lam x' u').

  End aeq.

End Def.

(***********************************************************************)
(** * Properties of and relations between these different definitions. *)

Module Make (Export L : L_Struct).

  Module Export A := LAlpha.Make L.

  Notation replace_var := (@replace_var X XOrd.eq_dec).
  Notation replace_all := (@replace_all F X XOrd.eq_dec).
  Notation transpose_var := (@transpose_var X XOrd.eq_dec).
  Notation transpose := (@transpose F X XOrd.eq_dec).
  Notation aeq_ch_top := (@aeq_ch_top F X XOrd.eq_dec ens_X).
  Notation aeq_ch := (@aeq_ch F X XOrd.eq_dec ens_X).
  Notation aeq_kr := (@aeq_kr F X XOrd.eq_dec ens_X).
  Notation aeq_gp := (@aeq_gp F X XOrd.eq_dec ens_X).
  Notation action := (@action F X).

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
    subst. eq_dec y y. refl. cong.
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
    refl. f_equal; fo. f_equal. rewrite replace_var2. refl. fo. fo.
  Qed.

  Lemma notin_fv_replace_all x y : x <> y ->
    forall u, ~In x (fv (replace_all x y u)).

  Proof.
    intro n.
    induction u; simpl; set_iff; unfold Def.replace_var; try (eq_dec x0 x); fo.
  Qed.

  Lemma notin_bv_replace_all x y : x <> y ->
    forall u, ~In x (bv (replace_all x y u)).

  Proof.
    intro n.
    induction u; simpl; set_iff; unfold Def.replace_var; try (eq_dec x0 x); fo.
  Qed.

  Lemma fv_replace_all x y : forall u,
    ~In y (bv u) -> ~In y (fv u) -> fv (replace_all x y u)
      [=] if mem x (fv u) then add y (remove x (fv u)) else fv u.

  Proof.
    induction u; simpl; set_iff; intros h1 h2; mem.
    (* var *)
    unfold Def.replace_var. eq_dec x0 x. subst. fset. refl.
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
    rewrite IHu; [idtac|fo|fo]. unfold Def.replace_var.
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
    rewrite rename_var. unfold Def.replace_var. eq_dec x0 x; refl.
    (* fun *)
    refl.
    (* app *)
    rewrite rename_app, IHu1, IHu2; firstorder auto with crelations.
    (* lam *)
    rewrite IHu; [idtac|fo|fo]. unfold Def.replace_var. eq_dec x0 x.
    subst x0. rewrite rename_notin_fv with (u:=Lam x u). 2: simpl; set_iff; fo.
    sym. apply aeq_alpha. fo.
    rewrite rename_lam. eq_dec y x0. firstorder auto with exfalso. bool. eq_dec x0 x. fo. refl.
  Qed.

(***********************************************************************)
(** ** Properties of [action]. *)

  Lemma action_eq f g : forall u,
    (forall x, In x (fv u) \/ In x (bv u) -> f x = g x) ->
    action f u = action g u.

  Proof.
    induction u; intro h; simpl; f_equal.
    apply h. left. simpl. set_iff. refl.
    apply IHu1. intros x hx. apply h. simpl. set_iff. destruct hx; tauto.
    apply IHu2. intros x hx. apply h. simpl. set_iff. destruct hx; tauto.
    apply h. simpl. set_iff. tauto.
    apply IHu. intros y hy. apply h. simpl. set_iff. destruct hy; tauto.
  Qed.

  Lemma size_action f : forall u, size (action f u) = size u.

  Proof.
    induction u; simpl. refl. refl. rewrite IHu1, IHu2. refl. rewrite IHu. refl.
  Qed.

  Lemma action_comp f g :
    forall u, action f (action g u) = action (fun x => f (g x)) u.

  Proof.
    induction u; simpl. refl. refl. rewrite IHu1, IHu2. refl. rewrite IHu. refl.
  Qed.

(***********************************************************************)
(** ** Properties of [transpose_var]. *)

  Lemma transpose_var_id x z : transpose_var x x z = z.

  Proof. unfold Def.transpose_var. eq_dec z x; subst; refl. Qed.

  Lemma transpose_var_sym x y z : transpose_var x y z = transpose_var y x z.

  Proof. unfold Def.transpose_var. eq_dec z x; eq_dec z y; subst; auto. Qed.

  Lemma transpose_var_com a b c d z : a <> c -> a <> d -> b <> c -> b <> d ->
    transpose_var a b (transpose_var c d z)
    = transpose_var c d (transpose_var a b z).

  Proof.
    intros nac nad nbc nbd. unfold Def.transpose_var.
    eq_dec z c; subst. eq_dec d a; subst. cong. eq_dec d b; subst. cong.
    eq_dec c a; subst. cong. eq_dec c b; subst. cong. eq_dec c c; subst.
    refl. cong. eq_dec z d; subst. eq_dec c a; subst. cong.
    eq_dec c b; subst. cong. eq_dec d a; subst. cong. eq_dec d b; subst.
    cong. eq_dec d c; subst. refl. eq_dec d d; subst. refl. cong.
    eq_dec z a; subst. eq_dec b c; subst. cong. eq_dec b d; subst. cong.
    refl. eq_dec z b; subst. eq_dec a c; subst. cong. eq_dec a d; subst.
    cong. refl. eq_dec z c; subst. cong. eq_dec z d; subst. cong. refl.
  Qed.

  Lemma transpose_var_idem x y z : transpose_var x y (transpose_var x y z) = z.

  Proof.
    unfold Def.transpose_var. eq_dec z x; subst.
    eq_dec y x; subst. refl. eq_dec y y; subst. refl. cong.
    eq_dec z y; subst. eq_dec x x; subst. refl. cong.
    eq_dec z x; subst. cong. eq_dec z y; subst. cong. refl.
  Qed.

  Lemma transpose_var_comp a b c z : b <> z -> c <> z ->
    transpose_var b c (transpose_var a b z) = transpose_var a c z.

  Proof.
    intros nbz ncz. unfold Def.transpose_var. eq_dec z a; subst.
    eq_dec b b; subst. refl. cong. eq_dec z b; subst. cong.
    eq_dec z b; subst. cong. eq_dec z c; subst. cong. refl.
  Qed.

(***********************************************************************)
(** ** Properties of [transpose]. *)

  Lemma transpose_id x : forall u, transpose x x u = u.

  Proof.
    unfold Def.transpose. induction u; simpl; repeat rewrite transpose_var_id.
    refl. refl. rewrite IHu1, IHu2. refl. rewrite IHu. refl.
  Qed.

  Lemma transpose_sym x y : forall u, transpose x y u = transpose y x u.

  Proof.
    unfold Def.transpose. induction u; simpl.
    rewrite transpose_var_sym. refl.
    refl.
    rewrite IHu1, IHu2. refl.
    rewrite IHu, transpose_var_sym, transpose_var_sym with (x:=y). refl.
  Qed.

  Lemma transpose_comp a b c : forall u, ~In b (fv u) -> ~In b (bv u) ->
                                         ~In c (fv u) -> ~In c (bv u) ->
    transpose b c (transpose a b u) = transpose a c u.

  Proof.
    unfold Def.transpose.
    induction u; simpl; set_iff; intros h1 h2 h3 h4; f_equal;
      try apply transpose_var_comp; fo.
  Qed.

(***********************************************************************)
(** ** Substitution corresponding to [transpose_var]. *)

  Definition subs_transpose a b x := Var (transpose_var a b x).

  Lemma domain_subs_transpose a b : forall xs, domain xs (subs_transpose a b)
    [=] if eqb a b then empty else inter xs (add a (singleton b)).

  Proof.
    apply set_induction_bis.
    (* Equal *)
    intros xs xs' xsxs'. destruct (eqb a b); rewrite xsxs'; auto.
    (* empty *)
    rewrite domain_empty. destruct (eqb a b). refl. rewrite inter_empty_l. refl.
    (* add *)
    intros x xs n IH. rewrite domain_add, IH. 2: hyp. unfold Def.domain_fun.
    ens. unfold subs_transpose, Def.transpose_var. rewrite beq_term_var.
    eq_dec x a. subst. eq_dec a b; eq_dec b a. refl. firstorder auto with exfalso. firstorder auto with exfalso.
    intro; set_iff; tauto.
    eq_dec x b. subst. eq_dec a b. refl. intro; set_iff; tauto.
    eq_dec x x. 2: cong. eq_dec a b. refl.
    intro y. set_iff. split_all; subst; cong.
  Qed.

  Lemma fvcod_subs_transpose a b : forall xs, fvcod xs (subs_transpose a b)
    [=] union (remove a (remove b xs))
              (union (if mem a xs then singleton b else empty)
                     (if mem b xs then singleton a else empty)).

  Proof.
    apply set_induction_bis.
    (* Equal *)
    intros xs xs' xsxs'. (*SLOW*)rewrite xsxs'. auto.
    (* empty *)
    mem. rewrite fvcod_empty. intro; set_iff; tauto.
    (* add *)
    intros x xs n IH. rewrite fvcod_add, IH. 2: hyp. mem. unfold Def.fvcod_fun.
    ens. rewrite remove_add_if, eqb_sym.
    unfold subs_transpose, Def.transpose_var, eqb.
    eq_dec x a; eq_dec x b; do 2 subst; simpl.
    rewrite !union_idem, !remove_idem.
    destruct (mem b xs); intro; set_iff; tauto.
    rewrite not_mem_iff in n.
    rewrite n, remove_add_eq, union_empty_l, union_sym_2. refl.
    rewrite not_mem_iff in n. rewrite n.
    destruct (mem a xs); intro; set_iff; tauto.
    rewrite remove_add_if. eq_dec a x. subst. cong.
    rewrite add_union_singleton, union_assoc. refl.
  Qed.

  Lemma fvcodom_subs_transpose a b xs :
    fvcodom xs (subs_transpose a b) [=] if eqb a b then empty
      else union (if mem a xs then singleton b else empty)
                 (if mem b xs then singleton a else empty).

  Proof.
    unfold Def.fvcodom. rewrite domain_subs_transpose.
    eq_dec a b. rewrite fvcod_empty. refl.
    rewrite fvcod_subs_transpose. mem. bool.
    rewrite !remove_inter, <- remove_add_com. 2: hyp.
    rewrite remove_singleton, remove_add_eq, remove_empty, inter_empty_r,
      union_empty_l. refl.
  Qed.

  Lemma transpose_subs a b : forall u, ~In a (bv u) -> ~In b (bv u) ->
    transpose a b u = subs (subs_transpose a b) u.

  Proof.
    unfold Def.transpose. induction u; simpl Def.bv; simpl Def.fv;
      simpl Def.action; set_iff; intros h1 h2.
    simpl. unfold subs_transpose, Def.transpose_var.
    eq_dec x a; eq_dec x b; do 2 subst; refl.
    refl.
    rewrite IHu1, IHu2; fo.
    (* Lam *)
    rewrite IHu; [idtac|fo|fo].

    assert (h : transpose_var a b x = x).
    unfold Def.transpose_var. eq_dec x a. fo. eq_dec x b. fo. refl.

    rewrite h, subs_lam_no_alpha.
    2:{ rewrite fvcodom_subs_transpose. eq_dec a b. set_iff. fo.
    mem. eq_dec x a. fo. eq_dec x b. fo. bool.
    destruct (mem a (fv u)); destruct (mem b (fv u)); set_iff; fo. }

    f_equal. rewrite update_id. refl. unfold subs_transpose. rewrite h. refl.
  Qed.

  Lemma transpose_rename x y :
    forall u, ~In y (fv u) -> ~In y (bv u) -> transpose x y u ~~ rename x y u.

  Proof.
    unfold Def.transpose.
    induction u; simpl; set_iff; intros h1 h2; unfold Def.rename.
    unfold Def.transpose_var, Def.single, Def.update; simpl.
    eq_dec x0 x. refl. eq_dec x0 y. subst. cong. refl.
    refl.
    rewrite IHu1; [idtac|fo|fo]. rewrite IHu2; [idtac|fo|fo]. refl.
    rewrite IHu; [idtac|fo|fo]. rewrite subs_lam_no_alpha.
    2:{ rewrite fvcodom_single.
    destruct (mem x (remove x0 (fv u)) && negb (beq_term (Var y) (Var x))).
    simpl. set_iff. fo. set_iff. fo. }
    unfold Def.transpose_var. eq_dec x0 x. subst.
    rewrite <- aeq_alpha. 2: fo. rewrite update_single_eq, single_id. refl.
    eq_dec x0 y. fo. rewrite update_id_single. 2: fo. refl.
  Qed.

  (** [transpose] is invariant by [aeq]. *)

  Global Instance transpose_aeq a b : Proper (aeq ==> aeq) (transpose a b).

  Proof.
    unfold Def.transpose.
    intro u; revert u. ind_size1 u; intros u' uu'; inv_aeq uu'; subst; simpl.
    refl. refl.
    rewrite hu with (y:=u), hv with (y:=u1). refl. hyp. hyp.
    (* Lam *)
    rename x0 into y. rename u0 into v.
    rewrite hu with (u':=v) (y:=rename x y u).
    2: rewrite i0, size_rename; refl. 2: hyp.
    eq_dec x y. subst. rewrite rename_id. refl.
    eq_dec a b. subst.
    fold (transpose b b u). fold (transpose b b (rename x y u)).
    rewrite !transpose_var_id, !transpose_id. apply aeq_alpha. fo.

    destruct (aeq_notin_bv (add y (add a (singleton b))) u) as [u' [h1 h2]].
    rewrite inter_sym, inter_empty in h2.
    assert (ha : ~In a (bv u')). apply h2. set_iff. auto.
    assert (hb : ~In b (bv u')). apply h2. set_iff. auto.
    assert (hy : ~In y (bv u')). apply h2. set_iff. auto.

    rewrite hu with (u':=u) (y:=u'). 2: refl. 2: hyp.
    rewrite hu with (u':=rename x y u) (y:=rename x y u').
    2: rewrite size_rename; refl. 2: rewrite h1; refl.
    fold (transpose a b u'). fold (transpose a b (rename x y u')).
    rewrite transpose_subs; auto. rewrite transpose_subs.
    2: rewrite bv_rename; auto. 2: rewrite bv_rename; auto.
    rewrite <- h1, <- i0.

    clear u' h1 h2 ha hb hy.
    set (x' := transpose_var a b x). set (y' := transpose_var a b y).
    set (u' := subs (subs_transpose a b) u).
    set (v' := subs (subs_transpose a b) v).
    set (xs := union (fv u') (fv v')). gen (var_notin_ok xs).
    set (z := var_notin xs). unfold xs. set_iff. split_all. cong.
    rewrite aeq_alpha with (y:=z). 2: hyp.
    rewrite aeq_alpha with (x:=y') (y:=z). 2: hyp.
    unfold u', v'. rewrite i0. unfold Def.rename. rewrite !subs_comp.
    apply aeq_refl_eq. f_equal. apply subs_seq.
    intros c hc. do 2 (unfold Def.comp at 1). unfold subs_transpose at 1.
    unfold x', y'. unfold Def.transpose_var. simpl. unfold Def.single.
    unfold Def.update at 3. eq_dec c x.
    (* c = x *)
    subst. rewrite update_eq. unfold Def.comp, subs_transpose. simpl.
    unfold Def.transpose_var. rewrite update_eq. refl.
    (* c <> x *)
    unfold Def.id at 3. unfold Def.comp, subs_transpose. simpl.
    unfold Def.transpose_var. eq_dec c y. subst. fo.
    eq_dec c a. subst. eq_dec x a. subst. cong.
    eq_dec y a. subst. cong. eq_dec x b. subst. rewrite update_neq. 2: hyp.
    eq_dec y b. subst. cong. rewrite update_neq; auto.
    rewrite update_neq. 2: hyp. eq_dec y b. subst.
    rewrite update_neq; auto. rewrite update_neq; auto.
    eq_dec x a. subst. eq_dec c b. subst. eq_dec y b. subst. cong.
    rewrite update_neq. 2: hyp. eq_dec y a. rewrite update_neq; auto.
    rewrite update_neq; auto. rewrite update_neq. 2: auto.
    eq_dec y a. subst. cong. eq_dec y b. rewrite update_neq; auto.
    unfold Def.update. eq_dec c y. subst. cong. refl.
    eq_dec x b. subst. eq_dec c b. subst. cong. rewrite update_neq. 2: auto.
    eq_dec y a. subst. rewrite update_neq; auto. eq_dec y b.
    rewrite update_neq; auto. unfold Def.update. eq_dec c y.
    subst. cong. refl. eq_dec c b. subst. rewrite update_neq. 2: hyp.
    eq_dec y a. subst. rewrite update_neq; auto. eq_dec y b. subst. cong.
    rewrite update_neq; auto. eq_dec y a. subst. rewrite !update_neq; auto.
    eq_dec y b. subst. rewrite !update_neq; auto. rewrite !update_neq; auto.
  Qed.

(***********************************************************************)
(** ** Properties of Church's definition. *)

  (** [aeq_ch] is a congruence relation. *)

  Global Instance aeq_ch_refl : Reflexive aeq_ch.

  Proof. unfold Def.aeq_ch. class. Qed.

  Global Instance aeq_ch_trans : Transitive aeq_ch.

  Proof. unfold Def.aeq_ch. class. Qed.

  Global Instance aeq_ch_top_sym : Symmetric aeq_ch_top.

  Proof.
    intros u v uv. inversion uv; clear uv; subst; unfold Ens_In in *.
    rewrite not_mem_iff in H. set (v := replace_all x y u).
    rewrite <- replace_all2 with (x:=x) (y:=y); auto.    
    apply aeq_ch_top_intro; ens; unfold v.
    rewrite fv_replace_all; [idtac|fo|fo]. rewrite H. hyp.
    rewrite fv_replace_all; [idtac|fo|fo]. rewrite H, not_mem_iff. hyp.
    eq_dec x y. subst y. rewrite replace_all_id. hyp.
    apply notin_bv_replace_all. hyp.
  Qed.

  Global Instance aeq_ch_sym : Symmetric aeq_ch.

  Proof. apply rtc_sym. apply clos_mon_sym. class. Qed.

  Global Instance aeq_ch_mon : Monotone aeq_ch.

  Proof. unfold Def.aeq_ch. class. Qed.

  (** [aeq_ch] is equivalent to [aeq]. *)

  Lemma aeq_ch_le_aeq : aeq_ch << aeq.

  Proof.
    apply rtc_min. constructor; class. apply clos_mon_min. class.
    intros u v uv; inversion uv; clear uv; subst.
    rewrite replace_all_aeq_rename; [idtac|fo|fo]. rewrite rename_notin_fv; firstorder auto with crelations.
  Qed.

  Lemma aeq_le_aeq_ch : aeq << aeq_ch.

  Proof.
    intro u; revert u.
    ind_size1 u; intros u' uu'; inv_aeq uu'; subst; ens. refl. refl.
    trans (App u v).
    apply mon_app_l. class. firstorder auto with crelations. fo. apply mon_app_r. class. fo. firstorder auto with crelations.
    rename x0 into y. rename u0 into v.
    set (xs := union
      (add x (union (fv u) (bv u))) (add y (union (fv v) (bv v)))).
    gen (var_notin_ok xs). set (z := var_notin xs).
    unfold xs. set_iff. intro hz.
    trans (replace_all x z (Lam x u)).
    apply rt_step. apply m_step. apply aeq_ch_top_intro; simpl; set_iff; fo.
    trans (replace_all y z (Lam y v)).
    2:{ sym. apply rt_step. apply m_step.
    apply aeq_ch_top_intro; simpl; set_iff; fo. }
    simpl. rewrite !replace_var_eq. apply mon_lam. class. refl.
    apply hu. rewrite size_replace_all. refl.
    rewrite !replace_all_aeq_rename, i0, rename2; firstorder auto with crelations.
  Qed.

(***********************************************************************)
(** ** Properties of Krivine's definition. *)

  (** [aeq_kr] is an equivalence relation. *)

  Global Instance aeq_kr_refl : Reflexive aeq_kr.

  Proof.
    intro u; revert u. ind_size1 u.
    apply aeq_kr_var.
    apply aeq_kr_fun.
    apply aeq_kr_app; hyp.
    apply aeq_kr_lam with (xs:=empty); simpl.
    intros y hy. apply hu. rewrite size_rename1. refl.
  Qed.

  Global Instance aeq_kr_sym : Symmetric aeq_kr.

  Proof.
    intro u; revert u. ind_size1 u; intros t' h; inversion h; clear h; subst.
    refl. refl. apply aeq_kr_app; fo.
    apply aeq_kr_lam with (xs:=xs). intros y hy. apply hu.
    rewrite size_rename1. refl. fo.
  Qed.

  Global Instance aeq_kr_trans : Transitive aeq_kr.

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
    refl. refl. apply aeq_kr_app; firstorder auto with crelations. clear tt'.
    pose (xs := union (bv u) (bv u0)).
    apply aeq_kr_lam with (xs := xs); ens. intro y.
    unfold xs. set_iff. intro hy.
    apply hu. rewrite size_rename1. refl.
    rewrite <- !rename1_no_alpha, i0, rename2. refl. hyp.
    right. right. fo. right. right. fo.
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

(***********************************************************************)
(** ** Properties of Gabbay and Pitts's definition. *)

  (** [aeq_gp] is reflexive. *)

  Global Instance aeq_gp_refl : Reflexive aeq_gp.

  Proof.
    intro u; revert u. ind_size1 u.
    apply aeq_gp_refl_var.
    apply aeq_gp_refl_fun.
    apply aeq_gp_app; hyp.
    set (xs := union (add x (union (fv u) (bv u)))
                     (add x (union (fv u) (bv u)))).
    gen (var_notin_ok xs). set (z := var_notin xs). intro hz.
    apply aeq_gp_lam with z. hyp. apply hu.
    unfold Def.transpose. rewrite size_action. refl.
  Qed.

  (** [aeq_gp] is symmetric. *)

  Global Instance aeq_gp_sym : Symmetric aeq_gp.

  Proof.
    intro u; revert u. ind_size1 u; intros t' h; inversion h; clear h; subst.
    refl. refl. apply aeq_gp_app; fo. ens.
    apply aeq_gp_lam with z. ens. rewrite union_sym. hyp.
    apply hu. unfold Def.transpose. rewrite size_action. refl. hyp.
  Qed.

  (** [aeq_gp] is included in [aeq]. *)

  Lemma aeq_gp_incl_aeq : aeq_gp << aeq.

  Proof.
    intros u v; revert u v; induction 1.
    refl. refl. rewrite IHaeq_gp1, IHaeq_gp2. refl. ens. revert IHaeq_gp.
    rewrite transpose_sym, transpose_sym with (x:=z).
    rewrite transpose_rename. 2-3: firstorder auto with set.
    rewrite transpose_rename. 2-3: firstorder auto with set.
    intro IH.
    rewrite aeq_alpha with (y:=z). 2: firstorder auto with set. rewrite IH, <- aeq_alpha; firstorder auto with crelations set.
  Qed.

  (** [transpose] is invariant by [aeq_gp]. *)

  Global Instance transpose_aeq_gp a b : Proper (aeq_gp ==> aeq_gp) (transpose a b).

  Proof.
    unfold Def.transpose. intros u v uv; revert u v uv a b.
    ind_size1 u; intros u' uu' a b; inversion uu'; subst.
    refl. refl. apply aeq_gp_app; fo.

    ens. revert H1; set_iff; intro H1.
    rename x' into y. rename u'0 into v. simpl.
    set (x' := transpose_var a b x). set (u' := transpose a b u).
    set (y' := transpose_var a b y). set (v' := transpose a b v).
    set (xs := add z (add a (add b (union
              (union (add x (union (fv u) (bv u)))
                     (add y (union (fv v) (bv v))))
              (union (add x' (union (fv u') (bv u')))
                     (add y' (union (fv v') (bv v')))))))).
    gen (var_notin_ok xs). set (z' := var_notin xs).
    unfold xs. (*SLOW*)set_iff. intro hz'. split_hyps.

    apply aeq_gp_lam with (z:=z'). ens. set_iff. split_all.
    unfold Def.transpose. do 2 rewrite action_comp.
    rewrite action_eq with
      (g := fun x0 => transpose_var a b (transpose_var z' x x0)).
    rewrite action_eq with (u := v)
      (g := fun x0 => transpose_var a b (transpose_var z' y x0)).
    rewrite <- action_comp, <- action_comp with (u:=v).
    apply hu. rewrite size_action. refl.

    rewrite action_eq with
      (g := fun x0 => transpose_var z' z (transpose_var z x x0)).
    rewrite action_eq with (u := v)
      (g := fun x0 => transpose_var z' z (transpose_var z y x0)).
    rewrite <- action_comp, <- action_comp with (u:=v).
    apply hu. rewrite size_action. refl. hyp.

    intros x0 h0. unfold Def.transpose_var. eq_dec x0 z. subst. fo.
    eq_dec x0 y. subst. eq_dec z z. 2: congruence. eq_dec y z'. congruence.
    eq_dec z z'; congruence. eq_dec x0 z'. subst. fo. eq_dec x0 z; congruence.

    intros x0 h0. unfold Def.transpose_var. eq_dec x0 z. subst. fo.
    eq_dec x0 x. subst. eq_dec z z. 2: congruence. eq_dec x z'. congruence.
    eq_dec z z'; congruence. eq_dec x0 z'. subst. fo. eq_dec x0 z; congruence.

    intros x0 h0. unfold y', x', Def.transpose_var. eq_dec x0 z'. subst.
    eq_dec z' a. congruence. eq_dec z' b. congruence. eq_dec z' z'.
    2: congruence. eq_dec y a. refl. eq_dec y b; refl. eq_dec x0 y. subst.
    eq_dec z' a. congruence. eq_dec z' b. congruence. eq_dec y a. eq_dec b z'.
    hyp. eq_dec b b; congruence. eq_dec y b. eq_dec a z'. hyp.
    eq_dec a a; congruence. eq_dec y z'. hyp. eq_dec y y; congruence.
    eq_dec x0 a. subst. eq_dec b z'. congruence. eq_dec y b. eq_dec y a.
    eq_dec b b; congruence. eq_dec b a; congruence. eq_dec y a.
    eq_dec b b; congruence. eq_dec b y; congruence. eq_dec x0 b. subst.
    eq_dec a z'. congruence. eq_dec y a. eq_dec a b; congruence. eq_dec y b.
    eq_dec a a; congruence. eq_dec a y; congruence. eq_dec x0 z'. congruence.
    eq_dec y a. eq_dec x0 b; congruence. eq_dec y b. eq_dec x0 a; congruence.
    eq_dec x0 y; congruence.

    intros x0 h0. unfold x', Def.transpose_var. eq_dec x0 z'. subst. fo.
    eq_dec x0 x. subst. eq_dec x a. eq_dec b z'. congruence. eq_dec b b.
    2: congruence. eq_dec z' a. congruence. eq_dec z' b; congruence.
    eq_dec x b. eq_dec a a. 2: congruence. eq_dec a z'. congruence.
    eq_dec z' a. congruence. eq_dec z' b; congruence. eq_dec x x.
    2: congruence. eq_dec z' a. congruence. eq_dec x z'. congruence.
    eq_dec z' b; congruence. eq_dec x0 a. subst. eq_dec b z'. congruence.
    eq_dec x a. congruence. eq_dec x b. eq_dec b a; congruence.
    eq_dec b x; congruence. eq_dec x0 b. subst. eq_dec a z'. congruence.
    eq_dec x a. eq_dec a b; congruence. eq_dec x b. eq_dec a a; congruence.
    eq_dec a x; congruence. eq_dec x0 z'. congruence. eq_dec x a.
    eq_dec x0 b; congruence. eq_dec x b. eq_dec x0 a; congruence.
    eq_dec x0 x; congruence.
  (*SLOW*)Qed.

  (** [aeq_gp] is transitive. *)

  Global Instance aeq_gp_trans : Transitive aeq_gp.

  Proof.
    intro u; revert u. ind_size1 u; intros b c tb bc;
      inversion tb; clear tb; subst; inversion bc; clear bc; subst.
    refl. refl. apply aeq_gp_app; fo. ens.
    rename x' into y. rename u' into v. rename z into a.
    rename x'0 into z. rename u'0 into w. rename z0 into b.
    set (xs := union (union (add x (union (fv u) (bv u)))
                            (add y (union (fv v) (bv v))))
                            (add z (union (fv w) (bv w)))).
    gen (var_notin_ok xs). set (c := var_notin xs).
    unfold xs. revert H1 H2. (*SLOW*)set_iff. split_all.
    apply aeq_gp_lam with (z:=c). ens. set_iff. split_all.
    apply hu with (y := transpose c y v).
    unfold Def.transpose. rewrite size_action. refl.

    rewrite transpose_sym.
    erewrite <- transpose_comp with (b:=a); auto.
    rewrite transpose_sym with (x:=c).
    erewrite <- transpose_comp with (u:=v) (b:=a); auto.
    rewrite transpose_sym with (x:=x), transpose_sym with (x:=y).
    apply transpose_aeq_gp. hyp.

    rewrite transpose_sym.
    erewrite <- transpose_comp with (b:=b); auto.
    rewrite transpose_sym with (x:=c).
    erewrite <- transpose_comp with (u:=w) (b:=b); auto.
    rewrite transpose_sym with (x:=y), transpose_sym with (x:=z).
    apply transpose_aeq_gp. hyp.
  Qed.

  (** [aeq] is included in [aeq_gp]. *)

  Lemma aeq_incl_aeq_gp : aeq << aeq_gp.

  Proof.
    intro u; revert u. ind_size1 u; intros u' uu'; inv_aeq uu'; subst.
    refl. refl. apply aeq_gp_app; firstorder auto with crelations.
    set (xs := union (union (add x (union (fv u) (bv u)))
                            (add x0 (union (fv u0) (bv u0))))
                     (union (fv (rename x x0 u)) (bv (rename x x0 u)))).
    gen (var_notin_ok xs). set (z := var_notin xs).
    unfold xs. set_iff. split_all.

    apply aeq_gp_lam with (z:=z). ens. set_iff. split_all. apply hu.
    unfold Def.transpose. rewrite size_action. refl.
    rewrite i0, transpose_sym. rewrite transpose_rename; auto.
    rewrite transpose_sym. rewrite transpose_rename; auto.
    rewrite rename2. refl. auto.

    apply aeq_gp_lam with (z:=z). ens. set_iff. split_all. apply hu.
    unfold Def.transpose. rewrite size_action. refl.
    rewrite i0, transpose_sym. rewrite transpose_rename; auto.
    rewrite transpose_sym. rewrite transpose_rename; auto.
    rewrite rename2. refl. auto.
  Qed.

End Make.
