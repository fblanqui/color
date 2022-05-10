(**
CoLoR, a Coq library on rewriting and termination.

See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2012-04-05

* Higher-order simultaneous substitutions

This formalization is inspired by the definition of a substitution of
one variable given by Haskell Curry and Robert Feys in Combinatory
Logic, volume 1, 1958, page 94 (written CF in the following). In order
to be able to use this in the context of higher-order rewriting, which
is more general than pure lambda-calculus, we instead define the
simultaneous substitution of any number of variables. *)

Set Implicit Arguments.

From Coq Require Import SetoidList Basics Morphisms.
From CoLoR Require Import BoolUtil LogicUtil RelUtil VecUtil EqUtil.
From CoLoR Require Export LTerm.

(****************************************************************************)
(** * Definition of substitution. *)

Module Export Def.

  (** Parameters. *)

  Section subs.

    (** We assume given decidable sets [F] and [X] for function
    symbols and variables respectively. *)

    Variables (F X : Type)
      (eq_fun_dec : forall f g : F, {f=g}+{~f=g})
      (eq_var_dec : forall x y : X, {x=y}+{~x=y}).

    Notation Te := (@Te F X).
    Notation Var := (@Var F X).
    Notation eq_term_dec := (@eq_term_dec F X eq_fun_dec eq_var_dec).
    Notation beq_term := (bool_of_rel eq_term_dec).

    (** We assume given a structure for finite sets on [X]. *)

    Variable ens_X : Ens X.

    Notation empty := (Ens_empty ens_X).
    Notation mem := (Ens_mem ens_X).
    Notation add := (Ens_add ens_X).
    Notation union := (Ens_union ens_X).
    Notation remove := (Ens_remove ens_X).
    Notation fold := (Ens_fold ens_X).
    Notation In := (Ens_In ens_X).

    Notation fv := (@fv F X ens_X).

    (** We assume that [X] is infinite. *)

    Variable var_notin : Ens_type ens_X -> X.

  (** ** Type for substitutions:
     a substitution is given by a total function from [X] to [Te]. *)

    (** Identity substitution. *)

    Definition id := fun y => Var y.

    (** [update x t s] is the substitution mapping [x] to [t] and any
       other variable [y] to [s y]. *)

    Definition update x (t : Te) s := fun y =>
      match eq_var_dec y x with
        | left _ => t
        | _ => s y
      end.

    (** [single x t] is the substitution mapping [x] to [t] and leaving
       any other variable unchanged. *)

    Definition single x t := update x t id.

    (** [restrict xs s] is the substitution mapping any variable [z] of
       [xs] to [s z] and leaving any other variable unchanged. *)
 
    Definition restrict xs s z := if mem z xs then s z else Var z.

    (** "Domain" of a substitution: given a substitution [s] and a
       finite set [xs], [domain s xs] is the set of variables [x] in [xs]
       such that [s x <> Var x]. It is defined by iteration of the function
       [domain_fun] on [xs]. *)

    Definition domain_fun s x xs :=
      if beq_term (s x) (Var x) then xs else add x xs.

    Definition domain xs s := fold (domain_fun s) xs empty.

    (** Free variables of the "codomain" of a substitution: given a
       substitution [s] and a finite set [xs], [fvcod s xs] is the union of
       the free variables of [s x] for every [x] in [xs]. It is defined by
       iteration of the function [fvcod_fun] on [xs]. *)

    Definition fvcod_fun s (x : X) xs := union (fv (s x)) xs.

    Definition fvcod xs s := fold (fvcod_fun s) xs empty.

    (** Let [fvcodom] be the composition of [fvcod] and [domain]. *)

    Definition fvcodom xs s := fvcod (domain xs s) s.

    (** Substitution with variable capture. *)

    Fixpoint subs1 s (t : Te) :=
      match t with
        | Def.Var x => s x
        | Def.Fun f => t
        | Def.App u v => App (subs1 s u) (subs1 s v)
        | Def.Lam x u => Lam x (subs1 (update x (Var x) s) u)
      end.

    (*TODO: replace by a notation?*)
    Definition rename1 y z := subs1 (single y (Var z)).

    Definition comp1 s2 s1 (x:X) := subs1 s2 (s1 x).

    (** Generation of a fresh variable. *)

    Definition var x u s :=
      let xs := fvcodom (remove x (fv u)) s in
        if mem x xs then var_notin (union (fv u) xs) else x.

    (** [subs]: Effect of a substitution on a term.
When applying [s] on [Lam x u], if [x] belongs to the set [xs] of the
free variables of the codomain of [s] w.r.t. the free variables of
[Lam x u], then [x] is renamed into a variable [var s x u] not
belonging to [fv u] nor [xs].

In Curry-Feys, [subs] is only defined for substitutions [s] of the
form [single y v] and [subs (Lam x u)] is defined as [Lam x' (subs s
(rename x x' u))] where:

- [rename x x' = subs (single x (Var x'))],

It is not possible to have a similar definition in Coq because the
inner recursive call is not recognized by Coq as preserving the [size]
of its argument. Considering simultaneous substitutions and [update]
avoid this problem.

- [x' = if negb (eqb x y) && mem y (fv u) && mem x (fv v) then
  var_notin (union (fv u) (add y (fv v))) else x].

With our definition, after Lemma [var_single] proved below, for [x'],
we get [if negb (eqb x y) && mem y (fv u) && mem x (fv v) && negb
(beq_term v (Var y)) then var_notin (union (fv u) (fv v)) else x]. Hence,
we do a renaming only if [v <> Var y] (i.e. if [s] is not the
identity), and [x] can be renamed into [y]. In Curry-Feys definition,
renaming [x] into [y] would not be correct. For instance, with [s =
single y (Var x)] and [u = Var x], we would have [subs (single y (Var
x)) (Lam x (Var x)) = Lam y (subs (single y (Var x)) (rename x y (Var
x))) = Lam y (Var x)] instead of a term alpha-equivalent to [Lam x
(Var x)]. With our definition, this is correct since we use
simultaneous substitutions instead of the composition of two
substitutions. In the example, we have [subs (single y (Var x)) (Lam x
(Var x)) = Lam y (subs (update x (Var y) (single y (Var x))) (Var x))
= Lam y (Var y)].

In "Substitution Revisited", Theoretical Computer Science 59:317-325,
1988, Allen Stoughton defines higher-order simultaneous substitutions
too, but by always renaming bound variables, i.e. [var x u s = choice
(new x u s)] where [new x u s] is the complement of [fvcodom (remove x
(fv u)) s] and [choice:XSet.t -> X] is a choice function ([In (choice
A) A] if [A] is not empty). *)

    Fixpoint subs s (t : Te) :=
      match t with
        | Def.Var x => s x
        | Fun f => t
        | App u v => App (subs s u) (subs s v)
        | Lam x u =>
          let x' := var x u s in Lam x' (subs (update x (Var x') s) u)
      end.

    (*TODO: replace by a notation?*)
    Definition rename y z := subs (single y (Var z)).

    Definition subs_single x u := subs (single x u).

    (** Composition of two substitutions. *)

    Definition comp s2 s1 (x : X) := subs s2 (s1 x).

    (** Closure by substitution of a relation on terms.

       Note that [clos_subs R] is a priori NOT stable by substitution
       since substitution composition is correct modulo alpha-equivalence
       only (Lemma [subs_comp] in LAlpha). *)

    Inductive clos_subs R : rel Te :=
    | subs_step : forall x y s, R x y -> clos_subs R (subs s x) (subs s y).

    (** Point-wise extension of a relation to substitutions. *)

    Definition subs_rel (R : rel Te) xs s s' :=
      forall x : X, In x xs -> R (s x) (s' x).

  End subs.

  Arguments domain [F X] eq_fun_dec eq_var_dec ens_X xs s : simpl never.
  Arguments fvcod [F X] ens_X xs s : simpl never.
  Arguments fvcodom [F X] eq_fun_dec eq_var_dec ens_X xs s : simpl never.

End Def.

(****************************************************************************)
(** * Properties of substitution. *)

Module Make (Export L : L_Struct).

  (** Notations for substitutions and related definitions. *)

  Notation id := (@id F X).
  Notation update := (@update F X XOrd.eq_dec).
  Notation single := (@single F X XOrd.eq_dec).
  Notation restrict := (@restrict F X ens_X).
  Notation domain_fun := (@domain_fun F X FOrd.eq_dec XOrd.eq_dec ens_X).
  Notation domain := (@domain F X FOrd.eq_dec XOrd.eq_dec ens_X).
  Notation fvcod_fun := (@fvcod_fun F X ens_X).
  Notation fvcod := (@fvcod F X ens_X).
  Notation fvcodom := (@fvcodom F X FOrd.eq_dec XOrd.eq_dec ens_X).
  Notation var := (@var F X FOrd.eq_dec XOrd.eq_dec ens_X var_notin).
  Notation subs1 := (@subs1 F X XOrd.eq_dec).
  Notation rename1 := (@rename1 F X XOrd.eq_dec).
  Notation comp1 := (@comp1 F X XOrd.eq_dec).
  Notation subs := (@subs F X FOrd.eq_dec XOrd.eq_dec ens_X var_notin).
  Notation subs_single :=
    (@subs_single F X FOrd.eq_dec XOrd.eq_dec ens_X var_notin).
  Notation comp := (@comp F X FOrd.eq_dec XOrd.eq_dec ens_X var_notin).
  Notation rename := (@rename F X FOrd.eq_dec XOrd.eq_dec ens_X var_notin).
  Notation clos_subs :=
    (@clos_subs F X FOrd.eq_dec XOrd.eq_dec ens_X var_notin).
  Notation subs_rel := (@subs_rel F X ens_X).

  Module Export T := LTerm.Make L.

  (** Basic properties. *)

  Global Instance rename_proper_eq A B : Proper (Logic.eq ==> A ==> B) subs ->
    Proper (Logic.eq ==> Logic.eq ==> A ==> B) rename.

  Proof.
    intros h x x' xx' y y' yy' u u' uu'. subst x' y'. unfold Def.rename.
    apply h. refl. hyp.
  Qed.

  Lemma update_eq x u s : update x u s x = u.

  Proof. unfold Def.update. eq_dec x x. refl. fo. Qed.

  Lemma update_neq x u s y : x <> y -> update x u s y = s y.

  Proof. intro n. unfold Def.update. eq_dec y x. subst y. tauto. refl. Qed.

  Lemma single_eq y v : single y v y = v.

  Proof. unfold Def.single. apply update_eq. Qed.

  Lemma single_neq y v z : y <> z -> single y v z = Var z.

  Proof.
    intro n. unfold Def.single, Def.update. eq_dec z y. subst. tauto. refl.
  Qed.

  (** Predicate saying that the domain of a substitution is included
  in some finite set. *)

  Definition dom_incl xs s := forall x, ~In x xs -> s x = Var x.

  Global Instance dom_incl_e : Proper (Equal ==> Logic.eq ==> iff) dom_incl.

  Proof. intros xs xs' e s s' ss'. subst s'. fo. Qed.

  Global Instance dom_incl_s : Proper (Subset ==> Logic.eq ==> impl) dom_incl.

  Proof.
    intros xs xs' xsxs' s s' ss' h x hx. subst s'. apply h. rewrite xsxs'. hyp.
  Qed.

  Lemma dom_incl_restrict s xs : dom_incl xs (restrict xs s).

  Proof.
    intro x. rewrite not_mem_iff. intro hx. unfold Def.restrict; ens.
    rewrite hx. refl.
  Qed.

(****************************************************************************)
(** ** Properties of [subs_rel]. *)

  Lemma subs_rel_update (R : rel Te) xs x u u' s s' :
    R u u' -> subs_rel R (remove x xs) s s'
    -> subs_rel R xs (update x u s) (update x u' s').

  Proof.
    intros uu' ss' y hy. unfold Def.update. eq_dec y x.
    hyp. apply ss'. set_iff. auto.
  Qed.

  (** Preserved properties. *)

  Global Instance subs_rel_refl R xs : Reflexive R -> Reflexive (subs_rel R xs).

  Proof. fo. Qed.

  Global Instance subs_rel_sym R xs : Symmetric R -> Symmetric (subs_rel R xs).

  Proof. fo. Qed.

  Global Instance subs_rel_trans R xs : Transitive R -> Transitive (subs_rel R xs).

  Proof. intros R_trans s1 s2 s3 a b x h. trans (s2 x); fo. Qed.

  (** [subs_rel R] is compatible with set inclusion and equality. *)

  Global Instance subs_rel_s :
    Proper (inclusion ==> Subset --> Logic.eq ==> Logic.eq ==> impl) subs_rel.

  Proof. intros R R' RR' xs xs' e s1 s1' h1 s2 s2' h2. subst s1' s2'. fo. Qed.

  Global Instance subs_rel_e :
    Proper (same ==> Equal ==> Logic.eq ==> Logic.eq ==> iff) subs_rel.

  Proof.
    intros R R' RR' xs xs' e s1 s1' h1 s2 s2' h2. subst s1' s2'.
    split; intros H x hx; apply RR'.
    rewrite <- e in hx. fo. rewrite e in hx. fo.
  Qed.

(****************************************************************************)
(** ** Syntactic equality of two substitutions on some finite set of variables *)

  Notation seq := (subs_rel Logic.eq).

  Lemma seq_restrict xs ys s : xs [<=] ys -> seq xs s (restrict ys s).

  Proof.
    intros i x. rewrite i, mem_iff. intro h. unfold Def.restrict; ens.
    rewrite h. refl.
  Qed.

(****************************************************************************)
(** ** Properties of [domain]. *)

  (** [domain_fun] is compatible with set inclusion and equality and
  commutes with [add]. *)

  Global Instance domain_fun_s :
    Proper (Logic.eq ==> Logic.eq ==> Subset ==> Subset) domain_fun.

  Proof.
    intros s s' ss' x x' xx' xs xs' xsxs'. subst x' s'.
    unfold Def.domain_fun, bool_of_rel.
    destruct (eq_term_dec (s x) (Var x)); rewrite xsxs'; refl.
  Qed.

  Global Instance domain_fun_e :
    Proper (Logic.eq ==> Logic.eq ==> Equal ==> Equal) domain_fun.

  Proof.
    intros s s' ss' x x' xx' xs xs' xsxs'. subst x' s'.
    unfold Def.domain_fun, bool_of_rel.
    destruct (eq_term_dec (s x) (Var x)); rewrite xsxs'; refl.
  Qed.

  Lemma domain_fun_transp s : transpose Equal (domain_fun s).

  Proof.
    intros x y xs. unfold Def.domain_fun, bool_of_rel.
    destruct (eq_term_dec (s x) (Var x)); destruct (eq_term_dec (s y) (Var y));
      try refl. apply add_add.
  Qed.

  (** [domain] is compatible with set equality. *)

  Global Instance domain_e : Proper (Equal ==> Logic.eq ==> Equal) domain.

  Proof.
    intros xs xs' xsxs' s s' ss'. subst s'. unfold Def.domain.
    apply fold_equal. apply Equal_ST. apply domain_fun_e. refl. hyp.
  Qed.

  (** Set equalities on [domain]. *)

  Lemma domain_empty s : domain empty s [=] empty.

  Proof. unfold Def.domain. rewrite fold_empty. refl. Qed.

  Lemma domain_add s x xs : ~In x xs ->
    domain (add x xs) s [=] domain_fun s x (domain xs s).

  Proof.
    intro n. unfold Def.domain. rewrite fold_add. refl.
    apply Equal_ST. apply domain_fun_e. refl. apply domain_fun_transp. hyp.
  Qed.

  (** Correctness proof of the definition of [domain]. *)

  Lemma In_domain x s : forall xs,
    In x (domain xs s) <-> In x xs /\ s x <> Var x.

  Proof.
    apply set_induction_bis.
    (* Equal *)
    intros xs xs' xsxs' h. rewrite <- xsxs', h. refl.
    (* empty *)
    rewrite domain_empty. set_iff. tauto.
    (* add *)
    intros y xs n IH. rewrite domain_add. set_iff. 2: hyp.
    unfold Def.domain_fun, bool_of_rel.
    destruct (eq_term_dec (s y) (Var y)); set_iff; rewrite IH; split.
    tauto. intros [[h1|h1] h2]; subst; tauto.
    intros [h1|h1]; subst; tauto. tauto.
  Qed.

  Lemma mem_domain x s xs :
    mem x (domain xs s) = mem x xs && negb (beq_term (s x) (Var x)).

  Proof.
    rewrite eqb_equiv, andb_true_iff, negb_true_iff, beq_term_false_iff.
    rewrite <- !mem_iff. apply In_domain.
  Qed.

  Lemma notin_domain s xs x :
    domain xs s [=] empty -> In x xs -> s x = Var x.

  Proof.
    intros h1 h2. destruct (eq_term_dec (s x) (Var x)). hyp.
    absurd (In x (domain xs s)). rewrite h1. set_iff. tauto.
    rewrite In_domain. tauto.
  Qed.

  (** [domain] is compatible with set inclusion. *)

  Global Instance domain_s : Proper (Subset ==> Logic.eq ==> Subset) domain.

  Proof.
    intros xs xs' xsxs' s s' ss' x. subst s'. do 2 rewrite In_domain.
    rewrite xsxs'. auto.
  Qed.

  Lemma domain_subset s xs : domain xs s [<=] xs.

  Proof. intro x. rewrite In_domain. tauto. Qed.

  (** More set equalities on [domain]. *)

  Lemma domain_singleton s x : domain (singleton x) s
    [=] if beq_term (s x) (Var x) then empty else singleton x.

  Proof.
    intro y. unfold bool_of_rel.
    destruct (eq_term_dec (s x) (Var x)); rewrite In_domain; set_iff; split.
    intros [h1 h2]. subst. fo. fo. fo. intro e. subst. fo.
  Qed.

  Lemma domain_union s p q :
    domain (union p q) s [=] union (domain p s) (domain q s).

  Proof. intro x. set_iff. rewrite !In_domain. set_iff. tauto. Qed.

  Lemma domain_single y v : forall xs, domain xs (single y v)
    [=] if mem y xs && negb (beq_term v (Var y)) then singleton y else empty.

  Proof.
    apply set_induction_bis.
    (* Equal *)
    intros xs xs' xsxs'. rewrite xsxs'. auto.
    (* empty *)
    rewrite domain_empty, empty_b. refl.
    (* add *)
    intros x xs n IH. rewrite domain_add, add_b, IH. 2: hyp. clear IH.
    unfold eqb, Def.domain_fun. unfold bool_of_rel at 1.
    destruct (eq_term_dec (single y v x) (Var x)).
    revert e. unfold Def.single, Def.update.
    eq_dec x y; intro h.
    subst. rewrite not_mem_iff in n.
    rewrite n, beq_term_refl. refl.
    refl.
    unfold bool_of_rel. revert n0. unfold Def.single, Def.update.
    eq_dec x y; simpl. 2: tauto. subst.
    destruct (mem y xs); destruct (eq_term_dec v (Var y)); simpl.
    tauto.
    rewrite singleton_equal_add, add_equal. refl. set_iff. auto.
    tauto.
    rewrite singleton_equal_add. refl.
  Qed.

  Lemma domain_rename y z xs : domain xs (single y (Var z))
    [=] if mem y xs && negb (eqb z y) then singleton y else empty.

  Proof. rewrite domain_single, beq_term_var. refl. Qed.

  Lemma domain_single_empty y v xs :
    domain xs (single y v) [=] empty <-> ~In y xs \/ v = Var y.

  Proof.
    rewrite domain_single. case_eq (mem y xs && negb (beq_term v (Var y))).
    rewrite andb_true_iff, <- mem_iff, negb_true_iff, beq_term_false_iff.
    intros [h1 h2]. split. 2: fo.
    intro e. absurd (In y empty). set_iff. fo. rewrite <- e. set_iff. refl.
    rewrite andb_false_iff, <- not_mem_iff, negb_false_iff, beq_term_true_iff.
    intros [h1|h2]; split. fo. refl. right. hyp. refl.
  Qed.

  Lemma domain_id : forall xs, domain xs id [=] empty.

  Proof.
    apply set_induction_bis.
    (* Equal *)
    intros xs xs' xsxs' h. rewrite <- xsxs'. hyp.
    (* empty *)
    apply domain_empty.
    (* add *)
    intros x xs n IH. rewrite domain_add. 2: hyp.
    unfold Def.domain_fun, bool_of_rel.
    destruct (eq_term_dec (id x) (Var x)). hyp. absurd (id x=Var x); tauto.
  Qed.

  Lemma domain_update_id x s xs :
    domain xs (update x (Var x) s) [=] domain (remove x xs) s.

  Proof.
    intro y. rewrite !In_domain. set_iff. unfold Def.update.
    eq_dec y x. subst. tauto. fo.
  Qed.

  (** [domain] is compatible with [subs_rel]. *)
  (*FIXME: change order of arguments in fvcod, domain and fvcodom? *)

  Global Instance domain_subs_rel_Subset (R : rel Te) : VarInvL R ->
    forall xs, Proper (subs_rel R xs --> Subset) (domain xs).

  Proof.
    intros [var_R_l] xs s s' s's x. rewrite !In_domain.
    split_all. apply H1. apply var_R_l. rewrite <- H0. apply s's. hyp.
  Qed.

  Global Instance domain_subs_rel_Equal (R : rel Te) : VarInvL R -> VarInvR R ->
    forall xs, Proper (subs_rel R xs ==> Equal) (domain xs).

  Proof.
    intros [var_R_l] [var_R_r] xs s s' ss' x. rewrite !In_domain.
    split_all; apply H1; gen (ss' _ H); intro h; rewrite H0 in h.
    gen (var_R_r _ _ h). auto. gen (var_R_l _ _ h). auto.
  Qed.

(****************************************************************************)
(** ** Properties of [fvcod]. *)

  (** [fvcod_fun] is compatible with set equality and commutes with [add]. *)

  Global Instance fvcod_fun_e :
    Proper (Logic.eq ==> Logic.eq ==> Equal ==> Equal) fvcod_fun.

  Proof.
    intros s s' ss' x x' xx' vs vs' vsvs'. subst s' x'. unfold Def.fvcod_fun.
    rewrite vsvs'. refl.
  Qed.

  Lemma fvcod_fun_transp s : transpose Equal (fvcod_fun s).

  Proof. intros u v vs. unfold Def.fvcod_fun. intro x. set_iff. tauto. Qed.

  (** [fvcod] is compatible with set equality. *)

  Global Instance fvcod_e : Proper (Equal ==> Logic.eq ==> Equal) fvcod.

  Proof.
    intros xs xs' xsxs' s s' ss'. subst s'. unfold Def.fvcod.
    apply fold_equal. apply Equal_ST. apply fvcod_fun_e. refl. hyp.
  Qed.

  (** Set equalities on [fvcod]. *)

  Lemma fvcod_empty s : fvcod empty s [=] empty.

  Proof. unfold Def.fvcod. rewrite fold_empty. refl. Qed.

  Lemma fvcod_add s x xs : ~In x xs ->
    fvcod (add x xs) s [=] fvcod_fun s x (fvcod xs s).

  Proof.
    intro n. unfold Def.fvcod. rewrite fold_add. refl.
    apply Equal_ST. apply fvcod_fun_e. refl. apply fvcod_fun_transp. hyp.
  Qed.

  (** Correctness proof of [fvcod]. *)

  Lemma In_fvcod y s : forall xs,
    In y (fvcod xs s) <-> exists x, In x xs /\ In y (fv (s x)).

  Proof.
    apply set_induction_bis.
    (* Equal *)
    intros xs xs' xsxs' h. rewrite <- xsxs', h. clear h.
    split; intros [x [x1 x2]]; ex x; split; auto.
    rewrite <- xsxs'. hyp. rewrite xsxs'. hyp.
    (* empty *)
    rewrite fvcod_empty. set_iff. intuition. destruct H as [x].
    revert H. set_iff. tauto.
    (* add *)
    intros x xs n IH. rewrite fvcod_add. 2: hyp. unfold Def.fvcod_fun.
    set_iff. rewrite IH. clear IH. split.
    intros [h|[a [a1 a2]]]. ex x. set_iff. fo. ex a. set_iff. fo.
    intros [a [a1 a2]]. revert a1. set_iff. intros [a1|a1].
    subst. left. hyp. right. ex a. fo.
  Qed.

  (** [fvcod] is compatible with inclusion. *)

  Global Instance fvcod_s : Proper (Subset ==> Logic.eq ==> Subset) fvcod.

  Proof.
    intros xs xs' xsxs' s s' ss' x. subst s'. rewrite !In_fvcod.
    intros [a [h1 h2]]. ex a. fo.
  Qed.

  (** More equalities on [fvcod]. *)

  Lemma fvcod_singleton s x : fvcod (singleton x) s [=] fv (s x).

  Proof.
    intro y. split; rewrite In_fvcod.
    intros [z [h1 h2]]. revert h1. set_iff. intro e. subst z. hyp.
    intro h. ex x. set_iff. fo.
  Qed.

  Lemma fvcod_union s p q :
    fvcod (union p q) s [=] union (fvcod p s) (fvcod q s).

  Proof.
    intro x. rewrite In_fvcod. set_iff. split.
    intros [y [h1 h2]]. revert h1. set_iff. rewrite !In_fvcod.
    intros [h1|h1]. left. ex y. fo. right. ex y. fo.
    rewrite !In_fvcod. intros [[y [h1 h2]]|[y [h1 h2]]].
    ex y. set_iff. fo. ex y. set_iff. fo.
  Qed.
 
  Lemma fvcod_single y v : forall xs, fvcod xs (single y v)
    [=] if mem y xs then union (fv v) (remove y xs) else xs.

  Proof.
    apply set_induction_bis.
    (* Equal *)
    intros s s' ss'. rewrite ss'. intro h. rewrite h.
    destruct (mem y s'); rewrite ss'; refl.
    (* empty *)
    rewrite fvcod_empty, empty_b. refl.
    (* add *)
    intros x u n IH. rewrite fvcod_add, IH. 2: hyp. clear IH.
    unfold Def.fvcod_fun, Def.single, Def.update, eqb.
    eq_dec x y; simpl.
    subst y. rewrite add_b, eqb_refl. simpl. rewrite not_mem_iff in n.
    rewrite n. rewrite <- not_mem_iff in n.
    intro a. set_iff. split.
    intros [a1|a1]. auto. right. split. auto. intro e. subst. fo.
    intros [a1|[[a1|a1] a2]]; auto. subst. cong. 
    rewrite <- eqb_false_iff in n0. rewrite add_b, n0. simpl.
    case_eq (mem y u); [rewrite <- mem_iff|rewrite <- not_mem_iff]; intro hy.
    intro a. set_iff. split.
    intros [a1|[a1|[a1 a2]]]; auto. right. split. auto.
    intro e. subst. rewrite eqb_false_iff in n0. cong.
    intros [a1|[[a1|a1] a2]]; auto.
    sym. apply add_union_singleton.
  Qed.

  Lemma fvcod_rename y z xs : fvcod xs (single y (Var z))
    [=] if mem y xs then add z (remove y xs) else xs.

  Proof.
    rewrite fvcod_single. simpl. destruct (mem y xs).
    intro a. set_iff. tauto. refl.
  Qed.

  Lemma fvcod_id : forall xs, fvcod xs id [=] xs.

  Proof.
    apply set_induction_bis.
    (* Equal *)
    intros xs xs' xsxs' h. rewrite <- xsxs'. hyp.
    (* empty *)
    apply fvcod_empty.
    (* add *)
    intros x xs n IH. rewrite fvcod_add. 2: hyp. unfold Def.fvcod_fun.
    simpl. rewrite IH. intro a. set_iff. tauto.
  Qed.

  (** [fvcod] is compatible with [subs_rel]. *)

  Global Instance fvcod_subs_rel_Subset R : Proper (R --> Subset) fv ->
    forall xs, Proper (subs_rel R xs --> Subset) (fvcod xs).

  Proof.
    intros fv_R xs s s' s's x. rewrite !In_fvcod. split_all; ex x0; split; auto.
    rewrite <- (fv_R _ _ (s's _ H)). hyp.
  Qed.

  Global Instance fvcod_subs_rel_Equal R : Proper (R ==> Equal) fv ->
    forall xs, Proper (subs_rel R xs ==> Equal) (fvcod xs).

  Proof.
    intros fv_R xs s s' ss' x. rewrite !In_fvcod. split_all; ex x0; split; auto.
    rewrite <- (fv_R _ _ (ss' _ H)). hyp. rewrite (fv_R _ _ (ss' _ H)). hyp.
  Qed.

(****************************************************************************)
(** ** Properties of [fvcodom]. *)

  (** [fvcodom] is compatible with set inclusion and equality. *)

  Global Instance fvcodom_s : Proper (Subset ==> Logic.eq ==> Subset) fvcodom.

  Proof.
    intros xs xs' xsxs' s s' ss'. subst s'. unfold Def.fvcodom. rewrite xsxs'.
    refl.
  Qed.

  Global Instance fvcodom_e : Proper (Equal ==> Logic.eq ==> Equal) fvcodom.

  Proof.
    intros xs xs' xsxs' s s' ss' . subst s'. unfold Def.fvcodom. rewrite xsxs'.
    refl.
  Qed.

  (** Correctness of [fvcodom]. *)

  Lemma In_fvcodom s xs y : In y (fvcodom xs s)
    <-> (exists x, In x xs /\ s x <> Var x /\ In y (fv (s x))).

  Proof.
    unfold Def.fvcodom. rewrite In_fvcod. intuition;
      destruct H as [x hx]; exists x; rewrite In_domain in *; tauto.
  Qed.

  (* Set equalities on [fvcodom]. *)

  Lemma fvcodom_singleton s x : fvcodom (singleton x) s
    [=] if beq_term (s x) (Var x) then empty else fv (s x).

  Proof.
    unfold Def.fvcodom. rewrite domain_singleton. unfold bool_of_rel.
    destruct (eq_term_dec (s x) (Var x)). apply fvcod_empty.
    apply fvcod_singleton.
  Qed.

  Lemma fvcodom_union s p q :
    fvcodom (union p q) s [=] union (fvcodom p s) (fvcodom q s).

  Proof.
    intro x. set_iff. unfold Def.fvcodom.
    rewrite domain_union, fvcod_union. set_iff. refl.
  Qed.

  Lemma fvcodom_id xs : fvcodom xs id [=] empty.

  Proof. unfold Def.fvcodom. rewrite fvcod_id, domain_id. refl. Qed.

  Lemma fvcodom_single y v xs : fvcodom xs (single y v)
    [=] if mem y xs && negb (beq_term v (Var y)) then fv v else empty.

  Proof.
    unfold Def.fvcodom. rewrite domain_single, fvcod_single.
    unfold bool_of_rel. case_eq (mem y xs); intro hy;
      destruct (eq_term_dec v (Var y)); simpl; try rewrite empty_b.
    refl. rewrite singleton_b, eqb_refl, singleton_equal_add,
      remove_add, empty_union_2. refl. apply empty_1. set_iff. tauto. refl. refl.
  Qed.

  Lemma fvcodom_rename y z xs : fvcodom xs (single y (Var z))
    [=] if mem y xs && negb (eqb z y) then singleton z else empty.

  Proof. rewrite fvcodom_single, beq_term_var. refl. Qed.

  Lemma fvcodom_update_id x s xs :
    fvcodom xs (update x (Var x) s) [=] fvcodom (remove x xs) s.

  Proof.
    unfold Def.fvcodom. rewrite domain_update_id.
    set (d := domain (remove x xs) s). intro y. rewrite !In_fvcod.
    assert (h : ~In x d). unfold d. rewrite In_domain. set_iff. tauto.
    unfold Def.update; split; intros [a [h1 h2]]; ex a; eq_dec a x; subst; fo.
  Qed.

  (** [fvcodom] is compatible with [subs_rel]. *)

  Global Instance fvcodom_subs_rel_Subset R :
    Proper (R --> Subset) fv -> VarInvL R ->
    forall xs, Proper (subs_rel R xs --> Subset) (fvcodom xs).

  Proof.
    intros fv_R R_var_l xs s s' s's x hx. unfold Def.fvcodom in *.
    eapply fvcod_s. 2: refl. eapply domain_subs_rel_Subset. apply R_var_l.
    apply s's. eapply fvcod_subs_rel_Subset. apply fv_R.
    assert (s's2 : flip (subs_rel R (domain xs s)) s s').
    intros y hy; ens. apply domain_subset in hy. apply s's. hyp.
    apply s's2. hyp.
  Qed.

  Global Instance fvcodom_subs_rel_Equal R :
    Proper (R ==> Equal) fv -> VarInvL R -> VarInvR R ->
    forall xs, Proper (subs_rel R xs ==> Equal) (fvcodom xs).

  Proof.
    intros fv_R R_var_l R_var_r xs s s' ss' x. unfold Def.fvcodom in *.
    assert (e : domain xs s [=] domain xs s').
    eapply domain_subs_rel_Equal. apply R_var_l. apply R_var_r. apply ss'.
    rewrite e; clear e.
    revert x. change (fvcod (domain xs s') s [=] fvcod (domain xs s') s').
    eapply fvcod_subs_rel_Equal. apply fv_R.
    intros x hx; ens. rewrite domain_subset in hx. apply ss'. hyp.
  Qed.

(****************************************************************************)
(** ** Properties of [var]. *)

  Lemma var_subs_rel R :
    Proper (R ==> Equal) fv -> VarInvL R -> VarInvR R ->
    forall x u, Proper (subs_rel R (remove x (fv u)) ==> Logic.eq) (var x u).

  Proof.
    intros fv_R R_var_l R_var_r x u s s' ss'. unfold Def.var; ens.
    rewrite !(fvcodom_subs_rel_Equal fv_R R_var_l R_var_r ss'). refl.
  Qed.

  Arguments var_subs_rel [R] _ _ _ [x u s s'] _ : rename.

  Global Instance var_seq x u : Proper (seq (remove x (fv u)) ==> Logic.eq) (var x u).

  Proof. intros s s' ss'. apply (var_subs_rel _ _ _ ss'). Qed.

  Arguments var_seq [x u s s'] _ : rename.

  Lemma var_notin_fvcodom x u s :
    ~In (var x u s) (fvcodom (remove x (fv u)) s).

  Proof.
    unfold Def.var; ens. set (xs := fvcodom (remove x (fv u)) s).
    case_eq (mem x xs).
    gen (var_notin_ok (union (fv u) xs)). set_iff. tauto.
    rewrite <- not_mem_iff. auto.
  Qed.

  Lemma var_notin_fv_subs x u s y :
    In y (fv u) -> y <> x -> ~In (var x u s) (fv (s y)).

  Proof.
    intros hy n h. apply var_notin_fvcodom with (x:=x) (u:=u) (s:=s).
    rewrite In_fvcodom. exists y. set_iff. intuition.
    revert h. rewrite H. simpl. set_iff. intro e.
    set (xs := fvcodom (remove x (fv u)) s).
    revert e; unfold Def.var; ens; intro e. fold xs in e.
    case_eq (mem x xs); intro i; rewrite i in e. 2: fo.
    gen (var_notin_ok (union (fv u) xs)); intro h.
    apply h. rewrite <- e, <- union_subset_1. hyp.
  Qed.

  Arguments var_notin_fv_subs [x u] s [y] _ _ _.

  Lemma var_notin_fvcod x u s : ~In (var x u s) (fvcod (remove x (fv u)) s).

  Proof.
    rewrite In_fvcod. intros [y [h1 h]]. revert h1. set_iff.
    intros [hy n]. eapply var_notin_fv_subs. apply hy. 2: apply h. auto.
  Qed.

(****************************************************************************)
(** ** Properties of [subs]. *)

  Lemma fold_subs_single x u : subs (single x u) = subs_single x u.

  Proof. refl. Qed.

  Lemma subs_lam_no_alpha s x u :
    ~In x (fvcodom (remove x (fv u)) s) ->
    subs s (Lam x u) = Lam x (subs (update x (Var x) s) u).

  Proof.
    rewrite not_mem_iff. intro n. simpl. unfold Def.var; ens. rewrite n. refl.
  Qed.

  Lemma subs_apps s : forall n (us : Tes n) t,
    subs s (apps t us) = apps (subs s t) (Vmap (subs s) us).

  Proof. induction us; intro t; simpl. refl. rewrite IHus. refl. Qed.

  (** Given [u], [fun s => subs s u] is compatible with [subs_rel R (fv u)]. *)

  Lemma subs_rel_mon_preorder R : PreOrder R -> Monotone R ->
    Proper (R ==> Equal) fv -> VarInvL R -> VarInvR R ->
    forall u s s', subs_rel R (fv u) s s' -> R (subs s u) (subs s' u).

  Proof.
    intros R_refl_trans R_mon fv_R var_R_l var_R_r.
    induction u; simpl; intros s s' h.
    (* var *)
    apply h; simpl. set_iff. refl.
    (* fun *)
    refl.
    (* app *)
    destruct R_mon.
    rewrite IHu1 with (s:=s) (s':=s'), IHu2 with (s:=s) (s':=s'). refl.
    intros x hx. apply h. simpl. apply union_subset_2. hyp.
    intros x hx. apply h. simpl. apply union_subset_1. hyp.
    (* lam *)
    rewrite (var_subs_rel fv_R var_R_l var_R_r h). set (z := var x u s').
    mon. apply IHu. intros y hy. unfold Def.update. eq_dec y x. refl.
    apply h. set_iff. auto.
  Qed.

  Lemma subs_seq u s s' : seq (fv u) s s' -> subs s u = subs s' u.

  Proof. intro ss'. apply subs_rel_mon_preorder; class. Qed.

  Arguments subs_seq [u s s'] _.

  Lemma subs_seq_restrict u s : subs s u = subs (restrict (fv u) s) u.

  Proof. apply subs_seq. apply seq_restrict. refl. Qed.

  (** Applying the identity substitution does not change the term
  (extension of CF, Theorem 1a, page 95, proof given on page 97). *)

  Lemma subs_id : forall u, subs id u = u.

  Proof.
    induction u; simpl. refl. refl. rewrite IHu1, IHu2. refl.
    unfold Def.var; ens. (*VERY SLOW*)rewrite fvcodom_id, empty_b.
    f_equal. rewrite <- IHu at 2. apply subs_seq.
    intros y hy. unfold Def.update. eq_dec y x. rewrite e. refl. refl.
  Qed.

  (** Applying on a term [u] a substitution which domain w.r.t. [fv u]
  is empty does not change the term (CF, Theorem 1b, page 95, proof
  given on page 98). *)

  Lemma subs_notin_fv u s : domain (fv u) s [=] empty -> subs s u = u.

  Proof.
    rewrite empty_subset. revert u s. induction u; simpl; intro s.
    (* var *)
    rewrite singleton_equal_add, domain_add. 2: set_iff; auto.
    rewrite domain_empty. unfold Def.domain_fun, bool_of_rel.
    destruct (eq_term_dec (s x) (Var x)). auto.
    intro h. cut False. tauto. rewrite <- empty_iff, <- h. apply add_1. refl.
    (* fun *)
    refl.
    (* app *)
    intro h. rewrite IHu1, IHu2. refl.
    rewrite (@union_subset_2 (fv u1) (fv u2)). hyp.
    rewrite (@union_subset_1 (fv u1) (fv u2)). hyp.
    (* lam *)
    intro h. unfold Def.var; ens. set (xs := fvcodom (remove x (fv u)) s).
    case_eq (mem x xs); intro hx. rewrite <- mem_iff in hx. unfold xs in hx.
    rewrite In_fvcodom in hx. destruct hx as [z hz]. gen (h z).
    set_iff. intro a. cut False. tauto. apply a. revert hz.
    repeat (rewrite In_domain; set_iff). intuition.
    f_equal. apply IHu. intro y. gen (h y).
    do 2 rewrite In_domain. set_iff. unfold Def.update. eq_dec y x.
    subst y. intuition. intuition.
  Qed.

  (** Free variables of a substituted term. *)

  Lemma fv_subs : forall u s, fv (subs s u)
    [=] let xs := domain (fv u) s in union (diff (fv u) xs) (fvcod xs s).

  Proof.
    induction u; simpl; intro s.

    (* var *)
    rewrite singleton_equal_add, domain_add, domain_empty. 2: firstorder auto with set.
    unfold Def.domain_fun, bool_of_rel. destruct (eq_term_dec (s x) (Var x)).
    rewrite e. simpl. rewrite fvcod_empty. fset.
    rewrite fvcod_add, fvcod_empty. 2: set_iff; fo.
    unfold Def.fvcod_fun. intro a. set_iff. split. intro h. auto.
    intros [[h1 h2]|[h1|h1]]; fo.

    (* fun *)
    intro y. rewrite domain_empty, fvcod_empty. set_iff. tauto.

    (* app *)
    rewrite IHu1, IHu2. simpl. intro y. (*SLOW*)set_iff.
    rewrite !In_fvcod, !In_domain. set_iff. split_all; try tauto.
    right. ex x. revert H. rewrite !In_domain. set_iff. tauto.
    right. ex x. revert H. rewrite !In_domain. set_iff. tauto.
    revert H. rewrite In_domain. set_iff. split_all.
    left. right. ex x. rewrite In_domain. tauto.
    right. right. ex x. rewrite In_domain. tauto.

    (* lam *)
    unfold Def.var, Def.fvcodom; ens.
    set (xs := fvcod (domain (remove x (fv u)) s) s).
    case_eq (mem x xs); [rewrite <- mem_iff|rewrite <- not_mem_iff];
      intro hx; simpl; rewrite IHu; simpl.

    (* In x xs *)
    set (x' := var_notin (union (fv u) xs)).
    gen hx. unfold xs at 1. rewrite In_fvcod. intros [z hz]. revert hz.
    rewrite In_domain. set_iff. split_all.
    intro y. set_iff. rewrite !In_domain, In_fvcod.
    unfold Def.update at 1. eq_dec y x.

    (* y = x *)
    subst y. set_iff. split_all.
    right. exists z. rewrite In_domain. unfold Def.update.
    eq_dec z x. subst z. tauto. tauto.
    subst x'. apply var_notin_ok with (xs := union (fv u) xs).
    rewrite H4. apply union_subset_2. hyp.

    (* y <> x *)
    set_iff. split_all.

    left. split_all.

    revert H3 H5. rewrite In_domain. unfold Def.update.
    eq_dec x0 x; simpl; set_iff. subst x0. intuition.
    destruct (In_dec y xs). auto. left.
    absurd (In y xs). hyp. unfold xs. rewrite In_fvcod. exists x0.
    rewrite In_domain. set_iff. fo.

    tauto.

    revert H3. unfold xs. rewrite In_fvcod. intros [a ha]. revert ha.
    rewrite In_domain. set_iff. split_all. right. exists a.
    rewrite In_domain. unfold Def.update. eq_dec a x. subst a.
    cong. tauto.

    subst y. absurd (In x' (union (fv u) xs)). apply var_notin_ok.
    apply union_subset_1. hyp.

    subst y. absurd (In x' (union (fv u) xs)). apply var_notin_ok.
    apply union_subset_2. hyp.

    (* ~In x xs *)
    intro y. set_iff. rewrite !In_domain. set_iff.
    rewrite In_fvcod. unfold Def.update. eq_dec y x.

    (* y = x *)
    subst y. tauto.

    (* y <> x *)
    split_all; try tauto.
    revert H. rewrite In_domain. eq_dec x0 x.
    subst x0. tauto.
    split_all. right. unfold xs. rewrite In_fvcod. exists x0.
    rewrite In_domain. set_iff. fo.

    revert H. unfold xs. rewrite In_fvcod. intros [z hz]. revert hz.
    rewrite In_domain. set_iff. split_all. right. exists z.
    rewrite In_domain. eq_dec z x. subst z. tauto. tauto.
  Qed.

  Lemma fvcod_subset_fv_subs s u : fvcod (fv u) s [<=] fv (subs s u).

  Proof.
    rewrite fv_subs. simpl. intro x. rewrite In_fvcod.
    intros [y [h1 h2]]. set_iff. rewrite In_domain.
    fold (fvcodom (fv u) s). rewrite In_fvcodom.
    destruct (eq_term_dec (s y) (Var y)).
    left. revert h2. rewrite e. simpl. set_iff. intro h2. subst y. tauto.
    right. exists y. tauto.
  Qed.

(****************************************************************************)
(** ** Stability by substitution. *)

  Section stable.

    Definition stable R := Proper (Logic.eq ==> R ==> R) subs.

    Instance stable_same : Proper (same ==> impl) stable.

    Proof.
      intros S T e subs_S s s' ss' t u tu. subst s'. rewrite rel_eq in e.
      rewrite <- e. apply subs_S. refl. rewrite e. hyp.
    Qed.

    Instance stable_same_iff : Proper (same ==> iff) stable.

    Proof. intros S T e. split; intro h. rewrite <- e. hyp. rewrite e. hyp. Qed.

    Lemma stable_union R S : stable R -> stable S -> stable (R U S).

    Proof.
      intros subs_R subs_S s s' ss' t u [tu|tu]; subst s'.
      left. apply subs_R; auto. right. apply subs_S; auto.
    Qed.

  End stable.

(****************************************************************************)
(** ** [clos_subs] preserves free variables. *)

  Global Instance fv_clos_subs R :
    Proper (R --> Subset) fv -> Proper (clos_subs R --> Subset) fv.

  Proof.
    intros fv_R t u tu. inversion tu; subst; clear tu. rewrite 2!fv_subs.
    simpl. gen (fv_R _ _ H); intro h.
    assert (a : diff (fv y) (domain (fv y) s)
      [<=] diff (fv x) (domain (fv x) s)).
    intro z. set_iff. rewrite 2!In_domain. intuition.
    rewrite a, h. refl.
  Qed.

(****************************************************************************)
(** ** Some equalities on [update]. *)

  Lemma update2_eq x u v w s :
    subs (update x v (update x w s)) u = subs (update x v s) u.

  Proof. apply subs_seq. intros z hz. unfold Def.update. eq_dec z x; refl. Qed.

  Lemma update2_neq_com s x u y v w : x <> y ->
    subs (update x u (update y v s)) w = subs (update y v (update x u s)) w.

  Proof.
    intro n. apply subs_seq. intros z hz. unfold Def.update.
    eq_dec z x; eq_dec z y; try refl. subst. tauto.
  Qed.

  Lemma update_single_eq y v w u :
    subs (update y w (single y v)) u = subs (single y w) u.

  Proof. unfold Def.single at 1. rewrite update2_eq. refl. Qed.

  Lemma update2_single_eq y w x v v' u :
    subs (update y w (update x v' (single x v))) u
    = subs (update y w (single x v')) u.

  Proof.
    apply subs_seq. intros z hz.
    unfold Def.update at -2. eq_dec z y. refl.
    match goal with |- ?x _ = ?y _ => set (s1:=x); set (s2:=y) end.
    change (subs s1 (Var z) = subs s2 (Var z)). unfold s1, s2.
    rewrite update_single_eq. refl.
  Qed.

  Lemma update_id x s u :
    s x = Var x -> subs (update x (Var x) s) u = subs s u.

  Proof.
    intro h. apply subs_seq. intros z hz. unfold Def.update.
    eq_dec z x. subst. auto. refl.
  Qed.

  Lemma update_id_single y v x u : x<>y \/ v=Var x ->
    subs (update x (Var x) (single y v)) u = subs (single y v) u.

  Proof.
    intro h. apply subs_seq. intros b hb.
    unfold Def.single, Def.update. eq_dec b x; eq_dec b y.
    subst. destruct h. tauto. subst. refl.
    subst. refl. refl. refl.
  Qed.

(****************************************************************************)
(** ** Some equalities on [single]. *)

  (** CF, Theorem 1a, page 95, proof page 97. *)

  Lemma single_id y u : subs (single y (Var y)) u = u.

  Proof.
    rewrite <- subs_id. apply subs_seq. intros x hx.
    unfold Def.single, Def.update. eq_dec x y. subst. refl. refl.
  Qed.

  (** CF, Theorem 1b, page 95, proof page 98. *)

  Lemma single_notin_fv y u v : ~In y (fv v) -> subs (single y u) v = v.

  Proof.
    intro n. rewrite subs_notin_fv. refl. intro x.
    rewrite In_domain. set_iff. unfold Def.single, Def.update.
    eq_dec x y. subst x. intuition. intuition.
  Qed.

  (** Other equalities on [single]. *)

  Lemma single_var x u s v z : In z (fv u) -> x <> z ->
    subs (single (var x u s) v) (s z) = s z.

  Proof.
    intros h1 h2. rewrite single_notin_fv. refl. unfold Def.var; ens.
    case_eq (mem x (fvcodom (remove x (fv u)) s)).

    rewrite <- mem_iff. set (xs := union (fv u) (fvcodom (remove x (fv u)) s)).
    gen (var_notin_ok xs). set (x' := var_notin xs). unfold xs. set_iff.
    intros h hx g. apply h. right. rewrite In_fvcodom. exists z. set_iff.
    destruct (eq_term_dec (s z) (Var z)). 2: tauto.
    revert g. rewrite e. simpl. set_iff. intro g. subst z. tauto.

    rewrite <- not_mem_iff. intros h3 h4. apply h3. rewrite In_fvcodom.
    exists z. set_iff. destruct (eq_term_dec (s z) (Var z)). 2: tauto.
    revert h4. rewrite e. simpl. set_iff. intro h4. subst z. tauto.
  Qed.

  Lemma var_single y v x u : var x u (single y v) =
    if mem y (fv u) && negb (eqb x y) && negb (beq_term v (Var y))
      && mem x (fv v) then var_notin (union (fv u) (fv v)) else x.

  Proof.
    unfold Def.var; ens.
    rewrite fvcodom_single, remove_b, mem_if.
    case_eq (mem y (fv u) && negb (eqb x y) && negb (beq_term v (Var y)) &&
       mem x (fv v)). rewrite !andb_true_iff. intros [[[h1 h2] h3] h4].
    assert (e : fvcodom (remove x (fv u)) (single y v) [=] fv v).
    rewrite fvcodom_single, remove_b, h1, h2, h3. simpl. refl.
    rewrite e. refl. refl.
  Qed.

  Lemma single_lam_no_alpha y v x u :
    ~In y (fv u) \/ x=y \/ v=Var y \/ ~In x (fv v) ->
    subs (single y v) (Lam x u)
    = Lam x (subs (update x (Var x) (single y v)) u).

  Proof.
    rewrite !not_mem_iff, <- eqb_true_iff, <- beq_term_true_iff,
      <- !negb_false_iff. simpl. rewrite var_single.
    intros [h|[h|[h|h]]]; rewrite h; repeat rewrite !andb_false_r; refl.
  Qed.

  Lemma fv_single y v u : fv (subs (single y v) u) [=]
    if mem y (fv u) then union (remove y (fv u)) (fv v) else fv u.

  Proof.
    rewrite fv_subs. simpl. rewrite domain_single, fvcod_single.
    case_eq (mem y (fv u)); intro hy; simpl.
    unfold bool_of_rel.
    case (eq_term_dec v (Var y)); intro hv; simpl.
    subst. simpl. rewrite <- mem_iff in hy. rewrite empty_b.
    intro a. set_iff. split. intros [[a1 _]|a1]. eq_dec y a; subst; auto. contr.
    intros [[a1 a2]|a1]; subst; auto.
    rewrite singleton_b, eqb_refl. intro a. set_iff. tauto.
    rewrite empty_b. intro a. set_iff. tauto.
  Qed.

  Lemma single_update x y u v s :
    ~In y (remove x (fv u)) -> ~In y (fvcodom (remove x (fv u)) s) ->
    subs (comp (single y v) (update x (Var y) s)) u = subs (update x v s) u.

  Proof.
    intros h1 h2. apply subs_seq. intros z hz; ens.
    unfold Def.comp, Def.update. eq_dec z x.
    subst. simpl. rewrite single_eq. refl.
    case_eq (beq_term (s z) (Var z)).
    rewrite beq_term_true_iff. intro e. rewrite e. simpl.
    unfold Def.single, Def.update. eq_dec z y. 2: refl.
    subst. exfalso. apply h1. set_iff. auto.
    rewrite beq_term_false_iff. intro e. rewrite subs_notin_fv. refl.
    rewrite domain_single.
    case_eq (mem y (fv (s z)) && negb (beq_term v (Var y))). 2: refl.
    rewrite andb_true_iff, <- mem_iff, negb_lr, beq_term_false_iff.
    intros [i1 i2]. exfalso. apply h2. rewrite In_fvcodom. ex z. set_iff. fo.
  Qed.

  Lemma single_update_var x u v s :
    subs (comp (single (var x u s) v) (update x (Var (var x u s)) s)) u
    = subs (update x v s) u.

  Proof.
    apply single_update. 2: apply var_notin_fvcodom.
    unfold Def.var; ens. set (xs := fvcodom (remove x (fv u)) s).
    gen (var_notin_ok (union (fv u) xs)). destruct (mem x xs); set_iff; fo.
  Qed.

(****************************************************************************)
(** ** Some equalities on single renamings. *)

  Lemma rename_id x u : rename x x u = u.

  Proof. apply single_id. Qed.

  Lemma rename_notin_fv x y u : ~In x (fv u) -> rename x y u = u.

  Proof. unfold Def.rename. apply single_notin_fv. Qed.

  Lemma rename_var y z x : rename y z (Var x) = Var (if eqb x y then z else x).

  Proof.
    unfold Def.rename, Def.single, Def.update, eqb; simpl. eq_dec x y; refl.
  Qed.

  Lemma rename_fun x y f : rename x y (Fun f) = Fun f.

  Proof. refl. Qed.

  Lemma rename_app y z u v :
    rename y z (App u v) = App (rename y z u) (rename y z v).

  Proof. refl. Qed.

  Lemma var_rename y z x u : var x u (single y (Var z))
    = if mem y (fv u) && negb (eqb x y) && eqb z x
      then var_notin (add z (fv u)) else x.

  Proof.
    rewrite var_single, beq_term_var. simpl. rewrite singleton_b.
    case_eq (mem y (fv u) && negb (eqb x y) && eqb z x).
    rewrite !andb_true_iff. intros [[h1 h2] h3]. rewrite h1, h2, h3.
    simpl. rewrite eqb_true_iff in h3. subst z. rewrite h2. simpl.
    apply var_notin_e. intro a. set_iff. tauto.
    rewrite !andb_false_iff.
    intros [[h|h]|h]; rewrite h; repeat rewrite andb_false_r; refl.
  Qed.

  Lemma fv_rename y z u : fv (rename y z u) [=] replace y z (fv u).

  Proof.
    unfold Def.rename, replace. rewrite fv_single. simpl.
    destruct (mem y (fv u)). intro a. set_iff. tauto. refl.
  Qed.

  Lemma rename_lam_no_alpha y z x u :
    ~In y (fv u) \/ x=y \/ x<>z -> rename y z (Lam x u)
    = Lam x (subs (update x (Var x) (single y (Var z))) u).

  Proof.
    intro h. unfold Def.rename. rewrite single_lam_no_alpha. refl.
    simpl. set_iff. destruct h as [h|[h|h]]; auto.
  Qed.

  Lemma remove_fv_rename x y u : ~In y (fv u) ->
    remove y (fv (rename x y u)) [=] remove x (fv u).

  Proof.
    intro hy. rewrite fv_rename; unfold replace.
    case_eq (mem x (fv u)); intro hx.
    apply remove_add. set_iff. tauto.
    rewrite remove_equal. 2: hyp. rewrite remove_equal. refl.
    rewrite mem_iff, hx. discr.
  Qed.

(****************************************************************************)
(** ** Renamings: substitutions mapping variables to variables. *)

  Definition renaming s := exists m, forall x : X, s x = Var (m x).

  (** Applying a renaming preserves the size. *)

  Lemma size_renaming1 : forall u s, renaming s -> size (subs1 s u) = size u.

  Proof.
    induction u; intros s hs; gen hs; intros [m hm]; simpl; auto.
    rewrite hm. refl. rewrite IHu. refl.
    exists (fun y => match eq_dec y x with left _ => x | _ => m y end).
    intro y. unfold Def.update. eq_dec y x. refl. apply hm.
  Qed.

  Lemma size_renaming : forall u s, renaming s -> size (subs s u) = size u.

  Proof.
    induction u; intros s hs; gen hs; intros [m hm]; simpl; auto.
    rewrite hm. refl. unfold Def.var; ens.
    set (xs := fvcodom (remove x (fv u)) s).
    destruct (mem x xs); simpl; rewrite IHu. refl.
    set (x' := var_notin (union (fv u) xs)).
    exists (fun y => match eq_dec y x with left _ => x' | _ => m y end).
    intro y. unfold Def.update. eq_dec y x. refl. apply hm.
    refl. exists (fun y => match eq_dec y x with left _ => x | _ => m y end).
    intro y. unfold Def.update. eq_dec y x. refl. apply hm.
  Qed.

  (** [rename] is a renaming. *)

  Lemma renaming_update s y z : renaming s -> renaming (update y (Var z) s).

  Proof.
    intros [m hm].
    exists (fun x => match eq_dec x y with left _ => z | _ => m x end).
    intro x. unfold Def.update. eq_dec x y. refl. apply hm.
  Qed.

  Lemma renaming_single y z : renaming (single y (Var z)).

  Proof. apply renaming_update. exists (fun x => x). refl. Qed.

  Lemma size_rename1 x y u : size (rename1 x y u) = size u.

  Proof.
    unfold Def.rename1. rewrite size_renaming1. refl. apply renaming_single.
  Qed.

  Lemma size_rename x y u : size (rename x y u) = size u.

  Proof.
    unfold Def.rename. rewrite size_renaming. refl. apply renaming_single.
  Qed.

(****************************************************************************)
(** ** Preservation of bound variables by some renaming. *)

  Lemma bv_rename x y : forall u, ~In y (bv u) -> bv (rename x y u) [=] bv u.

  Proof.
    induction u.
    (* var *)
    simpl. intros _. unfold Def.rename. simpl.
    unfold Def.single, Def.update. eq_dec x0 x; refl.
    (* fun *)
    refl.
    (* app *)
    rewrite rename_app. simpl. set_iff. intro n.
    rewrite IHu1, IHu2. refl. tauto. tauto.
    (* lam *)
    unfold Def.rename in *. simpl. set_iff. intro n. rewrite var_rename.
    case_eq (mem x (fv u) && negb (eqb x0 x) && eqb x0 y).
    rewrite andb_true_iff, eqb_true_iff. tauto.
    rewrite !andb_false_iff. eq_dec x0 x.
    (* x0 = x *)
    subst x0. simpl. bool. rewrite update_single_eq, single_id. refl.
    (* x0 <> x *)
    simpl. bool. eq_dec y x0. firstorder auto with exfalso. bool. rewrite update_id, IHu. refl. tauto.
    rewrite single_neq. refl. fo.
  Qed.

(****************************************************************************)
(** ** Bound variables of the "codomain" of a substitution:
given a substitution [s] and a finite set [xs], [bvcod s xs] is the
union of the bound variables of [s x] for every [x] in [xs]. It is
defined by iteration of the function [bvcod_fun] on [xs]. *)

  Definition bvcod_fun s (x : X) xs := union (bv (s x)) xs.

  (** [bvcod_fun] is compatible with set equality and commutes with [add]. *)

  Global Instance bvcod_fun_e :
    Proper (Logic.eq ==> Logic.eq ==> Equal ==> Equal) bvcod_fun.

  Proof.
    intros s s' ss' x x' xx' vs vs' vsvs'. subst s' x'. unfold bvcod_fun.
    rewrite vsvs'. refl.
  Qed.

  Lemma bvcod_fun_transp s : transpose Equal (bvcod_fun s).

  Proof. intros u v vs. unfold bvcod_fun. intro a. set_iff. tauto. Qed.

  Definition bvcod xs s := fold (bvcod_fun s) xs empty.

  (** [bvcod] is compatible with set equality. *)

  Global Instance bvcod_e : Proper (Equal ==> Logic.eq ==> Equal) bvcod.

  Proof.
    intros xs xs' xsxs' s s' ss'. subst s'. unfold bvcod.
    apply fold_equal. apply Equal_ST. apply bvcod_fun_e. refl. hyp.
  Qed.

  (** Set equalities on [bvcod]. *)

  Lemma bvcod_empty s : bvcod empty s [=] empty.

  Proof. unfold bvcod. rewrite fold_empty. refl. Qed.

  Lemma bvcod_add s x xs : ~In x xs ->
    bvcod (add x xs) s [=] bvcod_fun s x (bvcod xs s).

  Proof.
    intro n. unfold bvcod. rewrite fold_add. refl.
    apply Equal_ST. apply bvcod_fun_e. refl. apply bvcod_fun_transp. hyp.
  Qed.

  (** Correctness proof of [bvcod]. *)

  Lemma In_bvcod y s : forall xs,
    In y (bvcod xs s) <-> exists x, In x xs /\ In y (bv (s x)).

  Proof.
    apply set_induction_bis.
    (* Equal *)
    intros xs xs' xsxs' h. rewrite <- xsxs', h. clear h.
    intuition; destruct H as [x]; exists x; [rewrite <- xsxs'|rewrite xsxs'];
      hyp.
    (* empty *)
    rewrite bvcod_empty. set_iff. intuition. destruct H as [x].
    revert H. set_iff. tauto.
    (* add *)
    intros x xs n IH. rewrite bvcod_add. 2: hyp. unfold bvcod_fun.
    set_iff. rewrite IH. clear IH. split.
    intros [h|[a [a1 a2]]].
    ex x. split; set_iff; auto. ex a. split; set_iff; auto.
    intros [a [a1 a2]]. eq_dec a x. subst. auto. right. ex a. split.
    revert a1. set_iff. firstorder auto with exfalso. hyp.
  Qed.

  (** [bvcod] is compatible with inclusion. *)

  Global Instance bvcod_s : Proper (Subset ==> Logic.eq ==> Subset) bvcod.

  Proof.
    intros xs xs' xsxs' s s' ss' x. subst s'. rewrite !In_bvcod.
    intros [a [h1 h2]]. exists a. intuition.
  Qed.

  (** More equalities on [bvcod]. *)

  Lemma bvcod_singleton s x : bvcod (singleton x) s [=] bv (s x).

  Proof.
    intro y. split; rewrite In_bvcod.
    intros [z [h1 h2]]. revert h1. set_iff. intro e. subst z. hyp.
    intro h. exists x. set_iff. intuition.
  Qed.

  Lemma bvcod_union s p q :
    bvcod (union p q) s [=] union (bvcod p s) (bvcod q s).

  Proof.
    intro x. rewrite In_bvcod. set_iff. split.
    intros [y [h1 h2]]. revert h1. set_iff. rewrite !In_bvcod.
    intros [h1|h1]. left. exists y. intuition. right. exists y. intuition.
    rewrite !In_bvcod. intros [[y [h1 h2]]|[y [h1 h2]]].
    exists y. set_iff. tauto. exists y. set_iff. tauto.
  Qed.
 
  Lemma bvcod_single y v : forall xs,
    bvcod xs (single y v) [=] if mem y xs then bv v else empty.

  Proof.
    apply set_induction_bis.
    (* Equal *)
    intros s s' ss'. rewrite ss'. auto.
    (* empty *)
    rewrite bvcod_empty, empty_b. refl.
    (* add *)
    intros x u n IH. rewrite bvcod_add, IH. 2: hyp. clear IH.
    unfold bvcod_fun. unfold Def.single, Def.update, eqb.
    eq_dec x y; rewrite add_b.
    subst y. rewrite eqb_refl. simpl. rewrite not_mem_iff in n. rewrite n.
    intro a; set_iff; tauto.
    rewrite <- eqb_false_iff in n0. rewrite n0. simpl.
    intro a; set_iff; tauto.
  Qed.

  Lemma bvcod_rename y z xs : bvcod xs (single y (Var z)) [=] empty.

  Proof. rewrite bvcod_single. simpl. destruct (mem y xs); fset. Qed.

  Lemma bvcod_id : forall xs, bvcod xs id [=] empty.

  Proof.
    apply set_induction_bis.
    (* Equal *)
    intros xs xs' xsxs' h. rewrite <- xsxs'. hyp.
    (* empty *)
    apply bvcod_empty.
    (* add *)
    intros x xs n IH. rewrite bvcod_add. 2: hyp.
    unfold bvcod_fun. simpl. rewrite IH. fset.
  Qed.

  Lemma bvcod_update x u s xs :
    bvcod xs (update x u s) [=]
    union (if mem x xs then bv u else empty) (bvcod (remove x xs) s).

  Proof.
    intro y. set_iff. do 2 rewrite In_bvcod. split_all.
    unfold Def.update in H0. eq_dec x0 x.
    subst x0. rewrite mem_iff in H. rewrite H. auto.
    right. exists x0. set_iff. auto.
    revert H. case_eq (mem x xs); intros hx H. exists x.
    rewrite <- mem_iff in hx. rewrite update_eq. auto.
    revert H. set_iff. tauto.
    revert H. set_iff. intro H.
    exists x0. unfold Def.update. eq_dec x0 x.
    subst x0. tauto. tauto.
  Qed.

  (** [bvcod] is compatible with substitution equality. *)

  Lemma bvcod_seq xs xs' : xs [=] xs' ->
    forall s s', seq xs s s' -> bvcod xs s [=] bvcod xs' s'.

  Proof.
    intros e s s' ss' x. rewrite <- e. rewrite !In_bvcod.
    split; intros [y [h1 h2]]; exists y.
    rewrite <- (ss' _ h1). tauto. rewrite (ss' _ h1). tauto.
  Qed.

  Global Instance bvcod_seq' xs : Proper (seq xs ==> Equal) (bvcod xs).

  Proof. intros s s' ss'. apply bvcod_seq. refl. hyp. Qed.

(****************************************************************************)
(** ** Commutation properties
when free variables are distinct from bound variables.

In fact, these properties won't be used later. Instead, we will use similar properties but with another renaming-free substitution function [subs1] defined hereafter, which is equivalent when bound variables are distinct from free variables(Lemma [subs1_no_alpha]) but easier to work with, and whose properties are easier to established. *)

  (** CF, Theorem 1c, page 95, proof page 98. *)

  Lemma single_com x y v w : x<>y -> forall u,
    ~In x (fv w) \/ ~In y (fv u) ->
    inter (bv u) (union (fv v) (fv w)) [=] empty ->
    subs (single y w) (subs (single x v) u)
    = subs (single x (subs (single y w) v)) (subs (single y w) u).

  Proof.
    intro n. induction u.
    (* var *)
    simpl. set_iff. intros h _. unfold Def.single at 5.
    unfold Def.update. eq_dec x0 y.
    subst x0. rewrite single_notin_fv with (v:=w). 2: tauto.
    rewrite single_neq. 2: hyp. simpl. apply single_eq.
    simpl. unfold Def.single at 2. unfold Def.single at 2.
    unfold Def.update. eq_dec x0 x. refl. simpl. apply single_neq. auto.
    (* fun *)
    refl.
    (* app *)
    simpl. set_iff. intro h. rewrite union_inter_1, union_empty. intros [a b].
    rewrite IHu1, IHu2; split_all.
    (* lam *)
    simpl Def.fv. simpl Def.bv. set_iff. rewrite inter_empty.
    intros h1 h2.
    assert (h3 : ~In x0 (union (fv v) (fv w))). apply h2. set_iff. auto.
    revert h3. set_iff. intro h3.
    rewrite !single_lam_no_alpha. f_equal.
    eq_dec x0 x.
    subst. repeat rewrite update_single_eq, single_id; auto.
    eq_dec x0 y.
    subst. repeat rewrite update_single_eq, single_id; auto.
    rewrite !update_id_single; auto.
    rewrite single_notin_fv with (v:=v); auto.
    rewrite !update_id_single; auto. rewrite IHu. refl.
    revert h1. simpl. set_iff. tauto.
    rewrite inter_empty. intros a ha. apply h2. set_iff. auto.

    eq_dec x0 x. auto. eq_dec x0 y.
    subst. rewrite update_single_eq, single_id.
    rewrite single_notin_fv; auto. clear IHu; tauto.
    rewrite update_id_single; auto. rewrite !fv_single.
    case_eq (mem y (fv v)); intro hyv; set_iff; clear IHu; tauto.

    clear IHu; tauto. 2: clear IHu; tauto.

    eq_dec x0 x. subst. rewrite update_single_eq, single_id.
    tauto. rewrite update_id_single; auto. rewrite fv_single.
    case_eq (mem x (fv u)); intro hx; set_iff; clear IHu; tauto.
  Qed.

  Lemma update_single_split : forall u x y v w, x<>y -> ~In y (fv v) ->
    inter (bv u) (union (fv v) (fv w)) [=] empty ->
    subs (update y w (single x v)) u = subs (single y w) (subs (single x v) u).

  Proof.
    induction u; intros x' y v w n hy h.
    (* var *)
    simpl. unfold Def.update. eq_dec x y.
    subst y. rewrite single_neq. 2: auto. simpl. sym. apply single_eq.
    unfold Def.single at -2. unfold Def.update. sym. eq_dec x x'.
    apply single_notin_fv. hyp. simpl. apply single_neq. auto.
    (* fun *)
    refl.
    (* app *)
    revert h. simpl. rewrite union_inter_1, union_empty. intros [a b].
    rewrite IHu1, IHu2; tauto.
    (* lam *)
    revert h. simpl Def.bv. rewrite inter_empty. intro h.
    assert (hx : ~In x (union (fv v) (fv w))). apply h. set_iff. auto.
    revert hx; set_iff; intro hx.
    assert (~In x (fv v) /\ ~In x (fv w)). tauto. clear hx.
    rewrite subs_lam_no_alpha.

    2:{ unfold not. rewrite In_fvcodom. intros [z hz].
    revert hz. set_iff. unfold Def.single, Def.update.
    eq_dec z y; eq_dec z x'; subst; tauto. }

    rewrite !single_lam_no_alpha; try tauto.
    f_equal. eq_dec x' x.
    (* x' = x *)
    subst x'. rewrite update2_neq_com. 2: hyp.
    rewrite update2_single_eq, update_single_eq, single_id.
    apply subs_seq. intros z hz. unfold Def.single, Def.update.
    eq_dec z y; eq_dec z x; try refl.
    subst. subst. tauto.
    (* x' <> x *)
    eq_dec x y.
    (* x = y *)
    subst. rewrite update2_eq, update_id_single. 2: auto.
    rewrite update_single_eq, single_id. refl.
    (* x <> y *)
    rewrite update_id.
    2:{ unfold Def.single, Def.update. eq_dec x y; eq_dec x x'; subst; tauto. }
    rewrite update_id.
    2:{ unfold Def.single, Def.update. eq_dec x y; subst; tauto. }
    rewrite update_id. 2:{ rewrite single_neq; auto. }
    apply IHu. hyp. hyp. intro z. gen (h z). set_iff. tauto.
  Qed.

  Lemma update_single_split_swap : forall u x y v w, x<>y -> ~In x (fv w) ->
    inter (bv u) (union (fv v) (fv w)) [=] empty ->
    subs (update y w (single x v)) u = subs (single x v) (subs (single y w) u).

  Proof.
    induction u; intros x' y v w n hy h.
    (* var *)
    simpl. unfold Def.single at 3. unfold Def.update. sym. eq_dec x y.
    apply single_notin_fv. hyp. refl.
    (* fun *)
    refl.
    (* app *)
    revert h. simpl. rewrite union_inter_1, union_empty. intros [a b].
    rewrite IHu1, IHu2; tauto.
    (* lam *)
    revert h. simpl Def.bv. rewrite inter_empty. intro h.
    assert (hx : ~In x (union (fv v) (fv w))). apply h. set_iff. auto.
    revert hx; set_iff; intro hx.
    assert (~In x (fv v) /\ ~In x (fv w)). tauto. clear hx.
    rewrite subs_lam_no_alpha.

    2:{ unfold not. rewrite In_fvcodom. intros [z hz].
    revert hz. set_iff. unfold Def.single, Def.update.
    eq_dec z y; eq_dec z x'.
    subst. subst. tauto. subst. intuition. subst. intuition. intuition. }

    rewrite !single_lam_no_alpha. 2: tauto. 2: tauto.
    f_equal. eq_dec x' x.
    (* x' = x *)
    subst x'. rewrite update2_neq_com. 2: hyp.
    rewrite update2_single_eq, update_single_eq, single_id.
    apply subs_seq. intros z hz. unfold Def.single, Def.update.
    eq_dec z y; eq_dec z x; try refl.
    subst. subst. tauto.
    (* x' <> x *)
    eq_dec x y.
    (* x = y *)
    subst. rewrite update2_eq, update_id_single. 2: auto.
    rewrite update_single_eq, single_id, update_id_single. refl. auto.
    (* x <> y *)
    rewrite update_id.
    2:{ unfold Def.single, Def.update. eq_dec x y; eq_dec x x'; subst; tauto. }
    rewrite update_id.
    2:{ unfold Def.single, Def.update. eq_dec x x'; subst; tauto. }
    rewrite update_id.
    2:{ unfold Def.single, Def.update. eq_dec x y; subst; tauto. }
    apply IHu. hyp. hyp. intro z. gen (h z). set_iff. tauto.
  Qed.

  Lemma subs_lam s x u :
    subs s (Lam x u) = subs (update x (Var x) s) (Lam x u).

  Proof.
    set (s' := update x (Var x) s). simpl. set (p := remove x (fv u)).

    assert (h : fvcodom p s [=] fvcodom p s'). intro y.
    rewrite !In_fvcodom. split; intros [z [h1 [h2 h3]]].
    exists z. unfold s'. unfold Def.update. eq_dec z x.
    subst z. absurd (In x p). unfold p. set_iff. tauto. hyp.
    intuition.
    exists z. revert h2 h3. unfold s'. unfold Def.update. eq_dec z x.
    subst z. tauto. tauto.

    assert (e : var x u s = var x u s'). unfold Def.var; ens. fold p.
    rewrite h. destruct (mem x (fvcodom p s')). rewrite h. refl. refl.
    rewrite e. set (x' := var x u s'). unfold s'. rewrite update2_eq. refl.
  Qed.

  Lemma rename_lam x y z u : rename x y (Lam z u) =
    if mem x (fv u) && negb (eqb y x) && eqb y z then
      let z' := var_notin (add y (fv u)) in
        Lam z' (subs (update z (Var z') (single x (Var y))) u)
    else if eqb z x then Lam z u else Lam z (rename x y u).

  Proof.
    unfold Def.rename at 1. simpl.
    rewrite var_single, beq_term_var. simpl. rewrite singleton_b.
    case_eq (mem x (fv u) && negb (eqb z x) && negb (eqb y x) && eqb y z).

    rewrite !andb_true_iff. intros [[[h1 h2] h3] h4].
    rewrite h1, h3, h4. simpl.
    (*SLOW:rewrite union_sym, <- add_union_singleton. refl.*)
    assert (e : var_notin (union (fv u) (singleton y))
                = var_notin (add y (fv u))).
    apply var_notin_e. rewrite union_sym, <- add_union_singleton. refl.
    rewrite e. refl.
    rewrite !andb_false_iff. intros [[[h|h]|h]|h].

    rewrite h. simpl. eq_dec z x.
    subst z. rewrite update_single_eq, single_id. refl.
    rewrite update_id_single. 2: auto. refl.

    revert h. rewrite negb_false_iff, eqb_true_iff. intro h. subst z.
    rewrite update_single_eq, single_id.
    rewrite <- andb_assoc. rewrite andb_comm with (b2:=eqb y x), andb_negb_r,
      andb_false_r, eqb_refl. refl.

    rewrite h. rewrite andb_false_r. simpl. eq_dec z x.
    subst z. rewrite update_single_eq, single_id. refl.
    rewrite update_id_single. 2: auto.
    revert h. rewrite negb_false_iff, eqb_true_iff. intro h. subst y.
    rewrite single_id, rename_id. refl.

    rewrite h. rewrite !andb_false_r. eq_dec z x.
    subst z. rewrite update_single_eq, single_id. refl.
    rewrite update_id_single. 2: auto. refl.
  Qed.

  Lemma rename_subs_com x y :
    forall u s, s x = Var x -> s y = Var y -> ~In x (fvcodom (fv u) s) ->
      inter (bv u) (add y (fvcodom (fv u) s)) [=] empty ->
      rename x y (subs s u) = subs s (rename x y u).

  Proof.
    induction u; intros s hx hy.
    (* var *)
    rename x0 into z. simpl. rewrite fvcodom_singleton, rename_var.
    unfold bool_of_rel. destruct (eq_term_dec (s z) (Var z)).
    rewrite e, rename_var. eq_dec z x; auto.
    intro h. unfold Def.rename. rewrite single_notin_fv. 2: hyp.
    eq_dec z x; simpl. subst z. tauto. refl.
    (* fun *)
    refl.
    (* app *)
    simpl. rewrite fvcodom_union, union_inter_1, union_empty. set_iff.
    intros h1 [h2 h3]. rewrite rename_app, IHu1, IHu2; auto;
      rewrite empty_subset.
    rewrite union_subset_2 with (s':=fvcodom (fv u2) s) (s:=fvcodom (fv u1) s).
    rewrite <- empty_subset. hyp.
    rewrite union_subset_1 with (s':=fvcodom (fv u2) s) (s:=fvcodom (fv u1) s).
    rewrite <- empty_subset. hyp.
    (* lam *)
    rename x0 into z. simpl Def.bv. intros h1 h2.
    rewrite rename_lam. case_eq (mem x (fv u) && negb (eqb y x) && eqb y z).
    (* In x (fv u) /\ y <> x /\ y = z *)
    rewrite !andb_true_iff, eqb_true_iff. intros [[i1 i2] i3].
    subst z. revert h2. rewrite add_union_singleton, union_inter_1,
      union_empty, singleton_equal_add, inter_add_1, inter_empty_l.
    intros [h _]. gen (h y). set_iff. tauto. set_iff. auto.
    (* ~In x (fv u) \/ y = x \/ y <> z *)
    rewrite !andb_false_iff. intros [[i|i]|i].
    (* 1. ~In x (fv u) *)
    eq_dec z x.
    (* z = x *)
    subst. apply rename_notin_fv. rewrite fv_subs. simpl in *. set_iff. tauto.
    (* z <> x *)
    rewrite rename_notin_fv with (u:=u). 2: rewrite not_mem_iff; hyp.
    apply rename_notin_fv. rewrite fv_subs. simpl in *. set_iff.
    unfold Def.fvcodom in h1. rewrite <- not_mem_iff in i. intuition.
    (* 2. y = x *)
    revert i. rewrite negb_false_iff, eqb_true_iff. intro i. subst y.
    rewrite !rename_id. eq_dec z x; refl.
    (* 3. y <> z *)
    eq_dec z x.
    subst. apply rename_notin_fv. rewrite fv_subs. simpl in *. set_iff. tauto.
    rewrite !subs_lam_no_alpha. set (s' := update z (Var z) s).
    rewrite <- IHu, rename_lam, i, !andb_false_r.
    rewrite <- eqb_false_iff in n. rewrite n. refl.

    unfold s'. unfold Def.update. eq_dec x z. subst. refl. hyp.
    unfold s'. unfold Def.update. eq_dec y z. subst. refl. hyp.

    rewrite In_fvcodom. intros [b [j1 [j2 j3]]]. apply h1. rewrite In_fvcodom.
    exists b. simpl. set_iff. revert j2 j3. unfold s'. unfold Def.update.
    eq_dec b z. subst. tauto. intuition.

    assert (e : fvcodom (fv u) s' [=] fvcodom (fv (Lam z u)) s). intro a.
    rewrite !In_fvcodom. split; intros [b [j1 [j2 j3]]]; exists b;
      simpl in *; revert j1 j2 j3; set_iff;
        unfold s'; unfold Def.update; eq_dec b z.
    subst. tauto. split_all. subst. tauto. tauto.

    rewrite e. revert h2. rewrite !empty_subset, add_union_singleton.
    intro h2. rewrite union_subset_2 with (s:=singleton z) (s':=bv u). hyp.

    assert (e : fvcodom (remove z (fv (rename x y u))) s
      [=] fvcodom (fv (Lam z u)) s). intro a.
    rewrite !In_fvcodom. split; intros [b [j1 [j2 j3]]]; exists b;
      revert j1 j2 j3; set_iff; rewrite fv_rename; unfold replace;
      case_eq (mem x (fv u)); simpl; set_iff; intros ??? H2; split_all.
    subst b. revert H2. rewrite hy. simpl. set_iff. intro e. subst a. tauto.
    right. split. hyp. intro h. subst b. tauto.

    rewrite e. rewrite inter_empty in h2. gen (h2 z). set_iff. tauto.
    rewrite inter_empty in h2. gen (h2 z). set_iff. tauto.
  Qed.

(****************************************************************************)
(** ** Properties of [subs1]. *)

  (** Given [u], [fun s => subs s u] is compatible with [subs_rel R (fv u)]. *)

  Lemma subs1_rel_mon_preorder R : PreOrder R -> Monotone R ->
    forall u s s', subs_rel R (fv u) s s' -> R (subs1 s u) (subs1 s' u).

  Proof.
    intros R_qo R_mon. induction u; simpl; intros s s' h.
    (* var *)
    apply h; simpl. set_iff. refl.
    (* fun *)
    refl.
    (* app *)
    destruct R_mon.
    rewrite IHu1 with (s:=s) (s':=s'), IHu2 with (s:=s) (s':=s'). refl.
    intros x hx. apply h. simpl. apply union_subset_2. hyp.
    intros x hx. apply h. simpl. apply union_subset_1. hyp.
    (* lam *)
    mon. apply IHu. intros y hy. unfold Def.update.
    eq_dec y x. refl. apply h. set_iff. auto.
  Qed.

  (** Bound variables of a term of the form [subs1 s u] (CF, Lemma 3,
  page 99). *)

  Lemma bv_subs1 : forall u s,
    bv (subs1 s u) [<=] union (bv u) (bvcod (fv u) s).

  Proof.
    induction u; intro s; simpl; set_iff; intro a.
    (* var *)
    intro ha. rewrite union_empty_l, In_bvcod. exists x. set_iff. auto.
    (* fun *)
    set_iff. auto.
    (* app *)
    set_iff. rewrite IHu1, IHu2, bvcod_union. set_iff. tauto.
    (* lam *)
    set_iff. rewrite IHu. set_iff. rewrite bvcod_update. simpl.
    destruct (mem x (fv u)); rewrite union_empty_l; tauto.
  Qed.

  (** [subs1 s u] equals [u] if no free variable of [u] is in the
  domain of [s]. *)

  Lemma subs1_notin_fv : forall u s,
    domain (fv u) s [=] empty -> subs1 s u = u.

  Proof.
    induction u; intro s; simpl.
    (* var *)
    intro h. eapply notin_domain. apply h. set_iff. refl.
    (* fun *)
    refl.
    (* app *)
    rewrite domain_union, union_empty. intros [h1 h2].
    rewrite IHu1, IHu2; auto.
    (* lam *)
    intro h. rewrite IHu. refl. rewrite domain_update_id. hyp.
  Qed.

  (** [subs s u] is equivalent to [subs1 s u] if no bound variable of
  [u] occurs in [fvcodom (fv u) s]. *)

  Lemma subs1_no_alpha : forall u s,
    inter (bv u) (fvcodom (fv u) s) [=] empty -> subs s u = subs1 s u.

  Proof.
    induction u; intro s; simpl; auto.
    (* app *)
    rewrite fvcodom_union, union_inter_1, union_empty, inter_sym,
      inter_sym with (s:=bv u2).
    rewrite !union_inter_1, !union_empty. split_all.
    rewrite IHu1, IHu2; try rewrite inter_sym; auto.
    (* lam *)
    rewrite inter_empty. intro h1.
    assert (i : mem x (fvcodom (remove x (fv u)) s) = false).
    rewrite <- not_mem_iff. apply h1. set_iff. auto.
    assert (j : var x u s = x). unfold Def.var; ens. rewrite i. refl.
    rewrite j, IHu. refl. rewrite empty_subset. intro y. set_iff.
    intros [i1 i2]. eapply h1. set_iff. right. apply i1.
    rewrite <- fvcodom_update_id. hyp.
  Qed.

  Lemma rename1_no_alpha u x y :
    x=y \/ ~In x (fv u) \/ ~In y (bv u) -> rename x y u = rename1 x y u.

  Proof.
    intro h. unfold Def.rename, Def.rename1. apply subs1_no_alpha.
    apply inter_empty. intros z hz. rewrite fvcodom_single.
    case_eq (mem x (fv u) && negb (beq_term (Var y) (Var x))); simpl; set_iff.
    2: fo. rewrite andb_eq, <- mem_iff, beq_term_var, negb_lr; simpl.
    unfold XSetFacts.eqb. eq_dec y x; split_all; subst; firstorder with bool.
  Qed.

  (** [subs1 s1 u] equals [subs1 s2 u] if [s1] and [s2] are equal on
  the free variables of [u]. *)

  Lemma subs1_seq : forall u s1 s2, (forall x, In x (fv u) -> s1 x = s2 x) ->
    subs1 s1 u = subs1 s2 u.

  Proof.
    induction u; simpl; intros s1 s2 h.
    (* var *)
    apply h. set_iff. refl.
    (* fun *)
    refl.
    (* app *)
    rewrite IHu1 with (s1:=s1) (s2:=s2), IHu2 with (s1:=s1) (s2:=s2);
      intuition; apply h; set_iff; auto.
    (* lam *)
    rewrite IHu with (s1:=update x (Var x) s1) (s2:=update x (Var x) s2).
    refl. intros y hy. unfold Def.update. eq_dec y x. refl.
    apply h. set_iff. auto.
  Qed.

  (** Other properties of [subs1]. *)

  Lemma subs1_update2_eq x u v w s :
    subs1 (update x v (update x w s)) u = subs1 (update x v s) u.

  Proof. apply subs1_seq. intros z hz. unfold Def.update. eq_dec z x; refl. Qed.

  Lemma subs1_update2_neq_com s x u y v w : x <> y ->
    subs1 (update x u (update y v s)) w = subs1 (update y v (update x u s)) w.

  Proof.
    intro n. apply subs1_seq. intros z hz. unfold Def.update.
    eq_dec z x; eq_dec z y; try refl. subst. tauto.
  Qed.

  Lemma subs1_update_single_eq y v w u :
    subs1 (update y w (single y v)) u = subs1 (single y w) u.

  Proof.
    apply subs1_seq. intros b hb. unfold Def.single, Def.update.
    eq_dec b y; refl.
  Qed.

  Lemma subs1_update2_single_eq y w x v v' u :
    subs1 (update y w (update x v' (single x v))) u
    = subs1 (update y w (single x v')) u.

  Proof.
    apply subs1_seq. intros z hz.
    unfold Def.update at -2. eq_dec z y. refl.
    match goal with |- ?x _ = ?y _ => set (s1:=x); set (s2:=y) end.
    change (subs s1 (Var z) = subs s2 (Var z)). unfold s1, s2.
    rewrite update_single_eq. refl.
  Qed.

  Lemma subs1_update_id x s u : s x = Var x ->
    subs1 (update x (Var x) s) u = subs1 s u.

  Proof.
    intro h. apply subs1_seq. intros z hz. unfold Def.update.
    eq_dec z x. subst. auto. refl.
  Qed.

  Lemma subs1_id : forall u, subs1 id u = u.

  Proof.
    induction u; simpl; auto. rewrite IHu1, IHu2. refl.
    f_equal. rewrite subs1_update_id. hyp. refl.
  Qed.

  Lemma subs1_single_id y u : subs1 (single y (Var y)) u = u.

  Proof.
    rewrite <- subs1_id. apply subs1_seq. intros x hx.
    unfold Def.single, Def.update. eq_dec x y. subst. refl. refl.
  Qed.
 
  Lemma subs1_update_id_single y v x u : x<>y \/ v=Var x ->
    subs1 (update x (Var x) (single y v)) u = subs1 (single y v) u.

  Proof.
    intro h. apply subs1_seq. intros b hb.
    unfold Def.single, Def.update. eq_dec b x; eq_dec b y.
    subst. destruct h. tauto. subst. refl.
    subst. refl. refl. refl.
  Qed.

  Lemma subs1_update_single_id y v x u :
    subs1 (update y v (single x (Var x))) u = subs1 (single y v) u.

  Proof.
    apply subs1_seq. intros z hz.
    unfold Def.single. unfold Def.update at -2.
    eq_dec z y. refl. unfold Def.update. eq_dec z x.
    subst z. refl. refl.
  Qed.

  (** Composition properties of [subs1]. *)

  Lemma subs1_update_single x y y' : forall u s, ~In y (bv u) ->
    subs1 (update y (Var y') s) (subs1 (single x (Var y)) u)
    = subs1 (update x (Var y') (update y (Var y') s)) u.

  Proof.
    induction u; intro s; simpl; set_iff; intro hy.
    (* var *)
    rename x0 into z. unfold Def.single. unfold Def.update at -1.
    eq_dec z x; simpl.
    rewrite update_eq. refl.
    unfold Def.update. eq_dec z y; refl.
    (* fun *)
    refl.
    (* app *)
    rewrite IHu1, IHu2; auto.
    (* lam *)
    rename x0 into z. f_equal. eq_dec z x.
    (* z = x *)
    subst z. rewrite subs1_update2_eq, subs1_update_single_eq, subs1_single_id.
    refl.
    (* z <> x *)
    rewrite subs1_update2_neq_com. 2: tauto.
    rewrite subs1_update_id_single. 2: tauto.
    rewrite IHu; auto. apply subs1_seq. intros a ha. unfold Def.update.
    eq_dec a x; eq_dec a y; eq_dec a z;
      try subst a; try subst x; try subst y; tauto.
  Qed.

  Lemma subs1_single_subs1 y v : forall u s, s y = Var y ->
    ~In y (fvcodom (fv u) s) ->
    subs1 (single y v) (subs1 s u) = subs1 (update y v s) u.

  Proof.
    induction u; intros s h1; simpl.
    (* var *)
    rewrite fvcodom_singleton. unfold bool_of_rel.
    destruct (eq_term_dec (s x) (Var x)).
    intros _. rewrite e. simpl. unfold Def.single, Def.update. eq_dec x y; auto.
    intro h2. rewrite subs1_notin_fv. unfold Def.update. eq_dec x y.
    subst y. tauto. refl.
    rewrite empty_subset. intro a. rewrite In_domain.
    unfold Def.single, Def.update. eq_dec a y. subst a. tauto. tauto.
    (* fun *)
    refl.
    (* app *)
    rewrite fvcodom_union. set_iff. intro h2. rewrite IHu1, IHu2; auto.
    (* lam *)
    intro h2. f_equal. unfold Def.single. eq_dec x y.
    subst y. rewrite !subs1_update2_eq, !subs1_update_id; auto. apply subs1_id.
    rewrite subs1_update_id. 2: unfold Def.update; eq_dec x y; tauto.
    fold (single y v). rewrite IHu, subs1_update2_neq_com. refl. auto.
    unfold Def.update. eq_dec y x. subst y. tauto. hyp.
    rewrite fvcodom_update_id. hyp.
  Qed.

  Lemma subs1_single_update x x' y' : forall u s, ~In x' (fv u) ->
    ~In x' (fvcodom (remove x (fv u)) s) -> ~In x' (bv u) -> ~In x (bv u) ->
    subs1 (single x' (Var y')) (subs1 (update x (Var x') s) u)
    = subs1 (update x' (Var y') (update x (Var y') s)) u.

  Proof.
    induction u; intro s; simpl; (*SLOW*)set_iff; intros h1 h2 h3 h4.
    (* var *)
    rename x0 into z. unfold Def.update.
    eq_dec z x; eq_dec z x'; simpl.
    unfold Def.single. rewrite update_eq. refl.
    unfold Def.single. rewrite update_eq. refl.
    tauto.
    rewrite subs1_notin_fv. refl. rewrite domain_single, beq_term_var.
    case_eq (mem x' (fv (s z)) && negb (eqb y' x')). 2: refl.
    rewrite andb_true_iff, negb_true_iff, eqb_false_iff, <- mem_iff.
    intros [i1 i2]. absurd (In x' (fvcodom (remove x (singleton z)) s)). hyp.
    rewrite In_fvcodom. exists z. set_iff. split_all.
    revert i1. rewrite H. simpl. set_iff. hyp.
    (* fun *)
    refl.
    (* app *)
    revert h2. rewrite remove_union, fvcodom_union. set_iff. intro h2.
    rewrite IHu1, IHu2; auto.
    (* lam *)
    rename x0 into z. f_equal. eq_dec z x'. tauto.
    rewrite subs1_update2_neq_com with (y:=x'). 2: tauto.
    rewrite subs1_update_id_single. 2: tauto. eq_dec z x. tauto.
    rewrite subs1_update2_neq_com. 2: tauto. rewrite IHu; auto.
    2:{ rewrite In_fvcodom. intros [a [i1 [i2 i3]]]. revert i1 i2 i3.
    unfold Def.update. eq_dec a z; simpl; set_iff. tauto.
    intros [i0 i1] i2 i3. apply h2. rewrite In_fvcodom. exists a. set_iff.
    intuition. }
    apply subs1_seq. intros a ha. unfold Def.update.
    eq_dec a x'; eq_dec a x; eq_dec a z;
      try subst a; try subst x; try subst z; tauto.
  Qed.

  Lemma subs1_comp : forall u s1 s2,
    inter (bv u) (fvcodom (fv u) s1) [=] empty ->
    subs1 s2 (subs1 s1 u) = subs1 (comp1 s2 s1) u.

  Proof.
    induction u; intros s1 s2 h; simpl. refl. refl.
    (* app *)
    rewrite IHu1, IHu2; try refl; revert h; simpl.
    rewrite union_inter_1, union_empty, fvcodom_union. intros [h1 h2].
    rewrite inter_sym, union_inter_1, union_empty in h1, h2.
    rewrite inter_sym. tauto.
    rewrite union_inter_1, union_empty, fvcodom_union. intros [h1 h2].
    rewrite inter_sym, union_inter_1, union_empty in h1, h2.
    rewrite inter_sym. tauto.
    (* lam *)
    f_equal. rewrite IHu. apply subs1_seq.
    intros y hy. unfold Def.comp1 at 1. unfold Def.update at -1.
    eq_dec y x; simpl. apply update_eq.
    unfold Def.comp1. apply subs1_seq. intros z hz. unfold Def.update.
    eq_dec z x. 2: refl. subst z. sym.

    rewrite inter_empty in h. simpl in h.
    absurd (In x (fvcodom (remove x (fv u)) s1)). apply h. set_iff. auto.
    rewrite In_fvcodom. exists y. set_iff. intuition.
    revert hz. rewrite H. simpl. set_iff. hyp.

    revert h. do 2 rewrite inter_empty. simpl. intros h y hy.
    rewrite In_fvcodom. intros [z [i1 [i2 i3]]]. revert i2 i3.
    unfold Def.update. eq_dec z x. subst z. tauto. intros i2 i3.
    eapply h. set_iff. right. apply hy. rewrite In_fvcodom. exists z.
    set_iff. intuition.
  Qed.

End Make.
