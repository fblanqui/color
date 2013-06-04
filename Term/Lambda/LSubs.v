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

Require Import BoolUtil SetoidList Basics Morphisms LogicUtil.
Require Import LTerm.

Module Make (Export L : L_Struct).

  Module Export T := LTerm.Make L.

(****************************************************************************)
(** ** Type for substitutions:
a substitution is given by a total function from [X] to [Te]. *)

  Definition Su := X -> Te.

  (** Identity substitution. *)

  Definition id := fun y => Var y.

  (** [update x t s] is the substitution mapping [x] to [t] and any
  other variable [y] to [s y]. *)

  Definition update x (t : Te) s := fun y =>
    match eq_dec y x with
      | left _ => t
      | _ => s y
    end.

  Lemma update_eq : forall x u s, update x u s x = u.

  Proof. intros x u s. unfold update. eq_dec x x. refl. fo. Qed.

  Lemma update_neq : forall x u s y, x <> y -> update x u s y = s y.

  Proof.
    intros x u s y n. unfold update. eq_dec y x. subst y. tauto. refl.
  Qed.

  (** [single x t] is the substitution mapping [x] to [t] and leaving
  any other variable unchanged. *)

  Definition single x t := update x t id.

  Lemma single_eq : forall y v, single y v y = v.

  Proof. intros y v. unfold single. apply update_eq. Qed.

  Lemma single_neq : forall y v z, y <> z -> single y v z = Var z.

  Proof.
    intros y v z n. unfold single, update, id. eq_dec z y. subst. tauto. refl.
  Qed.

  (** [restrict xs s] is the substitution mapping any variable [z] of
  [xs] to [s z] and leaving any other variable unchanged. *)
 
  Definition restrict xs s z := if mem z xs then s z else Var z.

  (** Predicate saying that the domain of a substitution is included
  in some finite set. *)

  Definition dom_incl xs s := forall x, ~In x xs -> s x = Var x.

  Instance dom_incl_e : Proper (Equal ==> Logic.eq ==> iff) dom_incl.

  Proof.
    intros xs xs' e s s' ss'. subst s'. unfold dom_incl. intuition.
    apply H. rewrite e. hyp. apply H. rewrite <- e. hyp.
  Qed.

  Instance dom_incl_s : Proper (Subset ==> Logic.eq ==> impl) dom_incl.

  Proof.
    intros xs xs' xsxs' s s' ss' h x hx. subst s'. apply h. rewrite xsxs'. hyp.
  Qed.

  Lemma dom_incl_restrict : forall s xs, dom_incl xs (restrict xs s).

  Proof.
    intros s xs x. rewrite not_mem_iff. intro hx. unfold restrict.
    rewrite hx. refl.
  Qed.

(****************************************************************************)
(** ** Syntactic equality of two substitutions on some finite set of variables *)

  Definition seq xs (s s' : Su) := forall x, In x xs -> s x = s' x.

  (** For all [xs], [seq xs] is an equivalence relation. *)

  Instance seq_refl : forall xs, Reflexive (seq xs).

  Proof. fo. Qed.

  Instance seq_sym : forall xs, Symmetric (seq xs).

  Proof. fo. Qed.

  Instance seq_trans : forall xs, Transitive (seq xs).

  Proof. intros xs s1 s2 s3 a b x h. trans (s2 x); fo. Qed.

  (** [seq] is compatible with set equality and inclusion. *)

  Instance seq_e : Proper (Equal ==> Logic.eq ==> Logic.eq ==> iff) seq.

  Proof.
    intros xs xs' e s1 s1' h1 s2 s2' h2. subst s1' s2'. unfold seq.
    intuition. apply H. rewrite e. hyp. apply H. rewrite <- e. hyp.
  Qed.

  Instance seq_s : Proper (Subset --> Logic.eq ==> Logic.eq ==> impl) seq.

  Proof.
    intros xs xs' e s1 s1' h1 s2 s2' h2. subst s1' s2'.
    unfold flip, impl, seq in *. intuition.
  Qed.

  Lemma seq_restrict : forall xs ys s, xs [<=] ys -> seq xs s (restrict ys s).

  Proof.
    intros xs ys s i x. rewrite i, mem_iff. intro h. unfold restrict.
    rewrite h. refl.
  Qed.

(****************************************************************************)
(** ** "Domain" of a substitution:
given a substitution [s] and a finite set [xs], [domain s xs] is the
set of variables [x] in [xs] such that [s x <> Var x]. It is defined
by iteration of the function [domain_fun] on [xs]. *)

  Definition domain_fun s x xs :=
    if beq_term (s x) (Var x) then xs else add x xs.

  (** [domain_fun] is compatible with set inclusion and equality and
  commutes with [add]. *)

  Instance domain_fun_s : Proper (Logic.eq ==> Logic.eq ==> Subset ==> Subset)
    domain_fun.

  Proof.
    intros s s' ss' x x' xx' xs xs' xsxs'. subst x' s'.
    unfold domain_fun, beq_term.
    destruct (eq_term_dec (s x) (Var x)); rewrite xsxs'; refl.
  Qed.

  Instance domain_fun_e : Proper (Logic.eq ==> Logic.eq ==> Equal ==> Equal)
    domain_fun.

  Proof.
    intros s s' ss' x x' xx' xs xs' xsxs'. subst x' s'.
    unfold domain_fun, beq_term.
    destruct (eq_term_dec (s x) (Var x)); rewrite xsxs'; refl.
  Qed.

  Lemma domain_fun_transp : forall s, transpose Equal (domain_fun s).

  Proof.
    intros s x y xs. unfold domain_fun, beq_term.
    destruct (eq_term_dec (s x) (Var x)); destruct (eq_term_dec (s y) (Var y));
      try refl. apply add_add.
  Qed.

  Definition domain xs s := fold (domain_fun s) xs empty.

  (** [domain] is compatible with set equality. *)

  Instance domain_e : Proper (Equal ==> Logic.eq ==> Equal) domain.

  Proof.
    intros xs xs' xsxs' s s' ss'. subst s'. unfold domain.
    apply fold_equal. apply Equal_ST. apply domain_fun_e. refl. hyp.
  Qed.

  (** Set equalities on [domain]. *)

  Lemma domain_empty : forall s, domain empty s [=] empty.

  Proof. intro s. unfold domain. rewrite fold_empty. refl. Qed.

  Lemma domain_add : forall s x xs, ~In x xs ->
    domain (add x xs) s [=] domain_fun s x (domain xs s).

  Proof.
    intros s x xs n. unfold domain. rewrite fold_add. refl.
    apply Equal_ST. apply domain_fun_e. refl. apply domain_fun_transp. hyp.
  Qed.

  (** Correctness proof of the definition of [domain]. *)

  Lemma In_domain : forall x s xs,
    In x (domain xs s) <-> In x xs /\ s x <> Var x.

  Proof.
    intros x s. apply set_induction_bis.
    (* Equal *)
    intros xs xs' xsxs' h. rewrite <- xsxs', h. refl.
    (* empty *)
    rewrite domain_empty. set_iff. intuition.
    (* add *)
    intros y xs n IH. rewrite domain_add. set_iff. 2: hyp.
    unfold domain_fun, beq_term. destruct (eq_term_dec (s y) (Var y)).
    rewrite IH. intuition. subst y. tauto.
    set_iff. rewrite IH. intuition. subst y. tauto.
  Qed.

  Lemma mem_domain : forall x s xs,
    mem x (domain xs s) = mem x xs && negb (beq_term (s x) (Var x)).

  Proof.
    intros x s xs.
    rewrite eqb_equiv, andb_true_iff, negb_true_iff, beq_term_false_iff.
    repeat rewrite <- mem_iff. apply In_domain.
  Qed.

  Lemma notin_domain : forall s xs x,
    domain xs s [=] empty -> In x xs -> s x = Var x.

  Proof.
    intros s xs x h1 h2. destruct (eq_term_dec (s x) (Var x)). hyp.
    absurd (In x (domain xs s)). rewrite h1. set_iff. tauto.
    rewrite In_domain. tauto.
  Qed.

  (** [domain] is compatible with set inclusion. *)

  Instance domain_s : Proper (Subset ==> Logic.eq ==> Subset) domain.

  Proof.
    intros xs xs' xsxs' s s' ss' x. subst s'. do 2 rewrite In_domain.
    rewrite xsxs'. auto.
  Qed.

  Lemma domain_subset : forall s xs, domain xs s [<=] xs.

  Proof. intros s xs x. rewrite In_domain. intuition. Qed.

  (** More set equalities on [domain]. *)

  Lemma domain_singleton : forall s x, domain (singleton x) s
    [=] if beq_term (s x) (Var x) then empty else singleton x.

  Proof.
    intros s x y. unfold beq_term.
    destruct (eq_term_dec (s x) (Var x)); rewrite In_domain; set_iff;
      intuition; subst; tauto.
  Qed.

  Lemma domain_union : forall s p q,
    domain (union p q) s [=] union (domain p s) (domain q s).

  Proof.
    intros s p q x. set_iff. repeat rewrite In_domain. set_iff. tauto.
  Qed.

  Lemma domain_single : forall y v xs, domain xs (single y v)
    [=] if mem y xs && negb (beq_term v (Var y)) then singleton y else empty.

  Proof.
    intros y v. apply set_induction_bis.
    (* Equal *)
    intros xs xs' xsxs'. rewrite xsxs'. auto.
    (* empty *)
    rewrite domain_empty, empty_b. refl.
    (* add *)
    intros x xs n IH. rewrite domain_add, add_b, IH. 2: hyp. clear IH.
    unfold eqb, domain_fun. unfold beq_term at 1.
    destruct (eq_term_dec (single y v x) (Var x)).
    revert e. unfold single, update, id.
    eq_dec x y; intro h.
    subst. rewrite not_mem_iff in n.
    rewrite n, beq_term_refl. refl.
    refl.
    unfold beq_term. revert n0. unfold single, update, id.
    eq_dec x y; simpl. 2: tauto. subst.
    destruct (mem y xs); destruct (eq_term_dec v (Var y)); simpl.
    tauto.
    rewrite singleton_equal_add, add_equal. refl. set_iff. auto.
    tauto.
    rewrite singleton_equal_add. refl.
  Qed.

  Lemma domain_rename : forall y z xs, domain xs (single y (Var z))
    [=] if mem y xs && negb (eqb z y) then singleton y else empty.

  Proof. intros x z xs. rewrite domain_single, beq_term_var. refl. Qed.

  Lemma domain_single_empty : forall y v xs,
    domain xs (single y v) [=] empty <-> ~In y xs \/ v = Var y.

  Proof.
    intros y v xs. rewrite domain_single.
    case_eq (mem y xs && negb (beq_term v (Var y))).
    rewrite andb_true_iff, <- mem_iff, negb_true_iff, beq_term_false_iff.
    intuition. exfalso. absurd (In y empty). fo. rewrite <- H. set_iff. refl.
    rewrite andb_false_iff, <- not_mem_iff, negb_false_iff, beq_term_true_iff.
    fo.
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
    unfold domain_fun, id, beq_term.
    destruct (eq_term_dec (Var x) (Var x)). hyp. absurd (Var x=Var x); tauto.
  Qed.

  Lemma domain_update_id : forall x s xs,
    domain xs (update x (Var x) s) [=] domain (remove x xs) s.

  Proof.
    intros x s xs. intro y. repeat rewrite In_domain. set_iff. unfold update.
    eq_dec y x. subst. intuition. intuition.
  Qed.

  (** [domain] is compatible with substitution equality. *)

  Lemma domain_seq : forall xs xs', xs [=] xs' ->
    forall s s', seq xs s s' -> domain xs s [=] domain xs' s'.

  Proof.
    intros xs xs' e s s' ss' x. rewrite <- e. repeat rewrite In_domain.
    intuition.
    apply H1. rewrite <- H. apply ss'. hyp.
    apply H1. rewrite <- H. sym. apply ss'. hyp.
  Qed.

  Instance domain_seq' : forall xs, Proper (seq xs ==> Equal) (domain xs).

  Proof. intros xs s s' ss'. apply domain_seq. refl. hyp. Qed.

(****************************************************************************)
(** ** Free variables of the "codomain" of a substitution:
given a substitution [s] and a finite set [xs], [fvcod s xs] is the
union of the free variables of [s x] for every [x] in [xs]. It is
defined by iteration of the function [fvcod_fun] on [xs]. *)

  Definition fvcod_fun s (x : X) xs := union (fv (s x)) xs.

  (** [fvcod_fun] is compatible with set equality and commutes with [add]. *)

  Instance fvcod_fun_e : Proper (Logic.eq ==> Logic.eq ==> Equal ==> Equal)
    fvcod_fun.

  Proof.
    intros s s' ss' x x' xx' vs vs' vsvs'. subst s' x'. unfold fvcod_fun.
    rewrite vsvs'. refl.
  Qed.

  Lemma fvcod_fun_transp : forall s, transpose Equal (fvcod_fun s).

  Proof. intros s u v vs. unfold fvcod_fun. fset. Qed.

  Definition fvcod xs s := fold (fvcod_fun s) xs empty.

  (** [fvcod] is compatible with set equality. *)

  Instance fvcod_e : Proper (Equal ==> Logic.eq ==> Equal) fvcod.

  Proof.
    intros xs xs' xsxs' s s' ss'. subst s'. unfold fvcod.
    apply fold_equal. apply Equal_ST. apply fvcod_fun_e. refl. hyp.
  Qed.

  (** Set equalities on [fvcod]. *)

  Lemma fvcod_empty : forall s, fvcod empty s [=] empty.

  Proof. intro s. unfold fvcod. rewrite fold_empty. refl. Qed.

  Lemma fvcod_add : forall s x xs, ~In x xs ->
    fvcod (add x xs) s [=] fvcod_fun s x (fvcod xs s).

  Proof.
    intros s x xs n. unfold fvcod. rewrite fold_add. refl.
    apply Equal_ST. apply fvcod_fun_e. refl. apply fvcod_fun_transp. hyp.
  Qed.

  (** Correctness proof of [fvcod]. *)

  Lemma In_fvcod : forall y s xs,
    In y (fvcod xs s) <-> exists x, In x xs /\ In y (fv (s x)).

  Proof.
    intros y s. apply set_induction_bis.
    (* Equal *)
    intros xs xs' xsxs' h. rewrite <- xsxs', h. clear h.
    intuition; destruct H as [x]; exists x; [rewrite <- xsxs'|rewrite xsxs'];
      hyp.
    (* empty *)
    rewrite fvcod_empty. set_iff. intuition. destruct H as [x].
    revert H. set_iff. intuition.
    (* add *)
    intros x xs n IH. rewrite fvcod_add. 2: hyp. unfold fvcod_fun.
    set_iff. rewrite IH. clear IH. intuition.
    exists x. set_iff. auto.
    destruct H0 as [z]. exists z. set_iff. intuition.
    destruct H as [z]. revert H. set_iff. intuition. subst z. auto.
    right. exists z. auto.
  Qed.

  (** [fvcod] is compatible with inclusion. *)

  Instance fvcod_s : Proper (Subset ==> Logic.eq ==> Subset) fvcod.

  Proof.
    intros xs xs' xsxs' s s' ss' x. subst s'. repeat rewrite In_fvcod.
    intros [a [h1 h2]]. exists a. intuition.
  Qed.

  (** More equalities on [fvcod]. *)

  Lemma fvcod_singleton : forall s x, fvcod (singleton x) s [=] fv (s x).

  Proof.
    intros s x y. split; rewrite In_fvcod.
    intros [z [h1 h2]]. revert h1. set_iff. intro e. subst z. hyp.
    intro h. exists x. set_iff. intuition.
  Qed.

  Lemma fvcod_union : forall s p q,
    fvcod (union p q) s [=] union (fvcod p s) (fvcod q s).

  Proof.
    intros s p q x. rewrite In_fvcod. set_iff. split.
    intros [y [h1 h2]]. revert h1. set_iff. repeat rewrite In_fvcod.
    intros [h1|h1]. left. exists y. intuition. right. exists y. intuition.
    repeat rewrite In_fvcod. intros [[y [h1 h2]]|[y [h1 h2]]].
    exists y. set_iff. intuition. exists y. set_iff. intuition.
  Qed.
 
  Lemma fvcod_single : forall y v xs, fvcod xs (single y v)
    [=] if mem y xs then union (fv v) (remove y xs) else xs.

  Proof.
    intros y v. apply set_induction_bis.
    (* Equal *)
    intros s s' ss'. rewrite ss'. intro h. rewrite h.
    destruct (mem y s'); rewrite ss'; refl.
    (* empty *)
    rewrite fvcod_empty, empty_b. refl.
    (* add *)
    intros x u n IH. rewrite fvcod_add, IH. 2: hyp. clear IH.
    unfold fvcod_fun, single, update, id, eqb. eq_dec x y; simpl.
    subst y. rewrite add_b, eqb_refl. simpl. rewrite not_mem_iff in n.
    rewrite n. rewrite <- not_mem_iff in n.
    fset. right. intuition. subst x. auto.
    rewrite <- eqb_false_iff in n0. rewrite add_b, n0. simpl.
    case_eq (mem y u); [rewrite <- mem_iff|rewrite <- not_mem_iff]; intro hy.
    fset. subst a. rewrite eqb_false_iff in n0. intuition.
    sym. apply add_union_singleton.
  Qed.

  Lemma fvcod_rename : forall y z xs, fvcod xs (single y (Var z))
    [=] if mem y xs then add z (remove y xs) else xs.

  Proof.
    intros y z xs. rewrite fvcod_single. simpl. destruct (mem y xs); fset.
  Qed.

  Lemma fvcod_id : forall xs, fvcod xs id [=] xs.

  Proof.
    apply set_induction_bis.
    (* Equal *)
    intros xs xs' xsxs' h. rewrite <- xsxs'. hyp.
    (* empty *)
    apply fvcod_empty.
    (* add *)
    intros x xs n IH. rewrite fvcod_add. 2: hyp. unfold fvcod_fun, id. simpl.
    rewrite IH. fset.
  Qed.

  (** [fvcod] is compatible with substitution equality. *)

  Lemma fvcod_seq : forall xs xs', xs [=] xs' ->
    forall s s', seq xs s s' -> fvcod xs s [=] fvcod xs' s'.

  Proof.
    intros xs xs' e s s' ss' x. rewrite <- e. repeat rewrite In_fvcod.
    split; intros [y [h1 h2]]; exists y; intuition.
    rewrite <- (ss' _ h1). hyp. rewrite (ss' _ h1). hyp.
  Qed.

  Instance fvcod_seq' : forall xs, Proper (seq xs ==> Equal) (fvcod xs).

  Proof. intros xs s s' ss'. apply fvcod_seq. refl. hyp. Qed.

(****************************************************************************)
(** ** Let [fvcodom] be the composition of [fvcod] and [domain]. *)

  Definition fvcodom xs s := fvcod (domain xs s) s.

  (** [fvcodom] is compatible with set inclusion and equality. *)

  Instance fvcodom_s : Proper (Subset ==> Logic.eq ==> Subset) fvcodom.

  Proof.
    intros xs xs' xsxs' s s' ss'. subst s'. unfold fvcodom. rewrite xsxs'.
    refl.
  Qed.

  Instance fvcodom_e : Proper (Equal ==> Logic.eq ==> Equal) fvcodom.

  Proof.
    intros xs xs' xsxs' s s' ss' . subst s'. unfold fvcodom. rewrite xsxs'.
    refl.
  Qed.

  (** Correctness of [fvcodom]. *)

  Lemma In_fvcodom : forall s xs y, In y (fvcodom xs s)
    <-> (exists x, In x xs /\ s x <> Var x /\ In y (fv (s x))).

  Proof.
    intros s xs y. unfold fvcodom. rewrite In_fvcod. intuition;
      destruct H as [x hx]; exists x; rewrite In_domain in *; tauto.
  Qed.

  (* Set equalities on [fvcodom]. *)

  Lemma fvcodom_singleton : forall s x, fvcodom (singleton x) s
    [=] if beq_term (s x) (Var x) then empty else fv (s x).

  Proof.
    intros s x. unfold fvcodom. rewrite domain_singleton. unfold beq_term.
    destruct (eq_term_dec (s x) (Var x)). apply fvcod_empty.
    apply fvcod_singleton.
  Qed.

  Lemma fvcodom_union : forall s p q,
    fvcodom (union p q) s [=] union (fvcodom p s) (fvcodom q s).

  Proof.
    intros s p q x. set_iff. unfold fvcodom. rewrite domain_union, fvcod_union.
    set_iff. refl.
  Qed.

  Lemma fvcodom_id : forall xs, fvcodom xs id [=] empty.

  Proof. intros xs. unfold fvcodom. rewrite fvcod_id, domain_id. refl. Qed.

  Lemma fvcodom_single : forall y v xs, fvcodom xs (single y v)
    [=] if mem y xs && negb (beq_term v (Var y)) then fv v else empty.

  Proof.
    intros y v xs. unfold fvcodom. rewrite domain_single, fvcod_single.
    unfold beq_term. case_eq (mem y xs); intro hy;
      destruct (eq_term_dec v (Var y)); simpl; try rewrite empty_b.
    refl. rewrite singleton_b, eqb_refl, singleton_equal_add,
      remove_add, empty_union_2. refl. fo. set_iff. tauto. refl. refl.
  Qed.

  Lemma fvcodom_rename : forall y z xs, fvcodom xs (single y (Var z))
    [=] if mem y xs && negb (eqb z y) then singleton z else empty.

  Proof. intros y z xs. rewrite fvcodom_single, beq_term_var. refl. Qed.

  Lemma fvcodom_update_id : forall x s xs,
    fvcodom xs (update x (Var x) s) [=] fvcodom (remove x xs) s.

  Proof.
    intros x s xs. unfold fvcodom. rewrite domain_update_id.
    set (d := domain (remove x xs) s). intro y. repeat rewrite In_fvcod.
    assert (h : ~In x d). unfold d. rewrite In_domain. set_iff. tauto.
    unfold update; split; intros [a [h1 h2]]; exists a; intuition;
      eq_dec a x; revert h1 h2; simpl; set_iff; intros h1 h2;
        auto; subst a; tauto.
  Qed.

  (** [fvcodom] is compatible with substitution equality. *)

  Lemma fvcodom_seq : forall xs xs', xs [=] xs' ->
    forall s s', seq xs s s' -> fvcodom xs s [=] fvcodom xs' s'.

  Proof.
    intros xs xs' e s s' ss'. unfold fvcodom. rewrite <- e. apply fvcod_seq.
    apply domain_seq. refl. hyp. rewrite domain_subset. hyp.
  Qed.

  Instance fvcodom_seq' : forall xs, Proper (seq xs ==> Equal) (fvcodom xs).

  Proof. intros xs s s' ss'. apply fvcodom_seq. refl. hyp. Qed.

(****************************************************************************)
(** ** [subs]: Effect of a substitution on a term.
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
A) A] if [A] is not empty).
*)

  (** Generation of a fresh variable. *)

  Definition var x u s :=
    let xs := fvcodom (remove x (fv u)) s in
      if mem x xs then var_notin (union (fv u) xs) else x.

  Lemma var_seq : forall x x', x=x' -> forall u u', u=u' -> forall s s',
    seq (remove x (fv u)) s s' -> var x u s = var x' u' s'.

  Proof.
    intros x x' xx' u u' uu' s s' ss'. subst x' u'. unfold var.
    rewrite ss'. destruct (mem x (fvcodom (remove x (fv u)) s')).
    rewrite ss'. refl. refl.
  Qed.

  Instance var_seq' : forall x u, Proper (seq (remove x (fv u)) ==> Logic.eq)
    (var x u).

  Proof. intros x u s s' ss'. apply var_seq; auto. Qed.

  Arguments var_seq' [x u x0 y] _.

  Lemma var_notin_fvcodom : forall x u s,
    ~In (var x u s) (fvcodom (remove x (fv u)) s).

  Proof.
    intros x u s. unfold var. set (xs := fvcodom (remove x (fv u)) s).
    case_eq (mem x xs).
    gen (var_notin_ok (union (fv u) xs)). set_iff. tauto.
    rewrite <- not_mem_iff. auto.
  Qed.

  Lemma var_notin_fv_subs : forall x u s y,
    In y (fv u) -> y <> x -> ~In (var x u s) (fv (s y)).

  Proof.
    intros x u s y hy n h.
    apply var_notin_fvcodom with (x:=x) (u:=u) (s:=s).
    rewrite In_fvcodom. exists y. set_iff. intuition.
    revert h. rewrite H. simpl. set_iff. intro e.
    set (xs := fvcodom (remove x (fv u)) s). unfold var in e. fold xs in e.
    case_eq (mem x xs); intro i; rewrite i in e.
    absurd (In y (fv u)). rewrite union_subset_1, e. apply var_notin_ok. hyp.
    absurd (x=y). auto. auto.
  Qed.

  Arguments var_notin_fv_subs [x u] s [y] _ _ _.

  Lemma var_notin_fvcod : forall x u s,
    ~In (var x u s) (fvcod (remove x (fv u)) s).

  Proof.
    intros x u s. rewrite In_fvcod. intros [y [h1 h]]. revert h1. set_iff.
    intros [hy n]. eapply var_notin_fv_subs. apply hy. 2: apply h. auto.
  Qed.

  (** Definition of substitution. *)

  Fixpoint subs s (t : Te) :=
    match t with
      | LTerm.Var x => s x
      | LTerm.Fun f => t
      | LTerm.App u v => App (subs s u) (subs s v)
      | LTerm.Lam x u =>
        let x' := var x u s in Lam x' (subs (update x (Var x') s) u)
    end.

  Lemma subs_lam_no_alpha : forall s x u,
    ~In x (fvcodom (remove x (fv u)) s) ->
    subs s (Lam x u) = Lam x (subs (update x (Var x) s) u).

  Proof.
    intros s x u. rewrite not_mem_iff. intro n. simpl.
    unfold var. rewrite n. refl.
  Qed.

  Require Import VecUtil.

  Lemma subs_apps : forall s n (us : Tes n) t,
    subs s (apps t us) = apps (subs s t) (Vmap (subs s) us).

  Proof. intro s. induction us; intro t; simpl. refl. rewrite IHus. refl. Qed.

  (** Composition of two substitutions. *)

  Definition comp s2 s1 (x : X) := subs s2 (s1 x).

  (** [subs] is compatible with substitution equality. *)

  Lemma subs_seq : forall u s s', seq (fv u) s s' -> subs s u = subs s' u.

  Proof.
    induction u; simpl; intros s s' h.
    (* var *)
    apply h. set_iff. refl.
    (* fun *)
    refl.
    (* app *)
    rewrite IHu1 with (s:=s)(s':=s'), IHu2 with (s:=s)(s':=s'). refl.
    intros x hx. apply h. apply union_subset_2. hyp.
    intros x hx. apply h. apply union_subset_1. hyp.
    (* lam *)
    rewrite (var_seq' h). apply (f_equal (Lam (var x u s'))).
    apply IHu. intros y hy. unfold update. eq_dec y x. refl.
    apply h. set_iff. auto.
  Qed.

  Arguments subs_seq [u s s'] _.

  Lemma subs_seq_restrict : forall u s, subs s u = subs (restrict (fv u) s) u.

  Proof. intros u s. apply subs_seq. apply seq_restrict. refl. Qed.

  (** Applying the identity substitution does not change the term
  (extension of CF, Theorem 1a, page 95, proof given on page 97). *)

  Lemma subs_id : forall u, subs id u = u.

  Proof.
    induction u; simpl. refl. refl. rewrite IHu1, IHu2. refl.
    unfold var. rewrite fvcodom_id, empty_b. apply (f_equal (Lam x)).
    rewrite <- IHu at 2. apply subs_seq. intros y hy. unfold update.
    eq_dec y x. rewrite e. refl. refl.
  Qed.

  (** Applying on a term [u] a substitution which domain w.r.t. [fv u]
  is empty does not change the term (CF, Theorem 1b, page 95, proof
  given on page 98). *)

  Lemma subs_notin_fv : forall u s,
    domain (fv u) s [=] empty -> subs s u = u.

  Proof.
    intros u s; rewrite empty_subset; revert u s.
    induction u; simpl; intro s.
    (* var *)
    rewrite singleton_equal_add, domain_add. 2: set_iff; auto.
    rewrite domain_empty. unfold domain_fun, beq_term.
    destruct (eq_term_dec (s x) (Var x)). auto.
    intro h. cut False. tauto. rewrite <- empty_iff, <- h. apply add_1. refl.
    (* fun *)
    refl.
    (* app *)
    intro h. rewrite IHu1, IHu2. refl.
    rewrite (@union_subset_2 (fv u1) (fv u2)). hyp.
    rewrite (@union_subset_1 (fv u1) (fv u2)). hyp.
    (* lam *)
    intro h. unfold var. set (xs := fvcodom (remove x (fv u)) s).
    case_eq (mem x xs); intro hx. rewrite <- mem_iff in hx. unfold xs in hx.
    rewrite In_fvcodom in hx. destruct hx as [z hz]. gen (h z).
    set_iff. intro a. cut False. tauto. apply a. revert hz.
    repeat (rewrite In_domain; set_iff). intuition.
    apply (f_equal (Lam x)). apply IHu. intro y. gen (h y).
    do 2 rewrite In_domain. set_iff. unfold update. eq_dec y x.
    subst y. intuition. intuition.
  Qed.

  (** Free variables of a substituted term. *)

  Lemma fv_subs : forall u s, fv (subs s u)
    [=] let xs := domain (fv u) s in union (diff (fv u) xs) (fvcod xs s).

  Proof.
    induction u; simpl; intro s.

    (* var *)
    rewrite singleton_equal_add, domain_add, domain_empty. 2: fo.
    unfold domain_fun, beq_term. destruct (eq_term_dec (s x) (Var x)).
    rewrite e. simpl. rewrite fvcod_empty. fset.
    rewrite fvcod_add, fvcod_empty. 2: fo. unfold fvcod_fun. fset.

    (* fun *)
    intro y. rewrite domain_empty, fvcod_empty. set_iff. tauto.

    (* app *)
    rewrite IHu1, IHu2. simpl. intro y. set_iff. repeat rewrite In_fvcod.
    repeat rewrite In_domain. set_iff. intuition.
    destruct H as [z hz]. revert hz. rewrite In_domain. intuition.
    right. exists z. rewrite In_domain. set_iff. intuition.
    destruct H as [z hz]. revert hz. rewrite In_domain. intuition.
    right. exists z. rewrite In_domain. set_iff. intuition.
    destruct H0 as [z hz]. revert hz. rewrite In_domain. set_iff. intuition.
    left. right. exists z. rewrite In_domain. intuition.
    right. right. exists z. rewrite In_domain. intuition.

    (* lam *)
    unfold var, fvcodom. set (xs := fvcod (domain (remove x (fv u)) s) s).
    case_eq (mem x xs); [rewrite <- mem_iff|rewrite <- not_mem_iff];
      intro hx; simpl; rewrite IHu; simpl.

    (* In x xs *)
    set (x' := var_notin (union (fv u) xs)).
    gen hx. unfold xs at 1. rewrite In_fvcod. intros [z hz]. revert hz.
    rewrite In_domain. set_iff. intuition.
    intro y. set_iff. repeat rewrite In_domain. rewrite In_fvcod.
    unfold update at 1. eq_dec y x.

    (* y = x *)
    subst y. set_iff. intuition.
    right. exists z. rewrite In_domain. unfold update.
    eq_dec z x. subst z. tauto. tauto.
    apply var_notin_ok with (xs := union (fv u) xs). fold x'. rewrite H.
    apply union_subset_2. hyp.

    (* y <> x *)
    set_iff. intuition.

    destruct H as [a ha]. revert ha. rewrite In_domain. unfold update.
    eq_dec a x; simpl; set_iff. subst a. intuition.
    destruct (In_dec y xs). auto. left.
    absurd (In y xs). hyp. unfold xs. rewrite In_fvcod. exists a.
    rewrite In_domain. set_iff. intuition.

    subst y. absurd (In x' (union (fv u) xs)). apply var_notin_ok.
    apply union_subset_1. hyp.

    revert H4. unfold xs. rewrite In_fvcod. intros [a ha]. revert ha.
    rewrite In_domain. set_iff. intuition. right. exists a. rewrite In_domain.
    unfold update. eq_dec a x. subst a. absurd (x=x); tauto.
    intuition.

    subst y. absurd (In x' (union (fv u) xs)). apply var_notin_ok.
    apply union_subset_2. hyp.

    (* ~In x xs *)
    intro y. set_iff. repeat rewrite In_domain. set_iff.
    rewrite In_fvcod. unfold update. eq_dec y x.

    (* y = x *)
    subst y. intuition.

    (* y <> x *)
    intuition.

    destruct H as [z hz]. revert hz. rewrite In_domain. eq_dec z x.
    subst z. intuition.
    intuition. right. unfold xs. rewrite In_fvcod. exists z.
    rewrite In_domain. set_iff. intuition.

    revert H0. unfold xs. rewrite In_fvcod. intros [z hz]. revert hz.
    rewrite In_domain. set_iff. intuition. right. exists z. rewrite In_domain.
    eq_dec z x. subst z. tauto. intuition.
  Qed.

  Lemma fvcod_subset_fv_subs : forall s u, fvcod (fv u) s [<=] fv (subs s u).

  Proof.
    intros s u. rewrite fv_subs. simpl. intro x. rewrite In_fvcod.
    intros [y [h1 h2]]. set_iff. rewrite In_domain.
    fold (fvcodom (fv u) s). rewrite In_fvcodom.
    destruct (eq_term_dec (s y) (Var y)).
    left. revert h2. rewrite e. simpl. set_iff. intro h2. subst y. tauto.
    right. exists y. tauto.
  Qed.

(****************************************************************************)
(** ** Stability by substitution. *)

  Section stable.

    Require Import RelUtil.

    Definition stable R := Proper (Logic.eq ==> R ==> R) subs.

    Instance stable_same_rel_impl : Proper (same_relation ==> impl) stable.

    Proof.
      intros S T e subs_S s s' ss' t u tu. subst s'. rewrite rel_eq in e.
      rewrite <- e. apply subs_S. refl. rewrite e. hyp.
    Qed.

    Instance stable_same_rel : Proper (same_relation ==> iff) stable.

    Proof. intros S T e. split; intro h. rewrite <- e. hyp. rewrite e. hyp. Qed.

    Lemma stable_union : forall R S, stable R -> stable S -> stable (R U S).

    Proof.
      intros R S subs_R subs_S s s' ss' t u [tu|tu]; subst s'.
      left. apply subs_R; auto. right. apply subs_S; auto.
    Qed.

  End stable.

(****************************************************************************)
(** ** Closure by substitution of a relation on terms.

Note that [clos_subs R] is a priori NOT stable by substitution since
substitution composition is correct modulo alpha-equivalence only
(Lemma [subs_comp] in LAlpha). *)

  Inductive clos_subs (R : relation Te) : relation Te :=
  | s_step : forall x y s, R x y -> clos_subs R (subs s x) (subs s y).

  (** The closure by substitution preserves free variables. *)

  Instance fv_clos_subs : forall R,
    Proper (R --> Subset) fv -> Proper (clos_subs R --> Subset) fv.

  Proof.
    intros R fv_R t u tu. inversion tu; subst; clear tu. rewrite 2!fv_subs.
    simpl. gen (fv_R _ _ H); intro h.
    assert (a : diff (fv y) (domain (fv y) s)
      [<=] diff (fv x) (domain (fv x) s)).
    intro z. set_iff. rewrite 2!In_domain. intuition.
    rewrite a, h. refl.
  Qed.

(****************************************************************************)
(** ** Some equalities on [update]. *)

  Lemma update2_eq : forall x u v w s,
    subs (update x v (update x w s)) u = subs (update x v s) u.

  Proof.
    intros x u v w s. apply subs_seq. intros z hz. unfold update.
    eq_dec z x; refl.
  Qed.

  Lemma update2_neq_com : forall s x u y v w, x <> y ->
    subs (update x u (update y v s)) w = subs (update y v (update x u s)) w.

  Proof.
    intros s x u y v w n. apply subs_seq. intros z hz. unfold update.
    eq_dec z x; eq_dec z y; try refl. subst. tauto.
  Qed.

  Lemma update_single_eq : forall y v w u,
    subs (update y w (single y v)) u = subs (single y w) u.

  Proof. intros y v w u. unfold single at 1. rewrite update2_eq. refl. Qed.

  Lemma update2_single_eq : forall y w x v v' u,
    subs (update y w (update x v' (single x v))) u
    = subs (update y w (single x v')) u.

  Proof.
    intros y w x v v' u. apply subs_seq. intros z hz.
    unfold update at -2. eq_dec z y. refl.
    match goal with |- ?x _ = ?y _ => set (s1:=x); set (s2:=y) end.
    change (subs s1 (Var z) = subs s2 (Var z)). unfold s1, s2.
    rewrite update_single_eq. refl.
  Qed.

  Lemma update_id : forall x s u, s x = Var x ->
    subs (update x (Var x) s) u = subs s u.

  Proof.
    intros x s u h. apply subs_seq. intros z hz. unfold update.
    eq_dec z x. subst. auto. refl.
  Qed.

  Lemma update_id_single : forall y v x u, x<>y \/ v=Var x ->
    subs (update x (Var x) (single y v)) u = subs (single y v) u.

  Proof.
    intros y v x u h. apply subs_seq. intros b hb. unfold single, update.
    eq_dec b x; eq_dec b y.
    subst. destruct h. tauto. subst. refl.
    subst. refl. refl. refl.
  Qed.

(****************************************************************************)
(** ** Some equalities on [single]. *)

  (** CF, Theorem 1a, page 95, proof page 97. *)

  Lemma single_id : forall y u, subs (single y (Var y)) u = u.

  Proof.
    intros y u. rewrite <- subs_id. apply subs_seq. intros x hx.
    unfold single, update. eq_dec x y. subst. refl. refl.
  Qed.

  (** CF, Theorem 1b, page 95, proof page 98. *)

  Lemma single_notin_fv : forall y u v, ~In y (fv v) -> subs (single y u) v = v.

  Proof.
    intros y u v n. rewrite subs_notin_fv. refl. intro x.
    rewrite In_domain. set_iff. unfold single, update, id.
    eq_dec x y. subst x. intuition. intuition.
  Qed.

  (** Other equalities on [single]. *)

  Lemma single_var : forall x u s v z, In z (fv u) -> x <> z ->
    subs (single (var x u s) v) (s z) = s z.

  Proof.
    intros x u s v z h1 h2. rewrite single_notin_fv. refl. unfold var.
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

  Lemma var_single : forall y v x u, var x u (single y v) =
    if mem y (fv u) && negb (eqb x y) && negb (beq_term v (Var y))
      && mem x (fv v) then var_notin (union (fv u) (fv v)) else x.

  Proof.
    intros y v x u. unfold var. rewrite fvcodom_single, remove_b, mem_if.
    case_eq (mem y (fv u) && negb (eqb x y) && negb (beq_term v (Var y)) &&
       mem x (fv v)). repeat rewrite andb_true_iff. intros [[[h1 h2] h3] h4].
    assert (e : fvcodom (remove x (fv u)) (single y v) [=] fv v).
    rewrite fvcodom_single, remove_b, h1, h2, h3. simpl. refl.
    rewrite e. refl. refl.
  Qed.

  Lemma single_lam_no_alpha : forall y v x u,
    ~In y (fv u) \/ x=y \/ v=Var y \/ ~In x (fv v) ->
    subs (single y v) (Lam x u)
    = Lam x (subs (update x (Var x) (single y v)) u).

  Proof.
    intros y v x u. repeat rewrite not_mem_iff.
    rewrite <- eqb_true_iff, <- beq_term_true_iff.
    repeat rewrite <- negb_false_iff. simpl. rewrite var_single.
    intros [h|[h|[h|h]]]; rewrite h; repeat rewrite andb_false_r; refl.
  Qed.

  Lemma fv_single : forall y v u, fv (subs (single y v) u) [=]
    if mem y (fv u) then union (remove y (fv u)) (fv v) else fv u.

  Proof.
    intros y v u. rewrite fv_subs. simpl. rewrite domain_single, fvcod_single.
    case_eq (mem y (fv u)); intro hy; simpl.
    unfold beq_term.
    case (eq_term_dec v (Var y)); intro hv; simpl.
    subst. simpl. rewrite <- mem_iff in hy. rewrite empty_b. fset.
    eq_dec y a; auto. subst. auto.
    rewrite singleton_b, eqb_refl. fset. rewrite empty_b. fset.
  Qed.

(****************************************************************************)
(** ** Some equalities on single renamings. *)

  Definition rename y z := subs (single y (Var z)).

  Lemma rename_id : forall x u, rename x x u = u.

  Proof. apply single_id. Qed.

  Lemma rename_notin_fv : forall x y u, ~In x (fv u) -> rename x y u = u.

  Proof. intros x y u. unfold rename. apply single_notin_fv. Qed.

  Lemma rename_var : forall y z x,
    rename y z (Var x) = Var (if eqb x y then z else x).

  Proof.
    intros y z x. unfold rename, single, update, id, eqb. simpl.
    eq_dec x y; refl.
  Qed.

  Lemma rename_fun : forall x y f, rename x y (Fun f) = Fun f.

  Proof. refl. Qed.

  Lemma rename_app : forall y z u v,
    rename y z (App u v) = App (rename y z u) (rename y z v).

  Proof. refl. Qed.

  Lemma var_rename : forall y z x u, var x u (single y (Var z))
    = if mem y (fv u) && negb (eqb x y) && eqb z x
      then var_notin (add z (fv u)) else x.

  Proof.
    intros y z x u. rewrite var_single, beq_term_var. simpl.
    rewrite singleton_b.
    case_eq (mem y (fv u) && negb (eqb x y) && eqb z x).
    repeat rewrite andb_true_iff. intros [[h1 h2] h3]. rewrite h1, h2, h3.
    simpl. rewrite eqb_true_iff in h3. subst z. rewrite h2. simpl.
    apply var_notin_e. fset.
    repeat rewrite andb_false_iff.
    intros [[h|h]|h]; rewrite h; repeat rewrite andb_false_r; refl.
  Qed.

  Lemma fv_rename : forall y z u, fv (rename y z u)
    [=] if mem y (fv u) then add z (remove y (fv u)) else fv u.

  Proof.
    intros y z u. unfold rename. rewrite fv_single. simpl.
    destruct (mem y (fv u)). fset. refl.
  Qed.

  Lemma rename_lam_no_alpha : forall y z x u,
    ~In y (fv u) \/ x=y \/ x<>z -> rename y z (Lam x u)
    = Lam x (subs (update x (Var x) (single y (Var z))) u).

  Proof.
    intros y z x u h. unfold rename. rewrite single_lam_no_alpha. refl.
    simpl. set_iff. intuition.
  Qed.

  Lemma remove_fv_rename : forall x y u, ~In y (fv u) ->
    remove y (fv (rename x y u)) [=] remove x (fv u).

  Proof.
    intros x y u hy. rewrite fv_rename. case_eq (mem x (fv u)); intro hx.
    apply remove_add. set_iff. tauto.
    rewrite remove_equal. 2: hyp. rewrite remove_equal. refl.
    rewrite mem_iff. rewrite hx. discr.
  Qed.

(****************************************************************************)
(** ** Renamings: substitutions mapping variables to variables. *)

  Definition renaming s := exists m, forall x : X, s x = Var (m x).

  (** Applying a renaming preserves the size. *)

  Lemma size_renaming : forall u s, renaming s -> size (subs s u) = size u.

  Proof.
    induction u; intros s hs; gen hs; intros [m hm]; simpl; auto.
    rewrite hm. refl. unfold var. set (xs := fvcodom (remove x (fv u)) s).
    destruct (mem x xs); simpl; rewrite IHu. refl.
    set (x' := var_notin (union (fv u) xs)).
    exists (fun y => match eq_dec y x with left _ => x' | _ => m y end).
    intro y. unfold update. eq_dec y x. refl. apply hm.
    refl. exists (fun y => match eq_dec y x with left _ => x | _ => m y end).
    intro y. unfold update. eq_dec y x. refl. apply hm.
  Qed.

  (** [rename] is a renaming. *)

  Lemma renaming_update : forall s y z,
    renaming s -> renaming (update y (Var z) s).

  Proof.
    intros s y z [m hm].
    exists (fun x => match eq_dec x y with left _ => z | _ => m x end).
    intro x. unfold update. eq_dec x y. refl. apply hm.
  Qed.

  Lemma renaming_single : forall y z, renaming (single y (Var z)).

  Proof. intros y z. apply renaming_update. exists (fun x => x). refl. Qed.

  Lemma size_rename : forall x y u, size (rename x y u) = size u.

  Proof.
    intros x y u. unfold rename. rewrite size_renaming. refl.
    apply renaming_single.
  Qed.

(****************************************************************************)
(** ** Bound variables. *)

  Fixpoint bv (t : Te) :=
    match t with
      | LTerm.Var _ => empty
      | LTerm.Fun _ => empty
      | LTerm.App u v => union (bv u) (bv v)
      | LTerm.Lam x u => add x (bv u)
    end.

  Lemma bv_rename : forall x y u, ~In y (bv u) -> bv (rename x y u) [=] bv u.

  Proof.
    intros x y. induction u.
    (* var *)
    simpl. intros _. unfold rename. simpl. unfold single, update, id.
    eq_dec x0 x; refl.
    (* fun *)
    refl.
    (* app *)
    rewrite rename_app. simpl. set_iff. intro n.
    rewrite IHu1, IHu2. refl. tauto. tauto.
    (* lam *)
    unfold rename in *. simpl. set_iff. intro n. rewrite var_rename.
    case_eq (mem x (fv u) && negb (eqb x0 x) && eqb x0 y).
    rewrite andb_true_iff, eqb_true_iff. tauto.
    repeat rewrite andb_false_iff. eq_dec x0 x.
    (* x0 = x *)
    subst x0. rewrite eqb_refl. simpl. rewrite andb_false_r. simpl.
    rewrite update_single_eq, single_id. refl.
    (* x0 <> x *)
    rewrite <- eqb_false_iff in n0. rewrite n0. simpl. rewrite andb_true_r.
    assert (e : eqb y x0 = false). rewrite eqb_sym, eqb_false_iff. tauto.
    rewrite e, andb_false_r, update_id, IHu. refl. tauto.
    rewrite single_neq. refl. rewrite <- eqb_false_iff, eqb_sym. hyp.
  Qed.

(****************************************************************************)
(** ** Bound variables of the "codomain" of a substitution:
given a substitution [s] and a finite set [xs], [bvcod s xs] is the
union of the bound variables of [s x] for every [x] in [xs]. It is
defined by iteration of the function [bvcod_fun] on [xs]. *)

  Definition bvcod_fun s (x : X) xs := union (bv (s x)) xs.

  (** [bvcod_fun] is compatible with set equality and commutes with [add]. *)

  Instance bvcod_fun_e : Proper (Logic.eq ==> Logic.eq ==> Equal ==> Equal)
    bvcod_fun.

  Proof.
    intros s s' ss' x x' xx' vs vs' vsvs'. subst s' x'. unfold bvcod_fun.
    rewrite vsvs'. refl.
  Qed.

  Lemma bvcod_fun_transp : forall s, transpose Equal (bvcod_fun s).

  Proof. intros s u v vs. unfold bvcod_fun. fset. Qed.

  Definition bvcod xs s := fold (bvcod_fun s) xs empty.

  (** [bvcod] is compatible with set equality. *)

  Instance bvcod_e : Proper (Equal ==> Logic.eq ==> Equal) bvcod.

  Proof.
    intros xs xs' xsxs' s s' ss'. subst s'. unfold bvcod.
    apply fold_equal. apply Equal_ST. apply bvcod_fun_e. refl. hyp.
  Qed.

  (** Set equalities on [bvcod]. *)

  Lemma bvcod_empty : forall s, bvcod empty s [=] empty.

  Proof. intro s. unfold bvcod. rewrite fold_empty. refl. Qed.

  Lemma bvcod_add : forall s x xs, ~In x xs ->
    bvcod (add x xs) s [=] bvcod_fun s x (bvcod xs s).

  Proof.
    intros s x xs n. unfold bvcod. rewrite fold_add. refl.
    apply Equal_ST. apply bvcod_fun_e. refl. apply bvcod_fun_transp. hyp.
  Qed.

  (** Correctness proof of [bvcod]. *)

  Lemma In_bvcod : forall y s xs,
    In y (bvcod xs s) <-> exists x, In x xs /\ In y (bv (s x)).

  Proof.
    intros y s. apply set_induction_bis.
    (* Equal *)
    intros xs xs' xsxs' h. rewrite <- xsxs', h. clear h.
    intuition; destruct H as [x]; exists x; [rewrite <- xsxs'|rewrite xsxs'];
      hyp.
    (* empty *)
    rewrite bvcod_empty. set_iff. intuition. destruct H as [x].
    revert H. set_iff. intuition.
    (* add *)
    intros x xs n IH. rewrite bvcod_add. 2: hyp. unfold bvcod_fun.
    set_iff. rewrite IH. clear IH. intuition.
    exists x. set_iff. auto.
    destruct H0 as [z]. exists z. set_iff. intuition.
    destruct H as [z]. revert H. set_iff. intuition. subst z. auto.
    right. exists z. auto.
  Qed.

  (** [bvcod] is compatible with inclusion. *)

  Instance bvcod_s : Proper (Subset ==> Logic.eq ==> Subset) bvcod.

  Proof.
    intros xs xs' xsxs' s s' ss' x. subst s'. repeat rewrite In_bvcod.
    intros [a [h1 h2]]. exists a. intuition.
  Qed.

  (** More equalities on [bvcod]. *)

  Lemma bvcod_singleton : forall s x, bvcod (singleton x) s [=] bv (s x).

  Proof.
    intros s x y. split; rewrite In_bvcod.
    intros [z [h1 h2]]. revert h1. set_iff. intro e. subst z. hyp.
    intro h. exists x. set_iff. intuition.
  Qed.

  Lemma bvcod_union : forall s p q,
    bvcod (union p q) s [=] union (bvcod p s) (bvcod q s).

  Proof.
    intros s p q x. rewrite In_bvcod. set_iff. split.
    intros [y [h1 h2]]. revert h1. set_iff. repeat rewrite In_bvcod.
    intros [h1|h1]. left. exists y. intuition. right. exists y. intuition.
    repeat rewrite In_bvcod. intros [[y [h1 h2]]|[y [h1 h2]]].
    exists y. set_iff. intuition. exists y. set_iff. intuition.
  Qed.
 
  Lemma bvcod_single : forall y v xs, bvcod xs (single y v)
    [=] if mem y xs then bv v else empty.

  Proof.
    intros y v. apply set_induction_bis.
    (* Equal *)
    intros s s' ss'. rewrite ss'. auto.
    (* empty *)
    rewrite bvcod_empty, empty_b. refl.
    (* add *)
    intros x u n IH. rewrite bvcod_add, IH. 2: hyp. clear IH.
    unfold bvcod_fun, single, update, id, eqb.
    eq_dec x y; rewrite add_b.
    subst y. rewrite eqb_refl. simpl. rewrite not_mem_iff in n. rewrite n. fset.
    rewrite <- eqb_false_iff in n0. rewrite n0. simpl. fset.
  Qed.

  Lemma bvcod_rename : forall y z xs, bvcod xs (single y (Var z)) [=] empty.

  Proof.
    intros y z xs. rewrite bvcod_single. simpl. destruct (mem y xs); fset.
  Qed.

  Lemma bvcod_id : forall xs, bvcod xs id [=] empty.

  Proof.
    apply set_induction_bis.
    (* Equal *)
    intros xs xs' xsxs' h. rewrite <- xsxs'. hyp.
    (* empty *)
    apply bvcod_empty.
    (* add *)
    intros x xs n IH. rewrite bvcod_add. 2: hyp. unfold bvcod_fun, id. simpl.
    rewrite IH. fset.
  Qed.

  Lemma bvcod_update : forall x u s xs,
    bvcod xs (update x u s) [=]
    union (if mem x xs then bv u else empty) (bvcod (remove x xs) s).

  Proof.
    intros x u s xs y. set_iff. do 2 rewrite In_bvcod. intuition.
    destruct H as [z [h1 h2]]. unfold update in h2. eq_dec z x.
    subst z. rewrite mem_iff in h1. rewrite h1. auto.
    right. exists z. set_iff. auto.
    revert H0. case_eq (mem x xs); intros hx H0. exists x.
    rewrite <- mem_iff in hx. rewrite update_eq. auto.
    revert H0. set_iff. tauto.
    destruct H0 as [z [h1 h2]]. revert h1 h2. set_iff. intros h1 h2.
    exists z. unfold update. eq_dec z x.
    subst z. tauto. tauto.
  Qed.

  (** [bvcod] is compatible with substitution equality. *)

  Lemma bvcod_seq : forall xs xs', xs [=] xs' ->
    forall s s', seq xs s s' -> bvcod xs s [=] bvcod xs' s'.

  Proof.
    intros xs xs' e s s' ss' x. rewrite <- e. repeat rewrite In_bvcod.
    split; intros [y [h1 h2]]; exists y; intuition.
    rewrite <- (ss' _ h1). hyp. rewrite (ss' _ h1). hyp.
  Qed.

  Instance bvcod_seq' : forall xs, Proper (seq xs ==> Equal) (bvcod xs).

  Proof. intros xs s s' ss'. apply bvcod_seq. refl. hyp. Qed.

(****************************************************************************)
(** ** Commutation properties when free variables are distinct from bound variables.

In fact, these properties won't be used later. Instead, we will use similar properties but with another renaming-free substitution function [subs1] defined hereafter, which is equivalent when bound variables are distinct from free variables(Lemma [subs1_no_alpha]) but easier to work with, and whose properties are easier to established. *)

  (** CF, Theorem 1c, page 95, proof page 98. *)

  Lemma single_com : forall x y v w, x<>y -> forall u,
    ~In x (fv w) \/ ~In y (fv u) ->
    inter (bv u) (union (fv v) (fv w)) [=] empty ->
    subs (single y w) (subs (single x v) u)
    = subs (single x (subs (single y w) v)) (subs (single y w) u).

  Proof.
    intros x y v w n. induction u.
    (* var *)
    simpl. set_iff. intros h _. unfold single at 5. unfold update, id.
    eq_dec x0 y. subst x0. rewrite single_notin_fv with (v:=w).
    2: tauto. rewrite single_neq. 2: hyp. simpl. apply single_eq.
    simpl. unfold single at 2. unfold single at 2. unfold update, id.
    eq_dec x0 x. refl. simpl. apply single_neq. auto.
    (* fun *)
    refl.
    (* app *)
    simpl. set_iff. intro h. rewrite union_inter_1, union_empty. intros [a b].
    rewrite IHu1, IHu2; tauto.
    (* lam *)
    simpl fv. simpl bv. set_iff. rewrite inter_empty. intros h1 h2.
    assert (h3 : ~In x0 (union (fv v) (fv w))). apply h2. set_iff. auto.
    revert h3. set_iff. intro h3.
    repeat rewrite single_lam_no_alpha. apply (f_equal (Lam x0)).
    eq_dec x0 x.
    subst. repeat rewrite update_single_eq, single_id; auto.
    eq_dec x0 y.
    subst. repeat rewrite update_single_eq, single_id; auto.
    repeat rewrite update_id_single; auto.
    rewrite single_notin_fv with (v:=v); auto.
    repeat rewrite update_id_single; auto. rewrite IHu. refl. tauto.
    rewrite inter_empty. intros a ha. apply h2. set_iff. auto.

    eq_dec x0 x. auto. eq_dec x0 y.
    subst. rewrite update_single_eq, single_id.
    rewrite single_notin_fv; auto. clear IHu; tauto.
    rewrite update_id_single; auto. repeat rewrite fv_single.
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
    simpl. unfold update, id. eq_dec x y.
    subst y. rewrite single_neq. 2: auto. simpl. sym. apply single_eq.
    unfold single at -2. unfold update, id. sym. eq_dec x x'.
    apply single_notin_fv. hyp. simpl. apply single_neq. auto.
    (* fun *)
    refl.
    (* app *)
    revert h. simpl. rewrite union_inter_1, union_empty. intros [a b].
    rewrite IHu1, IHu2; tauto.
    (* lam *)
    revert h. simpl bv. rewrite inter_empty. intro h.
    assert (hx : ~In x (union (fv v) (fv w))). apply h. set_iff. auto.
    revert hx; set_iff; intro hx.
    assert (~In x (fv v) /\ ~In x (fv w)). tauto. clear hx.
    rewrite subs_lam_no_alpha.

    Focus 2. unfold not. rewrite In_fvcodom. intros [z hz].
    revert hz. set_iff. unfold single, update.
    eq_dec z y; eq_dec z x'.
    subst. subst. tauto. subst. intuition. subst. intuition. intuition.

    Focus 1. repeat rewrite single_lam_no_alpha. 2: tauto. 2: tauto.
    apply (f_equal (Lam x)). eq_dec x' x.
    (* x' = x *)
    subst x'. rewrite update2_neq_com. 2: hyp.
    rewrite update2_single_eq, update_single_eq, single_id.
    apply subs_seq. intros z hz. unfold single, update.
    eq_dec z y; eq_dec z x; try refl.
    subst. subst. tauto.
    (* x' <> x *)
    eq_dec x y.
    (* x = y *)
    subst. rewrite update2_eq, update_id_single. 2: auto.
    rewrite update_single_eq, single_id. refl.
    (* x <> y *)
    rewrite update_id. Focus 2. unfold single, update.
    eq_dec x y; eq_dec x x'; try (subst; tauto).
    Focus 1. rewrite update_id. Focus 2. unfold single, update.
    eq_dec x y; try (subst; tauto).
    Focus 1. rewrite update_id. Focus 2. unfold single, update.
    eq_dec x x'; try (subst; tauto).
    Focus 1. apply IHu. hyp. hyp. intro z. gen (h z). set_iff. tauto.
  Qed.

  Lemma update_single_split_swap : forall u x y v w, x<>y -> ~In x (fv w) ->
    inter (bv u) (union (fv v) (fv w)) [=] empty ->
    subs (update y w (single x v)) u = subs (single x v) (subs (single y w) u).

  Proof.
    induction u; intros x' y v w n hy h.
    (* var *)
    simpl. unfold single at 3. unfold update, id. sym. eq_dec x y.
    apply single_notin_fv. hyp. refl.
    (* fun *)
    refl.
    (* app *)
    revert h. simpl. rewrite union_inter_1, union_empty. intros [a b].
    rewrite IHu1, IHu2; tauto.
    (* lam *)
    revert h. simpl bv. rewrite inter_empty. intro h.
    assert (hx : ~In x (union (fv v) (fv w))). apply h. set_iff. auto.
    revert hx; set_iff; intro hx.
    assert (~In x (fv v) /\ ~In x (fv w)). tauto. clear hx.
    rewrite subs_lam_no_alpha.

    Focus 2. unfold not. rewrite In_fvcodom. intros [z hz].
    revert hz. set_iff. unfold single, update.
    eq_dec z y; eq_dec z x'.
    subst. subst. tauto. subst. intuition. subst. intuition. intuition.

    Focus 1. repeat rewrite single_lam_no_alpha. 2: tauto. 2: tauto.
    apply (f_equal (Lam x)). eq_dec x' x.
    (* x' = x *)
    subst x'. rewrite update2_neq_com. 2: hyp.
    rewrite update2_single_eq, update_single_eq, single_id.
    apply subs_seq. intros z hz. unfold single, update.
    eq_dec z y; eq_dec z x; try refl.
    subst. subst. tauto.
    (* x' <> x *)
    eq_dec x y.
    (* x = y *)
    subst. rewrite update2_eq, update_id_single. 2: auto.
    rewrite update_single_eq, single_id, update_id_single. refl. auto.
    (* x <> y *)
    rewrite update_id. Focus 2. unfold single, update.
    eq_dec x y; eq_dec x x'; try (subst; tauto).
    Focus 1. rewrite update_id. Focus 2. unfold single, update.
    eq_dec x x'; try (subst; tauto).
    Focus 1. rewrite update_id. Focus 2. unfold single, update.
    eq_dec x y; try (subst; tauto).
    Focus 1. apply IHu. hyp. hyp. intro z. gen (h z). set_iff. tauto.
  Qed.

  Lemma subs_lam : forall s x u,
    subs s (Lam x u) = subs (update x (Var x) s) (Lam x u).

  Proof.
    intros s x u. set (s' := update x (Var x) s). simpl.
    set (p := remove x (fv u)).

    assert (h : fvcodom p s [=] fvcodom p s'). intro y.
    repeat rewrite In_fvcodom. split; intros [z [h1 [h2 h3]]].
    exists z. unfold s', update. eq_dec z x.
    subst z. absurd (In x p). unfold p. set_iff. tauto. hyp.
    intuition.
    exists z. revert h2 h3. unfold s', update. eq_dec z x.
    subst z. tauto. tauto.

    assert (e : var x u s = var x u s'). unfold var. fold p.
    rewrite h. destruct (mem x (fvcodom p s')). rewrite h. refl. refl.
    rewrite e. set (x' := var x u s'). unfold s'. rewrite update2_eq. refl.
  Qed.

  Lemma rename_lam : forall x y z u,
    rename x y (Lam z u) =
      if mem x (fv u) && negb (eqb y x) && eqb y z then
        let z' := var_notin (add y (fv u)) in
          Lam z' (subs (update z (Var z') (single x (Var y))) u)
        else if eqb z x then Lam z u else Lam z (rename x y u).

  Proof.
    intros x y z u. unfold rename at 1. simpl. rewrite var_single, beq_term_var.
    simpl. rewrite singleton_b.
    case_eq (mem x (fv u) && negb (eqb z x) && negb (eqb y x) && eqb y z).
    repeat rewrite andb_true_iff. intros [[[h1 h2] h3] h4].
    rewrite h1, h3, h4. simpl. rewrite union_sym, <- add_union_singleton. refl.
    repeat rewrite andb_false_iff. intros [[[h|h]|h]|h].
    rewrite h. simpl. unfold eqb. eq_dec z x.
    subst z. rewrite update_single_eq, single_id. refl.
    rewrite update_id_single. 2: auto. refl.
    revert h. rewrite negb_false_iff, eqb_true_iff. intro h. subst z.
    rewrite update_single_eq, single_id.
    rewrite <- andb_assoc, andb_comm with (b2:=eqb y x), andb_negb_r,
      andb_false_r, eqb_refl. refl.
    rewrite h. rewrite andb_false_r. simpl. unfold eqb. eq_dec z x.
    subst z. rewrite update_single_eq, single_id. refl.
    rewrite update_id_single. 2: auto.
    revert h. rewrite negb_false_iff, eqb_true_iff. intro h. subst y.
    rewrite single_id, rename_id. refl.
    rewrite h. repeat rewrite andb_false_r. unfold eqb. eq_dec z x.
    subst z. rewrite update_single_eq, single_id. refl.
    rewrite update_id_single. 2: auto. refl.
  Qed.

  Lemma rename_subs_com : forall x y,
    forall u s, s x = Var x -> s y = Var y -> ~In x (fvcodom (fv u) s) ->
      inter (bv u) (add y (fvcodom (fv u) s)) [=] empty ->
      rename x y (subs s u) = subs s (rename x y u).

  Proof.
    intros x y. induction u; intros s hx hy.
    (* var *)
    rename x0 into z. simpl. rewrite fvcodom_singleton, rename_var.
    unfold beq_term. destruct (eq_term_dec (s z) (Var z)).
    rewrite e, rename_var. unfold eqb. eq_dec z x; auto.
    intro h. unfold rename. rewrite single_notin_fv. 2: hyp.
    unfold eqb. eq_dec z x; simpl.
    subst z. tauto. refl.
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
    rename x0 into z. simpl bv. intros h1 h2.
    rewrite rename_lam. case_eq (mem x (fv u) && negb (eqb y x) && eqb y z).
    (* In x (fv u) /\ y <> x /\ y = z *)
    repeat rewrite andb_true_iff. rewrite eqb_true_iff. intros [[i1 i2] i3].
    subst z. revert h2. rewrite add_union_singleton, union_inter_1,
      union_empty, singleton_equal_add, inter_add_1, inter_empty_l.
    intros [h _]. gen (h y). set_iff. tauto. set_iff. auto.
    (* ~In x (fv u) \/ y = x \/ y <> z *)
    repeat rewrite andb_false_iff. intros [[i|i]|i].
    (* 1. ~In x (fv u) *)
    unfold eqb. eq_dec z x.
    (* z = x *)
    subst. apply rename_notin_fv. rewrite fv_subs. simpl in *. set_iff. tauto.
    (* z <> x *)
    rewrite rename_notin_fv with (u:=u). 2: rewrite not_mem_iff; hyp.
    apply rename_notin_fv. rewrite fv_subs. simpl in *. set_iff.
    unfold fvcodom in h1. rewrite <- not_mem_iff in i. intuition.
    (* 2. y = x *)
    revert i. rewrite negb_false_iff, eqb_true_iff. intro i. subst y.
    repeat rewrite rename_id. unfold eqb. eq_dec z x; refl.
    (* 3. y <> z *)
    unfold eqb. eq_dec z x.
    subst. apply rename_notin_fv. rewrite fv_subs. simpl in *. set_iff. tauto.
    repeat rewrite subs_lam_no_alpha. set (s' := update z (Var z) s).
    rewrite <- IHu. rewrite rename_lam, i. repeat rewrite andb_false_r.
    rewrite <- eqb_false_iff in n. rewrite n. refl.

    unfold s', update. eq_dec x z. subst. refl. hyp.
    unfold s', update. eq_dec y z. subst. refl. hyp.

    rewrite In_fvcodom. intros [b [j1 [j2 j3]]]. apply h1. rewrite In_fvcodom.
    exists b. simpl. set_iff. revert j2 j3. unfold s', update.
    eq_dec b z. subst. tauto. intuition.

    assert (e : fvcodom (fv u) s' [=] fvcodom (fv (Lam z u)) s). intro a.
    repeat rewrite In_fvcodom. split; intros [b [j1 [j2 j3]]]; exists b;
      simpl in *; revert j1 j2 j3; set_iff; unfold s', update; eq_dec b z.
    subst. tauto. intuition. subst. intuition. intuition.

    rewrite e. revert h2. repeat rewrite empty_subset.
    rewrite add_union_singleton. intro h2.
    rewrite union_subset_2 with (s:=singleton z) (s':=bv u). hyp.

    assert (e : fvcodom (remove z (fv (rename x y u))) s
      [=] fvcodom (fv (Lam z u)) s). intro a.
    repeat rewrite In_fvcodom. split; intros [b [j1 [j2 j3]]]; exists b;
      revert j1 j2 j3; set_iff; rewrite fv_rename; case_eq (mem x (fv u));
        simpl; set_iff; intuition.
    subst b. revert H2. rewrite hy. simpl. set_iff. intro e. subst a. tauto.
    right. intuition. subst b. tauto.

    rewrite e. rewrite inter_empty in h2. gen (h2 z). set_iff. tauto.
    rewrite inter_empty in h2. gen (h2 z). set_iff. tauto.
  Qed.

(****************************************************************************)
(** ** [subs1]: substitution with variable capture. *)

  Fixpoint subs1 s (t : Te) :=
    match t with
      | LTerm.Var x => s x
      | LTerm.Fun f => t
      | LTerm.App u v => App (subs1 s u) (subs1 s v)
      | LTerm.Lam x u => Lam x (subs1 (update x (Var x) s) u)
    end.

  Definition comp1 s2 s1 (x:X) := subs1 s2 (s1 x).

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
    repeat rewrite union_inter_1. repeat rewrite union_empty. intuition.
    rewrite IHu1, IHu2; try rewrite inter_sym; auto.
    (* lam *)
    rewrite inter_empty. intro h1.
    assert (i : mem x (fvcodom (remove x (fv u)) s) = false).
    rewrite <- not_mem_iff. apply h1. set_iff. auto.
    assert (j : var x u s = x). unfold var. rewrite i. refl.
    rewrite j, IHu. refl. rewrite empty_subset. intro y. set_iff.
    intros [i1 i2]. eapply h1. set_iff. right. apply i1.
    rewrite <- fvcodom_update_id. hyp.
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
    refl. intros y hy. unfold update. eq_dec y x. refl.
    apply h. set_iff. auto.
  Qed.

  (** Other properties of [subs1]. *)

  Lemma subs1_update2_eq : forall x u v w s,
    subs1 (update x v (update x w s)) u = subs1 (update x v s) u.

  Proof.
    intros x u v w s. apply subs1_seq. intros z hz. unfold update.
    eq_dec z x; refl.
  Qed.

  Lemma subs1_update2_neq_com : forall s x u y v w, x <> y ->
    subs1 (update x u (update y v s)) w = subs1 (update y v (update x u s)) w.

  Proof.
    intros s x u y v w n. apply subs1_seq. intros z hz. unfold update.
    eq_dec z x; eq_dec z y; try refl. subst. tauto.
  Qed.

  Lemma subs1_update_single_eq : forall y v w u,
    subs1 (update y w (single y v)) u = subs1 (single y w) u.

  Proof.
    intros y v w u. apply subs1_seq. intros b hb. unfold single, update.
    eq_dec b y; refl.
  Qed.

  Lemma subs1_update2_single_eq : forall y w x v v' u,
    subs1 (update y w (update x v' (single x v))) u
    = subs1 (update y w (single x v')) u.

  Proof.
    intros y w x v v' u. apply subs1_seq. intros z hz.
    unfold update at -2. eq_dec z y. refl.
    match goal with |- ?x _ = ?y _ => set (s1:=x); set (s2:=y) end.
    change (subs s1 (Var z) = subs s2 (Var z)). unfold s1, s2.
    rewrite update_single_eq. refl.
  Qed.

  Lemma subs1_update_id : forall x s u, s x = Var x ->
    subs1 (update x (Var x) s) u = subs1 s u.

  Proof.
    intros x s u h. apply subs1_seq. intros z hz. unfold update.
    eq_dec z x. subst. auto. refl.
  Qed.

  Lemma subs1_id : forall u, subs1 id u = u.

  Proof.
    induction u; simpl; auto. rewrite IHu1, IHu2. refl.
    apply (f_equal (Lam x)). rewrite subs1_update_id. hyp. refl.
  Qed.

  Lemma subs1_single_id : forall y u, subs1 (single y (Var y)) u = u.

  Proof.
    intros y u. rewrite <- subs1_id. apply subs1_seq. intros x hx.
    unfold single, update. eq_dec x y. subst. refl. refl.
  Qed.
 
  Lemma subs1_update_id_single : forall y v x u, x<>y \/ v=Var x ->
    subs1 (update x (Var x) (single y v)) u = subs1 (single y v) u.

  Proof.
    intros y v x u h. apply subs1_seq. intros b hb. unfold single, update.
    eq_dec b x; eq_dec b y.
    subst. destruct h. tauto. subst. refl.
    subst. refl. refl. refl.
  Qed.

  Lemma subs1_update_single_id : forall y v x u,
    subs1 (update y v (single x (Var x))) u = subs1 (single y v) u.

  Proof.
    intros y v x u. apply subs1_seq. intros z hz. unfold single, update at -2.
    eq_dec z y. refl. unfold update, id. eq_dec z x.
    subst z. refl. refl.
  Qed.

  (** Composition properties of [subs1]. *)

  Lemma subs1_update_single : forall x y y' u s, ~In y (bv u) ->
    subs1 (update y (Var y') s) (subs1 (single x (Var y)) u)
    = subs1 (update x (Var y') (update y (Var y') s)) u.

  Proof.
    intros x y y'. induction u; intro s; simpl; set_iff; intro hy.
    (* var *)
    rename x0 into z. unfold single. unfold update at -1.
    eq_dec z x; simpl.
    rewrite update_eq. refl.
    unfold update. eq_dec z y; refl.
    (* fun *)
    refl.
    (* app *)
    rewrite IHu1, IHu2; auto.
    (* lam *)
    rename x0 into z. apply (f_equal (Lam z)). eq_dec z x.
    (* z = x *)
    subst z. rewrite subs1_update2_eq, subs1_update_single_eq, subs1_single_id.
    refl.
    (* z <> x *)
    rewrite subs1_update2_neq_com. 2: tauto.
    rewrite subs1_update_id_single. 2: tauto.
    rewrite IHu; auto. apply subs1_seq. intros a ha. unfold update.
    eq_dec a x; eq_dec a y; eq_dec a z;
      try subst a; try subst x; try subst y; tauto.
  Qed.

  Lemma subs1_single_subs1 : forall y v u s, s y = Var y ->
    ~In y (fvcodom (fv u) s) ->
    subs1 (single y v) (subs1 s u) = subs1 (update y v s) u.

  Proof.
    intros y v. induction u; intros s h1; simpl.
    (* var *)
    rewrite fvcodom_singleton. unfold beq_term.
    destruct (eq_term_dec (s x) (Var x)).
    rewrite e. simpl. unfold single, update, id. eq_dec x y; auto.
    intro h2. rewrite subs1_notin_fv. unfold update. eq_dec x y.
    subst y. tauto. refl.
    rewrite empty_subset. intro a. rewrite In_domain.
    unfold single, update, id. eq_dec a y. subst a. tauto. tauto.
    (* fun *)
    refl.
    (* app *)
    rewrite fvcodom_union. set_iff. intro h2. rewrite IHu1, IHu2; auto.
    (* lam *)
    intro h2. apply (f_equal (Lam x)). unfold single. eq_dec x y.
    subst y. repeat rewrite subs1_update2_eq.
    repeat rewrite subs1_update_id; auto. apply subs1_id.
    rewrite subs1_update_id. 2: unfold update; eq_dec x y; tauto.
    fold (single y v). rewrite IHu, subs1_update2_neq_com. refl. auto.
    unfold update. eq_dec y x. subst y. tauto. hyp.
    rewrite fvcodom_update_id. hyp.
  Qed.

  Lemma subs1_single_update : forall x x' y' u s, ~In x' (fv u) ->
    ~In x' (fvcodom (remove x (fv u)) s) -> ~In x' (bv u) -> ~In x (bv u) ->
    subs1 (single x' (Var y')) (subs1 (update x (Var x') s) u)
    = subs1 (update x' (Var y') (update x (Var y') s)) u.

  Proof.
    intros x x' y'. induction u; intro s; simpl; set_iff; intros h1 h2 h3 h4.
    (* var *)
    rename x0 into z. unfold update.
    eq_dec z x; eq_dec z x'; simpl.
    unfold single. rewrite update_eq. refl.
    unfold single. rewrite update_eq. refl.
    tauto.
    rewrite subs1_notin_fv. refl. rewrite domain_single, beq_term_var.
    case_eq (mem x' (fv (s z)) && negb (eqb y' x')). 2: refl.
    rewrite andb_true_iff, negb_true_iff, eqb_false_iff, <- mem_iff.
    intros [i1 i2]. absurd (In x' (fvcodom (remove x (singleton z)) s)). hyp.
    rewrite In_fvcodom. exists z. set_iff. intuition.
    revert i1. rewrite H. simpl. set_iff. hyp.
    (* fun *)
    refl.
    (* app *)
    revert h2. rewrite remove_union, fvcodom_union. set_iff. intro h2.
    rewrite IHu1, IHu2; auto.
    (* lam *)
    rename x0 into z. apply (f_equal (Lam z)). eq_dec z x'. tauto.
    rewrite subs1_update2_neq_com with (y:=x'). 2: tauto.
    rewrite subs1_update_id_single. 2: tauto. eq_dec z x. tauto.
    rewrite subs1_update2_neq_com. 2: tauto. rewrite IHu; auto.
    Focus 2. rewrite In_fvcodom. intros [a [i1 [i2 i3]]]. revert i1 i2 i3.
    unfold update. eq_dec a z; simpl; set_iff. tauto.
    intros [i0 i1] i2 i3. apply h2. rewrite In_fvcodom. exists a. set_iff.
    intuition.
    Focus 1. apply subs1_seq. intros a ha. unfold update.
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
    apply (f_equal (Lam x)). rewrite IHu. apply subs1_seq.
    intros y hy. unfold comp1 at 1. unfold update at -1.
    eq_dec y x; simpl. apply update_eq.
    unfold comp1. apply subs1_seq. intros z hz. unfold update.
    eq_dec z x. 2: refl. subst z. sym.

    rewrite inter_empty in h. simpl in h.
    absurd (In x (fvcodom (remove x (fv u)) s1)). apply h. set_iff. auto.
    rewrite In_fvcodom. exists y. set_iff. intuition.
    revert hz. rewrite H. simpl. set_iff. hyp.

    revert h. do 2 rewrite inter_empty. simpl. intros h y hy.
    rewrite In_fvcodom. intros [z [i1 [i2 i3]]]. revert i2 i3. unfold update.
    eq_dec z x. subst z. tauto. intros i2 i3.
    eapply h. set_iff. right. apply hy. rewrite In_fvcodom. exists z.
    set_iff. intuition.
  Qed.

End Make.
