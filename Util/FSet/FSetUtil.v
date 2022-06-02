(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2008-02-22

* Lemmas and tactics extending Coq's library FSet.
*)

Set Implicit Arguments.

From Coq Require Import FSets.
From CoLoR Require Import LogicUtil RelUtil BoolUtil.

Create HintDb ordered_type.

Module Make (Export XSet : FSetInterface.S).

  Module Export XSetEqProps := EqProperties XSet.
  Module Export XSetProps := Properties XSet.
  Module Export XSetFacts := Facts XSet.
  Module Export XSetOrdProps := OrdProperties XSet.

  Infix "[=]" := Equal (at level 70, no associativity).
  Infix "[<=]" := Subset (at level 70, no associativity).

  Arguments remove_1 [s x y] _ _.
  Arguments remove_3 [s x y] _.
  Arguments singleton_1 [x y] _.
  Arguments union_1 [s s' x] _.

  Ltac eq_dec x y := unfold eqb; destruct (P.FM.eq_dec x y).

(***********************************************************************)
(** database of Equal-ity lemmas. *)

  Global Hint Rewrite union_assoc inter_assoc diff_inter_empty diff_inter_all : Equal.
  Global Hint Rewrite <- add_union_singleton : Equal.

  Ltac Equal := autorewrite with Equal.

(***********************************************************************)
(** database of equality lemmas on [mem]. *)

  Global Hint Rewrite empty_b singleton_b remove_b add_b union_b inter_b diff_b
    : mem.

  Ltac mem := autorewrite with mem.

(***********************************************************************)
(** Tactic putting a set built from intersections and unions into a
"disjunctive normal form", i.e. a union of intersections. *)

  Ltac dnf := repeat
    match goal with
      | |- context [inter (union ?a _) _] => rewrite union_inter_1 with (s:=a)
      | |- context [inter ?a (union _ _)] =>
        rewrite inter_sym with (s:=a), union_inter_1 with (s'':=a)
    end.

(***********************************************************************)
(** Tactic for proving simple membership propositions. *)

  Ltac fset := intro; set_iff; tauto.

(***********************************************************************)
(** boolean equality on [X] *)

  Lemma eqb_ok x y : eqb x y = true <-> E.eq x y.

  Proof. eq_dec x y; intuition. discr. Qed.

  Lemma eqb_refl x : eqb x x = true.

  Proof. eq_dec x x. refl. absurd (x=x); auto with ordered_type. Qed.

  Global Hint Rewrite eqb_refl : mem.

  Lemma eqb_sym : forall x y, eqb x y = eqb y x.

  Proof. intros x y. apply eqb_equiv. rewrite !eqb_ok. firstorder auto with crelations. Qed.

(***********************************************************************)
(** empty *)

  Lemma is_empty_eq s : is_empty s = true <-> s [=] empty.

  Proof.
    split; intro hs.
    apply empty_is_empty_1. rewrite is_empty_iff. hyp.
    rewrite <- is_empty_iff. apply empty_is_empty_2. hyp.
  Qed.

  Lemma mem_is_empty {x s} : mem x s = true -> is_empty s = false.

  Proof.
    rewrite false_not_true. unfold not. rewrite <- is_empty_iff, <- mem_iff.
    fo.
  Qed.

  Lemma subset_empty s : s [<=] empty -> s [=] empty.

  Proof. intro hs. rewrite double_inclusion. intuition. Qed.

  Lemma empty_subset s : s [=] empty <-> s [<=] empty.

  Proof. intuition. Qed.

(***********************************************************************)
(** remove *)

(*REMOVE?
  Lemma In_remove y x xs : ~E.eq y x -> In y xs -> In y (remove x xs).

  Proof. intros n hy. apply remove_2; fo. Qed.*)

  Lemma In_remove_neq x y s : In x (remove y s) -> ~E.eq y x.

  Proof. set_iff. tauto. Qed.

  Lemma remove_3 x y s : In x (remove y s) -> In x s /\ ~E.eq y x.

  Proof. set_iff. tauto. Qed.

  Lemma remove_singleton x : remove x (singleton x) [=] empty.

  Proof. fset. Qed.

  Global Hint Rewrite remove_singleton : Equal.

  Lemma remove_union x s s' :
    remove x (union s s') [=] union (remove x s) (remove x s').

  Proof. fset. Qed.

  Global Hint Rewrite remove_union : Equal.

  Lemma remove_empty x : remove x empty [=] empty.

  Proof. fset. Qed.

  Global Hint Rewrite remove_empty : Equal.

  Lemma remove_com x y s : remove x (remove y s) [=] remove y (remove x s).

  Proof. fset. Qed.

  Lemma remove_add_com x y s : ~E.eq x y ->
    add x (remove y s) [=] remove y (add x s).

  Proof. intros n z. set_iff. fo. intro n'. apply n. trans z; hyp. Qed.

  Lemma remove_add_eq x xs : remove x (add x xs) [=] remove x xs.

  Proof. fset. Qed.

  Global Hint Rewrite remove_add_eq : Equal.

  Lemma remove_idem x xs : remove x (remove x xs) [=] remove x xs.

  Proof. fset. Qed.

  Global Hint Rewrite remove_idem : Equal.

  Lemma remove_add_if x y xs : remove y (add x xs)
    [=] if eqb y x then remove y xs else add x (remove y xs).

  Proof.
    eq_dec y x. rewrite e at 1. rewrite remove_add_eq, e. refl.
    intro; set_iff; intuition. apply n. rewrite H, H0. refl.
  Qed.

  Lemma remove_inter x ys zs :
    remove x (inter ys zs) [=] inter (remove x ys) (remove x zs).

  Proof. fset. Qed.

(***********************************************************************)
(** Subset *)

  Lemma Subset_antisym s t : s [=] t <-> (s [<=] t /\ t [<=] s).

  Proof. intuition. Qed.

(***********************************************************************)
(** ~In *)

  Lemma notin_union x s s' : ~In x (union s s') <-> ~In x s /\ ~In x s'.

  Proof. set_iff. tauto. Qed.

  Lemma notin_singleton x y : ~In x (singleton y) <-> ~E.eq y x.

  Proof. set_iff. refl. Qed.

  Ltac notIn_elim := repeat
    match goal with
      | H : ~In _ (union _ _) |- _ => rewrite notin_union in H; destruct H
      | H : ~In _ (singleton _) |- _ => rewrite notin_singleton in H
    end.

(***********************************************************************)
(** union *)

  Lemma union_empty_l s : union empty s [=] s.

  Proof. fset. Qed.

  Global Hint Rewrite union_empty_l : Equal.

  Lemma union_empty_r s : union s empty [=] s.

  Proof. fset. Qed.

  Global Hint Rewrite union_empty_r : Equal.

  Lemma union_idem s : union s s [=] s.

  Proof. fset. Qed.

  Global Hint Rewrite union_idem : Equal.

  Lemma union_idem_1 s t : union s (union s t) [=] union s t.

  Proof. fset. Qed.

  Global Hint Rewrite union_idem_1 : Equal.

  Lemma union_idem_2 s t u :
    union s (union t (union s u)) [=] union s (union t u).

  Proof. fset. Qed.

  Global Hint Rewrite union_idem_2 : Equal.

  Lemma union_idem_3 s t u :
    union (union s t) (union s u) [=] union s (union t u).

  Proof. fset. Qed.

  Global Hint Rewrite union_idem_3 : Equal.

  Lemma union_sym_2 s t u : union s (union t u) [=] union t (union s u).

  Proof. fset. Qed.

  Lemma union_empty a b :
    union a b [=] empty <-> a [=] empty /\ b [=] empty.

  Proof.
    rewrite !empty_subset. split; intro h.
    split; trans (union a b).
    apply union_subset_1. hyp. apply union_subset_2. hyp.
    apply union_subset_3; tauto.
  Qed.

  Lemma union_empty_subset a b :
    union a b [<=] empty <-> (a [<=] empty /\ b [<=] empty).

  Proof. rewrite <- !empty_subset. apply union_empty. Qed.

(***********************************************************************)
(** difference *)

  Lemma diff_union s t u :
    diff (union s t) u  [=] union (diff s u) (diff t u).

  Proof. fset. Qed.

  Lemma diff_empty_r s : diff s empty [=] s.

  Proof. fset. Qed.

  Global Hint Rewrite diff_empty_r : Equal.

  Lemma diff_empty_l s : diff empty s [=] empty.

  Proof. fset. Qed.

  Global Hint Rewrite diff_empty_l : Equal.

  Lemma remove_diff_singleton x s : remove x s [=] diff s (singleton x).

  Proof. fset. Qed.

  Global Hint Rewrite <- remove_diff_singleton : Equal.

(***********************************************************************)
(** intersection *)

  Lemma inter_empty_l a : inter empty a [=] empty.

  Proof. fset. Qed.

  Lemma inter_empty_r a : inter a empty [=] empty.

  Proof. fset. Qed.

  Lemma inter_empty a b :
    inter a b [=] empty <-> (forall x, In x a -> ~In x b). 

  Proof.
    split; intro h.
    intros x h1 h2. rewrite <- empty_iff with (x:=x), <- h. apply inter_3; hyp.
    intro x. set_iff. fo.
  Qed.

(***********************************************************************)
(** some equivalences *)

  Lemma mem_In x s : mem x s = true <-> In x s.

  Proof. intuition. Qed.

  Lemma subset_Subset s t : subset s t = true <-> Subset s t.

  Proof. intuition. Qed.

  Lemma equal_Equal s t : equal s t = true <-> Equal s t.

  Proof. intuition. Qed.

  Lemma rel_equal_Equal : rel_of_bool equal == Equal.

  Proof. apply rel_eq. apply equal_Equal. Qed.

  Lemma mem_if x xs (b : bool) :
    mem x (if b then xs else empty) = b && mem x xs.

  Proof. destruct b; simpl. refl. rewrite empty_b. refl. Qed.

(***********************************************************************)
(** Compatibility of set operations wrt inclusion. *)

  Global Instance add_s : Proper (E.eq ==> Subset ==> Subset) add.

  Proof. intros x y xy s t st z. rewrite xy, st. auto. Qed.

  Global Instance inter_s : Proper (Subset ==> Subset ==> Subset) inter.

  Proof. intros a a' aa' b b' bb' x. set_iff. rewrite aa', bb'. auto. Qed.

  Global Instance union_s : Proper (Subset ==> Subset ==> Subset) union.

  Proof. intros a a' aa' b b' bb' x. set_iff. rewrite aa', bb'. auto. Qed.

  Global Instance diff_s : Proper (Subset ==> Subset --> Subset) diff.

  Proof. intros a a' aa' b b' b'b x. set_iff. rewrite aa', b'b. auto. Qed.

(***********************************************************************)
(** Monotony properties of [max_elt]. *)

  Inductive le_opt : relation (option E.t) :=
  | le_opt_1 : le_opt None None
  | le_opt_2 : forall x, le_opt None (Some x)
  | le_opt_3 : forall x y, E.lt x y \/ E.eq x y -> le_opt (Some x) (Some y).

  Global Instance max_elt_s : Proper (Subset ==> le_opt) max_elt.

  Proof.
    intros A B AB. case_eq (max_elt A).
    intros a amA. gen (max_elt_1 amA). intro aA. apply AB in aA.
    case_eq (max_elt B).
    intros b bmB. apply le_opt_3. gen (max_elt_2 bmB aA).
    intro n. destruct (E.compare a b); fo.
    intro Be. exfalso. gen (max_elt_3 Be). fo.
    intro Ae. case_eq (max_elt B).
    intros b bmB. apply le_opt_2.
    intro Be. apply le_opt_1.
  Qed.

  Global Instance max_elt_e : Proper (Equal ==> opt_r E.eq) max_elt.

  Proof.
    intros A B e. assert (AB : Subset A B). rewrite e. refl.
    assert (BA : Subset B A). rewrite e. refl.
    gen (max_elt_s AB); intro h; inversion h; clear h.
    apply opt_r_None.
    gen (max_elt_s BA); intro h; inversion h; clear h.
    rewrite <- H in H2. discr. rewrite <- H in H2. discr.
    rewrite <- H0 in H2. discr. apply opt_r_Some.
    gen (max_elt_s BA); intro h; inversion h; clear h.
    rewrite <- H in H4. discr. rewrite <- H0 in H3. discr.
    rewrite <- H in H3. inversion H3; clear H3.
    rewrite <- H0 in H2. inversion H2; clear H2. subst.
    symmetry in H. symmetry in H0.
    gen (max_elt_1 H). rewrite e. intro xB. gen (max_elt_2 H0 xB).
    gen (max_elt_1 H0). rewrite <- e. intro yA. gen (max_elt_2 H yA).
    intuition.
  Qed.

(***********************************************************************)
(** fold *)

  Section fold.

    Variables (A : Type) (eqA : relation A) (heqA : Equivalence eqA).

    Definition feq f f' :=
      forall x x', E.eq x x' -> forall a a', eqA a a' -> eqA (f x a) (f' x' a').

    Global Instance feq_Sym : Symmetric eqA -> Symmetric feq.

    Proof. firstorder auto with crelations. Qed.

    Global Instance Proper_m' :
      Proper (feq ==> impl) (Proper (E.eq ==> eqA ==> eqA)).

    Proof.
      intros f f' ff' fm x x' xx' a a' aa'. trans (f x a).
      sym. apply ff'; refl. apply ff'; hyp.
    Qed.

    Global Instance transpose_feq' : Proper (feq ==> impl) (transpose eqA).

    Proof.
      intros f f' ff' hf x y z. trans (f x (f y z)).
      sym. apply ff'. refl. apply ff'; refl.
      rewrite hf. apply ff'. refl. apply ff'; refl.
    Qed.

    Global Instance fold_m f : Proper (E.eq ==> eqA ==> eqA) f ->
      Proper (Equal ==> eqA ==> eqA) (fold f).

    Proof.
      intros f_m s s' ss' a a' aa'. trans (fold f s' a).
      apply fold_equal; hyp. apply fold_init; hyp.
    Qed.

    Lemma fold_m_ext f : Proper (E.eq ==> eqA ==> eqA) f ->
      transpose eqA f ->
      forall f', feq f f' -> forall s s', s [=] s' -> forall a a', eqA a a' ->
        eqA (fold f s a) (fold f' s' a').

    Proof.
      intros fm ft f' ff' s s' ss' a a' aa'; revert s' ss' a a' aa'.
      pattern s; apply set_induction_bis; clear s.
      (* Equal *)
      intros s s' ss' h t s't a a' aa'. trans (fold f s a).
      apply fold_equal; auto. hyp. apply h. trans s'; hyp. hyp.
      (* empty *)
      intros s' e a a' aa'. trans (fold f' empty a').
      rewrite 2!fold_empty. hyp.
      apply fold_m; try hyp||refl. rewrite <- ff'. hyp.
      (* add *)
      intros x s nxs h s' e a a' aa'. trans (fold f' (add x s) a').
      rewrite 2!fold_add; unfold compat_op; try rewrite <- ff'; auto.
      apply ff'. refl. apply h. refl. hyp.
      apply fold_m; auto. rewrite <- ff'. hyp. refl.
    Qed.

  End fold.

(***********************************************************************)
(** replace *)

  Definition replace y z xs :=
    if mem y xs then add z (remove y xs) else xs.

  Global Instance replace_Subset :
    Proper (E.eq ==> E.eq ==> Subset ==> Subset) replace.

  Proof.
    intros y y' yy' z z' zz' xs xs' xsxs'. unfold replace.
    rewrite <- yy'. case_eq (mem y xs); intro hy.
    assert (hy' : mem y xs' = true).
    rewrite <- mem_iff. apply xsxs'. rewrite mem_iff. hyp.
    rewrite hy'. intro a. set_iff. rewrite <- zz', <- yy'. fo.
    case_eq (mem y xs'); intro hy'. 2: hyp.
    intros a ha. set_iff. rewrite <- zz', <- yy'. eq_dec z a. auto.
    right. split. fo. intro ya. rewrite ya, <- not_mem_iff in hy. contr.
  Qed.

  Global Instance replace_Equal :
    Proper (Logic.eq ==> Logic.eq ==> Equal ==> Equal) replace.

  Proof.
    intros y' y y'y z' z z'z xs' xs e; subst; unfold replace.
    rewrite e. destruct (mem y xs); rewrite e; refl.
  Qed.

  Lemma notin_replace x y xs : E.eq y x \/ ~In x (replace x y xs).

  Proof with auto with ordered_type.
    eq_dec y x... unfold replace. case_eq (mem x xs); intro hx; set_iff.
    right. split_all... right. rewrite not_mem_iff. hyp.
  Qed.

  Lemma replace_idem x xs : replace x x xs [=] xs.

  Proof.
    unfold replace. case_eq (mem x xs); intro hx. 2: refl.
    rewrite <- mem_iff in hx. intro a. set_iff. split_all.
    rewrite <- H. hyp. eq_dec x a; auto.
  Qed.

  Lemma replace2 x y z xs :
    x = y \/ ~In y xs -> replace y z (replace x y xs) [=] replace x z xs.

  Proof.
    intros [h|h]. subst. rewrite replace_idem. refl.
    unfold replace at -1. case_eq (mem x xs); intro hx.
    unfold replace. rewrite add_b, eqb_refl; simpl. rewrite remove_add_eq.
    eq_dec x y. (*SLOW:rewrite <- e, remove_idem. refl.*)
    apply add_m. refl. rewrite <- e, remove_idem. refl.
    rewrite remove_com, remove_equal with (x:=y). refl. hyp.
    unfold replace. rewrite not_mem_iff in h. rewrite h. refl.
  Qed.

End Make.
