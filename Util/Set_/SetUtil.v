(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTSGHTS and LICENSE files.

- Frederic Blanqui, 2009-06-26

* Potentially infinite sets
*)

Set Implicit Arguments.

From Stdlib Require Import Basics Morphisms Setoid.
From CoLoR Require Import LogicUtil RelUtil FunUtil ListUtil NatUtil
     ClassicUtil BoundNat.

(****************************************************************************)
(** We assume given a type A for elements. *)

Section S.

  Context {A : Type}.

  Notation eq_dec_type := (forall x y : A, {x=y}+{~x=y}).

(****************************************************************************)
(** * Type for sets of elements of type [A] *)

  Definition set := A -> Prop.

(****************************************************************************)
(** * Definition of basic predicates and operations on sets *)

  Definition mem a (P : set) := P a.

  Definition subset : relation set := pointwise_relation A impl.

  Infix "[<=]" := subset (at level 70).

  Definition equiv : relation set := pointwise_relation A iff.

  Infix "[=]" := equiv (at level 70). (* notation already defined in ListUtil *)

  Definition strict_subset P Q := P [<=] Q /\ ~Q [<=] P.

  Infix "[<]" := strict_subset (at level 70).

  Definition empty : set := fun _ => False.

  Definition all : set := fun _ => True.

  Definition add a (P : set) : set := fun x => x = a \/ mem x P.

  Definition singleton a := add a empty.

  Definition union (P Q : set) : set := fun x => mem x P \/ mem x Q.

  Definition rem a (P : set) : set := fun x => x <> a /\ mem x P.

  Definition diff (P Q : set) : set := fun x => mem x P /\ ~mem x Q.

  Definition of_list l : set := fun x => In x l.

  Ltac stac := intro; unfold add, rem, diff, union, of_list, mem; simpl; tauto.

(****************************************************************************)
(** Properties of [subset]. *)

  Global Instance subset_preorder : PreOrder subset.

  Proof. fo. Qed.

(****************************************************************************)
(** Properties of [equiv]. *)

  Lemma equiv_subset2 P Q : P [=] Q <-> P [<=] Q /\ Q [<=] P.

  Proof. fo. Qed.

  Global Instance equiv_Equivalence : Equivalence equiv.

  Proof. fo. Qed.

  Global Instance subset_equiv : Proper (equiv ==> equiv ==> impl) subset.

  Proof. fo. Qed.

  Lemma equiv_inter_transp : equiv == inter_transp subset.

  Proof. fo. Qed.

  Lemma equiv_elim P Q : P [=] Q <-> P [<=] Q /\ Q [<=] P.

  Proof. fo. Qed.

(****************************************************************************)
(** Properties of [mem]. *)

  Global Instance mem_subset : Proper (eq ==> subset ==> impl) mem.

  Proof. intros x y xy P Q PQ. subst. fo. Qed.

  Global Instance mem_equiv_impl : Proper (eq ==> equiv ==> impl) mem.

  Proof. intros x y xy P Q PQ. subst. fo. Qed.

  Global Instance mem_equiv : Proper (eq ==> equiv ==> iff) mem.

  Proof. intros x y xy P Q PQ. subst. fo. Qed.

(****************************************************************************)
(** Properties of [strict_subset]. *)

  Global Instance strict_subset_incl_subset : subrelation strict_subset subset.

  Proof. intros X Y [XY nYX]. hyp. Qed.

  Global Instance strict_subset_trans : Transitive strict_subset.

  Proof. intros X Y Z [XY nYX] [YZ nZY]. split. trans Y; hyp. fo. Qed.

  Global Instance strict_subset_subset_impl :
    Proper (subset --> subset ==> impl) strict_subset.

  Proof.
    intros P P' P'P Q Q' QQ' [PQ n]; unfold flip in P'P. split.
    rewrite P'P, <- QQ'. hyp. intro Q'P'. apply n. rewrite QQ', Q'P'. hyp.
  Qed.

  Global Instance strict_subset_equiv :
    Proper (equiv ==> equiv ==> impl) strict_subset.

  Proof.
    intros P P' PP' Q Q' QQ' [PQ n]. split.
    rewrite <- PP', <- QQ'. hyp.
    intro Q'P'. apply n. rewrite QQ', PP'. hyp.
  Qed.

(****************************************************************************)
(** Properties of [empty]. *)

  Lemma notin_empty x : ~mem x empty.

  Proof. fo. Qed.

(****************************************************************************)
(** Properties of [all]. *)

  Lemma subset_all P : P [<=] all.

  Proof. fo. Qed.

(****************************************************************************)
(** Properties of [add]. *)

  Global Instance add_subset : Proper (eq ==> subset ==> subset) add.

  Proof. intros a b ab P Q PQ. subst. fo. Qed.

  Lemma subset_add a P : P [<=] add a P.

  Proof. fo. Qed.

  Lemma mem_add a P : mem a (add a P).

  Proof. fo. Qed.

  Global Instance add_equiv : Proper (eq ==> equiv ==> equiv) add.

  Proof. intros a b ab P Q PQ. subst b. fo. Qed.

  Lemma add_already_in a P : mem a P -> add a P [=] P.

  Proof. intros a_in_P x. split; fo. subst. hyp. Qed.

  Arguments add_already_in [a P] _ _.

(****************************************************************************)
(** Properties of [rem]. *)

  Global Instance rem_subset : Proper (eq ==> subset ==> subset) rem.

  Proof. intros a b ab P Q PQ. subst b. fo. Qed.

  Global Instance rem_equiv : Proper (eq ==> equiv ==> equiv) rem.

  Proof. intros a b ab P Q PQ. subst b. fo. Qed.

  Lemma notin_rem a P : ~mem a (rem a P).

  Proof. fo. Qed.

  Lemma rem_notin a P : ~mem a P -> rem a P [=] P.

  Proof. intros a_notin_P x. fo. intro e. subst. fo. Qed.

  Lemma subset_rem a P : rem a P [<=] P.

  Proof. fo. Qed.

  Lemma strict_subset_rem a P : mem a P -> rem a P [<] P.

  Proof.
    intro aP. split. apply subset_rem. intro h. apply h in aP. revert aP.
    apply notin_rem.
  Qed.

  Lemma add_rem_neq a b P : a <> b -> add a (rem b P) [=] rem b (add a P).
 
  Proof. intro nab. split. fo. subst. hyp. fo. Qed.

  Lemma rem_add_neq a b P : a <> b -> rem a (add b P) [=] add b (rem a P).
 
  Proof. intro nab. split. fo. fo. subst. fo. Qed.

  Lemma add_rem (eq_dec : eq_dec_type) a P : mem a P -> add a (rem a P) [=] P.

  Proof. intros aP x. split. fo. subst. hyp. stac. Qed.

  Arguments add_rem _ [a P] _ _.

  Lemma rem_add a P : ~mem a P -> rem a (add a P) [=] P.

  Proof. intros naP x. fo. intro; subst; contr. Qed.

  Arguments rem_add [a P] _ _.

(****************************************************************************)
(** Properties of [union]. *)

  Global Instance union_subset : Proper (subset ==> subset ==> subset) union.

  Proof. fo. Qed.

  Global Instance union_equiv : Proper (equiv ==> equiv ==> equiv) union.

  Proof. fo. Qed.

  Lemma union_com P Q : union P Q [=] union Q P.

  Proof. fo. Qed.

  Lemma union_assoc P Q R : union (union P Q) R [=] union P (union Q R).

  Proof. fo. Qed.

  Lemma subset_union_l P Q : P [<=] union P Q.

  Proof. fo. Qed.

  Lemma subset_union_r P Q : Q [<=] union P Q.

  Proof. fo. Qed.

  Lemma union_empty_l P : union empty P [=] P.

  Proof. fo. Qed.

  Lemma union_empty_r P : union P empty [=] P.

  Proof. fo. Qed.

(****************************************************************************)
(** Properties of [diff]. *)

  Global Instance diff_subset : Proper (subset ==> subset --> subset) diff.

  Proof. fo. Qed.

  Global Instance diff_equiv : Proper (equiv ==> equiv ==> equiv) diff.

  Proof. fo. Qed.

  Lemma union_diff P Q (Q_dec : forall x, {Q x}+{~Q x}) :
    union (diff P Q) Q [=] union P Q.

  Proof. split. fo. unfold union, diff, mem. destruct (Q_dec a); tauto. Qed.

(****************************************************************************)
(** * Type for the elements of a set. *)

  Definition elts (P : set) := sig (fun x => mem x P).

  Definition elt {P x} (h : mem x P) : elts P := @exist _ P _ h.

  Definition elt_val {P} (x : elts P) := proj1_sig x.

  Coercion elt_val : elts >-> A.

  Definition elts_subset P Q : P [<=] Q -> elts P -> elts Q.

  Proof. intros PQ [x_val x]. ex x_val. apply PQ. hyp. Defined.

  Lemma inj_elts_subset P Q (h : P [<=] Q) : injective (elts_subset h).

  Proof.
    intros [x_val x] [y_val y] e. apply sig_eq in e. apply sig_eq. hyp.
  Qed.

  Definition elts_equiv P Q : P [=] Q -> elts P -> elts Q.

  Proof. intros PQ [x_val x]. apply exist with (x:=x_val). fo. Defined.

  Definition elts_eq {P} : relation (elts P) :=
    fun x y => elt_val x = elt_val y.

  Instance elts_eq_Equivalence P : Equivalence (@elts_eq P).

  Proof.
    split. fo. firstorder auto with crelations.
    intros x y z xy yz. unfold elts_eq in *. trans (elt_val y); hyp.
  Qed.

(****************************************************************************)
(** * Fiber (inverse image of a singleton) *)

  Definition fiber (P : set) B (f : elts P -> B) b : set :=
    fun x => exists h : mem x P, f (elt h) = b.

(****************************************************************************)
(** * Properties of [of_list]. *)

  Lemma of_cons a l : of_list (a :: l) [=] add a (of_list l). 

  Proof. fo. Qed.

  Lemma of_remove (eq_dec : eq_dec_type) a :
    forall l, of_list (remove eq_dec a l) [=] rem a (of_list l). 

  Proof.
    induction l; simpl. fo. destruct (eq_dec a0 a). subst. firstorder auto with exfalso.
    rewrite !of_cons, IHl, add_rem_neq, rem_add_neq; auto. refl.
  Qed.

  Lemma of_app l m : of_list (l++m) [=] union (of_list l) (of_list m).

  Proof.
    intro x. fo. destruct (in_app_or H); fo.
    apply in_appl. hyp. apply in_appr. hyp.
  Qed.

  Lemma of_map_L P n (f : N n -> elts P) :
    surjective f -> P [=] of_list (map (elt_val o f) (L n)).

  Proof.
    intro f_surj. set (g := elt_val o f).
    rewrite equiv_subset2. split; intros x_val x.
    (* P <= of_list (map g (L n)) *)
    unfold mem, of_list. destruct (f_surj (elt x)) as [[k_val k] e].
    apply sig_eq in e; simpl in e. subst.
    change (In (g (N_ k)) (map g (L n))). apply in_map. apply In_L.
    (* of_list (map g (L n)) <= P *)
    unfold mem, of_list in x. destruct (in_map_elim x) as [k [k1 k2]].
    subst. unfold g, comp. destruct (f k) as [y_val y]. fo.
  Qed.

End S.

Arguments set : clear implicits.
Arguments rem_add [A a P] _ _.
Arguments add_rem [A] _ [a P] _ _.

Infix "[<=]" := subset (at level 70).
Infix "[=]" := equiv (at level 70).
Infix "[<]" := strict_subset (at level 70).

(***********************************************************************)
(** * Compatibility of [subset] and [equiv] with [inclusion] and [same_rel]. *)

Global Instance subset_equiv1 A1 B (f : set A1 -> relation B) :
  Proper (subset ==> inclusion) f -> Proper (equiv ==> same) f.

Proof. intros hf s1 s1'. rewrite equiv_elim. fo. Qed.

Global Instance subset_equiv2 A1 A2 B (f : set A1 -> set A2 -> relation B) :
  Proper (subset ==> subset ==> inclusion) f ->
  Proper (equiv ==> equiv ==> same) f.

Proof.
  intros hf s1 s1'. rewrite equiv_elim. intros [s1s1' s1's1] s2 s2'.
  rewrite equiv_elim. intros [s2s2' s2's2]. split; apply hf; hyp.
Qed.

(***********************************************************************)
(** * Image of a set by a function. *)

Section image.

  Variables (X Y : Type) (f : X -> Y).

  Definition image (A : set X) : set Y := fun y => exists x, A x /\ y = f x.

  Lemma image_empty : image empty [=] empty.

  Proof. fo. Qed.

  Lemma image_add a A : image (add a A) [=] add (f a) (image A).

  Proof. intro x. split. fo. subst. fo. fo. Qed.

  Lemma image_singleton x : image (singleton x) [=] singleton (f x).

  Proof. unfold singleton. rewrite image_add, image_empty. refl. Qed.

  Lemma image_union A B : image (union A B) [=] union (image A) (image B).

  Proof. fo. Qed.

End image.
