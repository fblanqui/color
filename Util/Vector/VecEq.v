(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-04-13

setoid equality on vectors
*)

Set Implicit Arguments.

Require Import Setoid VecUtil LogicUtil NatUtil.

(***********************************************************************)
(** pointwise equality of vectors *)

Section eq_vec.

Variables (A : Type) (eqA : A -> A -> Prop) (stA : Setoid_Theory A eqA).
Notation "x =A= y" := (eqA x y) (at level 70).
Add Setoid A eqA stA as A_eqA.

Notation vec := (vector A).

Definition eq_vec := @Vforall2n A A eqA.

Notation "v1 =v v2" := (eq_vec v1 v2) (at level 70).

Lemma eq_vec_refl : forall n (x : vec n), x =v x.

Proof.
unfold eq_vec. intros. apply Vforall2n_intro. refl.
Qed.

Lemma eq_vec_sym : forall n (x y : vec n), x =v y -> y =v x.

Proof.
unfold eq_vec. intros. apply Vforall2n_intro. intros. symmetry.
apply Vforall2n_nth with (R:=eqA). hyp.
Qed.

Lemma eq_vec_trans : forall n (x y z : vec n), x =v y -> y =v z -> x =v z.

Proof.
unfold eq_vec. intros. apply Vforall2n_intro. intros.
transitivity (Vnth y ip); apply Vforall2n_nth with (R:=eqA); hyp.
Qed.

Definition eq_vec_st : forall n, Setoid_Theory (vec n) (@eq_vec n).

Proof.
constructor. unfold Reflexive. apply eq_vec_refl.
unfold Symmetric. apply eq_vec_sym. unfold Transitive. apply eq_vec_trans.
Defined.

Lemma eq_vec_cons : forall x x' n (v v' : vec n),
  Vcons x v =v Vcons x' v' <-> x =A= x' /\ v =v v'.

Proof.
unfold eq_vec, Vforall2n. intros. simpl. tauto.
Qed.

(***********************************************************************)
(** morphisms *)

Lemma Vnth_mor : forall n (v v' : vec n), v =v v' ->
  forall i (h : i<n), Vnth v h =A= Vnth v' h.

Proof.
intros. apply Vforall2n_nth with (R:=eqA). hyp.
Qed.

Lemma Veq_vec_nth : forall n (v v' : vec n), 
  (forall i (ip : i < n), Vnth v ip =A= Vnth v' ip) ->
  v =v v'.
Proof.
  apply Vforall2n_intro.
Qed.

Section Vforall.

Variable f : A -> A -> Prop.
Variable f_mor : forall a1 a1', a1 =A= a1' -> forall a2 a2', a2 =A= a2' ->
  (f a1 a2 <-> f a1' a2').

Add Morphism f with signature eqA ==> eqA ==> iff as f_mor_eqA.

Proof.
exact f_mor.
Qed.

Lemma Vforall2n_aux_mor : forall n1 (v1 v1' : vec n1),
  v1 =v v1' -> forall n2 (v2 v2': vec n2), v2 =v v2' ->
    (Vforall2n_aux f v1 v2 <-> Vforall2n_aux f v1' v2').

Proof.
induction v1; simpl; intros. VOtac. simpl.
destruct v2. VOtac. tauto. VSntac v2'. tauto.
revert H. VSntac v1'. simpl. destruct v2. VOtac. tauto.
revert H0. VSntac v2'. repeat rewrite eq_vec_cons.
intros [h1 h2] [h3 h4]. rewrite <- h1. rewrite <- h3.
rewrite (IHv1 _ h4 _ _ _ h2). tauto.
Qed.

Lemma Vforall2n_mor : forall n (v1 v1' : vec n), v1 =v v1' ->
  forall v2 v2': vec n, v2 =v v2' ->
    (Vforall2n f v1 v2 <-> Vforall2n f v1' v2').

Proof.
intros. unfold Vforall2n. apply Vforall2n_aux_mor; hyp.
Qed.

End Vforall.

(***********************************************************************)
(** (Vfold_left f) is a morphism is f is a morphism *)

Variables (B : Type) (eqB : B -> B -> Prop) (stB : Setoid_Theory B eqB).
Notation "x =B= y" := (eqB x y) (at level 70).
Add Setoid B eqB stB as B_eqB.

Section Vfold_left.

Variable f : B -> A -> B.
Variable f_mor :
  forall b b', b =B= b' -> forall a a', a =A= a' -> f b a =B= f b' a'.

Lemma Vfold_left_mor : forall b b', b =B= b' ->
  forall n (v v': vec n), v =v v' -> Vfold_left f b v =B= Vfold_left f b' v'.

Proof.
induction v; simpl; intros. VOtac. simpl. hyp. revert H0. VSntac v'.
rewrite eq_vec_cons. intuition. simpl. apply f_mor; try hyp. apply IHv; hyp.
Qed.

End Vfold_left.

End eq_vec.

Implicit Arguments eq_vec_cons [A x x' n v v'].
Implicit Arguments Vforall2n_mor [A eqA f n v1 v1' v2 v2'].
Implicit Arguments Vnth_mor [A n v v' i].

(***********************************************************************)
(** assumptions for more morphisms *)

Section S.

Variables (A : Type) (eqA : A -> A -> Prop) (stA : Setoid_Theory A eqA).
Notation "x =A= y" := (eqA x y) (at level 70).
Add Setoid A eqA stA as A_eqA2.

Add Parametric Relation n : (@vector A n) (@eq_vec A eqA n)
  reflexivity proved by (@eq_vec_refl A eqA stA n)
  symmetry proved by (@eq_vec_sym A eqA stA n)
    transitivity proved by (@eq_vec_trans A eqA stA n)
      as eq_vecA_rel.

Variables (B : Type) (eqB : B -> B -> Prop) (stB : Setoid_Theory B eqB).
Notation "x =B= y" := (eqB x y) (at level 70).
Add Setoid B eqB stB as B_eqB2.

Add Parametric Relation n : (@vector B n) (@eq_vec B eqB n)
  reflexivity proved by (@eq_vec_refl B eqB stB n)
  symmetry proved by (@eq_vec_sym B eqB stB n)
    transitivity proved by (@eq_vec_trans B eqB stB n)
      as eq_vecB_rel.

Variables (C : Type) (eqC : C -> C -> Prop) (stC : Setoid_Theory C eqC).
Notation "x =C= y" := (eqC x y) (at level 70).
Add Setoid C eqC stC as C_eqC2.

Add Parametric Relation n : (@vector C n) (@eq_vec C eqC n)
  reflexivity proved by (@eq_vec_refl C eqC stC n)
  symmetry proved by (@eq_vec_sym C eqC stC n)
    transitivity proved by (@eq_vec_trans C eqC stC n)
      as eq_vecC_rel.

(***********************************************************************)
(** (Vmap f) is a morphism is f is a morphism *)

Section Vmap.

Variable f : A -> B.
Variable f_mor : forall a a', a =A= a' -> f a =B= f a'.

Lemma Vmap_mor : forall n (v v': vector A n), eq_vec eqA v v' ->
  eq_vec eqB (Vmap f v) (Vmap f v').

Proof.
induction v; simpl; intros. VOtac. refl. revert H. VSntac v'. simpl.
repeat rewrite eq_vec_cons. intuition.
Qed.

(***********************************************************************)
(** Vmap equality *)

Variable g : A -> B.

Lemma Vmap_eqA : forall n (v : vector A n),
  Vforall (fun x => f x =B= g x) v -> eq_vec eqB (Vmap f v) (Vmap g v).

Proof.
induction v; simpl; intros. refl. rewrite eq_vec_cons. intuition.
Qed.

End Vmap.

(***********************************************************************)
(** (Vmap2 f) is a morphism is f is a morphism *)

Section Vmap2.

Variable f : A -> B -> C.
Variable f_mor :
  forall a a', a =A= a' -> forall b b', b =B= b' -> f a b =C= f a' b'.

Lemma Vmap2_mor : forall n (va va': vector A n), eq_vec eqA va va' ->
  forall (vb vb' : vector B n), eq_vec eqB vb vb' ->
    eq_vec eqC (Vmap2 f va vb) (Vmap2 f va' vb').

Proof.
induction va; simpl; intros. refl. revert H. VSntac va'. revert H0. VSntac vb.
VSntac vb'. repeat rewrite eq_vec_cons. intuition.
Qed.

End Vmap2.

End S.
