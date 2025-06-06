(**

CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17
- Pierre-Yves Strub, 2009-04-09

* Basic meta-theorems and tactics
*)

Set Implicit Arguments.

From Stdlib Require Import Basics.

Arguments exist [A P x] _.
Arguments existT [A P x] _.

Definition decidable0 P := {P}+{~P}.
Definition decidable1 A P := forall x : A, {P x}+{~P x}.
Definition decidable2 A B P := forall (x : A) (y : B), {P x y}+{~P x y}.

(***********************************************************************)
(** Abbreviations of some basic Coq tactics. *)

Ltac hyp := assumption || (symmetry; assumption).
Ltac ehyp := eassumption.
Ltac refl := reflexivity.
Ltac sym := symmetry.
Ltac trans x := transitivity x.
Ltac contr := contradiction.
Ltac cong := congruence.
Ltac discr := intros; discriminate.
Ltac fo := unfold flip, impl; firstorder.
Ltac gen t := generalize t.
Ltac ded t := gen t; intro.
Ltac class := fold impl; auto with typeclass_instances.
Ltac decomp h := decompose [and or ex] h; clear h.
Ltac inv h := inversion h; clear h; subst.

Tactic Notation "ex" constr(x1) := exists x1.
Tactic Notation "ex" constr(x1) constr(x2) := exists x1; exists x2.
Tactic Notation "ex" constr(x1) constr(x2) constr(x3) :=
  exists x1; exists x2; exists x3.
Tactic Notation "ex" constr(x1) constr(x2) constr(x3) constr(x4) :=
  exists x1; exists x2; exists x3; exists x4.
Tactic Notation "ex" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5) :=
  exists x1; exists x2; exists x3; exists x4; exists x5.
Tactic Notation "ex" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) := exists x1; exists x2; exists x3; exists x4; exists x5;
    exists x6.
Tactic Notation "ex" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7) := exists x1; exists x2; exists x3; exists x4;
    exists x5; exists x6; exists x7.
Tactic Notation "ex" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7) constr(x8) := exists x1; exists x2; exists x3;
    exists x4; exists x5; exists x6; exists x7; exists x8.

(***********************************************************************)
(** [geneq H x e(x)] transforms a goal [G(x)] into
[forall t, H t -> forall x, e(x) = t -> G(x)] *)

Ltac geneq H x e := gen (eq_refl e); gen (H e);
  clear H; generalize e at -2; let t := fresh "t" in let h := fresh "h" in
    intros t h; revert t h x.

(***********************************************************************)
(** Normalization tactics used in Rainbow. *)

Ltac norm e :=
  let x := fresh in set (x := e); vm_compute in x; subst x.

Ltac norm_in H e :=
  let x := fresh in set (x := e) in H; vm_compute in x; subst x.

(*FIXME: Tactic Notation "norm" constr(e) "in" ident(H) := norm_in H e.*)

Ltac check_eq := vm_compute; refl.

(***********************************************************************)
(** Other tactics. *)

Ltac intro_neg := match goal with |- ~ _ => intro | _ => idtac end.

Ltac done :=
  trivial; hnf; intros; solve
   [ repeat progress first
       [solve [trivial | apply eq_sym; trivial]
         | discr | contr | split]
   | hyp
   | match goal with H : ~ _ |- _ => solve [case H; trivial] end ].

Tactic Notation "by" tactic(T) := (T; done).

(***********************************************************************)
(** Tactic for handling irreflexivity. *)

  Ltac irrefl_rel R :=
    match goal with
    | h1 : R ?x ?x -> False |- _ => exfalso; apply h1; refl
    | h1 : ~R ?x ?x |- _ => exfalso; apply h1; refl
    | h1 : ~R ?x ?y, h2 : R ?x ?y |- _ => exfalso; apply h1; hyp
    | h1 : ~R ?x ?y, h2 : R ?y ?x |- _ => exfalso; apply h1; hyp
    | h1 : ~R ?x ?y, h2 : R ?x ?z, h3 : R ?z ?y |- _ =>
      exfalso; apply h1; rewrite h2, <- h3; refl
    | h1 : ~R ?x ?y, h2 : R ?x ?z, h3 : R ?y ?z |- _ =>
      exfalso; apply h1; rewrite h2, h3; refl
    | h1 : ~R ?x ?y, h2 : R ?z ?x, h3 : R ?y ?z |- _ =>
      exfalso; apply h1; rewrite <- h2, h3; refl
    | h1 : ~R ?x ?y, h2 : R ?z ?x, h3 : R ?z ?y |- _ =>
      exfalso; apply h1; rewrite <- h2, <- h3; refl
    end.

(***********************************************************************)
(** Basic theorems on intuitionist propositional calculus. *)

Lemma impl_refl : forall P, P -> P.

Proof. fo. Qed.

Lemma contraposee_inv : forall P Q : Prop, (P -> Q) -> ~Q -> ~P.

Proof. fo. Qed.

Lemma and_assoc : forall P Q R, P /\ Q /\ R <-> (P /\ Q) /\ R.

Proof. fo. Qed.

Lemma or_sym : forall P Q, P \/ Q <-> Q \/ P.

Proof. fo. Qed.

Lemma and_idem : forall P, P /\ P <-> P.

Proof. fo. Qed.

Lemma and_idem_and_l : forall P Q, P /\ P /\ Q <-> P /\ Q.

Proof. fo. Qed.

Lemma and_idem_and_r : forall P Q, Q /\ P /\ P <-> Q /\ P.

Proof. fo. Qed.

Lemma not_or P Q : ~(P \/ Q) <-> ~P /\ ~Q.

Proof. fo. Qed.

Lemma iff_and : forall P Q P' Q',
  ((P <-> P') /\ (Q <-> Q')) -> ((P /\ Q) <-> (P' /\ Q')).

Proof. fo. Qed.

Lemma iff_forall : forall A (P Q : A->Prop),
  (forall x, P x <-> Q x) -> ((forall x, P x) <-> (forall x, Q x)).

Proof. fo. Qed.

(***********************************************************************)
(** Tactic removing identical propositions in a conjunction. *)

Ltac and_idem := rewrite !and_assoc;
  repeat (rewrite and_idem_and_l || rewrite and_idem_and_r || rewrite and_idem).

(***********************************************************************)
(** Basic theorems on intuitionist predicate calculus. *)

Section pred.

  Variables (A : Type) (P : A -> Prop).

  Lemma not_exists_imply_forall_not : ~(exists x, P x) -> forall x, ~P x.

  Proof. fo. Qed.

  Lemma forall_not_imply_not_exists : (forall x, ~P x) -> ~(exists x, P x).

  Proof. fo. Qed.

  Lemma not_exists_eq : ~(exists x, P x) <-> (forall x, ~P x).

  Proof. fo. Qed.

  Lemma exists_not_imply_not_forall : (exists x, ~P x) -> ~(forall x, P x).

  Proof. fo. Qed.

End pred.

(***********************************************************************)
(** Tactic for decomposing a goal. *)

Ltac split_hyps :=
  match goal with
  | h : False |- _ => contr
  | h : ~(_ \/ _) |- _ => rewrite not_or in h; split_hyps
  | h : _ <-> _ |- _ => destruct h; split_hyps
  | h : _ /\ _ |- _ => destruct h; split_hyps
  | h : @ex _ _ |- _ => destruct h; split_hyps
  | h : _ \/ _ |- _ => destruct h; split_hyps
  | h : True |- _ => clear h; split_hyps
  | |- _ => idtac
  end.

Ltac split_goal :=
  match goal with
  | |- ~(_ \/ _) => rewrite not_or; split_goal
  | |- ~ _ => intro; split_goal
  | |- _ <-> _ => split; split_goal
  | |- _ /\ _ => split; split_goal
  | |- _ -> _ => intro; split_goal
  | |- _ => idtac
  end.

Ltac split_all := split_goal; split_hyps; auto.
