(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2009-03-27

Utility results about the option/exception type.
*)

Set Implicit Arguments.

From Stdlib Require Import Bool Program.
From CoLoR Require Import ListUtil LogicUtil.
Import ListNotations.

Lemma Some_eq : forall A (x y : A), Some x = Some y -> x = y.

Proof. intros. inversion H. auto. Qed.

Lemma option_dec A (el : option A) : el = None \/ exists w, el = Some w.

Proof.
  intros. destruct el.
  right; exists a; trivial.
  left; trivial.
Qed.

Section dec.

  Variables (A : Type) (eq_dec : forall x y : A, {x=y}+{~x=y}).

  Lemma eq_opt_dec : forall x y : option A, {x=y}+{~x=y}.

  Proof. decide equality. Qed.

End dec.

Section OptUtil.

  Variable A : Type.
  Variable P : A -> Prop.
  Variable f : forall a : A, option (P a).

  Definition opt_to_bool (P : Prop) (e : option P) :=
    match e with
      | Some _ => true
      | None => false
    end.

  Definition pred_opt_to_bool x := opt_to_bool (f x).

  Program Definition lforall_opt (l : list A) : 
    option (lforall (fun x : A => exists p, f x = Some p) l) :=
    match forallb pred_opt_to_bool l with
      | true => Some _
      | false => None
    end.

  Next Obligation.
  Proof with auto.
    apply forallb_imp_lforall with (fun x => opt_to_bool (f x))...
    intros. destruct (f x). exists p... discr.
  Qed.

  Program Definition partition_opt (l : list A) :
    { ll : list A * list A |
      let (l1, l2) := ll in
        lforall P l1 /\
        (lforall (fun x => f x = error) l2) /\
        (forall x, In x l -> In x l1 \/ In x l2)
    } := partition pred_opt_to_bool l.

  Next Obligation.
  Proof with auto.
    assert (left := fun x => partition_left pred_opt_to_bool x l).
    assert (right := fun x => partition_right pred_opt_to_bool x l).
    assert (complete := fun x => partition_complete pred_opt_to_bool x l).
    destruct (partition pred_opt_to_bool l).
    unfold pred_opt_to_bool in *.
    repeat split...
    apply lforall_intro. intros x xl.
    assert (ll := left x xl). destruct (f x); try discr...
    apply lforall_intro. intros x xl.
    assert (rr := right x xl). destruct (f x); try discr...
  Qed.

End OptUtil.

Section Map_option.

  Variable A B : Type.
  Variable f : A -> option B.

  Program Fixpoint map_opt (l : list A) : option (list B) :=
    match l with
      | [] => Some []
      | cons x xs => 
        match f x with
          | None => None
          | Some v =>
            match map_opt xs with
              | None => None
              | Some vs => Some (v :: vs)
            end
        end
    end.

End Map_option.

Arguments opt_to_bool [P] _.
