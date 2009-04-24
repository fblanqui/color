(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2009-03-27

  Utility results about the option/exception type.
*)

Require Import Bool.
Require Import ListForall.
Require Import ListUtil.
Require Import Program.

Set Implicit Arguments.

Section ExcUtil.

Variable A : Type.
Variable P : A -> Prop.
Variable f : forall a : A, Exc (P a).

Definition exc_to_bool (P : Prop) (e : Exc P) :=
  match e with
  | value _ => true
  | error => false
  end.

Definition pred_exc_to_bool x := exc_to_bool (f x).

Program Definition lforall_exc (l : list A) : 
  Exc (lforall (fun x : A => exists p, f x = value p) l) :=
  match forallb pred_exc_to_bool l with
  | true => value _
  | false => error
  end.

Next Obligation.
Proof with auto.
  apply forallb_imp_lforall with (fun x => exc_to_bool (f x))...
  intros. destruct (f x). exists p... discriminate.
Qed.

Program Definition partition_exc (l : list A) :
  { ll : list A * list A |
      let (l1, l2) := ll in
        lforall P l1 /\
        (lforall (fun x => f x = error) l2) /\
        (forall x, In x l -> In x l1 \/ In x l2)
        
  } :=
  partition pred_exc_to_bool l.

Next Obligation.
Proof with auto.
  assert (left := fun x => partition_left pred_exc_to_bool x l).
  assert (right := fun x => partition_right pred_exc_to_bool x l).
  assert (complete := fun x => partition_complete pred_exc_to_bool x l).
  destruct (partition pred_exc_to_bool l).
  unfold pred_exc_to_bool in *.
  repeat split...
  apply lforall_intro. intros x xl.
  assert (ll := left x xl). destruct (f x); try discriminate...
  apply lforall_intro. intros x xl.
  assert (rr := right x xl). destruct (f x); try discriminate...
Qed.

End ExcUtil.

Section MapExc.

Variable A B : Type.
Variable f : A -> Exc B.

Program Fixpoint map_exc (l : list A) : Exc (list B) :=
  match l with
  | [] => value []
  | cons x xs => 
      match f x with
      | error => error
      | value v =>
          match map_exc xs with
          | error => error
          | value vs => value (v :: vs)
          end
      end
  end.

End MapExc.

(* Anomaly: *)
(*
Section Error.

Variable A B : Type.
Variable f : A -> B.

Program Fixpoint map_exc (l : list A) : Exc (list B) :=
  match l with
  | [] => value []
  | cons x xs => 
      match f x with
      | error => error
      | value v =>
          match map_exc xs with
          | error => error
          | value vs => value (v :: vs)
          end
      end
  end.

End Error.
*)

Implicit Arguments exc_to_bool [P].
