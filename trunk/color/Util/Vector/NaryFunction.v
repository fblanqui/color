(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-04-02

basic definitions on functions taking vectors as arguments
*)

Set Implicit Arguments.

Require Import RelUtil.
Require Import VecUtil.

Section S.

Variables (A B : Type).

Definition naryFunction n := vector A n -> B.

Variables (n : nat) (f : naryFunction n).

Definition Vmonotone_i (Ra : relation A) (Rb : relation B)
  i j (H : i + S j = n) :=
  forall vi vj, monotone Ra Rb (fun z => f (Vcast (Vapp vi (Vcons z vj)) H)).

Implicit Arguments Vmonotone_i [i j].

Lemma Vmonotone_i_transp : forall (Ra : relation A) (Rb : relation B)
  i j (H : i + S j = n),
  Vmonotone_i Ra Rb H -> Vmonotone_i (transp Ra) (transp Rb) H.

Proof.
unfold Vmonotone_i. intros Ra Rb i j H H' vi vj. apply monotone_transp.
apply H'.
Qed.

Definition Vmonotone (Ra : relation A) (Rb : relation B) :=
  forall i j (H : i + S j = n), Vmonotone_i Ra Rb H.

Lemma Vmonotone_transp : forall (Ra : relation A) (Rb : relation B),
  Vmonotone Ra Rb -> Vmonotone (transp Ra) (transp Rb).

Proof.
unfold Vmonotone. intros Ra Rb H i j H'. apply Vmonotone_i_transp. apply H.
Qed.

End S.

Definition naryFunction1 A := @naryFunction A A.
Definition Vmonotone1_i A n f R := @Vmonotone_i A A n f R R.
Definition Vmonotone1 A n f R := @Vmonotone A A n f R R.

Implicit Arguments Vmonotone_i [A B n i j].

Section preserv.

Variables (A : Type) (P : A->Prop) (n : nat) (f : naryFunction A A n).

Definition preserv := forall v, Vforall P v -> P (f v).

Definition restrict (H : preserv) : naryFunction (sig P) (sig P) n :=
  fun v => exist P (f (Vmap (@proj1_sig _ _) v)) (H _ (Vforall_of_vsig v)).

End preserv.
