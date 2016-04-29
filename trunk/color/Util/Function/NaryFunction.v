(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-04-02

basic definitions on functions taking vectors as arguments
*)

Set Implicit Arguments.

From CoLoR Require Import RelUtil VecUtil.

Section S.

  Variables A B : Type.

  Definition naryFunction n := vector A n -> B.

  Variables (n : nat) (f : naryFunction n).

  Definition Vmonotone_i (Ra : relation A) (Rb : relation B)
    i j (H : i + S j = n) :=
    forall vi vj, monotone Ra Rb (fun z => f (Vcast (Vapp vi (Vcons z vj)) H)).

  Arguments Vmonotone_i Ra Rb [i j] _.

  Lemma Vmonotone_i_transp Ra Rb i j (H : i + S j = n) :
    Vmonotone_i Ra Rb H -> Vmonotone_i (transp Ra) (transp Rb) H.

  Proof. intros H' vi vj. apply monotone_transp. apply H'. Qed.

  Definition Vmonotone Ra Rb :=
    forall i j (H : i + S j = n), Vmonotone_i Ra Rb H.

  Lemma Vmonotone_transp Ra Rb :
    Vmonotone Ra Rb -> Vmonotone (transp Ra) (transp Rb).

  Proof. intros H i j H'. apply Vmonotone_i_transp. apply H. Qed.

End S.

Definition naryFunction1 A := naryFunction A A.
Definition Vmonotone1_i A n f R := @Vmonotone_i A A n f R R.
Definition Vmonotone1 A n f R := @Vmonotone A A n f R R.

Arguments Vmonotone_i [A B n] _ _ _ [i j] _.

Section preserv.

  Variables (A : Type) (P : A->Prop) (n : nat) (f : naryFunction A A n).

  Definition preserv := forall v, Vforall P v -> P (f v).

  Definition restrict (H : preserv) : naryFunction (sig P) (sig P) n :=
    fun v => exist (H _ (Vforall_of_sig v)).

End preserv.
