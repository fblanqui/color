(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-07-07

root labelling (Zantema & Waldmann, RTA'07) (Sternagel & Middeldorp, RTA'08)
*)

Set Implicit Arguments.

From CoLoR Require Import ATrs LogicUtil ListUtil VecUtil BoolUtil EqUtil ASemLab SN
  NatUtil RelUtil AWFMInterpretation.

(***********************************************************************)
(** data necessary for a root labelling *)

Module Type RootLab.

  Parameter Sig : Signature.
  Parameter some_symbol : Sig.

  Parameter Fs : list Sig.
  Parameter Fs_ok : forall x : Sig, List.In x Fs.

End RootLab.

(***********************************************************************)
(** root labelling *)

Module RootSemLab (Import R : RootLab) <: FinSemLab.

  Notation beq_symb_ok := (@beq_symb_ok Sig).
  Notation eq_symb_dec := (@eq_symb_dec Sig).

  Notation term := (term Sig). Notation terms := (vector term).
  Notation rule := (rule Sig). Notation rules := (rules Sig).

  Definition Sig := Sig.

  Definition I := mkInterpretation some_symbol (fun f _ => f).

  Definition L (f : Sig) := vector Sig (arity f).

  Definition beq f g (l : L f) (m : L g) := beq_vec (@beq_symb Sig) l m.

  Lemma beq_ok : forall f (l1 l2 : L f), beq l1 l2 = true <-> l1 = l2.

  Proof.
    intros f l1 l2. apply beq_vec_ok. apply @beq_symb_ok.
  Qed.

  Definition pi (f : Sig) (v : vector Sig (arity f)) := v.

  Definition beqI (t u : term) :=
    match t, u with
      | Var x, Var y => beq_nat x y
      | Fun f _, Fun g _ => beq_symb f g
      | _, _ => false
    end.

  Lemma beqI_ok : rel_of_bool beqI << IR I (@eq I).

  Proof.
    intros t u. unfold rel_of_bool.
    destruct t; destruct u; simpl; intros; try discr.
    rewrite beq_nat_ok in H. subst. intro. refl.
    rewrite beq_symb_ok in H. subst. intro. refl.
  Qed.

  Definition Fs := Fs.
  Definition Fs_ok := Fs_ok.

  Definition Is := Fs.
  Definition Is_ok := Fs_ok.

  Definition Ls (f : Sig) := enum_tuple I Is (arity f).

  Lemma Ls_ok : forall f (x : L f), List.In x (Ls f).

  Proof.
    intros f x. unfold Ls. apply (enum_tuple_complete I Is_ok).
  Qed.

End RootSemLab.

Module RootLabProps (RL : RootLab).

  Module FSL := RootSemLab RL.

  Module Props := FinSemLabProps FSL.

  Module LabSig := Props.LabSig.

  Ltac rootlab := Props.semlab.

End RootLabProps.
