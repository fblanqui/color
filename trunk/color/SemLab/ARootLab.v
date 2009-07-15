(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-07-07

root labelling (Zantema & Waldmann, RTA'07) (Sternagel & Middeldorp, RTA'08)
*)

Set Implicit Arguments.

Require Import ATrs.
Require Import LogicUtil.
Require Import ListUtil.
Require Import VecUtil.
Require Import BoolUtil.
Require Import EqUtil.
Require Import ASemLab.
Require Import SN.
Require Import NatUtil.
Require Import RelUtil.
Require Import AWFMInterpretation.

(***********************************************************************)
(** data necessary for a root labelling *)

Module Type RootLab.

  Parameter Sig : Signature.
  Parameter some_symbol : Sig.

  Parameter Fs : list Sig.
  Parameter Fs_ok : forall x : Sig, In x Fs.

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

  Record Lab : Type := mk {
    L_symb : Sig;
    L_args : vector I (arity L_symb)
  }.

  Ltac Leqtac := repeat
    match goal with
      | H : mk ?x ?v = mk ?x ?w |- _ =>
        let h := fresh in
          (injection H; intro h1; ded (inj_pairT2 eq_symb_dec h1);
            clear h1; clear H)
      | H : mk ?x ?v = mk ?y ?w |- _ =>
        let h1 := fresh in let h2 := fresh in
          (injection H; intros h1 h2; subst; ded (inj_pairT2 eq_symb_dec h1);
            clear h1; clear H)
    end.

  Definition L := Lab.

  Definition beq (l1 l2 : L) :=
    let (f1,v1) := l1 in let (f2,v2) := l2 in
      beq_symb f1 f2 && beq_vec (@beq_symb Sig) v1 v2.

  Lemma beq_ok : forall l1 l2, beq l1 l2 = true <-> l1 = l2.

  Proof.
    intros [f1 v1] [f2 v2]. simpl. rewrite andb_eq. rewrite beq_symb_ok.
    intuition. subst. apply beq_vec_beq_impl_eq in H1. subst. refl.
    apply beq_symb_ok. Leqtac. refl. Leqtac. apply beq_vec_ok2.
    apply beq_symb_ok. hyp.
  Qed.

  Definition pi := mk.

  Definition beqI (t u : term) :=
    match t, u with
      | Var x, Var y => beq_nat x y
      | Fun f _, Fun g _ => beq_symb f g
      | _, _ => false
    end.

  Lemma beqI_ok : rel beqI << IR I (@eq I).

  Proof.
    intros t u. unfold rel. destruct t; destruct u; simpl; intros; try discr.
    rewrite beq_nat_ok in H. subst. intro. refl.
    rewrite beq_symb_ok in H. subst. intro. refl.
  Qed.

  Definition Fs := Fs.
  Definition Fs_ok := Fs_ok.

  Definition Is := Fs.
  Definition Is_ok := Fs_ok.

  Definition Ls := flat_map (fun f =>
    map (fun fs => @mk f fs) (enum_tuple I Is (arity f))) Fs.

  Lemma Ls_ok : forall x, In x Ls.

  Proof.
    intros [f fs]. unfold Ls. rewrite in_flat_map. exists f. split.
    apply Fs_ok. rewrite in_map_iff. exists fs. intuition.
    apply enum_tuple_complete. apply Is_ok.
  Qed.

End RootSemLab.

Module RootLabProps (RL : RootLab).

  Module FSL := RootSemLab RL.

  Include (FinSemLabProps FSL).

  Ltac rootlab := semlab.

End RootLabProps.
