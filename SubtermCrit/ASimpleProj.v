(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sidi Ould-Biha & Frederic Blanqui, 2010-04-08

simple projections for the subterm criterion
*)

Set Implicit Arguments.

Require Import ATrs NatUtil BoolUtil VecUtil ListUtil LogicUtil RelUtil SN
  ACompat.

Section S.

Variable Sig : Signature.

Notation term := (term Sig).
Notation rule := (rule Sig). Notation rules := (list rule).

(***********************************************************************)
(** projection definition *)

Variable pi : Sig -> nat.

Definition valid := forall f, arity f > 0 -> pi f < arity f.

(***********************************************************************)
(** projection function *)

Variable Hpi : valid.

Implicit Arguments Hpi [f].

Fixpoint proj t :=
  match t with
    | Var _ => t
    | Fun f ts =>
      match zerop (arity f) with
        | right H => Vnth ts (Hpi H)
        | left H => t
      end
  end.

Definition proj_rule a := mkRule (proj (lhs a)) (proj (rhs a)).

Definition proj_rules := map proj_rule.

Lemma subterm_eq_proj : forall t, subterm_eq (proj t) t.

Proof.
intro. case t. simpl. intro. apply subterm_eq_refl.
simpl. intros. case (zerop (arity f)). intros. apply subterm_eq_refl.
intros. apply subterm_strict. apply subterm_fun. apply Vnth_in.
Qed.

(***********************************************************************)
(** properties wrt substitutions *)

Definition proj_sub s (x : variable) := proj (s x).

Lemma proj_sub_var : forall s n,
  proj (sub s (Var n)) = sub (proj_sub s) (Var n).

Proof.
intros. simpl. auto.
Qed.

Lemma proj_sub_fun : forall s f ts,
  proj (sub s (Fun f ts)) = sub s (proj (Fun f ts)).

Proof.
intros. simpl. case (zerop (arity f)). intros. simpl. refl.
intros. rewrite Vnth_map; auto.
Qed.

Lemma subterm_eq_proj_sub : forall s t,
  subterm_eq (proj (sub s t)) (sub s (proj t)).

Proof.
intros. case t. simpl. intros. apply subterm_eq_proj.
intros. rewrite proj_sub_fun. apply subterm_eq_refl.
Qed.

(***********************************************************************)
(** projection ordering *)

Section proj_ord.

  Variable succ : relation term.

  Definition proj_ord : relation term := fun t u => succ (proj t) (proj u).

  (* preservation of transitivity *)
  Lemma proj_trans : transitive succ -> transitive proj_ord.

  Proof.
    intro. unfold transitive, proj_ord. intros. eapply H. apply H0. hyp.
  Qed.

  (* preservation of wellfoundedness *)
  Lemma WF_proj : WF succ -> WF proj_ord.

  Proof.
    intro. unfold proj_ord. apply (WF_inverse proj H).
  Qed.

  (* compatibility with rules *)
  Lemma compat_proj_ord : forall R : rules,
    compat succ (proj_rules R) -> compat proj_ord R.

  Proof.
    unfold compat. intros. unfold proj_ord. apply H.
    change (In (proj_rule (mkRule l r)) (proj_rules R)).
    apply in_map. hyp.
  Qed.

End proj_ord.

(* monotony wrt inclusion *)
Lemma incl_proj : forall R S, R << S -> proj_ord R << proj_ord S.

Proof.
intros. unfold inclusion, proj_ord. intros. apply H. exact H0.
Qed.

(* properties wrt reflexive closure *)
(*REMOVE:
Section clos_refl.

  Variable succ : relation term.

  Notation proj_ord_eq := (proj_ord succ%).
  Notation proj_ord := (proj_ord succ).

  Lemma refl_proj_ord_eq : reflexive proj_ord_eq.

  Proof.
  unfold reflexive, clos_refl, union. auto.
  Qed.

  Lemma proj_ord_rc_incl_proj_ord_eq : proj_ord% << proj_ord_eq.

  Proof.
  unfold inclusion, clos_refl, union. intros. decomp H. subst y. auto. auto.
  Qed.

End clos_refl.*)

(***********************************************************************)
(** decision procedure for validity *)

Variables (Fs : list Sig) (Fs_ok : forall f, In f Fs).

Definition bvalid :=
  forallb (fun f => beq_nat (arity f) 0 || bgt_nat (arity f) (pi f)) Fs.

Lemma bvalid_ok : bvalid = true <-> valid.

Proof.
unfold valid, bvalid. apply forallb_ok_fintype. 2: hyp.
intro f. rewrite orb_eq. rewrite beq_nat_ok. rewrite bgt_nat_ok. omega.
Qed.

End S.

Implicit Arguments valid [Sig].
Implicit Arguments bvalid [Sig].
Implicit Arguments bvalid_ok [Sig Fs].
Implicit Arguments proj [Sig pi].
Implicit Arguments proj_ord [Sig pi].

Ltac valid Fs_ok := rewrite <- (bvalid_ok _ Fs_ok);
  (check_eq || fail 10 "invalid simple projection").