(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Leo Ducas, 2007-08-06

We give a way to decide the SCC relation using the adjacency matrix.
*)

Set Implicit Arguments.

From CoLoR Require Import GDomainBij AdjMat RelSub ListExtras RelUtil
  LogicUtil BoundNat SCC ListNodup.

Record SCC_dec_hyps : Type := mkSCC_dec_hyps {
  hyp_A : Type;
  hyp_eq_dec : forall x y : hyp_A, {x=y} + {~x=y};
  hyp_Dom : list hyp_A;
  hyp_R : relation hyp_A;
  hyp_restriction : is_restricted hyp_R hyp_Dom;
  hyp_nodup: nodup hyp_Dom;
  hyp_R_dec : forall x y, {hyp_R x y} + {~hyp_R x y}
}.

Section SCC_effectif.

  Variable hyps : SCC_dec_hyps.

  Notation A := (hyp_A hyps).
  Notation eq_dec := (hyp_eq_dec hyps).
  Notation Dom := (hyp_Dom hyps).
  Notation R := (hyp_R hyps).
  Notation restriction := (hyp_restriction hyps).
  Notation Dom_nodup := (hyp_nodup hyps).
  Notation R_dec := (hyp_R_dec hyps).
  Notation dim := (length Dom).

  Definition SCC_mat_effective :=
    let M := MoG dim (rel_on_nat Dom R) (rel_on_nat_dec Dom R R_dec) in
    SCC_mat M.

  (* The Matrix M is kept as an argument, so main file may only compute
it once *)

  Definition SCC_effective M (H : M = SCC_mat_effective) x y :=
    rel_on_dom eq_dec Dom (GoM M) x y.

  Lemma SCC_effective_exact : forall M (H : M = SCC_mat_effective) x y,
      SCC R x y <-> SCC_effective H x y.

  Proof.
    split; intros; unfold SCC_effective in *; unfold SCC_mat_effective in *;
    rewrite <- (dom_change_SCC eq_dec restriction Dom_nodup x y) in *;
    unfold rel_on_dom in *;
    destruct (find_first (eq x) (eq_dec x) Dom); auto with *;
    destruct (find_first (eq y) (eq_dec y) Dom); auto with *;
    subst;
    rewrite GoM_SCC in *.
    assert (rel_on_nat Dom R
      << GoM (MoG dim (rel_on_nat Dom R) (rel_on_nat_dec Dom R R_dec))).
    unfold inclusion; intros;
    rewrite GoM_MoG; intros. trivial.
    ded (rel_on_nat_is_restricted _ _ _ _ H1).
    do 2 rewrite <- In_nats_decr_lt in H2; trivial.
    ded (SCC_incl H); auto.
    assert (GoM (MoG dim (rel_on_nat Dom R) (rel_on_nat_dec Dom R R_dec))
                << rel_on_nat Dom R).
    unfold inclusion; intros.
    rewrite GoM_MoG in H; intros; auto.
    ded (rel_on_nat_is_restricted _ _ _ _ H1). 
    do 2 rewrite <- In_nats_decr_lt in H2; trivial. ded (SCC_incl H). auto.
  Qed.

  Lemma SCC_effective_dec : forall M (H : M = SCC_mat_effective) x y,
      {SCC_effective H x y} + {~SCC_effective H x y}.

  Proof.
    intros. unfold SCC_effective. subst.
    unfold rel_on_dom.
    destruct (find_first (eq x) (eq_dec x)); auto with *.
    destruct (find_first (eq y) (eq_dec y)); auto with *.
    apply GoM_dec.
  Defined.

End SCC_effectif.
