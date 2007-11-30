(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Leo Ducas, 2007-08-06

Strongly Connected Components (SCC) of a graph seen as a relation
*)


Set Implicit Arguments.

Require Export Cycle.
Require Export Path.
Require Export ListUtil.

Section S.

Variable A : Set.

Section definition.

Variable R : relation A.

(** Definition of SCC seen as a relation : are x and y in the same SCC ? *) 

Definition SCC x y := R! x y /\ R! y x.

End definition.

(** Basic Properties of SCC *)

Section basic_properties.

Variable R : relation A.

Lemma trans_SCC : forall x y z, SCC R x y -> SCC R y z -> SCC R x z.

Proof.
intros.
unfold SCC in *.
destruct H;destruct H0.
split;eapply t_trans;eauto;auto.
Qed.

Lemma sym_SCC : forall x y, SCC R x y -> SCC R y x.

Proof.
intros.
unfold SCC in *.
destruct H;split;assumption.
Qed.

End basic_properties.

Section inclusion.

Variables R1 R2 : relation A.

Lemma SCC_incl : R1 << R2 -> SCC R1 << SCC R2.

Proof.
intros.
unfold inclusion; unfold SCC.
intros.
destruct H0.
assert ((R1 !) << (R2 !)).
apply incl_tc;assumption.
split;unfold inclusion in H2.
apply (H2 x y); assumption.
apply (H2 y x); assumption.
Qed.

End inclusion.

(** Facts about SCC *)

Section facts.

Variable R : relation A.

Lemma cycle_in_SCC : forall x l, cycle R x l -> forall y, In y l -> SCC R x y.

Proof.
intros.
unfold SCC.
unfold cycle in H.
generalize (in_elim H0) ;intros.
destruct H1;destruct H1;subst.
apply path_app_elim in H.
destruct H.
apply path_clos_trans in H;apply path_clos_trans in H1.
split;auto.
Qed.

Lemma SCC_in_cycles : forall x y, SCC R x y -> exists l, cycle R x l /\ In y l.

Proof.
intros.
destruct H.
apply clos_trans_path in H; apply clos_trans_path in H0.
destruct H;destruct H0.
exists (x0++y::x1).
split;auto with *.
unfold cycle.
apply path_app;auto.
Qed.

Lemma cycle_in_SCC_bound : forall x l, cycle R x l -> SCC R x x.

Proof.
intros;unfold SCC;unfold cycle in H.
split;apply path_clos_trans in H;auto.
Qed.

End facts.

End S.
