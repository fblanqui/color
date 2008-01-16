(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Leo Ducas, 2007-08-06

We give a way to decide of the SCC relation, using the 2 morphisms
Domain bijection and Adjacence Matrix.
*)

Set Implicit Arguments.

Require Export GDomainBij.
Require Export AdjMat.

Section SCC_effectif.

Record TSCC_dec_hyps : Type := mkSCC_dec_hyps {
  hyp_A : Set;
  hyp_A_eq_dec : forall x y : hyp_A, {x=y} + {~x=y};
  hyp_Dom : list hyp_A;
  hyp_R : relation hyp_A;
  hyp_restriction : is_restricted hyp_R hyp_Dom;
  hyp_rp_free: repeat_free hyp_Dom;
  hyp_R_dec : forall x y, {hyp_R x y} + {~hyp_R x y}
}.

Variable hyps : TSCC_dec_hyps.

Notation A:=(hyp_A hyps).
Notation A_eq_dec:=(hyp_A_eq_dec hyps).
Notation Dom:=(hyp_Dom hyps).
Notation R:=(hyp_R hyps).
Notation restriction:=(hyp_restriction hyps).
Notation rp_free:=(hyp_rp_free hyps).
Notation R_dec:=(hyp_R_dec hyps).

Notation dim := (length Dom).

Definition SCC_mat_effective :=
  let M:=matofG dim (domtonat Dom R) (domtonat_dec  Dom R R_dec ) in
  SCC_mat M.

(** The Matrix M is keep as an argument, so main file may only compute
it once *)

Definition SCC_effective M (H : M = SCC_mat_effective) x y :=
  nattodom A_eq_dec Dom (gofmat M) x y.

Lemma SCC_effective_exact : forall M (H : M = SCC_mat_effective) x y,
  SCC R x y <-> SCC_effective H x y.

Proof.
split;intros;unfold SCC_effective in *;unfold SCC_mat_effective in *;
rewrite <- (dom_change_SCC A_eq_dec restriction rp_free x y) in *;
unfold nattodom in *;
destruct (list_find_first (eq x) (A_eq_dec x) Dom);auto with *;
destruct (list_find_first (eq y) (A_eq_dec y) Dom);auto with *;
subst;
rewrite (gofmat_SCC ) in *.
assert ((domtonat Dom R) <<
 (gofmat (matofG dim (domtonat Dom R) (domtonat_dec Dom R R_dec)))).

unfold inclusion;intros;
rewrite mat_G_isom;intros.
deduce (domtonat_is_restricted _ _ _ _ H1).
do 2 rewrite nfirst_exact in H2;trivial.
trivial.
deduce(SCC_incl H);auto.
assert ( (gofmat (matofG dim (domtonat Dom R) 
(domtonat_dec Dom R R_dec))) << (domtonat Dom R)).
unfold inclusion;intros.
rewrite mat_G_isom in H;intros;auto. deduce (domtonat_is_restricted _ _ _ _ H1). 
do 2 rewrite nfirst_exact in H2;trivial. deduce (SCC_incl H).  auto.
Qed.

Lemma SCC_effective_dec : forall M (H: M= SCC_mat_effective) x y,
  {SCC_effective H x y} + {~SCC_effective H x y}.

Proof.
intros. unfold SCC_effective. subst.
unfold nattodom.
destruct (list_find_first (eq x) (A_eq_dec x));auto with *.
destruct (list_find_first (eq y) (A_eq_dec y));auto with *.
apply gofmat_dec.
Defined.

(*
Lemma SCC_dec : forall x y, {SCC _ R x y} + {~SCC _ R x y}.

Proof.
intros.
set (M:= SCC_mat_effective).
assert (M = SCC_mat_effective);auto.
deduce (SCC_effective_dec M H x y).
destruct H0;rewrite <- SCC_effectif_exact in *;tauto.
Qed.
*)

End SCC_effectif.
