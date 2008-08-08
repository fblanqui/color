(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2008-05-19

decomposition of an over DP graph
*)

Set Implicit Arguments.

Require Export AGraph.
Require Export Union.

Section S.

Variable Sig : Signature.

Notation term := (term Sig). Notation terms := (vector term).
Notation rule := (rule Sig). Notation rules := (list rule).

(***********************************************************************)
(** we consider the relation (hd_red_Mod S R) *)

Variable S : relation term.
Variable R : rules.

(***********************************************************************)
(** a decomposition of a list of rules is a list of list of rules *)

Notation decomp := (list rules).

(***********************************************************************)
(** we assume given a decidable graph on rules *)

Variable g : rule -> rule -> bool.
Definition G x y := g x y = true.

(***********************************************************************)
(** we assume that G is an over graph of (hd_rules_graph S R) *)

Variable hypG : hd_rules_graph S R << G.

(***********************************************************************)
(** a decomposition cs = [c1; ..; cn] is valid wrt R if for all i, for
all rule b in li, for all j > i, and for all rule c in lj, there is no
edge from b to c *)

Fixpoint valid_decomp (cs : decomp) : bool :=
  match cs with
    | nil => true
    | ci :: cs' => valid_decomp cs' &&
      forallb (fun b =>
        forallb (fun cj =>
          forallb (fun c => negb (g b c)) cj)
        cs')
      ci
  end.

(***********************************************************************)
(** relation corresponding to a decomposition *)

Fixpoint Union (cs : decomp) : relation term :=
  match cs with
    | nil => @empty_rel term
    | ci :: cs' => hd_red_Mod S ci U Union cs'
  end.

Lemma decomp_incl :
  forall cs (hyp1 : incl R (flat cs)), hd_red_Mod S R << Union cs.

Proof.
intros. intros x y h. redtac. ded (hyp1 _ H0). gen H3.
elim cs; simpl; intros. contradiction. destruct (in_app_or H4).
left. exists t. intuition. subst. apply hd_red_rule. hyp.
right. apply H3. hyp.
Qed.

Lemma In_Union_elim : forall cs x y, Union cs x y ->
  exists ci, In ci cs /\ hd_red_Mod S ci x y.

Proof.
induction cs; simpl; intros. contradiction. destruct H.
exists a. intuition. destruct (IHcs _ _ H). exists x0. intuition.
Qed.

Implicit Arguments In_Union_elim [cs x y].

(***********************************************************************)
(** main theorem *)

Lemma WF_hd_red_Mod_decomp :
  forall (hypR : rules_preserv_vars R)
    (cs : decomp)
    (hypl2 : incl (flat cs) R)
    (hypl3 : valid_decomp cs = true)
    (hypl4 : lforall (fun ci => WF (hd_red_Mod S ci)) cs),
    WF (Union cs).

Proof.
induction cs; simpl; intros. apply WF_empty_rel.
ded (andb_elim hypl3). clear hypl3. intuition. apply WF_union; try hyp.
Focus 2. apply IHcs; try hyp. apply incl_appl_incl with a. hyp.
clear IHcs H0 H1 H2. intros t v h. destruct h. destruct H. redtac.
rewrite forallb_forall in H3. ded (H3 _ H1). clear H3.
destruct (In_Union_elim H0). destruct H3. clear H0. redtac.
rewrite forallb_forall in H5. ded (H5 _ H3). clear H5.
rewrite forallb_forall in H9. ded (H9 _ H6). clear H9.
symmetry in H5. ded (negb_sym _ _ H5). clear H5. simpl in H9.
absurd (G (mkRule l r) (mkRule l0 r0)). unfold G. rewrite H9. discr. clear H9.
apply hypG.
apply hd_red_Mod_rule2_hd_rules_graph with (t := t) (u := x) (v := v);
  unfold hd_red_Mod_rule; subst; intuition. exists s. intuition.
assert (incl x0 R). apply incl_tran with (flat cs). apply In_incl_flat. hyp.
apply incl_appl_incl with a. hyp. apply H2. hyp.
exists s0. intuition.
Qed.

Lemma WF_decomp :
  forall (hypR : rules_preserv_vars R)
    (cs : decomp)
    (hypl1 : incl R (flat cs))
    (hypl2 : incl (flat cs) R)
    (hypl3 : valid_decomp cs = true)
    (hypl4 : lforall (fun ci => WF (hd_red_Mod S ci)) cs),
    WF (hd_red_Mod S R).

Proof.
intros. apply WF_incl with (Union cs). apply decomp_incl. hyp.
apply WF_hd_red_Mod_decomp; hyp.
Qed.

End S.
