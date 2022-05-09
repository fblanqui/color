(**
CoLoR, a Coq library on rewriting and termination.

See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2013-07-30

* Interpretation of positive inductive data type systems

as computability predicates so that the accessible arguments (that
must satisfy some positivity condition) of a computable constructor
term are computable.
*)

Set Implicit Arguments.

From Coq Require Import IndefiniteDescription Structures.OrderedType.
From CoLoR Require Import LogicUtil SN LCompSimple Tarski VecUtil SetUtil
     RelUtil.
From CoLoR Require Union SetUtil RelUtil AccUtil.


(****************************************************************************)
(** * Accessible supterm relation. *)

Module Export Def.

  Section supterm_acc.

    Variables F X : Type.
    Notation Fun := (@Fun F X).
    Notation Te := (@Te F X).

    Variable So : Type.
    Notation Ty := (@Ty So).

    Variable typ : F -> Ty.
    Notation TypArgs := (@TypArgs F X So typ).

    Variables (Acc : F -> set nat)
      (Acc_arity : forall f i, Acc f i -> i < arity (typ f)).

    Inductive supterm_acc : relation Te :=
    | stacc_intro : forall f (ts : TypArgs f) i (hi : Acc f i),
      supterm_acc (apps (Fun f) ts) (Vnth ts (Acc_arity hi)).

    Lemma stacc_intro' f (ts : TypArgs f) i (hi : Acc f i) t u :
      t = apps (Fun f) ts -> u = Vnth ts (Acc_arity hi) -> supterm_acc t u.

    Proof. intros e1 e2. subst. apply stacc_intro. Qed.

  End supterm_acc.

End Def.

(****************************************************************************)
(** * Structure on base types for defining their interpretation as computability predicates. *)

Module Type BI_Struct.

  (** We assume given an ST structure. *)

  Declare Module Export ST : ST_Struct.

  (** We assume given a decidable total ordering structure on base
  types. *)

  Declare Module Export BOrd : OrderedType
  with Definition t := So
  with Definition eq := @Logic.eq So.

  Infix "<B" := lt (at level 70).
  Notation gtB := (transp lt) (only parsing).
  Infix ">B" := gtB (at level 70).

  (** We assume that [ltB] is well-founded (in Coq sense). *)

  Parameter ltB_wf : well_founded lt.

  (** For each symbol [f : T_0 ~~> .. ~~> T_{n-1} -> A], we assume
     given a set [Acc f] of accessible argument positions [i] between
     [0] and [n-1] such that, for every base type [B] occurring in
     [T_i], either [B] is smaller than [A], or [B] is equivalent to
     [A] and occurs only positively in [T_i]. *)

  Parameter Acc : F -> set nat.
  Parameter Acc_arity : forall f i, Acc f i -> i < arity (typ f).
  Parameter Acc_ok : forall f i (hi : Acc f i) a,
    occurs a (Vnth (inputs (typ f)) (Acc_arity hi)) ->
    a <B output_base (typ f)
    \/ (a = output_base (typ f)
      /\ pos a (Vnth (inputs (typ f)) (Acc_arity hi))).

  Arguments Acc_ok [f i hi a] _.

  (** Notations. *)

  Notation aeq := (@aeq F X FOrd.eq_dec XOrd.eq_dec ens_X var_notin).
  Notation vaeq := (Vforall2 aeq).
  Notation supterm_acc := (@supterm_acc F X So typ Acc Acc_arity).

End BI_Struct.

(****************************************************************************)
(** * Definition of the interpretation of base types

given an ST structure for terms, a CP structure for the rewrite
relation, and a BI structure. *)

Module Make (Export ST : ST_Struct)
  (Export CP : CP_Struct with Module L := ST.L)
  (Export BI : BI_Struct with Module ST := ST).

  Module Import P := OrderedTypeFacts BOrd.
  Module Export CS := LCompSimple.Make ST CP.

  (*COQ: why is it needed?*)
  Infix "=>R" := (clos_aeq (clos_mon Rh)).
  Infix "=>R*" := (R_aeq*).

(****************************************************************************)
(** ** Properties of [supterm_acc]. *)

  Lemma supterm_acc_supterm : supterm_acc << supterm!.

  Proof. intros t u [f ts i hi]. apply supterm_nth. Qed.

  Lemma supterm_acc_wf : WF supterm_acc.

  Proof.
    eapply WF_incl. apply supterm_acc_supterm. apply WF_tc. apply supterm_wf.
  Qed.

  #[global] Instance size_subpterm_acc : Proper (supterm_acc --> Peano.lt) size.

  Proof. intros t u tu. inversion tu; subst. apply size_apps_r_nth. Qed.

  Lemma supterm_acc_size : supterm_acc << transp (ltof size).

  Proof. intros t u tu. apply size_subpterm_acc. hyp. Qed.

  Lemma aeq_supterm_acc_commut : aeq @ supterm_acc << supterm_acc @ aeq.

  Proof.
    intros t u [t' [tt' t'u]]. inversion t'u; clear t'u; subst.
    inv_aeq tt'; subst. exists (Vnth us (Acc_arity hi)). split.
    apply stacc_intro. apply Vforall2_elim_nth. hyp.
  Qed.

  Lemma aeq_tc_supterm_acc_commut :
    aeq @ (supterm_acc!) << (supterm_acc!) @ aeq.

  Proof. apply commut_tc_inv. apply aeq_supterm_acc_commut. Qed.

  Lemma supterm_acc_subs : forall s t u,
    supterm_acc t u -> supterm_acc (subs s t) (subs s u).

  Proof.
    intros s t u tu. inversion tu; clear tu; subst.
    rewrite subs_apps, <- Vnth_map. apply stacc_intro.
  Qed.

  Lemma tc_supterm_acc_subs : forall s t u,
    supterm_acc! t u -> supterm_acc! (subs s t) (subs s u).

  Proof.
    intros s t u tu. revert t u tu; induction 1.
    apply t_step. apply supterm_acc_subs. hyp.
    trans (subs s y); fo.
  Qed.

  Section tc_supterm_acc_R_mon_wf.

    Variables (R : relation Te) (R_mon : Monotone R).

    Lemma supterm_acc_R_mon_commut : supterm_acc @ R << R @ supterm_acc.

    Proof.
      intros t v [u [tu uv]]. inversion tu; clear tu; subst.
      exists (apps (Fun f) (Vreplace ts (Acc_arity hi) v)).
      split. (*COQ:rewrite <- (Vreplace_nth_eq ts (Acc_arity hi)) at 1.*)
      set (ts' := Vreplace ts (Acc_arity hi) v).
      rewrite <- (Vreplace_nth_eq ts (Acc_arity hi)). unfold ts'. mon.
      rewrite <- (Vnth_replace (Acc_arity hi) (Acc_arity hi) ts v) at 2.
      apply stacc_intro.
    Qed.

    Lemma tc_supterm_acc_R_mon_commut : supterm_acc! @ R << R @ supterm_acc!.

    Proof. apply commut_tc. apply supterm_acc_R_mon_commut. Qed.

    Lemma tc_supterm_acc_R_mon_wf : WF R -> WF (supterm_acc! U R).

    Proof.
      intro R_wf. apply Union.WF_union_commut.
      apply WF_tc. apply supterm_acc_wf. hyp.
      apply tc_supterm_acc_R_mon_commut.
    Qed.

    Import RelUtil.

    Section restrict.

      Variables (P : set Te) (P_R : Proper (R ==> impl) P).

      Lemma restrict_tc_supterm_acc_R_mon_wf :
        WF (restrict P R) -> WF (restrict P (supterm_acc! U R)).

      Proof.
        intro R_wf. rewrite restrict_union. apply Union.WF_union_commut.
        apply wf_restrict_sn. intros t ht. apply WF_tc. apply supterm_acc_wf.
        hyp. intros t v [u [[ht tu] [hu uv]]].
        assert (a : (supterm_acc! @ R) t v). exists u. fo.
        destruct (tc_supterm_acc_R_mon_commut a) as [u' [tu' u'v]]. exists u'.
        split; split; auto. eapply P_R. apply tu'. hyp.
      Qed.

    End restrict.

    Lemma restrict_SN_tc_supterm_acc_R_mon_wf :
      WF (restrict (SN R) (supterm_acc! U R)).

    Proof.
      apply restrict_tc_supterm_acc_R_mon_wf. class.
      apply wf_restrict_sn. refl.
    Qed.

  End tc_supterm_acc_R_mon_wf.

(****************************************************************************)
(** ** Properties of [clos_aeq supterm_acc]. *)

  Lemma clos_aeq_supterm_acc_wf : WF (clos_aeq supterm_acc).

  Proof. apply clos_aeq_wf_size. apply supterm_acc_size. Qed.

  #[global] Instance clos_aeq_tc_supterm_cc_trans : Transitive (clos_aeq (supterm_acc!)).

  Proof.
    rewrite <- trans_intro. rewrite clos_aeq_eq, !comp_assoc.
    rewrite (commut_comp (tc_supterm_acc_R_mon_commut (R:=aeq) _)), !comp_assoc.
    rewrite (commut_comp (tc_supterm_acc_R_mon_commut (R:=aeq) _)), !comp_assoc.
    rewrite !(comp_incl_assoc (trans_comp_incl _)). refl.
  Qed.

  Lemma clos_aeq_tc_supterm_acc_eq :
    clos_aeq (supterm_acc!) == (clos_aeq supterm_acc)!.

  Proof.
    split.
    (* << *)
    intros t u tu. inversion tu; clear tu; subst.
    revert u' v' H1 t H u H0; induction 1; intros t tt' u uu'.
    apply t_step. eapply clos_aeq_intro. apply tt'. apply uu'. hyp.
    trans y; firstorder auto with crelations.
    (* >> *)
    apply tc_min. 2: class. apply clos_aeq_incl. apply incl_tc. refl.
  Qed.

  Lemma clos_aeq_tc_supterm_acc_wf : WF (clos_aeq (supterm_acc!)).

  Proof.
    apply clos_aeq_wf_size. apply tc_incl_trans. apply transp_trans. class.
    apply supterm_acc_size.
  Qed.

  Lemma clos_aeq_tc_supterm_acc_subs : forall s t u,
    clos_aeq (supterm_acc!) t u ->
    clos_aeq (supterm_acc!) (subs s t) (subs s u).

  Proof.
    intros s t u tu.
    destruct (clos_aeq_inv tu) as [t' [u' [tt' [uu' t'u']]]]; clear tu.
    rewrite tt', uu'. apply clos_aeq_intro_refl.
    apply tc_supterm_acc_subs. hyp.
  Qed.

  Section clos_aeq_tc_supterm_acc_R_mon_wf.

    Variables (R : relation Te) (R_mon : Monotone R)
      (R_aeq : Proper (aeq ==> aeq ==> impl) R).

    Lemma clos_aeq_supterm_acc_R_mon_commut :
      clos_aeq supterm_acc @ R << R @ clos_aeq supterm_acc.

    Proof.
      intros t v [u [tu uv]].
      inversion tu; clear tu; subst; rename u' into t'; rename v' into u'.
      assert (a : (supterm_acc @ R) t' v). exists u'. rewrite H0 in uv. fo.
      destruct (supterm_acc_R_mon_commut R_mon a) as [w [t'w wv]].
      exists w. split. rewrite H. hyp. apply clos_aeq_intro_refl. hyp.
    Qed.

    Lemma clos_aeq_tc_supterm_acc_R_mon_commut :
      clos_aeq (supterm_acc!) @ R << R @ clos_aeq (supterm_acc!).

    Proof.
      rewrite clos_aeq_tc_supterm_acc_eq. apply commut_tc.
      apply clos_aeq_supterm_acc_R_mon_commut.
    Qed.

    Lemma clos_aeq_tc_supterm_acc_R_mon_wf :
      WF R -> WF (clos_aeq (supterm_acc!) U R).

    Proof.
      intro R_wf. apply Union.WF_union_commut.
      apply clos_aeq_tc_supterm_acc_wf. hyp.
      apply clos_aeq_tc_supterm_acc_R_mon_commut.
    Qed.

    Import SetUtil RelUtil.

    Section restrict.

      Variables (P : set Te) (P_R : Proper (R ==> impl) P).

      Lemma restrict_clos_aeq_tc_supterm_acc_R_mon_wf :
        WF (restrict P R) -> WF (restrict P (clos_aeq (supterm_acc!) U R)).

      Proof.
        intro R_wf. rewrite restrict_union. apply Union.WF_union_commut.
        apply wf_restrict_sn. intros t ht. apply clos_aeq_tc_supterm_acc_wf.
        hyp. intros t v [u [[ht tu] [hu uv]]].
        assert (a : (clos_aeq (supterm_acc!) @ R) t v). exists u. fo.
        destruct (clos_aeq_tc_supterm_acc_R_mon_commut a) as [u' [tu' u'v]].
        exists u'. split; split; auto. eapply P_R. apply tu'. hyp.
      Qed.

    End restrict.

    Lemma restrict_SN_clos_aeq_tc_supterm_acc_R_mon_wf :
      WF (restrict (SN R) (clos_aeq (supterm_acc!) U R)).

    Proof.
      apply restrict_clos_aeq_tc_supterm_acc_R_mon_wf. class.
      apply wf_restrict_sn. refl.
    Qed.

  End clos_aeq_tc_supterm_acc_R_mon_wf.

(****************************************************************************)
(** ** Interpretation of types

The interpretation [I] will be defined by well-founded induction
on [ltB] using Coq's corresponding combinator [Wf.Fix], which requires
a function [F] computing the interpretation of a base type [a] from
the interpretation [I_lt_a] for each base type strictly smaller than
[a]. The interpretation of [a] itself is defined as the least fixpoint
of some variant of the following monotone function [G]. *)

  Import SetUtil AccUtil.

  Section fixpoint.

    Variable a : So.

    Definition G I : set Te := fun t =>
      SN R_aeq t /\ forall f, output_base (typ f) = a ->
        forall ts : Tes (arity (typ f)), R_aeq* t (apps (Fun f) ts) ->
          forall i (hi : Acc f i),
            int I (Vnth (inputs (typ f)) (Acc_arity hi))
                  (Vnth ts (Acc_arity hi)).

    Variable I_lt_a : forall b, b <B a -> set Te.

    Definition update (X : set Te) b :=
      match BOrd.compare b a with
        | LT h => I_lt_a h
        | EQ _ => X
        | GT _ => SN R_aeq
      end.

    Definition G' X := G (update X).

    Definition F := lfp subset set_glb G'.

  End fixpoint.

  Definition I : So -> set Te := Fix ltB_wf F.

(** We now check that [G] is monotone. *)

  Section G'_props.

    Variables (a : So) (I_lt_a : forall b, b <B a -> set Te).

    Global Instance G'_mon : Proper (subset ==> subset) (G' I_lt_a).

    Proof.
      intros X Y XY t [snt ht]. split. hyp. intros f hf ts h i hi.
      apply int_pos with (I:=update I_lt_a X) (a:=a). apply BOrd.eq_dec.
      (* [update X a [= update Y a] *)
      unfold update. destruct (BOrd.compare a a). refl. hyp. refl.
      intros b n. unfold update. destruct (BOrd.compare b a). refl. fo. refl.
      (* [pos a Ti] *)
      set (Ti := Vnth (inputs (typ f)) (Acc_arity hi)).
      destruct (occurs_dec BOrd.eq_dec a Ti).
      destruct (Acc_ok o) as [l|[_ l]].
      rewrite hf in l. apply BOrd.lt_not_eq in l. unfold BOrd.eq in l. cong.
      hyp.
      apply not_occurs_pos. hyp.
      (* [int (update X) ti Ti] *)
      apply ht; hyp.
    Qed.

    Global Instance G'_equiv : Proper (equiv ==> equiv) (G' I_lt_a).

    Proof.
      intros X Y. rewrite 2!equiv_elim. intros [XY YX]. split.
      rewrite XY. refl. rewrite YX. refl.
    Qed.

  End G'_props.

(** We also check that [G] and [F] are compatible with [equiv]. *)

  Section G_ext.

    Variables (a : So) (I J : So -> set Te)
      (e : forall b, ~b >B a -> I b [=] J b).

    Lemma G_ext : G a I [=] G a J.

    Proof.
      intro t. apply iff_and. split. refl.
      cut (forall f, output_base (typ f) = a ->
        forall ts : Tes (arity (typ f)), t =>R* apps (Fun f) ts ->
          forall i (hi : Acc f i),
            int I (Vnth (inputs (typ f)) (Acc_arity hi))
                  (Vnth ts (Acc_arity hi))
        <-> int J (Vnth (inputs (typ f)) (Acc_arity hi))
                  (Vnth ts (Acc_arity hi))).
      intro h1. split.
      intros h2 f hf ts r i hi. rewrite <- h1; auto.
      intros h2 f hf ts r i hi. rewrite h1; auto.
      intros f hf ts r i hi. apply int_equiv. intros b h. apply e.
      destruct (Acc_ok h) as [j|[j1 j2]]. rewrite hf in j. intro k.
      absurd (b <B b). apply lt_antirefl. trans a; hyp.
      subst. apply lt_antirefl.
    Qed.

  End G_ext.

  Section F_ext.

    Variables (a : So) (I_lt_a J_lt_a : forall b, b <B a -> set Te)
      (e : forall b (h : b <B a), I_lt_a h [=] J_lt_a h).

    Lemma G'_ext : forall X Y, X [=] Y -> G' I_lt_a X [=] G' J_lt_a Y.

    Proof.
      intros X Y XY t. unfold G'. apply G_ext. intro b. unfold update.
      destruct (BOrd.compare b a); fo.
    Qed.

    Lemma F_ext : F I_lt_a [=] F J_lt_a.

    Proof.
      unfold F. apply lfp_ext. fo. fo. fo. intro X. apply G'_ext. refl.
    Qed.

  End F_ext.

(** Fixpoint equation satisfied by [I]. *)

  Definition I' a b (_ : b <B a) := I b.

  Arguments I' _ [_] _ _.

  Lemma I_eq_F : forall a, I a [=] F (I' a).

  Proof. intro a. unfold I. rewrite Fix_eq. refl. apply F_ext. Qed.

  Lemma I_eq_G' : forall a, I a [=] G' (I' a) (I a).

  Proof.
    intro a. rewrite I_eq_F at 1. unfold F. rewrite set_lfp_eq. 2: apply G'_mon.
    apply G'_ext. refl. rewrite I_eq_F. refl.
  Qed.

  Lemma I_eq : forall a, I a [=] G a I.

  Proof.
    intro a. rewrite I_eq_G'. unfold G'. apply G_ext. intros b h.
    unfold update. destruct (BOrd.compare b a). refl. rewrite e. refl. fo.
  Qed.

(** We now check that base types are interpreted by computability
predicates. *)

  Section cp.

    Variables (a : So) (I_lt_a : forall b, b <B a -> set Te)
      (I_lt_a_cp_aeq : forall b (h : b<B a), cp_aeq (I_lt_a h))
      (I_lt_a_cp_sn : forall b (h : b<B a), cp_sn (I_lt_a h))
      (I_lt_a_cp_red : forall b (h : b<B a), cp_red (I_lt_a h))
      (I_lt_a_cp_neutral : forall b (h : b<B a), cp_neutral (I_lt_a h))
      (X : set Te) (X_cp_aeq : cp_aeq X) (X_cp_sn : cp_sn X)
      (X_cp_red : cp_red X) (X_cp_neutral : cp_neutral X).

    Lemma G'_cp_aeq : cp_aeq (G' I_lt_a X).

    Proof.
      intros t u tu [ht1 ht2]. split. rewrite <- tu. hyp.
      intros f hf ts. rewrite <- tu. fo.
    Qed.

    Lemma G'_cp_sn : cp_sn (G' I_lt_a X).

    Proof. fo. Qed.

    Lemma G'_cp_red : cp_red (G' I_lt_a X).

    Proof.
      intros t u tu [ht1 ht2]. split. eapply SN_inv. apply tu. hyp.
      intros f hf ts hu. assert (ht : t =>R* apps (Fun f) ts).
      trans u. apply at_step. hyp. hyp. apply ht2; hyp.
    Qed.

    Lemma  G'_cp_neutral :
      (forall f n (ts : Tes n), ~neutral (apps (Fun f) ts)) ->
      cp_neutral (G' I_lt_a X).

    Proof.
      intros hn t ht1 ht2. split.
      apply SN_intro. intros u tu. destruct (ht2 _ tu) as [h _]. hyp.
      intros f hf ts r. destruct (clos_aeq_trans_inv _ r) as [h|[u [h1 h2]]].
      rewrite h in ht1. fo.
      eapply ht2. apply h1. hyp. hyp.
    Qed.

  End cp.

  Lemma I_cp : (forall f n (ts : Tes n), ~neutral (apps (Fun f) ts)) ->
    forall a, cp (I a).

  Proof.
    intros hn a. induction (ltB_wf a) as [a _ IH]. rewrite I_eq_G'.
    constructor. apply G'_cp_aeq. apply G'_cp_sn. apply G'_cp_red.
    apply G'_cp_neutral. hyp.
  Qed.

(** Computability of accessible arguments. *)

  Lemma comp_acc : forall f (ts : Tes (arity (typ f))),
    I (output_base (typ f)) (apps (Fun f) ts) -> forall i (hi : Acc f i),
      int I (Vnth (inputs (typ f)) (Acc_arity hi)) (Vnth ts (Acc_arity hi)).

  Proof.
    intros f ts. set (a := output_base (typ f)).
    (*COQ: rewrite I_eq. does not work here! *)
    gen (I_eq a); unfold equiv, pointwise_relation; intro e; rewrite e; clear e.
    intros [h1 h2] i hi. apply h2; refl.
  Qed.

(** Computability of function symbols. *)

  Lemma comp_fun : (forall f n (ts : Tes n), ~neutral (apps (Fun f) ts)) ->
    forall f (ts : Tes (arity (typ f))), vint I (inputs (typ f)) ts ->
      (forall u, apps (Fun f) ts =>R u -> I (output_base (typ f)) u) ->
      I (output_base (typ f)) (apps (Fun f) ts).

  Proof.
    intros hn f ts hts h. set (a := output_base (typ f)).
    gen (I_cp hn a). intros [a1 a2 a3 a4].
    (*COQ: rewrite I_eq. does not work here! *)
    gen (I_eq a); unfold equiv, pointwise_relation; intro e; rewrite e; clear e.
    split.
    apply SN_intro. fo.
    intros g hg us r i hi. destruct (clos_aeq_trans_inv _ r) as [j|[v [h1 h2]]].
    inv_aeq j; subst. gen (eq_apps_fun_head i0). intro e. subst g.
    apply eq_apps_nb_args_args in i0. subst us0. apply vint_elim_nth.
    (*COQ:rewrite i2.*) eapply vint_vaeq. apply I_cp. hyp. sym. apply i2. hyp.
    gen (h _ h1). fold a. (*COQ: rewrite I_eq.*)
    gen (I_eq a); unfold equiv, pointwise_relation; intro e; rewrite e; clear e.
    intros [i1 i2]. apply i2; hyp.
  Qed.

End Make.
