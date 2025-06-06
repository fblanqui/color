(**
CoLoR, a Coq library on rewriting and termination.

See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2013-08-16

* Function calls
*)

Set Implicit Arguments.

From Stdlib Require Import Morphisms Basics Lexicographic_Product.
From CoLoR Require Import LogicUtil LSimple VecUtil RelUtil VecOrd EqUtil 
  Lexico SN NatUtil.

Module Export Def.

(****************************************************************************)
(** * Abstract definition of function calls and alpha-equivalence on function calls. *)

  Section call.

    (** We assume given a set [F] for function symbols and a set [X] for
       variables. *)

    Variables F X : Type.

    Notation Te := (@Te F X).
    Notation Var := (@Var F X).
    Notation Fun := (@Fun F X).
    Notation Tes := (vector Te).

    (** A [call] is made of a function symbol [f] and a vector of terms. *)

    Record call : Type := mk_call {
      call_fun : F;
      call_nb_args : nat;
      call_args : Tes call_nb_args }.

    (** We assume given a set [So] of type constants. *)

    Variable So : Type.

    Notation Ty := (@Ty So).
    Notation Tys := (vector Ty).

    (** We assume given a type for each function symbol. *)

    Variable typ : F -> Ty.

    Notation TypArgs := (@TypArgs F X So typ).

    (** A [max_call] is a call [mk_call f ts] with [ts] of length
       [arity (typ f)], that is, the maximum number of arguments that
       [f] can take. *)

    Record max_call : Type := build_max_call {
      max_call_call :> call;
      max_call_eq :
        call_nb_args max_call_call = arity (typ (call_fun max_call_call)) }.

    Definition mk_max_call f (ts : TypArgs f) :=
      build_max_call (mk_call f ts) Logic.eq_refl.

    (** Parameters for alpha-equivalence. *)

    Variables (eq_fun_dec : forall x y : F, {x=y}+{~x=y})
      (eq_var_dec : forall x y : X, {x=y}+{~x=y})
      (ens_X : Ens X) (var_notin : Ens_type ens_X -> X).

    Notation aeq := (@aeq F X eq_fun_dec eq_var_dec ens_X var_notin).
    Notation clos_vaeq :=
      (@clos_vaeq F X eq_fun_dec eq_var_dec ens_X var_notin). 

    (** Extension of alpha-equivalence to calls. *)

    Inductive caeq : relation call :=
    | caeq_intro : forall f n (ts us : Tes n),
      Vforall2 aeq ts us -> caeq (mk_call f ts) (mk_call f us).

    Definition mcaeq : relation max_call := caeq.

(****************************************************************************)
(** * Argument reduction relation on terminating calls. *)

(*FIXME: gt_red is similar to caeq: factorize?*)
    Inductive gt_red R : relation call :=
    | gt_red_intro : forall f n (ts us : Tes n),
      restrict (SN (clos_vaeq R)) (clos_vaeq R) ts us ->
      gt_red R (mk_call f ts) (mk_call f us).

(****************************************************************************)
(** * Dependant lexicographic quasi-ordering on calls.

We want to compare two calls [mk_call f ts] and [mk_call g us] by
first comparing [f] and [g] in some quasi-ordering [>=F] whose strict
part [>F] is wellfounded and, in case [f] and [g] are equivalent
modulo [=F], by comparing [ts] and [us] using some lexicographic or
multiset extension of some wellfounded relation on terms. Considering
a quasi-ordering instead of an ordering is necessary to handle
function symbols defined mutually. However, to do this, there are two
difficulties:

1) In the case where we want to compare [ts] and [us]
lexicographically, we have the problem that [ts] and [us] may not have
the same number of arguments. Even if [f] and [g] are Leibniz equal,
[ts] and [us] may have different lengths. To solve this problem, we
propose:

- to use, for each equivalence class modulo [=F], a filter, that is, a
  vector of natural numbers of fixed length indicating which arguments
  should be taken into account in the comparisons;

- to replace each missing argument by some new constant and compare
  arguments by using the option extension [opt] of a relation.

2) The second problem is the formalization of such a relation where
the ordering on arguments depends on the function symbols when
function symbols are not Leibniz equal but only equivalent modulo some
relation [=F]. In this case, the ordering on [f] and the ordering on
[g] are Leibniz distinct and no comparison can be well typed in Coq.
And, indeed, the [lexprod] relation defined in Coq standard library
provides such a dependent lexicographic relation but only when [=F] is
Leibniz equality.

To solve this problem, we assume that there is a type [C] of codes for
each equivalence classes modulo [=F] and a function [code:F->C]
compatible with [=F] providing the code of the equivalence class of
each function symbol.

In fact, we can just assume given [C] and [code:F->C] and forget about
[=F] and [>F], and just consider Leibniz equality and some wellfounded
relation [>C] on [C]. *)

    (** We assume given a type [C] of codes for function symbols (two
       symbols having the same code can be considered as equivalent)
       equipped with a relation [gtC]. *)

    Variables (C : Type) (code : F -> C) (gtC : relation C).

    (** For each code, we assume given a filter, that is, a vector of
       natural numbers indicating which arguments (the 1st argument is
       denoted by 0, etc.) have to be taken into account when
       comparing two function calls. *)

    Variables (filter_arity : C -> nat)
      (filter : forall r, vector nat (filter_arity r)).

    (** We define the ordering on calls by first comparing the codes
       of function symbols and then the arguments. For typing reasons,
       we also use the type [call] for arguments. To this end, we
       reuse the Coq standard library [lexprod] and inverse the
       relations using [transp] (because, for wellfoundedness, CoLoR
       and Coq relations are oriented differently). *)

    Definition gt_call (gt_args : C -> relation call) : relation call :=
      Rof (transp (lexprod (transp gtC) (fun r => transp (gt_args r))))
          (fun c => @existT _ _ (code (call_fun c)) c).

    (** Finally, we define a lexicographic ordering on arguments.

    Given a code [r], [gt_args_lex r] compares two calls [mk_call f
    ts] and [mk_call g us] by filtering [ts] and [us] with
    [Vopt_filter (filter r)] and comparing lexicographically the
    resulting vectors.

    To compare filtered arguments, we use the _irreflexive_ relation
    [opt], with which the value [None] used for missing arguments is
    comparable to no value and thus not to itself. It is important to
    do so because, otherwise, we could get problems when comparing
    partial function calls with non sorted filters. For instance, with
    [filter r = Vcons 2 (Vcons 1 Vnil)], we could have [mk_call f
    (Vcons t1 Vnil) > mk_call f (Vcons u1 Vnil)] since [Vcons None
    (Vcons (Some t1) Vnil) > Vcons None (Vcons (Some u1) Vnil)], and
    [mk_call f (Vcons t1 (Vcons t2 Vnil)) < mk_call f (Vcons u1 (Vcons
    u2 Vnil))] since [Vcons (Some t2) (Vcons (Some t1) Vnil) < Vcons
    (Some u2) (Vcons (Some u1) Vnil)]. But the opposite is necessary
    since a decrease in the computability closure must imply a
    decrease in the induction ordering on maximally applied function
    calls used in the termination proof (see LCompClos). Said
    otherwise, the ordering on function calls must be invariant when
    adding arguments, that is compatible with the definition of
    computability: if [t] is computable then, for all computable term
    [u], [App t u] is computable. Using [opt] makes [Vcons None (Vcons
    (Some t1) Vnil) > Vcons None (Vcons (Some u1) Vnil)] impossible,
    and thus [gt_args_lex] compatible with computability.

    Finally, note that, in this definition, [r] does not need to be a
    code for [f] and [g]. We do this since, for typing reasons, we
    cannot define a relation on vectors of different lengths. *)

    Definition gt_args_lex (gt : relation Te) r : relation call := Rof
      (lexv (opt aeq) (opt gt))
      (fun c => Vopt_filter (filter r) (call_args c)).

  End call.

  Arguments mk_call [F X] _ {call_nb_args} _.
  Arguments mk_max_call [F X So typ] _ _.

End Def.

(****************************************************************************)
(** * Ingredients for defining a DLQO on calls. *)

Module Type DLQO_Struct.

  Declare Module Export ST : ST_Struct.

  (** We assume given a type [C] of codes for function symbols (two
  symbols having the same code can be considered as equivalent). *)

  Parameter C : Type.
  Parameter code : F -> C.

  (** We assume given a wellfounded relation [>C] on codes. *)

  Parameter gtC : relation C.
  Parameter gtC_wf : WF gtC.

  (** For each code, we assume given a filter, that is, a vector of
  natural numbers indicating which arguments have to be taken into
  account when comparing two function calls. *)

  Parameter filter_arity : C -> nat.
  Parameter filter : forall r, vector nat (filter_arity r).

  (** Notations. *)

  Notation gt_call := (@gt_call F X C code gtC).
  Notation gt_args_lex := (@gt_args_lex F X FOrd.eq_dec XOrd.eq_dec ens_X
    var_notin C filter_arity filter).

End DLQO_Struct.

(****************************************************************************)
(** * Properties of [caeq] and [gt_red]. *)

Module Make (Export ST : ST_Struct).

  Module Export A := LAlpha.Make ST.L.

  Notation call := (@call F X).
  Notation mk_call := (@mk_call F X).
  Notation max_call := (@max_call F X So typ).
  Notation max_call_call := (@max_call_call F X So typ).
  Notation mk_max_call := (@mk_max_call F X So typ).
  Notation build_max_call := (@build_max_call F X So typ).
  Notation caeq := (@caeq F X FOrd.eq_dec XOrd.eq_dec ens_X var_notin).
  Notation mcaeq := (@mcaeq F X So typ FOrd.eq_dec XOrd.eq_dec ens_X var_notin).
  Notation gt_red := (@gt_red F X FOrd.eq_dec XOrd.eq_dec ens_X var_notin).

  (** Inversion lemmas and tactics for [caeq]. *)

  Lemma caeq_inv : forall f n (ts : Tes n) g p (us : Tes p),
    caeq (mk_call f ts) (mk_call g us) -> exists f0 n0 (ts1 us1 : Tes n0),
      ts1 ~~~ us1 /\ f0 = f /\ n0 = n /\ existT ts1 = existT ts
                  /\ f = g /\ n = p /\ existT us1 = existT us.

  Proof.
    intros f n ts g p us e. inversion e; clear e; subst. ex g p ts1 us1. fo.
  Qed.

  Ltac inv_caeq r g p :=
    let f0 := fresh "f" in let ts1 := fresh "ts" in let us1 := fresh "us" in
      let h1 := fresh "h" in let h2 := fresh "h" in let h3 := fresh "h" in
        let h4 := fresh "h" in let h5 := fresh "h" in let h6 := fresh "h" in
          let h7 := fresh "h" in let n0 := fresh "n" in
            destruct (caeq_inv r)
              as [f0 [n0 [ts1 [us1 [h1 [h2 [h3 [h4 [h5 [h6 h7]]]]]]]]]];
                subst f0 n0 g p;
                  (apply inj_existT in h4; [subst ts1|exact eq_nat_dec]);
                  (apply inj_existT in h7; [subst us1|exact eq_nat_dec]).

  (** [caeq] and [mcaeq] are equivalence relations. *)

  Global Instance caeq_equiv : Equivalence caeq.

  Proof.
    constructor.
    intros [f n ts]. apply caeq_intro. refl.
    intros [f n ts] [g p us] fg. inv_caeq fg g p. apply caeq_intro. hyp.
    intros [f n ts] [g p us] [h q vs] fg gh. inv_caeq fg g p. inv_caeq gh h q.
    apply caeq_intro. trans us; hyp.
  Qed.

  Global Instance mcaeq_equiv : Equivalence mcaeq.

  Proof.
    unfold Def.mcaeq. constructor.
    intros [c hc]. refl.
    intros [c hc] [d hd] cd. hyp.
    intros [c hc] [d hd] [e he] cd de. trans (build_max_call d hd); hyp.
  Qed.

  (** Properties of [mk_call] amd [mk_max_call]. *)

  Global Instance mk_call_vaeq f n :
    Proper (vaeq ==> caeq) (mk_call f (call_nb_args:=n)).

  Proof. intros ts us e. apply caeq_intro. hyp. Qed.

  Global Instance mk_max_call_vaeq f : Proper (vaeq ==> mcaeq) (mk_max_call f).

  Proof. intros ts us e. apply caeq_intro. hyp. Qed.

  Lemma mk_call_cast : forall f n (ts : Tes n) p (h : n=p),
    mk_call f (Vcast ts h) = mk_call f ts.

  Proof. intros f n ts p h. subst p. rewrite Vcast_refl. refl. Qed.

  (** Inversion lemma and tactic for [gt_red]. *)

  Import RelUtil.

  Lemma gt_red_inv : forall R f n (ts : Tes n) g p (us : Tes p),
    gt_red R (mk_call f ts) (mk_call g us) -> exists f0 n0 (ts1 us1 : Tes n0),
      restrict (SN (clos_vaeq R)) (clos_vaeq R) ts1 us1
      /\ f0 = f /\ n0 = n /\ existT ts1 = existT ts
      /\ f = g /\ n = p /\ existT us1 = existT us.

  Proof.
    intros R f n ts g p us e. inversion e; clear e; subst. ex g p ts1 us1. fo.
  Qed.

  Ltac inv_gt_red r g p :=
    let f0 := fresh "f" in let ts1 := fresh "ts" in let us1 := fresh "us" in
      let h1 := fresh "h" in let h2 := fresh "h" in let h3 := fresh "h" in
        let h4 := fresh "h" in let h5 := fresh "h" in let h6 := fresh "h" in
          let h7 := fresh "h" in let h8 := fresh "h" in let n0 := fresh "n" in
            destruct (gt_red_inv r)
              as [f0 [n0 [ts1 [us1 [[h1 h2] [h3 [h4 [h5 [h6 [h7 h8]]]]]]]]]];
                subst f0 n0 g p;
                  (apply inj_existT in h5; [subst ts1|exact eq_nat_dec]);
                  (apply inj_existT in h8; [subst us1|exact eq_nat_dec]).

  (** [gt_red] is wellfounded. *)

  Lemma gt_red_wf R : WF (gt_red R).

  Proof.
    intros [f n ts]. apply SN_intro. intros [g p us] r. inv_gt_red r g p.
    gen (SN_inv h0 h). clear r h h0 ts.
    revert us; induction 1; rename x into ts.
    apply SN_intro. intros [g p us] r. inv_gt_red r g p. fo.
  Qed.

  (** [gt_red] is invariant by [caeq]. *)

  Global Instance gt_red_caeq R : Proper (caeq ==> caeq ==> impl) (gt_red R).

  Proof.
    intros [f n ts] [f' n' ts'] e [g p us] [g' p' us'] e' h.
    inv_caeq e f' n'. inv_caeq e' g' p'. inv_gt_red h g p. apply gt_red_intro.
    rewrite <- h0, <- h1. fo.
  Qed.

End Make.

(****************************************************************************)
(** * Properties of [gt_call] and [gt_args_lex]. *)

Module Lex (Export CO : DLQO_Struct).

  Module Export M := Make CO.ST.

  Section gt_call.

    Variable gt_args : C -> relation call.

    (** [gt_call] preserves wellfoundedness. *)

    Lemma gt_call_wf : (forall r, WF (gt_args r)) -> WF (gt_call gt_args).

    Proof.
      intro gt_args_wf. apply WF_inverse. apply wf_WF_transp. apply wf_lexprod.
      apply WF_wf_transp. apply gtC_wf.
      intro r. apply WF_wf_transp. apply gt_args_wf.
    Qed.

    (** [gt_call] preserves compatibility with [caeq]. *)

    Global Instance gt_call_caeq :
      (forall r, Proper (caeq ==> caeq ==> impl) (gt_args r)) ->
      Proper (caeq ==> caeq ==> impl) (gt_call gt_args).

    Proof.
      intros gt_args_caeq [f n ts] [f' n' ts'] hf [g p us] [g' p' us'] hg.
      inv_caeq hf f' n'. inv_caeq hg g' p'.
      unfold impl, Def.gt_call, Rof, transp.
      intro l; inversion l; clear l; subst; simpl.
      apply left_lex. hyp.
      rewrite H2. apply right_lex. eapply gt_args_caeq.
      3: rewrite <- H2; apply H0. hyp. hyp.
    Qed.

  End gt_call.

  Section gt_args_lex.

    Variables (gt : relation Te) (gt_aeq : Proper (aeq ==> aeq ==> impl) gt).

    (** [gt_args_lex] preserves wellfoundedness. *)

    Lemma gt_args_lex_wf : WF gt -> forall r, WF (gt_args_lex gt r).

    Proof.
      intros gt_wf r. apply WF_inverse. apply lexv_wf. apply wf_opt; hyp. class.
      apply opt_absorbs_left. intros t u [t' [tt' t'u]]. rewrite tt'. hyp.
    Qed.

    (** [gt_args_lex] preserves compatibility with [caeq]. *)

    Global Instance gt_args_lex_caeq r :
      Proper (caeq ==> caeq ==> impl) (gt_args_lex gt r).

    Proof.
      intros [f n ts] [f' n' ts'] hf [g p us] [g' p' us'] hg; unfold impl.
      unfold Def.gt_args_lex, Rof. simpl. set (M := CO.filter r).
      inv_caeq hf f' n'. inv_caeq hg g' p'. rewrite !lexv_eq.
      intros [i [i1 [i2 i3]]]. ex i i1. split.
      (* i-th argument is decreasing. *)
      revert i2. rewrite !Vnth_opt_filter.
      destruct (lt_dec (Vnth M i1) n); destruct (lt_dec (Vnth M i1) p);
        intro i2; inversion i2; clear i2; subst. apply opt_intro.
      rewrite <- (Vforall2_elim_nth _ h), <- (Vforall2_elim_nth _ h0). hyp.
      (* for j < i, j-th argument is equivalent. *)
      intros j ji jr. gen (i3 _ ji jr). rewrite !Vnth_opt_filter.
      destruct (lt_dec (Vnth M jr) n); destruct (lt_dec (Vnth M jr) p);
        intro j2; inversion j2; clear j2; subst. apply opt_intro.
      rewrite <- (Vforall2_elim_nth _ h), <- (Vforall2_elim_nth _ h0). hyp.
    Qed.

    (** [gt_args_lex S r] absorbs [gt_red R] if [S] is transitive,
    compatible with [aeq] and contains [restrict (SN (clos_aeq R))
    (clos_aeq R)]. **)

    Import RelUtil.

    Lemma gt_args_lex_absorbs_gt_red R S r :
      Proper (aeq ==> aeq ==> impl) S -> Transitive S ->
      restrict (SN (clos_aeq R)) (clos_aeq R) << S ->
      gt_args_lex S r @ gt_red R << gt_args_lex S r.

    Proof.
      intros S_aeq S_trans RS [f n ts] [g' p' vs] [[g p us] [h1 h2]].
      (* We simplify [h2]. Let [j] be the position in [us] at which the
      reduction occurs. *)
      inv_gt_red h2 g' p'. destruct h0 as [us' [usus' [vs' [h0 vs'vs]]]].
      rewrite Vrel1_nth_iff in h0. destruct h0 as [j [j1 [j2 j3]]].
      (* We prove that [S (Vnth us j1) (Vnth vs j1)]. *)
      assert (a : S (Vnth us j1) (Vnth vs j1)). apply RS.
      split. apply sn_clos_vaeq_elim. hyp.
      eapply clos_aeq_intro. 3: apply j2.
      apply Vforall2_elim_nth. hyp. apply Vforall2_elim_nth. hyp.
      (* We simplify [h1]. Let [i] be the position in [M:= CO.filter r]
      at which the decrease occurs. *)
      revert h1. unfold Def.gt_args_lex, Rof. simpl. set (M := CO.filter r).
      rewrite !lexv_eq. intros [i [i1 [i2 i3]]].
      case_eq (Vfirst_position (eq_nat_dec j) M).
      (* Case when [k] is the first position of [j] in [M]. *)
      intros k hk. destruct (lt_dec k i).
      (* k < i *)
      assert (kr : k < filter_arity r). lia. ex k kr. split.
      (* Proof that the k-th argument decrease. *)
      gen (i3 _ l kr).
      rewrite !Vnth_opt_filter, <- (Vnth_first_position (eq_nat_dec j) hk).
      destruct (lt_dec j n); destruct (lt_dec j p); try lia;
        intro i3k; inversion i3k; clear i3k; subst; apply opt_intro.
      rewrite H1, Vnth_eq with (h2:=j1), Vnth_eq with (h1:=l1) (h2:=j1); auto.
      (* Proof that the arguments m<k are equivalent. *)
      intros m mk mr. assert (mi : m < i). lia. gen (i3 _ mi mr).
      rewrite !Vnth_opt_filter. set (q := Vnth M mr).
      destruct (lt_dec q n); destruct (lt_dec q p); try lia;
        intro i3k; inversion i3k; clear i3k; subst; apply opt_intro.
      rewrite H1, (Vforall2_elim_nth _ usus'),
        <- (Vforall2_elim_nth _ vs'vs), j3.
      refl.
      intro b. symmetry in b. gen (Vfirst_position_nth (eq_nat_dec j) hk b).
      lia.
      (* k >= i *)
      ex i i1. split.
      (* Proof that the i-th argument decrease. *)
      revert i2. rewrite !Vnth_opt_filter. set (q := Vnth M i1).
      destruct (lt_dec q n); destruct (lt_dec q p);
        intro i2; inversion i2; clear i2; subst; apply opt_intro.
      destruct (eq_nat_dec k i).
      (* k = i *)
      subst. assert (b : j = q). eapply Vnth_first_position. apply hk.
      rewrite !Vnth_eq with (h1:=j1) (h2:=l0) in a; auto.
      apply S_trans with (Vnth us l0); hyp.
      (* k > i *)
      rewrite <- (Vforall2_elim_nth _ vs'vs), <- j3,
        <- (Vforall2_elim_nth _ usus').
      hyp.
      intro b. symmetry in b. gen (Vfirst_position_nth (eq_nat_dec j) hk b).
      lia.
      (* Proof that the arguments m<i are equivalent. *)
      intros m mi mr. gen (i3 _ mi mr).
      rewrite !Vnth_opt_filter. set (q := Vnth M mr).
      destruct (lt_dec q n); destruct (lt_dec q p); try lia;
        intro i3k; inversion i3k; clear i3k; subst; apply opt_intro.
      rewrite H1, (Vforall2_elim_nth _ usus'),
        <- (Vforall2_elim_nth _ vs'vs), j3.
      refl.
      intro b. symmetry in b. gen (Vfirst_position_nth (eq_nat_dec j) hk b).
      lia.
      (* Case when [j] does not occur in [M]. *)
      ex i i1. split.
      (* Proof that the i-th argument decrease. *)
      revert i2. rewrite !Vnth_opt_filter. set (q := Vnth M i1).
      destruct (lt_dec q n); destruct (lt_dec q p);
        intro i2; inversion i2; clear i2; subst; apply opt_intro.
      rewrite <- (Vforall2_elim_nth _ vs'vs), <- j3, <- (Vforall2_elim_nth _ usus').
      hyp.
      intro. subst j. assert (b : Vin q M). apply Vnth_in.
      destruct (Vin_first_position eq_nat_dec b) as [i0 hi0].
      rewrite H in hi0. discr.
      (* Proof that the arguments m<i are equivalent. *)
      intros m mi mr. gen (i3 _ mi mr).
      rewrite !Vnth_opt_filter. set (q := Vnth M mr).
      destruct (lt_dec q n); destruct (lt_dec q p); try lia;
        intro i3k; inversion i3k; clear i3k; subst; apply opt_intro.
      rewrite H2, (Vforall2_elim_nth _ usus'),
        <- (Vforall2_elim_nth _ vs'vs), j3.
      refl.
      intro. subst j. assert (b : Vin q M). apply Vnth_in.
      destruct (Vin_first_position eq_nat_dec b) as [i0 hi0].
      rewrite H in hi0. discr.
    Qed.

  End gt_args_lex.

End Lex.
