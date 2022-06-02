(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2006-04-27

This file contains development concerning convertibility relation
of simply-typed lambda terms. This convertibility relation is an 
extension of alpha-conversion to environments. So terms equal up to
permutation of the order of declarations of ground variables in
environment are identified.   
*)

Set Implicit Arguments.

From CoLoR Require Import RelExtras ListPermutation TermsPos ListUtil
     ListExtras LogicUtil.
From Coq Require Import Compare_dec Max Setoid Morphisms Lia.
From Coq Require Psatz.

Module TermsConv (Sig : TermsSig.Signature).

  Module Export TP := TermsPos.TermsPos Sig.

  Record EnvSubst : Type := build_envSub { 
    envSub:     relation nat;
    size:       nat;
    envSub_dec: forall  i j, {envSub i j} + {~envSub i j};
    envSub_Lok: forall i j j', envSub i j -> envSub i j' -> j = j';
    envSub_Rok: forall i i' j, envSub i j -> envSub i' j -> i = i';
    sizeOk:     forall i j, envSub i j -> i < size /\ j < size
  }.

  Lemma envSubst_dec : forall i Q,
    {j: nat | envSub Q i j} + {forall j, ~envSub Q i j}.

  Proof.
    assert (H: forall s i Q,
      {j: nat | envSub Q i j} + {forall j, j < s -> ~envSub Q i j}).
    induction s.
    right; intros; lia.
    intros.
    destruct (IHs i Q) as [[j Qij] | Qn].
    left; exists j; trivial.
    destruct (envSub_dec Q i s).
    left; exists s; trivial.
    right; intros j js.
    destruct (le_gt_dec s j).
    assert (j_s: j = s); [lia | rewrite j_s; trivial].
    apply Qn; trivial.
    intros i Q.
    destruct (H (size Q) i Q) as [[j Qij] | Qn].
    left; exists j; trivial.
    right; intros j.
    destruct (le_gt_dec (size Q) j).
    intro Qij.
    absurd (j < size Q).
    lia.
    destruct (sizeOk Q i j); trivial.
    apply Qn; trivial.
  Qed.

  Definition envSubst_extends S1 S2 :=
    forall i j, envSub S2 i j -> envSub S1 i j.

  Notation "S1 |=> S2" := (envSubst_extends S1 S2) (at level 70).

  Definition envSubst_eq S1 S2 := S1 |=> S2 /\ S2 |=> S1.

  Notation "S1 <=> S2" := (envSubst_eq S1 S2) (at level 70).
  
  Lemma envSubst_eq_def : forall S1 S2 i j,
    S1 <=> S2 -> (envSub S1 i j <-> envSub S2 i j).

  Proof.
    intros; destruct H; split; intro. apply (H0 i j H1). apply (H i j H1).
  Qed.

  Lemma envSubst_extends_refl : forall S, S |=> S.

  Proof. fo. Qed.

  Lemma envSubst_extends_trans : forall S1 S2 S3,
    S1 |=> S2 -> S2 |=> S3 -> S1 |=> S3.

  Proof. fo. Qed.

  Lemma envSubst_eq_refl : forall S, S <=> S.

  Proof. fo. Qed.

  Lemma envSubst_eq_sym : forall S1 S2, S1 <=> S2 -> S2 <=> S1.

  Proof. fo. Qed.

  Lemma envSubst_eq_trans : forall S1 S2 S3,
    S1 <=> S2 -> S2 <=> S3 -> S1 <=> S3.

  Proof. fo. Qed.

  Global Instance envSubst_eq_Equivalence : Equivalence envSubst_eq.

  Proof.
    split.
    intro x. apply envSubst_eq_refl.
    intros x y. apply envSubst_eq_sym.
    intros x y z. apply envSubst_eq_trans.
  Qed.

  Global Instance envSubst_extends_morph :
    Proper (envSubst_eq ==> envSubst_eq ==> iff) envSubst_extends.

  Proof. fo. Qed.

  Definition emptyEnvSubst: EnvSubst.

  Proof. apply (@build_envSub (fun (x y: nat) => False) 0); fo. Defined.

  Definition singletonEnvSubst : nat -> nat -> EnvSubst.

  Proof.
    intros i j.
    apply (@build_envSub (fun x y => x = i /\ y = j) (S (Max.max i j))). 2-3: firstorder auto with zarith.
    intros i0 j0; destruct (eq_nat_dec i0 i); destruct (eq_nat_dec j0 j); fo.
    intros i0 j0 [ H H0 ]; split.
    rewrite H; auto with arith.
    rewrite H0; auto with arith.
  Defined.

  Definition idEnvSubst : nat -> EnvSubst.

  Proof.
    intro s. apply (@build_envSub (fun x y => x = y /\ x < s) s); firstorder auto with zarith.
    destruct (eq_nat_dec i j).
    destruct (le_gt_dec s i).
    right; lia.
    left; lia.
    right; lia.
  Defined.

  Definition compEnvSubst : forall (E1 E2: Env), E1 [<->] E2 -> EnvSubst.

  Proof.
    intros E1 E2 E1E2.
    apply (@build_envSub (fun x y => 
      x = y /\ 
      (exists A: SimpleType, E1 |= x := A) /\ 
      (exists A: SimpleType, E2 |= x := A)
    ) (max (length E1) (length E2))); split_all.
    destruct (eq_nat_dec i j).
    destruct (isVarDecl_dec E1 i).
    destruct (isVarDecl_dec E2 i).
    left; fo.
    right; intros [_ [_ [A E2i]]]; inversion v; inversion E2i; try_solve.
    right; intros [_ [[A E1i] _]]; inversion v; inversion E1i; try_solve.
    right; intros [ij _]; lia.
    lia. lia.
    apply max_case2; [apply (nth_some E1 i H0) | apply (nth_some E2 i H1)].
    rewrite <- H.
    apply max_case2; [apply (nth_some E1 i H0) | apply (nth_some E2 i H1)].
  Defined.

  Definition sumEnvSubst : forall Q Q1 Q2, Q |=> Q1 -> Q |=> Q2 -> EnvSubst.

  Proof.
    intros Q Q1 Q2 QQ1 QQ2.
    apply (@build_envSub (fun (x y: nat) => envSub Q1 x y \/ envSub Q2 x y) 
      (Max.max (size Q1) (size Q2))).
    intros i j; destruct (envSub_dec Q1 i j); destruct (envSub_dec Q2 i j);
      fo.
    intros i j j' D1 D2; destruct D1; destruct D2; try_solve; 
	solve [
	  apply envSub_Lok with Q i; solve 
	    [ apply QQ1; trivial
	    | apply QQ2; trivial
	  ]
	].
    intros i i' j D1 D2; destruct D1; destruct D2; try_solve;
	solve [
	  apply envSub_Rok with Q j; solve 
	    [ apply QQ1; trivial
	    | apply QQ2; trivial
	  ]
	].
    intros; destruct H.
    split; destruct (sizeOk Q1 i j H); eauto with arith.
    split; destruct (sizeOk Q2 i j H); eauto with arith.
  Defined.

  Lemma sumEnvSubst_or : forall Q Ql Qr (QQl: Q |=> Ql) (QQr: Q |=> Qr) p q,
    envSub (sumEnvSubst QQl QQr) p q -> envSub Ql p q \/ envSub Qr p q.

  Proof. intros; destruct H; auto. Qed.

  Lemma sumEnvSubst_ext_l : forall Q Ql Qr (QQl: Q |=> Ql) (QQr: Q |=> Qr),
    sumEnvSubst QQl QQr |=> Ql.

  Proof. intros; intros p q pq; simpl; auto. Qed.

  Lemma sumEnvSubst_ext_r : forall Q Ql Qr (QQl: Q |=> Ql) (QQr: Q |=> Qr),
    sumEnvSubst QQl QQr |=> Qr.

  Proof. intros; intros p q pq; simpl; auto. Qed.

  Lemma sumEnvSubst_ext : forall Q Ql Qr (QQl: Q |=> Ql) (QQr: Q |=> Qr),
    Q |=> sumEnvSubst QQl QQr.

  Proof. intros; intros p q pq; destruct pq; auto. Qed.

  Definition addEnvSubst : forall (Q: EnvSubst) (i: nat) (j: nat) 
    (ok: envSub Q i j \/ (forall x, ~envSub Q i x /\ ~envSub Q x j)), EnvSubst.

  Proof.
    intros Q i j ok.
    set (s := Max.max (size Q) (Max.max (S i) (S j))).
    apply (@build_envSub (fun (x y: nat) => 
        envSub Q x y \/ (x = i /\ y = j)) s).

    intros.
    destruct (eq_nat_dec i0 i); destruct (eq_nat_dec j0 j); 
      destruct (envSub_dec Q i0 j0); split_all; subst; right; tauto.

    intros; destruct H; destruct H0; try_solve;
      try solve [split_all; subst; auto].
    apply envSub_Lok with Q i0; trivial.
    apply envSub_Lok with Q i0; trivial.
    destruct H0; rewrite H0; rewrite H1.
    destruct ok; trivial.
    rewrite H0 in H.
    destruct (H2 j0); try_solve.
    apply envSub_Lok with Q i0; trivial.
    destruct H; rewrite H, H1.
    destruct ok; trivial.
    rewrite H in H0.
    destruct (H2 j'); try_solve.

    intros; destruct H; destruct H0; try_solve;
      try solve [split_all; subst; auto].
    apply envSub_Rok with Q j0; trivial.
    apply envSub_Rok with Q j0; trivial.
    destruct H0; rewrite H0, H1.
    destruct ok; trivial.
    rewrite H1 in H.
    destruct (H2 i0); try_solve.
    apply envSub_Rok with Q j0; trivial.
    destruct H; rewrite H; rewrite H1.
    destruct ok; trivial.
    rewrite H1 in H0.
    destruct (H2 i'); try_solve.

    intros. destruct H; unfold s.
    split; destruct (sizeOk Q i0 j0 H); eauto with arith.
    destruct H; rewrite H; rewrite H0.
    Import Psatz. lia.
  Defined.

  Definition liftEnvSubst : forall (n: nat) (k: nat) (size: nat), EnvSubst.

  Proof.
    intros n k s.
    apply (@build_envSub (fun x y => 
        x < s /\
        match (le_gt_dec k x) with
	| left _ =>  (* x >= k *) x + n = y
	| right _ => (* x < k *)  x = y
	end) (s + n)); intros; destruct (le_gt_dec k i); try lia.

    destruct (lt_dec i s).
    destruct (eq_nat_dec (i+n) j). auto. right. lia.
    right. lia.

    destruct (lt_dec i s).
    destruct (eq_nat_dec i j). auto. right. lia.
    right. lia.

    destruct (le_gt_dec k i'); lia.

    destruct (le_gt_dec k i'); lia.
  Defined.

  Definition lowerEnvSubst : forall (k: nat) (size: nat), EnvSubst.  

  Proof.
    intros k s.
    apply (@build_envSub (fun x y =>
      x < s /\
      match (eq_nat_dec k x) with
      | left _ => False
      | right _ =>
	match (le_gt_dec k x) with
	| left _ =>  (* x > k *) x = S y
	| right _ => (* x < k *) x = y
	end
      end) (S s));
    intros; destruct (eq_nat_dec k i); destruct (le_gt_dec k i); try lia.

    right. tauto.

    destruct (lt_dec i s).
    destruct (eq_nat_dec i (S j)). auto. right. lia.
    right. lia.

    destruct (lt_dec i s).
    destruct (eq_nat_dec i j). auto. right. lia.
    right. lia.

    destruct (eq_nat_dec k i'); destruct (le_gt_dec k i'); lia.

    destruct (eq_nat_dec k i'); destruct (le_gt_dec k i'); lia.
  Defined.
 
  Definition envSubst_lower : EnvSubst -> EnvSubst.

  Proof.
    intros S; destruct S as [es s es_dec esL esR sOk].
    apply (@build_envSub (fun x y => es (S x) (S y)) (pred s)).
    intros; destruct (es_dec (S i) (S j)); trivial.
    intros. apply eq_add_S. eapply esL. apply H. hyp.
    intros. apply eq_add_S. eapply esR. apply H. hyp.
    intros. gen (sOk (S i) (S j) H). lia.
  Defined.

  Definition envSubst_lift1 : EnvSubst -> EnvSubst.

  Proof.
    intros S; destruct S as [es s es_dec esL esR sOk].
    apply (@build_envSub (fun x y => 
      match x, y with
      | 0, 0 => True
      | S x, S y => es x y
      | _, _ => False
      end
    ) (S s)).
    destruct i; destruct j; auto.
    destruct i; destruct j; destruct j'; try contr.
    refl.
    intros. f_equal. eapply esL. apply H. hyp.
    destruct i; destruct i'; destruct j; try contr.
    refl.
    intros. f_equal. eapply esR. apply H. hyp.
    destruct i; destruct j; try contr.
    lia.
    intro h. gen (sOk i j h). lia.
  Defined.

  Fixpoint envSubst_lift (Q: EnvSubst) (n: nat) : EnvSubst :=
    match n with
    | 0 => Q
    | S x => envSubst_lift1 (envSubst_lift Q x)
    end.

  Lemma envSubst_lift1_ext : forall Q Q',
    Q' |=> Q -> envSubst_lift1 Q' |=> envSubst_lift1 Q.

  Proof.
    intros Q Q' Q'Q p q Qpq.    
    destruct p; destruct q; destruct Q; destruct Q'; fo.
  Qed.

  Lemma envSubst_lift1_ext_rev : forall Q Q',
    envSubst_lift1 Q' |=> envSubst_lift1 Q -> Q' |=> Q.

  Proof.
    intros Q Q' Q'Q p q Qpq.
    assert (Qpq': envSub (envSubst_lift1 Q) (S p) (S q)).
    destruct Q; trivial.
    set (w := Q'Q (S p) (S q) Qpq').
    destruct Q'; trivial.
  Qed.

  Lemma envSubst_lift1_absurdR : forall i Q,
    envSub (envSubst_lift1 Q) 0 (S i) -> False.

  Proof.
    intros i Q p.
    absurd (0 = S i); try_solve.
    apply envSub_Lok with (envSubst_lift1 Q) 0; trivial.
    destruct Q; simpl; trivial.
  Qed.

  Lemma envSubst_lift1_absurdL : forall i Q,
    envSub (envSubst_lift1 Q) (S i) 0 -> False.

  Proof.
    intros i Q p.
    absurd (S i = 0); try_solve.
    apply envSub_Rok with (envSubst_lift1 Q) 0; trivial.
    destruct Q; simpl; trivial.
  Qed.

  Definition envSubst_transp : forall E : EnvSubst, EnvSubst.

  Proof.
    intros S; destruct S as [es s es_dec esL esR sOk].
    apply (@build_envSub (transp es) s).
    intros; destruct (es_dec j i); auto.
    intros. eapply esR. apply H. hyp.
    intros. eapply esL. apply H. hyp.
    intros. gen (sOk j i H). lia.
  Defined.

  Definition envSubst_compose : forall (E1 E2 : EnvSubst), EnvSubst.

  Proof.
    intros E1 E2.
    apply (@build_envSub (fun x y => exists z, envSub E1 x z /\ envSub E2 z y) 
      (max (size E1) (size E2))).
    intros.
    destruct (envSubst_dec i E1) as [[z iz] | nz].
    destruct (envSub_dec E2 z j).
    left; exists z; auto.
    right; intros [w [iw wj]].
    rewrite (envSub_Lok E1 i z w iz iw) in n; auto.
    right; intros [z [iz _]]; apply (nz z); trivial.
    intros i j j' ij ij'.
    inversion ij as [p [ip pj]].
    inversion ij' as [q [iq qj]].
    rewrite (envSub_Lok E1 i p q) in pj; trivial.
    apply (envSub_Lok E2) with q; trivial.
    intros i i' j ij i'j.
    inversion ij as [p [ip pj]].
    inversion i'j as [q [iq qj]].
    rewrite (envSub_Rok E2 p q j) in ip; trivial.
    apply (envSub_Rok E1) with q; trivial.
    intros; destruct H as [z [iz zj]]; split.
    destruct (sizeOk E1 i z iz).
    eauto with arith.
    destruct (sizeOk E2 z j zj).
    eauto with arith.
  Defined.

  Lemma envSubst_transp_def : forall p q Q,
    envSub Q p q -> envSub (envSubst_transp Q) q p.

  Proof. intros; destruct Q; trivial. Qed.

  Lemma envSubst_transp_lower : forall S,
    envSubst_transp (envSubst_lower S) <=> envSubst_lower (envSubst_transp S).

  Proof. intros; constructor; destruct S; fo. Qed.

  Lemma envSubst_transp_lift : forall S,
    envSubst_transp (envSubst_lift1 S) <=> envSubst_lift1 (envSubst_transp S).

  Proof.
    intros; constructor; intros i j; destruct S; destruct i; destruct j; fo.
  Qed.

  Lemma envSubst_transp_twice : forall S,
    envSubst_transp (envSubst_transp S) <=> S.

  Proof. intro S; constructor; intros i j; destruct S; trivial. Qed.

  Lemma envSubst_lift_lower : forall Q,
    envSub Q 0 0 -> envSubst_lift1 (envSubst_lower Q) <=> Q.

  Proof.
    intros; constructor; intros x y;
      destruct Q; destruct x; destruct y; try_solve.
    intro h. assert (0 = S y). eapply envSub_Lok0. apply H. hyp. discr.
    intro h. assert (S x = 0). eapply envSub_Rok0. apply h. hyp. discr.
  Qed.

  Lemma envSubst_lower_lift : forall Q, envSubst_lower (envSubst_lift1 Q) <=> Q.

  Proof. intros; destruct Q; fo. Qed.

  Lemma envSubst_eq_cons : forall S1 S2,
    envSubst_lower S1 <=> envSubst_lower S2 ->
    envSub S1 0 0 -> envSub S2 0 0 -> S1 <=> S2.

  Proof.
    intros S1 S2 S1S2 S10 S20; constructor; intros i j ij; destruct S1;
      destruct S2.
    destruct i; destruct j. auto.
    set (hint := envSub_Lok1 0 0 (S j)); fo; try_solve.
    set (hint := envSub_Rok1 0 (S i) 0); fo; try_solve.
    fo.
    destruct i; destruct j.
    fo.
    set (hint := envSub_Lok0 0 0 (S j)); fo; try_solve.
    set (hint := envSub_Rok0 0 (S i) 0); fo; try_solve.
    fo.
  Qed.

  Lemma envSubst_eq_abs : forall M N (Mabs: isAbs M) (Nabs: isAbs N) 
    (MN: env M [<->] env N) (MNin: env (absBody Mabs) [<->] env (absBody Nabs)),
    envSubst_lift1 (compEnvSubst MN) <=> compEnvSubst MNin.

  Proof.
    intros M N Mabs Nabs MN MNin; constructor; intros i j; term_inv M;
      term_inv N.
    set (hint := MNin 0 A A0).
    destruct i; destruct j; firstorder auto with zarith.
    set (hint := MNin 0 A A0).
    destruct i; destruct j; try contr.
    split_all. ex A. fo. ex A0. fo.
    split_all. subst j. ex x0. fo. ex x. fo.
  Qed.

  Lemma envSubst_lift_eq : forall S1 S2,
    S1 <=> S2 -> envSubst_lift1 S1 <=> envSubst_lift1 S2.

  Proof.
    intros S1 S2 S1S2; constructor; intros i j; destruct S1; destruct S2.
    destruct i; destruct j; fo.
    destruct i; destruct j; fo.
  Qed.

  Lemma envSubst_lift_compose : forall S1 S2, 
    envSubst_lift1 (envSubst_compose S1 S2) <=> 
    envSubst_compose (envSubst_lift1 S1) (envSubst_lift1 S2).

  Proof.
    intros S1 S2; constructor; intros i j; destruct S1; destruct S2.
    destruct i; destruct j; fo; destruct x; fo.
    destruct i; destruct j; try_solve.
    exists 0; fo.
    destruct 1; exists (S x); trivial.
  Qed.

  Lemma lift_liftEnvSubst : forall n k s,
    envSubst_lift1 (liftEnvSubst n k s) <=> liftEnvSubst n (S k) (S s).

  Proof.
    intros n k s; constructor; intros i j.
    destruct i; destruct j; try_solve; try lia.
    destruct (le_gt_dec k i); try_solve; try lia.
    destruct (le_gt_dec k i); try_solve; try lia.
    destruct i; destruct j; try_solve; try lia.
    destruct (le_gt_dec k i); try_solve; lia.
  Qed.

  Lemma lift_lowerEnvSubst : forall k s,
    envSubst_lift1 (lowerEnvSubst k s) <=> lowerEnvSubst (S k) (S s).

  Proof.
    intros k; constructor; intros i j.
    destruct i; destruct j; try_solve.
    destruct (eq_nat_dec (S k) 0); lia.
    destruct (eq_nat_dec (S k) (S i)); try_solve.
    destruct (le_gt_dec k i); try_solve; try lia.
    destruct (eq_nat_dec (S k) (S i)); try_solve.
    destruct (le_gt_dec k i); try_solve; try lia.
    destruct (eq_nat_dec k i); lia.
    destruct (eq_nat_dec k i); lia.
    destruct i; destruct j; try_solve.
    destruct (eq_nat_dec (S k) 0); lia.
    destruct (eq_nat_dec (S k) (S i)); try_solve.
    destruct (eq_nat_dec k i); try_solve.
    destruct (eq_nat_dec k i); try_solve.
    destruct (le_gt_dec k i); try_solve; lia.
  Qed.

  Inductive conv_term: Preterm -> Preterm -> EnvSubst -> Prop :=
  | ConvVar: forall x y S,
      S.(envSub) x y ->
      conv_term (%x) (%y) S
  | ConvFun: forall f S, 
      conv_term (^f) (^f) S
  | ConvAbs: forall A L R S,
      conv_term L R (envSubst_lift1 S) ->
      conv_term (\A => L) (\A => R) S
  | ConvApp: forall LL LR RL RR S,
      conv_term LL RL S ->
      conv_term LR RR S ->
      conv_term (LL @@ LR) (RL @@ RR) S.

  Lemma conv_term_morph_aux :
    forall (x x0 : Preterm) (x1 x2 : EnvSubst),
    x1 <=> x2 -> conv_term x x0 x1 -> conv_term x x0 x2.

  Proof.
    induction x; intros p' E E' EE' convE; inversion convE.
    constructor 1.
    rewrite_lr (envSubst_eq_def x y EE'); trivial.
    constructor 2.
    constructor 3.
    apply IHx with (envSubst_lift1 E); trivial.
    apply envSubst_lift_eq; trivial.
    constructor 4.
    apply IHx1 with E; trivial.
    apply IHx2 with E; trivial.   
  Qed.

  Global Instance conv_term_morph :
    Proper (eq ==> eq ==> envSubst_eq ==> iff) conv_term.

  Proof.
    intros a b ab c d cd E F EF. subst b d. split_all.
    eapply conv_term_morph_aux. apply EF. trivial.
    eapply conv_term_morph_aux. apply envSubst_eq_sym. apply EF. trivial.
  Qed.

  Lemma conv_term_refl : forall M,
    conv_term (term M) (term M) (idEnvSubst (length (env M))).

  Proof.
    destruct M as [E Pt T M]; induction M; simpl.
    constructor 1; simpl; split; trivial.
    apply nth_some with (Some A); trivial.
    constructor 2.
    constructor 3; trivial.
    setoid_replace (envSubst_lift1 (idEnvSubst (length E))) with 
      (idEnvSubst (S (length E))); trivial.
    constructor; intros i j; intros; destruct i; destruct j;
      simpl in *; split_all; try lia.
    constructor 4; trivial.
  Qed.

  Lemma conv_term_comp_refl : forall M N (MN: env M [<->] env N),
    term M = term N -> conv_term (term M) (term N) (compEnvSubst MN).

  Proof.
    intro M; destruct M as [EM PtM TM M].
    induction M; intros N MN MN_term; rewrite <- MN_term; simpl.
    term_inv N.
    constructor 1; repeat split.
    exists A; trivial.
    exists A0; inversion MN_term; trivial.
    constructor 2.
    constructor 3.
    replace (@compEnvSubst E (env N) MN) with 
      (@compEnvSubst (env (buildT (TAbs M))) (env N) MN); trivial.
    destruct N as [??? typingN]; destruct typingN; inversion MN_term.
    assert (EE0: decl A E [<->] decl A0 E0).
    unfold decl; apply env_comp_cons; trivial.
    left; try_solve.
    rewrite (envSubst_eq_abs (buildT (TAbs M)) (buildT (TAbs typingN))
      I I MN EE0).
    set (w := IHM (buildT typingN) EE0); simpl in w.
    rewrite <- H1 in w.
    apply w; trivial.
    constructor 4; term_inv N; inversion MN_term.
    set (w := IHM1 (appBodyL (M:=buildT (TApp T1 T2)) I)).
    rewrite H0 in w; apply w; trivial.
    set (w := IHM2 (appBodyR (M:=buildT (TApp T1 T2)) I)).
    rewrite H1 in w; apply w; trivial.
  Qed.

  Lemma conv_term_sym : forall PtL PtR S, conv_term PtL PtR S ->
    conv_term PtR PtL (envSubst_transp S).

  Proof.
    intros.
    induction H.
    constructor 1; destruct S; trivial.
    constructor 2.
    constructor 3.
    rewrite <- (envSubst_transp_lift S); trivial.
    constructor 4; trivial.
  Qed.

  Lemma conv_term_trans : forall M N P mn np,
    conv_term M N mn -> conv_term N P np ->
    conv_term M P (envSubst_compose mn np).

  Proof.
    intros M N P mn np MN NP; revert P np NP; induction MN;
      intros P np NP; destruct P; inversion NP.
    constructor 1; simpl.
    destruct S; destruct np;
    exists y; split; trivial.
    constructor 2.
    constructor 3.
    rewrite (envSubst_lift_compose S np).
    apply IHMN; trivial.
    constructor 4.
    apply IHMN1; trivial.
    apply IHMN2; trivial.
  Qed.

  Lemma conv_term_lift : forall M n k,
    conv_term (term M) (prelift_aux n (term M) k)
    (liftEnvSubst n k (length (env M))).

  Proof.
    destruct M as [E Pt T M]; induction M; unfold prelift; intros n k; simpl.
    destruct (le_gt_dec k x); constructor; simpl; split;
      try solve 
	[ apply nth_some with (Some A); trivial
	| destruct (le_gt_dec k x); try solve [trivial | lia]
	].
    constructor 2.
    constructor 3.
    rewrite (lift_liftEnvSubst n k (length E)).
    apply IHM.
    constructor 4; trivial.
  Qed.

  Lemma conv_term_lower : forall M k (M0: env M |= k :!),
    conv_term (term M) (prelower_aux (term M) k)
    (lowerEnvSubst k (length (env M))).

  Proof.
    destruct M as [E Pt T M]; induction M; intros k M0; simpl.
    unfold prelower_aux; simpl in * .
    assert (hint: k = x -> False).
    intros; apply varD_UD_absurd with E x A; trivial.
    rewrite <- H; trivial.
    destruct (le_gt_dec k x); constructor; simpl; split; solve 
      [ apply nth_some with (Some A); trivial
      | destruct (eq_nat_dec k x); destruct (le_gt_dec k x); 
	solve [try_solve | lia]
      ].
    constructor 2.
    constructor 3.
    rewrite (lift_lowerEnvSubst k (length E)); try_solve.
    constructor 4.
    apply IHM1; trivial.
    apply IHM2; trivial.
  Qed.

  Lemma conv_term_lifted_aux : forall M N i Q, conv_term M N Q ->
    (forall j, j < i -> Q.(envSub) j j) ->
    conv_term (prelift_aux 1 M i) (prelift_aux 1 N i) (envSubst_lift1 Q).

  Proof.
    intros M N i Q MNQ; gen i; clear i.
    induction MNQ; intros; simpl.
     (* variables *)
    destruct S.
    destruct (le_gt_dec i x).
    destruct (le_gt_dec i y).
    constructor; simpl.
    replace (x + 1) with (S x); [idtac | lia].
    replace (y + 1) with (S y); [trivial | lia].
    absurd (x = y).
    lia.
    apply envSub_Rok0 with y; trivial.
    apply H0; trivial.
    destruct (le_gt_dec i y).
    absurd (x = y).
    lia.
    apply envSub_Lok0 with x; trivial.
    apply H0; trivial.
    destruct (eq_nat_dec x y).
    rewrite <- e.
    constructor.
    destruct x; destruct y; simpl; trivial.
    apply H0; lia.
    apply H0; lia.
    absurd (x = y); trivial.
    apply envSub_Lok0 with x; trivial.
    apply H0; trivial.
     (* function symbol *)
    constructor 2.
     (* abstraction *)
    constructor 3.
    apply IHMNQ.
    intros j ji.
    destruct j.
    destruct S; try_solve.
    destruct S.
    simpl; apply H; lia.
     (* application *)
    constructor 4.
    apply IHMNQ1; trivial.
    apply IHMNQ2; trivial.
  Qed.

  Lemma conv_term_lifted : forall M N Q, conv_term M N Q ->
    conv_term (prelift M 1) (prelift N 1) (envSubst_lift1 Q).

  Proof.
    intros. unfold prelift. apply conv_term_lifted_aux; trivial.
    intros; lia.
  Qed.

  Lemma conv_term_unique : forall M N N' Q,
    conv_term M N  Q -> conv_term M N' Q -> N = N'.

  Proof.
    induction M; intros; inversion H; inversion H0.
    assert (y = y0); auto.
    apply envSub_Lok with Q x; trivial.
    trivial.
    rewrite IHM with R R0 (envSubst_lift1 Q); trivial.
    rewrite (IHM1 RL RL0 Q); trivial.
    rewrite (IHM2 RR RR0 Q); trivial.
  Qed.

  Lemma conv_term_ext : forall M N Q Q',
    conv_term M N Q -> Q' |=> Q -> conv_term M N Q'.

  Proof.
    induction M; intros; destruct N; inversion H.
    constructor; apply H0; trivial.
    constructor.
    constructor.
    eapply IHM; eauto.
    apply envSubst_lift1_ext; trivial.
    constructor.
    eapply IHM1; eauto.
    eapply IHM2; eauto.
  Qed.

  Definition activeEnv_compSubst_on M N x y :=
    forall A, activeEnv M |= x := A <-> activeEnv N |= y := A.

  Definition conv_env (M N: Term) (S: EnvSubst) :=
    forall x y, S.(envSub) x y -> activeEnv_compSubst_on M N x y.

  Global Instance conv_env_morph :
    Proper (eq ==> eq ==> envSubst_eq ==> iff) conv_env.

  Proof.
    intros a b ab c d cd E F EF. subst b d. Set Firstorder Depth 5. fo.
  Qed.

  Lemma conv_env_refl : forall M, conv_env M M (idEnvSubst (length (env M))).

  Proof. intros E x y xy A; split; inversion xy; rewrite H; trivial. Qed.

  Lemma conv_env_sym : forall M N mn,
    conv_env M N mn -> conv_env N M (envSubst_transp mn).

  Proof. intros i j; intros; destruct mn; fo. Qed.

  Lemma conv_env_trans : forall M N P mn np,
    conv_env M N mn -> conv_env N P np -> conv_env M P (envSubst_compose mn np).

  Proof.
    intros; destruct mn; destruct np.
    intros x y xy A; destruct xy as [z [xz zy]].
    split; intro. Set Firstorder Depth 5.
    set (hint := H x z xz); fo.
    set (hint := H0 z y zy); fo.
  Qed. 

  Lemma conv_env_empty : forall M N, conv_env M N emptyEnvSubst.

  Proof. intros M N x y F; try_solve. Qed.

  Lemma terms_conv_var_usage : forall M N Q x y,
    (forall A B, activeEnv M |= x := A -> activeEnv N |= y := B -> A = B) ->
    envSub Q x y -> conv_term (term M) (term N) Q ->
    activeEnv_compSubst_on M N x y.

  Proof.
    destruct M as [E Pt T M]; induction M; intros; inversion H1.
     (* variable *)
    intro A0; unfold VarD.
    term_inv N; split; intro D.
    destruct (@activeEnv_var_det (buildT (TVar v)) x x0 A0); trivial.
    assert (x2 = y).
    inversion H3; rewrite <- H9.
    apply (envSub_Lok Q x y0 y); trivial.
    rewrite <- H6; trivial.
    assert (A0 = A1).
    rewrite H7; simpl.
    apply H.
    simpl in H7.
    rewrite <- H7; rewrite <- H7 in D; trivial.
    change (copy x2 None ++ A1 [#] EmptyEnv) with (activeEnv (buildT (TVar T))).
    apply activeEnv_var_decl; trivial.
    rewrite <- H8; trivial.
    rewrite <- H8; trivial.
    rewrite H8; rewrite H9.
    unfold decl, EmptyEnv; apply nth_after_copy.
    destruct (@activeEnv_var_det (buildT (TVar T)) x2 y A0); trivial.
    assert (x = x0).
    apply (envSub_Rok Q x x0 y); trivial.
    inversion H3.
    rewrite H6; rewrite <- H9; trivial.
    assert (A = A0).
    rewrite H7; simpl.
    apply H.
    change (copy x None ++ A [#] EmptyEnv) with (activeEnv (buildT (TVar v))).
    apply activeEnv_var_decl; trivial.
    rewrite <- H8; trivial.
    rewrite <- H8; trivial.
    simpl in H7.
    rewrite <- H7; rewrite <- H7 in D; trivial.
    rewrite H8; rewrite H9.
    unfold decl, EmptyEnv; apply nth_after_copy.
     (* function symbol *)
    term_inv N; split; destruct x; destruct y; try_solve.
     (* abstraction *)
    intro A1; clear S H3.
    term_inv N.
    assert (Qii: envSub (envSubst_lift1 Q) (S x) (S y)). 
    destruct Q; trivial.
    assert (Conv: conv_term Pt (term (buildT T)) (envSubst_lift1 Q)).
    simpl; inversion H5; rewrite <- H8; trivial.
    assert (Econv: forall A B, 
      activeEnv (buildT M) |= S x := A ->
      activeEnv (buildT T) |= S y := B ->
      A = B).
    intros; apply H.
    apply varD_tail; trivial.
    apply varD_tail; trivial.
    set (hint :=
      IHM (buildT T) (envSubst_lift1 Q) (S x) (S y) Econv Qii Conv A1).
    fold (activeEnv (buildT M)) in *; fold (activeEnv (buildT T)).
    split; intro D.
    apply varD_tail.
    apply (proj1 hint).
    apply varD_tail_rev; trivial.
    apply varD_tail.
    apply (proj2 hint).
    apply varD_tail_rev; trivial.
     (* application *)
    term_inv N; intro A1; simpl.
    fold (activeEnv (buildT M1)) in *; fold (activeEnv (buildT T1)) in * .
    fold (activeEnv (buildT M2)) in *; fold (activeEnv (buildT T2)) in * .
    inversion H4.
    rewrite H9 in H5.
    rewrite H10 in H7.
    assert (EcompL: forall A B,
      activeEnv (buildT M1) |= x := A ->
      activeEnv (buildT T1) |= y := B ->
      A = B).
    intros C D LC RD.
    apply H.
    apply env_sum_ly; trivial.
    apply (activeEnv_app_comp (buildT (TApp M1 M2)) I); trivial.
    apply env_sum_ly; trivial.
    apply (activeEnv_app_comp (buildT (TApp T1 T2)) I); trivial.
    assert (EcompR: forall A B,
      activeEnv (buildT M2) |= x := A ->
      activeEnv (buildT T2) |= y := B ->
      A = B).
    intros C D LC RD.
    apply H.
    apply env_sum_ry; trivial.
    apply env_sum_ry; trivial.
    split; intro D.
    destruct (env_sum_varDecl
      (activeEnv (buildT M1)) (activeEnv (buildT M2)) D) as [[l _] | r].
    apply env_sum_ly.
    exact (@activeEnv_app_comp (buildT (TApp T1 T2)) I y).
    apply (proj1 (IHM1 (buildT T1) Q x y EcompL H0 H5 A1)); trivial.
    apply env_sum_ry.
    apply (proj1 (IHM2 (buildT T2) Q x y EcompR H0 H7 A1)); trivial.
    destruct (env_sum_varDecl
      (activeEnv (buildT T1)) (activeEnv (buildT T2)) D) as [[l _] | r].
    apply env_sum_ly.
    exact (@activeEnv_app_comp (buildT (TApp M1 M2)) I x).
    apply (proj2 (IHM1 (buildT T1) Q x y EcompL H0 H5 A1)); trivial.
    apply env_sum_ry.
    apply (proj2 (IHM2 (buildT T2) Q x y EcompR H0 H7 A1)); trivial.
  Qed.

  Lemma conv_env_absBody : forall M N (Mabs: isAbs M) (Nabs: isAbs N) Q,
    conv_term (term M) (term N) Q -> conv_env M N Q ->
    conv_env (absBody Mabs) (absBody Nabs) (envSubst_lift1 Q).

  Proof.
    intros.
    inversion H; try solve [term_inv M; term_inv N].
    assert (Ecomp: env_comp_on
      (activeEnv (absBody Mabs)) (activeEnv (absBody Nabs)) 0).
    intros B C M0 N0.
    set (Mb := activeEnv_subset (absBody Mabs) M0).
    set (Nb := activeEnv_subset (absBody Nabs) N0).
    rewrite absBody_env in Mb.
    rewrite absBody_env in Nb.
    rewrite (abs_term M Mabs) in H1; inversion H1; rewrite <- H6 in Mb.
    rewrite (abs_term N Nabs) in H2; inversion H2; rewrite <- H8 in Nb.
    inversion Mb; inversion Nb; try_solve.
    intros x y xy B; split.

    destruct x; destruct y; try solve [destruct Q; try_solve].
    set (hint := terms_conv_var_usage (absBody Mabs) (absBody Nabs) Ecomp xy).
    rewrite (absBody_term M Mabs (sym_eq H1)) in hint.
    rewrite (absBody_term N Nabs (sym_eq H2)) in hint.
    apply (proj1 (hint H3 B)).
    term_inv M; term_inv N.
    fold (activeEnv (buildT T)); fold (activeEnv (buildT T0)).
    assert (Qxy: envSub Q x y).
    destruct Q; trivial.
    intro TxA.
    assert (activeEnv Tr0 |= y := B).
    apply (proj1 (H0 x y Qxy B)); trivial.
    simpl; fold (activeEnv (buildT T)).
    apply varD_tail; trivial.
    apply varD_tail_rev; trivial.
    
    destruct x; destruct y; try solve [destruct Q; try_solve].
    set (hint := terms_conv_var_usage (absBody Mabs) (absBody Nabs) Ecomp xy).
    rewrite (absBody_term M Mabs (sym_eq H1)) in hint.
    rewrite (absBody_term N Nabs (sym_eq H2)) in hint.
    apply (proj2 (hint H3 B)).
    term_inv M; term_inv N.
    fold (activeEnv (buildT T)); fold (activeEnv (buildT T0)).
    assert (Qxy: envSub Q x y).
    destruct Q; trivial.
    intro TxA.
    assert (activeEnv Tr |= x := B).
    apply (proj2 (H0 x y Qxy B)); trivial.
    simpl; fold (activeEnv (buildT T0)).
    apply varD_tail; trivial.
    apply varD_tail_rev; trivial.
  Qed.

  Lemma conv_env_abs : forall M N (Mabs: isAbs M) (Nabs: isAbs N) Q,
    conv_term (term M) (term N) Q ->
    conv_env (absBody Mabs) (absBody Nabs) (envSubst_lift1 Q) ->
    conv_env M N Q.

  Proof.
    intros; term_inv M; term_inv N.
    intros p q Qpq C.
    unfold Tr; rewrite (activeEnv_abs (buildT (TAbs T)) I).
    unfold Tr0; rewrite (activeEnv_abs (buildT (TAbs T0)) I).
    assert (Q_pq: envSub (envSubst_lift1 Q) (S p) (S q)). 
    destruct Q; trivial.
    split; intro D.
    apply varD_tail.
    apply (proj1 (H0 (S p) (S q) Q_pq C)).
    apply varD_tail_rev; trivial.
    apply varD_tail.
    apply (proj2 (H0 (S p) (S q) Q_pq C)).
    apply varD_tail_rev; trivial.
  Qed.

  Lemma conv_env_app : forall M N (Mapp: isApp M) (Napp: isApp N) Q,
    conv_term (term M) (term N) Q -> 
    conv_env (appBodyL Mapp) (appBodyL Napp) Q ->
    conv_env (appBodyR Mapp) (appBodyR Napp) Q ->
    conv_env M N Q.

  Proof.
    intros; term_inv M; term_inv N.    
    intros p q Qpq C; unfold Tr; unfold Tr0.
    rewrite (activeEnv_app (buildT (TApp T1 T2)) I).
    rewrite (activeEnv_app (buildT (TApp T3 T4)) I).
    split; intro D.
    destruct (env_sum_varDecl (activeEnv (buildT T1))
                              (activeEnv (buildT T2)) D) as [[Lc Rn] | Rc].
    apply env_sum_ly.
    apply activeEnv_app_comp.
    apply (proj1 (H0 p q Qpq C)); trivial.
    apply env_sum_ry.
    apply (proj1 (H1 p q Qpq C)); trivial.
    destruct (env_sum_varDecl (activeEnv (buildT T3))
                              (activeEnv (buildT T4)) D) as [[Lc Rn] | Rc].
    apply env_sum_ly.
    apply activeEnv_app_comp.
    apply (proj2 (H0 p q Qpq C)); trivial.
    apply env_sum_ry.
    apply (proj2 (H1 p q Qpq C)); trivial.
  Qed.

  Lemma conv_env_var: forall M N x y Q,
    envSub Q x y -> term M = %x -> term N = %y ->
    type M = type N -> conv_env M N Q.

  Proof.
    intros; intros p q pq B.
    split; intro D.
    destruct (activeEnv_var_det M H0 D).
    rewrite H3 in pq.
    rewrite <- (envSub_Lok Q x y q H pq).
    rewrite (activeEnv_var N H1).    
    rewrite <- H2; rewrite H4.
    unfold VarD, decl, EmptyEnv; apply nth_after_copy.
    destruct (activeEnv_var_det N H1 D).
    rewrite H3 in pq.
    rewrite <- (envSub_Rok Q x p y H pq).
    rewrite (activeEnv_var M H0).
    rewrite H2; rewrite H4.
    unfold VarD, decl, EmptyEnv; apply nth_after_copy.
  Qed.

  Lemma conv_env_lifted : forall M N Q, conv_env M N Q ->
    conv_env (lift M 1) (lift N 1) (envSubst_lift1 Q).

  Proof.
    intros.
    intros x y Qxy A.
    rewrite (activeEnv_lift M 1).
    rewrite (activeEnv_lift N 1).
    unfold liftedEnv; autorewrite with datatypes terms using simpl.
    destruct x; destruct y.
    split; intro; inversion H0.
    exfalso; apply envSubst_lift1_absurdR with y Q; trivial.
    exfalso; apply envSubst_lift1_absurdL with x Q; trivial.
    assert (Q_xy: envSub Q x y).
    destruct Q; trivial.
    set (w := H x y Q_xy A).
    tauto.
  Qed.

  Lemma conv_env_lift : forall M n,
    conv_env M (lift M n) (liftEnvSubst n 0 (length (env M))).

  Proof.
    intros.
    intros x y Qxy A.
    rewrite (activeEnv_lift M n).
    unfold liftedEnv; autorewrite with datatypes terms using simpl.
    inversion Qxy; unfold VarD.
    destruct (le_gt_dec 0 x); try solve [lia].
    split; intro D.
    rewrite <- H0.
    rewrite nth_app_right; autorewrite with datatypes using try lia.
    replace (x + n - n) with x; [trivial | lia].
    rewrite <- H0 in D.
    rewrite nth_app_right in D; autorewrite with datatypes using try lia.
    replace (x + n - length (copy n (None (A:=SimpleType)))) with x in D;
    trivial.
    autorewrite with datatypes using lia.
  Qed.

  Lemma conv_env_lower : forall M Menv,
    conv_env M (lower M Menv) (lowerEnvSubst 0 (length (env M))).

  Proof.
    intros.
    intros x y Qxy A.
    rewrite !activeEnv_lower.
    unfold loweredEnv; autorewrite with datatypes terms using simpl.
    destruct x; try_solve.
    destruct (eq_nat_dec 0 0); try_solve.
    destruct (eq_nat_dec 0 (S x)); try_solve.
    inversion Qxy.
    destruct (activeEnv M); try_solve.
    split; destruct y; try_solve.
    rewrite (finalSeg_cons o e); try_solve.
    inversion H0; try_solve.
  Qed.

  Lemma conv_env_appBodyL : forall M N (Mapp: isApp M) (Napp: isApp N) Q,
    conv_env M N Q ->
    conv_term (term M) (term N) Q -> conv_env (appBodyL Mapp) (appBodyL Napp) Q.

  Proof.
    intros.
    intros x y xy A.
    inversion H0; try solve [term_inv M; term_inv N].
    assert (Ecomp: forall A B, 
      activeEnv (appBodyL Mapp) |= x := A -> 
      activeEnv (appBodyL Napp) |= y := B -> 
      A = B).
    intros C D MC ND. 
    assert (activeEnv N |= y := C).
    apply (proj1 (H x y xy C)).
    apply activeEnv_appBodyL_varD with Mapp; trivial.
    set (w := activeEnv_appBodyL_varD N Napp ND).
    inversion H6; inversion w; try_solve.
    replace LL with (term (appBodyL Mapp)) in H3.
    replace RL with (term (appBodyL Napp)) in H3.
    exact (terms_conv_var_usage (appBodyL Mapp) (appBodyL Napp) Ecomp xy H3 A).
    eapply appBodyL_term; eauto.
    eapply appBodyL_term; eauto.
  Qed.

  Lemma conv_env_appBodyR : forall M N (Mapp: isApp M) (Napp: isApp N) Q,
    conv_env M N Q ->
    conv_term (term M) (term N) Q -> conv_env (appBodyR Mapp) (appBodyR Napp) Q.

  Proof.
    intros.
    intros x y xy A.
    inversion H0; try solve [term_inv M; term_inv N].
    assert (Ecomp: forall A B, 
      activeEnv (appBodyR Mapp) |= x := A -> 
      activeEnv (appBodyR Napp) |= y := B -> 
      A = B).
    intros C D MC ND. 
    assert (activeEnv N |= y := C).
    apply (proj1 (H x y xy C)).
    apply activeEnv_appBodyR_varD with Mapp; trivial.
    set (w := activeEnv_appBodyR_varD N Napp ND).
    inversion H6; inversion w; try_solve.
    replace LR with (term (appBodyR Mapp)) in H4.
    replace RR with (term (appBodyR Napp)) in H4.
    exact (terms_conv_var_usage (appBodyR Mapp) (appBodyR Napp) Ecomp xy H4 A).
    eapply appBodyR_term; eauto.
    eapply appBodyR_term; eauto.
  Qed.

  Lemma conv_env_ext : forall M N Q Q',
    conv_term (term M) (term N) Q -> conv_env M N Q ->
    Q' |=> Q -> conv_env M N Q'.

  Proof.
    destruct M as [E Pt T M]; induction M; intros N Q Q' MN_term MN_env Q'Q;
      term_inv N; inversion MN_term; intros p q Q'pq C.
     (* variable *)
    split; intro D.
    destruct (@activeEnv_var_det (buildT (TVar v)) x p C); trivial.
    assert (q = x0).
    apply (envSub_Lok Q' x q x0).
    rewrite <- H3; trivial.
    apply Q'Q; trivial.
    rewrite H5.
    apply (proj1 (MN_env x x0 H1 C)).
    rewrite H4.
    apply activeEnv_var_decl; trivial.
    destruct (@activeEnv_var_det (buildT (TVar T)) x0 q C); trivial.
    assert (p = x).
    apply (envSub_Rok Q' p x x0).
    rewrite <- H3; trivial.
    apply Q'Q; trivial.
    rewrite H5.
    apply (proj2 (MN_env x x0 H1 C)).
    rewrite H4.
    apply activeEnv_var_decl; trivial.
     (* function symbol *)
    simpl; split; intros D; destruct p; destruct q; try_solve.
     (* abstraction *)
    assert (Env_conv: conv_env (buildT (TAbs M)) (buildT (TAbs T)) Q').
    apply conv_env_abs with I I; trivial.
    apply conv_term_ext with Q; trivial.
    apply IHM with (envSubst_lift1 Q); trivial.
    apply (conv_env_absBody (M:=buildT (TAbs M)) (N:=buildT (TAbs T)) I I);
      trivial.
    apply envSubst_lift1_ext; trivial.
    apply (Env_conv p q Q'pq).
     (* application *)    
    set (envL_conv := @conv_env_appBodyL
      (buildT (TApp M1 M2)) (buildT (TApp T1 T2)) I I Q MN_env MN_term).
    set (IHL := IHM1 (buildT T1) Q Q' H4 envL_conv Q'Q).
    set (envR_conv := @conv_env_appBodyR
      (buildT (TApp M1 M2)) (buildT (TApp T1 T2)) I I Q MN_env MN_term).
    set (IHR := IHM2 (buildT T2) Q Q' H5 envR_conv Q'Q).
    set (MNQ'_term := conv_term_ext MN_term Q'Q).
    apply (conv_env_app (buildT (TApp M1 M2)) (buildT (TApp T1 T2)) I I 
      MNQ'_term IHL IHR p q Q'pq).
  Qed.

  Definition terms_conv_with S M N :=
    conv_term (term M) (term N) S /\ conv_env M N S.

  Notation "M ~ ( S ) N" := (terms_conv_with S M N) (at level 5).

  Lemma terms_conv_with_morph_aux :
    forall x1 x2 : EnvSubst,
    x1 <=> x2 -> forall x x0 : Term, x ~ (x1)x0 -> x ~ (x2)x0.

  Proof. intros; inversion H0. constructor; rewrite <- H; trivial. Qed.

  Global Instance terms_conv_with_morph :
    Proper (envSubst_eq ==> eq ==> eq ==> iff) terms_conv_with.

  Proof.
    intros E F EF a b ab c d cd. subst b d. split_all.
    eapply terms_conv_with_morph_aux. apply EF. hyp.
    eapply terms_conv_with_morph_aux. apply envSubst_eq_sym. apply EF. hyp.
  Qed.

  Definition terms_conv M N := exists S, M ~(S) N.

  Infix "~" := terms_conv (at level 7).

  Lemma terms_conv_criterion : forall M N,
    env M [<->] env N -> term M = term N -> M ~ N.

  Proof.
    intros M N MNenv MNterm; exists (compEnvSubst MNenv); constructor.
    apply conv_term_comp_refl; trivial.
    intros x y xy A.
    inversion xy; rewrite H.
    rewrite (equiv_term_activeEnv M N); trivial.
    split; trivial.
  Qed.

  Lemma terms_conv_criterion_strong : forall M N,
    activeEnv M = activeEnv N -> term M = term N -> M ~ N.

  Proof.
    intros.
    exists (idEnvSubst (length (env M))).
    constructor.
    rewrite <- H0.
    apply conv_term_refl.
    intros p q pq.
    inversion pq.
    intro.
    rewrite H; rewrite H1; split; trivial.
  Qed.

  Lemma terms_conv_eq_type : forall M N, M ~ N -> type M = type N.

  Proof.
    destruct M as [EM PtM AM M].
    induction M; intros; inversion H; inversion H0; inversion H1;
      destruct N as [EN PtN AN N]; destruct N; try_solve.
     (* variable *)
    assert (env (buildT (TVar v0)) |= x2 := A).
    apply activeEnv_subset.
    inversion H4.
    rewrite H8 in H5.
    apply (proj1 (H2 x x2 H5 A)).
    apply activeEnv_var_decl; trivial.
    inversion H7; inversion v0; try_solve.

     (* abstraction *)
    rewrite (IHM (buildT N)); try_solve.
    inversion H1; exists (envSubst_lift1 x); constructor; trivial.
    replace (buildT M) with (absBody (M := buildT (TAbs M)) I); trivial.
    replace (buildT N) with (absBody (M := buildT (TAbs N)) I); trivial.
    apply conv_env_absBody; trivial.

      (* application *)
    inversion H5.
    assert (M1N1: terms_conv (buildT M1) (buildT N1)).
    exists x; constructor; simpl; trivial.
    inversion H5; rewrite <- H10; trivial.
    replace (buildT M1) with (appBodyL (M := buildT (TApp M1 M2)) I); trivial.
    replace (buildT N1) with (appBodyL (M := buildT (TApp N1 N2)) I); trivial.
    apply conv_env_appBodyL; trivial.
    set (w := IHM1 (buildT N1) M1N1); try_solve.
  Qed.

  Lemma terms_conv_refl : forall M, M ~ M.

  Proof.
    intro M. exists (idEnvSubst (length (env M))); constructor.
    apply conv_term_refl. apply conv_env_refl.
  Qed.

  Lemma terms_conv_sym_aux : forall M N Q, M ~(Q) N -> N ~(envSubst_transp Q) M.

  Proof.
    intros. constructor. apply conv_term_sym; fo. apply conv_env_sym; fo.
  Qed.

  Lemma terms_conv_sym : forall M N, M ~ N -> N ~ M.

  Proof.
    intros M N MN; destruct MN.
    exists (envSubst_transp x).
    apply terms_conv_sym_aux; trivial.
  Qed.

  Lemma terms_conv_trans : forall M N P, M ~ N -> N ~ P -> M ~ P.

  Proof.
    intros M N P MN NP.
    destruct MN; destruct NP.
    inversion H; inversion H0.
    exists (envSubst_compose x x0); constructor.
    apply conv_term_trans with (term N); trivial.
    apply conv_env_trans with N; trivial.
  Qed.

  Lemma terms_eq_conv : forall M N, M = N -> M ~ N.

  Proof.
    intros; exists (idEnvSubst (length (env M))); rewrite H.
    constructor.
    apply conv_term_refl.
    apply conv_env_refl.
  Qed.

  Global Instance terms_conv_Equivalence : Equivalence terms_conv.

  Proof.
    split.
    intro x. apply terms_conv_refl.
    intros x y. apply terms_conv_sym.
    intros x y z. apply terms_conv_trans.
  Qed.

  Global Instance isApp_morph : Proper (terms_conv ==> iff) isApp.

  Proof.
    intros t t' H; split; intro H'; inversion H; inversion H0; inversion H1; 
      term_inv t; term_inv t'.
  Qed.

  Global Instance isVar_morph : Proper (terms_conv ==> iff) isVar.

  Proof.
    intros t t' H; split; intro H'; inversion H; inversion H0; inversion H1;
      term_inv t; term_inv t'.
  Qed.

  Global Instance isAbs_morph : Proper (terms_conv ==> iff) isAbs.

  Proof.
    intros t t' H; split; intro H'; inversion H; inversion H0; inversion H1;
      term_inv t; term_inv t'.
  Qed.

  Global Instance isNeutral_morph : Proper (terms_conv ==> iff) isNeutral.

  Proof.
     intros t t' H; split; intro H'; inversion H; inversion H0; inversion H1;
      term_inv t; term_inv t'.
  Qed.

  Global Instance isFunS_morph : Proper (terms_conv ==> iff) isFunS.

  Proof.
    intros t t' H; split; intro H'; inversion H; inversion H0; inversion H1;
      term_inv t; term_inv t'.
  Qed.

  Lemma conv_by : forall M N Q, M ~(Q) N -> M ~ N.

  Proof. intros. exists Q; trivial. Qed.

  Lemma abs_conv_absBody_aux : forall M N Q (Mabs: isAbs M) (Nabs: isAbs N),
    M ~(Q) N -> (absBody Mabs) ~(envSubst_lift1 Q) (absBody Nabs).

  Proof.
    intros.
    term_inv M; term_inv N.
    inversion H.
    constructor.
    inversion H0; trivial.
    replace (buildT T) with (@absBody (buildT (TAbs T)) I); trivial.
    replace (buildT T0) with (@absBody (buildT (TAbs T0)) I); trivial.
    apply conv_env_absBody; trivial.
  Qed.

  Lemma abs_conv_absBody : forall M N (Mabs: isAbs M) (Nabs: isAbs N), M ~ N -> 
    terms_conv (absBody Mabs) (absBody Nabs).

  Proof.
    intros; inversion H.
    exists (envSubst_lift1 x).
    apply abs_conv_absBody_aux; trivial.
  Qed.

  Lemma abs_conv_absType : forall M N (Mabs: isAbs M) (Nabs: isAbs N), M ~ N ->
    absType Mabs = absType Nabs.

  Proof.
    intros M N; term_inv M; term_inv N; intros.
    destruct H; destruct H; inversion H; trivial.
  Qed.

  Lemma abs_conv : forall M N (Mabs: isAbs M) (Nabs: isAbs N) Q,
    absType Mabs = absType Nabs ->
    (absBody Mabs) ~(envSubst_lift1 Q) (absBody Nabs) -> M ~(Q) N.

  Proof.
    intros.
    term_inv M; term_inv N.
    assert (Conv_term: conv_term (\A => Pt) (\A0 => Pt0) Q).
    simpl; rewrite H.
    constructor 3.
    destruct H0; trivial.
    constructor; trivial.
    apply conv_env_abs with I I; simpl; trivial.
    destruct H0; trivial.
  Qed.

  Lemma app_conv_app_left_aux : forall M N (Mapp: isApp M) (Napp: isApp N) Q,
    M ~(Q) N -> (appBodyL Mapp) ~(Q) (appBodyL Napp).

  Proof.
    intros; term_inv M; term_inv N.
    inversion H; inversion H0.
    constructor; trivial.
    change (buildT T1) with (appBodyL (M:=buildT (TApp T1 T2)) I).
    change (buildT T3) with (appBodyL (M:=buildT (TApp T3 T4)) I).
    apply conv_env_appBodyL; trivial.
  Qed.

  Lemma app_conv_app_left : forall M N (Mapp: isApp M) (Napp: isApp N), M ~ N ->
    terms_conv (appBodyL Mapp) (appBodyL Napp).

  Proof.
    intros; destruct H. exists x; apply app_conv_app_left_aux; trivial.
  Qed.

  Lemma app_conv_app_right_aux : forall M N (Mapp: isApp M) (Napp: isApp N) Q,
    M ~(Q) N -> (appBodyR Mapp) ~(Q) (appBodyR Napp).

  Proof.
    intros; term_inv M; term_inv N.
    inversion H; inversion H0.
    constructor; trivial.
    change (buildT T2) with (appBodyR (M:=buildT (TApp T1 T2)) I).
    change (buildT T4) with (appBodyR (M:=buildT (TApp T3 T4)) I).
    apply conv_env_appBodyR; trivial.
  Qed.

  Lemma app_conv_app_right : forall M N (Mapp: isApp M) (Napp: isApp N),
    M ~ N -> terms_conv (appBodyR Mapp) (appBodyR Napp).

  Proof.
    intros; destruct H.
    exists x; apply app_conv_app_right_aux; trivial.
  Qed.

  Lemma app_conv : forall M N (Mapp: isApp M) (Napp: isApp N) Q,
    (appBodyL Mapp) ~(Q) (appBodyL Napp)
    -> (appBodyR Mapp) ~(Q) (appBodyR Napp) -> M ~(Q) N.

  Proof.
    intros.
    term_inv M; term_inv N.
    destruct H; destruct H0.
    assert (Conv_term: conv_term (term Tr) (term Tr0) Q).
    simpl; constructor 4; trivial.
    constructor; trivial.
    apply conv_env_app with I I; simpl; trivial.
  Qed.

  Lemma terms_conv_conv_lift : forall M N Q,
    M ~(Q) N -> (lift M 1) ~(envSubst_lift1 Q) (lift N 1).

  Proof.
    intros; constructor.
    rewrite !lift_term.
    apply conv_term_lifted.
    destruct H; trivial.
    apply conv_env_lifted; destruct  H; trivial.
  Qed.

  Lemma terms_lift_conv : forall M n, terms_conv M (lift M n).

  Proof.
    intros M n.
    exists (liftEnvSubst n 0 (length (env M))); constructor; simpl.
    rewrite lift_term.
    unfold prelift; apply conv_term_lift.
    apply conv_env_lift.
  Qed.

  Lemma terms_lower_conv :
    forall M (Menv: env M |= 0 :!), terms_conv M (lower M Menv).

  Proof.
    intros M Menv.
    exists (lowerEnvSubst 0 (length (env M))); constructor; simpl.
    rewrite lower_term; simpl.
    unfold prelower; apply conv_term_lower; trivial.
    apply conv_env_lower.
  Qed.

  Lemma appHead_conv : forall M N Q, M ~(Q) N -> (appHead M) ~(Q) (appHead N).

  Proof.
    intro M.
    apply well_founded_ind with (R := subterm)
      (P := fun M =>
	forall N Q,
	  M ~(Q) N ->
	  (appHead M) ~(Q) (appHead N)).
    apply subterm_wf.
    clear M; intros M IH N Q MN.
    destruct (isApp_dec M).
    term_inv M.
    inversion MN.    
    term_inv N; inversion H.
    rewrite appHead_app with Tr I.
    rewrite appHead_app with Tr0 I.
    apply IH.
    apply appBodyL_subterm.
    constructor; trivial.
    apply conv_env_appBodyL; trivial.    
    rewrite appHead_notApp; trivial.
    rewrite appHead_notApp; trivial.
    term_inv N.
    inversion MN; inversion H; term_inv M.
  Qed.

  Global Instance appHead_morph : Proper (terms_conv ==> terms_conv) appHead.

  Proof.
    intros t t' teqt'.
    destruct teqt' as [s].  
    exists s.
    apply appHead_conv; trivial.
  Qed.

  Global Instance isFunApp_morph : Proper (terms_conv ==> iff) isFunApp.

  Proof. unfold isFunApp; intros t t' H. rewrite H; split; trivial. Qed.

  Lemma terms_conv_activeEnv: forall M N Q, M ~(Q) N ->
    forall p A, activeEnv M |= p := A -> exists q, envSub Q p q.

  Proof.
    destruct M as [E Pt T M]; induction M; intros; inversion H.
     (* variable *)
    inversion H1; exists y.
    rewrite <- (@activeEnv_var_single (buildT (TVar v)) x p A0); trivial.
     (* function symbol *)
    destruct p; try_solve.
     (* abstraction *)
    term_inv N; inversion H1.
    set (Conv := @abs_conv_absBody_aux
      (buildT (TAbs M)) (buildT (TAbs T)) Q I I H).
    set (Mdec := varD_tail_rev (activeEnv (buildT M)) H0).
    destruct (IHM (buildT T) (envSubst_lift1 Q) Conv (Datatypes.S p) A0 Mdec).
    destruct x.
    destruct Q; try_solve.
    exists x; destruct Q; trivial.
     (* application *)
    rewrite (activeEnv_app (buildT (TApp M1 M2)) I) in H0.
    assert (Napp: isApp N).
    term_inv N; inversion H1.
    destruct (env_sum_varDecl (activeEnv (buildT M1))
                              (activeEnv (buildT M2)) H0) as [[l _] | r].
    set (Conv := app_conv_app_left_aux (M := buildT (TApp M1 M2)) I Napp H).
    exact (IHM1 (appBodyL Napp) Q Conv p A0 l).
    set (Conv := app_conv_app_right_aux (M := buildT (TApp M1 M2)) I Napp H).
    exact (IHM2 (appBodyR Napp) Q Conv p A0 r).
  Qed.

  Lemma terms_conv_activeEnv_rev : forall N M Q, M ~(Q) N ->
    forall q A, activeEnv N |= q := A -> exists p, envSub Q p q.

  Proof.
    intros.
    inversion H.
    set (NM := terms_conv_sym_aux H).
    destruct (terms_conv_activeEnv NM H0).
    exists x.
    destruct Q; trivial.
  Qed.

  Lemma terms_conv_activeEnv_sub : forall M M' N N' Q, M ~(Q) M' ->
    envSubset (activeEnv N) (activeEnv M) -> N ~(Q) N' ->
    envSubset (activeEnv N') (activeEnv M').

  Proof.
    intros; intros x A N'x.
    destruct (terms_conv_activeEnv_rev H1 N'x).    
    apply (proj1 ((proj2 H) x0 x H2 A)).
    apply H0.
    apply (proj2 ((proj2 H1) x0 x H2 A)); trivial.
  Qed.

  Lemma terms_conv_extend_subst : forall M N Q Q',
    M ~(Q) N -> Q' |=> Q -> M ~(Q') N.

  Proof.
    intros.
    destruct H.
    constructor.
    apply conv_term_ext with Q; trivial.
    apply conv_env_ext with Q; trivial.
  Qed.

  Lemma terms_conv_shrink_subst : forall M N Q Q', M ~(Q') N -> Q' |=> Q -> 
    (forall x A, activeEnv M |= x := A -> exists y, envSub Q x y) -> M ~(Q) N.

  Proof.
    destruct M as [E Pt T M]; induction M; intros; destruct H.
     (* variable *)
    inversion H.
    destruct (H1 x A).
    simpl; unfold VarD, decl, EmptyEnv.
    apply nth_after_copy.
    replace x1 with y in H7.
    constructor.
    simpl; rewrite <- H4; constructor; trivial.
    apply conv_env_var with x y; auto.
    apply terms_conv_eq_type; exists Q'; constructor; trivial.
    apply envSub_Lok with Q' x; trivial.
    apply H0; trivial.
     (* function symbol *)
    inversion H.
    constructor.
    rewrite <- H5; simpl; constructor.
    intros x y xy A.
    rewrite activeEnv_funS; simpl; trivial.
    rewrite activeEnv_funS.
    split; intro w; destruct x; destruct y; try_solve.
    apply funS_is_funS with f; auto.
     (* abstraction *)
    inversion H.
    assert (Nabs: isAbs N).
    apply abs_isAbs with A R; auto.
    term_inv N; inversion H6; unfold Tr.
    assert (MNbody: (buildT M) ~(envSubst_lift1 Q') (buildT T)).
    constructor.
    simpl; rewrite <- H10; trivial.
    change (buildT M) with (absBody (M:=buildT (TAbs M)) I).
    change (buildT T) with (absBody (M:=buildT (TAbs T)) I).
    apply conv_env_absBody; trivial.
    destruct (IHM (buildT T) (envSubst_lift1 Q) (envSubst_lift1 Q')); trivial.
    apply envSubst_lift1_ext; trivial.
    fold (activeEnv (buildT M)) in * .
    intros.
    destruct x.
    exists 0; destruct Q; trivial.
    destruct (H1 x A2).
    apply varD_tail; trivial.
    exists (Datatypes.S x0); destruct Q; trivial.
    constructor; simpl.
    rewrite H9.
    constructor; trivial.
    apply conv_env_abs with I I.
    simpl; rewrite H9; constructor; trivial.
    simpl; trivial.
     (* application *)
    inversion H; destruct N as [E' Pt' C N]; destruct N; try discr.
    apply app_conv with I I.
    apply IHM1 with Q'; trivial.
    change (buildT M1) with (appBodyL (M:=buildT (TApp M1 M2)) I).
    apply app_conv_app_left_aux; constructor; trivial.
    intros; destruct (H1 x A1).
    apply (activeEnv_appBodyL_varD (buildT (TApp M1 M2)) I); trivial.
    exists x0; trivial.
    apply IHM2 with Q'; trivial.
    change (buildT M2) with (appBodyR (M:=buildT (TApp M1 M2)) I).
    apply app_conv_app_right_aux; constructor; trivial.
    intros; destruct (H1 x A1).
    apply (activeEnv_appBodyR_varD (buildT (TApp M1 M2)) I); trivial.
    exists x0; trivial.
  Qed.

  Lemma terms_conv_diff_env : forall M N N' Q, M ~(Q) N -> term N' = term N ->
    activeEnv N' = activeEnv N -> M ~(Q) N'.

  Proof.
    intros; destruct H; constructor.
    rewrite H0; trivial.
    intros x y xy A.
    rewrite H1.
    apply H2; trivial.
  Qed.

  Lemma terms_conv_diff_env_rev : forall M N M' Q,
    M ~(Q) N -> term M' = term M -> activeEnv M' = activeEnv M -> M' ~(Q) N.

  Proof.
    intros.
    rewrite <- (envSubst_transp_twice Q).
    apply terms_conv_sym_aux.
    apply terms_conv_diff_env with M; trivial.
    apply terms_conv_sym_aux; trivial.
  Qed.

  Definition envSub_minimal Q M :=
    forall x y, envSub Q x y -> exists A, activeEnv M |= x := A.

  Lemma envSub_minimal_rev : forall Q M M' x y, envSub_minimal Q M ->
    M ~(Q) M' -> envSub Q x y -> exists A, activeEnv M' |= y := A.

  Proof.
    intros Q M M' x y QMmin MM' Qxy.
    destruct (QMmin x y Qxy).
    exists x0.
    apply (proj1 ((proj2 MM') x y Qxy x0)); trivial.
  Qed.

  Lemma envSubst_add: forall Q i j,
    envSub Q i j \/ (forall x, ~envSub Q i x /\ ~envSub Q x j)  ->
    exists Q', Q' |=> Q /\ envSub Q' i j /\
      (forall p q, envSub Q' p q -> (envSub Q p q \/ (p = i /\ q = j))).

  Proof. intros. exists (addEnvSubst Q i j H); fo. Qed.

  Lemma envSub_min_ex : forall M N Q, M ~(Q) N -> exists Q', 
    M ~(Q') N /\ envSub_minimal Q' M /\ Q |=> Q'.

  Proof.
    destruct M as [E Pt T M]; induction M; intros; 
      destruct H; inversion H; term_inv N; unfold Tr.
     (* variable *)
    exists (singletonEnvSubst x y); split.
    constructor.
    inversion H2.
    simpl; rewrite <- H6.
    constructor; simpl; auto.
    apply conv_env_var with x y; try solve [simpl; auto].
    apply terms_conv_eq_type; exists Q; constructor; trivial.
    split.
    intros p q pq.
    inversion pq.
    rewrite H5.
    exists A; simpl; unfold VarD, EmptyEnv, decl.
    apply nth_after_copy.
    intros p q pq.
    inversion pq.
    rewrite H5; rewrite H6; trivial.
     (* function symbol *)
    exists emptyEnvSubst; repeat split; try_solve;
      try solve [intros x y xy; inversion xy].
    rewrite H3; constructor.
     (* abstraction *)
    destruct (IHM (buildT T) (envSubst_lift1 Q)) as [Q' [MT [Q'min QQ']]].
    change (buildT M) with (absBody (M:=buildT (TAbs M)) I).
    change (buildT T) with (absBody (M:=buildT (TAbs T)) I).
    apply abs_conv_absBody_aux; constructor; trivial.
    destruct (envSubst_add Q' 0 0) as [Q'' [Q''Q' [Q''00 Q''ext]]].
    destruct (envSub_dec Q' 0 0).
    left; trivial.
    right; split; intro.
    destruct x; try_solve.
    absurd (0 = Datatypes.S x).
    lia.
    apply envSub_Lok with (envSubst_lift1 Q) 0.
    destruct Q; simpl; trivial.
    apply QQ'; trivial.
    destruct x; try_solve.
    absurd (Datatypes.S x = 0).
    lia.
    apply envSub_Rok with (envSubst_lift1 Q) 0.
    apply QQ'; trivial.
    destruct Q; simpl; trivial.
    exists (envSubst_lower Q''); split.
    apply abs_conv with I I.
    inversion H4; trivial.
    simpl.
    rewrite (envSubst_lift_lower Q'' Q''00); trivial.
    apply terms_conv_extend_subst with Q'; trivial.
    split.
    intros p q pq.
    destruct (Q''ext (Datatypes.S p) (Datatypes.S q)).
    destruct Q''; simpl; trivial.
    destruct (Q'min (Datatypes.S p) (Datatypes.S q) H6).
    exists x.
    rewrite (activeEnv_abs (buildT (TAbs M)) I).
    apply varD_tail; trivial.
    inversion H6; try_solve.
    apply envSubst_lift1_ext_rev.
    rewrite (envSubst_lift_lower Q'' Q''00); trivial.
    intros p q pq.
    destruct (Q''ext p q pq).
    apply QQ'; trivial.
    destruct H6; rewrite H6; rewrite H7.
    destruct Q; simpl; trivial.

     (* application *)
    destruct (IHM1 (buildT T1) Q) as [Q'l [MTl [Q'l_min QQ'l]]].
    change (buildT M1) with (appBodyL (M:=buildT (TApp M1 M2)) I).
    change (buildT T1) with (appBodyL (M:=buildT (TApp T1 T2)) I).
    apply app_conv_app_left_aux; constructor; trivial.
    destruct (IHM2 (buildT T2) Q) as [Q'r [MTr [Q'r_min QQ'r]]].
    change (buildT M2) with (appBodyR (M:=buildT (TApp M1 M2)) I).
    change (buildT T2) with (appBodyR (M:=buildT (TApp T1 T2)) I).
    apply app_conv_app_right_aux; constructor; trivial.
    exists (sumEnvSubst QQ'l QQ'r); split.
    apply app_conv with I I; simpl.
    apply terms_conv_extend_subst with Q'l; trivial.
    apply sumEnvSubst_ext_l.
    apply terms_conv_extend_subst with Q'r; trivial.
    apply sumEnvSubst_ext_r.
    split.
    intros p q pq.
    destruct (sumEnvSubst_or pq).
    destruct (Q'l_min p q H7).
    exists x.
    apply (activeEnv_appBodyL_varD (buildT (TApp M1 M2)) I H8).
    destruct (Q'r_min p q H7).
    exists x.
    apply (activeEnv_appBodyR_varD (buildT (TApp M1 M2)) I H8).
    apply sumEnvSubst_ext.
  Qed.

  Lemma envSubst_extend : forall i Q E,
    (forall j, ~envSub Q i j) -> exists Q',
      Q' |=> Q /\ exists j, envSub Q' i j /\ E |= j :! /\ 
	(forall k l, envSub Q' k l -> (k <> i \/ l <> j) -> envSub Q k l).

  Proof.
    intros.
    set (v := max (size Q) (max i (length E))).
    set (f := fun x y => (x = i /\ y = v) \/ (envSub Q x y)).
    assert (f_dec: forall i j, {f i j} + {~f i j}).
    intros p q.
    destruct (envSub_dec Q p q).
    fo.
    destruct (eq_nat_dec p i); destruct (eq_nat_dec q v);
      subst; unfold f; tauto.
    assert (f_Lok: forall i j j', f i j -> f i j' -> j = j').
    unfold f; intros.
    destruct H0; destruct H1.
    lia.
    absurd (envSub Q i0 j'); trivial.
    destruct H0; rewrite H0; fo.
    absurd (envSub Q i0 j); trivial.
    destruct H1; rewrite H1; fo.
    apply (envSub_Lok Q i0); trivial.
    assert (f_Rok: forall i i' j, f i j -> f i' j -> i = i').
    unfold f; intros.
    destruct H0; destruct H1.
    lia.
    absurd (j < size Q).
    destruct H0; rewrite H2.
    unfold v; intro w.
    set (w' := le_max_l (size Q) (max i (length E))); lia.
    set (w := sizeOk Q i' j H1); fo.
    absurd (j < size Q).
    destruct H1; rewrite H2.
    unfold v; intro w.
    set (w' := le_max_l (size Q) (max i (length E))); lia.
    set (w := sizeOk Q i0 j H0); fo.
    apply (envSub_Rok Q) with j; trivial.
    assert (s_ok: forall i j, f i j -> i < S v /\ j < S v).
    intros.
    destruct H0 as [[i0_i jv] | x]; unfold v.
    rewrite jv; rewrite i0_i; split; auto. lia.

    destruct (sizeOk Q i0 j x).
    split; eauto with arith.
    exists (build_envSub f f_dec f_Lok f_Rok s_ok).
    simpl; split.
    fo.
    exists v; split.
    fo.
    split.
    constructor; apply nth_beyond.
    unfold v; eauto with arith.
    fo.
  Qed.

  Lemma term_build_conv : forall M Q E,
    (forall x y A B, envSub Q x y -> activeEnv M |= x := A ->
      E |= y := B -> A = B) ->
    exists Q', Q' |=> Q /\ exists M', 
      M ~(Q') M' /\ env M' [<->] E /\ envMinimal M' /\
      (forall x y, envSub Q' x y -> envSub Q x y \/ E |= y :!).

  Proof.
    destruct M as [E Pt T M]; induction M; intros.
     (* variable *)
    destruct (envSubst_dec x Q) as [[y xy] | ny].
    exists Q; split.
    apply envSubst_extends_refl.
    set (v' := buildVar A y).
    exists (buildT v'); split.
    constructor.
    simpl; constructor; trivial.
    apply conv_env_var with x y; trivial.
    split; simpl.
    apply env_comp_single.
    destruct (isVarDecl_dec E0 y) as [[B E0y] | E0yn].
    rewrite (H x y A B xy); trivial.
    right; trivial.
    apply activeEnv_var_decl; trivial.
    left; trivial.
    split.
    unfold v'; apply buildVar_minimal.
    intros.
    left; trivial.
    destruct (envSubst_extend x Q E0 ny) as [Q' [QQ' [j [Q'xj [E0j Q'Q_ext]]]]].
    exists Q'; split; trivial.
    set (v' := buildVar A j).
    exists (buildT v'); split.
    constructor.
    simpl; constructor; trivial.
    apply conv_env_var with x j; trivial.
    split; simpl.
    apply env_comp_single.
    left; trivial.
    split; simpl.
    unfold v'; apply buildVar_minimal.
    intros.
    destruct (eq_nat_dec x0 x); destruct (eq_nat_dec y j); solve
      [ right; rewrite e0; trivial
      | left; apply Q'Q_ext; auto
      ].

     (* function symbol *)
    exists Q; split.
    apply envSubst_extends_refl.
    exists (buildT (TFun EmptyEnv f)); split.
    split.
    simpl; constructor.
    intros x y xy A.
    rewrite activeEnv_funS; simpl; trivial.
    split; intro X; destruct x; destruct y; try_solve.
    split.
    simpl.
    apply env_comp_empty_r.
    split.
    unfold envMinimal; trivial.
    fo.
     (* abstraction *)
    destruct (IHM (envSubst_lift1 Q) (Some A :: E0)) as 
      [Q' [Q'Q [M'b [MM' [M'E0 [M'min Q'ext]]]]]].
    intros.
    destruct x; destruct y.
    rewrite (@activeEnv_abs0 (buildT (TAbs M)) I A0); trivial.
    inversion H2; trivial.
    absurd (0 = S y).
    lia.
    apply envSub_Lok with (envSubst_lift1 Q) 0; destruct Q; simpl; trivial.
    absurd (0 = S x).
    lia.
    apply envSub_Rok with (envSubst_lift1 Q) 0; destruct Q; simpl; trivial.
    apply (H x y).   
    destruct Q; simpl; trivial.
    rewrite (@activeEnv_abs (buildT (TAbs M)) I).
    change (absBody (M:=buildT (TAbs M)) I) with (buildT M).
    destruct (activeEnv (buildT M)); try_solve.
    try_solve.    
    exists (envSubst_lower Q'); split; trivial.
    intros i j Qij.
    destruct Q; destruct Q'.
    exact (Q'Q (S i) (S j) Qij).
    assert (Q'00: envSub Q' 0 0).
    apply Q'Q; destruct Q; try_solve.
    assert (M''b_t: A [#] tail (env M'b) |- term M'b := type M'b).
    replace (A [#] tail (env M'b)) with ((Some A::EmptyEnv) [+] env M'b).
    apply typing_ext_env_l; exact (typing M'b).
    destruct (env M'b); simpl; trivial.
    destruct o; destruct e; trivial;
      solve [rewrite (M'E0 0 s A); trivial; constructor].
    set (M''b := buildT M''b_t).
    assert (M''0: env M''b |= 0 := A).
    constructor.
    set (M''cond := Build_absCond M''b M''0).
    set (M'' := buildAbs M''cond).
    exists M''; unfold M''; split.
    apply abs_conv with I (buildAbs_isAbs M''cond).
    rewrite buildAbs_absType; trivial.
    rewrite buildAbs_absBody; simpl.
    rewrite (envSubst_lift_lower Q' Q'00); trivial.
    apply terms_conv_diff_env with M'b; trivial.
    apply equiv_term_activeEnv; trivial.
    simpl; intros w C D LC RD.
    destruct w.
    inversion LC.
    sym; apply (M'E0 0); trivial.
    inversion LC; inversion RD; destruct (env M'b); try_solve.
    split.
    rewrite buildAbs_env; simpl.
    clear M''cond M''.
    destruct (env M'b); simpl.
    apply env_comp_empty_r.
    apply env_comp_tail with o (Some A); trivial.
    split.   
    apply envMinimal_abs with M'b (buildAbs_isAbs M''cond); trivial.
    destruct (env M'b); try destruct o.
    compute. auto.
    right; simpl.
    rewrite (M'E0 0 s A); unfold VarD; simpl; trivial.
    left; right; trivial.
    intros x y Q'xy.
    destruct (Q'ext (S x) (S y)).
    destruct Q'; try_solve.
    left; destruct Q; try_solve.
    right; try_solve.

     (* application *)
    destruct (IHM1 Q E0) as [Q' [Q'Q [M'L0 [MM'L [M'Lenv [M'Lmin Q'ext]]]]]].
    intros.
    apply H with x y; trivial.
    rewrite (activeEnv_app (buildT (TApp M1 M2)) I).
    apply env_sum_ly; trivial.
    apply activeEnv_app_comp.
    destruct (IHM2 Q' (E0 [+] env M'L0)) as 
      [Q'' [Q''Q' [M'R0 [MM'R [M'Renv [M'Rmin Q''ext]]]]]].
    intros.
    destruct (env_sum_varDecl E0 (env M'L0) H2) as [[E0y _] | M'L0y].
    apply H with x y; trivial.
    destruct (Q'ext x y); trivial.
    inversion E0y; inversion H3; try_solve.
    rewrite (activeEnv_app (buildT (TApp M1 M2)) I).
    apply env_sum_ry; trivial.
    rewrite M'Lmin in M'L0y.
    sym.
    apply ((activeEnv_app_comp (buildT (TApp M1 M2)) I) x); trivial.    
    set (MM'comp := proj2 MM'L x y H0 B0).
    apply (proj2 MM'comp); trivial.
    exists Q''; split.
    apply envSubst_extends_trans with Q'; trivial.
    assert (M'L_typ: env M'L0 [+] env M'R0 |- term M'L0 := type M'L0).
    apply typing_ext_env_r.
    apply env_comp_sym; trivial.
    apply env_comp_sum_comp_right with E0; trivial.    
    exact (typing M'L0).
    set (M'L := buildT M'L_typ).
    assert (M'R_typ: env M'L0 [+] env M'R0 |- term M'R0 := type M'R0).
    apply typing_ext_env_l.
    exact (typing M'R0).
    set (M'R := buildT M'R_typ).
    assert (envOk: env M'L = env M'R).
    trivial.
    assert (Larr: isArrowType (type M'L)).
    simpl; rewrite <- (terms_conv_eq_type (conv_by MM'L)); try_solve.
    assert (typeOk: type_left (type M'L) = type M'R).
    simpl.
    rewrite <- (terms_conv_eq_type (conv_by MM'L)).
    rewrite <- (terms_conv_eq_type (conv_by MM'R)).
    trivial.
    set (M'cond := Build_appCond M'L M'R envOk Larr typeOk).
    set (M' := buildApp M'cond).
    exists M'; split.
    assert (Conv_term: conv_term (PtL @@ PtR) (term M') Q'').
    unfold M'; rewrite buildApp_preterm; simpl.
    constructor.
    apply conv_term_ext with Q'; trivial.
    destruct MM'L; trivial.
    destruct MM'R; trivial.
    constructor; trivial.
    apply conv_env_app with I (buildApp_isApp M'cond).
    simpl; unfold M'; trivial.
    rewrite buildApp_Lok; simpl.
    apply conv_env_ext with Q'; trivial.
    destruct MM'L; trivial.
    unfold conv_env, activeEnv_compSubst_on.
    rewrite (equiv_term_activeEnv M'L M'L0); trivial.
    destruct MM'L; trivial.
    simpl; apply env_comp_sym; apply env_comp_sum.
    apply env_comp_refl.
    apply env_comp_sym; apply env_comp_sum_comp_right with E0; trivial.
    rewrite buildApp_Rok; simpl. 
    unfold conv_env, activeEnv_compSubst_on.
    rewrite (equiv_term_activeEnv M'R M'R0); trivial.
    destruct MM'R; trivial.
    simpl; apply env_comp_ext_l.
    split.
    unfold M'; rewrite buildApp_env_l; simpl.
    apply env_comp_sym.
    apply env_comp_sum; apply env_comp_sym; trivial.
    apply env_comp_sum_comp_right with (env M'L0); trivial.
    rewrite env_comp_sum_comm; trivial.
    split.
    apply envMinimal_app with M'L0 M'R0; unfold M'; trivial.
    apply buildApp_isApp.
    apply env_comp_sym.
    apply env_comp_sum_comp_right with E0; trivial.
    rewrite buildApp_env_l; trivial.
    rewrite buildApp_preterm; trivial.
    intros x y Q''xy.
    destruct (Q''ext x y); trivial.
    destruct (Q'ext x y); trivial.
    left; trivial.
    right; trivial.
    right; apply env_sumn_ln with (env M'L0); trivial.
  Qed.

  Lemma term_build_conv_ext : forall M Q, exists Q', Q' |=> Q /\ 
    exists M', M ~(Q') M' /\ envMinimal M'.

  Proof.
    intros.
    destruct (@term_build_conv M Q EmptyEnv)
      as [Q' [Q'Q [M' [MM' [_ [Mmin _]]]]]].
    intros; inversion H1; destruct y; try_solve.
    exists Q'; split; trivial.
    exists M'; split; trivial.
  Qed.

  Lemma term_build_conv_rel : forall M N N' Q,
    envSubset (activeEnv N) (activeEnv M) ->
    N ~(Q) N' -> envSub_minimal Q N -> exists Q', Q' |=> Q /\
      exists M', M ~(Q') M' /\ envSubset (env N') (env M').

  Proof.
    intros.
    destruct (@term_build_conv M Q (env N'))
      as [Q' [Q'Q [M' [MM' [Nenv Mmin]]]]].
    intros.
    destruct (envSub_minimal_rev x y H1 H0 H2).
    set (N'y := activeEnv_subset N' H5).
    set (Nenv_conv := proj2 H0 x y H2 x0).
    set (Nx := (proj2 Nenv_conv) H5).
    set (Mx := H x x0 Nx).
    inversion H3; inversion Mx.
    inversion N'y; inversion H4; try_solve.
    exists Q'; split; trivial.
    assert (M'': env N' [+] env M' |- term M' := type M').
    apply typing_ext_env_l; exact (typing M').
    exists (buildT M''); split.
    apply terms_conv_diff_env with M'; trivial.
    apply equiv_term_activeEnv; trivial.
    simpl; apply env_comp_ext_l.
    simpl; apply env_subset_sum_l.
    apply env_comp_sym; trivial.
    apply env_subset_refl.
  Qed.

  Lemma term_build_conv_sim : forall M M' N Q,
    M ~(Q) M' -> envSub_minimal Q M -> env M = env N ->
    envSubset (activeEnv N) (activeEnv M) ->
    exists N', env M' = env N' /\ N ~(Q) N'.

  Proof.
    intros M M' N Q MM' QMmin MNenv MNact.
    destruct (@term_build_conv N Q (env M')) 
      as [Q' [Q'Q [N' [NN' [N'env [N'min _]]]]]].
    intros.
    destruct (QMmin x y H).
    destruct (envSub_minimal_rev x y QMmin MM' H).
    set (M'y_x1 := activeEnv_subset M' H3).
    set (Mx_x0 := activeEnv_subset M H2).
    set (Mx_A := activeEnv_subset N H0).
    rewrite <- MNenv in Mx_A.
    destruct MM'.
    set (M'y_x0 := proj1 (H5 x y H x0) H2).
    inversion Mx_x0; inversion Mx_A.
    inversion H1; inversion M'y_x1.
    inversion M'y_x0; inversion H3.
    try_solve.
    assert (N'': env M' [+] dropEmptySuffix (env N') |- term N' := type N').
    apply typing_ext_env_l.
    apply typing_drop_suffix.
    exact (typing N').
    exists (buildT N''); split.
    simpl; rewrite N'min.
    rewrite term_env_activeEnv.
    rewrite env_sum_assoc.
    set (MQ'M' := terms_conv_extend_subst MM' Q'Q).
    set (N'M'aenv := terms_conv_activeEnv_sub MQ'M' MNact NN').
    rewrite <- (@env_subset_as_sum_r
      (activeEnv M') (dropEmptySuffix (activeEnv N'))); 
      trivial.
    apply env_subset_dropSuffix_length; trivial.
    apply env_subset_trans with (activeEnv N'); trivial.
    apply (proj1 (env_subset_dropSuffix_eq (activeEnv N'))).
    apply terms_conv_diff_env with N'; trivial.
    apply terms_conv_shrink_subst with Q'; trivial.
    intros.
    set (Mx := MNact x A H).
    exact (terms_conv_activeEnv MM' Mx).
    apply equiv_term_activeEnv; trivial.
    simpl.
    apply env_comp_dropSuffix.
    apply env_comp_ext_l.
  Qed.

  Lemma conv_arg : forall M Marg N Q, M ~(Q) N -> isArg Marg M ->
    exists Narg, isArg Narg N /\ Marg ~(Q) Narg.

  Proof.
    intro M.
    apply well_founded_ind with (R := subterm)
      (P := fun M =>
	forall Marg N Q,
	  M ~(Q) N ->
	  isArg Marg M ->
	  exists Narg,
	    isArg Narg N /\ Marg ~(Q) Narg).
    apply subterm_wf.
    clear M; intros M IH Marg N Q MN MargM.
    unfold isArg in MargM.
    destruct (isApp_dec M) as [Mapp | Mnapp].
    rewrite (appArgs_app M Mapp) in MargM.
    set (Napp := proj1 (isApp_morph (conv_by MN)) Mapp).
    destruct (in_app_or MargM).
    set (Msub := appBodyL_subterm M Mapp).
    destruct (IH (appBodyL Mapp) Msub Marg (appBodyL Napp) Q) 
      as [Narg [NargN MNargs]]; trivial.
    apply app_conv_app_left_aux; trivial.
    exists Narg; split; trivial.
    apply appArg_left with Napp; trivial.
    inversion H; try_solve.
    exists (appBodyR Napp); split.
    apply appArg_right with Napp; trivial.
    rewrite <- H0.
    apply app_conv_app_right_aux; trivial.
    rewrite appArgs_notApp in MargM; trivial.
    inversion MargM.
  Qed.

  Lemma conv_arg_rev : forall M N Narg Q, M ~(Q) N -> isArg Narg N ->
    exists Marg, isArg Marg M /\ Marg ~(Q) Narg.

  Proof.
    intros.
    set (NM := terms_conv_sym_aux H).
    destruct (conv_arg Narg NM) as [Marg [MargM NMarg]]; trivial.
    exists Marg; split; trivial.
    rewrite <- (envSubst_transp_twice Q).
    apply terms_conv_sym_aux; trivial.
  Qed.

  #[global] Hint Resolve terms_eq_conv terms_conv_eq_type terms_conv_sym terms_conv_refl 
    terms_conv_trans app_conv_app_left app_conv_app_right (* abs_conv_absBody 
    abs_conv_absType *) : terms_eq.

  Definition conv_list Ms Ns Q := list_sim (fun M N => M ~(Q) N) Ms Ns.

  Lemma appUnits_conv : forall M N Q,
    M ~(Q) N -> conv_list (appUnits M) (appUnits N) Q.

  Proof.
    intro M.
    apply well_founded_ind with (R := subterm)
      (P := fun M =>
	forall N Q,
	  M ~(Q) N ->
	  conv_list (appUnits M) (appUnits N) Q).
    apply subterm_wf.
    clear M; intros M IH N Q MN.
    destruct (isApp_dec M) as [Mapp | Mnapp].
    set (Napp := proj1 (isApp_morph (conv_by MN)) Mapp).
    rewrite (appUnits_app M Mapp).
    rewrite (appUnits_app N Napp).
    unfold conv_list; apply list_sim_app.
    apply IH.
    apply appBodyL_subterm.
    apply app_conv_app_left_aux; trivial.
    constructor.
    apply app_conv_app_right_aux; trivial.
    constructor.
    rewrite !appUnits_notApp; trivial.
    constructor; trivial.
    constructor.
    rewrite <- (conv_by MN); trivial.
  Qed.

  Lemma appArgs_conv : forall M N Q,
    M ~(Q) N -> conv_list (appArgs M) (appArgs N) Q.

  Proof.
    intros.
    set (w := appUnits_conv H).
    inversion w.    
    set (p := appUnits_not_nil M); try_solve.
    unfold appArgs.
    rewrite <- H0; rewrite <- H1; simpl; trivial.
  Qed.

  Lemma appUnit_conv_appUnit : forall M M' N Q, M ~(Q) N -> isAppUnit M' M ->
    exists N', isAppUnit N' N /\ M' ~(Q) N'.

  Proof.
    intros.
    destruct (list_In_nth (appUnits M) M' H0) as [p Mp].
    set (MNunits := appUnits_conv H).
    destruct (list_sim_nth p MNunits Mp) as [N' [Np M'N']].
    exists N'; split; trivial.
    unfold isAppUnit; apply nth_some_in with p; trivial.
  Qed.

  Lemma appArg_conv_appArg : forall M M' N Q, M ~(Q) N -> isArg M' M ->
    exists N', isArg N' N /\ M' ~(Q) N'.

  Proof.
    intros.
    destruct (list_In_nth (appArgs M) M' H0) as [p Mp].
    set (MNargs := appArgs_conv H).
    destruct (list_sim_nth p MNargs Mp) as [N' [Np M'N']].
    exists N'; split; trivial.
    unfold isArg; apply nth_some_in with p; trivial.
  Qed.    

  Lemma partialFlattening_conv : forall M Ms N Q,
    M ~(Q) N -> isPartialFlattening Ms M ->
    exists Ns, isPartialFlattening Ns N /\ conv_list Ms Ns Q.

  Proof.
    destruct M as [E Pt T M]; induction M; intros.
    set (w := partialFlattening_app (buildT (TVar v)) Ms H0); try_solve.
    set (w := partialFlattening_app (buildT (TFun E f)) Ms H0); try_solve.
    set (w := partialFlattening_app (buildT (TAbs M)) Ms H0); try_solve.
    assert (Napp: isApp N).
    assert (H' : (buildT (TApp M1 M2)) ~ N) by (exists Q; trivial).
    rewrite <- H'; simpl; trivial.
    destruct (partialFlattening_inv (buildT (TApp M1 M2)) I Ms) 
      as [Ms_def | [Ms' [Ms'l MsMs']]]; trivial.
    exists (appBodyL Napp :: appBodyR Napp :: nil); split.
    unfold isPartialFlattening; rewrite (appUnits_app N Napp); trivial.
    rewrite Ms_def.
    constructor.
    apply app_conv_app_left_aux; trivial.
    constructor.
    apply app_conv_app_right_aux; trivial.
    constructor.
    destruct (IHM1 Ms' (appBodyL Napp) Q) as [Ns' [Ns'Nl Ms'Ns']]; trivial.
    change (buildT M1) with (@appBodyL (buildT (TApp M1 M2)) I).
    apply app_conv_app_left_aux; trivial.
    exists (Ns' ++ appBodyR Napp :: nil); split.
    unfold isPartialFlattening.
    destruct Ns'; try solve [inversion Ns'Nl].
    destruct Ns'; try solve [inversion Ns'Nl].
    simpl in * ; rewrite app_comm_cons.
    rewrite <- app_ass; rewrite Ns'Nl.
    sym; apply appUnits_app.
    rewrite MsMs'.
    unfold conv_list; apply list_sim_app; trivial.
    constructor.
    apply app_conv_app_right_aux; trivial.
    constructor.
  Qed.

  Lemma apply_variable : forall M, isArrowType M.(type) ->
    exists MA: Term, exists Mapp: isApp MA, 
      (appBodyL Mapp) ~ M /\ term (appBodyR Mapp) = %length (env M) /\ 
      env MA = env M ++ Some (type_left (type M))::EmptyEnv.

  Proof.
    intros M MA.
    destruct M as [ME MPt [T | A B] M]; try_solve.
    set (newVarEnv := copy (length ME) None ++ (Some A::EmptyEnv)).
    assert (RL: newVarEnv [+] ME |- MPt := A --> B).
    apply typing_ext_env_l; trivial.
    assert (RR: newVarEnv [+] ME |- %(length ME) := A).
    constructor.
    apply env_sum_ly_rn.
    unfold newVarEnv, VarD.
    rewrite nth_app_right; autorewrite with datatypes using auto.
    rewrite <- Minus.minus_n_n; trivial.
    left; apply nth_beyond; auto.
    assert (envOk: env (buildT RL) = env (buildT RR)); trivial.
    assert (Larr: isArrowType (type (buildT RL))); trivial.
    assert (TypOk: type_left (type (buildT RL)) = type (buildT RR)); trivial.
    set (w := Build_appCond (buildT RL) (buildT RR) envOk Larr TypOk).
    exists (buildApp w).
    exists (buildApp_isApp w); repeat split; simpl.
    apply terms_conv_criterion.
    simpl; apply env_comp_ext_l.
    trivial.
    unfold newVarEnv.
    rewrite env_sum_disjoint; trivial.
  Qed.

End TermsConv.
