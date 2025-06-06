(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2006-04-27

Some results concerning typing of terms of simply typed
lambda-calculus are introduced in this file.
*)

Set Implicit Arguments.

From Stdlib Require Import Eqdep_dec.
From CoLoR Require Import RelExtras ListExtras LogicUtil.
From CoLoR Require TermsDef.

Module TermsTyping (Sig : TermsSig.Signature).

  Module Export TD := TermsDef.TermsDef Sig.

  Lemma baseType_dec : forall A, {isBaseType A} + {isArrowType A}.

  Proof. destruct A; fo. Qed.

  Lemma type_discr : forall A B, ~A = A --> B.

  Proof.
    induction A; unfold not; simpl; intros. discr.
    unfold not in *. inversion H. eapply IHA1. apply H1.
  Qed.

  Lemma type_discr2 : forall A B C, ~A = (A --> B) --> C.

  Proof.
    induction A; unfold not; simpl; intros. discr.
    unfold not in *. inversion H. eapply IHA1. apply H1.
  Qed.

(*Section Equality_Decidable.*)

(* FIXME: eq_nat_dec has to be redefined here for the following Hint
Resolve, otherwise it does not work! *)
  Lemma eq_nat_dec : forall (m n: nat), {m=n}+{m<>n}.

  Proof. decide equality. Qed.

  #[global] Hint Resolve eq_nat_dec : terms.

  Lemma eq_SimpleType_dec : forall (A B: SimpleType), {A=B} + {A<>B}.

  Proof. decide equality; auto with terms. Defined.

  #[global] Hint Resolve eq_SimpleType_dec : terms.

  Lemma eq_Env_dec : forall (E1 E2 : Env), {E1=E2} + {E1<>E2}.

  Proof.
    decide equality; generalize a o; decide equality; apply eq_SimpleType_dec.
  Defined.

  #[global] Hint Resolve eq_Env_dec : terms.

  Lemma eq_Preterm_dec : forall (F G: Preterm), {F=G}+{F<>G}.

  Proof. decide equality; auto with terms. Defined.

  #[global] Hint Resolve eq_Preterm_dec : terms.

  Lemma isVarDecl_dec : forall E x,
    {A: SimpleType | E |= x := A} + {E |= x :!}.

  Proof.
    intros; unfold VarUD.
    destruct (nth_error_In E x) as [[A ExA] | Exn].
    destruct A.
    left; exists s; trivial.
    right; auto.
    right; auto.
  Defined.

  Lemma eq_EPS_dec :
    forall (a b : Env * Preterm * SimpleType), {a=b} + {a<>b}.

  Proof.
    decide equality.
    apply eq_SimpleType_dec.
    generalize a p; decide equality.
    apply eq_Preterm_dec.
    apply eq_Env_dec.
  Defined.

(*Section Typing.*)

  Lemma VarD_unique : forall E x A (v1 v2 : VarD E x A), v1 = v2.

  Proof.
    unfold VarD; intros; generalize v1 v2; rewrite v1.
    intros; apply K_dec_type; 
      [idtac |  pattern v0; apply K_dec_type]; 
      auto; decide equality; generalize a o; decide equality; 
      apply eq_SimpleType_dec.
  Qed.

  Lemma Type_unique : forall Pt E T1 T2 (d1 : Typing E Pt T1)
    (d2 : Typing E Pt T2), T1 = T2.

  Proof.
    induction Pt; intros; inversion d1; 
      inversion d2; trivial.
    unfold  VarD in * .
    assert(Some (Some T1) = Some (Some T2)).
    trans (nth_error E x); auto.
    injection H7; trivial.
    rewrite(@IHPt _ _ _ X X0); auto.
    set(e0 := IHPt1 _ _ _ X X1); injection e0; auto.
  Qed.

  Lemma typing_unique : forall E Pt T (d1 d2 : Typing E Pt T), d1 = d2.

  Proof.
    refine(
      fix Deriv_unique e t T (d1 d2 : Typing e t T) {struct d1}
       : d1 = d2 :=
      match d1 as d1' in Typing e1 t1 T1, 
	    d2 as d2' in Typing e2 t2 T2 
      return 
        forall (cast : (e1,t1,T1) = (e2,t2,T2)), 
          (e1,t1,T1) = (e,t,T) ->
          eq_rect (e1,t1,T1) 
	  (fun etT => 
	     match etT with 
	    (e,t,T) => Typing e t T 
	    end) 
	  d1' _ cast = d2'
      with
      | TVar _, TVar _ => _
      | TFun _ _, TFun _ _ => _
      | TAbs _, TAbs _ => _
      | TApp _ _, TApp _ _ => _
      | _, _ => _
      end (eq_refl _) (eq_refl _));
    intros; destruct t; try discr;
    try discr cast; try discr dis;
    injection cast; intros; gen cast; clear cast.

    revert v v0.
    rewrite H0; rewrite H1; rewrite H2.
    intros; pattern cast; apply (K_dec_type eq_EPS_dec).
    rewrite (VarD_unique v v0); apply eq_refl.

    rewrite H1; rewrite H2.
    intros; pattern cast; apply (K_dec_type eq_EPS_dec); 
      apply eq_refl.

    revert t1.
    rewrite <- H0; rewrite <- H1; rewrite <- H2; rewrite <- H4.
    intros; pattern cast; apply (K_dec_type eq_EPS_dec).
    rewrite(Deriv_unique _ _ _ t0 t1); apply eq_refl.

    revert t2 t3.
    rewrite <- H0; rewrite <- H1; rewrite <- H2; rewrite <- H3.
    intros t2 t3.
    intros; pattern cast; apply (K_dec_type eq_EPS_dec).
    set(h1 := Type_unique t0 t2); injection h1; intro H7.
    clear h1. revert t2 t3. rewrite <- H7.
    intros; rewrite(Deriv_unique _ _ _ t0 t2); 
      rewrite(Deriv_unique _ _ _ t1 t3);
    apply eq_refl.
  Qed.

  Lemma deriv_uniq : forall M N, env M = env N -> term M = term N ->
    type M = type N -> M = N.

  Proof.
    intros [??? typingM] [??? typingN] H H0 H1; simpl in *.
    revert typingM.
    rewrite H; rewrite H0; rewrite H1.
    intros.
    rewrite(typing_unique typingM typingN).
    apply eq_refl.
  Qed.

  Lemma typing_uniq : forall M N, env M = env N -> term M = term N ->
    type M = type N.

  Proof.
    intros; destruct M as [??? typingM]; destruct N as [??? typingN]; simpl in *.
    revert typingM.
    rewrite H; rewrite H0; intros.
    apply (Type_unique typingM typingN).
  Qed.

  Lemma term_eq : forall M N, env M = env N -> term M = term N -> M = N.

  Proof.
    intros; apply deriv_uniq; auto.
    apply typing_uniq; auto.
  Qed.

  Lemma eq_Term_dec : forall (M N: Term), {M=N} + {M<>N}.

  Proof.
     intros M N.
     case (eq_Env_dec M.(env) N.(env)); 
       case (eq_Preterm_dec M.(term) N.(term));
       case (eq_SimpleType_dec M.(type) N.(type));
       try solve [right; congruence].
     left; apply deriv_uniq; trivial.
  Qed.

  #[global] Hint Resolve typing_uniq deriv_uniq term_eq : terms.

(*Section Auto_Typing.*)
  
  Definition autoType : forall E Pt, {N: Term | env N = E & term N = Pt} + 
    {~exists N: Term, env N = E /\ term N = Pt}.

  Proof.
    intros E Pt. revert Pt E. induction Pt; intro E.
     (* -) variable *)
    destruct (isVarDecl_dec E x) as [[A xt] | xut].
     (*   - variable declared *)
    left.
    exists (buildT (TVar xt)); trivial. 
     (*   - variable undeclared *)
    right.
    intro abs; destruct abs as [T [T_env T_term]].
    term_inv T.
    unfold VarD in T0.
    destruct xut; congruence.
     (* -) function symbol *)
    left.
    assert (t: E |- ^f := f_type f).
    constructor.
    exists (buildT t); trivial.
     (* -) abstraction *)
    destruct (IHPt (decl A E)) as [[T T_env T_term] | Tne].
     (*   - typable *)
    left.
    assert (t: E |- \A => Pt := A --> type T).
    constructor.
    rewrite <- T_env.
    rewrite <- T_term.
    exact (typing T).
    exists (buildT t); trivial.
     (*   - no-typable *)
    right.
    intro Nt.
    destruct Nt as [T [T_env T_term]].
    absurd (exists N, env N = decl A E /\ term N = Pt); trivial.
    destruct T as [TE TPt TA TT].
    inversion TT; simpl in *; try congruence.
    exists (buildT X); split; simpl; congruence.
     (* -) application *)
    destruct (IHPt1 E) as [[Tl Tl_env Tl_term] | Tln].
    destruct (IHPt2 E) as [[Tr Tr_env Tr_term] | Trn].
    destruct Tl as [EL PtL AL TypL].
    destruct Tr as [ER PtR AR TypR].
    simpl in *.
    destruct AL.
     (*   - bad: left argument of simple type *)
    right.
    intro Tl; destruct Tl as [Tl [envL termL]].
    destruct Tl as [EL' PtL' AL TypL'].
    simpl in *.
    rewrite termL in TypL'.
    inversion TypL'.
    assert (buildT X = buildT TypL).
    apply term_eq; simpl; congruence.
    absurd (A --> AL = #T).
    discr.
    eapply Type_unique. apply X.
    rewrite envL; rewrite <- Tl_env; rewrite <- Tl_term; hyp.
    destruct (eq_SimpleType_dec AL1 AR) as [AL1_AR | AL1_ne_AR].
     (*   - all ok *)
    left.
    assert (t: E |- PtL @@ PtR := AL2).
    constructor 4 with AL1.
    rewrite <- Tl_env; trivial.
    rewrite <- Tr_env; rewrite AL1_AR; trivial.
    exists (buildT t); trivial.
    simpl; congruence.
     (*   - bad: types do not match *)
    right.
    intro Tl; destruct Tl as [Tl [envL termL]].
    destruct Tl as [EL' PtL' AL TypL'].
    simpl in *.
    rewrite termL in TypL'.
    inversion TypL'.
    absurd (AL1 = AR).
    trivial.
    assert (type (buildT TypL) = type (buildT X)).
    apply typing_uniq; simpl; congruence.
    assert (type (buildT TypR) = type (buildT X0)).
    apply typing_uniq; simpl; congruence.
    simpl in *; congruence.
     (*   - bad: right argument not typable *)
    right.
    intro Tr; destruct Tr as [Tr [envR termR]].
    destruct Tr as [ER PtR AR TypR].
    simpl in *.
    rewrite termR in TypR.
    inversion TypR.
    apply Trn.
    exists (buildT X0); auto.
     (*   - bad: left argument not typable *)
    right.
    intro Tl; destruct Tl as [Tl [envL termL]].
    destruct Tl as [EL PtL AL TypL].
    simpl in *.
    rewrite termL in TypL.
    inversion TypL.
    apply Tln.
    exists (buildT X); auto.
  Defined.

  Definition typeTerm (E: Env) (Pt: Preterm) (T: SimpleType) : option Term.

  Proof.
     intros.
     destruct (autoType E Pt) as [[W Wenv Wterm] | x].
     destruct (eq_SimpleType_dec (type W) T).
     exact (Some W).
     exact None.
     exact None.
  Defined.

Module TermsSet <: SetA.
  Definition A := Term.
End TermsSet.

Module TermsEqset <: Eqset := Eqset_def TermsSet.

Module TermsEqset_dec <: Eqset_dec.

  Module Export Eq := TermsEqset.

  Definition eqA_dec := eq_Term_dec.

End TermsEqset_dec.

Ltac infer_tt :=
  compute;
    match goal with
    | |- _ |- ?t := _ =>
      match t with
      | App _ _ => eapply TApp; infer_tt
      | Abs _ _ => eapply TAbs; infer_tt
      | Fun _ => intuition auto with *
      | Var _ => eapply TVar; compute; trivial
      end
    end.

End TermsTyping.
