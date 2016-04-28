(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2006-04-27

Constructing terms.
*)

Set Implicit Arguments.

From CoLoR Require Import RelExtras ListExtras LogicUtil.
From CoLoR Require TermsActiveEnv.
From Coq Require Import Omega.

Module TermsBuilding (Sig : TermsSig.Signature).

  Module Export TAE := TermsActiveEnv.TermsActiveEnv Sig.

  Record appCond : Type := {
     appL: Term;
     appR: Term;
     eqEnv: env appL = env appR;
     typArr: isArrowType (type appL);
     typOk: type_left (type appL) = type appR
  }.

  Definition buildApp : appCond -> Term.

  Proof.
    intro t; inversion t as [L R eq_env typ_arr typ_ok].
    destruct L; destruct R; simpl in *.
    rewrite eq_env in typing0.
    destruct type0; try contr; simpl in *.
    rewrite typ_ok in typing0.
    exact (buildT (TApp typing0 typing1)).
  Defined.

  Lemma buildApp_isApp : forall a, isApp (buildApp a).

  Proof.
    intros; destruct a; term_type_inv appL0; term_type_inv appR0.
  Qed.

  Lemma buildApp_Lok : forall a, appBodyL (buildApp_isApp a) = a.(appL).

  Proof.
    destruct a; destruct appR0; term_type_inv appL0.
  Qed.

  Lemma buildApp_Rok : forall a, appBodyR (buildApp_isApp a) = a.(appR).

  Proof.
    destruct a; destruct appR0; term_type_inv appL0.
  Qed.

  Lemma buildApp_preterm : forall a,
    term (buildApp a) = term a.(appL) @@ term a.(appR).

  Proof.
    destruct a; destruct appR0; term_type_inv appL0.
  Qed.

  Lemma buildApp_env_l : forall a, env (buildApp a) = env a.(appL).

  Proof.
    destruct a; destruct appR0; term_type_inv appL0.
  Qed.

  Lemma buildApp_type : forall a,
    type (buildApp a) = type_right (type a.(appL)).

  Proof.
    destruct a; destruct appR0; term_type_inv appL0.
  Qed.

  Record absCond : Type := {
    absB: Term;
    absT: SimpleType;
    envNotEmpty: env absB |= 0 := absT
  }.
  
  Definition buildAbs : absCond -> Term.

  Proof.
    intro t; inversion t as [aBody aType envCond].
    destruct aBody; simpl in *; destruct env0.
    try_solve.
    destruct o.
    exact (buildT (TAbs typing0)).
    try_solve.
  Defined.

  Lemma buildAbs_isAbs: forall a, isAbs (buildAbs a).
  Proof.
    destruct a; destruct absB0; destruct env0.
    try_solve.
    destruct o; try_solve.
  Qed.

  Lemma buildAbs_absBody : forall a, absBody (buildAbs_isAbs a) = a.(absB).

  Proof.
    destruct a; destruct absB0; destruct env0.
    try_solve.
    destruct o; try_solve.
  Qed.

  Lemma buildAbs_absType : forall a, absType (buildAbs_isAbs a) = a.(absT).

  Proof.
    destruct a; destruct absB0; destruct env0.
    try_solve.
    destruct o; try_solve.
    unfold VarD in * .
    inversion envNotEmpty0; trivial.
  Qed.

  Lemma buildAbs_env : forall a, env (buildAbs a) = tail (env a.(absB)).

  Proof.
    destruct a; destruct absB0; destruct env0.
    try_solve.
    destruct o; try_solve.
  Qed.

  Definition buildVar : forall A x, (copy x None ++ A [#] EmptyEnv) |- %x := A.

  Proof.
    constructor; unfold VarD.
    rewrite nth_app_right; autorewrite with datatypes using try omega.
    replace (x - x) with 0; trivial.
    omega.
  Defined.

  Lemma buildVar_minimal : forall A x, envMinimal (buildT (buildVar A x)).

  Proof.
    intros; unfold envMinimal; trivial.
  Qed.

End TermsBuilding.
