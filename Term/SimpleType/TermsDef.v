(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2006-04-27

This file provides a definition of terms of simply typed
lambda-calculus.
*)

Set Implicit Arguments.

From CoLoR Require Import RelExtras ListExtras TermsSig.
From Stdlib Require Setoid.

Module TermsDef (Sig : Signature).

  Export Sig.

   (*
      We introduce equivalence relation on types by identifying all 
      base types. So two types are equivalent (we denote it with '==' 
      symbol) when they have the same arrow structure.
   *)
  Fixpoint TypeEq (A B: SimpleType) { struct A } : Prop :=
  match A, B with
  | A1-->A2, B1-->B2 => TypeEq A1 B1 /\ TypeEq A2 B2
  | #_, #_ => True
  | _, _ => False
  end.

  Notation "A == B" := (TypeEq A B) (at level 70).
  #[global] Hint Unfold TypeEq : terms.

  Definition isArrowType (A: SimpleType) : Prop :=
    match A with
    | _ --> _ => True
    | _ => False
    end.

  Definition isBaseType (A: SimpleType) : Prop :=
    match A with
    | #b => True
    | _ => False
    end.

  #[global] Hint Unfold isArrowType isBaseType : terms.

  (* 
     Every simple type A can be written in an unique way as:
      A1 -> A2 -> ... -> An -> b
     with 'b' of base type. We have following functions to perform this 
     decomposition:
     -/ type_result: returns 'b'
     -/ type_prefix: returns (Some A1->...->An) or None if A itself is 
                     of a base type
     -/ type_head: returns A1
   *)
  Definition type_left (A: SimpleType) : SimpleType :=
     match A with
     | #b => #b
     | A1 --> A2 => A1
     end.

  Definition type_right (A: SimpleType) : SimpleType :=
    match A with
    | #b => #b
    | A1 --> A2 => A2
    end.

  Lemma type_eq_equiv : forall A B, A = B -> A == B.

  Proof.
    induction A; intros; rewrite <- H; simpl; auto.
  Qed.
  #[global] Hint Resolve type_eq_equiv : terms.

   (* 
        We are using de Bruijn indices for bindings so environments are 
      simply lists of simple types.
   *)
  Definition Env := list (option SimpleType).
  Definition EmptyEnv : Env := nil.
  Implicit Type x y : nat.
  Implicit Type E : Env.

   (* 
        'Typ E x A' states that variable x in environment E is declared
      to have type A.
    *)
  Definition VarD  E x A := nth_error E x = Some (Some A).
  Definition VarUD E x := nth_error E x = None \/ 
                          nth_error E x = Some None.
  Notation "E |= x := A" := (VarD E x A) (at level 60).
  Notation "E |= x :!" := (VarUD E x) (at level 60).

   (* 'decl A E' returns environment E with new declaration for A *)
  Definition decl A E := Some A::E.
  Infix "[#]" := decl (at level 20, right associativity).  
   (* 'declDummy E' returns environment E with new dummy variable *)
  Definition declDummy E := None::E.
  #[global] Hint Unfold VarD VarUD decl declDummy EmptyEnv : terms.

   (* 
      Preterm represents the set of preterms
    *)
  Inductive Preterm : Type :=
   | Var(x: nat)
   | Fun(f: FunctionSymbol)
   | Abs(A: SimpleType)(M: Preterm)
   | App(M N: Preterm).

   (* Some notation for preterms *)
  Implicit Type Pt : Preterm.
  Notation "^ f" := (Fun f) (at level 20).
  Notation "% x" := (Var x) (at level 20).
  Infix "@@" := App (at level 25, left associativity).
  Notation "s [ x ]" := (s @@ x) (at level 50).
  Notation "s [ x , y ]" := (s @@ x @@ y) (at level 50).
  Notation "s [ x , y , z ]" := (s @@ x @@ y @@ z) (at level 50).
  Notation "s [ x , y , z , w ]" := (s @@ x @@ y @@ z @@ w) 
    (at level 50).
  Notation "s [ x , y , z , w , v ]" := (s @@ x @@ y @@ z @@ w @@ v) 
    (at level 50).
  Notation "\ A => M" := (Abs A M) (at level 35).

  Reserved Notation "E |- Pt := A" (at level 60).
  Inductive Typing : Env -> Preterm -> SimpleType -> Type :=
  | TVar: forall E x A, 
            E |= x := A -> 
            E |- %x := A
  | TFun: forall E f, 
            E |- ^f := f_type f
  | TAbs: forall E A B Pt, 
            A [#] E |- Pt := B -> 
            E |- \A => Pt := A --> B
  | TApp: forall E A B PtL PtR, 
            E |- PtL := A --> B -> 
            E |- PtR := A -> 
            E |- PtL @@ PtR := B
  where "E |- Pt := A" := (Typing E Pt A).

  #[global] Hint Constructors Typing : terms.
  #[global] Hint Extern 5 (?X1 |- %?X2 := ?X3) => 
         (apply TVar; auto with terms) : terms.
  #[global] Hint Extern 5 (?X1 |- ^?X2 := ?X3) => 
         (apply TFun with (f := X2); auto with terms) : terms.
  #[global] Hint Extern 5 (?X1 |- \?X2 => ?X3 := ?X4) =>
         (apply TAbs; auto with terms) : terms.

  Record Term : Type := buildT { 
    env: Env;
    term: Preterm;
    type: SimpleType; 
    typing: Typing env term type
  }.
  Implicit Types M N T : Term.
  Definition TermTyping M : Type := Typing M.(env) M.(term) M.(type).

  Ltac term_inv X := 
     let  env := fresh "E"
     with term := fresh "Pt"
     with termL := fresh "PtL"
     with termR := fresh "PtR"
     with type := fresh "A"
     with type' := fresh "B"
     with typing := fresh "T"
     with name := fresh "Tr"
     with var := fresh "x"
     with funS := fresh "f"
     in (
       first [intros until X | idtac];
       set (name := X) in *;
       destruct X as [env term type typing];
       destruct typing as [ env var type typing
                          | env funS
			  | env type type' term typing
			  | env type type' termL termR
			  ];
       try_solve
     ).

  Ltac term_type_inv X := 
     let  env := fresh "E"
     with term := fresh "Pt"
     with type := fresh "A"
     with typing := fresh "Typ"
     in (
       first [simpl in X | intros until X];
       destruct X as [env term type typing];
       destruct type;
       try_solve
     ).

End TermsDef.
