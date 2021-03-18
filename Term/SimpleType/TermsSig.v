(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2006-04-27

This file presents the definition of simple types
for the development of theory of simpe typed lambda-calculus.
*)

Set Implicit Arguments.

Module Type BaseTypes.

   (* Base types; denoted as a, b, c, ... *)
  Parameter BaseType : Type.
  Implicit Types a b c : BaseType.
   (* Equality on base types needs to be decidable *)
  Parameter eq_BaseType_dec : forall (a b: BaseType), {a=b}+{~a=b}.
  #[global] Hint Resolve eq_BaseType_dec : terms.
   (* To ensure that set of base types is not empty *)
  Parameter baseTypesNotEmpty : BaseType.

End BaseTypes.

(* ==================================================================
     Specification of simple types. They are built using base types
   that are given as a parameter to this module.
   ================================================================== *)
Module SimpleTypes (BT : BaseTypes).

  Export BT.

   (*
      Simple types: either basic types or arrow types A->B with A and B 
      simple types. We denote them as A, B, C, ...
    *)
  Inductive SimpleType : Type :=
    | BasicType(T: BaseType)
    | ArrowType(A B : SimpleType).
  Notation "x --> y" := (ArrowType x y) 
    (at level 55, right associativity) : type_scope.
  Notation "# x " := (BasicType x) (at level 0) : type_scope.
  Implicit Types A B C : SimpleType.
  #[global] Hint Constructors SimpleType : terms.

End SimpleTypes.

(* ==================================================================
     Specification of signature.
     Signature consists of a non-empty set of function symbols 
   (FunctionSymbol) with given types (f_type).
   ================================================================== *)
Module Type Signature.

  Declare Module BT : BaseTypes.

  Module Export ST := SimpleTypes BT.

   (* Function symbols, denoted as f, g, h, ... *)
  Parameter FunctionSymbol : Type.
  Implicit Types f g h : FunctionSymbol.

   (* Equality on function symbols needs to be decidable *)
  Parameter eq_FunctionSymbol_dec : forall (f g: FunctionSymbol), 
    {f=g} + {~f=g}.
  #[global] Hint Resolve eq_FunctionSymbol_dec : terms.

    (* To ensure that set of function symbols is not empty *)
  Parameter functionSymbolsNotEmpty : FunctionSymbol.

    (* Types for function symbols *)
  Parameter f_type : FunctionSymbol -> SimpleType.

End Signature.
