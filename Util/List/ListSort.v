(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2008-09-17

sorting functions on lists
*)

(* $Id: ListSort.v,v 1.1 2008-09-19 03:04:23 blanqui Exp $ *)

Set Implicit Arguments.

Require Export List.

Section S.

Variable A : Type.
Variable cmp : A -> A -> comparison.

Fixpoint insert x (l : list A) :=
  match l with
    | nil => cons x nil
    | cons y m =>
      match cmp x y with
        | Gt => cons y (insert x m)
        | _ => cons x l
      end
  end.

Fixpoint sort (l : list A) : list A :=
  match l with
    | nil => nil
    | cons x m => insert x (sort m)
  end.

End S.
