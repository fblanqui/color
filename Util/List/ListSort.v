(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2008-09-17

sorting functions on lists
*)

Set Implicit Arguments.

From Stdlib Require Import List.

Section S.

  Variables (A : Type) (cmp : A -> A -> comparison).

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
