(************************************************************************
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17

general lemmas and tactics
************************************************************************)

(* $Id: LogicUtil.v,v 1.1.1.1 2006-09-08 09:07:00 blanqui Exp $ *)

Set Implicit Arguments.

Ltac deduce h := generalize h; intro.

Ltac refl := reflexivity.

Ltac decomp h := decompose [and or ex] h; clear h.

Ltac irrefl :=
  match goal with
    | _ : ?x <> ?x |- _ => absurd (x=x); [assumption | refl]
    | _ : ?x <> ?y, _ : ?x = ?y |- _ => subst y; irrefl
    | _ : ?x <> ?y, _ : ?y = ?x |- _ => subst y; irrefl
    | _ : ?x <> ?y, _ : ?x = ?z, _ : ?z = ?y |- _ => subst y; irrefl
    | _ : ?x <> ?y, _ : ?x = ?z, _ : ?y = ?z |- _ => subst y; irrefl
    | _ : ?x <> ?y, _ : ?z = ?x, _ : ?z = ?y |- _ => subst y; irrefl
    | _ : ?x <> ?y, _ : ?z = ?x, _ : ?y = ?z |- _ => subst y; irrefl
  end.
