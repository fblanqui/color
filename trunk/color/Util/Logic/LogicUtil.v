(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17

general lemmas and tactics
*)

(* $Id: LogicUtil.v,v 1.6 2007-05-24 15:18:11 blanqui Exp $ *)

Set Implicit Arguments.

Definition prop_dec A (P : A -> Prop) := forall x, {P x}+{~P x}.

Ltac refl := reflexivity.

Ltac gen h := generalize h.

Ltac deduce h := gen h; intro.

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

Ltac normalize e :=
  let x := fresh in set (x := e); vm_compute in x; subst x.

Ltac normalize_in H e :=
  let x := fresh in set (x := e) in H; vm_compute in x; subst x.
