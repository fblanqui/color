(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17

general lemmas and tactics
*)

Set Implicit Arguments.

(***********************************************************************)
(** tactics *)

Ltac hyp := assumption.

Ltac refl := reflexivity.
(* We need that because in presence of Program module 'refl' is hidden *)
Ltac reflx := reflexivity. 

Ltac gen h := generalize h; clear h.

Ltac ded h := generalize h; intro.

Ltac decomp h := decompose [and or ex] h; clear h.

Ltac discr := intros; discriminate.

Ltac irrefl := intros;
  match goal with
    | _ : ?x = ?x -> False |- _ => absurd (x=x); [assumption | refl]
    | _ : ?x <> ?x |- _ => absurd (x=x); [assumption | refl]
    | _ : ?x <> ?y, _ : ?x = ?y |- _ => subst y; irrefl
    | _ : ?x <> ?y, _ : ?y = ?x |- _ => subst y; irrefl
    | _ : ?x <> ?y, _ : ?x = ?z, _ : ?z = ?y |- _ => subst y; irrefl
    | _ : ?x <> ?y, _ : ?x = ?z, _ : ?y = ?z |- _ => subst y; irrefl
    | _ : ?x <> ?y, _ : ?z = ?x, _ : ?z = ?y |- _ => subst y; irrefl
    | _ : ?x <> ?y, _ : ?z = ?x, _ : ?y = ?z |- _ => subst y; irrefl
  end.

Ltac norm e :=
  let x := fresh in set (x := e); vm_compute in x; subst x.

Ltac norm_in H e :=
  let x := fresh in set (x := e) in H; vm_compute in x; subst x.

(*Tactic Notation "norm" constr(e) "in" ident(H) := norm_in H e.*)

Ltac coq_case_eq x := generalize (refl_equal x); pattern x at -1; case x.

Ltac case_eq e := coq_case_eq e; intros.

(***********************************************************************)
(** basic meta-theorems *)

Section meta.

Lemma contraposee_inv : forall P Q : Prop, (P -> Q) -> ~Q -> ~P.

Proof.
intros. intro. apply H0. exact (H H1).
Qed.

Variables (A : Type) (P : A -> Prop).

Lemma not_exists_imply_forall_not : ~(exists x, P x) -> forall x, ~P x.

Proof.
intros. intro. apply H. exists x. exact H0.
Qed.

Lemma forall_not_imply_not_exists : (forall x, ~(P x)) -> ~(exists x, P x).

Proof.
intros. intro. destruct H0. exact (H x H0).
Qed.

Lemma exists_not_imply_not_forall : (exists x, ~(P x)) -> ~(forall x, P x).

Proof.
intros. destruct H. intro. ded (H0 x). contradiction.
Qed.

End meta.
