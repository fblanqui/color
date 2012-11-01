(**

CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17
- Pierre-Yves Strub, 2009-04-09

* Basic lemmas and tactics
*)

Set Implicit Arguments.

(***********************************************************************)
(** Abbreviations of some basic Coq tactics. *)

Ltac hyp := assumption.
Ltac ehyp := eassumption.
Ltac refl := reflexivity.
Ltac sym := symmetry.
Ltac trans x := transitivity x.
Ltac contr := contradiction.
Ltac discr := intros; discriminate.
Ltac fo := firstorder.
Ltac gen t := generalize t.

Ltac ded t := gen t; intro.

(***********************************************************************)
(** [geneq H x e(x)] transforms a goal [G(x)] into
[forall t, H t -> forall x, e(x) = t -> G(x)] *)

Ltac geneq H x e := gen (refl_equal e); gen (H e);
  clear H; generalize e at -2; let t := fresh "t" in let h := fresh "h" in
    intros t h; revert t h x.

(***********************************************************************)
(** Tactics for decomposing disjunctions and conjonctions. *)

Ltac decomp h := decompose [and or ex] h; clear h.

(*REMOVE? can be replaced by decomp?*)
Ltac decomp_hyp H := 
  match type of H with
  | _ /\ _ => decompose [and] H
  | _ \/ _ => decompose [or] H
  | ex _ => decompose [ex] H
  | sig _ => decompose record H
  end;
  clear H.

Ltac decomp_hyps := repeat
  match goal with
    | H: _ |- _ => decomp_hyp H
  end.

(***********************************************************************)
(** Tactic that can be used to conclude when there is an assumption of
the form [x <> x]. *)

Ltac irrefl := intros;
  match goal with
    | _ : ?x = ?x -> False |- _ => absurd (x=x); [hyp | refl]
    | _ : ?x <> ?x |- _ => absurd (x=x); [hyp | refl]
    | _ : ?x <> ?y, _ : ?x = ?y |- _ => subst y; irrefl
    | _ : ?x <> ?y, _ : ?y = ?x |- _ => subst y; irrefl
    | _ : ?x <> ?y, _ : ?x = ?z, _ : ?z = ?y |- _ => subst y; irrefl
    | _ : ?x <> ?y, _ : ?x = ?z, _ : ?y = ?z |- _ => subst y; irrefl
    | _ : ?x <> ?y, _ : ?z = ?x, _ : ?z = ?y |- _ => subst y; irrefl
    | _ : ?x <> ?y, _ : ?z = ?x, _ : ?y = ?z |- _ => subst y; irrefl
  end.

(***********************************************************************)
(** Normalization tactics (used in Rainbow). *)

Ltac norm e :=
  let x := fresh in set (x := e); vm_compute in x; subst x.

Ltac norm_in H e :=
  let x := fresh in set (x := e) in H; vm_compute in x; subst x.

Ltac check_eq := vm_compute; refl.

(*FIXME: Tactic Notation "norm" constr(e) "in" ident(H) := norm_in H e.*)

(*REMOVE since it can be replaced by rewrite R1, R2, ...*)
(***********************************************************************)
(** Rewriting tactics. *)

Tactic Notation "rwn" constr(R1) constr(R2) :=
  rewrite R1; rewrite R2.

Tactic Notation "rwn" constr(R1) constr(R2) constr(R3) :=
  rewrite R1; rewrite R2; rewrite R3.

(***********************************************************************)
(** Other tactics. *)

Ltac done :=
  trivial; hnf; intros; solve
   [ repeat progress first
       [solve [trivial | apply sym_equal; trivial]
         | discr | contr | split]
   | hyp
   | match goal with H : ~ _ |- _ => solve [case H; trivial] end ].

Tactic Notation "by" tactic(T) := (T; done) .

(***********************************************************************)
(** Basic theorems on (intuitionist) propositional calculus. *)

Lemma contraposee_inv : forall P Q : Prop, (P -> Q) -> ~Q -> ~P.

Proof. fo. Qed.

Lemma and_assoc : forall P Q R, P /\ Q /\ R <-> (P /\ Q) /\ R.

Proof. fo. Qed.

Lemma or_sym : forall P Q, P \/ Q <-> Q \/ P.

Proof. fo. Qed.

Lemma and_idem : forall P, P /\ P <-> P.

Proof. fo. Qed.

Lemma and_idem_and_l : forall P Q, P /\ P /\ Q <-> P /\ Q.

Proof. fo. Qed.

Lemma and_idem_and_r : forall P Q, Q /\ P /\ P <-> Q /\ P.

Proof. fo. Qed.

Lemma iff_and : forall P Q P' Q',
  ((P <-> P') /\ (Q <-> Q')) -> ((P /\ Q) <-> (P' /\ Q')).

Proof. fo. Qed.

Lemma iff_forall : forall A (P Q : A->Prop),
  (forall x, P x <-> Q x) -> ((forall x, P x) <-> (forall x, Q x)).

Proof. fo. Qed.

(** Tactic removing identical propositions in a conjunction. *)

Ltac and_idem := repeat rewrite and_assoc;
  repeat (rewrite and_idem_and_l || rewrite and_idem_and_r || rewrite and_idem).

(***********************************************************************)
(** Basic theorems on (intuitionist) predicate calculus. *)

Section pred.

  Variables (A : Type) (P : A -> Prop).

  Lemma not_exists_imply_forall_not : ~(exists x, P x) -> forall x, ~P x.

  Proof. fo. Qed.

  Lemma forall_not_imply_not_exists : (forall x, ~P x) -> ~(exists x, P x).

  Proof. fo. Qed.

  Lemma not_exists_eq : ~(exists x, P x) <-> (forall x, ~P x).

  Proof. fo. Qed.

  Lemma exists_not_imply_not_forall : (exists x, ~P x) -> ~(forall x, P x).

  Proof. fo. Qed.

End pred.
