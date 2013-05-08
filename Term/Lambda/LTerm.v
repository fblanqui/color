(**
CoLoR, a Coq library on rewriting and termination.

See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2012-04-05


* Lambda-terms
*)

Set Implicit Arguments.

Require Import LogicUtil BoolUtil.

(****************************************************************************)
(** ** The set [Te] of lambda-terms
given a set [F] of constants and a set [X] of variables.

The type of terms is defined outside any functor because, in Coq,
functor instanciation generates distinct inductive types. *)

Section term.

  Variables F X : Type.

  Inductive Te : Type :=
  | Var (x : X)
  | Fun (f : F)
  | App (u v : Te)
  | Lam (x : X) (u : Te).

End term.

(****************************************************************************)
(** ** Structure on which we will define lambda-terms. *)

Require Import Structures.OrderedType FSets.

Module Type L_Struct.

  (** We assume given a set [F] for constants and a module [FOrd]
  providing a structure of decidable ordered set to [F]. *)

  Parameter F : Type.

  Declare Module Export FOrd : OrderedType
  with Definition t := F
  with Definition eq := @Logic.eq F.

  (** We assume given a set [X] for variables and a module [XOrd]
  providing a structure of decidable ordered set to [X]. *)

  Parameter X : Type.

  Declare Module Export XOrd : OrderedType
  with Definition t := X
  with Definition eq := @Logic.eq X.

  (** Module providing finite sets of variables. *)

  Declare Module Export XSet : FSetInterface.S with Module E := XOrd.

  (** We assume that [X] is infinite. *)

  Parameter var_notin : XSet.t -> X.

  Parameter var_notin_ok : forall xs, ~In (var_notin xs) xs.

  Arguments var_notin_ok : clear implicits.

  Declare Instance var_notin_e : Proper (Equal ==> Logic.eq) var_notin.

  Notation Te := (Te F X).
  Notation Var := (@Var F X).
  Notation Fun := (@Fun F X).
  Notation App := (@App F X).
  Notation Lam := (@Lam F X).

End L_Struct.

(****************************************************************************)
(** ** This development is defined as a functor [Lambda] providing the definition of lambda-terms, substitution, etc. and some of their properties.

We have to use a functor instead of a section because modules cannot
be defined inside sections (and we need [XSet] for instance). This has
bad consequences because, in Coq, functor instanciation generates
distinct Inductive's, i.e. if F(M) provides an Inductive t, N1:=F(M)
and N2:=F(M), then N1.t <> N2.t. *)

Module Make (Export L : L_Struct).

  (** Properties of finite set of variables. *)

  Require FSetUtil.
  Module Export XSetUtil := FSetUtil.Make XSet.

  (** Tactic for proving simple membership propositions. *)

  Ltac fset := intro; set_iff; intuition.

  (** Tactic doing [destruct (eq_dec x y)] and unfolding
  [XOrd.eq]. Otherwise, Coq's tactic [subst] does not work. *)

  Ltac eq_dec x y := destruct (XOrd.eq_dec x y); unfold XOrd.eq in *.

  (** Equivalence between boolean and propositional equality on variables. *)

  Lemma eqb_true_iff : forall x y, eqb x y = true <-> x = y.

  Proof. intros x y. unfold eqb. eq_dec x y; intuition. discr. Qed.

  Lemma eqb_false_iff : forall x y, eqb x y = false <-> x <> y.

  Proof.
    intros x y. unfold eqb. eq_dec x y. intuition. tauto.
  Qed.

(****************************************************************************)
(** ** Equality on [Te] is decidable. *)

  Lemma eq_term_dec : forall u v : Te, {u=v}+{~u=v}.

  Proof.
    decide equality. apply XOrd.eq_dec. apply FOrd.eq_dec. apply XOrd.eq_dec.
  Qed.

  (** Boolean equality on terms. *)

  Definition beq_term u v :=
    match eq_term_dec u v with
      | left _ => true
      | _ => false
    end.

  Lemma beq_term_true_iff : forall u v, beq_term u v = true <-> u = v.

  Proof.
    intros u v. unfold beq_term. destruct (eq_term_dec u v); intuition. discr.
  Qed.

  Lemma beq_term_false_iff : forall u v, beq_term u v = false <-> u <> v.

  Proof.
    intros u v. unfold beq_term. destruct (eq_term_dec u v); intuition.
  Qed.

  Lemma beq_term_refl : forall u, beq_term u u = true.

  Proof.
    intro u. unfold beq_term. destruct (eq_term_dec u u).
    refl. absurd (u=u); tauto.
  Qed.

  Lemma beq_term_var : forall x y, beq_term (Var x) (Var y) = eqb x y.

  Proof.
    intros x y. rewrite eqb_equiv, beq_term_true_iff, eqb_true_iff.
    intuition. inversion H. refl. subst. refl.
  Qed.

  (** Predicate saying that a term is not of the form [Lam x a]. *)

  Definition not_lam u := forall x a, u <> Lam x a.

(****************************************************************************)
(** ** Predicate saying if a relation on terms is monotone. *)

  Class Monotone R := {
    mon_app_l : Proper (R ==> Logic.eq ==> R) App;
    mon_app_r : Proper (Logic.eq ==> R ==> R) App;
    mon_lam : Proper (Logic.eq ==> R ==> R) Lam }.

  (** Tactic trying to simplify and possibly prove goals of the form
  [?R _ _] when [?R] is [Monotone]. *)

  Ltac mon_aux h := repeat
    match goal with
      | |- ?R (App ?x _) (App ?x _) => apply (@mon_app_r _ h); [refl|idtac]
      | |- ?R (App _ ?y) (App _ ?y) => apply (@mon_app_l _ h); [idtac|refl]
      | |- ?R (Lam ?x _) (Lam ?x _) => apply (@mon_lam _ h); [refl|idtac]
      | h : ?R ?x ?y |- ?R ?x ?y => exact h
    end.

  Ltac mon :=
    match goal with
      | h : Monotone ?R |- ?R _ _ => mon_aux h
      | |- ?R _ _ => let h := fresh "h" in
        assert (h : Monotone R); [auto with typeclass_instances|mon_aux h];
          clear h
    end.

  (** Monotony is compatible with [same_relation]. *)

  Instance Monotone_impl : Proper (@same_relation Te ==> impl) Monotone.

  Proof.
    intros R S [RS SR] h. split.
    intros u u' uu' v v' vv'. subst v'. apply RS. apply SR in uu'. mon.
    intros u u' uu' v v' vv'. subst u'. apply RS. apply SR in vv'. mon.
    intros x x' xx' u u' uu'. subst x'. apply RS. apply SR in uu'. mon.
  Qed.

  (** Closure by equivalence preserves monotony. *)

  Require Import RelUtil.

  Instance clos_equiv_mon R : Monotone R -> Monotone (clos_equiv R).

  Proof.
    intro h. split.
    (* app_l *)
    intros u u' uu' v v' vv'. subst v'. revert u u' uu'. induction 1.
    apply e_step. mon. refl. trans (App y v); hyp. sym. hyp.
    (* app_r *)
    intros u u' uu' v v' vv'. subst u'. revert v v' vv'. induction 1.
    apply e_step. mon. refl. trans (App u y); hyp. sym. hyp.
    (* lam *)
    intros x x' xx' u u' uu'. subst x'. revert u u' uu'. induction 1.
    apply e_step. mon. refl. trans (Lam x y); hyp. sym. hyp.
  Qed.

(****************************************************************************)
(** ** Monotone closure of a relation. *)

  Section clos_mon.

    Variable R : relation Te.

    Inductive clos_mon : relation Te :=
    | m_step : forall u v, R u v -> clos_mon u v
    | m_app_l : forall v u u', clos_mon u u' -> clos_mon (App u v) (App u' v)
    | m_app_r : forall u v v', clos_mon v v' -> clos_mon (App u v) (App u v')
    | m_lam : forall x u u', clos_mon u u' -> clos_mon (Lam x u) (Lam x u').

    Global Instance monotone_clos_mon : Monotone clos_mon.

    Proof.
      split.
      intros u u' uu' v v' vv'. subst v'. apply m_app_l. hyp.
      intros u u' uu' v v' vv'. subst u'. apply m_app_r. hyp.
      intros x x' xx' u u' uu'. subst x'. apply m_lam. hyp.
    Qed.

  End clos_mon.

  (** The monotone closure is compatible with relation inclusion and
  equivalence. *)

  Instance clos_mon_incl : Proper (@inclusion Te ==> @inclusion Te) clos_mon.

  Proof. intros R S RS. induction 1; try mon. apply m_step. apply RS. hyp. Qed.

  Instance clos_mon_same_rel :
    Proper (@same_relation Te ==> @same_relation Te) clos_mon.

  Proof. intros R S [RS SR]. split. rewrite RS. refl. rewrite SR. refl. Qed.

  (** The closure by monotony distributes over union. *)

  Lemma clos_mon_union : forall R S,
    clos_mon (R U S) == clos_mon R U clos_mon S.

  Proof.
    intros R S. split.
    (* << *)
    induction 1.
    destruct H as [H|H]. left. apply m_step. hyp. right. apply m_step. hyp.
    destruct IHclos_mon as [h|h].
    left. apply m_app_l. hyp. right. apply m_app_l. hyp.
    destruct IHclos_mon as [h|h].
    left. apply m_app_r. hyp. right. apply m_app_r. hyp.
    destruct IHclos_mon as [h|h].
    left. apply m_lam. hyp. right. apply m_lam. hyp.
    (* >> *)
    intros t u [h|h]. eapply clos_mon_incl. apply incl_union_l. refl. hyp.
    eapply clos_mon_incl. apply incl_union_r. refl. hyp.
  Qed.
  
(****************************************************************************)
(** ** Size of a term *)

  Require Import Min Max Wf_nat Omega.

  Fixpoint size (t : Te) :=
    match t with
      | LTerm.Var _ => 0
      | LTerm.Fun _ => 0
      | LTerm.App u v => 1 + max (size u) (size v)
      | LTerm.Lam _ u => 1 + size u
    end.

  (** Tactic for proving arithmetic goals with [max]. *)

  Ltac max := unfold ltof; simpl;
    match goal with
      | |- context [max ?x ?y] => gen (le_max_l x y); gen (le_max_r x y)
    end; intros; omega.

  (** Induction principles on term size. *)

  Lemma intro_size : forall P : Te -> Prop,
    (forall n u, size u < n -> P u) -> forall u, P u.

  Proof. intros P h u. eapply h with (n:=S(size u)). omega. Qed.

  Lemma ind_size0 : forall P : Te -> Prop,
    (forall u, (forall v, size v < size u -> P v) -> P u) -> forall u, P u.

  Proof.
    intros P h. apply intro_size. induction n; intro u; simpl; intro hs.
    exfalso. omega.
    destruct (eq_nat_dec (size u) n).
    subst. apply h. hyp.
    apply IHn. omega.
  Qed.

  Lemma ind_size1 : forall P : Te -> Prop,
    (forall x, P (Var x)) -> (forall f, P (Fun f)) ->
    (forall u v, P u -> P v -> P (App u v)) ->
    (forall x u, (forall u', size u' <= size u -> P u') -> P (Lam x u)) ->
    forall u, P u.

  Proof.
    intros P hv hf ha hl. apply ind_size0. intros [x|f|u v|x u] h.
    apply hv. apply hf. apply ha; apply h; max.
    apply hl. intros u' h'. apply h. simpl. omega.
  Qed.

  Ltac ind_size1 u :=
    intro u; pattern u; apply ind_size1;
      [clear u; let x := fresh "x" in intro x
      |clear u; let f := fresh "f" in intro f
      |clear u; let u := fresh "u" in let v := fresh "v" in
                let hu := fresh "hu" in let hv := fresh "hv" in
                intros u v hu hv
      |clear u; let x := fresh "x" in let hu := fresh "hu" in intros x u hu].

(****************************************************************************)
(** ** Set of free variables of a term *)

  Fixpoint fv (t : Te) :=
    match t with
      | LTerm.Var x => singleton x
      | LTerm.Fun _ => empty
      | LTerm.App u v => XSet.union (fv u) (fv v)
      | LTerm.Lam x u => remove x (fv u)
    end.

  Lemma notin_fv_lam : forall x y u,
    y=x \/ ~In x (fv u) <-> ~In x (fv (Lam y u)).
 
  Proof. intros x y u. simpl. set_iff. eq_dec y x; fo. Qed.

  (** The monotone closure preserves free variables. *)

  Instance fv_clos_mon : forall R,
    Proper (R --> Subset) fv -> Proper (clos_mon R --> Subset) fv.

  Proof.
    intros R fv_R. induction 1; simpl; (rewrite IHclos_mon || rewrite H); refl.
  Qed.

(****************************************************************************)
(** ** Application of a term to a vector of terms. *)

  Require Import VecUtil.

  Notation Tes := (vector Te).

  Fixpoint apps n t (us : Tes n) :=
    match us with
      | Vnil => t
      | Vcons u _ us' => apps (App t u) us'
    end.

  Lemma app_apps : forall n (us : Tes n) u v,
    App (apps u us) v = apps u (Vadd us v).

  Proof.
    induction us; intros u v. refl. simpl Vadd. simpl apps. apply IHus.
  Qed.

End Make.

(*COQ: We set the following Emacs file variables so that the file can
be run in ProofGeneral. Otherwise, the identifiers LTerm.* are not
recognized by coqtop. *)

(* Local Variables: *)
(* coq-prog-args: ("-emacs" "-top" "LTerm") *)
(* End: *)
