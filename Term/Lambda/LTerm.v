(**
CoLoR, a Coq library on rewriting and termination.

See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2012-04-05


* Lambda-terms

Remark on the structure of the files in this directory: In Coq,
functor instanciation generates distinct Inductive's (or Class'es or
Record's), i.e. if F(M) provides an Inductive t, N1:=F(M) and
N2:=F(M), then N1.t <> N2.t. To avoid name conflicts, we therefore
need to define Inductive's outside any module. Moreover, in order to
define some Module Type's, we also need some functions (e.g. free
variables, substitution, etc) to be defined outside any module
too. Therefore, in this library, the files start by defining some
Inductive's and some functions in a Section with the necessary
abstract parameters. Then, a functor Make provides the properties of
these Inductive's and functions when these abstract parameters are
correctly set. We use a functor and not a Section because, in Coq,
modules cannot be defined inside a Section and we rely on the FSet and
FMap modules defined in the standard Coq library. *)

Set Implicit Arguments.

Require Import LogicUtil BoolUtil VecUtil Min Max Wf_nat Omega FSets FSetUtil
  Structures.OrderedType RelUtil.

(*FIXME: move to ZUtil? *)
(** Tactic for proving arithmetic goals with [max]. *)

Ltac max := unfold ltof; simpl;
  match goal with
    | |- context [max ?x ?y] => gen (le_max_l x y); gen (le_max_r x y)
  end; intros; omega.

(****************************************************************************)
(** * The set [Te] of lambda-terms
given a set [F] of constants and a set [X] of variables. *)

Section term.

  Variables F X : Type.

  Inductive Te : Type :=
  | Var (x : X)
  | Fun (f : F)
  | App (u v : Te)
  | Lam (x : X) (u : Te).

(****************************************************************************)
(** ** Equality on [Te] is decidable. *)

  Variable eq_fun_dec : forall f g : F, {f=g}+{~f=g}.
  Variable eq_var_dec : forall x y : X, {x=y}+{~x=y}.

  Lemma eq_term_dec : forall u v : Te, {u=v}+{~u=v}.

  Proof. decide equality. Qed.

(****************************************************************************)
(** ** Size of a term *)

  Fixpoint size (t : Te) :=
    match t with
      | Var _ => 0
      | Fun _ => 0
      | App u v => 1 + max (size u) (size v)
      | Lam _ u => 1 + size u
    end.

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

(****************************************************************************)
(** ** Application of a term to a vector of terms. *)

  Notation Tes := (vector Te).

  Fixpoint apps {n} t (us : Tes n) :=
    match us with
      | Vnil => t
      | Vcons u _ us' => apps (App t u) us'
    end.

  Lemma apps_app_cons : forall t u n (us : Tes n),
    apps (App t u) us = apps t (Vcons u us).

  Proof. refl. Qed.

  Lemma app_apps : forall n (us : Tes n) u v,
    App (apps u us) v = apps u (Vadd us v).

  Proof.
    induction us; intros u v. refl. simpl Vadd. simpl apps. apply IHus.
  Qed.

  Lemma apps_app : forall n (us : Tes n) t u, apps (App t u) us
    = App (apps t (Vremove_last (Vcons u us))) (Vlast u us).

  Proof.
    induction us; intros t u; simpl. refl. rewrite IHus.
    apply (f_equal (fun v => App (apps (App t u) v) (Vlast h us))).
    unfold Vremove_last. rewrite Vsub_cons. apply Vsub_pi.
  Qed.

  Lemma apps_apps : forall p (ts : Tes p) t q (us : Tes q),
    apps (apps t ts) us = apps t (Vapp ts us).

  Proof. induction ts; fo. Qed.

  Lemma apps_cast : forall n (ts : Tes n) p (h : n=p) t,
    apps t (Vcast ts h) = apps t ts.

  Proof.
    induction ts; destruct p; simpl; intros e t.
    refl. discr. discr. apply IHts.
  Qed.

(****************************************************************************)
(** ** Head and arguments of a term. *)

  Fixpoint head (t : Te) :=
    match t with
      | App u _ => head u
      | _ => t
    end.

  Lemma head_head : forall u, head (head u) = head u.

  Proof. induction u; simpl; auto. Qed.

  Fixpoint nb_args (t : Te) :=
    match t with
      | App u _ => S (nb_args u)
      | _ => 0
    end.

  Fixpoint args (t : Te) :=
    match t as t return Tes (nb_args t) with
      | App u v => Vadd (args u) v
      | _ => Vnil
    end.

  Lemma head_apps : forall n (us : Tes n) t, head (apps t us) = head t.

  Proof.
    induction n; intros us t.
    VOtac. refl.
    VSntac us. simpl. rewrite apps_app. simpl. apply IHn.
  Qed.

  Lemma apps_head_args : forall u, u = apps (head u) (args u).

  Proof.
    induction u; simpl; auto.
    rewrite IHu1, app_apps, head_apps, head_head, <- IHu1. refl.
  Qed.

  Lemma nb_args_apps : forall n (ts : Tes n) t,
    nb_args (apps t ts) = nb_args t + n.

  Proof. induction ts; intro t; simpl. omega. rewrite IHts. simpl. omega. Qed.

  Lemma eq_apps_head : forall p (ts : Tes p) q (us : Tes q) a b,
    apps a ts = apps b us -> nb_args a = nb_args b -> a = b.

  Proof.
    induction ts; destruct us; intros a b e1 e2; simpl in *.
    hyp.
    gen (f_equal nb_args e1).
      rewrite apps_app. simpl. rewrite nb_args_apps. omega.
    gen (f_equal nb_args e1).
      rewrite apps_app. simpl. rewrite nb_args_apps. omega.
    assert (i : nb_args (App a h) = nb_args (App b h0)). simpl. omega.
    gen (IHts _ us (App a h) (App b h0) e1 i); intro j. inversion j. refl.
  Qed.

  Arguments eq_apps_head [p ts q us a b] _ _.

  Lemma eq_apps_nb_args : forall p (ts : Tes p) q (us : Tes q) a b,
    apps a ts = apps b us -> nb_args a = nb_args b -> p = q.

  Proof.
    induction ts; destruct us; intros a b e1 e2; simpl in *.
    refl.
    gen (f_equal nb_args e1).
      rewrite apps_app. simpl. rewrite nb_args_apps. omega.
    gen (f_equal nb_args e1).
      rewrite apps_app. simpl. rewrite nb_args_apps. omega.
    assert (i : nb_args (App a h) = nb_args (App b h0)). simpl. omega.
    gen (IHts _ us (App a h) (App b h0) e1 i); intro j. omega.
  Qed.

  Arguments eq_apps_nb_args [p ts q us a b] _ _.

  Lemma eq_apps_nb_args_sym : forall p (ts : Tes p) q (us : Tes q) a b,
    apps a ts = apps b us -> nb_args a = nb_args b -> q = p.

  Proof. intros p ts q us a b e. sym. eapply eq_apps_nb_args. apply e. hyp. Qed.

  Arguments eq_apps_nb_args_sym [p ts q us a b] _ _.

  Lemma eq_apps_args : forall p (ts : Tes p) q (us : Tes q) a b
    (h1 : apps a ts = apps b us) (h2 : nb_args a = nb_args b),
    ts = Vcast us (eq_apps_nb_args_sym h1 h2).

  Proof.
    induction ts; destruct us; intros a b e1 e2; simpl in *.
    refl.
    gen (f_equal nb_args e1).
      rewrite apps_app. simpl. rewrite nb_args_apps. omega.
    gen (f_equal nb_args e1).
      rewrite apps_app. simpl. rewrite nb_args_apps. omega.
    assert (i : nb_args (App a h) = nb_args (App b h0)). simpl. omega.
    gen (eq_apps_head e1 i); intro j. inversion j; subst. apply Vtail_eq.
    gen (IHts _ us (App b h0) (App b h0) e1 i); intro k. rewrite k at 1.
    apply Vcast_pi.
  Qed.

  Arguments eq_apps_args [p ts q us a b] _ _.

  Lemma eq_apps_fun_head : forall f p (ts : Tes p) g q (us : Tes q),
    apps (Fun f) ts = apps (Fun g) us -> f = g.

  Proof.
    intros f p ts g q us e. gen (f_equal head e).
    rewrite !head_apps. simpl. intro a. inversion a. refl.
  Qed.

  Arguments eq_apps_fun_head [f p ts g q us] _.

  Lemma eq_apps_fun_nb_args : forall f p (ts : Tes p) g q (us : Tes q),
    apps (Fun f) ts = apps (Fun g) us -> p = q.

  Proof.
    intros f p ts g q us e. gen (f_equal nb_args e).
    rewrite !nb_args_apps. simpl. auto.
  Qed.

  Arguments eq_apps_fun_nb_args [f p ts g q us] _.

  Lemma eq_apps_fun_nb_args_sym : forall f p (ts : Tes p) g q (us : Tes q),
    apps (Fun f) ts = apps (Fun g) us -> q = p.

  Proof. intros f p ts g q us e. sym. eapply eq_apps_fun_nb_args. apply e. Qed.

  Arguments eq_apps_fun_nb_args_sym [f p ts g q us] _.

  Lemma eq_apps_fun_args : forall f p (ts : Tes p) g q (us : Tes q)
    (h : apps (Fun f) ts = apps (Fun g) us),
    ts = Vcast us (eq_apps_fun_nb_args_sym h).

  Proof.
    intros f p ts g q us h.
    assert (i : nb_args (Fun f) = nb_args (Fun g)). refl.
    gen (eq_apps_args h i); intro j. rewrite j at 1. apply Vcast_pi.
  Qed.

  Lemma eq_apps_nb_args_head : forall n (ts us : Tes n) t u,
    apps t ts = apps u us -> t = u.

  Proof.
    induction ts; simpl; intros us t u.
    VOtac. fo.
    VSntac us. simpl. intro e. gen (IHts _ _ _ e). intro i. inversion i. refl.
  Qed.

  Arguments eq_apps_nb_args_head [n ts us t u] _.

  Lemma eq_apps_nb_args_args : forall n (ts us : Tes n) t u,
    apps t ts = apps u us -> ts = us.

  Proof.
    induction ts; simpl; intros us t u.
    VOtac. refl.
    VSntac us. simpl. intro e.
    gen (eq_apps_nb_args_head e); intro i. inversion i. subst t h; clear i.
    apply Vtail_eq. eapply IHts. apply e.
  Qed.

  Arguments eq_apps_nb_args_args [n ts us t u] _.

(****************************************************************************)
(** ** Structure for sets of variables. *)

  Record Ens := mk_Ens {
    Ens_type : Type;
    Ens_empty : Ens_type;
    Ens_singleton : X -> Ens_type;
    Ens_add : X -> Ens_type -> Ens_type;
    Ens_union : Ens_type -> Ens_type -> Ens_type;
    Ens_remove : X -> Ens_type -> Ens_type;
    Ens_diff : Ens_type -> Ens_type -> Ens_type;
    Ens_In : X -> Ens_type -> Prop;
    Ens_mem : X -> Ens_type -> bool;
    Ens_fold : forall A, (X -> A -> A) -> Ens_type -> A -> A }.

(****************************************************************************)
(** ** Set of free variables of a term. *)

  Section fv.

    Variable ens_X : Ens.

    Notation empty := (Ens_empty ens_X).
    Notation singleton := (Ens_singleton ens_X).
    Notation union := (Ens_union ens_X).
    Notation remove := (Ens_remove ens_X).

    Fixpoint fv (t : Te) :=
      match t with
        | Var x => singleton x
        | Fun _ => empty
        | App u v => union (fv u) (fv v)
        | Lam x u => remove x (fv u)
      end.

    Fixpoint fvs {n} (ts : Tes n) :=
      match ts with
        | Vnil => empty
        | Vcons t _ ts' => union (fv t) (fvs ts')
      end.

  End fv.

(****************************************************************************)
(** ** Predicate saying if a relation on terms is monotone. *)

  Class Monotone R := {
    mon_app_l : Proper (R ==> Logic.eq ==> R) App;
    mon_app_r : Proper (Logic.eq ==> R ==> R) App;
    mon_lam : Proper (Logic.eq ==> R ==> R) Lam }.

(****************************************************************************)
(** ** Monotone closure of a relation. *)

  Section clos_mon.

    Variable R : relation Te.

    Inductive clos_mon : relation Te :=
    | m_step : forall u v, R u v -> clos_mon u v
    | m_app_l : forall v u u', clos_mon u u' -> clos_mon (App u v) (App u' v)
    | m_app_r : forall u v v', clos_mon v v' -> clos_mon (App u v) (App u v')
    | m_lam : forall x u u', clos_mon u u' -> clos_mon (Lam x u) (Lam x u').

  End clos_mon.

End term.

Arguments eq_apps_fun_head [F X f p ts g q us] _.
Arguments eq_apps_fun_nb_args [F X f p ts g q us] _.
Arguments eq_apps_fun_args [F X f p ts g q us] _.
Arguments eq_apps_nb_args_head [F X n ts us t u] _.
Arguments eq_apps_nb_args_args [F X n ts us t u] _.

(****************************************************************************)
(** ** Tactics. *)

(** Tactic for unfolding the projections of the type [Ens]. *)

Ltac ens := unfold Ens_type, Ens_empty, Ens_singleton, Ens_add, Ens_union, Ens_remove, Ens_diff, Ens_In, Ens_mem, Ens_fold.

(** Tactic for doing induction on the size of a term. *)

Ltac ind_size1 u :=
  intro u; pattern u; apply ind_size1;
    [clear u; let x := fresh "x" in intro x
    |clear u; let f := fresh "f" in intro f
    |clear u; let u := fresh "u" in let v := fresh "v" in
      let hu := fresh "hu" in let hv := fresh "hv" in
        intros u v hu hv
    |clear u; let x := fresh "x" in let hu := fresh "hu" in intros x u hu].

(****************************************************************************)
(** * Structure on which we will define lambda-terms. *)

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

  Notation ens_X := (mk_Ens empty singleton add union remove diff In mem fold).

  (** We assume that [X] is infinite. *)

  Parameter var_notin : XSet.t -> X.

  Parameter var_notin_ok : forall xs, ~In (var_notin xs) xs.

  Arguments var_notin_ok : clear implicits.

  Declare Instance var_notin_e : Proper (Equal ==> Logic.eq) var_notin.

  Notation Te := (Te F X).
  Notation Tes := (vector Te).

  Notation Var := (@Var F X).
  Notation Fun := (@Fun F X).
  Notation App := (@App F X).
  Notation Lam := (@Lam F X).

  Notation size := (@size F X).
  Notation apps := (@apps F X).
  Notation head := (@head F X).
  Notation nb_args := (@nb_args F X).
  Notation args := (@args F X).
  Notation fv := (@fv F X ens_X).
  Notation fvs := (@fvs F X ens_X).
  Notation Monotone := (@Monotone F X).
  Notation clos_mon := (@clos_mon F X).
  Notation eq_term_dec := (@eq_term_dec F X FOrd.eq_dec XOrd.eq_dec).
  Notation beq_term := (brel eq_term_dec).

End L_Struct.

(****************************************************************************)
(** * Properties of terms. *)

Module Make (Export L : L_Struct).

  (** Properties of finite set of variables. *)

  Module Export XSetUtil := FSetUtil.Make XSet.

  (** Tactic for proving simple membership propositions. *)

  Ltac fset := intro; set_iff; intuition.

  (** Tactic doing [destruct (eq_dec x y)] and unfolding
  [XOrd.eq]. Otherwise, Coq's tactic [subst] does not work. *)

  Ltac eq_dec x y := destruct (XOrd.eq_dec x y); unfold XOrd.eq in *.

  (** Equivalence between boolean and propositional equality on variables. *)

  Lemma eqb_true_iff : forall x y, eqb x y = true <-> x = y.

  Proof. intros x y. unfold eqb. eq_dec x y; intuition. Qed.

  Lemma eqb_false_iff : forall x y, eqb x y = false <-> x <> y.

  Proof. intros x y. unfold eqb. eq_dec x y. intuition. tauto. Qed.

(****************************************************************************)
(** ** Equality on terms. *)

  Lemma beq_term_true_iff : forall u v, beq_term u v = true <-> u = v.

  Proof. intros u v. unfold brel. destruct (eq_term_dec u v); intuition. Qed.

  Lemma beq_term_false_iff : forall u v, beq_term u v = false <-> u <> v.

  Proof. intros u v. unfold brel. destruct (eq_term_dec u v); intuition. Qed.

  Lemma beq_term_refl : forall u, beq_term u u = true.

  Proof.
    intro u. unfold brel. destruct (eq_term_dec u u).
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
(** ** Properties of [Monotone]. *)

  (** Tactic trying to simplify and possibly prove goals of the form
  [?R _ _] when [?R] is [Monotone]. *)

  Ltac mon := repeat
    match goal with
      | |- ?R (App ?x _) (App ?x _) => apply mon_app_r; [class|refl|idtac]
      | |- ?R (App _ ?y) (App _ ?y) => apply mon_app_l; [class|idtac|refl]
      | |- ?R (Lam ?x _) (Lam ?x _) => apply mon_lam; [class|refl|idtac]
      | |- ?R ?x ?y => hyp
    end.

  (** Monotony is compatible with [same_relation]. *)

  Instance Monotone_impl : Proper (same_relation ==> impl) Monotone.

  Proof.
    intros R S [RS SR] h. split.
    intros u u' uu' v v' vv'. subst v'. apply RS. apply SR in uu'. mon.
    intros u u' uu' v v' vv'. subst u'. apply RS. apply SR in vv'. mon.
    intros x x' xx' u u' uu'. subst x'. apply RS. apply SR in uu'. mon.
  Qed.

  (** Closure by equivalence preserves monotony. *)

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
(** ** Properties of [clos_mon]. *)

  Instance monotone_clos_mon R : Monotone (clos_mon R).

  Proof.
    split.
    intros u u' uu' v v' vv'. subst v'. apply m_app_l. hyp.
    intros u u' uu' v v' vv'. subst u'. apply m_app_r. hyp.
    intros x x' xx' u u' uu'. subst x'. apply m_lam. hyp.
  Qed.

  (** The monotone closure is compatible with relation inclusion and
  equivalence. *)

  Instance clos_mon_incl : Proper (inclusion ==> inclusion) clos_mon.

  Proof. intros R S RS. induction 1; try mon. apply m_step. apply RS. hyp. Qed.

  Instance clos_mon_same_rel :
    Proper (same_relation ==> same_relation) clos_mon.

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
(** ** Properties wrt free variables. *)

  Lemma notin_fv_lam : forall x y u,
    y=x \/ ~In x (fv u) <-> ~In x (fv (Lam y u)).
 
  Proof. intros x y u. simpl. set_iff. eq_dec y x; fo. Qed.

  Lemma In_fvs_Vnth : forall x n (ts : Tes n) i (h : i<n),
    In x (fv (Vnth ts h)) -> In x (fvs ts).

  Proof.
    intro x. induction ts; intros i hi.
    exfalso. omega.
    destruct i; simpl; set_iff. auto. intro a. right. eapply IHts. apply a.
  Qed.

  Arguments In_fvs_Vnth [x n ts i h] _.

  (** The monotone closure preserves free variables. *)

  Instance fv_clos_mon : forall R,
    Proper (R --> Subset) fv -> Proper (clos_mon R --> Subset) fv.

  Proof.
    intros R fv_R. induction 1; simpl; (rewrite IHclos_mon || rewrite H); refl.
  Qed.

  Instance fv_union : forall R S,
    Proper (R --> Subset) fv -> Proper (S --> Subset) fv ->
    Proper (R U S --> Subset) fv.

  Proof. intros R S fv_R fv_S t u [tu|tu]; rewrite <- tu; refl. Qed.

End Make.
