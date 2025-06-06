(** CoLoR, a Coq library on rewriting and termination.

See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2012-04-05

* Lambda-terms

Remark on the structure of the files in this directory: In Coq,
functor instantiation generates distinct Inductive's (or Class'es or
Record's), i.e. if [F(M)] provides an [Inductive t], [N1:=F(M)] and
[N2:=F(M)], then [N1.t <> N2.t]. To get around this problem, we have
to define [Inductive]'s outside any module. Moreover, in order to
define some module types, we also need some functions (e.g. free
variables, substitution, etc.) to be defined outside any module
too. Therefore, in this library, the files start by defining some
[Inductive]'s and some functions in a section with the necessary
abstract parameters. Then, a functor [Make] provides the properties of
these [Inductive]'s and functions when the abstract parameters are
correctly set. We use a functor and not a section because, in Coq,
modules cannot be defined inside a section and we rely on the [FSet]
and [FMap] modules defined in the standard Coq library. We also use
notations overriding the abstract names. These definitions are
therefore put in a module [Def] in order to be refered later
(e.g. tactic [unfold]). *)

Set Implicit Arguments.

From Stdlib Require Import FSets Structures.OrderedType.
From CoLoR Require Import LogicUtil BoolUtil VecUtil FSetUtil NatUtil RelUtil
     SN SetUtil.
From CoLoR Require Union.

(****************************************************************************)
(** * The set [Te] of lambda-terms
given a set [F] of constants and a set [X] of variables. *)

Module Export Def.

Section term.

  Variables F X : Type.

  Inductive Te : Type :=
  | Var (x : X)
  | Fun (f : F)
  | App (u v : Te)
  | Lam (x : X) (u : Te).

(****************************************************************************)
(** Predicate saying that a term is not of the form [Lam x a]. *)

  Definition not_lam u := forall x a, u <> Lam x a.

(****************************************************************************)
(** ** Equality on [Te] is decidable. *)

  Section dec.

    Variables
      (eq_fun_dec : forall f g : F, {f=g}+{~f=g})
      (eq_var_dec : forall x y : X, {x=y}+{~x=y}).

    Lemma eq_term_dec : forall u v : Te, {u=v}+{~u=v}.

    Proof. decide equality. Qed.

  End dec.

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

  Proof. intros P h u. eapply h with (n:=S(size u)). lia. Qed.

  Lemma ind_size0 : forall P : Te -> Prop,
    (forall u, (forall v, size v < size u -> P v) -> P u) -> forall u, P u.

  Proof.
    intros P h. apply intro_size. induction n; intro u; simpl; intro hs.
    exfalso. lia.
    destruct (eq_nat_dec (size u) n).
    subst. apply h. hyp.
    apply IHn. lia.
  Qed.

  Lemma ind_size1 : forall P : Te -> Prop,
    (forall x, P (Var x)) -> (forall f, P (Fun f)) ->
    (forall u v, P u -> P v -> P (App u v)) ->
    (forall x u, (forall u', size u' <= size u -> P u') -> P (Lam x u)) ->
    forall u, P u.

  Proof.
    intros P hv hf ha hl. apply ind_size0. intros [x|f|u v|x u] h.
    apply hv. apply hf. apply ha; apply h; simpl; max.
    apply hl. intros u' h'. apply h. simpl. lia.
  Qed.

(****************************************************************************)
(** ** Application of a term to a vector of terms. *)

  Notation Tes := (vector Te).

  Fixpoint apps {n} t (us : Tes n) :=
    match us with
      | Vnil => t
      | Vcons u us' => apps (App t u) us'
    end.

  Lemma apps_app_cons t u n (us : Tes n) :
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
    rewrite Vcast_refl. refl. discr. discr.
    rewrite Vcast_cons. apply IHts.
  Qed.

  Lemma size_apps_l : forall n (ts : Tes n) t, size t <= size (apps t ts).

  Proof.
    induction n; intros ts t. VOtac; simpl. refl. VSntac ts; simpl.
    rewrite <- IHn. simpl. max.
  Qed.

  Lemma size_apps_r_in : forall n (ts : Tes n) t ti,
    Vin ti ts -> size ti < size (apps t ts).

  Proof.
    induction n; intros ts t ti. VOtac; simpl. fo.
    VSntac ts; simpl. intros [h|h].
    rewrite h. eapply Nat.lt_le_trans. 2: apply size_apps_l. simpl. max.
    apply IHn. hyp.
  Qed.

  Lemma size_apps_r_nth : forall n (ts : Tes n) t i (hi : i<n),
    size (Vnth ts hi) < size (apps t ts).

  Proof. intros n ts t i hi. apply size_apps_r_in. apply Vnth_in. Qed.

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

  Proof. induction ts; intro t; simpl. lia. rewrite IHts. simpl. lia. Qed.

  Lemma eq_apps_head : forall p (ts : Tes p) q (us : Tes q) a b,
    apps a ts = apps b us -> nb_args a = nb_args b -> a = b.

  Proof.
    induction ts; destruct us; intros a b e1 e2; simpl in *.
    hyp.
    gen (f_equal nb_args e1).
      rewrite apps_app. simpl. rewrite nb_args_apps. lia.
    gen (f_equal nb_args e1).
      rewrite apps_app. simpl. rewrite nb_args_apps. lia.
    assert (i : nb_args (App a h) = nb_args (App b h0)). simpl. lia.
    gen (IHts _ us (App a h) (App b h0) e1 i); intro j. inversion j. refl.
  Qed.

  Arguments eq_apps_head [p ts q us a b] _ _.

  Lemma eq_apps_nb_args : forall p (ts : Tes p) q (us : Tes q) a b,
    apps a ts = apps b us -> nb_args a = nb_args b -> p = q.

  Proof.
    induction ts; destruct us; intros a b e1 e2; simpl in *.
    refl.
    gen (f_equal nb_args e1).
      rewrite apps_app. simpl. rewrite nb_args_apps. lia.
    gen (f_equal nb_args e1).
      rewrite apps_app. simpl. rewrite nb_args_apps. lia.
    assert (i : nb_args (App a h) = nb_args (App b h0)). simpl. lia.
    gen (IHts _ us (App a h) (App b h0) e1 i); intro j. lia.
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
    rewrite Vcast_refl. refl.
    gen (f_equal nb_args e1).
      rewrite apps_app. simpl. rewrite nb_args_apps. lia.
    gen (f_equal nb_args e1).
      rewrite apps_app. simpl. rewrite nb_args_apps. lia.
    assert (i : nb_args (App a h) = nb_args (App b h0)). simpl. lia.
    gen (eq_apps_head e1 i); intro j. inversion j; subst.
    match goal with |- _ = Vcast _ ?p => set (h:=p) end.
    rewrite Vcast_cons. apply Vtail_eq.
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
(** ** Sets of free and bound variables of a term. *)

  Section fv.

    Variable ens_X : Ens.

    Notation empty := (Ens_empty ens_X).
    Notation singleton := (Ens_singleton ens_X).
    Notation union := (Ens_union ens_X).
    Notation remove := (Ens_remove ens_X).
    Notation add := (Ens_add ens_X).

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
        | Vcons t ts' => union (fv t) (fvs ts')
      end.

    Fixpoint bv (t : Te) :=
      match t with
        | Var _ => empty
        | Fun _ => empty
        | App u v => union (bv u) (bv v)
        | Lam x u => add x (bv u)
      end.

  End fv.

(****************************************************************************)
(** ** Predicate saying if a relation on terms is monotone. *)

  Class Monotone R := {
    mon_app_l : Proper (R ==> Logic.eq ==> R) App;
    mon_app_r : Proper (Logic.eq ==> R ==> R) App;
    mon_lam : Proper (Logic.eq ==> R ==> R) Lam }.

  Global Instance eq_mon : Monotone eq.

  Proof. split; congruence. Qed.

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

(****************************************************************************)
(** ** Supterm relation. *)

  Inductive supterm : relation Te :=
  | st_app_l : forall u v, supterm (App u v) u
  | st_app_r : forall u v, supterm (App u v) v
  | st_lam : forall x u, supterm (Lam x u) u.

(****************************************************************************)
(** ** Predicate saying if a relation is invariant on variables. *)

  Class VarInvL R := { var_inv_l : forall x u, R (Var x) u -> u = Var x }.

  Class VarInvR R := { var_inv_r : forall x u, R u (Var x) -> u = Var x }.

  Global Instance VarInvR_sym R : Symmetric R -> VarInvL R -> VarInvR R.

  Proof. fo. Qed.

  Global Instance VarInvL_eq : VarInvL eq.

  Proof. split. auto. Qed.

End term.

Arguments Var [F X] _.
Arguments Fun [F X] _.
Arguments eq_apps_fun_head [F X f p ts g q us] _.
Arguments eq_apps_fun_nb_args [F X f p ts g q us] _.
Arguments eq_apps_fun_args [F X f p ts g q us] _.
Arguments eq_apps_nb_args_head [F X n ts us t u] _.
Arguments eq_apps_nb_args_args [F X n ts us t u] _.

(****************************************************************************)
(** ** Tactics. *)

(** Tactic for unfolding the projections of the type [Ens]. *)

Ltac ens := unfold Ens_type, Ens_empty, Ens_singleton, Ens_add, Ens_union, Ens_remove,
  Ens_diff, Ens_In, Ens_mem, Ens_fold in *.

(** Tactic for doing induction on the size of a term. *)

Ltac ind_size1 u :=
  intro u; pattern u; apply ind_size1;
    [clear u; let x := fresh "x" in intro x
    |clear u; let f := fresh "f" in intro f
    |clear u; let u := fresh "u" in let v := fresh "v" in
      let hu := fresh "hu" in let hv := fresh "hv" in
        intros u v hu hv
    |clear u; let x := fresh "x" in let hu := fresh "hu" in intros x u hu].

End Def.

(****************************************************************************)
(** * Structure for infinite sets of variables. *)

Module Type Var.

  (** We assume given a set [X] for variables and a module [XOrd]
  providing a structure of decidable ordered set to [X]. *)

  Parameter X : Type.

  Declare Module Export XOrd : OrderedType
  with Definition t := X
  with Definition eq := @Logic.eq X.

  (** Module providing finite sets of variables. *)

  Declare Module Export XSet : FSetInterface.S with Module E := XOrd.

  #[global] Declare Instance eq_rel : @RelationClasses.RewriteRelation t Equal.

  Notation ens_X :=
    (@mk_Ens X XSet.t empty singleton add union remove diff In mem fold).

  (** We assume that [X] is infinite. *)

  Parameter var_notin : XSet.t -> X.

  Parameter var_notin_ok : forall xs, ~In (var_notin xs) xs.

  Arguments var_notin_ok : clear implicits.

  Global Declare Instance var_notin_e : Proper (Equal ==> Logic.eq) var_notin.

End Var.

(** Example of [Var] structure using natural numbers. *)

From Stdlib Require OrderedTypeEx FSetAVL.

Module NatVar <: Var.

  Definition X := nat.

  Module XOrd := OrderedTypeEx.Nat_as_OT.

  Module Export XSet := FSetAVL.Make XOrd.

  #[global] Instance eq_rel : @RelationClasses.RewriteRelation t Equal := {}.

  Notation ens_X :=
    (@mk_Ens X XSet.t empty singleton add union remove diff In mem fold).

  Definition var_notin xs :=
    match max_elt xs with
      | Some k => S k
      | None => 0
    end.

  Lemma var_notin_ok xs : ~In (var_notin xs) xs.

  Proof.
    unfold var_notin. case_eq (max_elt xs).
    intros k e h. gen (max_elt_2 e h). lia.
    intro h. apply max_elt_3 in h. fo.
  Qed.

  Module Export XSetUtil := FSetUtil.Make XSet.

  Global Instance var_notin_e : Proper (Equal ==> Logic.eq) var_notin.

  Proof.
    intros xs xs' xsxs'. unfold var_notin.
    gen (XSetUtil.max_elt_e xsxs'). intro h. inversion h; subst; refl.
  Qed.

End NatVar.

(****************************************************************************)
(** * Structure on which we will define lambda-terms. *)

Module Type L_Struct.

  (** We assume given a set [F] for constants and a module [FOrd]
  providing a structure of decidable ordered set to [F]. *)

  Parameter F : Type.

  Declare Module Export FOrd : OrderedType
  with Definition t := F
  with Definition eq := @Logic.eq F.

  (** We assume given a [Var] structure. *)

  Declare Module Export V : Var.

  (** Notations. *)

  Notation Te := (Te F X).
  Notation Tes := (vector Te).

  Notation Var := (@Var F X).
  Notation Fun := (@Fun F X).
  Notation App := (@App F X).
  Notation Lam := (@Lam F X).

  Notation not_lam := (@not_lam F X).
  Notation size := (@size F X).
  Notation apps := (@apps F X).
  Notation head := (@head F X).
  Notation nb_args := (@nb_args F X).
  Notation args := (@args F X).
  Notation fv := (@fv F X ens_X).
  Notation bv := (@bv F X ens_X).
  Notation fvs := (@fvs F X ens_X).
  Notation Monotone := (@Monotone F X).
  Notation clos_mon := (@clos_mon F X).
  Notation eq_term_dec := (@eq_term_dec F X FOrd.eq_dec XOrd.eq_dec).
  Notation beq_term := (bool_of_rel eq_term_dec).
  Notation supterm := (@supterm F X).

End L_Struct.

(****************************************************************************)
(** * Properties of terms. *)

Module Make (Export L : L_Struct).

  (** Properties of finite set of variables. *)

  Module Export XSetUtil := FSetUtil.Make XSet.

  (** Tactic doing [destruct (eq_dec x y)] and unfolding
  [XOrd.eq]. Otherwise, Coq's tactic [subst] does not work. *)

  Ltac eq_dec x y :=
    unfold eqb; destruct (XOrd.eq_dec x y); unfold XOrd.eq in *.

  (** Equivalence between boolean and propositional equality on variables. *)

  Lemma eqb_true_iff x y : eqb x y = true <-> x = y.

  Proof. eq_dec x y; intuition auto with *. Qed.

  Lemma eqb_false_iff x y : eqb x y = false <-> x <> y.

  Proof. eq_dec x y. intuition auto with *. tauto. Qed.

(****************************************************************************)
(** ** Equality on terms. *)

  Lemma beq_term_true_iff u v : beq_term u v = true <-> u = v.

  Proof. unfold bool_of_rel. destruct (eq_term_dec u v); intuition auto with *. Qed.

  Lemma beq_term_false_iff u v : beq_term u v = false <-> u <> v.

  Proof. unfold bool_of_rel. destruct (eq_term_dec u v); intuition auto with *. Qed.

  Lemma beq_term_refl u : beq_term u u = true.

  Proof. unfold bool_of_rel. destruct (eq_term_dec u u). refl. cong. Qed.

  Lemma beq_term_var x y : beq_term (Var x) (Var y) = eqb x y.

  Proof.
    rewrite eqb_equiv, beq_term_true_iff, eqb_true_iff.
    intuition. inversion H. refl. subst. refl.
  Qed.

(****************************************************************************)
(** Properties of monotone relations. **)

  Section mon_apps.

    Variables (R : relation Te) (R_mon : Monotone R).

    Global Instance mon_apps_l n : Proper (R ==> Logic.eq ==> R) (@apps n).

    Proof.
      intros u u' uu' ts ts' tsts'. subst ts'.
      revert n ts u u' uu'; induction ts; intros u u' uu'; simpl. hyp.
      apply IHts. apply mon_app_l; auto.
    Qed.

    Lemma mon_apps_app_cons : forall u u', R u u' ->
      forall p (ts : Tes p) q (vs : Tes q) t,
        R (apps t (Vapp ts (Vcons u vs))) (apps t (Vapp ts (Vcons u' vs))).

    Proof.
      intros u u' uu'. induction ts; intros q vs t; simpl.
      apply mon_apps_l. apply mon_app_r; auto. refl.
      apply IHts.
    Qed.

    Lemma mon_apps_replace : forall u u', R u u' ->
      forall n (ts : Tes n) t i (h1 h2 : i<n),
        R (apps t (Vreplace ts h1 u)) (apps t (Vreplace ts h2 u')).

    Proof.
      intros u u' uu'. induction ts; intros t i h1 h2. lia.
      rename h into t0. simpl. destruct i; simpl.
      apply mon_apps_l. apply mon_app_r; auto. refl.
      apply IHts.
    Qed.

  End mon_apps.

  (** Tactic trying to simplify and possibly prove goals of the form
  [?R _ _] when [?R] is [Monotone]. *)

  Ltac mon := repeat
    match goal with
      | |- ?R (App ?x _) (App ?x _) => apply mon_app_r; [class|refl|idtac]
      | |- ?R (App _ ?x) (App _ ?x) => apply mon_app_l; [class|idtac|refl]
      | |- ?R (Lam ?x _) (Lam ?x _) => apply mon_lam; [class|refl|idtac]
      | |- ?R (apps _ ?ts) (apps _ ?ts) => apply mon_apps_l; [class|idtac|refl]
      | |- ?R (apps ?t (Vapp ?ts (Vcons _ ?vs)))
              (apps ?t (Vapp ?ts (Vcons _ ?vs))) =>
        apply mon_apps_app_cons; [class|idtac]
      | |- ?R (apps ?t (Vreplace ?ts _ _)) (apps ?t (Vreplace ?ts _ _)) =>
        apply mon_apps_replace; [class|idtac]
      | |- ?R ?x ?y => hyp
    end.

(****************************************************************************)
(** ** Properties of [Monotone]. *)

  (** Monotony is compatible with [same]. *)

  Global Instance Monotone_impl : Proper (same ==> impl) Monotone.

  Proof.
    intros R S [RS SR] h. split.
    intros u u' uu' v v' vv'. subst v'. apply RS. apply SR in uu'. mon.
    intros u u' uu' v v' vv'. subst u'. apply RS. apply SR in vv'. mon.
    intros x x' xx' u u' uu'. subst x'. apply RS. apply SR in uu'. mon.
  Qed.

  (** [clos_trans] preserves [Monotone]. *)

  Global Instance clos_trans_mon R : Monotone R -> Monotone (R!).

  Proof.
    intro R_mon. split.
    (* app_l *)
    intros u u' uu' v v' vv'. subst v'. revert u u' uu'. induction 1.
    apply t_step. mon. trans (App y v); hyp.
    (* app_r *)
    intros u u' uu' v v' vv'. subst u'. revert v v' vv'. induction 1.
    apply t_step. mon. trans (App u y); hyp.
    (* lam *)
    intros x x' xx' u u' uu'. subst x'. revert u u' uu'. induction 1.
    apply t_step. mon. trans (Lam x y); hyp.
  Qed.

  (** [clos_refl_trans] preserves [Monotone]. *)

  Global Instance clos_refl_trans_mon R : Monotone R -> Monotone (R#).

  Proof.
    intro R_mon. split.
    (* app_l *)
    intros u u' uu' v v' vv'. subst v'. revert u u' uu'. induction 1.
    apply rt_step. mon. refl. trans (App y v); hyp.
    (* app_r *)
    intros u u' uu' v v' vv'. subst u'. revert v v' vv'. induction 1.
    apply rt_step. mon. refl. trans (App u y); hyp.
    (* lam *)
    intros x x' xx' u u' uu'. subst x'. revert u u' uu'. induction 1.
    apply rt_step. mon. refl. trans (Lam x y); hyp.
  Qed.

  (** [clos_equiv] preserves [Monotone]. *)

  Global Instance clos_equiv_mon R : Monotone R -> Monotone (clos_equiv R).

  Proof.
    intro R_mon. split.
    (* app_l *)
    intros u u' uu' v v' vv'. subst v'. revert u u' uu'. induction 1.
    apply e_step. mon. refl. trans (App y v); hyp. hyp.
    (* app_r *)
    intros u u' uu' v v' vv'. subst u'. revert v v' vv'. induction 1.
    apply e_step. mon. refl. trans (App u y); hyp. hyp.
    (* lam *)
    intros x x' xx' u u' uu'. subst x'. revert u u' uu'. induction 1.
    apply e_step. mon. refl. trans (Lam x y); hyp. hyp.
  Qed.

(****************************************************************************)
(** ** Properties of [clos_mon]. *)

  Global Instance monotone_clos_mon R : Monotone (clos_mon R).

  Proof.
    split.
    intros u u' uu' v v' vv'. subst v'. apply m_app_l. hyp.
    intros u u' uu' v v' vv'. subst u'. apply m_app_r. hyp.
    intros x x' xx' u u' uu'. subst x'. apply m_lam. hyp.
  Qed.

  Lemma clos_mon_min R S : Monotone S -> R << S -> clos_mon R << S.

  Proof. intros S_mon RS. intros u v; revert u v; induction 1; mon. fo. Qed.

  (** The monotone closure is compatible with relation inclusion and
  equivalence. *)

  Global Instance clos_mon_incl : Proper (inclusion ==> inclusion) clos_mon.

  Proof. intros R S RS. induction 1; try mon. apply m_step. apply RS. hyp. Qed.

  Global Instance clos_mon_same : Proper (same ==> same) clos_mon.

  Proof. intros R S [RS SR]. split. rewrite RS. refl. rewrite SR. refl. Qed.

  (** The closure by monotony distributes over union. *)

  Lemma clos_mon_union R S : clos_mon (R U S) == clos_mon R U clos_mon S.

  Proof.
    split.
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

  (** Preservation of some properties by [clos_mon]. *)

  (*COQ: creates problem in the proof of LSubs.subs_id when declared
  as Instance. *)

  Lemma clos_mon_refl R : Reflexive R -> Reflexive (clos_mon R).

  Proof. intros R_refl u. apply m_step. refl. Qed.

  Lemma clos_mon_sym R : Symmetric R -> Symmetric (clos_mon R).

  Proof.
    intros R_sym u v; revert u v; induction 1.
    apply m_step. hyp.
    apply m_app_l. hyp. apply m_app_r. hyp. apply m_lam. hyp.
  Qed.

  Global Instance VarInvL_clos_mon (R : rel Te) : VarInvL R -> VarInvL (clos_mon R).

  Proof. intros [h]. split; intros x u xu. inversion xu; subst. fo. Qed.

  Global Instance VarInvR_clos_mon (R : rel Te) : VarInvR R -> VarInvR (clos_mon R).

  Proof. intros [h]. split; intros x u xu. inversion xu; subst. fo. Qed.

(****************************************************************************)
(** ** Properties wrt free variables. *)

  Lemma notin_fv_lam x y u : y=x \/ ~In x (fv u) <-> ~In x (fv (Lam y u)).
 
  Proof. simpl. set_iff. eq_dec y x; fo. Qed.

  Lemma In_fvs_Vnth : forall x n (ts : Tes n) i (h : i<n),
    In x (fv (Vnth ts h)) -> In x (fvs ts).

  Proof.
    intro x. induction ts; intros i hi.
    exfalso. lia.
    destruct i; simpl; set_iff. auto. intro a. right. eapply IHts. apply a.
  Qed.

  Arguments In_fvs_Vnth [x n ts i h] _.

  (** The monotone closure preserves free variables. *)

  Global Instance fv_clos_mon : forall R,
    Proper (R --> Subset) fv -> Proper (clos_mon R --> Subset) fv.

  Proof.
    intros R fv_R. induction 1; simpl; (rewrite IHclos_mon || rewrite H); refl.
  Qed.

  Global Instance fv_clos_mon_Equal : forall R,
    Proper (R ==> Equal) fv -> Proper (clos_mon R ==> Equal) fv.

  Proof.
    intros R fv_R. induction 1; simpl; (rewrite IHclos_mon || rewrite H); refl.
  Qed.

  Global Instance fv_union : forall R S,
    Proper (R --> Subset) fv -> Proper (S --> Subset) fv ->
    Proper (R U S --> Subset) fv.

  Proof. intros R S fv_R fv_S t u [tu|tu]; rewrite <- tu; refl. Qed.

(****************************************************************************)
(** ** Properties of [supterm]. *)

  Lemma supterm_nth f : forall n (ts : Tes n) i (hi : i<n),
    supterm! (apps (Fun f) ts) (Vnth ts hi).

  Proof.
    induction n; intros ts i hi. lia.
    rewrite (VSn_add ts). rewrite <- app_apps.
    set (us := Vremove_last ts). set (t0 := Vhead ts). set (tn := Vlast t0 ts).
    rewrite Vnth_add. destruct (eq_nat_dec i n).
    subst i. apply t_step. apply st_app_r.
    trans (apps (Fun f) us). apply t_step. apply st_app_l. apply IHn.
  Qed.

  Lemma supterm_wf : WF supterm.

  Proof.
    apply (WF_incl (Rof Peano.gt size)).
    induction 1; unfold Rof; simpl; try max; lia.
    apply WF_inverse. apply WF_gt.
  Qed.

  Section union.

    Variables (R : relation Te) (R_mon : Monotone R).

    Lemma supterm_R_mon_commut : supterm @ R << R @ supterm.

    Proof.
      intros t v [u [tu uv]]; revert t u tu v uv; induction 1.
      intros u' uu'. exists (App u' v). split. mon. apply st_app_l.
      intros v' vv'. exists (App u v'). split. mon. apply st_app_r.
      intros u' uu'. exists (Lam x u'). split. mon. apply st_lam.
    Qed.

    Lemma tc_supterm_R_mon_commut : supterm! @ R << R @ supterm!.

    Proof. apply commut_tc. apply supterm_R_mon_commut. Qed.

    Lemma SN_supterm_R_mon : forall u, SN R u -> SN (supterm! U R) u.

    Proof.
      intros u hu. apply Union.SN_union_commut.
      intros x _. apply WF_tc. apply supterm_wf. hyp.
      apply tc_supterm_R_mon_commut.
    Qed.

    Lemma SN_st u v : SN R u -> supterm u v -> SN R v.

    Proof.
      intros u_sn uv. eapply SN_incl. eapply incl_union_r. refl.
      eapply SN_inv. left. eapply t_step. apply uv.
      apply SN_supterm_R_mon. hyp.
    Qed.

    Lemma SN_st_app_l u v : SN R (App u v) -> SN R u.

    Proof. intro h. eapply SN_st. apply h. apply st_app_l. Qed.

    Lemma SN_st_app_r u v : SN R (App u v) -> SN R v.

    Proof. intro h. eapply SN_st. apply h. apply st_app_r. Qed.

    Lemma SN_st_lam x u : SN R (Lam x u) -> SN R u.

    Proof. intro h. eapply SN_st. apply h. apply st_lam. Qed.

    Lemma supterm_R_mon_wf : WF R -> WF (supterm! U R).

    Proof.
      intro R_wf. apply Union.WF_union_commut.
      apply WF_tc. apply supterm_wf. hyp.
      apply commut_tc. apply supterm_R_mon_commut.
    Qed.

    Section restrict.

      Variables (P : set Te) (P_R : Proper (R ==> impl) P).

      Lemma restrict_tc_supterm_R_mon_wf :
        WF (restrict P R) -> WF (restrict P (supterm! U R)).

      Proof.
        intro h. rewrite restrict_union. apply Union.WF_union_commut.
        apply wf_restrict_sn. intros t ht. apply WF_tc. apply supterm_wf. hyp.
        intros t v [u [[ht tu] [hu uv]]].
        assert (a : (supterm! @ R) t v). exists u. fo.
        destruct (tc_supterm_R_mon_commut a) as [u' [tu' u'v]]. exists u'.
        split; split; auto. eapply P_R. apply tu'. hyp.
      Qed.

    End restrict.

    Lemma restrict_SN_tc_supterm_R_mon_wf : WF (restrict (SN R) (supterm! U R)).

    Proof.
      apply restrict_tc_supterm_R_mon_wf.
      intros u u' uu' h. eapply SN_inv. apply uu'. hyp.
      apply wf_restrict_sn. refl.
    Qed.

  End union.

End Make.
