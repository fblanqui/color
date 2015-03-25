(**
CoLoR, a Coq library on rewriting and termination.

See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2012-04-05

* Simply-typed lambda-terms
*)

Set Implicit Arguments.

Require Import VecUtil LogicUtil Relations OrdUtil.
Require Export LBeta.

(****************************************************************************)
(** * Simple types over a set [So] of type constants or sorts. *)

Section simple.

  Variable So : Type.

  Inductive Ty : Type :=
  | Base : So -> Ty
  | Arr : Ty -> Ty -> Ty.

  Infix "~~>" := Arr (at level 55, right associativity).

  Notation Tys := (vector Ty).

(** Basic functions on simple types. *)

  Fixpoint arity (T : Ty) :=
    match T with
      | Base _ => 0
      | Arr _ T' => S (arity T')
    end.

  Fixpoint inputs (T : Ty) :=
    match T as T return Tys (arity T) with
      | Base _ => Vnil
      | Arr T1 T2 => Vcons T1 (inputs T2)
    end.

  Fixpoint output (T : Ty) k {struct k} :=
    match k, T with
      | S k', Arr U V => output V k'
      | _, _ => T
    end.

  Fixpoint output_base (T : Ty) :=
    match T with
      | Base b => b
      | Arr _ T' => output_base T'
    end.

  Lemma output_arity : forall T, output T (arity T) = Base (output_base T).

  Proof. induction T; fo. Qed.

  Lemma arity_output : forall p T, arity (output T p) = arity T - p.

  Proof. induction p; destruct T; simpl; try refl. rewrite IHp. refl. Qed.

  Lemma output_output : forall p q T, output (output T p) q = output T (p+q).

  Proof.
    induction p; destruct T; simpl; try refl.
    destruct q; refl. rewrite IHp. refl.
  Qed.

  Lemma inputs_output_aux : forall p T,
    p <= arity T -> p + arity (output T p) <= arity T.

  Proof. intros p T. rewrite arity_output. omega. Qed.

  Arguments inputs_output_aux [p T] _.

  Lemma inputs_output : forall p T (h : p <= arity T),
    inputs (output T p) = Vsub (inputs T) (inputs_output_aux h).

  Proof.
    induction p; destruct T; simpl; intro h. refl.
    apply Vtail_eq. rewrite Vsub_cons, Vsub_id. refl.
    omega.
    assert (h' : p <= arity T2). omega.
    rewrite IHp with (h:=h'), Vsub_cons. apply Vsub_pi.
  Qed.

(** Building the type [T1 ~~> .. ~~> Tn -> U] from the type vector
[Ts] and the type [U]. *)

  Fixpoint arrow n (Ts : Tys n) U :=
    match Ts with
      | Vnil => U
      | Vcons T _ Ts' => T ~~> arrow Ts' U
    end.

  Lemma arrow_cast : forall n (Ts : Tys n) U n' (h:n=n'),
    arrow (Vcast Ts h) U = arrow Ts U.

  Proof. induction Ts; intros U n' e; subst; rewrite Vcast_refl; refl. Qed.

  Lemma arrow_output : forall T p q (h : p+q<=arity T),
    arrow (Vsub (inputs T) h) (output T (p+q)) = output T p.

  Proof.
    induction T; simpl; intros p q h.
    assert (p=0). omega. assert (q=0). omega. subst. refl.
    destruct p; simpl.
    destruct q; simpl. refl. rewrite Vsub_cons, IHT2. refl.
    rewrite Vsub_cons, IHT2. refl.
  Qed.

(** Decidability of equality on types. *)

  Section dec.

    Variable eq_so_dec : forall a b : So, {a=b}+{~a=b}.

    Lemma eq_typ_dec : forall A B : Ty, {A=B}+{~A=B}.

    Proof. decide equality. Qed.

  End dec.

(** [occurs a T] says if [T] contains some [a]. *)

  Section occurs.

    Fixpoint occurs a T :=
      match T with
        | Base b => a = b
        | Arr A B => occurs a A \/ occurs a B
      end.
 
    Variable eq_dec : forall x y : So, {x = y}+{~x = y}.

    Lemma occurs_dec : forall a T, {occurs a T}+{~occurs a T}.

    Proof.
      intro a. induction T; simpl. apply eq_dec.
      destruct IHT1. fo. destruct IHT2. fo. right. fo.
    Qed.

  End occurs.

(** Predicate saying that a type constant occurs only
positively/negatively in a simple type. *)

  Section pos.

    Variable a : So.

    Fixpoint pos T :=
      match T with
        | Base _ => True
        | Arr A B => neg A /\ pos B
      end

    with neg T :=
      match T with
        | Base b => b <> a
        | Arr A B => pos A /\ neg B
      end.

    (*COQ: [pos] and [neg] not [simpl]ified outside the section. See bug
    report https://coq.inria.fr/bugs/show_bug.cgi?id=3097 *)

    Lemma pos_base : forall b, pos (Base b) <-> True.

    Proof. refl. Qed.

    Lemma pos_arrow : forall A B, pos (A ~~> B) <-> neg A /\ pos B.

    Proof. refl. Qed.

    Lemma neg_base : forall b, neg (Base b) <-> b <> a.

    Proof. refl. Qed.

    Lemma neg_arrow : forall A B, neg (A ~~> B) <-> pos A /\ neg B.

    Proof. refl. Qed.

(** Some properties of [occurs], [pos] and [neg]. *)

    Lemma not_occurs_pos_neg : forall {T}, ~occurs a T -> pos T /\ neg T.

    Proof. induction T; simpl; fo. Qed.

    Lemma not_occurs_pos : forall {T}, ~occurs a T -> pos T.

    Proof. intros T h. gen (not_occurs_pos_neg h). fo. Qed.

    Lemma not_occurs_neg : forall {T}, ~occurs a T -> neg T.

    Proof. intros T h. gen (not_occurs_pos_neg h). fo. Qed.

  End pos.

End simple.

Infix "~~>" := Arr (at level 55, right associativity).

Hint Rewrite pos_base pos_arrow neg_base neg_arrow : pos.

Ltac simpl_pos := autorewrite with pos; simpl.

(****************************************************************************)
(** ** Functor building a Cmp structure for simple types from a Cmp
structure for type constants. *)

Module ST_Cmp (Export BCmp : Cmp) <: Cmp.

  Definition t := Ty BCmp.t.

  Fixpoint cmp A B :=
    match A, B with
      | Base a, Base b => BCmp.cmp a b
      | Base _, Arr _ _ => Lt
      | Arr _ _, Base _ => Gt
      | Arr A1 A2, Arr B1 B2 =>
          match cmp A1 B1 with
            | Eq => cmp A2 B2
            | c => c
          end
    end.

  Lemma cmp_opp : forall x y, cmp x y = CompOpp (cmp y x).

  Proof.
    induction x; destruct y; simpl; auto.
    apply BCmp.cmp_opp.
    rewrite IHx1. destruct (cmp y1 x1); simpl; auto.
  Qed.

End ST_Cmp.

(****************************************************************************)
(** ** Functor building a CmpTransLeibniz structure for simple types
from a CmpTransLeibniz structure for type constants. *)

Module ST_CmpTransLeibniz (Export BCmpTransLeibniz : CmpTransLeibniz)
  <: CmpTransLeibniz.

  Module C := ST_Cmp BCmpTransLeibniz.

  Include C.

  Lemma cmp_eq : forall x y, cmp x y = Eq -> x = y.

  Proof.
    induction x; destruct y; simpl; try discr.
    intro e. apply BCmpTransLeibniz.cmp_eq in e. subst. refl.
    case_eq (cmp x1 y1); intros e1 e2; f_equal;
      try apply IHx1 in e1; try apply IHx2 in e2; subst; (refl||discr).
  Qed.

  Lemma cmp_lt_trans :
    forall x y z, cmp x y = Lt -> cmp y z = Lt -> cmp x z = Lt.

  Proof.
    induction x; destruct y; destruct z; simpl; try (refl||discr).
    apply BCmpTransLeibniz.cmp_lt_trans.
    case_eq (cmp x1 y1); intro e1; try (refl||discr).
    apply cmp_eq in e1. subst.
    case_eq (cmp y1 z1); intro e2; try (refl||discr).   
    apply cmp_eq in e2. subst. fo.
    intros _. case_eq (cmp y1 z1); intro e2; try (refl||discr).
    apply cmp_eq in e2. subst.
    case_eq (cmp y2 z2); intro e2; try (refl||discr).
    intros _. case_eq (cmp x1 z1); intro e3; try (refl||discr).
    apply cmp_eq in e3. subst.
    Module CF := CmpFacts C. rewrite CF.eq_refl in e1. discr.
    rewrite e1 in e3. auto.
    intros _. case_eq (cmp x1 z1); intro e3; try (refl||discr).
    apply cmp_eq in e3. subst.
    rewrite C.cmp_opp, e2 in e1. discr.
    rewrite (IHx1 _ _ e1 e2) in e3. discr.
  Qed.

End ST_CmpTransLeibniz.

(****************************************************************************)
(** * Typing relation

Note that, for typing an abstraction [Lam x u] in [E], we do not
assume that [x] does not occur in [E], but overrides its type in
[E]. This is a restricted form of weakening. *)

Section typing.

  Variables F X So : Type.

  Notation Te := (@Te F X).
  Notation Var := (@Var F X).
  Notation Fun := (@Fun F X).
  Notation Ty := (@Ty So).

  Variable typ : F -> Ty.

  Definition Args f := vector Te (arity (typ f)).

  Variables (En : Type)
    (MapsTo : X -> Ty -> En -> Prop)
    (add : X -> Ty -> En -> En).

  Inductive tr : En -> Te -> Ty -> Prop :=
  | tr_var : forall E x T, MapsTo x T E -> tr E (Var x) T
  | tr_fun : forall E f, tr E (Fun f) (typ f)
  | tr_app : forall E u v V T, tr E u (V ~~> T) -> tr E v V -> tr E (App u v) T
  | tr_lam : forall E x X v V, tr (add x X E) v V -> tr E (Lam x v) (X ~~> V).

End typing.

(****************************************************************************)
(** * Structure over which we will define typing. *)

Require FMapInterface.

Module Type ST_Struct.

  Declare Module Export L : L_Struct.

  Parameter So : Type.

  Notation Ty := (Ty So).
  Notation Tys := (vector Ty).
 
  Parameter typ : F -> Ty.

  (** Module providing finite maps on variables. *)

  Declare Module Export XMap : FMapInterface.S with Module E := XOrd.

  (** Notations. *)

  Notation En := (XMap.t Ty).
  Notation empty := (XMap.empty Ty).
  Notation Args := (@Args F X So typ).

  (** Equivalence on environments. *)

  Infix "=&=" := (@Equal Ty) (at level 30).

End ST_Struct.

(****************************************************************************)
(** * Typing relation over an ST structure. *)

Module Make (Export ST : ST_Struct).

  Module Export B := LBeta.Make ST.L.

(****************************************************************************)
(** ** Typing environments

are finite maps from variables to types. *)

  Require Import FMapFacts.

  Module Export XMapFacts := Facts XMap.
  Module Export XMapProps := Properties XMap.
  Module Export XMapOrdProps := OrdProperties XMap.

  Export XMap ST.

  (** Inclusion ordering on environments. *)

  Definition le (E F : En) := forall x T, MapsTo x T E -> MapsTo x T F.

  Infix "<&=" := le (at level 40).

  Instance le_refl : Reflexive le.

  Proof. fo. Qed.

  Instance le_trans : Transitive le.

  Proof. intros E F G EF FG x T h. apply FG. apply EF. hyp. Qed.

  Instance le_Equal : Proper (@Equal Ty ==> @Equal Ty ==> impl) le.

  Proof.
    intros E E' EE' F F' FF' EF x T hx.
    rewrite <- FF'. apply EF. rewrite EE'. hyp.
  Qed.

  Lemma le_add : forall E x T, find x E = None -> E <&= add x T E.

  Proof.
    intros E x T hx y U hy. rewrite add_mapsto_iff. right. intuition.
    subst y. rewrite find_mapsto_iff, hx in hy. discr.
  Qed.

  Instance MapsTo_le : Proper (Logic.eq ==> Logic.eq ==> le ==> impl)
    (@MapsTo Ty).

  Proof. intros x y xy T V TV E F EF h. subst y V. fo. Qed.

  Instance In_le : Proper (Logic.eq ==> le ==> impl) (@In Ty).

  Proof. intros x y xy E F EF [T h]. subst y. exists T. fo. Qed.

  Instance add_le : Proper (XOrd.eq ==> Logic.eq ==> le ==> le) (@add Ty).

  Proof.
    intros x y xy T V TV E F EF. subst V. rewrite xy. intros z V.
    do 2 rewrite find_mapsto_iff, add_o. eq_dec y z.
    auto. do 2 rewrite <- find_mapsto_iff. rewrite EF. auto.
  Qed.

(****************************************************************************)
(** ** Restriction of an environment to some set of variables. *)

  Definition restrict_fun xs x (T:Ty) E :=
    if XSet.mem x xs then add x T E else E.

  Instance restrict_fun_e :
    Proper (XSet.Equal ==> XOrd.eq ==> Logic.eq ==> Equal ==> Equal)
      restrict_fun.

  Proof.
    intros xs xs' xsxs' x x' xx' T T' TT' E E' EE'. subst T'.
    unfold restrict_fun. rewrite xx', xsxs'. destruct (XSet.mem x' xs').
    rewrite xx', EE'. refl. hyp.
  Qed.

  Lemma restrict_fun_transp : forall xs,
    transpose_neqkey Equal (restrict_fun xs).

  Proof.
    intros xs x x' T T' E h z. unfold restrict_fun.
    destruct (XSet.mem x xs); destruct (XSet.mem x' xs); try refl.
    rewrite !add_o. eq_dec x z; eq_dec x' z; try refl. subst. tauto.
  Qed.

  Definition restrict_dom E xs := fold (restrict_fun xs) E empty.

  Lemma restrict_dom_empty : forall xs, Equal (restrict_dom empty xs) empty.

  Proof.
    intro xs. unfold restrict_dom. rewrite fold_Empty. refl. auto.
    apply empty_1.
  Qed.

  Lemma restrict_dom_add : forall xs x T E, ~In x E ->
    restrict_dom (add x T E) xs =&= restrict_fun xs x T (restrict_dom E xs).

  Proof.
    intros xs x T E hx. unfold restrict_dom. rewrite fold_add. refl. auto.
    apply restrict_fun_e. refl. apply restrict_fun_transp. hyp.
  Qed.

  Instance restrict_dom_e : Proper (Equal ==> XSet.Equal ==> Equal)
    restrict_dom.

  Proof.
    intro E; pattern E; apply map_induction_bis; clear E.
    (* Equal *)
    intros E E' EE' h F E'F xs xs' xsxs'. trans (restrict_dom E xs).
    sym. apply h. hyp. refl. apply h. trans E'; hyp. hyp.
    (* empty *)
    intros E h xs xs' xsxs'. rewrite restrict_dom_empty. unfold restrict_dom.
    rewrite fold_Empty. refl. auto. rewrite <- h. apply empty_1.
    (* add *)
    intros x T E hx h F e xs xs' xsxs'. rewrite restrict_dom_add. 2: hyp.
    unfold restrict_dom at -1. rewrite <- (fold_Equal _ _ _ e).
    rewrite fold_add; auto. apply restrict_fun_e; auto. apply h; auto. refl.
    apply restrict_fun_e. refl. apply restrict_fun_transp.
  Qed.
 
  Lemma mapsto_restrict_dom : forall E xs x T,
    MapsTo x T (restrict_dom E xs) <-> (MapsTo x T E /\ XSet.In x xs).

  Proof.
    intro E; pattern E; apply map_induction_bis; clear E.
    (* Equal *)
    intros E E' EE' h xs x T. rewrite <- EE'. apply h.
    (* empty *)
    intros xs x T. rewrite restrict_dom_empty. rewrite empty_mapsto_iff. tauto.
    (* add *)
    intros x T E hx h xs y V. rewrite restrict_dom_add. 2: hyp.
    unfold restrict_fun. case_eq (XSet.mem x xs).
    do 2 rewrite add_mapsto_iff. rewrite h. rewrite mem_iff. intuition.
    subst. hyp. 
    rewrite add_mapsto_iff, h, <- not_mem_iff. intuition.
    right. intuition. subst y. tauto.
    subst. tauto.
  Qed.

  Instance restrict_dom_s : Proper (le ==> Subset ==> le) restrict_dom.

  Proof.
    intros E F EF xs xs' xsxs' x T. do 2 rewrite mapsto_restrict_dom.
    rewrite <- xsxs', EF. auto.
  Qed.

  Lemma restrict_dom_le : forall E xs, restrict_dom E xs <&= E.

  Proof. intros E xs y hy. rewrite mapsto_restrict_dom. tauto. Qed.

  Lemma restrict_dom_singleton : forall E x,
    restrict_dom E (singleton x) =&=
    match find x E with None => empty | Some T => add x T empty end.

  Proof.
    intros E x. case_eq (find x E).
    (* Some *)
    intro T. rewrite <- find_mapsto_iff, Equal_mapsto_iff. intros hx y V.
    rewrite mapsto_restrict_dom. set_iff.
    rewrite add_mapsto_iff, empty_mapsto_iff.
    intuition; subst. 2: hyp. left. intuition. eapply MapsTo_fun. apply hx. hyp.
    (* None *)
    rewrite <- not_find_in_iff, Equal_mapsto_iff. intros hx y V.
    rewrite empty_mapsto_iff, mapsto_restrict_dom. set_iff. intuition.
    apply hx. exists V. subst. hyp.
  Qed.

  Lemma mapsto_restrict_dom_singleton : forall x T E,
    MapsTo x T E -> MapsTo x T (restrict_dom E (singleton x)).

  Proof. intros x T E h. rewrite mapsto_restrict_dom. set_iff. auto. Qed.

(****************************************************************************)
(** ** Domain of a typing environment. *)

  Definition dom_fun x (T:Ty) xs := XSet.add x xs.

  Instance dom_fun_e :
    Proper (Logic.eq ==> Logic.eq ==> XSet.Equal ==> XSet.Equal) dom_fun.

  Proof.
    intros x y xy T V TV s t st. subst. unfold dom_fun. rewrite st. refl.
  Qed.

  Lemma dom_fun_transp : transpose_neqkey XSet.Equal dom_fun.

  Proof. intros x y xy T V E. unfold dom_fun. apply add_add. Qed.

  Definition dom E := fold dom_fun E XSet.empty.

  Instance dom_e : Proper (Equal ==> XSet.Equal) dom.

  Proof.
    intros E F EF. unfold dom. apply fold_Equal. fo. apply dom_fun_e. hyp.
  Qed.

  Lemma dom_empty : dom empty [=] XSet.empty.

  Proof. unfold dom. rewrite fold_Empty. refl. fo. apply empty_1. Qed.

  Lemma dom_add_notin : forall x T E,
    ~In x E -> dom (add x T E) [=] XSet.add x (dom E).

  Proof.
    intros x T E h. unfold dom. rewrite fold_add. refl. fo. apply dom_fun_e.
    apply dom_fun_transp. hyp.
  Qed.

  Lemma In_dom : forall x E, XSet.In x (dom E) <-> In x E.

  Proof.
    intros x E; pattern E; apply map_induction_bis; clear E.
    (* Equal *)
    intros E F EF h. rewrite <- EF. hyp.
    (* empty *)
    rewrite dom_empty, empty_in_iff. set_iff. refl.
    (* add *)
    intros y T E hy h. rewrite dom_add_notin. 2: hyp.
    set_iff. rewrite add_in_iff, h. refl.
  Qed.

  Lemma dom_add : forall x T E, dom (add x T E) [=] XSet.add x (dom E).

  Proof.
    intros x T E y. rewrite In_dom, add_in_iff, <- In_dom. set_iff. refl.
  Qed.

(****************************************************************************)
(** ** Typing. *)

  Notation tr := (@tr F X So typ En (@MapsTo Ty) (@add Ty)).

  Notation "E '|-' v '~:' V" := (tr E v V) (at level 70).

(** If a term [v] is typable in [E], then its free variable are in
[E]. In fact, any subterm of [v] is typable in some extension of
[restrict_dom E (fv v)]. *)

  Lemma tr_fv_dom : forall E v V, E |- v ~: V -> fv v [<=] dom E.

  Proof.
    induction 1; simpl; intro z; set_iff.
    intro e. subst z. rewrite In_dom. exists T. hyp.
    tauto.
    intros [h|h]. apply IHtr1. hyp. apply IHtr2. hyp.
    intros [h1 h2]. rewrite In_dom, <- add_neq_in_iff. 2: apply h2.
    rewrite <- In_dom. apply IHtr. hyp.
  Qed.

(** Weakening: [tr] is compatible with [le]. *)

  Instance tr_le : Proper (le ==> Logic.eq ==> Logic.eq ==> impl) tr.

  Proof.
    intros E F EF t v tv T V TV ht. subst v V. revert E t T ht F EF.
    induction 1; intros F EF.
    apply tr_var. rewrite EF in H. hyp.
    apply tr_fun.
    apply tr_app with V. apply IHht1. hyp. apply IHht2. hyp.
    apply tr_lam. apply IHht. rewrite EF. refl.
  Qed.

(** Contraction: only the type of free variables need to be given. *)

  Lemma tr_contraction : forall E v V,
    E |- v ~: V -> forall y, ~XSet.In y (fv v) -> remove y E |- v ~: V.

  Proof.
    induction 1; intro y; simpl; set_iff; intro hy.
    apply tr_var. apply remove_2; auto.
    apply tr_fun.
    apply tr_app with V. apply IHtr1. tauto. apply IHtr2. tauto.
    apply tr_lam. eq_dec x y.
    (* x = y *)
    subst y. eapply tr_le with (x:=add x X0 E).
    intros z hz. do 2 rewrite find_mapsto_iff, add_o. rewrite remove_o.
    eq_dec x z; auto. refl. refl. hyp.
    (* x <> y *)
    eapply tr_le with (x:= remove y (add x X0 E)). 2: refl. 2: refl.
    intros z hz. do 2 rewrite find_mapsto_iff. rewrite add_o.
    do 2 rewrite remove_o. rewrite add_o.
    eq_dec y z. discr.
    eq_dec x z; auto.
    apply IHtr. tauto.
  Qed.

  Lemma tr_restrict : forall E v V,
    E |- v ~: V -> restrict_dom E (fv v) |- v ~: V.

  Proof.
    induction 1; simpl.
    apply tr_var. apply mapsto_restrict_dom_singleton. hyp.
    apply tr_fun.
    apply tr_app with V; eapply tr_le.
    apply restrict_dom_s. refl. apply union_subset_1. refl. refl. hyp.
    apply restrict_dom_s. refl. apply union_subset_2. refl. refl. hyp.
    apply tr_lam. eapply tr_le. 2: refl. 2: refl. 2: apply IHtr.
    intros y hy. rewrite mapsto_restrict_dom. do 2 rewrite add_mapsto_iff.
    rewrite mapsto_restrict_dom. set_iff. tauto.
  Qed.

(****************************************************************************)
(** ** Well-typed substitutions. *)

  Definition wt s E F := forall x T, MapsTo x T E -> F |- s x ~: T.

  Notation "F |-s s ~: E" := (wt s E F) (at level 70).

  Instance wt_le : Proper (Logic.eq ==> le --> le ==> impl) wt.

  Proof.
    intros s t st E E' E'E F F' FF' hs x T hx. subst t. eapply tr_le.
    apply FF'. refl. refl. apply hs. rewrite E'E. hyp.
  Qed.

  Lemma tr_subs : forall E v V, E |- v ~: V ->
    forall s F, F |-s s ~: E -> F |- subs s v ~: V.

  Proof.
    (* Assume that [t = Lam x v] and [T = U ~~> V]. Then, [subs s t =
      Lam x' (subs s' v)] and it may be the case that there is [y]
      such that [In y E] but [~In y (fv v)]. Then, it may be the case
      that there is [U' <> U] such that [MapsTo x' U' (restrict_dom F
      (fv (s y)))], in which case we cannot pove that [add x' U F |- s
      y ~: T]. We therefore need to restrict [E] to [restrict_dom E
      (fv t)] to prove the lemma. *)
    cut (forall E v V, E |- v ~: V ->
      forall s F, F |-s s ~: restrict_dom E (fv v) -> F |- subs s v ~: V).
    intros h E v V ht s F hs. eapply h. apply ht.
    intros x T. rewrite mapsto_restrict_dom. intros [h1 h2]. apply hs. hyp.
    (* end cut *)
    induction 1; simpl; intros s F hs.
    (* var *)
    apply hs. rewrite mapsto_restrict_dom. set_iff. tauto.
    (* fun *)
    apply tr_fun.
    (* app *)
    apply tr_app with V.
    apply IHtr1. intros x A. rewrite mapsto_restrict_dom. intros [h1 h2].
    apply hs. rewrite mapsto_restrict_dom. set_iff. tauto.
    apply IHtr2. intros x A. rewrite mapsto_restrict_dom. intros [h1 h2].
    apply hs. rewrite mapsto_restrict_dom. set_iff. tauto.
    (* lam *)
    set (x' := var x v s). set (s' := S.update x (Var x') s).
    apply tr_lam. apply IHtr. intros y T.
    rewrite mapsto_restrict_dom, add_mapsto_iff.
    intros [[[h1 h2]|[h1 h2]] h3]; unfold s', Def.update; eq_dec y x.
    (* (y,T) = (x,U) *)
    subst y T. apply tr_var. rewrite add_mapsto_iff. intuition. intuition.
    (* y <> x /\ MapsTo y T E *)
    intuition.
    assert (h2' : MapsTo y T (restrict_dom E (XSet.remove x (fv v)))).
    rewrite mapsto_restrict_dom. set_iff. intuition.
    gen (hs _ _ h2'); intro h. apply tr_restrict in h.
    set (F' := restrict_dom F (fv (s y))) in h. case_eq (find x' F').
    (* find x' F' = Some U' *)
    intro U'. rewrite <- find_mapsto_iff. unfold F'.
    rewrite mapsto_restrict_dom. intros [i1 i2].
    exfalso. eapply var_notin_fv_subs. apply h3. apply n. apply i2.
    (* find x' F' = None *)
    intro i. eapply tr_le with (x:=add x' X0 F') (x0:=s y) (x1:=T); try refl.
    unfold F'. rewrite restrict_dom_le. refl. rewrite <- le_add; hyp.
  Qed. 

(****************************************************************************)
(** ** Typing is compatible with alpha-equivalence. *)

  Instance tr_aeq_impl : Proper (Equal ==> aeq ==> Logic.eq ==> impl) tr.

  Proof.
    intros E E' EE' v v' vv' V V' VV' h. subst V'. revert v E V h E' EE' v' vv'.
    ind_size1 v; intros E V ht E' EE' v' vv'; inversion ht; inv_aeq vv'; subst.
    (* var *)
    apply tr_var. rewrite <- EE'. hyp.
    (* fun *)
    apply tr_fun.
    (* app *)
    apply tr_app with V0.
    eapply hu. apply H2. hyp. sym. hyp.
    eapply hv. apply H4. hyp. sym. hyp.
    (* lam *)
    apply tr_lam. eapply hu with (u':=rename x x1 v) (E:=add x1 X0 E).
    rewrite size_rename. refl. unfold Def.rename. eapply tr_subs.
    apply tr_restrict. apply H3. 2: rewrite EE'; refl. 2: sym; hyp.

    intros y V. unfold Def.single, Def.update.
    rewrite mapsto_restrict_dom, add_mapsto_iff. intros [h1 h2].
    eq_dec y x.
    subst y. assert (b : X0 = V). tauto. subst V.
    apply tr_var. rewrite add_mapsto_iff. auto.
    assert (b : MapsTo y V E). destruct h1. exfalso. apply n. sym. tauto. tauto.
    apply tr_var. rewrite add_mapsto_iff. eq_dec x1 y.
    subst x1. tauto. tauto.
  Qed.

  Instance tr_aeq : Proper (Equal ==> aeq ==> Logic.eq ==> iff) tr.

  Proof.
    intros E E' EE' v v' vv' V V' VV'. subst V'.
    split; apply tr_aeq_impl; (auto || sym; auto).
  Qed.

(****************************************************************************)
(** ** Subject reduction for beta. *)

  Instance tr_beta_aeq :
    Proper (Logic.eq ==> beta_aeq ==> Logic.eq ==> impl) tr.

  Proof.
    intros E E' EE' v v' vv' V V' VV' ht. subst E' V'. revert E v V ht v' vv'.
    induction 1; intros v' b; inv_beta_aeq b; subst.
    (* app_l *)
    rewrite h. apply tr_app with V. apply IHht1. hyp. hyp.
    (* app_r *)
    rewrite h. apply tr_app with V. hyp. apply IHht2. hyp.
    (* top *)
    rewrite h0. inversion ht1; subst. eapply tr_subs. apply H1.
    intros z B. rewrite add_mapsto_iff. intros [[h1 h2]|[h1 h2]].
    subst z B. rewrite single_eq. hyp.
    rewrite single_neq. 2: hyp. apply tr_var. hyp.
    (* lam *)
    destruct (fv_R_notin_fv_lam _ b).
    subst. apply tr_lam. apply IHht. rewrite rename_id in h0. hyp.
    rewrite (aeq_alpha x). 2: hyp. apply tr_lam. apply IHht. hyp.
  Qed.

End Make.
