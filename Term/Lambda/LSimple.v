(**
CoLoR, a Coq library on rewriting and termination.

See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2012-04-05

* Simply-typed lambda-terms
*)

Set Implicit Arguments.

From Coq Require Import Relations.
From CoLoR Require Import VecUtil LogicUtil OrdUtil NatUtil.
From CoLoR Require Export LBeta.
From CoLoR Require FMapUtil.

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

  Proof. intros p T. rewrite arity_output. lia. Qed.

  Arguments inputs_output_aux [p T] _.

  Lemma inputs_output : forall p T (h : p <= arity T),
    inputs (output T p) = Vsub (inputs T) (inputs_output_aux h).

  Proof.
    induction p; destruct T; simpl; intro h. refl.
    apply Vtail_eq. rewrite Vsub_cons, Vsub_id. refl.
    lia.
    assert (h' : p <= arity T2). lia.
    rewrite IHp with (h:=h'), Vsub_cons. apply Vsub_pi.
  Qed.

  Lemma output_Base (s : So) n : output (Base s) n = Base s.

  Proof. destruct n; refl. Qed.

  Lemma output_arrow_elim : forall n (A B C : Ty), output A n = B ~~> C
    -> output A (S n) = C /\ exists h : S n <= arity A, Vnth (inputs A) h = B.

  Proof.
    induction n; destruct A; intros B C; rewrite ?output_Base; try discr;
      simpl; intro e. inversion e; subst. split. refl.
    ex (le_n_S (le_0_n (arity C))). refl.
    destruct (IHn _ _ _ e) as [h1 [h2 h3]]. split.
    revert h1. destruct A2; auto.
    ex (le_n_S h2). rewrite <- h3. apply Vnth_eq. refl.
  Qed.

(** Building the type [T1 ~~> .. ~~> Tn -> U] from the type vector
[Ts] and the type [U]. *)

  Fixpoint arrow n (Ts : Tys n) U :=
    match Ts with
      | Vnil => U
      | Vcons T Ts' => T ~~> arrow Ts' U
    end.

  Lemma arrow_cast : forall n (Ts : Tys n) U n' (h:n=n'),
    arrow (Vcast Ts h) U = arrow Ts U.

  Proof. induction Ts; intros U n' e; subst; rewrite Vcast_refl; refl. Qed.

  Lemma arrow_output : forall T p q (h : p+q<=arity T),
    arrow (Vsub (inputs T) h) (output T (p+q)) = output T p.

  Proof.
    induction T; simpl; intros p q h.
    assert (p=0). lia. assert (q=0). lia. subst. refl.
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

Arguments output_arrow_elim [So n A B C] _.

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
  Notation Tes := (vector Te).
  Notation Var := (@Var F X).
  Notation Fun := (@Fun F X).
  Notation Ty := (@Ty So).

  Variable typ : F -> Ty.

  Definition TypArgs f := vector Te (arity (typ f)).

  Record Env := mk_Env {
    Env_type : Type;
    Env_empty : Env_type;
    Env_add : X -> Ty -> Env_type -> Env_type;
    Env_In : X -> Env_type -> Prop;
    Env_MapsTo : X -> Ty -> Env_type -> Prop;
    Env_Equal : relation Env_type }.

  Variable env : Env.

  Notation En := (Env_type env).
  Notation MapsTo := (Env_MapsTo env).
  Notation add := (Env_add env).

  Inductive tr : En -> Te -> Ty -> Prop :=
  | tr_var : forall E x T, MapsTo x T E -> tr E (Var x) T
  | tr_fun : forall E f, tr E (Fun f) (typ f)
  | tr_app : forall E u v V T, tr E u (V ~~> T) -> tr E v V -> tr E (App u v) T
  | tr_lam : forall E x X v V, tr (add x X E) v V -> tr E (Lam x v) (X ~~> V).

  Lemma tr_apps : forall n (us : Tes n) E t T (hn : n <= arity T),
    tr E t T
    -> (forall i (hi : i < n),
           tr E (Vnth us hi) (Vnth (inputs T) (lt_le_trans hi hn)))
    -> tr E (apps t us) (output T n).

  Proof.
    induction us; intros E t T hn ht g. hyp.
    rename h into u. simpl. destruct T as [b|A B]; simpl in hn. lia.
    apply IHus with (hn := le_S_n hn).
    apply tr_app with A. hyp. gen (g _ (lt_0_Sn n)). simpl. auto.
    intros i hi. gen (g _ (lt_n_S hi)). simpl.
    rewrite lt_unique with (h1 := lt_S_n (lt_n_S hi)) (h2 := hi).
    rewrite lt_unique with (h1 := lt_S_n _)
                             (h2 := lt_le_trans hi (le_S_n hn)). auto.
  Qed.

  Lemma tr_apps_fun_inv E f :
    forall n (ts : Tes n) T, tr E (apps (Fun f) ts) T
    -> T = output (typ f) n
       /\ exists nf : n <= arity (typ f), forall i (hi : i < n),
          tr E (Vnth ts hi) (Vnth (inputs (typ f)) (lt_le_trans hi nf)).

  Proof.
    induction n; intros ts T hT.
    VOtac. inversion hT; subst. split. refl. ex (le_0_n (arity (typ f))). lia.
    revert hT. VSntac ts. simpl Def.apps. rewrite apps_app.
    set (us := Vremove_last (Vcons (Vhead ts) (Vtail ts))). rewrite <- !H.
    intro hT. inversion hT. subst E0 T0. destruct (IHn _ _ H3) as [e [p h]].
    symmetry in e. destruct (output_arrow_elim e) as [h1 [h2 h3]]. split. hyp.
    ex h2. intros i hi. destruct (lt_dec i n) as [l|l].
    rewrite Vnth_remove_last_intro with (h1:=l). rewrite H. fold us.
    rewrite (lt_unique (lt_le_trans hi h2) (lt_le_trans l p)). apply h.
    assert (i=n). lia. subst i. rewrite <- Vlast_nth with (x := Vhead ts).
    rewrite Vnth_eq with (h2 := h2).
    setoid_rewrite h3.
    rewrite <- Vlast_tail. hyp. refl.
  Qed.

End typing.

Arguments tr_apps_fun_inv [F X So typ env E f n ts T] _.

Ltac env :=
  unfold Env_type, Env_empty, Env_add, Env_In, Env_MapsTo, Env_Equal in *.

(****************************************************************************)
(** * Structure over which we will define typing. *)

From Coq Require FMapInterface.

Module Type ST_Struct.

  Declare Module Export L : L_Struct.

  Parameter So : Type.

  Notation Ty := (Ty So).
  Notation Tys := (vector Ty).
 
  Parameter typ : F -> Ty.

  Notation TypArgs := (@TypArgs F X So typ).

  (** Module providing finite maps on variables. *)

  Declare Module Export XMap : FMapInterface.S with Module E := XOrd.

  Notation En := (@XMap.t Ty).
  Notation empty := (@XMap.empty Ty).
  Notation add := (@XMap.add Ty).
  Notation In := (@XMap.In Ty).
  Notation MapsTo := (@XMap.MapsTo Ty).
  Notation Equal := (@XMap.Equal Ty).
  Notation env := (mk_Env empty add In MapsTo Equal).

End ST_Struct.

(****************************************************************************)
(** * Typing relation over an ST structure. *)

Module Make (Export ST : ST_Struct).

  Module Export B := LBeta.Make ST.L.

(****************************************************************************)
(** ** Typing environments

are finite maps from variables to types. *)

  Module XMapUtil := FMapUtil.Make XMap.
  Module Export Domain := XMapUtil.Domain XSet.
  Export XMapUtil.

(****************************************************************************)
(** ** Typing. *)

  Notation tr := (@tr F X So typ env).

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
    eapply tr_le with (x:=add x X0 E). 2: refl. 2: refl.
    intros z hz. env. do 2 rewrite find_mapsto_iff, add_o. eq_dec x z; auto.
    rewrite remove_o. eq_dec y z. exfalso. apply n. trans y; hyp. auto. hyp.
    (* x <> y *)
    eapply tr_le with (x:= remove y (add x X0 E)). 2: refl. 2: refl.
    intros z hz. env. rewrite !find_mapsto_iff, add_o, !remove_o, add_o.
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
    eapply restrict_dom_s. refl. apply union_subset_1. refl. refl. hyp.
    eapply restrict_dom_s. refl. apply union_subset_2. refl. refl. hyp.
    apply tr_lam. eapply tr_le. 2: refl. 2: refl. 2: apply IHtr.
    intros y hy.
    env. rewrite mapsto_restrict_dom, !add_mapsto_iff, mapsto_restrict_dom.
    set_iff. tauto.
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
    env. rewrite mapsto_restrict_dom, add_mapsto_iff.
    intros [[[h1 h2]|[h1 h2]] h3]; unfold s', Def.update; eq_dec y x.
    (* (y,T) = (x,U) *)
    subst y T. apply tr_var. env. rewrite add_mapsto_iff. intuition. intuition.
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
    eapply hu. apply H2. hyp. hyp.
    eapply hv. apply H4. hyp. hyp.
    (* lam *)
    apply tr_lam. eapply hu with (u':=rename x x1 v) (E:=add x1 X0 E).
    rewrite size_rename. refl. unfold Def.rename. eapply tr_subs.
    eapply tr_restrict. apply H3. 2: rewrite EE'; refl. 2: hyp.

    intros y V. unfold Def.single, Def.update.
    env. rewrite mapsto_restrict_dom, add_mapsto_iff. intros [h1 h2].
    eq_dec y x. unfold XSet.E.eq in e. subst.
    assert (b : X0 = V). tauto. subst V.
    apply tr_var. env. rewrite add_mapsto_iff. auto.
    assert (b : MapsTo y V E). destruct h1. exfalso. apply n. sym. tauto. tauto.
    apply tr_var. env. rewrite add_mapsto_iff. eq_dec x1 y.
    unfold XSet.E.eq in e. subst x1. tauto. tauto.
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
    intros z B. env. rewrite add_mapsto_iff. intros [[h1 h2]|[h1 h2]].
    subst z B. rewrite single_eq. hyp.
    rewrite single_neq. 2: hyp. apply tr_var. hyp.
    (* lam *)
    destruct (fv_R_notin_fv_lam _ b).
    subst. apply tr_lam. apply IHht. rewrite rename_id in h0. hyp.
    rewrite (aeq_alpha x). 2: hyp. apply tr_lam. apply IHht. hyp.
  Qed.

End Make.
