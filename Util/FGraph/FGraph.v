(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2011-01-18

finite graphs
*)

From Coq Require Import OrderedType.
From CoLoR Require Import ListUtil FSetUtil FMapUtil RelUtil LogicUtil.

Set Implicit Arguments.

Module Make (XSet : FSetInterface.S)
       (XMap : FMapInterface.S with Module E := XSet.E).

  Module Export S := FSetUtil.Make XSet.
  Module Export M := FMapUtil.Make XMap.

  Module R := RelUtil.
  Module Import X := E.

  Lemma eq_com x y : eq x y <-> eq y x.

  Proof. firstorder auto with crelations. Qed.

(***********************************************************************)
(** A finite graph on X.t is represented by its successor map: a
finite map from X.t to the type of finite sets on X.t. Since an
element can be mapped to the empty set, this representation is not
unique and the setoid equality on maps based on the setoid equality on
sets (meq) does not identify a map with no mapping for x and a map
mapping x to the empty set. We therefore have to consider another
equivalence (geq). We will consider that two graphs are equivalent if
they define the same relation. See below for more details. *)

  Definition graph := XMap.t XSet.t.

  Implicit Type g h : graph.

  Definition meq : relation graph := XMap.Equiv XSet.Equal.

  #[global] Instance Equal_meq : subrelation Equal meq.

  Proof. intros g h gh. apply Equal_Equiv with (eq:=XSet.Equal) in gh; fo. Qed.

(***********************************************************************)
(** relation corresponding to a graph *)

  (*COQ: necessary to define rel (hereafter) as a coercion *)
  SubClass relation_on_X := relation X.t.

  Definition rel g : relation_on_X :=
    fun x y => exists s, find x g = Some s /\ XSet.In y s.

  Coercion rel : graph >-> relation_on_X.

  Lemma rel_empty : rel empty == empty_rel.

  Proof.
    rewrite rel_eq; intros a b. unfold empty_rel. split_all.
    destruct H as [sa [a1 a2]]. rewrite <- find_mapsto_iff in a1.
    rewrite empty_mapsto_iff in a1. hyp.
  Qed.

  #[global] Instance rel_meq_ext' : Proper (meq ==> eq ==> eq ==> impl) rel.

  Proof.
    intros g g' gg' x x' xx' y y' yy'. unfold impl, rel. intro h.
    destruct h as [sx [hx hy]].
    destruct (Equiv_find_Some gg' hx) as [sx' [h1 h2]].
    exists sx'. rewrite <- yy'. rewrite <- h2 at 2. split_all.
    (*SLOW:rewrite <- xx'.*) rewrite <- h1. apply find_o. hyp.
  Qed.

  (*COQ: can be removed? Coq stuck in In_preds_rel *)
  #[global] Instance rel_meq_ext : Proper (meq ==> eq ==> eq ==> iff) rel.

  Proof.
    intros g g' gg' x x' xx' y y' yy'. split; intro h.
    rewrite  <- gg', <- xx', <- yy'. hyp.
    rewrite  gg', xx', yy'. hyp.
  Qed.

  Lemma find_Some_rel {g x s} : find x g = Some s ->
    XSet.is_empty s = false -> exists y, rel g x y.

  Proof.
    intros hx hs. destruct (choose_mem_3 _ hs) as [y [h1 h2]].
    rewrite <- mem_iff in h2. ex y s. tauto.
  Qed.

(***********************************************************************)
(** singleton relation *)

  Definition id x y a b := eq a x /\ eq b y.

(***********************************************************************)
(** relation defined by an element and a set of successors *)

  Definition succ x s a b := eq a x /\ XSet.In b s.

  #[global] Instance succ_m_ext' : Proper (eq ==> XSet.Equal ==> eq ==> eq ==> impl) succ.

  Proof.
    intros x x' xx' s s' ss' a a' aa' b b' bb'. unfold succ.
    rewrite xx', ss', aa', bb'. refl.
  Qed.

  (*COQ: can be removed? used in rel_set_fold_add_edge *)
  #[global] Instance succ_m' : Proper (eq ==> XSet.Equal ==> inclusion) succ.

  Proof.
    intros x x' xx' s s' ss' a b. unfold succ. rewrite xx', ss'. tauto.
  Qed.

  (*COQ: can be removed? used in rel_set_fold_add_edge *)
  #[global] Instance succ_m : Proper (eq ==> XSet.Equal ==> same) succ.

  Proof.
    intros x x' xx' s s' ss'. split.
    rewrite xx', ss'. refl. rewrite <- xx', <- ss'. refl.
  Qed.

  Lemma succ_empty : forall x, succ x XSet.empty == empty_rel.

  Proof.
    intro x. rewrite rel_eq; intros a b. unfold succ, empty_rel. split_all.
    revert H0. set_iff. auto.
  Qed.

  Lemma succ_add : forall x y s, succ x (XSet.add y s) == id x y U succ x s.

  Proof.
    intros x y s. apply rel_eq; intros a b.
    unfold Relation_Operators.union, succ, id. rewrite add_iff. firstorder auto with crelations.
  Qed.

  Lemma rel_add : forall x g s, ~In x g -> rel (add x s g) == succ x s U g.

  Proof.
    intros x g s n. rewrite rel_eq; intros a b.
    unfold Relation_Operators.union. split.
    (* -> *)
    intros [t [t1 t2]]. rewrite add_o in t1. destruct (eq_dec x a).
    inversion t1. subst t. firstorder auto with crelations.
    right. exists t. tauto.
    (* <- *)
    intros [ab|ab]. exists s. unfold succ in ab. split_all. rewrite add_o.
    destruct (eq_dec x a). refl. absurd (eq x a); hyp.
    destruct ab as [t [t1 t2]]. exists t. split_all. rewrite add_o.
    destruct (eq_dec x a). 2: hyp. absurd (In x g). hyp. rewrite e.
    exists t. change (MapsTo a t g). rewrite find_mapsto_iff. hyp.
  Qed.

(***********************************************************************)
(** relation defined by an element and a list of successors *)

  Definition succ_list x s a (b : X.t) := eq a x /\ InA eq b s.

  #[global] Instance succ_list_m_ext' :
    Proper (eq ==> eqlistA eq ==> eq ==> eq ==> impl) succ_list.

  Proof.
    intros x x' xx' s s' ss' a a' aa' b b' bb'. unfold succ_list.
    (*SLOW*)rewrite xx', ss', aa', bb'. refl.
  Qed.

  Lemma succ_list_nil : forall x, succ_list x nil == empty_rel.

  Proof.
    intro x. rewrite rel_eq; intros a b. unfold succ_list, empty_rel.
    split_all. inversion H0.
  Qed.

  Lemma succ_list_cons : forall x y l,
    succ_list x (y :: l) == id x y U succ_list x l.

  Proof.
    intros x y l. apply rel_eq; intros a b.
    unfold Relation_Operators.union, succ_list, id. rewrite InA_cons. fo.
  Qed.

(***********************************************************************)
(** product relation *)

  Definition prod s t a b := XSet.In a s /\ XSet.In b t.

  Lemma prod_m_ext :
    Proper (XSet.Equal ==> XSet.Equal ==> eq ==> eq ==> iff) prod.

  Proof.
    intros s s' ss' t t' tt' a a' aa' b b' bb'. unfold prod.
    rewrite ss', tt', aa', bb'. refl.
  Qed.

(***********************************************************************)
(** ordering on graphs: [g] is smaller than [g'] if [rel g] is
included in [rel g'] *)

  Definition gle g h := g << h.

  #[global] Instance gle_PreOrder : PreOrder gle.

  Proof. fo. Qed.

  Lemma empty_gle : forall g, rel empty << g.

  Proof. intro g. rewrite rel_empty. fo. Qed.

(***********************************************************************)
(** equality on graphs: two graphs are equivalent if they define the
same relation *)

  Definition geq g h := g == h.

  #[global] Instance geq_Equivalence : Equivalence geq.

  Proof. fo. Qed.

  Lemma meq_geq : meq << geq.

  Proof.
    intros g h gh. split; intros x y xy. rewrite <- gh. hyp. rewrite gh. hyp.
  Qed.

  #[global] Instance geq_meq : Proper (meq ==> meq ==> iff) geq.

  Proof.
    intros g g' gg' h h' hh'. apply meq_geq in gg'. apply meq_geq in hh'.
    split; intro H. rewrite <- gg', <- hh'. hyp. rewrite gg', hh'. hyp.
  Qed.

  #[global] Instance geq_Equal : Proper (Equal ==> Equal ==> iff) geq.

  Proof.
    eapply prop2_incl. 4: apply geq_meq.
    apply Equal_meq. apply Equal_meq. refl.
  Qed.

  Lemma Equal_geq : Equal << geq.

  Proof. trans meq. apply Equal_meq. apply meq_geq. Qed.

(***********************************************************************)
(** relations between gle and geq *)

  Lemma gle_antisym : forall g h, geq g h <-> (gle g h /\ gle h g).

  Proof. fo. Qed.

  #[global] Instance gle_geq' : Proper (geq ==> geq ==> impl) gle.

  Proof.
    intros g g' gg' h h' hh'. rewrite gle_antisym in gg', hh'. unfold impl.
    intuition. trans g. hyp. trans h. hyp. hyp.
  Qed.

(***********************************************************************)
(** properties of rel *)

  #[global] Instance rel_gle_ext : Proper (gle ==> eq ==> eq ==> impl) rel.

  Proof.
    intros g g' gg' x x' xx' y y' yy' [s [s1 s2]]. apply gg'. exists s.
    (*SLOW:rewrite <- xx', <- yy'. tauto.*) split.
    rewrite <- s1. apply find_o. hyp. rewrite <- yy'. hyp.
  Qed.

  (*COQ: can be removed? used in TransClos *)
  #[global] Instance rel_geq_ext' : Proper (geq ==> eq ==> eq ==> impl) rel.

  Proof.
    intros g g' gg' x x' xx' y y' yy' [s [s1 s2]]. apply gg'. exists s.
    (*SLOW:rewrite <- xx', <- yy'. tauto.*) split.
    rewrite <- s1. apply find_o. hyp. rewrite <- yy'. hyp.
  Qed.

(***********************************************************************)
(** successors of a node *)

  Definition succs x g :=
    match find x g with
      | Some s => s
      | None => XSet.empty
    end.

  Lemma In_succs_rel : forall g x y, XSet.In y (succs x g) <-> rel g x y.

  Proof.
    intros. unfold succs, rel. destruct (find x g) as [t|]; split_all.
    ex t. tauto. inversion H. hyp. revert H. set_iff. tauto. discr.
  Qed.

  Lemma mem_succs_rel : forall g x y,
    XSet.mem y (succs x g) = true <-> rel g x y.

  Proof. intros. rewrite <- mem_iff. apply In_succs_rel. Qed.

  Lemma succs_empty : forall x, succs x empty = XSet.empty.

  Proof. intro x. unfold succs. rewrite find_empty. refl. Qed.

  Lemma succs_add : forall x y s g,
    succs x (add y s g) = if eq_dec y x then s else succs x g.

  Proof.
    intros x y s g. unfold succs at 1. rewrite add_o.
    destruct (eq_dec y x); refl.
  Qed.

  Lemma succs_add_id : forall x s g, succs x (add x s g) = s.

  Proof. intros x s g. unfold succs. rewrite add_eq_o. refl. refl. Qed.

  #[global] Instance succs_gle : Proper (eq ==> gle ==> XSet.Subset) succs.

  Proof.
    intros x x' xx' g g' gg'. unfold succs. rewrite <- xx'. clear x' xx'.
    destruct (find x g) as [t|] eqn:H; destruct (find x g') as [t0|] eqn:H0.
    (* find x g = Some t0, find x g' = Some t1 *)
    intros y hy.
    assert (xy : rel g x y). exists t. intuition. rewrite gg' in xy.
    destruct xy as [s [s1 s2]]. rewrite H0 in s1. inversion s1. subst t0. hyp.
    (* find x g = Some t0, find x g' = None *)
    case_eq (XSet.is_empty t); intros.
    rewrite is_empty_eq in H1. rewrite H1. refl.
    destruct (find_Some_rel H H1) as [y hy]. rewrite gg' in hy.
    destruct hy as [s [s1 s2]]. rewrite H0 in s1. discr.
    (* find x g = None, find x g' = Some t0 *)
    intro; set_iff; intuition.
    (* find x g = None, find x g' = None *)
    refl.
  Qed.

  (*COQ: can be removed? used in geq_add_remove *)
  #[global] Instance succs_geq : Proper (eq ==> geq ==> XSet.Equal) succs.

  Proof.
    intros x x' xx' g g' gg'. rewrite gle_antisym in gg'.
    destruct gg' as [gg' g'g]. rewrite Subset_antisym. split.
    rewrite xx', gg'. refl. (*SLOW:rewrite xx', g'g. refl.*)
    apply succs_gle; hyp.
  Qed.

  Lemma mem_succs_id : forall g x y,
    XSet.mem y (succs x g) = true -> g U id x y == g.

  Proof.
    intros g x y h. split. rewrite union_incl_eq. split. refl.
    intros a b [xa yb]. rewrite xa, yb. rewrite <- mem_succs_rel. hyp.
    apply incl_union_l. refl.
  Qed.

(***********************************************************************)
(** g is smaller then g' iff the successors of g are included in the
successors of g' *)

  Lemma gle_succs : forall g g',
    gle g g' <-> forall x, succs x g [<=] succs x g'.

  Proof.
    intros g g'. split.
    intros gg' x. rewrite gg'. refl.
    intro h. intros x y. rewrite <- !In_succs_rel.
    rewrite (h x). auto.
  Qed.

(***********************************************************************)
(** two graphs are equivalent iff they have the same successors *)

  Lemma geq_succs : forall g g',
    geq g g' <-> forall x, succs x g [=] succs x g'.

  Proof. intros g g'. rewrite gle_antisym. rewrite !gle_succs. fo. Qed.

(***********************************************************************)
(** properties of geq wrt add *)

  Lemma geq_add_remove : forall y s g g', ~In y g -> geq (add y s g) g' ->
    geq g (if XSet.is_empty s then g' else remove y g').

  Proof.
    intros y s g g' n e. case_eq (XSet.is_empty s); intros.
    (* s empty *)
    rewrite geq_succs; intro z. rewrite <- e. rewrite succs_add.
    destruct (eq_dec y z). 2: refl. rewrite <- e0. unfold succs.
    rewrite not_find_in_iff in n. rewrite n. sym. apply is_empty_eq. hyp.
    (* s not empty *)
    rewrite geq_succs; intro z. unfold succs at 2. rewrite remove_o.
    case_eq (eq_dec y z); intros.
    rewrite <- e0. unfold succs. rewrite not_find_in_iff in n. rewrite n. refl.
    fold (succs z g'). trans (succs z (add y s g)).
    rewrite succs_add. rewrite H0. refl. rewrite e. refl.
  Qed.

  Lemma geq_add : forall y s g g', ~In y g -> geq (add y s g) g' ->
    if XSet.is_empty s then geq g' g else Add y (succs y g') (remove y g') g'.

  Proof.
    intros y s g g' n e. case_eq (XSet.is_empty s); intros.
    (* s empty *)
    rewrite geq_succs; intro z. rewrite <- e. rewrite succs_add.
    destruct (eq_dec y z). 2: refl.
    rewrite <- e0. unfold succs. rewrite not_find_in_iff in n. rewrite n.
    apply is_empty_eq. hyp.
    (* s not empty *)
    unfold Add. intro z. rewrite add_o. case_eq (eq_dec y z); intros.
    (* y = z *)
    unfold succs. (*SLOW*)rewrite e0. case_eq (find z g'); intros. refl.
    rewrite geq_succs in e. ded (e y). rewrite succs_add_id in H2.
    rewrite e0 in H2. unfold succs in H2. rewrite H1 in H2.
    rewrite <- is_empty_eq in H2. rewrite H in H2. discr.
    (* y <> z *)
    rewrite remove_o. rewrite H0. refl.
  Qed.

(***********************************************************************)
(** predecessors of a node *)

  Definition preds_aux x y sy s := if XSet.mem x sy then XSet.add y s else s.

  #[global] Instance preds_aux_m :
    Proper (eq ==> eq ==> XSet.Equal ==> XSet.Equal ==> XSet.Equal) preds_aux.

  Proof.
    intros x x' xx' y y' yy' s s' ss' t t' tt'. unfold preds_aux.
    rewrite xx', ss'. destruct (XSet.mem x' s'). rewrite yy', tt'. refl. hyp.
  Qed.

  (*COQ: can be removed? apply preds_aux_m doesn't work in some cases *)
  #[global] Instance preds_aux_m' :
    Proper (Logic.eq ==> eq ==> Logic.eq ==> XSet.Equal ==> XSet.Equal)
    preds_aux.

  Proof.
    eapply prop4_incl. 6: apply preds_aux_m.
    apply eq_incl_refl_rel. class.
    refl.
    apply eq_incl_refl_rel. class.
    refl.
    refl.
  Qed.

  Lemma preds_aux_transp : forall x, transpose_neqkey XSet.Equal (preds_aux x).

  Proof.
    unfold transpose_neqkey. intros x y z s t u n. unfold preds_aux.
    destruct (XSet.mem x s); destruct (XSet.mem x t); try refl.
    apply XSetProps.add_add.
  Qed.

  Definition preds x g := fold (preds_aux x) g XSet.empty.

  #[global] Instance preds_Equal : Proper (eq ==> Equal ==> XSet.Equal) preds.

  Proof.
    intros x x' xx' g g' gg'. unfold preds.
    apply fold_Equiv_ext with (eq := XSet.Equal). fo. fo.
    apply preds_aux_m. refl. apply preds_aux_transp.
    apply preds_aux_m. hyp. apply Equal_Equiv. fo. hyp. refl.
  Qed.

  Lemma preds_empty : forall x, preds x empty [=] XSet.empty.

  Proof. intro x. unfold preds. rewrite fold_empty. refl. Qed.

  Lemma preds_add : forall x y s g, ~In y g -> preds x (add y s g)
    [=] if XSet.mem x s then XSet.add y (preds x g) else preds x g.

  Proof.
    intros x y s g nyg. unfold preds. rewrite fold_add. refl. fo.
    apply preds_aux_m'. refl. apply preds_aux_transp. hyp.
  Qed.

  Lemma preds_geq_empty : forall x g,
    geq g empty -> preds x g [=] XSet.empty.

  Proof.
    intros x g. pattern g; apply map_induction_bis; clear g.
    (* Equal *)
    intros m m' mm' h hm'. rewrite <- mm'. apply h. rewrite mm'. hyp.
    (* empty *)
    intros _. unfold preds. rewrite fold_empty. refl.
    (* add *)
    intros y s g n h e. rewrite preds_add. 2: hyp.
    case_eq (XSet.mem x s); intros.
    (* x in s *)
    ded (geq_add n e). rewrite (mem_is_empty H) in H0. ded (H0 y).
    rewrite empty_o, succs_empty, add_o in H1.
    destruct (eq_dec y y). discr. absurd (eq y y). hyp. refl.
    (* x not in s *)
    apply h. ded (geq_add_remove n e). rewrite H0. destruct (XSet.is_empty s).
    refl. rewrite remove_empty. refl.
  Qed.

  #[global] Instance preds_geq : Proper (eq ==> geq ==> XSet.Equal) preds.

  Proof.
    intros x x' xx' g; revert x x' xx'.
    pattern g; apply map_induction_bis; clear g.
    (* [=] *)
    intros m m' mm' hm x x' xx' g m'g. apply Equal_geq in mm'.
    trans (preds x m).
    sym. apply hm. refl. hyp.
    apply hm. hyp. trans m'; hyp.
    (* empty *)
    intros x x' xx' g hg. rewrite preds_empty. sym. apply preds_geq_empty. hyp.
    (* add *)
    intros y s g n h x x' xx' g' e. unfold preds. rewrite fold_add.
    2: class. 2: apply preds_aux_m'. 2: refl. 2: apply preds_aux_transp.
    2: hyp. fold (preds x g). fold (preds x' g'). ded (geq_add_remove n e).
    revert H. case_eq (XSet.is_empty s); intros; unfold preds_aux.
    (* s empty *)
    rewrite mem_3. apply h; hyp. rewrite <- XSetFacts.is_empty_iff in H.
    apply H.
    (* s not empty *)
    ded (geq_add n e). rewrite H in H1. unfold preds at 3. rewrite fold_Add.
    6: apply H1. 2: class. 2: apply preds_aux_m'. 2: refl.
    2: apply preds_aux_transp.
    2:{rewrite remove_in_iff. intros [h1 h2]. absurd (eq y y). hyp. refl. }
    fold (preds x' (remove y g')). unfold preds_aux. rewrite <- xx'.
    rewrite <- e at 1. rewrite succs_add_id. destruct (XSet.mem x s).
    rewrite <- xx'. apply XSetFacts.add_m. refl. apply h. refl. hyp.
    apply h. hyp. hyp.
  Qed.

  Lemma In_preds_rel : forall x y g, XSet.In x (preds y g) <-> rel g x y.

  Proof.
    intros x y g. pattern g; apply map_induction_bis; clear g.
    (* Equal *)
    intros m m' mm' h. (*SLOW*)rewrite <- mm'. hyp.
    (* empty *)
    rewrite preds_empty. split. intro h. revert h. set_iff. tauto.
    intros [s [s1 s2]]. rewrite empty_o in s1. discr.
    (* add *)
    intros z s g n h. rewrite preds_add. 2: hyp.
    case_eq (XSet.mem y s); intros.
    (* y in s *)
    rewrite add_iff. rewrite h. split.
    (* -> *)
    intros [h'|h']. exists s. rewrite add_eq_o. rewrite mem_iff. intuition. hyp.
    destruct h' as [t [t1 t2]]. exists t. rewrite add_o. destruct (eq_dec z x).
    (*SLOW*)rewrite not_find_in_iff, e in n. rewrite n in t1. discr. tauto.
    (* <- *)
    intros [t [t1 t2]]. rewrite add_o in t1. destruct (eq_dec z x). auto.
    right. exists t. tauto.
    (* y not in s *)
    rewrite h. split.
    (* -> *)
    intros [t [t1 t2]]. exists t. rewrite add_o. destruct (eq_dec z x).
    (*SLOW*)rewrite not_find_in_iff, e in n. rewrite n in t1. discr. tauto.
    (* <- *)
    intros [t [t1 t2]]. rewrite add_o in t1. destruct (eq_dec z x).
    inversion t1. subst t. rewrite XSetFacts.mem_iff in t2. rewrite H in t2.
    discr.
    exists t. tauto.
  Qed.

  Lemma prod_add_incl_tc_id : forall x y g,
    prod (XSet.add x (preds x g)) (XSet.add y (succs y g)) << (g U id x y)!.

  Proof.
    intros x y g a b. unfold prod. rewrite !add_iff.
    rewrite In_preds_rel, In_succs_rel. split_all.
    (* eq x a /\ eq y b *)
    apply t_step. firstorder auto with crelations.
    (* g a x /\ eq y b *)
    apply t_trans with x; apply t_step; firstorder auto with crelations.
    (* eq x a /\ g y b *)
    apply t_trans with y; apply t_step; firstorder auto with crelations.
    (* g a x /\ g y b *)
    apply t_trans with x. firstorder auto with sets.
    apply t_trans with y; apply t_step; firstorder auto with crelations.
  Qed.

(***********************************************************************)
(** add an edge into a graph *)

  Definition add_edge x y g : graph := add x (XSet.add y (succs x g)) g.

  #[global] Instance add_edge_gle : Proper (eq ==> eq ==> gle ==> gle) add_edge.

  Proof.
    intros x x' xx' y y' yy' g g' gg'. unfold add_edge.
    rewrite gle_succs. intro z. rewrite !succs_add.
    destruct (eq_dec x z); destruct (eq_dec x' z).
    rewrite xx', yy', gg'. refl.
    rewrite xx' in e. contr. rewrite xx' in n. contr.
    rewrite gg'. refl.
  Qed.

  (*COQ: can be removed? used in TransClos*)
  #[global] Instance add_edge_geq : Proper (eq ==> eq ==> geq ==> geq) add_edge.

  Proof.
    intros x x' xx' y y' yy' g g' gg'. rewrite gle_antisym.
    rewrite gle_antisym in gg'. destruct gg' as [gg' g'g]. split.
    (*SLOW:rewrite xx', yy', gg'. refl.*) apply add_edge_gle; hyp.
    (*SLOW:rewrite <- xx', <- yy', g'g. refl.*) apply add_edge_gle; hyp.
  Qed.

  Lemma rel_add_edge : forall x y g, add_edge x y g == g U id x y.

  Proof.
    intros. rewrite rel_eq; intros a b.
    unfold add_edge, Relation_Operators.union, id. split_all.
    destruct H as [sa [a1 a2]]. rewrite add_o in a1. destruct (eq_dec x a).
    inversion a1. subst sa. rewrite add_iff in a2. rewrite In_succs_rel in a2.
    rewrite e in a2. split_all. auto with ordered_type.
    left. exists sa. tauto.
    destruct H as [sa [a1 a2]]. unfold rel. rewrite add_o.
    destruct (eq_dec x a).
    exists (XSet.add y (succs x g)). split_all. rewrite add_iff. right.
    rewrite e, In_succs_rel. exists sa. auto.
    exists sa. auto.
    unfold rel. rewrite add_o. destruct (eq_dec x a).
    exists (XSet.add y (succs x g)). split_all. rewrite add_iff. auto with ordered_type.
    absurd (eq x a); hyp.
  Qed.

  Lemma add_edge_transp_geq : forall x, transpose geq (add_edge x).

  Proof.
    intros x y z g. unfold geq. rewrite !rel_add_edge.
    unfold same, inclusion, id, Relation_Operators.union. tauto.
  Qed.

(***********************************************************************)
(** set iteration of (add_edge x) *)

  Lemma rel_set_fold_add_edge : forall x s g0,
    XSet.fold (add_edge x) s g0 == succ x s U g0.

  Proof.
    intros x s g0. pattern (XSet.fold (add_edge x) s g0).
    apply XSetProps.fold_rec_weak; clear s.
    (* [=] *)
    intros s t g st i. rewrite <- st. hyp.
    (* empty *)
    rewrite succ_empty. rewrite R.union_empty_l. refl.
    (* add *)
    intros z g s nzs e. rewrite rel_add_edge. rewrite e.
    rewrite R.union_assoc. rewrite union_commut with (R:=rel g0).
    rewrite <- R.union_assoc. apply R.union_same. 2: refl.
    rewrite rel_eq; intros a b. unfold succ, Relation_Operators.union, id.
    rewrite add_iff, (eq_com b z). tauto.
  Qed.

  (*COQ: can we remove this lemma? *)
  Lemma rel_set_fold_add_edge_ext : forall x s g0 a b,
    rel (XSet.fold (add_edge x) s g0) a b <-> succ x s a b \/ rel g0 a b.

  Proof.
    split; intro h. apply rel_set_fold_add_edge in h. hyp.
    apply rel_set_fold_add_edge. hyp.
  Qed.

(***********************************************************************)
(** list iteration of (add_edge x) *)

  Definition add_edge' x g y := add_edge x y g.

  Lemma rel_list_fold_left_add_edge : forall x l g0,
    fold_left (add_edge' x) l g0 == succ_list x l U g0.

  Proof.
    induction l; simpl; intro g. rewrite succ_list_nil, R.union_empty_l. refl.
    rewrite IHl, succ_list_cons. unfold add_edge'. rewrite rel_add_edge.
    rewrite union_commut with (R:=rel g). rewrite <- R.union_assoc.
    rewrite union_commut with (R:=id x a). refl.
  Qed.

(***********************************************************************)
(** building graphs by list iteration *)

  Section list_fold_left.

    Variables (A : Type) (F : graph -> A -> graph)
      (hF : forall g a, F g a == F empty a U g).

    Lemma rel_list_fold_left : forall l g x y, rel (fold_left F l g) x y
      <-> (rel g x y \/ exists a, List.In a l /\ rel (F empty a) x y).

    Proof.
      induction l; simpl. fo. intros g x y. rewrite IHl. split_all.
      apply hF in H. destruct H. right. exists a. tauto. tauto.
      right. exists x0. tauto.
      left. apply hF. right. hyp.
      subst x0. left. apply hF. left. hyp.
      right. exists x0. tauto.
    Qed.

  End list_fold_left.

End Make.
