(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2011-01-18

Transitive closure of a finite graph.
*)

From Stdlib Require Import OrderedType.
From CoLoR Require Import RelUtil LogicUtil BoolUtil FGraph.
From CoLoR Require ListUtil.

Set Implicit Arguments.

Module Make (XSet : FSetInterface.S)
       (XMap : FMapInterface.S with Module E := XSet.E).

  Module Export G := FGraph.Make XSet XMap.

  Implicit Type g h : graph.

  Import X.

  Module R := RelUtil.

(***********************************************************************)
(** (a,b) in (pred x s g) if a is a predecessor of x in g and b in s *)

  Definition pred x s g a b := rel g a x /\ XSet.In b s.

  Global Instance pred_geq' :
    Proper (eq ==> XSet.Equal ==> geq ==> inclusion) pred.

  Proof.
    intros x x' xx' s s' e g g' gg' a b. unfold pred. rewrite xx', e, gg'.
    tauto.
  Qed.

  Global Instance pred_geq :
    Proper (eq ==> XSet.Equal ==> geq ==> same) pred.

  Proof. split; apply pred_geq'; hyp. Qed.

  Global Instance pred_geq_ext' :
    Proper (eq ==> XSet.Equal ==> geq ==> eq ==> eq ==> impl) pred.

  Proof.
    intros x x' xx' s s' e g g' gg' a a' aa' b b' bb'. unfold pred.
    rewrite xx', e, gg', aa', bb'. refl.
  Qed.

  Global Instance pred_geq_ext :
    Proper (eq ==> XSet.Equal ==> geq ==> eq ==> eq ==> iff) pred.

  Proof. split; apply pred_geq_ext'; hyp. Qed.

  Lemma pred_empty : forall x s, pred x s empty == empty_rel.

  Proof.
    split; intros a b; unfold pred, empty_rel; intros.
    destruct H. destruct H as [t [t1 t2]]. rewrite empty_o in t1. discr.
    contr.
  Qed.

  Lemma pred_succ_prod : forall x y g,
    let ysy := XSet.add y (succs y g) in
      let xpx := XSet.add x (preds x g) in
        pred x ysy g U succ x ysy == prod xpx ysy.

  Proof.
    intros x y g. cbv zeta. set (ysy := XSet.add y (succs y g)).
    set (xpx := XSet.add x (preds x g)). split.
    (* << *)
    rewrite union_incl_eq. split; intros a b [h1 h2]; split.
    (* pred *)
    unfold xpx. rewrite add_iff. right. rewrite In_preds_rel. hyp. hyp.
    (* succ *)
    unfold xpx. rewrite add_iff. left. hyp. hyp.
    (* >> *)
    intros a b [h1 h2]. unfold Relation_Operators.union, pred, succ.
    subst xpx ysy. rewrite add_iff in h1, h2. rewrite !add_iff.
    rewrite In_preds_rel in h1. rewrite In_succs_rel in h2.
    rewrite !In_succs_rel, (eq_com a x). tauto.
  Qed.

(***********************************************************************)
(** if x is in sw, then add a pair (w,z) for every z in s *)

  Definition add_pred x s w sw g :=
    if XSet.mem x sw then XSet.fold (add_edge w) s g else g.

  Global Instance add_pred_geq :
    Proper (eq ==> XSet.Equal ==> eq ==> XSet.Equal ==> geq ==> geq) add_pred.

  Proof.
    intros x x' xx' s s' ss' y y' yy' t t' tt' g g' gg'. unfold add_pred.
    rewrite <- xx', <- tt'. clear - ss' yy' gg'. destruct (XSet.mem x t).
    2: hyp. apply S.fold_m_ext; auto. class. apply add_edge_geq. refl.
    apply add_edge_transp_geq. apply add_edge_geq. hyp.
  Qed.

  Lemma rel_map_fold_add_pred : forall x s g g0,
    fold (add_pred x s) g g0 == pred x s g U g0.

  Proof.
    intros x s g g0. pattern g, (fold (add_pred x s) g g0).
    apply fold_rec_weak; clear g.
    (* Equal *)
    intros m n g mn h. apply Equal_geq in mn. (*SLOW:rewrite <- mn. hyp.*)
    rewrite h. apply union_same. apply pred_geq; (refl||hyp). refl.
    (* empty *)
    rewrite pred_empty, R.union_empty_l. refl.
    (* add *)
    intros z t g m n h. unfold add_pred. case_eq (XSet.mem x t); intros.
    (* x in t *)
    rewrite <- mem_iff in H.
    rewrite rel_set_fold_add_edge, h, <- R.union_assoc.
    apply R.union_same. 2: refl.
    rewrite rel_eq; intros a b. unfold succ, pred, Relation_Operators.union.
    split_all.
    rewrite H0. unfold rel. exists t. rewrite add_eq_o. tauto. refl.
    unfold rel. rewrite add_o. destruct (eq_dec z a).
    exists t. tauto.
    destruct H0 as [u [u1 u2]]. exists u. tauto.
    unfold rel in H0. rewrite add_o in H0. destruct (eq_dec z a).
    left. rewrite (eq_com a z). tauto.
    right. tauto.
    (* x notin t *)
    rewrite <- not_mem_iff in H. rewrite h. apply R.union_same. 2: refl.
    rewrite rel_eq; intros a b. unfold pred.
    rewrite not_find_in_iff in n. split_all.
    unfold rel. rewrite add_o. destruct (eq_dec z a). 2: hyp.
    (*SLOW*)rewrite e in n. destruct H0 as [u [u1 u2]]. rewrite n in u1. discr.
    unfold rel in H0. rewrite add_o in H0. destruct (eq_dec z a). 2: hyp.
    destruct H0 as [u [u1 u2]]. inversion u1. subst t. contr.
  Qed.

  (*COQ: can we remove this lemma? *)
  Lemma rel_map_fold_add_pred_ext : forall x s g g0 a b,
    rel (fold (add_pred x s) g g0) a b <-> pred x s g a b \/ rel g0 a b.

  Proof.
    split; intro h. apply rel_map_fold_add_pred in h. hyp.
    apply rel_map_fold_add_pred. hyp.
  Qed.

  Lemma add_pred_transp_geq : forall x s, transpose_neqkey geq (add_pred x s).

  Proof.
    unfold transpose_neqkey. intros x s w w' sw sw' g nww'.
    unfold geq, add_pred. destruct (XSet.mem x sw); destruct (XSet.mem x sw');
    repeat rewrite rel_set_fold_add_edge; try refl.
    rewrite <- !R.union_assoc. apply R.union_same.
    apply union_commut. refl.
  Qed.

(***********************************************************************)
(** given a transitive graph [g], [add x y g] adds edges to g to get
the transitive closure of [id x y U g] *)

  Definition trans_add_edge x y g :=
    (* if (x,y) is already in g, do nothing *)
    if XSet.mem y (succs x g) then g
    (* otherwise, for every pair (w,x) in g,
      add a pair (w,z) for every z in {y} U (succs y g) *)
      else let ysy := XSet.add y (succs y g) in
        fold (add_pred x ysy) g
        (* and, for every z in {y} U (succs y g), add a pair (x,z) *)
          (XSet.fold (add_edge x) ysy g).

  Global Instance trans_add_edge_geq :
    Proper (eq ==> eq ==> geq ==> geq) trans_add_edge.

  Proof.
    intros x x' xx' y y' yy' g g' gg'. unfold geq, trans_add_edge.
    (*SLOW*)rewrite xx', yy', gg'. destruct (XSet.mem y' (succs x' g')).
    hyp. repeat rewrite rel_map_fold_add_pred, rel_set_fold_add_edge.
    apply union_same. (*SLOW:rewrite xx', yy', gg'. refl.*)
    apply pred_geq. hyp. apply XSetFacts.add_m. hyp. apply succs_geq; hyp. hyp.
    apply union_same. rewrite xx', yy', gg'. refl. hyp.
  Qed.

  Lemma rel_trans_add_edge_pred_succ : forall x y g,
    trans_add_edge x y g == if XSet.mem y (succs x g) then g
      else let ysy := XSet.add y (succs y g) in pred x ysy g U (succ x ysy U g).

  Proof.
    intros x y g. unfold trans_add_edge.
    case_eq (XSet.mem y (succs x g)); intros. refl.
    rewrite rel_map_fold_add_pred. apply R.union_same. refl.
    rewrite rel_set_fold_add_edge. refl.
  Qed.

  Lemma rel_trans_add_edge_prod : forall x y g,
    trans_add_edge x y g == if XSet.mem y (succs x g) then g
      else prod (XSet.add x (preds x g)) (XSet.add y (succs y g)) U g.

  Proof.
    intros x y g. rewrite rel_trans_add_edge_pred_succ.
    destruct (XSet.mem y (succs x g)). refl.
    cbv zeta. set (ysy := XSet.add y (succs y g)).
    set (xpx := XSet.add x (preds x g)). rewrite <- R.union_assoc.
    apply R.union_same. apply pred_succ_prod. refl.
  Qed.

  Lemma add_edge_incl_trans : forall x y g,
    add_edge x y g << trans_add_edge x y g.

  Proof.
    intros x y g. rewrite rel_add_edge, rel_trans_add_edge_pred_succ.
    case_eq (XSet.mem y (succs x g)); intros.
    rewrite mem_succs_id. refl. hyp.
    cbv zeta; set (ysy:=XSet.add y (succs y g)).
    rewrite <- R.union_assoc, union_incl_eq. split.
    apply incl_union_r. refl. apply incl_union_l. apply incl_union_r.
    unfold ysy. rewrite succ_add. apply incl_union_l. refl.
  Qed.

  Lemma transitive_trans_add_edge : forall x y g,
    Transitive g -> Transitive (trans_add_edge x y g).

  Proof.
    intros x y g tg. rewrite rel_trans_add_edge_prod.
    destruct (XSet.mem y (succs x g)). hyp.
    intros a b c. unfold Relation_Operators.union, prod.
    rewrite !add_iff. repeat rewrite In_preds_rel, In_succs_rel. split_all.
    (* g a b /\ eq x b /\ eq y c *)
    (*SLOW*)rewrite H0, H1. intuition auto with *.
    (* g a b /\ g b x /\ eq y c *)
    left. split_all. right. apply tg with b; hyp.
    (* g a b /\ eq x b /\ g y c *)
    (*SLOW*)rewrite H0. tauto.
    (* g a b /\ g b x /\ g y c *)
    left. split_all. right. apply tg with b; hyp.
    (* g b c /\ eq x a /\ eq y b *)
    (*SLOW*)rewrite H, H1. intuition auto with *.
    (* g b c /\ g a x /\ eq y b *)
    (*SLOW*)rewrite H1. tauto.
    (* g b c /\ eq x a /\ g y b *)
    left. split_all. right. apply tg with b; hyp.
    (* g b c /\ g a x /\ g y b *)
    left. split_all. right. apply tg with b; hyp.
    (* g a b /\ g b c *)
    right. apply tg with b; hyp.
  Qed.

  Lemma rel_trans_add_edge : forall x y g,
    Transitive g -> trans_add_edge x y g == add_edge x y g!.

  Proof.
    intros x y g tg. cut (Transitive (trans_add_edge x y g)).
    2: apply transitive_trans_add_edge; hyp.
    rewrite rel_add_edge. rewrite !rel_trans_add_edge_prod.
    case_eq (XSet.mem y (succs x g)); intros.
    (* y in sx *)
    rewrite mem_succs_id. rewrite trans_tc. refl. hyp. hyp.
    (* y not in sx *)
    split.
    rewrite union_incl_eq. split. apply prod_add_incl_tc_id.
    trans (g U id x y). apply incl_union_l. refl. apply incl_tc. refl.
    apply tc_min. 2: hyp. rewrite union_commut. apply R.union_incl.
    2: refl. intros a b [xa yb]. split; rewrite add_iff; intuition auto with *.
  Qed.

  Lemma succs_trans_add_edge_id : forall x y g,
    succs x (trans_add_edge x y g)
    [=] if XSet.mem y (succs x g) then succs x g
      else XSet.union (XSet.add y (succs y g)) (succs x g).

  Proof.
    intros x y g. unfold trans_add_edge.
    case_eq (XSet.mem y (succs x g)); intros. refl.
    intro z. rewrite In_succs_rel, rel_map_fold_add_pred_ext,
    rel_set_fold_add_edge_ext. unfold pred, succ. rewrite union_iff.
    rewrite !add_iff, !In_succs_rel. split_all; auto with ordered_type.
  Qed.

  Lemma preds_trans_add_edge_id : forall x y g,
    preds x (trans_add_edge x y g)
    [=] if XSet.mem y (succs x g) then preds x g
      else if XSet.mem x (XSet.add y (succs y g)) then XSet.add x (preds x g)
        else preds x g.

  Proof.
    intros x y g. unfold trans_add_edge.
    case_eq (XSet.mem y (succs x g)); intros. refl.
    set (ysy := XSet.add y (succs y g)). intro z.
    rewrite In_preds_rel, rel_map_fold_add_pred_ext, rel_set_fold_add_edge_ext.
    case_eq (XSet.mem x ysy); intros.
    (* x in ysy *)
    rewrite add_iff, In_preds_rel. unfold ysy in H0.
    rewrite XSetFacts.add_b, orb_eq, eqb_ok, mem_succs_rel in H0.
    unfold ysy, pred, succ. rewrite add_iff, In_succs_rel. split_all; auto with ordered_type.
    (* x not in ysy *)
    unfold ysy, pred, succ. rewrite add_iff, In_succs_rel, In_preds_rel.
    rewrite false_not_true in H, H0. unfold ysy in H0.
    rewrite <- mem_iff, add_iff, In_succs_rel in H0. rewrite mem_succs_rel in H.
    split_all; contr.
  Qed.

(***********************************************************************)
(** building a transitive graph using list iteration *)

  Import ListUtil.

  Definition trans_add_edge' x g y := trans_add_edge x y g.

  Lemma transitive_list_fold_left_trans_add_edge : forall x l g,
    Transitive g -> Transitive (fold_left (trans_add_edge' x) l g).

  Proof.
    intro x. induction l; simpl. auto. intros g tg. apply IHl.
    apply transitive_trans_add_edge. hyp.
  Qed.

(***********************************************************************)
(** In the following, we assume given a type [A] (e.g. rule) and a
function [f] on [A] returning either [None] or some pair [x,l] where
[x] is an element of X.t (e.g. a symbol) and l is a list of elements
of X.t. *)

  Section list.

    Variable (A : Type) (f : A -> option (X.t * list X.t)).

(***********************************************************************)
(** graph obtained by extending [g] with the arcs provided by [f a] *)

    Definition add_edge_list g a :=
      match f a with
        | None => g
        | Some (x,l) => fold_left (add_edge' x) l g
      end.

    Lemma rel_add_edge_list : forall g a, add_edge_list g a ==
      match f a with
        | None => g
        | Some (x,l) => succ_list x l U g
      end.

    Proof.
      intros g a. unfold add_edge_list. destruct (f a) as [[x l]|].
      apply rel_list_fold_left_add_edge. refl.
    Qed.

    Global Instance add_edge_list_gle :
      Proper (gle ==> Logic.eq ==> gle) add_edge_list.

    Proof.
      intros g g' gg' a a' aa'. subst a'. unfold gle.
      do 2 rewrite rel_add_edge_list. destruct (f a) as [[x l]|].
      (*COQ:unfold needed before rewrite*)unfold gle in gg'.
      rewrite gg'. refl. hyp.
    Qed.

    Global Instance add_edge_list_geq :
      Proper (geq ==> Logic.eq ==> geq) add_edge_list.

    Proof.
      intros g g' gg' a a' aa'. subst a'. rewrite gle_antisym in gg'.
      destruct gg' as [gg' g'g]. split.
      (*COQ:unfold needed before rewrite*)unfold gle in gg'.
      (*COQ:rewrite gg' does not work*)apply add_edge_list_gle. hyp. refl.
      (*COQ:rewrite g'g does not work*)apply add_edge_list_gle. hyp. refl.
    Qed.

(***********************************************************************)
(** iteration of [add_edge_list] on a list of elements of [A] *)

    Lemma rel_list_fold_left_add_edge_list : forall l g,
      fold_left add_edge_list l g == fold_left add_edge_list l empty U g.

    Proof.
      induction l; simpl; intro g. rewrite rel_empty, R.union_empty_l. refl.
      rewrite IHl. rewrite (IHl (add_edge_list empty a)).
      do 2 rewrite rel_add_edge_list.
      destruct (f a) as [[x m]|]; rewrite rel_empty, R.union_empty_r.
      rewrite R.union_assoc. refl. refl.
    Qed.

(***********************************************************************)
(** graph obtained by extending [g] with the arcs provided by [f a]
using the function [trans_add_edge] now *)

    Definition trans_add_edge_list g a :=
      match f a with
        | None => g
        | Some (x,l) => fold_left (trans_add_edge' x) l g
      end.

    Lemma transitive_trans_add_edge_list : forall g a,
      Transitive g -> Transitive (trans_add_edge_list g a).

    Proof.
      intros. unfold trans_add_edge_list. destruct (f a).
      destruct p as [x l]. apply transitive_list_fold_left_trans_add_edge. hyp.
      hyp.
    Qed.

    Lemma rel_trans_add_edge_list : forall g a, Transitive g ->
      trans_add_edge_list g a == add_edge_list g a!.

    Proof.
      intros g a tg. unfold trans_add_edge_list, add_edge_list. destruct (f a).
      (* f a = None *)
      2: sym; apply trans_tc; hyp.
      (* f a = Some (x, l) *)
      destruct p as [x l]. revert g tg. induction l; simpl; intros g tg.
      (* nil *)
      sym. apply trans_tc. hyp.
      (* cons *)
      rename a0 into y. rewrite IHl. 2: apply transitive_trans_add_edge; hyp.
      unfold add_edge' at 3, trans_add_edge'.
      rewrite !rel_list_fold_left_add_edge,
        rel_add_edge, rel_trans_add_edge_prod.
      case_eq (XSet.mem y (succs x g)); intros.
      (* y in (succs x g) *)
      rewrite mem_succs_id. 2: hyp. refl.
      (* y not in (succs x g): R! == S! *)
      apply tc_eq.
      (* S << R *)
      apply R.union_incl. refl. rewrite union_commut.
      apply R.union_incl. 2: refl.
      intros u v [xu yv]. unfold prod. rewrite xu, yv, !add_iff. intuition auto with *.
      (* R << S! *)
      rewrite union_incl_eq. split. apply incl_tc. apply incl_union_l. refl.
      rewrite union_incl_eq. split. rewrite prod_add_incl_tc_id.
      apply tc_incl. apply incl_union_r. refl.
      apply incl_tc. apply incl_union_r. apply incl_union_l. refl.
    Qed.

    Lemma transitive_list_fold_left_trans_add_edge_list : forall l g,
      Transitive g -> Transitive (fold_left trans_add_edge_list l g).

    Proof.
      induction l; simpl. auto. intros g tg. apply IHl.
      apply transitive_trans_add_edge_list. hyp.
    Qed.

(***********************************************************************)
(** iteration of [trans_add_edge_list] on a list of elements of [A] *)

    Lemma rel_list_fold_left_trans_add_edge_list : forall l g, Transitive g ->
      fold_left trans_add_edge_list l g == fold_left add_edge_list l g!.

    Proof.
      induction l; simpl. intros. sym. apply trans_tc. hyp.
      intros g tg. rewrite IHl. 2: apply transitive_trans_add_edge_list; hyp.
      rewrite rel_list_fold_left_add_edge_list.
      rewrite rel_list_fold_left_add_edge_list with (g:=add_edge_list g a).
      set (g0 := fold_left add_edge_list l empty).
      rewrite rel_trans_add_edge_list. 2: hyp. apply tc_eq.
      (* S << R *)
      apply R.union_incl. refl. apply incl_tc. refl.
      (* R << S! *)
      rewrite union_incl_eq. split. apply incl_tc. apply incl_union_l. refl.
      apply tc_incl. apply incl_union_r. refl.
    Qed.

(***********************************************************************)
(** transitive closure of a graph defined by a list of elements of [A] *)

    Definition trans_clos_list l := fold_left trans_add_edge_list l empty.

    Lemma transitive_empty : Transitive (rel empty).

    Proof. intros x y z [s [s1 s2]]. rewrite find_empty in s1. discr. Qed.

    Lemma transitive_trans_clos_list : forall l, Transitive (trans_clos_list l).

    Proof.
      intro l. apply transitive_list_fold_left_trans_add_edge_list.
      apply transitive_empty.
    Qed.

    Lemma rel_trans_clos_list : forall l,
      trans_clos_list l == fold_left add_edge_list l empty!.

    Proof.
      intro l. unfold trans_clos_list.
      rewrite rel_list_fold_left_trans_add_edge_list. refl.
      apply transitive_empty.
    Qed.

  End list.

(***********************************************************************)
(** building a transitive graph using set iteration *)

  Lemma transitive_set_fold_trans_add_edge : forall x g,
    Transitive g -> forall s, Transitive (XSet.fold (trans_add_edge x) s g).

  Proof.
    intros x g gtrans s. pattern (XSet.fold (trans_add_edge x) s g).
    apply XSetProps.fold_rec_weak; split_all. apply transitive_trans_add_edge.
    hyp.
  Qed.

End Make.
