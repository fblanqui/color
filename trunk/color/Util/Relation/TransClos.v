(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2011-01-18

Transitive closure of a finite graph.
*)

Require Import OrderedType RelUtil LogicUtil BoolUtil FGraph.

Set Implicit Arguments.

Module Make (X : OrderedType).

Module Import G := FGraph.Make X.

Implicit Type g h : graph.

Import X.

(***********************************************************************)
(** (a,b) in (pred x s g) if a is a predecessor of x in g and b in s *)

Definition pred x s g a b := rel g a x /\ XSet.In b s.

Instance pred_geq' :
  Proper (eq ==> XSet.Equal ==> geq ==> @inclusion X.t) pred.

Proof.
intros x x' xx' s s' e g g' gg' a b. unfold pred. rewrite xx', e, gg'.
tauto.
Qed.

Instance pred_geq_ext' :
  Proper (eq ==> XSet.Equal ==> geq ==> eq ==> eq ==> impl) pred.

Proof.
intros x x' xx' s s' e g g' gg' a a' aa' b b' bb'. unfold pred.
rewrite xx', e, gg', aa', bb'. refl.
Qed.

Instance pred_geq :
  Proper (eq ==> XSet.Equal ==> geq ==> @same_relation X.t) pred.

Proof.
split; apply pred_geq'; hyp||(symmetry;hyp).
Qed.

Instance pred_geq_ext :
  Proper (eq ==> XSet.Equal ==> geq ==> eq ==> eq ==> iff) pred.

Proof.
split; apply pred_geq_ext'; hyp||(symmetry;hyp).
Qed.

Lemma pred_empty : forall x s, pred x s (@empty XSet.t) == @empty_rel X.t.

Proof.
split; intros a b; unfold pred, empty_rel; intros.
destruct H. destruct H as [t [t1 t2]]. rewrite empty_o in t1. discr.
contradiction.
Qed.

Lemma pred_succ_prod : forall x y g,
  let ysy := XSet.add y (succs y g) in
    let xpx := XSet.add x (preds x g) in
      pred x ysy g U succ x ysy == prod xpx ysy.

Proof.
intros x y g. cbv zeta. set (ysy := XSet.add y (succs y g)).
set (xpx := XSet.add x (preds x g)). split.
(* << *)
rewrite union_incl. split; intros a b [h1 h2]; split.
(* pred *)
unfold xpx. rewrite add_iff. right. rewrite In_preds_rel. hyp. hyp.
(* succ *)
unfold xpx. rewrite add_iff. left. symmetry. hyp. hyp.
(* >> *)
intros a b [h1 h2]. unfold Relation_Operators.union, pred, succ.
subst xpx ysy. rewrite add_iff in h1, h2. repeat rewrite add_iff.
rewrite In_preds_rel in h1. rewrite In_succs_rel in h2.
repeat rewrite In_succs_rel. intuition.
Qed.

(***********************************************************************)
(** if x is in sw, then add a pair (w,z) for every z in s *)

Definition add_pred x s w sw g :=
  if XSet.mem x sw then XSet.fold (add_edge w) s g else g.

Instance add_pred_geq :
  Proper (eq ==> XSet.Equal ==> eq ==> XSet.Equal ==> geq ==> geq) add_pred.

Proof.
intros x x' xx' s s' ss' y y' yy' t t' tt' g g' gg'. unfold add_pred.
rewrite <- xx', <- tt'. clear - ss' yy' gg'. destruct (XSet.mem x t). 2: hyp.
apply S.fold_m_ext; intuition. apply add_edge_geq. refl.
apply add_edge_transp_geq. apply add_edge_geq. hyp.
Qed.

Lemma fold_add_pred_rel : forall x s g g0,
  rel (fold (add_pred x s) g g0) == pred x s g U g0.

Proof.
intros x s g g0. pattern (fold (add_pred x s) g g0).
apply fold_rec_weak; clear g.
(* Equal *)
intros m n g mn h. apply Equal_geq in mn. rewrite <- mn. hyp.
(* empty *)
rewrite pred_empty. rewrite union_empty_l. refl.
(* add *)
intros z t g m n h. unfold add_pred. case_eq (XSet.mem x t).
(* x in t *)
rewrite <- mem_iff in H. rewrite fold_add_edge_rel. rewrite h.
rewrite <- RelUtil.union_assoc. apply RelUtil.union_m. 2: refl.
rewrite rel_eq; intros a b. unfold succ, pred, Relation_Operators.union.
intuition.
rewrite H0. unfold rel. exists t. rewrite add_eq_o. intuition. refl.
unfold rel. rewrite add_o. destruct (eq_dec z a).
exists t. intuition.
destruct H0 as [u [u1 u2]]. exists u. intuition.
unfold rel in H1. rewrite add_o in H1. destruct (eq_dec z a).
left. intuition.
right. intuition.
(* x notin t *)
rewrite <- not_mem_iff in H. rewrite h. apply RelUtil.union_m. 2: refl.
rewrite rel_eq; intros a b. unfold pred.
intuition; change (~In z m) in n; rewrite not_find_in_iff in n.
unfold rel. rewrite add_o. destruct (eq_dec z a). 2: hyp.
rewrite e in n. destruct H1 as [u [u1 u2]]. rewrite n in u1. discr.
unfold rel in H1. rewrite add_o in H1. destruct (eq_dec z a). 2: hyp.
destruct H1 as [u [u1 u2]]. inversion u1. subst t. contradiction.
Qed.

(*COQ: can we remove this lemma? *)
Lemma fold_add_pred_rel_ext : forall x s g g0 a b,
  rel (fold (add_pred x s) g g0) a b <-> pred x s g a b \/ rel g0 a b.

Proof.
split; intro h. apply fold_add_pred_rel in h. hyp.
apply fold_add_pred_rel. hyp.
Qed.

Lemma add_pred_transp_geq : forall x s, transpose_neqkey geq (add_pred x s).

Proof.
unfold transpose_neqkey. intros x s w w' sw sw' g nww'.
unfold geq, add_pred. destruct (XSet.mem x sw); destruct (XSet.mem x sw');
  repeat rewrite fold_add_edge_rel; try refl.
repeat rewrite <- RelUtil.union_assoc. apply RelUtil.union_m.
apply RelUtil.union_commut. refl.
Qed.

(***********************************************************************)
(** given a transitive graph [g], [add x y g] adds edges to g to get
the transitive closure of [g U id x y] *)

Definition trans_add_edge x y g :=
  (* if (x,y) is already in g, do nothing *)
  if XSet.mem y (succs x g) then g
  (* otherwise, for every pair (w,x) in g,
     add a pair (w,z) for every z in {y} U (succs y g) *)
  else let ysy := XSet.add y (succs y g) in
    fold (add_pred x ysy) g
      (* and, for every z in {y} U (succs y g), add a pair (x,z) *)
      (XSet.fold (add_edge x) ysy g).

Instance trans_add_edge_geq : Proper (eq ==> eq ==> geq ==> geq) trans_add_edge.

Proof.
intros x x' xx' y y' yy' g g' gg'. unfold geq, trans_add_edge.
rewrite xx', yy', gg'. destruct (XSet.mem y' (succs x' g')).
hyp. repeat rewrite fold_add_pred_rel, fold_add_edge_rel.
apply RelUtil.union_m. rewrite xx', yy', gg'. refl.
apply RelUtil.union_m. rewrite xx', yy', gg'. refl.
hyp.
Qed.

Lemma trans_add_edge_rel_pred_succ : forall x y g,
  rel (trans_add_edge x y g) ==
  if XSet.mem y (succs x g) then g
    else let ysy := XSet.add y (succs y g) in pred x ysy g U (succ x ysy U g).

Proof.
intros x y g. unfold trans_add_edge. case_eq (XSet.mem y (succs x g)). refl.
rewrite fold_add_pred_rel. apply RelUtil.union_m. refl.
rewrite fold_add_edge_rel. refl.
Qed.

Lemma trans_add_edge_rel_prod : forall x y g, rel (trans_add_edge x y g)
  == if XSet.mem y (succs x g) then g
    else prod (XSet.add x (preds x g)) (XSet.add y (succs y g)) U g.

Proof.
intros x y g. rewrite trans_add_edge_rel_pred_succ.
destruct (XSet.mem y (succs x g)). refl.
cbv zeta. set (ysy := XSet.add y (succs y g)).
set (xpx := XSet.add x (preds x g)). rewrite <- RelUtil.union_assoc.
apply RelUtil.union_m. apply pred_succ_prod. refl.
Qed.

Lemma transitive_trans_add_edge : forall x y g,
  transitive g -> transitive (trans_add_edge x y g).

Proof.
intros x y g tg. rewrite trans_add_edge_rel_prod.
destruct (XSet.mem y (succs x g)). hyp.
intros a b c. unfold Relation_Operators.union, prod.
repeat rewrite add_iff. repeat rewrite In_preds_rel, In_succs_rel. intuition.
rewrite H0, H. intuition.
left. intuition. right. apply tg with b; hyp.
rewrite H. intuition.
left. intuition. right. apply tg with b; hyp.
rewrite H, H0. intuition.
rewrite H. intuition.
left. intuition. right. apply tg with b; hyp.
left. intuition. right. apply tg with b; hyp.
right. apply tg with b; hyp.
Qed.

Lemma trans_add_edge_ok : forall x y g,
  transitive g -> trans_add_edge x y g == add_edge x y g!.

Proof.
intros x y g tg. cut (transitive (trans_add_edge x y g)).
2: apply transitive_trans_add_edge; hyp.
rewrite add_edge_rel. repeat rewrite trans_add_edge_rel_prod.
case_eq (XSet.mem y (succs x g)).
(* y in sx *)
rewrite mem_succs_rel in H. rewrite <- (trans_tc tg) at 1. apply clos_trans_m.
split. apply union_idem_l. rewrite union_incl. split. refl.
intros a b [xa yb]. rewrite xa, yb. hyp.
(* y not in sx *)
split.
(* << *)
intros a b. unfold Relation_Operators.union at -2, prod.
repeat rewrite add_iff. rewrite In_preds_rel, In_succs_rel. intuition.
apply t_step. unfold id. intuition.
apply t_trans with y; apply t_step; unfold id; intuition.
apply t_trans with x; apply t_step; unfold id; intuition.
apply t_trans with x. intuition.
apply t_trans with y; apply t_step; unfold id; intuition.
(* >> *)
apply tc_incl_trans. 2: hyp. rewrite RelUtil.union_commut. apply union_m'.
2: refl. intros a b [xa yb]. split; rewrite add_iff; intuition.
Qed.

Lemma trans_fold_set : forall x g,
  transitive g -> forall s, transitive (XSet.fold (trans_add_edge x) s g).

Proof.
intros x g gtrans s. pattern (XSet.fold (trans_add_edge x) s g).
apply XSetProps.fold_rec_weak; intuition. apply transitive_trans_add_edge. hyp.
Qed.

Lemma succs_trans_add_edge_id : forall x y g,
  succs x (trans_add_edge x y g)
  [=] if XSet.mem y (succs x g) then succs x g
    else XSet.union (XSet.add y (succs y g)) (succs x g).

Proof.
intros x y g. unfold trans_add_edge. case_eq (XSet.mem y (succs x g)). refl.
intro z. rewrite In_succs_rel, fold_add_pred_rel_ext, fold_add_edge_rel_ext.
unfold pred, succ. rewrite union_iff. repeat rewrite add_iff.
repeat rewrite In_succs_rel. intuition.
Qed.

Lemma preds_trans_add_edge_id : forall x y g,
  preds x (trans_add_edge x y g)
  [=] if XSet.mem y (succs x g) then preds x g
    else if XSet.mem x (XSet.add y (succs y g)) then XSet.add x (preds x g)
    else preds x g.

Proof.
intros x y g. unfold trans_add_edge. case_eq (XSet.mem y (succs x g)). refl.
set (ysy := XSet.add y (succs y g)). intro z. rewrite In_preds_rel.
rewrite fold_add_pred_rel_ext. rewrite fold_add_edge_rel_ext.
case_eq (XSet.mem x ysy).
(* x in ysy *)
rewrite add_iff. rewrite In_preds_rel. unfold ysy in H0.
rewrite XSetFacts.add_b, orb_eq, eqb_ok, mem_succs_rel in H0.
unfold ysy, pred, succ. rewrite add_iff, In_succs_rel. intuition.
(* x not in ysy *)
unfold ysy, pred, succ. rewrite add_iff, In_succs_rel, In_preds_rel.
rewrite false_not_true in H, H0. unfold ysy in H0.
rewrite <- mem_iff, add_iff, In_succs_rel in H0. rewrite mem_succs_rel in H.
intuition.
Qed.

End Make.
