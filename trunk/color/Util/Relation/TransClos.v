(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2011-01-18

Computation of the transitive closure of a finite relation.
*)

Require Import FSetUtil FMapUtil OrderedType RelUtil LogicUtil BoolUtil.

Set Implicit Arguments.

Module Make (X : OrderedType).

Module Export S := FSetUtil.Make X.
Module Export M := FMapUtil.Make X.

Import X.

(***********************************************************************)
(** a finite graph on X.t is represented by its successor map: a
finite map from X.t to the type of finite sets on X.t *)

Definition graph := XMap.t XSet.t.

Implicit Type g h : graph.

(***********************************************************************)
(** nodes of a graph *)

(*REMOVE: Definition nodes g :=
  fold (fun x sx s => XSet.add x (XSet.union sx s)) g XSet.empty.*)

(***********************************************************************)
(** relation corresponding to a graph *)

(*COQ: necessary to define rel (hereafter) as a coercion *)
SubClass relation_on_X := relation X.t.

Definition rel g : relation_on_X :=
  fun x y => exists s, find x g = Some s /\ XSet.In y s.

Coercion rel : graph >-> relation_on_X.

Lemma rel_empty : rel (empty XSet.t) == @empty_rel X.t.

Proof.
rewrite rel_eq; intros a b. unfold empty_rel. intuition.
destruct H as [sa [a1 a2]]. rewrite <- find_mapsto_iff in a1.
rewrite empty_mapsto_iff in a1. hyp.
Qed.

(***********************************************************************)
(** equality on maps *)

Definition meq : relation graph := XMap.Equiv XSet.Equal.

Instance meq_Equiv : Equivalence meq.

Instance rel_meq' : Proper (meq ==> eq ==> eq ==> impl) rel.

Proof.
intros g g' gg' x x' xx' y y' yy'. unfold impl, rel. intuition.
destruct H as [sx [hx hy]]. rewrite xx' in hx.
destruct (Equiv_find_Some gg' hx) as [sx']. destruct H.
exists sx'. intuition. rewrite <- yy', <- H0. hyp.
Qed.

Instance rel_meq : Proper (meq ==> eq ==> eq ==> iff) rel.

Proof.
split; apply rel_meq'; hyp||(symmetry;hyp).
Qed.

(***********************************************************************)
(** successors of a node *)

Definition succs x g :=
  match find x g with
    | Some s => s
    | None => XSet.empty
  end.

Instance succs_meq : Proper (eq ==> meq ==> XSet.Equal) succs.

Proof.
intros x y xy g h gh. unfold succs. rewrite xy. clear x xy. case_eq (find y g).
destruct (Equiv_find_Some gh H). destruct H0. rewrite H0. hyp.
erewrite Equiv_find_None with (eq:=XSet.Equal) in H. 2: apply gh.
rewrite H. refl.
Qed.

Lemma In_succs : forall g x y, XSet.In y (succs x g) <-> rel g x y.

Proof.
intros. unfold succs, rel. destruct (find x g); firstorder.
inversion H. hyp. In_elim. discr.
Qed.

Lemma mem_succs : forall g x y, XSet.mem y (succs x g) = true <-> rel g x y.

Proof.
intros. rewrite <- mem_iff. apply In_succs.
Qed.

Lemma succs_add : forall x y s g,
  succs x (add y s g) = if eq_dec y x then s else succs x g.

Proof.
intros x y s g. unfold succs at 1. rewrite add_o. destruct (eq_dec y x); refl.
Qed.

Lemma succs_add_id : forall x s g, succs x (add x s g) = s.

Proof.
intros x s g. unfold succs. rewrite add_eq_o. refl. refl.
Qed.

(***********************************************************************)
(** equality on graphs: two graphs are equivalent if they define the
same relation *)

Definition geq g h := g == h.

Lemma meq_geq : meq << geq.

Proof.
intros g h gh. split; intros x y xy. rewrite <- gh. hyp. rewrite gh. hyp.
Qed.

(***********************************************************************)
(** the representation of graphs is not unique since some node can be
mapped to the empty set, but any map is equivalent to a minimal one
mapping no element to the empty set (lemma min_ok proved hereafter) *)

Definition has_succ (x : X.t) sx := negb (XSet.is_empty sx).

Instance has_succ_m : Proper (eq ==> XSet.Equal ==> Logic.eq) has_succ.

Proof.
intros x x' xx' s s' ss'. unfold has_succ. rewrite ss'. refl.
Qed.

Definition is_min := for_all has_succ.

Instance is_min_m : Proper (Equal ==> @Logic.eq bool) is_min.

Proof.
eapply for_all_m; intuition. proper2 has_succ_m.
Qed.

Instance is_min_meq : Proper (meq ==> @Logic.eq bool) is_min.

Proof.
apply for_all_Equiv; intuition.
Qed.

(***********************************************************************)
(** minimal map *)

Definition add_not_empty x sx m := if XSet.is_empty sx then m else add x sx m.

Instance add_not_empty_m :
  Proper (eq ==> Logic.eq ==> Equal ==> Equal) add_not_empty.

Proof.
intros x x' xx' y y' yy' m m' mm'. subst y'.
unfold add_not_empty. destruct (XSet.is_empty y). hyp. rewrite xx', mm'. refl.
Qed.

Instance add_not_empty_meq :
  Proper (eq ==> XSet.Equal ==> meq ==> meq) add_not_empty.

Proof.
intros x x' xx' s s' ss' m m' mm'. unfold add_not_empty.
rewrite <- ss'. destruct (XSet.is_empty s). hyp. apply add_Equiv; hyp.
Qed.

Lemma add_not_empty_transp : transpose_neqkey Equal add_not_empty.

Proof.
unfold transpose_neqkey. intros k k' e e' m nkk'. unfold add_not_empty.
destruct (XSet.is_empty e); destruct (XSet.is_empty e'); try refl.
apply add_transp. hyp.
Qed.

Lemma add_not_empty_transp_meq : transpose_neqkey meq add_not_empty.

Proof.
eapply transpose_neqkey_m'. apply Equal_Equiv. intuition. refl.
apply add_not_empty_transp.
Qed.

Definition min g : graph := fold add_not_empty g (@empty XSet.t).

Instance min_m : Proper (Equal ==> Equal) min.

Proof.
intros m m' mm'. unfold min. apply fold_Equal; intuition.
Qed.

Instance min_meq : Proper (meq ==> meq) min.

Proof.
intros m m' mm'. unfold min.
apply fold_Equiv with (eq0:=XSet.Equal); intuition.
apply add_not_empty_transp_meq.
Qed.

(***********************************************************************)
(** properties of minimal maps *)

Lemma min_add : forall x s m, ~In x m ->
  Equal (min (add x s m)) (if XSet.is_empty s then min m else add x s (min m)).

Proof.
intros x s m nxm. unfold min at 1. rewrite fold_add; intuition.
2: apply add_not_empty_transp. refl.
Qed.

Lemma min_add_meq : forall x s m, ~In x m ->
  meq (min (add x s m)) (if XSet.is_empty s then min m else add x s (min m)).

Proof.
intros x s m nxm. apply Equal_Equiv. intuition. apply min_add. hyp.
Qed.

Lemma In_min : forall x m, In x (min m) -> In x m.

Proof.
intros x m. pattern m; apply map_induction_bis; clear m.
(* Equal *)
intros m m' mm' h. apply Equal_Equiv with (eq:=XSet.Equal) in mm'.
rewrite <- mm'. hyp. intuition.
(* empty *)
unfold min. rewrite fold_Empty. auto. intuition. apply empty_1.
(* add *)
intros y s m nym h. rewrite min_add. 2: hyp.
destruct (XSet.is_empty s); repeat rewrite add_in_iff; intuition.
Qed.

Lemma find_min_Some : forall x m s,
  find x (min m) = Some s -> find x m = Some s.

Proof.
intros x m. pattern m; apply map_induction_bis; clear m.
(* Equal *)
intros m m' mm' h s. rewrite <- mm'. apply h.
(* empty *)
intro s. unfold min. rewrite fold_Empty; intuition. apply empty_1.
(* add *)
intros y t m nym h s. rewrite min_add. 2: hyp. destruct (XSet.is_empty t);
  repeat rewrite add_o; destruct (eq_dec y x); intuition. ded (h _ H).
absurd (In y m). hyp. rewrite in_find_iff. rewrite e. rewrite H0. discr.
Qed.

Lemma find_Some_min : forall x m s,
  find x m = Some s -> XSet.is_empty s = false -> find x (min m) = Some s.

Proof.
intros x m. pattern m; apply map_induction_bis; clear m.
(* Equal *)
intros m m' mm' h s. rewrite <- mm'. apply h.
(* empty *)
intro s. unfold min. rewrite fold_Empty; intuition. apply empty_1.
(* add *)
intros y t m nym h s. rewrite min_add. 2: hyp. coq_case_eq (XSet.is_empty t);
  repeat rewrite add_o; destruct (eq_dec y x); intuition.
inversion H0. subst t. rewrite H1 in H. discr.
Qed.

Lemma is_min_min : forall m, is_min (min m) = true.

Proof.
apply map_induction_bis.
(* Equal *)
intros m m' mm'. apply Equal_Equiv with (eq:=XSet.Equal) in mm'. 2: intuition.
rewrite mm'. auto.
(* empty *)
unfold is_min, min, for_all.
repeat rewrite fold_Empty; intuition; apply empty_1.
(* add *)
intros x s m nxm h. rewrite min_add_meq. 2: hyp. case_eq (XSet.is_empty s).
hyp. unfold is_min. rewrite for_all_add with (eq0:=XSet.Equal); intuition.
rewrite andb_true_iff. intuition. unfold has_succ. rewrite H. refl.
apply nxm. apply In_min. hyp.
Qed.

Lemma min_In : forall x m,
  In x m -> XSet.is_empty (succs x m) = true \/ In x (min m).

Proof.
intros x m. pattern m; apply map_induction_bis; clear m.
(* Equal *)
intros m m' mm' h. apply Equal_Equiv with (eq:=XSet.Equal) in mm'.
2: intuition. rewrite <- mm'. hyp.
(* empty *)
rewrite empty_in_iff. auto.
(* add *)
intros y s m nym h. rewrite min_add. 2: hyp.
coq_case_eq (XSet.is_empty s); rewrite succs_add; repeat rewrite add_in_iff;
  destruct 1; destruct (eq_dec y x); intuition.
Qed.

Lemma min_ok : forall g, min g == g.

Proof.
intro g. split; intros x y [s [h1 h2]].
apply find_min_Some in h1. exists s. intuition.
apply find_Some_min in h1. exists s. intuition.
rewrite false_not_true. intro h. rewrite <- XSetFacts.is_empty_iff in h.
apply (h _ h2).
Qed.

(***********************************************************************)
(** add an edge into a graph *)

Definition raw_add x y g : graph := add x (XSet.add y (succs x g)) g.

Instance raw_add_meq : Proper (eq ==> eq ==> meq ==> meq) raw_add.

Proof.
intros x x' xx' y y' yy' g g' gg'. unfold raw_add.
apply add_Equiv; auto. rewrite xx', yy', gg'. refl.
Qed.

Definition id x y a b := eq a x /\ eq b y.

Lemma raw_add_rel : forall x y g, raw_add x y g == g U id x y.

Proof.
intros. rewrite rel_eq; intros a b.
unfold raw_add, Relation_Operators.union, id. intuition.
destruct H as [sa [a1 a2]]. rewrite add_o in a1. destruct (eq_dec x a).
inversion a1. subst sa. rewrite add_iff in a2. rewrite In_succs in a2.
rewrite e in a2. intuition.
left. exists sa. intuition.
destruct H0 as [sa [a1 a2]]. unfold rel. rewrite add_o. destruct (eq_dec x a).
exists (XSet.add y (succs x g)). intuition. rewrite add_iff. right.
rewrite e. rewrite In_succs. exists sa. auto.
exists sa. auto.
unfold rel. rewrite add_o. destruct (eq_dec x a).
exists (XSet.add y (succs x g)). intuition. rewrite add_iff. auto.
absurd (eq x a). hyp. symmetry. hyp.
Qed.

Definition succ x s a b := eq a x /\ XSet.In b s.

Instance succ_m' : Proper (eq ==> XSet.Equal ==> @inclusion X.t) succ.

Proof.
intros x x' xx' s s' ss' a b. unfold succ. rewrite xx', ss'. tauto.
Qed.

Instance succ_m : Proper (eq ==> XSet.Equal ==> @same_relation X.t) succ.

Proof.
split; apply succ_m'; hyp||(symmetry;hyp).
Qed.

Lemma succ_empty : forall x, succ x XSet.empty == @empty_rel X.t.

Proof.
intro x. rewrite rel_eq; intros a b. unfold succ, empty_rel. intuition.
In_elim.
Qed.

Lemma fold_raw_add_rel : forall x s g0,
  rel (XSet.fold (raw_add x) s g0) == succ x s U g0.

Proof.
intros x s g0. pattern (XSet.fold (raw_add x) s g0).
apply XSetProps.fold_rec_weak; clear s.
(* [=] *)
intros s t g st i. rewrite <- st. hyp.
(* empty *)
rewrite succ_empty. rewrite union_empty_l. refl.
(* add *)
intros z g s nzs e. rewrite raw_add_rel. rewrite e.
rewrite RelUtil.union_assoc. rewrite RelUtil.union_commut with (R:=rel g0).
rewrite <- RelUtil.union_assoc. apply RelUtil.union_m. 2: refl.
rewrite rel_eq; intros a b. unfold succ, Relation_Operators.union, id.
rewrite add_iff. firstorder.
Qed.

Lemma raw_add_transp : forall x, transpose meq (raw_add x).

Proof.
intros x y z g. unfold raw_add. set (sxg := succs x g).
set (zsxg := XSet.add z sxg). set (ysxg := XSet.add y sxg).
repeat rewrite succs_add_id. repeat (rewrite add_add_eq_Equiv; intuition).
apply add_Equiv; try refl. unfold zsxg, ysxg. apply XSetProps.add_add.
Qed.

(***********************************************************************)
(** given a transitive graph [g], [add x y g] adds edges to g to get
the transitive closure of [g U id x y] *)

(* if x is in sw, then add to g a pair (w,z) for every z in ysy *)
Definition add_pred x ysy w sw g :=
  if XSet.mem x sw then XSet.fold (raw_add w) ysy g else g.

Definition add x y g :=
  (* if (x,y) is already in g, do nothing *)
  if XSet.mem y (succs x g) then g
  (* otherwise, for every pair (w,x) in g,
     add a pair (w,z) for every z in {y} U (succs y g) *)
  else let ysy := XSet.add y (succs y g) in
    fold (add_pred x ysy) g
      (* and, for every z in ysy, add a pair (x,z) *)
      (XSet.fold (raw_add x) ysy g).

Definition pred x ysy g a b := rel g a x /\ XSet.In b ysy.

Instance pred_meq' :
  Proper (eq ==> XSet.Equal ==> meq ==> @inclusion X.t) pred.

Proof.
intros x x' xx' ysy ysy' e g g' gg' a b. unfold pred. rewrite xx', e, gg'.
tauto.
Qed.

Instance pred_meq :
  Proper (eq ==> XSet.Equal ==> meq ==> @same_relation X.t) pred.

Proof.
split; apply pred_meq'; hyp||(symmetry;hyp).
Qed.

Instance add_pred_m :
  Proper (X.eq ==> XSet.Equal ==> X.eq ==> XSet.Equal ==> meq ==> meq) add_pred.

Proof.
intros x x' xx' s s' ss' y y' yy' t t' tt' g g' gg'. unfold add_pred.
rewrite xx', tt'. clear - ss' yy' gg'. destruct (XSet.mem x' t'). 2: hyp.
apply S.fold_m_ext; intuition. apply raw_add_meq. refl. apply raw_add_transp.
apply raw_add_meq. hyp.
Qed.

Lemma add_pred_transp : forall x s, transpose_neqkey meq (add_pred x s).

Proof.
unfold transpose_neqkey. intros x ysy w w' sw sw' g nww'. unfold add_pred.
destruct (XSet.mem x sw); destruct (XSet.mem x sw'). 4: refl.
(* *)
split.
intro y. apply In_Equiv with (eq0:=XSet.Equal). intuition. refl.
gen g. pattern ysy; apply set_induction_bis; clear ysy.
intros s s' ss' e g. rewrite <- ss'. auto.
repeat rewrite fold_empty. refl.
intros z s nzs IH g.
rewrite XSetProps.fold_add; unfold compat_op;
  try apply raw_add_m||apply transpose_raw_add; auto; intuition.
rewrite XSetProps.fold_add; unfold compat_op;
  try apply raw_add_m||apply transpose_raw_add; auto; intuition.
(*COQ: rewrite does not work properly here *)
transitivity (raw_add w' z
  (XSet.fold (raw_add w') s (XSet.fold (raw_add w) (XSet.add z s) g))).
2: symmetry; apply XSetProps.fold_add; unfold compat_op;
  try apply raw_add_m||apply transpose_raw_add; auto; intuition.
(*COQ: rewrite does not work properly here *)
transitivity (raw_add w' z
  (XSet.fold (raw_add w') s (raw_add w z (XSet.fold (raw_add w) s g)))).
2: rewrite XSetProps.fold_add; unfold compat_op;
  try apply raw_add_m||apply transpose_raw_add; auto; intuition.
Abort.

Instance add_meq : Proper (eq ==> eq ==> meq ==> meq) add.

Proof.
intros x x' xx' y y' yy' g g' gg'. unfold add.
rewrite <- xx', <- yy', <- gg'. destruct (XSet.mem y (succs x g)). hyp.
eapply fold_Equiv_ext with (eq0:=XSet.Equal); intuition.
apply add_pred_m; refl. clear.
Abort.

Lemma pred_empty : forall x ysy, pred x ysy (@empty XSet.t) == @empty_rel X.t.

Proof.
split; intros a b; unfold pred, empty_rel; intros.
destruct H. destruct H as [s [a1 a2]]. rewrite empty_o in a1. discr.
contradiction.
Qed.

Lemma fold_add_pred_rel : forall x ysy g g0,
  rel (fold (add_pred x ysy) g g0) == pred x ysy g U g0.

Proof.
intros x ysy g g0. pattern (fold (add_pred x ysy) g g0).
apply fold_rec_weak; clear g.
(* Equal *)
intros m n g mn h. apply Equal_Equiv with (eq:=XSet.Equal) in mn. 2: intuition.
rewrite <- mn. hyp.
(* empty *)
rewrite pred_empty. rewrite union_empty_l. refl.
(* add *)
intros z s g m nzm h. unfold add_pred. case_eq (XSet.mem x s).
(* x in s *)
rewrite <- mem_iff in H. rewrite fold_raw_add_rel. rewrite h.
rewrite <- RelUtil.union_assoc. apply RelUtil.union_m. 2: refl.
rewrite rel_eq; intros a b. unfold succ, pred, Relation_Operators.union.
intuition.
rewrite H0. unfold rel. exists s. rewrite add_eq_o. intuition. refl.
unfold rel. rewrite add_o. destruct (eq_dec z a).
exists s. intuition.
destruct H0 as [t [a1 a2]]. exists t. intuition.
unfold rel in H1. rewrite add_o in H1. destruct (eq_dec z a).
left. intuition.
right. intuition.
(* x notin s *)
rewrite <- not_mem_iff in H. rewrite h. apply RelUtil.union_m. 2: refl.
rewrite rel_eq; intros a b. unfold pred.
intuition; change (~In z m) in nzm; rewrite not_find_in_iff in nzm.
unfold rel. rewrite add_o. destruct (eq_dec z a). 2: hyp.
rewrite e in nzm. destruct H1 as [t [a1 a2]]. rewrite nzm in a1. discr.
unfold rel in H1. rewrite add_o in H1. destruct (eq_dec z a). 2: hyp.
destruct H1 as [t [a1 a2]]. inversion a1. subst s. contradiction.
Qed.
 
Lemma add_rel : forall g, transitive g -> forall x y,
  rel (add x y g) == let ysy := XSet.add y (succs y g) in
    pred x ysy g U (succ x ysy U g).

Proof.
intros g gtrans x y. unfold add. case_eq (XSet.mem y (succs x g)).
(* y in (succs x g) *)
rewrite rel_eq; intros a b. unfold pred, succ, Relation_Operators.union.
repeat rewrite add_iff. repeat rewrite In_succs. rewrite mem_succs in H.
intuition.
rewrite <- H1. apply gtrans with x; hyp.
apply gtrans with x. hyp. apply gtrans with y; hyp.
rewrite H1. rewrite <- H0. hyp.
rewrite H1. apply gtrans with y; hyp.
(* y notin (succs x g) *)
rewrite fold_add_pred_rel. apply RelUtil.union_m. refl.
rewrite fold_raw_add_rel. refl.
Qed.

Lemma trans_add : forall x y g, transitive g -> transitive (add x y g).

Proof.
intros x y g gtrans. rewrite add_rel. 2: hyp. intros a b c.
unfold Relation_Operators.union, pred, succ. repeat rewrite add_iff.
repeat rewrite In_succs. intuition.
left. intuition. right. rewrite <- H0 in H2. hyp.
left. intuition. right. apply gtrans with b; hyp.
left. intuition. apply gtrans with b; hyp.
left. intuition. apply gtrans with b; hyp.
right. left. intuition. right. rewrite <- H in H0. hyp.
right. left. intuition. right. apply gtrans with b; hyp.
left. intuition. rewrite <- H. hyp.
left. intuition. rewrite <- H. hyp.
right. right. apply gtrans with b; hyp.
Qed.

Lemma add_ok : forall x y g, transitive g -> add x y g == raw_add x y g!.

Proof.
intros x y g gtrans. rewrite raw_add_rel. rewrite add_rel. 2: hyp.
change (let ysy := XSet.add y (succs y g) in
  pred x ysy g U (succ x ysy U g) == (g U id x y)!). intro ysy. split.
(* << *)
intros a b. unfold pred, succ, ysy. unfold Relation_Operators.union at -3.
rewrite add_iff. rewrite In_succs. intuition.
apply t_trans with x. apply t_step. intuition. apply t_step.
unfold Relation_Operators.union, id. auto.
apply t_trans with x. apply t_step. intuition.
apply t_trans with y. apply t_step. unfold Relation_Operators.union, id. auto.
apply t_step. intuition.
apply t_step. unfold Relation_Operators.union, id. auto.
apply t_trans with y. apply t_step. unfold Relation_Operators.union, id. auto.
apply t_step. unfold Relation_Operators.union, id. auto.
(* >> *)
apply tc_incl_trans. apply union_incl; split.
trans (succ x ysy U g). apply union_idem_r. apply union_idem_r.
trans (succ x ysy U g). trans (succ x ysy).
intros a b. unfold id, succ. unfold ysy. rewrite add_iff. intuition.
apply union_idem_l. apply union_idem_r.
unfold ysy. rewrite <- add_rel. 2: hyp. apply trans_add. hyp.
Qed.

Lemma trans_empty : transitive (rel (empty XSet.t)).

Proof.
rewrite rel_empty. firstorder.
Qed.

Lemma trans_fold_set : forall x g,
  transitive g -> forall s, transitive (XSet.fold (add x) s g).

Proof.
intros x g gtrans s. pattern (XSet.fold (add x) s g).
apply XSetProps.fold_rec_weak; intros. hyp. hyp. apply trans_add. hyp.
Qed.

Lemma compat_op_add : forall x, compat_op eq Logic.eq (add x).

Proof.
unfold compat_op. intros x y y' yy' g g' gg'. subst.
Abort.

Lemma fold_set_ok : forall x g, transitive g ->
  forall s, XSet.fold (add x) s g == XSet.fold (raw_add x) s g !.

Proof.
intros x g gtrans s. pattern s; apply set_induction_bis; clear s.
intros s s' ss' H.
rewrite XSetOrdProps.fold_equal with (s:=s') (s':=s).
2: apply eq_equivalence.
rewrite XSetOrdProps.fold_equal with (s:=s') (s':=s). 
Abort.

(***********************************************************************)
(** building a transitive graph *)

Require Import List.

Section trans_clos.

  Variable (A : Type) (f : A -> option (X.t * XSet.t)).

  Definition raw_adds g a :=
    match f a with
      | None => g
      | Some (x,s) => XSet.fold (raw_add x) s g
    end.

  Definition adds g a :=
    match f a with
      | None => g
      | Some (x,s) => XSet.fold (add x) s g
    end.

  Lemma trans_adds : forall g a, transitive g -> transitive (adds g a).

  Proof.
  intros. unfold adds. destruct (f a).
  destruct p. apply trans_fold_set. hyp.
  hyp.
  Qed.

  Lemma adds_ok : forall g a, transitive g -> adds g a == raw_adds g a!.

  Proof.
  intros g a gtrans. unfold adds, raw_adds. destruct (f a).
  destruct p as [x s].
  Abort.

  Definition trans_clos l := fold_left adds l (empty XSet.t).

  Lemma trans_trans_clos : forall l, transitive (trans_clos l).

  Proof.
  unfold trans_clos.
  cut (forall l g, transitive g -> transitive (fold_left adds l g)); intro h.
  intro l. apply h. apply trans_empty. rename h into l.
  induction l; intros; simpl. hyp. apply IHl. apply trans_adds. hyp.
  Qed.

End trans_clos.

End Make.
