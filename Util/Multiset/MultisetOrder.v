(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2004-09-06
- Solange Coupet-Grimal and William Delobel, 2005-09-19

Theory concerning extension of an relation to multisets is developed
in this file.
*)

Set Implicit Arguments.

From CoLoR Require RelUtil.
From Stdlib Require Import Transitive_Closure Compare_dec Relations Permutation
     Setoid Morphisms Basics Lia.
From CoLoR Require Import RelExtras MultisetTheory ListPermutation MultisetCore
     ListExtras AccUtil LogicUtil.

Declare Scope mord_scope.

Module MultisetOrder (MC: MultisetCore).

  Module Import MSet := MultisetTheory.Multiset MC.

Section OrderDefinition. 

  Variable gtA : relation A.

  Let ltA := transp gtA.
  Let leA x y := ~gtA x y.
  Let gtA_trans := clos_trans gtA.
  Let geA x y := gtA x y \/ eqA x y.
  Hint Unfold ltA leA gtA_trans : sets.

  Notation "X >A Y" := (gtA X Y) (at level 50). 
  Notation "X <A Y" := (ltA X Y) (at level 50). 
  Notation "X <=A Y" := (leA X Y) (at level 50). 
  Notation "X >=A Y" := (geA X Y) (at level 50). 
  Notation "X >*A Y" := (gtA_trans X Y) (at level 50).

(* ------------------------------------------------------------------
          Definition of multiset order
   ------------------------------------------------------------------ *)

  (* MultisetRed expresses the ordering on multisets that can be
     achieved in one step. *)

  Inductive MultisetRedGt (A B: Multiset) : Prop :=
  | MSetRed: forall X a Y, 
       A =mul= X + {{a}} ->
       B =mul= X + Y ->
       (forall y, y in Y -> a >A y) ->
       MultisetRedGt A B.

  (* Then multiset order is just a transitive closure of this
      reduction *)

  Definition MultisetGt := clos_trans MultisetRedGt.

  (* Less than part of an order *) 

  Definition MultisetRedLt := transp MultisetRedGt.
  Definition MultisetLt := transp MultisetGt.

  (* Alternative definition of an order *)

  Inductive MultisetGT (M N: Multiset) : Prop :=
  | MSetGT: forall X Y Z,
     X <>mul empty ->
     M =mul= Z + X ->
     N =mul= Z + Y ->
     (forall y, y in Y -> (exists2 x, x in X & x >A y)) ->
     MultisetGT M N.

  Definition MultisetLT := transp MultisetGT.

  Let AccA := Acc ltA.
  Let AccM := Acc MultisetLt.
  Let AccM_1 := Acc MultisetRedLt.
  Let ACC_M := Acc MultisetLT.

  Let clos_transM_RedGt := clos_trans MultisetRedGt.
  Let clos_transM_RedLt := clos_trans MultisetRedLt.

(* ------------------------------------------------------------------
     Notations
   ------------------------------------------------------------------ *)

  Notation "X >mul Y" := (MultisetGt X Y) (at level 70) : mord_scope.
  Notation "X >MUL Y" := (MultisetGT X Y) (at level 70) : mord_scope.
  Notation "X <mul Y" := (MultisetLt X Y) (at level 70) : mord_scope.
  Notation "X <MUL Y" := (MultisetLT X Y) (at level 70) : mord_scope.
  Notation "X >mul_1 Y" := (MultisetRedGt X Y) (at level 70) : mord_scope.
  Notation "X <mul_1 Y" := (MultisetRedLt X Y) (at level 70) : mord_scope.

  Delimit Scope mord_scope with mord.
  Open Scope mord_scope.

(* ------------------------------------------------------------------
     Some morphisms
   ------------------------------------------------------------------ *)

  Instance MultisetRedGt_morph : Proper (meq ==> meq ==> iff) MultisetRedGt.

  Proof.
    intros x1 x2 H x3 x4 H0. split; intros H1; inversion H1.
    constructor 1 with X a Y; trivial. rewrite <- H; trivial.
    rewrite <- H0; trivial.
    constructor 1 with X a Y; trivial. rewrite H; trivial.
    rewrite H0; trivial.
  Qed.

  Instance AccM_1_morph : Proper (meq ==> iff) AccM_1.

  Proof.
    intros; split; intro H0; inversion H0.
    constructor; intros. apply H1; compute in *; rewrite H; trivial.
    constructor; intros. apply H1; compute in *; rewrite <- H; trivial.
  Qed.

  Instance clos_transM_RedGt_morph :
    Proper (meq ==> meq ==> iff) clos_transM_RedGt.

  Proof.
    intros a b ab c d cd. unfold clos_transM_RedGt.
    refine (RelUtil.tc_prop_iff meq_Equivalence MultisetRedGt_morph a b ab c d cd).
  Qed.

  Instance clos_transM_RedLt_morph :
    Proper (meq ==> meq ==> iff) clos_transM_RedLt.

  Proof.
    intros a b ab c d cd. unfold clos_transM_RedLt.
    refine (RelUtil.tc_prop_iff meq_Equivalence _ a b ab c d cd).
    reduce. unfold MultisetRedLt. unfold transp. rewrite H, H0. reflexivity.
  Qed.

  Instance MultisetGt_morph_equiv : Proper (meq ==> meq ==> iff) MultisetGt.

  Proof.
    intros x1 x2 H x0 x3 H0; split; intro; inversion H1.
    constructor 1; rewrite <- H, <- H0; trivial.
    constructor 2 with y; fold clos_transM_RedGt.
    rewrite <- H; hyp. rewrite <- H0; hyp.
    constructor 1; rewrite H, H0; trivial.
    constructor 2 with y; fold clos_transM_RedGt.
    rewrite H; hyp. rewrite H0; hyp.
  Qed.

  Instance MultisetGT_morph : Proper (meq ==> meq ==> iff) MultisetGT.

  Proof.
    intros xL xR H yL yR H0; split; intro; inversion H1.
    constructor 1 with X Y Z. hyp.
    rewrite <- H. hyp.
    rewrite <- H0. hyp.
    hyp.
    constructor 1 with X Y Z. hyp.
    rewrite H. hyp.
    rewrite H0. hyp.
    hyp.
  Qed.

  Lemma MultisetGt_morph : forall x1 x2 : Multiset, x1 =mul= x2 ->
    forall x3 x4 : Multiset, x3 =mul= x4 -> x1 >mul x3 -> x2 >mul x4.

  Proof.
    intros. apply (proj1 (MultisetGt_morph_equiv H H0)). hyp.
  Qed.

  Instance AccM_morph : Proper (meq ==> iff) AccM.

  Proof.
    intros; split; intro; inversion H0.
    unfold AccM; constructor; intros.
    apply H1; compute; fold clos_transM_RedGt.
    rewrite H; trivial.
    unfold AccM; constructor; intros.
    apply H1; compute; fold clos_transM_RedGt.
    rewrite <- H; trivial.
  Qed.

(* -----------------------------------------------------------------
     Some additional properties needed for some lemmas
   ----------------------------------------------------------------- *)

  Variable gtA_transitive : Transitive gtA.
  Existing Instance gtA_transitive.
  Variable gtA_irreflexive : RelUtil.irreflexive gtA.
  Variable gtA_eqA_compat : Proper (eqA ==> eqA ==> impl) gtA.
  Existing Instance gtA_eqA_compat.

  Hint Resolve gtA_transitive : sets.
  Hint Resolve gtA_irreflexive : sets.
  Hint Extern 3 False => simple eapply (so_not_symmetric (Build_strict_order gtA_transitive gtA_irreflexive)) : sets.

  Lemma gtA_eqA_compat' :
    forall a b, eqA a b -> forall c d, eqA c d -> gtA a c -> gtA b d.

  Proof. apply gtA_eqA_compat. Qed.

  Hint Resolve gtA_eqA_compat' : sets.

  Instance gtA_morph : Proper (eqA ==> eqA ==> iff) gtA.

  Proof.
    intros a b ab c d cd.
    intuition. eapply gtA_eqA_compat. apply ab. apply cd. hyp.
    eapply gtA_eqA_compat. apply Seq_sym. exact eqA_Equivalence. apply ab.
    apply Seq_sym. exact eqA_Equivalence. apply cd. hyp.
  Qed.

  Instance ltA_morph : Proper (eqA ==> eqA ==> iff) ltA.

  Proof. intros a b ab c d cd. unfold ltA, transp. apply gtA_morph; hyp. Qed.

  Instance gtA_trans_morph : Proper (eqA ==> eqA ==> iff) gtA_trans.

  Proof.
    compute. intros a a' a_a' b b' b_b'.
    refine (RelUtil.tc_prop_iff eqA_Equivalence gtA_morph a a' a_a' b b' b_b').
  Qed.

  Instance geA_morph : Proper (eqA ==> eqA ==> iff) geA.
  
  Proof.
    intros; split; intro; destruct H1.
    left; rewrite <- H, <- H0; trivial.
    right; rewrite <- H, <- H0; trivial.
    left; rewrite H, H0; trivial.
    right; rewrite H, H0; trivial.
  Qed.

(* -----------------------------------------------------------------
     Some conclusions following from the fact that ordering holds.
   ----------------------------------------------------------------- *)

Section OrderCharacterization.

  Lemma lt_as_red: same_relation MultisetLt clos_transM_RedLt.

  Proof. exact (RelUtil.tc_transp MultisetRedGt). Qed.

  Lemma empty_min_red: forall M, ~(empty >mul_1 M).

  Proof.
    intros M empty_red_M; inversion empty_red_M.
    apply not_empty with (X + {{a}}) a; auto with multisets.
  Qed.

  (* There is no multiset less than an empty one *) 

  Lemma empty_min: forall M, ~(empty >mul M).

  Proof.
    intros M empty_lt_M; case (RelUtil.tc_step_l empty_lt_M).
    intro M_red_empty; apply empty_min_red with M; trivial.
    intro step; destruct step; apply empty_min_red with x; trivial.
  Qed.

  Lemma mOrd_trans: forall M N P, M >MUL N -> N >MUL P -> M >MUL P.

  Proof.
    destruct 1 as [X1 Y1 Z1 X1_ne M1_def N1_def Ord1].
    destruct 1 as [X2 Y2 Z2 X2_ne N2_def P2_def Ord2].
    constructor 1 with (union X1 (diff X2 Y1)) 
      (union Y2 (diff Y1 X2)) (intersection Z1 Z2).
     (* 'X' not empty *)
    auto with multisets.
     (* left component ok *)
    rewrite M1_def, (union_assoc (Z1#Z2) X1 (X2-Y1)),
      (union_perm (Z1#Z2) X1 (X2-Y1)).
    apply meq_meq_union.
    apply double_split.
    rewrite (union_comm Y1 Z1), (union_comm X2 Z2), <- N1_def, <- N2_def;
      auto with multisets.
     (* right component ok *)
    rewrite P2_def, (union_assoc (Z1#Z2) Y2 (Y1-X2)),
      (union_perm (Z1#Z2) Y2 (Y1-X2)).
    apply meq_meq_union.
    rewrite (intersection_comm Z1 Z2).
    apply double_split.
    rewrite (union_comm X2 Z2), (union_comm Y1 Z1), <- N1_def, <- N2_def;
      auto with multisets.
     (* order of elements ok *)
    intros y y_in_union; case (member_union y_in_union); intro y_in.
     (* *)
    destruct (Ord2 y y_in) as [x x_in_X2 x_gt_y].
    case (member_dec x Y1); intro x_in_Y1.
        (* *)
    destruct (Ord1 x x_in_Y1) as [x' x'_in_X1 x'_gt_x]. 
    exists x'.
    apply member_member_union; trivial.
    eauto with sets.
        (* *)
    exists x.
    rewrite (union_comm X1 (X2-Y1)); apply member_member_union.
    unfold member in *; rewrite (diff_mult X2 Y1); lia.
    trivial.
     (* *)
    destruct (Ord1 y).
    eauto with multisets.
    exists x.
    auto with multisets.
    trivial.
  Qed.

  Lemma gtA_comp: forall a, comp_eqA (gtA a).

  Proof. intros a b c bc. apply gtA_morph. refl. hyp. Qed.

  Lemma leA_comp: forall a, comp_eqA (leA a).

  Proof.
    intros a b c bc ab ca. apply ab. eapply gtA_morph. refl. apply bc. hyp.
  Qed.

(* Begin addition by Solange Coupet-Grimal and William Delobel *)

  Lemma acc_mord : forall M, AccM M -> (forall x, x in M -> AccA x).

  Proof.
    intros M acc_M.
    induction acc_M as [M acc_M IHM].
    intros x x_in_M.
    constructor.
    intros y y_less_x.
    apply (IHM (M - {{x}} + {{y}})); auto with multisets.
    constructor.
    apply MSetRed with (X := M - {{x}}) (a := x) (Y := {{y}});
      auto with multisets.
    intros y0 Hy0.
    gen (member_singleton Hy0); clear Hy0; intro Hy0.
    eapply gtA_eqA_compat. refl. sym. apply Hy0. hyp.
  Qed.

  Lemma sub_transp_trans_2_mOrd_trans: forall P,
    (forall p, p in P -> forall x y, x >A p -> y >A x -> y >A p) -> 
    forall M N, MultisetGT M N -> MultisetGT N P -> MultisetGT M P.

  Proof.
    intros P Hsub.
    destruct 1 as [X1 Y1 Z1 X1_ne M1_def N1_def Ord1].
    destruct 1 as [X2 Y2 Z2 X2_ne N2_def P2_def Ord2].
    constructor 1 with (union X1 (diff X2 Y1)) 
      (union Y2 (diff Y1 X2)) (intersection Z1 Z2).
     (* 'X' not empty *)
    auto with multisets.
     (* left component ok *)
    rewrite M1_def, (union_assoc (Z1#Z2) X1 (X2-Y1)),
      (union_perm (Z1#Z2) X1 (X2-Y1)).
    apply meq_meq_union.
    apply double_split.
    rewrite (union_comm Y1 Z1), (union_comm X2 Z2), <- N1_def, <- N2_def;
      auto with multisets.
     (* right component ok *)
    rewrite P2_def, (union_assoc (Z1#Z2) Y2 (Y1-X2)),
      (union_perm (Z1#Z2) Y2 (Y1-X2)).
    apply meq_meq_union.
    rewrite (intersection_comm Z1 Z2).
    apply double_split.
    rewrite (union_comm X2 Z2), (union_comm Y1 Z1), <- N1_def, <- N2_def;
      auto with multisets.
     (* order of elements ok *)
    intros y y_in_union; case (member_union y_in_union); intro y_in.
     (* *)
    destruct (Ord2 y y_in) as [x x_in_X2 x_gt_y].
    case (member_dec x Y1); intro x_in_Y1.
     (* *)
    destruct (Ord1 x x_in_Y1) as [x' x'_in_X1 x'_gt_x]. 
    exists x'.
    apply member_member_union; trivial.
    cut (y in P); [intro y_in_P
                  | rewrite P2_def, (union_comm Z2 Y2); auto with multisets].
    apply (Hsub y y_in_P x x'); trivial.
     (* *)
    exists x.
    rewrite (union_comm X1 (X2-Y1)); apply member_member_union.
    unfold member in *; rewrite (diff_mult X2 Y1); lia.
    trivial.
     (* *)
    destruct (Ord1 y).
    eauto with multisets.
    exists x.
    auto with multisets.
    trivial.
  Qed.

  Lemma partition2 : forall Y X a, 
    (forall y, y in Y -> exists2 x : A, x in (X + {{a}}) & x >A y) ->
    exists Ya, (exists2 Yx : Multiset,
      Y =mul= Ya + Yx & (forall y, y in Ya -> a >A y)
      /\ (forall y, y in Yx -> exists2 x, x in X & x >A y)).

  Proof.
    induction Y as [ | Y] using mset_ind.
    intros; exists empty; exists empty.
    solve_meq.
    split; intros.
    unfold member in H0; rewrite (empty_mult y) in H0; inversion H0.
    unfold member in H0; rewrite (empty_mult y) in H0; inversion H0.
    intros X a'; intros.
    cut (forall y : A, y in Y -> exists2 x : A, x in (X + {{a'}}) & x >A y).
    intro H'.
    elim (IHY X a' H').
    intros Ya HYa.
    elim HYa; clear HYa; intros Yx HY HYx.
    elim HYx; clear HYx; intros HYa HYx.
    cut (a in (Y + {{a}})).
    intro Ha; elim (H a Ha); intros x' Hx' Hx'2.
    elim (member_union Hx'); intro case_x'.    
      (* x' in X : *)
    exists Ya; exists (Yx + {{a}}).
    rewrite HY.
    auto with multisets.
    split.
    hyp.
    intros y Hy.
    elim (member_union Hy); intro case_y.
    apply HYx; trivial.
    exists x'; trivial.
    generalize (member_singleton case_y) Hx'2; intro y_is_a.
    apply gtA_eqA_compat; auto with multisets.
    rewrite y_is_a; auto with multisets.
      (* x' = a' : *)
    exists (Ya + {{a}}); exists Yx.
    rewrite HY.
    solve_meq.
    split.
    intros y Hy.
    elim (member_union Hy); intro case_y.
    apply HYa; trivial.
    gen Hx'2; apply gtA_eqA_compat.
    apply (member_singleton case_x').
    rewrite (member_singleton case_y); auto with multisets.
    hyp.
    rewrite (union_comm Y {{a}}).
    apply member_member_union.
    apply singleton_member.
    intros y HY; apply H.
    apply member_member_union; trivial.
  Qed.
  
(* end of addition *)

  Lemma direct_subset_red : forall M N, M >MUL N -> M >mul N.
  
  Proof.
    destruct 1.
    generalize dependent Y.
    generalize dependent Z.
    generalize M N.
    generalize dependent X.
    induction X as [ | X] using mset_ind.
    intros; absurd (empty <>mul empty); auto with multisets.
    intros; case (empty_dec X).
     (* X = empty *)
    intro X_empty.
    assert (X + {{a}} =mul= {{a}}); 
      [ rewrite X_empty; eauto with multisets 
      | idtac].
    constructor; constructor 1 with Z a Y.
    solve_meq_ext.
    trivial.
    intros y yY; destruct (H2 y); trivial.
    assert (x in {{a}}); [rewrite <- H3; trivial | idtac].
    assert (x =A= a); [apply member_singleton; trivial | idtac].
    rewrite <- H7; trivial.
     (* X <> empty *)
    intro X_nempty.
    destruct (partition2 H2) as [Yg [Yl Ydec [Yg_ord Yl_ord]]].
    constructor 2 with (Z + Yl + {{a}}).
     (* Z + X + {{a}} >mul Z + Yl + {{a}} *)
    apply IHX with (Z + {{a}}) Yl; 
      try solve [auto with multisets | solve_meq_ext].
     (* Z + Yl + {{a}} >mul Z + Yl + Yg *)
    constructor; constructor 1 with (Z + Yl) a Yg.
    solve_meq_ext.
    solve_meq_ext.
    trivial.
  Qed.

   (* Be careful this equivalence holds only if >gtA is a strict order and 
      if >gtA is decidable *)
  Lemma red_eq_direct : forall M N, M >mul N <-> M >MUL N.
  
  Proof.
    intros; split.
     (* => *)
    induction 1.
    inversion H.
    constructor 1 with {{a}} Y X; solve [ solve_meq_ext 
                                        | eauto with multisets ].
    apply mOrd_trans with y; trivial.
     (* <= *)
    apply direct_subset_red.
  Qed.

  Lemma red_insert: forall M N a, N <mul_1 (M + {{a}}) -> exists M', 
    (N =mul= M' + {{a}} /\ M' <mul_1 M) 
    \/ (N =mul= M + M' /\ forall x, x in M' -> x <A a).

  Proof.
    intros; inversion H.
    case (eqA_dec a a0); intro a_a0.
     (* a = a0, order proved using inserted element *)
    exists Y; right; split.
    rewrite H1; setoid_replace X with M. auto with multisets.
    apply meq_union_meq with {{a}}. rewrite <- a_a0 in H0.
    auto with multisets.
    intros; rewrite a_a0; apply (H2 x); trivial.
     (* a <> a0, order proved with other element that inserted one *)
    assert (a0_a: ~a0 =A= a); auto with sets.
    exists (Y + (M - {{a0}})); left; split.
    rewrite H1; setoid_replace X with (M - {{a0}} + {{a}}).
    2: rewrite (meq_ins_ins (meq_sym H0)); auto with multisets.
    2: try_solve_meq; case (eqA_dec x a); case (eqA_dec x a0); 
      intros; try_solve_meq_ext.
    try_solve_meq.
    constructor 1 with (M - {{a0}}) a0 Y; auto with multisets.
    apply meq_ins_rem; eauto with multisets.
  Qed.

  Lemma noext_big: forall a M N, M >mul N ->
    (forall m, m in M -> a >A m) -> (forall n, n in N -> a >A n).

  Proof.
    intros a m n MN; induction MN; intros.
     (* induction base *)
    inversion H.
    assert (n in (X+Y)); [rewrite <- H3; trivial | idtac].
    case (member_union H5); intro nIn.
    apply H0.
    rewrite H2; unfold insert; auto with multisets.
    assert (a >A a0).
    apply H0.
    rewrite H2; auto with multisets.
    assert (a0 >A n).
    apply H4; auto with multisets.
    eauto with sets.
     (* induction step *)
    apply IHMN2; trivial.
    apply IHMN1; trivial.
  Qed.

  Lemma maxin_not_lt: forall M N, M >mul N ->
    {x:A | x in N & (forall y, y in M -> x >A y)} -> False.

  Proof.
    intros M N MN cond; destruct cond.
    absurd (x >A x); auto with sets.
    apply (noext_big MN g m).
  Qed.

  Lemma mord_ext1_aux: forall a X Y, a in X -> a in Y ->
    (forall y, y in Y -> (exists2 x, x in X & x >A y)) ->
    (forall y, y in (Y - {{a}}) -> (exists2 x, x in (X - {{a}}) & x >A y)).

  Proof.
    intros; destruct (H1 y).
    eauto with multisets.
    case (eqA_dec a x); intro ax.
    destruct (H1 a).
    eauto with multisets.
    exists x0; try apply mem_memrem; eauto with sets.
    exists x; solve [apply mem_memrem; auto with sets | trivial].
  Qed.

  Lemma mord_ext1: forall M N a, M >mul N  <->  M + {{a}} >mul N + {{a}}.

  Proof.
    intros; split; intros.
     (* => *)
    destruct (proj1 (red_eq_direct M N) H).
    rewrite_rl (red_eq_direct (M + {{a}}) (N + {{a}})).
    constructor 1 with X Y (insert a Z); solve [solve_meq_ext; auto].
     (* <= *)
    destruct (proj1 (red_eq_direct (M + {{a}}) (N + {{a}})) H).
    rewrite_rl (red_eq_direct M N).
     (* a in equal part of two multisets *)
    case (member_dec a Z); intro a_Z.
    constructor 1 with X Y (Z - {{a}}); solve 
      [ apply ins_meq_union; trivial 
      | auto].
     (* a in parts that differ *)
    assert (a_in_X: a in X).
    apply member_meq_union with {{a}} M Z; auto with multisets.
    rewrite (union_comm {{a}} M), (union_comm X Z); auto with multisets.
    assert (a_in_Y: a in Y).
    apply member_meq_union with {{a}} N Z; auto with multisets.
    rewrite (union_comm {{a}} N), (union_comm Y Z); auto with multisets.
    constructor 1 with (X - {{a}}) (Y - {{a}}) Z.
    destruct (H3 a); [trivial | idtac].
    apply member_notempty with x.
    apply mem_memrem; eauto with sets.
    rewrite (union_comm Z (X - {{a}})); eauto with multisets.
    rewrite (union_comm Z (Y - {{a}})); eauto with multisets.
    apply mord_ext1_aux; trivial.
  Qed.

  Lemma mord_ext_r: forall M N P, M >mul N  <->  M + P >mul N + P.

  Proof.
    intros; induction P as [ | P] using mset_ind.
     (* induction base *)
    rewrite (union_empty M), (union_empty N); split; auto.
     (* induction step *)
    rewrite (union_assoc M P {{a}}), (union_assoc N P {{a}}).
    split; intro ord.
    rewrite_lr (mord_ext1 (M + P) (N + P) a).
    rewrite_lr IHP; trivial.
    rewrite_rl IHP.
    rewrite_rl (mord_ext1 (M + P) (N + P) a); trivial.
  Qed.

  Lemma mord_ext_l M N P : M >mul N <-> union P M >mul union P N.

  Proof. rewrite (union_comm P M), (union_comm P N). apply mord_ext_r. Qed.

End OrderCharacterization.

Hint Resolve empty_min empty_min_red : multisets.

(* -----------------------------------------------------------------
     Multiset order being strict order
   ----------------------------------------------------------------- *)

Section MultisetOrder_StrictOrder.

  (* Multiset order is irreflexible *)

  Lemma mord_irreflex: forall M, ~ M >mul M.

  Proof.
    unfold not; intros M MgtM.
    assert (M + empty >mul M + empty); 
      [ rewrite (union_empty M); trivial 
      | idtac].
    absurd (empty >mul empty).
    apply empty_min.
    rewrite_rl (mord_ext_l empty empty M); trivial.
  Qed.

  (* ...it's also transitive *)

  Lemma mord_trans: forall X Y Z, X >mul Y -> Y >mul Z -> X >mul Z.

  Proof.
    intros X Y Z oXY oYZ.
    compute; constructor 2 with Y; trivial.
  Qed.

  (* Multiset reduction is irreflexible *)

  Lemma mred_irreflex: forall M, ~M >mul_1 M.

  Proof.
    unfold not; intros.
    absurd (M >mul M); [apply mord_irreflex | constructor; trivial].
  Qed.

   (* ...so it's a strict ordering *)
  Lemma mord_sorder : strict_order MultisetGt.
  
  Proof.
    exact (Build_strict_order mord_trans mord_irreflex).
  Qed.

End MultisetOrder_StrictOrder.

(* -----------------------------------------------------------------
     Well foundedness of multiset order
   ----------------------------------------------------------------- *)

Section MultisetOrder_Wf.

  Lemma mord_wf_1: forall a M0,
    (forall b M, b <A a -> AccM_1 M -> AccM_1 (M + {{b}})) ->
    AccM_1 M0 -> (forall M, M <mul_1 M0 -> AccM_1 (M + {{a}})) ->
    AccM_1 (M0 + {{a}}).

  Proof.
    intros a M0 H1 H2 H3; constructor; intros N N_lt.
    case (red_insert N_lt); intros; repeat destruct H; fold AccM_1; rewrite H.
    apply H3; trivial.
    clear H N_lt H3; induction x as [|M a0] using mset_ind.
    setoid_replace (M0 + empty) with M0; auto with multisets.
    setoid_replace (M0 + (M + {{a0}})) with ((M0 + M) + {{a0}}).
    auto with multisets.
    auto with multisets.
  Qed.

  Lemma mord_wf_2: forall a,
    (forall b M, b <A a -> AccM_1 M -> AccM_1 (M + {{b}})) ->
    forall M, AccM_1 M -> AccM_1 (M + {{a}}).

  Proof.
    unfold AccM_1; intros.
    apply Acc_ind with (P := fun M => AccM_1 (M + {{a}})) 
      (R := MultisetRedLt).
    intros x wfH wfH2; apply mord_wf_1; intros; unfold AccM_1.
    apply H; trivial.
    constructor; trivial.
    apply wfH2; trivial.
    trivial.
  Qed.

  Lemma mord_wf_3:
    forall a, AccA a -> forall M, AccM_1 M -> AccM_1 (M + {{a}}).

  Proof.
    intros a a_wf.
    apply Acc_ind with
      (P := fun a => forall M, AccM_1 M -> AccM_1 (M + {{a}}))
      (R := ltA); trivial.
    intros; apply mord_wf_2; trivial.
    intros; apply H0; trivial.
  Qed.

  Lemma mred_acc : forall M, (forall x, x in M -> AccA x) -> AccM_1 M.

  Proof.
    intros M wf_el.
    induction M using mset_ind.
    constructor; intros y y_lt; absurd (empty >mul_1 y); 
      auto with multisets.
    apply mord_wf_3.
    apply wf_el; auto with multisets.
    apply IHM; intros; apply wf_el; auto with multisets.
  Qed.

  Lemma mred_wf : well_founded ltA -> well_founded MultisetRedLt.

  Proof.
    intro wf_lt; constructor; intros; apply mred_acc.
    intros; exact (wf_lt x).
  Qed.

  Lemma mord_acc : forall M, (forall x, x in M -> AccA x) -> AccM M.

  Proof.
    intros; unfold AccM.
    apply Acc_eq_rel with clos_transM_RedLt.
    split.
    apply (proj2 lt_as_red a b).
    apply (proj1 lt_as_red a b).
    unfold clos_transM_RedLt; apply Transitive_Closure.Acc_clos_trans.
    apply mred_acc; trivial.
  Qed.

  Lemma mord_wf : well_founded ltA -> well_founded MultisetLt. 

  Proof.
    intro wf_lt; constructor; intros; apply mord_acc.
    intros; exact (wf_lt x).
  Qed.


  Lemma mord_acc_mOrd_acc : forall x, AccM x -> ACC_M x.

  Proof.
    intros.
    unfold ACC_M.
    apply Acc_homo with Multiset MultisetLt (fun x y : Multiset => x = y) x;
      trivial.
    intros.
    exists y; trivial.
    unfold MultisetLt, transp; simpl.
    apply direct_subset_red.
    rewrite H0; trivial.
  Qed.

  Lemma mOrd_acc : forall M, (forall x, x in M -> AccA x) -> ACC_M M.
  
  Proof.
    intros.
    apply mord_acc_mOrd_acc.
    apply mord_acc; trivial.
  Qed.

  Lemma mOrd_wf : well_founded ltA -> well_founded MultisetLT. 
  
  Proof.
    intro wf_lt; constructor; intros; apply mOrd_acc.
    intros; exact (wf_lt x).
  Qed.

End MultisetOrder_Wf.

(* -----------------------------------------------------------------
     Additional facts about multiset order
   ----------------------------------------------------------------- *)

Section OrderLemmas.

  Variables M N : Multiset.

  Lemma mord_meq_compat mA mA' mB mB' :
     mA =mul= mA' -> mB =mul= mB' -> mA >mul mB -> mA' >mul mB'.

  Proof. intros. rewrite <- H, <- H0; trivial. Qed.

  Lemma mOrd_elts_ge : M >MUL N ->
   (forall n, n in N -> exists2 m, m in M & m >=A n).

  Proof.
    intros.
    destruct H as [X Y Z Xne MZX NZY Cond].
    assert (nn: n =A= n); auto with sets.
    set (nZY := proj1 (member_morph nn NZY) H0).
    destruct (member_union nZY).
     (* n in equal part *)
    exists n.
    rewrite MZX.
    apply member_member_union; trivial.
    right; trivial.
     (* n in strict part *)
    destruct (Cond n H) as [m mX mn].
    exists m.
    rewrite MZX, (union_comm Z X).
    apply member_member_union; trivial.
    left; trivial.
  Qed.

  Lemma mord_elts_ge: M >mul N -> forall n, n in N ->
    exists2 m, m in M & m >*A n \/ m =A= n.

  Proof.
     (* induction on number of steps needed to show the ordering *)
    induction 1 as [M N M_N | M N P M_N IH_MN N_P IH_NP];
      intros n n_in_N.
     (* order in one step *)
    destruct M_N as [X a Y Mdef Ndef Ya_ord].
    cut (n in N); [rewrite Ndef | trivial].
    intros n_in_XY; destruct (member_union n_in_XY) as [n_in_X | n_in_Y].
    exists n.
    rewrite Mdef; auto with multisets.
    right; auto with sets.
    exists a.
    rewrite Mdef; auto with multisets.
    left; constructor; auto with sets.
     (* order in many steps *)
    destruct (IH_NP n n_in_N) as [np np_in_N np_ge_n].
    destruct (IH_MN np np_in_N) as [mp mp_in_M mp_ge_n].
    exists mp.
    trivial.
    destruct np_ge_n as [np_gt_n | np_n].
    destruct mp_ge_n as [mp_gt_n | mp_n].
    left; constructor 2 with np; trivial.
    left; rewrite mp_n; trivial.
    rewrite <- np_n; trivial.
  Qed.

End OrderLemmas.

Section MOrdPair.

  Variables aL aR bL bR : A.

  Lemma pair_mord_left :
    aL >A aR -> bL >=A bR -> {{ aL, bL }} >mul {{ aR, bR }}.

  Proof.
    intros; destruct H0.
    constructor 2 with {{aR, bL}}.
    constructor; constructor 1 with {{bL}} aL {{aR}}; intros;
      eauto with multisets.
    assert (xAr: y =A= aR); [apply member_singleton | rewrite xAr]; 
      trivial.
    constructor; constructor 1 with {{aR}} bL {{bR}}; intros;
      eauto with multisets.
    assert (xAr: y =A= bR); [apply member_singleton | rewrite xAr]; 
      trivial.
    rewrite H0.
    constructor; constructor 1 with {{bR}} aL {{aR}}; intros;
      eauto with multisets.
    assert (xAr: y =A= aR); [apply member_singleton | rewrite xAr]; 
      trivial.
  Qed.

  Lemma pair_mord_right :
    aL >=A aR -> bL >A bR -> {{ aL, bL }} >mul {{ aR, bR }}.

  Proof.
    intros; destruct H.
    constructor 2 with {{aR, bL}}.
    constructor; constructor 1 with {{bL}} aL {{aR}}; intros;
      eauto with multisets.
    assert (xAr: y =A= aR); [apply member_singleton | rewrite xAr]; 
      trivial.
    constructor; constructor 1 with {{aR}} bL {{bR}}; intros;
      eauto with multisets.
    assert (xAr: y =A= bR); [apply member_singleton | rewrite xAr]; 
      trivial.
    rewrite H.
    constructor; constructor 1 with {{aR}} bL {{bR}}; intros;
      eauto with multisets.
    assert (xAr: y =A= bR); [apply member_singleton | rewrite xAr]; 
      trivial.
  Qed.

  Lemma pair_mOrd : {{ aL, bL }} >MUL {{ aR, bR }} ->
    (aL >=A aR /\ aL >=A bR /\ (aL >A aR \/ aL >A bR)) \/
    (bL >=A aR /\ bL >=A bR /\ (bL >A aR \/ bL >A bR)) \/
    (aL >=A aR /\ bL >=A bR /\ (aL >A aR \/ bL >A bR)) \/
    (bL >=A aR /\ aL >=A bR /\ (bL >A aR \/ aL >A bR)).

  Proof.
    intros.
    inversion H.
    destruct (pair_decomp H1)
      as [[ZaLbL Xempty] | [[Zempty XaLbL] | [[ZaL XbL] | [ZbL XaL]]]].
     (* {aL, bL}, {} *)
    absurd (X =mul= empty); trivial.
     (* {}, {aL, bL} *)
    assert (Y =mul= {{aR, bR}}).
    rewrite H2, Zempty; solve_meq.
    destruct (H3 aR).
    rewrite H4; mset_unfold.
    apply member_union_l; auto with multisets.
    assert (x in {{aL, bL}}).
    rewrite <- XaLbL; trivial.
    destruct (H3 bR).
    rewrite H4; mset_unfold.
    apply member_union_r; auto with multisets.
    assert (x0 in {{aL, bL}}).
    rewrite <- XaLbL; trivial.
    destruct (member_pair H7); destruct (member_pair H10).
    left; repeat split; rewrite <- H11; try solve [left; trivial].
    left; rewrite H11, <- H12; trivial.
    right; right; left; repeat split; 
      try rewrite <- H11; try rewrite <- H12; try solve [left; trivial].
    right; right; right; repeat split;
      try rewrite <- H11; try rewrite <- H12; try solve [left; trivial].
    right; left; repeat split; rewrite <- H11; try solve [left; trivial].
    left; rewrite H11, <- H12; trivial.
     (* {aL}, {bL} *)
    destruct (eqA_dec aL aR).
    assert (Y =mul= {{bR}}).
    setoid_replace Y with (Z + Y - Z).
    rewrite <- (meq_diff_meq Z H2), ZaL, e.
    solve_meq.
    solve_meq.
    destruct (H3 bR).
    rewrite H4; auto with multisets.
    assert (bL >A bR).
    setoid_replace bL with x; trivial.
    apply Seq_sym. exact eqA_Equivalence. apply member_singleton.
    rewrite <- XbL; trivial.
    right; right; left; repeat split.
    right; trivial.
    left; trivial.
    right; trivial.
    destruct (eqA_dec aL bR).
    assert (Y =mul= {{aR}}).
    setoid_replace Y with (Z + Y - Z).
    rewrite <- (meq_diff_meq Z H2), ZaL, e.
    solve_meq.
    solve_meq.
    destruct (H3 aR).
    rewrite H4; auto with multisets.
    assert (bL >A aR).
    setoid_replace bL with x; trivial.
    apply Seq_sym. exact eqA_Equivalence. apply member_singleton.
    rewrite <- XbL; trivial.
    right; right; right; repeat split.
    left; trivial.
    right; trivial.
    left; trivial.
    absurd (mult aL {{aR, bR}} = mult aL (Z + Y)).
    mset_unfold; rewrite !union_mult, !singleton_mult_notin; trivial.
    assert (aL in Z).
    rewrite ZaL; auto with multisets.
    unfold member in H4; lia.
    apply meq_multeq; trivial.
     (* {bL}, {aL} *)    
    destruct (eqA_dec bL aR).
    assert (Y =mul= {{bR}}).
    setoid_replace Y with (Z + Y - Z).
    rewrite <- (meq_diff_meq Z H2), ZbL, e.
    solve_meq.
    solve_meq.
    destruct (H3 bR).
    rewrite H4; auto with multisets.
    assert (aL >A bR).
    setoid_replace aL with x; trivial.
    apply Seq_sym. exact eqA_Equivalence. apply member_singleton.
    rewrite <- XaL; trivial.
    right; right; right; repeat split.
    right; trivial.
    left; trivial.
    right; trivial.
    destruct (eqA_dec bL bR).
    assert (Y =mul= {{aR}}).
    setoid_replace Y with (Z + Y - Z).
    rewrite <- (meq_diff_meq Z H2), ZbL, e.
    solve_meq.
    solve_meq.
    destruct (H3 aR).
    rewrite H4; auto with multisets.
    assert (aL >A aR).
    setoid_replace aL with x; trivial.
    apply Seq_sym. exact eqA_Equivalence. apply member_singleton.
    rewrite <- XaL; trivial.
    right; right; left; repeat split.
    left; trivial.
    right; trivial.
    left; trivial.
    absurd (mult bL {{aR, bR}} = mult bL (Z + Y)).
    mset_unfold; rewrite !union_mult, !singleton_mult_notin; trivial.
    assert (bL in Z).
    rewrite ZbL; auto with multisets.
    unfold member in H4; lia.
    apply meq_multeq; trivial.
  Qed.

  Lemma pair_mOrd_left :
    aL >A aR -> bL >=A bR -> {{ aL, bL }} >MUL {{ aR, bR }}.

  Proof.
    intros.
    destruct H0.
    constructor 1 with {{aL, bL}} {{aR, bR}} empty; try solve_meq.
    intros.
    destruct (member_pair H1).
    exists aL.
    unfold pair; apply member_insert.
    rewrite H2; trivial.
    exists bL.
    unfold pair, insert; auto with multisets.
    rewrite H2; trivial.
    constructor 1 with {{aL}} {{aR}} {{bL}}; try solve_meq.
    rewrite H0; solve_meq.
    intros.
    exists aL.
    auto with multisets.
    rewrite (member_singleton H1); trivial.
  Qed.

  Lemma pair_mOrd_right :
    aL >=A aR -> bL >A bR -> {{ aL, bL }} >MUL {{ aR, bR }}.

  Proof.
    intros.
    destruct H.
    constructor 1 with {{aL, bL}} {{aR, bR}} empty; try solve_meq.
    intros.
    destruct (member_pair H1).
    exists aL.
    unfold pair; apply member_insert.
    rewrite H2; trivial.
    exists bL.
    unfold pair, insert; auto with multisets.
    rewrite H2; trivial.
    constructor 1 with {{bL}} {{bR}} {{aL}}; try solve_meq.
    rewrite H; solve_meq.
    intros.
    exists bL.
    auto with multisets.
    rewrite (member_singleton H1); trivial.
  Qed.

  Lemma pair_mOrd_fromList : 
    aL >=A aR -> bL >=A bR -> aL >A aR \/ bL >A bR ->
    list2multiset (aL :: bL :: nil) >MUL list2multiset (aR :: bR :: nil).

  Proof.
    intros.
    setoid_replace (list2multiset (aL :: bL :: nil)) with {{aL, bL}}.
    setoid_replace (list2multiset (aR :: bR :: nil)) with {{aR, bR}}.
    destruct H1.
    apply pair_mOrd_left; trivial.
    apply pair_mOrd_right; trivial.
    simpl. solve_meq.
    simpl. solve_meq.
  Qed.

End MOrdPair.

Section OrderSim.

  Variables (P : relation A) (eqA_eq : eqA = eq (A:=A)). (*FIXME*)

  Lemma eqA_refl : forall x, x =A= x.

  Proof. rewrite eqA_eq; trivial. Qed.
 
  Instance P_eqA_comp : Proper (eqA ==> eqA ==> impl) P.

  Proof.
    intros a b ab c d cd h. rewrite eqA_eq in *. rewrite <- ab, <- cd; trivial.
  Qed.

  Instance eqA_Equivalence : Equivalence eqA.

  Proof. rewrite eqA_eq; constructor; try_solve. Qed.

  Lemma list_sim_insert : forall M M' a b,
    P a b -> list_sim P (multiset2list M) M' ->
    exists M'', list2multiset M'' =mul= insert b (list2multiset M') /\
      list_sim P (multiset2list (insert a M)) M''.

  Proof.
    intros M M' a b Pab MM'.
    destruct (multiset2list_insert a M) as [a' [p [a'a [Mperm Mp]]]].
    destruct (list_sim_permutation eqA_Equivalence P_eqA_comp MM' Mperm)
      as [M'' [M''sim M'M'']].
    exists (insert_nth M'' p b); split.
    rewrite (list2multiset_insert_nth b M'' p),
      (permutation_meq M'M''); auto with multisets.
    assert (length M'' >= p).
    rewrite <- (list_sim_length M''sim).
    set (h := drop_nth_length (multiset2list (insert a M)) p).
    set (h' := nth_some (multiset2list (insert a M)) p Mp).
    lia.
    apply (@list_sim_insert_nth A A P p (multiset2list (insert a M)) 
      (insert_nth M'' p b) a' b); trivial.
    apply nth_insert_nth; trivial.
    replace a' with a; trivial.    
    rewrite <- eqA_eq; trivial.
    rewrite drop_nth_insert_nth; trivial.
  Qed.

  Lemma list_sim_remove : forall M M' a b,
    P a b -> a in M -> list_sim P (multiset2list (remove a M)) M' ->
    exists M'', list2multiset M'' =mul= insert b (list2multiset M') /\
      list_sim P (multiset2list M) M''.

  Proof.
    intros M M' a b Pab aM MM'_sim.
    destruct (list_sim_insert (remove a M) Pab MM'_sim) as [C [CbM' Csim]].
    destruct (@list_sim_permutation A P eqA eqA_dec eqA_Equivalence P_eqA_comp
     (multiset2list (insert a (remove a M))) C (multiset2list M)) 
     as [C' [C'sim C'perm]]; trivial.
    apply meq_permutation.
    rewrite (double_convertion M), (double_convertion (insert a (remove a M))).
    apply multeq_meq; intro x.
    mset_unfold; unfold member in aM.
    destruct (eqA_dec x a); autorewrite with multisets.
    rewrite !singleton_mult_in; trivial.
    rewrite <- (mult_eqA_compat M e) in aM.
    lia.
    rewrite !singleton_mult_notin; trivial.
    lia.
    exists C'; split; trivial.
    rewrite <- (permutation_meq C'perm); trivial.
  Qed.

  Lemma multiset_split : forall xs xs' A B,
    list_sim P xs xs' -> list2multiset xs =mul= A + B ->
    exists A', exists B',
      list2multiset xs' =mul= list2multiset A' + list2multiset B'
      /\ list_sim P (multiset2list A) A' /\ list_sim P (multiset2list B) B'.

  Proof.
    induction xs.

     (* induction base *)
    intros ? A B H H0; inversion H.
    exists (nil (A:=Eq.A)).
    exists (nil (A:=Eq.A)); split.
    solve_meq.
    split.
    rewrite (multiset2list_meq_empty).
    constructor.
    exact (union_isempty (meq_sym H0)).
    rewrite (multiset2list_meq_empty).
    constructor.
    assert (empty =mul= B + A).
    eauto with multisets.
    exact (union_isempty (meq_sym H1)).

     (* induction step *)
    intros ? A B H H0.
    inversion H.
    rewrite <- H4 in H.
    simpl in H0.
    assert (list2multiset xs + {{a}} =mul= A + B).
    eauto with multisets.
    clear H0.
    assert (a_AB: a in (A + B)).
    rewrite <- H6; auto with multisets.
    destruct (member_union a_AB) as [aA | aB].

     (* a in A *)
    destruct (IHxs ys (remove a A) B H5 (ins_meq_union H6 aA))
      as [A' [B' [ys' [simL simR]]]].
    inversion H.
    destruct (list_sim_remove H9 aA simL) as [C [CA Csim]].
    exists C; exists B'; split; [idtac | split]; trivial.
    simpl; rewrite CA, ys'; solve_meq.

     (* a in B *)
    assert (list2multiset xs =mul= A + (remove a B)).
    rewrite (union_comm A (remove a B)).
    unfold remove; apply ins_meq_union; eauto with multisets.
    destruct (IHxs ys A (remove a B) H5 H0) as [A' [B' [ys' [simL simR]]]].
    inversion H.
    destruct (list_sim_remove H10 aB simR) as [C [CA Csim]].
    exists A'; exists C; split; [idtac | split]; trivial.
    simpl; rewrite CA, ys'; solve_meq.
  Qed.

  Lemma in_mul_sum : forall xs X Y x, list2multiset xs =mul= X + Y ->
    x in X -> exists x', x =A= x' /\ In x' xs.

  Proof.
    intros.
    assert (x_xs: x in (list2multiset xs)).
    rewrite H.
    apply member_member_union; trivial.
    destruct (member_multiset_list xs x_xs).
    exists x0; auto.
  Qed.

  Definition order_compatible xs ys xs' ys' :=
    forall x x' y y', 
      In x xs ->
      In x' xs' ->
      P x x' -> 
      In y ys ->
      In y' ys' ->
      P y y' -> 
      (x >A y -> x' >A y') /\ (x =A= y -> x' =A= y').

  Definition eq_compat xs xs' ys':=
    forall x y y',
      In x xs ->
      In y xs' ->
      In y' ys' ->
      P x y ->
      P x y' ->
      y = y'.

  Lemma mord_list_sim : forall xs ys xs' ys',
    order_compatible xs ys xs' ys' ->
    eq_compat xs xs' ys' ->
    list_sim P xs xs' ->
    list_sim P ys ys' ->
    list2multiset xs  >MUL list2multiset ys ->
    list2multiset xs' >MUL list2multiset ys'.

  Proof.
    intros xs ys xs' ys' ordC eqC xs_xs' ys_ys' xs_ys.
    inversion xs_ys as [X Y Z Xne xs_split ys_split Cond].
    destruct (multiset_split xs_xs' xs_split)
      as [Z' [X' [xs'_split [Z_sim X_sim]]]].
    destruct (multiset_split ys_ys' ys_split)
      as [Z'' [Y' [ys'_split [Z'_sim Y_sim]]]].
    exists (list2multiset X') (list2multiset Y') (list2multiset Z'); trivial.
    cut (multiset2list X <> nil).
    destruct (multiset2list X); try_solve.
    inversion X_sim.
    intros _; apply member_notempty with y.
    simpl; unfold insert.
    apply member_member_union; auto with multisets.
    apply multiset2list_meq_non_empty; trivial.
    assert (uniqCond: forall x y y',
      In x (multiset2list Z) ->
      In y Z' ->
      In y' Z'' ->
      P x y ->
      P x y' ->
      y = y').
    intros.
    apply (eqC x); trivial.
    assert (x in (list2multiset xs)).
    rewrite xs_split.
    apply member_member_union.
    apply in_multiset2list_in_multiset; trivial.
    destruct (member_multiset_list xs H4).
    replace x with x0; trivial.
    sym; rewrite <- eqA_eq; trivial.
    assert (y in (list2multiset xs')).
    rewrite xs'_split.
    apply member_member_union.
    apply member_list_multiset; trivial.
    destruct (member_multiset_list xs' H4).
    replace y with x0; trivial.
    sym; rewrite <- eqA_eq; trivial.
    assert (y' in (list2multiset ys')).
    rewrite ys'_split.
    apply member_member_union.
    apply member_list_multiset; trivial.
    destruct (member_multiset_list ys' H4).
    replace y' with x0; trivial.
    sym; rewrite <- eqA_eq; trivial.
    rewrite (list_sim_unique uniqCond Z_sim Z'_sim); trivial.
    intros y' y'Y'.
    destruct (member_multiset_list Y' y'Y') as [y'' y''Y' y'y''].
    destruct (list_In_nth Y' y'' y''Y') as [p Y'py''].
    destruct (list_sim_nth_rev p Y_sim Y'py'') as [y [Ypy Pyy'']].
    destruct (Cond y).
    apply in_multiset2list_in_multiset.
    apply nth_some_in with p; trivial. 
    destruct (in_multiset_in_multiset2list H) as [x' [xx' x'X]].
    destruct (list_In_nth (multiset2list X) x' x'X) as [q Xqw].
    destruct (list_sim_nth q X_sim Xqw) as [x'' [X'qx'' Pxx'']].
    exists x''.
    apply member_list_multiset.
    apply nth_some_in with q; trivial.
    assert (ord: forall x x' y y' : A,
      In x xs -> In x' xs' -> P x x' ->
      In y ys -> In y' ys' -> P y y' -> 
      x >A y -> x' >A y').
    intros; exact (proj1 (ordC x0 x'0 y0 y'0 H1 H2 H3 H4 H5 H6) H7).
    destruct (@in_mul_sum xs X Z x) as [mx [xmx mx_xs]]; trivial.
    rewrite (union_comm X Z); trivial.
    destruct (@in_mul_sum ys Y Z y) as [my [ymy my_ys]]; trivial.
    rewrite (union_comm Y Z); trivial.
    apply in_multiset2list_in_multiset.
    apply nth_some_in with p; trivial.
    destruct (@in_mul_sum xs' (list2multiset X') (list2multiset Z') x'') 
      as [mx' [x'mx' mx'_xs']]; trivial.
    rewrite (union_comm (list2multiset X') (list2multiset Z')); trivial.
    apply member_list_multiset.
    apply nth_some_in with q; trivial.
    destruct (@in_mul_sum ys' (list2multiset Y') (list2multiset Z'') y'') 
      as [my' [y'my' my'_ys']]; trivial.
    rewrite (union_comm (list2multiset Y') (list2multiset Z'')); trivial.
    apply member_list_multiset.
    apply nth_some_in with p; trivial.
    rewrite y'y'', x'mx', y'my'.
    apply ord with mx my; trivial.
    rewrite eqA_eq in xmx.
    rewrite eqA_eq in x'mx'.
    rewrite eqA_eq in xx'.
    replace mx with x'.
    replace mx' with x''.
    trivial.
    congruence.
    rewrite eqA_eq in ymy.
    rewrite eqA_eq in y'my'.
    replace my with y.
    replace my' with y''.
    trivial.
    rewrite <- xmx, <- ymy; trivial.
  Qed.
 
  Lemma mulOrd_oneElemDiff : forall l m a b, a >A b ->
    list2multiset (l ++ a::m) >MUL list2multiset (l ++ b::m).

  Proof.
    intros.
    constructor 1 with {{a}} {{b}} (list2multiset l + list2multiset m).
    auto with multisets.
    rewrite (list2multiset_app l (a::m)).
    simpl; solve_meq.
    rewrite (list2multiset_app l (b::m)).
    simpl; solve_meq.
    intros.
    exists a; auto with multisets.
    rewrite (member_singleton H0); trivial.
  Qed.

End OrderSim.

Section OrderDec.

  Lemma mult_split: forall M N,
    {MNS: list (Multiset * Multiset * Multiset) |
      forall L R S,
      (In (L, R, S) MNS -> M =mul= S + L /\ N =mul= S + R) /\
      (M =mul= S + L ->
       N =mul= S + R ->
       exists L', exists R', exists S',
         L =mul= L' /\ R =mul= R' /\ S =mul= S' /\ In (L', R', S') MNS
      )
    }.

  Proof.
    intro M.
    apply mset_ind_type with (P := fun M =>
      forall N,
        {MNS: list (Multiset * Multiset * Multiset) |
          forall L R S,
           (In (L, R, S) MNS -> M =mul= S + L /\ N =mul= S + R) /\
           (M =mul= S + L ->
            N =mul= S + R ->
            exists L', exists R', exists S',
              L =mul= L' /\ R =mul= R' /\ S =mul= S' /\ In (L', R', S') MNS
           )
         }).
     (* induction base *)
    intros.
    exists ((empty, N, empty)::nil).
    repeat split; intros.
    inversion H; try_solve.
    inversion H0; auto with multisets.
    inversion H; try_solve.
    inversion H0; eauto with multisets.
    exists empty; exists N; exists empty; repeat split.
    apply union_isempty with S.
    rewrite H; solve_meq.
    rewrite H0.
    setoid_replace S with empty.
    eauto with multisets.
    apply union_isempty with L. auto with multisets.
    eauto with multisets.
    eauto with multisets.
    auto with datatypes.
     (* induction step *)
    intros.
    destruct (X N) as [restN restNok].
    destruct (X (remove a N)) as [restNa restNaok].
    set (joinL := fun MNS: Multiset * Multiset * Multiset => 
      (insert a (fst (fst MNS)), snd (fst MNS), snd MNS)).
    set (joinS := fun MNS: Multiset * Multiset * Multiset => 
      (fst (fst MNS), snd (fst MNS), insert a (snd MNS))).
    destruct (member_dec a N).
     (* a in N *)
    exists (map joinL restN ++ map joinS restNa); intros.
    split; intros.
     (*   - soundness *)
    destruct (@in_app_or _ (map joinL restN) (map joinS restNa) (L, R, S));
      trivial.
    destruct (list_In_nth (map joinL restN) (L, R, S) H0).
    destruct (nth_map_some_rev _ _ _ H1) as [x' [restNx x'LRS]].
    inversion x'LRS.
    destruct x' as [[x'L x'R] x'S]; simpl in * . 
    destruct (proj1 (restNok x'L x'R x'S)).
    apply nth_some_in with x; trivial.
    split; trivial.
    rewrite H2; solve_meq.
    destruct (list_In_nth (map joinS restNa) (L, R, S) H0).
    destruct (nth_map_some_rev _ _ _ H1) as [x' [restNax x'LRS]].
    inversion x'LRS.
    destruct x' as [[x'L x'R] x'S]; simpl in * . 
    destruct (proj1 (restNaok x'L x'R x'S)).
    apply nth_some_in with x; trivial.
    split; trivial.
    rewrite H2; solve_meq.
    unfold insert; rewrite <- (union_assoc {{a}} x'S x'R), <- H6.
    fold (insert a (remove a N)).
    rewrite (meq_insert_remove m); auto with multisets.
     (*   - completeness *)
    destruct (@member_union a S L) as [aS | aL]; trivial.
    rewrite <- H; auto with multisets.
    destruct (proj2 (restNaok L R (remove a S)))
      as [L' [R' [S' [LL' [RR' [SS' LRSN]]]]]]; trivial.
    rewrite (union_comm (remove a S) L).
    apply meq_remove_elem_right; trivial.
    rewrite (union_comm L S); trivial.
    rewrite <- (remove_union R aS), H0; auto with multisets.
    exists L'; exists R'; exists (insert a S'); repeat split; trivial.
    rewrite <- SS', (meq_insert_remove aS); auto with multisets.
    destruct (list_In_nth restNa (L', R', S')); trivial.
    apply in_or_app; right.
    apply nth_some_in with x.
    change (L', R', insert a S') with (joinS (L', R', S')).
    apply nth_map_some; trivial.
    destruct (proj2 (restNok (remove a L) R S))
      as [L' [R' [S' [LL' [RR' [SS' LRSN]]]]]]; trivial.
    apply meq_remove_elem_right; trivial.
    exists (insert a L'); exists R'; exists S'; repeat split; trivial.
    rewrite <- LL', (meq_insert_remove aL); auto with multisets.
    destruct (list_In_nth restN (L', R', S')); trivial.
    apply in_or_app; left.
    apply nth_some_in with x.
    change (insert a L', R', S') with (joinL (L', R', S')).
    apply nth_map_some; trivial.
     (* a not in N *)
    exists (map joinL restN); intros.
    split; intros.
     (*   - soundness *)
    destruct (list_In_nth (map joinL restN) (L, R, S) H).
    destruct (nth_map_some_rev _ _ _ H0) as [x' [restNx x'LRS]].
    inversion x'LRS.
    destruct x' as [[x'L x'R] x'S]; simpl in * . 
    destruct (proj1 (restNok x'L x'R x'S)).
    apply nth_some_in with x; trivial.
    split; trivial.
    rewrite H1; solve_meq.
    assert (aL: a in L).
    destruct (@member_union a S L); trivial.
    rewrite <- H; auto with multisets.
    absurd (a in N); trivial.
    rewrite H0; auto with multisets.
     (*   - completeness *)
    destruct (proj2 (restNok (remove a L) R S))
      as [L' [R' [S' [LL' [RR' [SS' LRSN]]]]]]; trivial.
    apply meq_remove_elem_right; trivial.
    exists (insert a L'); exists R'; exists S'; repeat split; trivial.
    rewrite <- LL', (meq_insert_remove aL); auto with multisets.
    destruct (list_In_nth restN (L', R', S')); trivial.
    apply nth_some_in with x.
    change (insert a L', R', S') with (joinL (L', R', S')).
    apply nth_map_some; trivial.
  Qed.

  Lemma dom_dec : forall M n,
    (forall m, m in M -> {m >A n} + {~m >A n}) ->
    {m: A | m in M /\ m >A n} + {forall m, m in M -> ~m >A n}.

  Proof.
    intro M.
    apply mset_ind_type with (P := fun M =>
      forall n,
        (forall m, m in M -> {m >A n} + {~m >A n}) ->
        {m: A | m in M /\ m >A n} + {forall m, m in M -> ~m >A n}).
    right; intros.
    exfalso; apply not_empty with empty m; auto with multisets.
    intros.
    destruct (X n) as [[m [mM0 mn]] | nm].
    intros; apply X0; auto with multisets.
    left; exists m; auto with multisets.
    destruct (X0 a); auto with multisets.
    left; exists a; auto with multisets.
    right; intros.
    destruct (member_union H).
    apply nm; trivial.
    rewrite (member_singleton H0); trivial.
  Qed.

  Definition Ord L R :=
    L <>mul empty /\
    (forall r, r in R -> (exists2 l, l in L & l >A r)).
    
  Lemma Ord_dec : forall M N, 
    (forall m n, m in M -> n in N -> {m >A n} + {~m >A n}) ->
    {Ord M N} + {~Ord M N}.

  Proof.
    intros M N; gen M; clear M.
    apply mset_ind_type with (P := fun N =>
      forall M,
        (forall m n, m in M -> n in N -> {m >A n} + {~m >A n}) ->
        {Ord M N} + {~Ord M N}); intros.
    destruct (empty_dec M).
    right; intro MN; inversion MN; try_solve.
    left; split; trivial.
    intros; exfalso.
    apply not_empty with empty r; auto with multisets.
    clear N.
    destruct (X M0).
    intros; apply X0; trivial.
    apply member_member_union; trivial.
    destruct (@dom_dec M0 a) as [[m [mM0 mma]] | nm].
    intros; apply X0; trivial.
    auto with multisets.
    inversion o.
    left; split; trivial.
    intros; destruct (member_union H1).
    apply H0; trivial.
    exists m; trivial.
    rewrite (member_singleton H2); trivial.
    right; intro MN; inversion MN.
    destruct (H0 a).
    auto with multisets.
    apply (nm x); trivial.
    right; intro MN; inversion MN.
    apply n; split; trivial; intros.
    apply H0; auto with multisets.
  Qed.

  Lemma mOrd_dec_aux : forall M N,
    (forall m n, m in M -> n in N -> {m >A n} + {~m >A n}) ->
    {M >MUL N} + {~M >MUL N}.

  Proof.
    intros.
    destruct (mult_split M N).
    destruct (@many_one_dec (Multiset*Multiset*Multiset) Multiset
      (fun LRS N => Ord (fst (fst LRS)) (snd (fst LRS)))
      x N).
    intros.
    destruct x0 as [[L R] S].
    apply Ord_dec; simpl; intros.
    destruct (proj1 (a L R S) H).
    apply X.
    rewrite H2; auto with multisets.
    rewrite H3; auto with multisets.
    destruct s as [[[L R] S] [LRSx LRSord]].
    simpl in LRSord; inversion LRSord.
    destruct (proj1 (a L R S) LRSx).
    left; constructor 1 with L R S; trivial.
    right; intro MN; inversion MN.
    destruct (proj2 (a X0 Y Z) H0 H1) as [L [R [S [XL [YR [ZS LRSx]]]]]].
    absurd (Ord L R).
    apply (n (L, R, S)); trivial.
    split; trivial.
    rewrite <- XL; trivial.
    intros.
    destruct (H2 r).
    rewrite YR; trivial.
    exists x0; trivial.
    rewrite <- XL; trivial.
  Qed.

  Variable gtA_dec : forall (a b: A), {a >A b}+{a <=A b}.

  Lemma mOrd_dec : forall M N, {M >MUL N} + {~M >MUL N}.

  Proof.
    intros.
    apply mOrd_dec_aux.
    intros.
    change (~m >A n) with (m <=A n).
    apply gtA_dec.
  Qed.

End OrderDec.

End OrderDefinition.

Section MultisetOrder_on_subrelation.

  Variables R R' : relation A.
  Variable R'sub : inclusion R' R.

  Lemma mord_inclusion : forall M N, MultisetGt R' M N -> MultisetGt R M N.

  Proof.
    intros M N M_N.
    induction M_N.
     (* order in one step *)
    constructor 1.
    inversion H.
    constructor 1 with X a Y; trivial.
    intros b b_Y.
    apply R'sub.
    apply H2; trivial.
     (* order in many steps *)
    constructor 2 with y; trivial.
  Qed.

  Lemma mOrd_inclusion: forall M N, MultisetGT R' M N -> MultisetGT R M N.

  Proof.
    intros M N M_N.
    inversion M_N.
    exists X Y Z; trivial.
    intros.
    destruct (H2 y); trivial.
    exists x; trivial.
    apply R'sub; trivial.
  Qed.

End MultisetOrder_on_subrelation.

End MultisetOrder.
