(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski and Hans Zantema, 2007-03-22

Termination criterion based on matrix interpretations.

References:
-  J. Endrullis, J. Waldmann and H. Zantema, "Matrix Interpretations for Proving
   Termination of Term Rewriting", Proceedings of the 3rd International Joint
   Conference (IJCAR 2006), 2006.
*)

Set Implicit Arguments.

Require Export Matrix.
Require Import AMonAlg.

Export NMatrix.

(** Interpretation type for matrix interpretations *)
Section FunInt.

  Variables (Sig : Signature) (f : symbol Sig) (dim : nat).

   (* function interpretation : one [dim]x[dim] matrix per argument and
      one vector of dimension [dim] for a constant factor *)
  Record matrixInt (argCnt : nat) : Type := mkMatrixInt {
    const : vector nat dim;
    args : vector (matrix dim dim) argCnt
  }.

  Variable dim_pos : dim > 0.

   (* additional property of interpretation required to ensure strict
      monotonicity of interpretations: upper left corner of every matrix
      needs to be positive *)
  Definition monotone_interpretation n (fi : matrixInt n) := 
    Vforall (fun m => get_elem m dim_pos dim_pos > 0) (args fi).

End FunInt.

(** Module type for proving relative-top termination (in the DP setting) *)
Module Type TMatrixInt_DP.

  Parameter sig : Signature.
  Parameter dim : nat.
  Parameter dim_pos : dim > 0.
  Parameter trsInt : forall f : sig, matrixInt dim (arity f).

End TMatrixInt_DP.

(** Module type for proving relative termination *)
Module Type TMatrixInt.

  Declare Module MI : TMatrixInt_DP.
  Export MI.

  Parameter matrixInt_monotone : forall f : sig, 
    monotone_interpretation dim_pos (trsInt f).

End TMatrixInt.

Ltac matrixInt_monotonicity := intro f; destruct f; compute; auto with arith.

Module MatrixInt_DP (MI : TMatrixInt_DP).

  Export MI.

  Notation vec := (vector nat dim).
  Notation mint := (matrixInt dim).
  Notation mat := (matrix dim dim).

  Definition zero_vec := Vconst 0 dim.

  Definition vector_plus (v1 v2 : vec) := Vmap2 plus v1 v2.
  Infix "[+]" := vector_plus (at level 50).

  Definition add_vectors n (v : vector vec n) := Vfold_left vector_plus zero_vec v.

  Definition add_matrices i m n (v : vector (matrix m n) i) := 
    Vfold_left (@mat_plus m n) (zero_matrix m n) v.

  Definition vec_at0 (v : vec) := Vnth v dim_pos.

  Definition mat_vect_prod (m : mat) (v : vec) := 
    col_matrix_to_vector (mat_mult m (vector_to_col_matrix v)).

  Definition mi_eval n (mi : matrixInt dim n) (v : vector vec n) : vec :=
    add_vectors (Vmap2 mat_vect_prod (args mi) v) [+] const mi.

  (** Monotone algebra instantiated to matrices *)
  Module MonotoneAlgebra <: MonotoneAlgebraType.

    Definition Sig := sig.
    
    Definition I := @mkInterpretation sig vec zero_vec (fun f => mi_eval (trsInt f)).

    Definition succeq (v1 v2 : vec) := Vforall2n ge v1 v2.
    Notation "x >=v y" := (succeq x y) (at level 70).

    Definition succ v1 v2 := v1 >=v v2 /\ vec_at0 v1 > vec_at0 v2.
    Notation "x >v y" := (succ x y) (at level 70).

    Lemma succeq_trans : transitive succeq.

    Proof.
      intros x y z xy yz. unfold succeq. 
      apply Vforall2_intro. intros.
      unfold ge. apply le_trans with (Vnth y ip).
      apply (Vforall2_nth ge). assumption.
      apply (Vforall2_nth ge). assumption.
    Qed.

     (** Monotonicity *)
    Section VecMonotonicity.

      Variables (n : nat) (vl vl' vr : vec).

      Lemma vec_plus_monotone_r : vl >=v vl' -> vl [+] vr >=v vl' [+] vr.

      Proof.
        unfold vector_plus, succeq. intros. apply Vforall2_intro.
        intros. simpl. do 2 rewrite Vmap2_nth.
        unfold ge. apply plus_le_compat_r.
        apply (Vforall2_nth ge). assumption.
      Qed.

      Variable f : matrix dim dim -> vec -> vec.
      Variable f_mon : forall M v1 v2, v1 >=v v2 -> f M v1 >=v f M v2.
      Variables (a b : vec).

      Lemma vec_add_monotone_map2 : forall n1 (v1 : vector vec n1) n2 (v2 : vector vec n2) 
        n (M : vector (matrix dim dim) n) i_j, a >=v b ->
        add_vectors (Vmap2 f M (Vcast (Vapp v1 (Vcons a v2)) i_j)) >=v 
        add_vectors (Vmap2 f M (Vcast (Vapp v1 (Vcons b v2)) i_j)).

      Proof.
        induction v1; intros; simpl.
        destruct n0; try solve [elimtype False; omega].
        unfold add_vectors, succeq. simpl. apply Vforall2_intro. intros.
        unfold vector_plus. do 2 rewrite Vmap2_nth.
        assert (Vnth (f (Vhead M) a) ip >= Vnth (f (Vhead M) b) ip).
        apply (Vforall2_nth ge). apply f_mon. assumption.
        omega.
        destruct n1; try solve [elimtype False; omega].
        unfold add_vectors, succeq. simpl. apply Vforall2_intro. intros.
        unfold vector_plus. do 2 rewrite Vmap2_nth.
        unfold ge. apply plus_le_compat_r.
        match goal with |- ?Hl <= ?Hr => fold (ge Hr Hl) end.
        unfold succeq in IHv1. apply (Vforall2_nth ge).
        unfold add_vectors in IHv1. apply IHv1. assumption.
      Qed.

    End VecMonotonicity.

    Lemma monotone_succeq : monotone I succeq.

    Proof.
      intros f i j i_j vi vj a b ab.
      simpl. unfold mi_eval. apply vec_plus_monotone_r.
      apply vec_add_monotone_map2; trivial.
      intros. unfold succeq. apply Vforall2_intro. intros.
      unfold mat_vect_prod. do 2 rewrite Vnth_col_matrix. apply mat_mult_mon.
      apply mat_ge_refl. intros x y xp yp.
      do 2 rewrite vector_to_col_matrix_spec.
      apply (Vforall2_nth ge). assumption.
    Qed.

    Lemma succ_wf : WF succ.

    Proof.
      apply wf_WF. apply well_founded_lt_compat with (fun v : vec => vec_at0 v).
      intros. destruct H. omega.
    Qed.

    Lemma succ_succeq_compat : absorb succ succeq.

    Proof.
      intros x z xz. destruct xz as [y [xy yz]]. split.
      apply succeq_trans with y. assumption. destruct yz. assumption.
      apply le_gt_trans with (Vnth y dim_pos). unfold vec_at0.
      apply (Vforall2_nth ge). assumption. 
      destruct yz. assumption.
    Qed.

    Lemma succeq_dec : rel_dec succeq.
  
    Proof.
      intros x y. unfold succeq, Vforall2n. apply Vforall2_dec.
      intros m n. destruct (le_lt_dec n m); intuition.
    Defined.

    Lemma succ_dec : rel_dec succ.
  
    Proof.
      intros x y. destruct (succeq_dec x y).
      destruct (le_gt_dec (vec_at0 x) (vec_at0 y)).
      right. intro H. destruct H. intuition.
      left. split; intuition.
      right. intro H. destruct H. intuition.
    Defined.

    (** decidability of order on terms induced by matrix interpretations *)
    Section OrderDecidability.

      Require Export ABterm.

      Notation bterm := (bterm sig).

      (** symbolic computation of term interpretation *)
      Definition mat_matrixInt_prod n M (mi : mint n) : mint n := 
        mkMatrixInt (mat_vect_prod M (const mi)) (Vmap (mat_mult M) (args mi)).

      Definition combine_matrices n k (v : vector (vector mat k) n) :=
        Vbuild (fun i ip => add_matrices (Vmap (fun v => Vnth v ip) v)).

      Fixpoint mi_of_term k (t : bterm k) {struct t} : mint (S k) :=
        match t with
        | BVar i ip => 
            let zero_int := Vconst (zero_matrix dim dim) (S k) in
            let args_int := Vreplace zero_int (le_lt_S ip) (id_matrix dim) in
              mkMatrixInt zero_vec args_int
        | BFun f v => 
            let f_int := trsInt f in
            let args_int := Vmap (@mi_of_term k) v in
            let args_int' := Vmap2 (@mat_matrixInt_prod (S k)) (args f_int) args_int in
            let res_const := add_vectors (Vcons (const f_int) (Vmap (@const dim (S k)) args_int')) in
            let res_args := combine_matrices (Vmap (@args dim (S k)) args_int') in
              mkMatrixInt res_const res_args
        end.

      Require Export ATrs.

      Definition rule_mi r :=
        let mvl := maxvar (lhs r) in
        let mvr := maxvar (rhs r) in
        let m := max mvl mvr in
        let lt := inject_term (le_max_l mvl mvr) in
        let rt := inject_term (le_max_r mvl mvr) in
          (mi_of_term lt, mi_of_term rt).

      (** order characteristic for symbolically computed interpretation and its decidability *)
      Notation mat_ge := (@mat_ge dim dim).
      Notation vec_ge := (@vec_ge dim).

      Definition mint_ge n (l r : mint n) := 
        Vforall2 mat_ge (args l) (args r) /\ vec_ge (const l) (const r).

      Definition mint_gt n (l r : mint n) := 
        mint_ge l r /\ vec_at0 (const l) > vec_at0 (const r).

      Definition term_ord (ord : forall n, relation (mint n)) l r :=
        let (li, ri) := rule_mi (mkRule l r) in
          ord _ li ri.

      Definition term_ge := term_ord mint_ge.
      Definition term_gt := term_ord mint_gt.

      Lemma mint_ge_dec : forall n, rel_dec (@mint_ge n).

      Proof.
        intros n x y. unfold mint_ge.
        destruct (Vforall2_dec (@mat_ge_dec dim dim) (args x) (args y)); intuition.
        destruct (vec_ge_dec (const x) (const y)); intuition.
      Defined.

      Lemma mint_gt_dec : forall n, rel_dec (@mint_gt n).
      
      Proof.
        intros n x y. unfold mint_gt.
        destruct (mint_ge_dec x y); intuition.
        destruct (le_lt_dec (vec_at0 (const x)) (vec_at0 (const y))); intuition.
      Defined.

      Lemma term_ge_dec : rel_dec term_ge.
    
      Proof.
        intros l r. unfold term_ge, term_ord. simpl.
        match goal with
        |- {mint_ge ?l ?r} + {~mint_ge ?l ?r} => destruct (mint_ge_dec l r); auto
        end.
      Defined.

      Lemma term_gt_dec : rel_dec term_gt.
    
      Proof.
        intros l r. unfold term_gt, term_ord. simpl.
        match goal with
        |- {mint_gt ?l ?r} + {~mint_gt ?l ?r} => destruct (mint_gt_dec l r); auto
        end.
      Defined.

      Notation IR_succ := (IR I succ).
      Notation IR_succeq := (IR I succeq).

      Lemma term_gt_incl_succ : term_gt << IR_succ.

      Proof.
      Admitted.

      Lemma term_ge_incl_succeq : term_ge << IR_succeq.

      Proof.
      Admitted.

      Definition succ' := term_gt.
      Definition succ'_sub := term_gt_incl_succ.
      Definition succ'_dec := term_gt_dec.

      Definition succeq' := term_ge.
      Definition succeq'_sub := term_ge_incl_succeq.
      Definition succeq'_dec := term_ge_dec.

    End OrderDecidability.

  End MonotoneAlgebra.

  Export MonotoneAlgebra.
  Module MAR := MonotoneAlgebraResults MonotoneAlgebra.
  Export MAR.

End MatrixInt_DP.

Module MatrixInt (MI : TMatrixInt).

  Export MI.

  Module MI_DP := MatrixInt_DP MI.MI.
  Export MI_DP.

  Module ExtendedMonotoneAlgebra <: ExtendedMonotoneAlgebraType.

    Module MA := MI_DP.MonotoneAlgebra.
    Export MA.

    Section VecMonotonicity.
      
      Variables (n : nat) (vl vl' vr : vec).

      Lemma vec_plus_monotone_r : vec_at0 vl > vec_at0 vl' ->
        vec_at0 (vl [+] vr) > vec_at0 (vl' [+] vr).

      Proof.
        unfold vec_at0, vector_plus. intros.
        simpl. do 2 rewrite Vmap2_nth. 
        unfold gt. apply plus_lt_compat_r. assumption.
      Qed.

      Variable f : matrix dim dim -> vec -> vec.
      Variable f_mon : forall M v1 v2, get_elem M dim_pos dim_pos > 0 ->
        v1 >=v v2 -> vec_at0 v1 > vec_at0 v2 -> vec_at0 (f M v1) > vec_at0 (f M v2).

      Variables (a b : vec).

      Lemma vec_add_monotone_map2 : forall n1 (v1 : vector vec n1) n2 (v2 : vector vec n2) 
        n (M : vector (matrix dim dim) n) i_j,  
        Vforall (fun m => get_elem m dim_pos dim_pos > 0) M ->
        a >=v b -> vec_at0 a > vec_at0 b ->
        vec_at0 (add_vectors (Vmap2 f M (Vcast (Vapp v1 (Vcons a v2)) i_j))) >
        vec_at0 (add_vectors (Vmap2 f M (Vcast (Vapp v1 (Vcons b v2)) i_j))).

      Proof.
        induction v1; intros; simpl.
        destruct n0; [solve [elimtype False; omega] | idtac].
        unfold add_vectors, vec_at0, vector_plus. simpl.
        do 2 rewrite Vmap2_nth. 
        unfold gt. apply plus_lt_compat_l.
        unfold vec_at0 in f_mon. apply f_mon; try assumption.
        apply (Vforall_in (x:=Vhead M) H). apply Vin_head.
        destruct n1; [solve [elimtype False; omega] | idtac].
        unfold add_vectors, vec_at0, vector_plus. simpl.
        do 2 rewrite Vmap2_nth.
        unfold gt. apply plus_lt_compat_r.
        match goal with |- ?Hl < ?Hr => fold (gt Hr Hl) end.
        unfold vec_at0, add_vectors in IHv1. 
        apply IHv1; try assumption.
        apply Vforall_incl with (S n1) M. 
        intros. VSntac M. simpl. auto.
        assumption.
      Qed.

    End VecMonotonicity.

    Lemma monotone_succ : monotone I succ.

    Proof.
      intros f i j i_j vi vj a b ab. split.
      apply monotone_succeq. destruct ab. assumption.
      simpl. unfold mi_eval. apply vec_plus_monotone_r.
      apply vec_add_monotone_map2; try solve [destruct ab; assumption].
      intros. unfold vec_at0. unfold mat_vect_prod. do 2 rewrite Vnth_col_matrix.
      do 2 rewrite mat_mult_spec. apply dot_product_mon_r with 0 dim_pos.
      unfold vec_ge. apply Vforall2_intro. auto.
      unfold vec_ge. apply Vforall2_intro. intros.
      do 2 rewrite get_col_col_matrix. destruct ab.
      apply (Vforall2_nth ge). assumption.
      assumption.
      do 2 rewrite get_col_col_matrix. assumption.
      apply matrixInt_monotone.
    Qed.

  End ExtendedMonotoneAlgebra.

  Export ExtendedMonotoneAlgebra.
  Module EMAR := ExtendedMonotoneAlgebraResults ExtendedMonotoneAlgebra.
  Export EMAR.

End MatrixInt.
