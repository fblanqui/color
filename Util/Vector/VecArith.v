(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-03-19 (setoid)
- Adam Koprowski, 2007-04-02

Arithmetic over vectors on some semiring.
*)

Set Implicit Arguments.

From Coq Require Import Setoid Morphisms.
From CoLoR Require Import VecUtil RelUtil SemiRing OrdSemiRing NatUtil
  LogicUtil.

Module VectorArith (SRT : SemiRingType).

  Module Export SR := SemiRing SRT.

  Notation vec := (vector A).

  Definition zero_vec := Vconst A0.

  Definition id_vec n i (ip : i < n) := Vreplace (zero_vec n) ip A1.

  Notation "v1 =v v2" := (Vforall2 eqA v1 v2) (at level 70).

  (***********************************************************************)
  (** addition *)

  Definition vector_plus n (v1 v2 : vec n) := Vmap2 Aplus v1 v2.

  Infix "[+]" := vector_plus (at level 50).

  Global Instance vector_plus_mor n :
    Proper (Vforall2 eqA ==> Vforall2 eqA ==> Vforall2 eqA) (@vector_plus n).

  Proof.
    intros u u' uu' v v' vv'. apply Vforall2_intro_nth. intros.
    unfold vector_plus. rewrite !Vnth_map2.
    (*COQ: rewrite H does not work even if Vnth is declared as morphism *)
    apply Aplus_mor; apply Vforall2_elim_nth; hyp.
  Qed.

  Lemma vector_plus_nth n (vl vr : vec n) i (ip : i < n) :
    Vnth (vl [+] vr) ip =A= Vnth vl ip + Vnth vr ip.

  Proof. unfold vector_plus. rewrite Vnth_map2. refl. Qed.

  Lemma vector_plus_comm n (v1 v2 : vec n) : v1 [+] v2 =v v2 [+] v1.

  Proof. apply Vforall2_intro_nth. intros. rewrite !vector_plus_nth. ring. Qed.

  Lemma vector_plus_assoc n (v1 v2 v3 : vec n) :
    v1 [+] (v2 [+] v3) =v v1 [+] v2 [+] v3.

  Proof. apply Vforall2_intro_nth. intros. rewrite !vector_plus_nth. ring. Qed.

  Lemma vector_plus_zero_r n (v : vec n) : v [+] zero_vec n =v v.

  Proof.
    apply Vforall2_intro_nth. intros. rewrite vector_plus_nth.
    set (w := Vnth_const A0 ip). fold zero_vec in w. rewrite w. ring.
  Qed.

  Lemma vector_plus_zero_l n (v : vec n) : zero_vec n [+] v =v v.

  Proof. rewrite vector_plus_comm. apply vector_plus_zero_r. Qed.

  (***********************************************************************)
  (** sum of a vector of vectors *)

  Definition add_vectors n k (v : vector (vec n) k) := 
    Vfold_left_rev (@vector_plus n) (zero_vec n) v.

  Global Instance add_vectors_mor n k :
    Proper (Vforall2 (Vforall2 eqA) ==> Vforall2 eqA) (@add_vectors n k).

  Proof.
    intro x; revert x.
    induction x; simpl; intros. VOtac. refl. revert H. VSntac y.
    unfold add_vectors. simpl. rewrite Vforall2_cons_eq. intuition.
    rewrite H1. apply vector_plus_mor. 2: refl.
    eapply Vfold_left_rev_Vforall2. apply vector_plus_mor. refl. hyp.
  Qed.

  Lemma add_vectors_cons n i (a : vec n) (v : vector (vec n) i) :
    add_vectors (Vcons a v) =v a [+] add_vectors v.

  Proof. unfold add_vectors. simpl. rewrite vector_plus_comm. refl. Qed.

  Lemma add_vectors_zero n k : forall v : vector (vec n) k, 
    Vforall (fun v => v =v zero_vec n) v -> add_vectors v =v zero_vec n.

  Proof.
    induction v. refl. rewrite add_vectors_cons. simpl. intuition.
    rewrite H0, vector_plus_zero_l. hyp.
  Qed.

  Lemma add_vectors_perm n i v v' (vs : vector (vec n) i) :
    add_vectors (Vcons v (Vcons v' vs)) =v add_vectors (Vcons v' (Vcons v vs)).

  Proof.
    rewrite !add_vectors_cons, !vector_plus_assoc, (vector_plus_comm v v').
    refl.
  Qed.

  Lemma add_vectors_nth n k : forall (vs : vector (vec n) k) i (ip : i < n),
    Vnth (add_vectors vs) ip
    =A= Vfold_left_rev Aplus A0 (Vmap (fun v => Vnth v ip) vs).

  Proof.
    induction vs; simpl; intros.
    unfold add_vectors, zero_vec; simpl. rewrite Vnth_const. refl.
    rewrite (Vforall2_elim_nth (R:=eqA)). 2: rewrite add_vectors_cons; refl.
    rewrite vector_plus_nth, IHvs, Aplus_comm. refl.
  Qed.

  Lemma add_vectors_split n : forall k (v vl vr : vector (vec n) k),
    (forall i (ip : i < k), Vnth v ip =v Vnth vl ip [+] Vnth vr ip) ->
    add_vectors v =v add_vectors vl [+] add_vectors vr.

  Proof.
    induction k; intros.
    VOtac. unfold add_vectors. simpl. rewrite vector_plus_zero_r. refl.
    VSntac v. VSntac vl. VSntac vr.
    rewrite !add_vectors_cons, (IHk (Vtail v) (Vtail vl) (Vtail vr)),
      !Vhead_nth, (H 0 (Nat.lt_0_succ k)).
    match goal with
      |- (?A [+] ?B) [+] (?C [+] ?D) =v (?A [+] ?C) [+] (?B [+] ?D) =>
        set (X := A); set (Y := B); set (W := C); set (V := D) end.
    rewrite <- !vector_plus_assoc, (vector_plus_assoc W Y V),
      (vector_plus_comm W Y), !vector_plus_assoc. refl.
    intros. rewrite !Vnth_tail. apply H.
  Qed.

  (***********************************************************************)
  (** point-wise product *)

  Definition dot_product n (l r : vec n) :=
    Vfold_left_rev Aplus A0 (Vmap2 Amult l r).

  Global Instance dot_product_mor n :
    Proper (Vforall2 eqA ==> Vforall2 eqA ==> eqA) (@dot_product n).

  Proof.
    intros u u' uu' v v' vv'; revert u u' uu' v v' vv'.
    induction n; intros. VOtac. refl.
    revert uu' vv'. VSntac u. VSntac v. VSntac u'. VSntac v'. intros H3 H4.
    rewrite Vforall2_cons_eq in H3. rewrite Vforall2_cons_eq in H4. intuition.
    unfold dot_product. simpl. unfold dot_product in IHn.
    rewrite (IHn _ _ H6 _ _ H7), H5, H3. refl.
  Qed.

  Lemma dot_product_zero : forall n (v v' : vec n),
    Vforall (fun el => el =A= A0) v -> dot_product v v' =A= A0.

  Proof.
    induction n; intros.
    VOtac. refl.
    VSntac v. VSntac v'. unfold dot_product. simpl.
    fold (dot_product (Vtail v) (Vtail v')). rewrite IHn.
    assert (Vhead v =A= A0). rewrite Vhead_nth. apply Vforall_nth. hyp.
    rewrite H2. ring.
    apply Vforall_incl with (S n) v. intros.
    apply Vin_tail. hyp. hyp.
  Qed.

  Lemma dot_product_id : forall i n (ip : i < n) v,
    dot_product (id_vec ip) v =A= Vnth v ip.

  Proof.
    induction i. intros. 
    destruct n. lia.

    (* induction base *)
    VSntac v. unfold id_vec, dot_product. simpl.
    change (dot_product (Vconst A0 n) (Vtail v) + A1 * Vhead v =A= Vhead v).
    rewrite dot_product_zero. ring.
    apply Vforall_nth_intro. intros.
    rewrite Vnth_const. refl.

    (* induction step *)
    intros. destruct n. lia.
    VSntac v. unfold dot_product. simpl.
    rewrite <- (IHi n (NatCompat.lt_S_n ip) (Vtail v)).
    ring_simplify. unfold dot_product. refl.
  Qed.

  Lemma dot_product_comm : forall n (u v : vec n),
    dot_product u v =A= dot_product v u.

  Proof.
    induction n. refl. intros. VSntac u. VSntac v. unfold dot_product. simpl.
    unfold dot_product in IHn. rewrite IHn. ring.
  Qed.

  Lemma dot_product_distr_r : forall n (v vl vr : vec n),
    dot_product v (vl [+] vr) =A= dot_product v vl + dot_product v vr.

  Proof.
    induction n; intros.
    VOtac. unfold dot_product. simpl. ring.
    VSntac v. VSntac vl. VSntac vr. unfold dot_product. simpl.
    fold (Vtail vl [+] Vtail vr).
    fold (dot_product (Vtail v) (Vtail vl [+] Vtail vr)).
    rewrite IHn. unfold dot_product. ring.
  Qed.

  Lemma dot_product_distr_l n (v vl vr : vec n) :
    dot_product (vl [+] vr) v =A= dot_product vl v + dot_product vr v.

  Proof.
    rewrite dot_product_comm, dot_product_distr_r, (dot_product_comm v vl),
      (dot_product_comm v vr). refl.
  Qed.

  Lemma dot_product_cons : forall n al ar (vl vr : vec n),
    dot_product (Vcons al vl) (Vcons ar vr) =A= al * ar + dot_product vl vr.

  Proof. intros. unfold dot_product. simpl. ring. Qed.

  Lemma dot_product_distr_mult : forall n a (v v' : vec n),
    a * dot_product v v'
    =A= dot_product (Vbuild (fun i ip => a * Vnth v ip)) v'.

  Proof.
    induction n; intros.
    VOtac. unfold dot_product. simpl. ring.
    rewrite (VSn_eq (Vbuild (fun i (ip : i < S n) => a * Vnth v ip))).
    VSntac v. VSntac v'. rewrite !dot_product_cons. ring_simplify.
    rewrite IHn, Vbuild_tail, Vbuild_head. simpl. ring_simplify.
    match goal with
      |- _ + dot_product ?X _ =A= _ + dot_product ?Y _ => replace X with Y end.
    refl. apply Veq_nth. intros. 
    rewrite !Vbuild_nth, lt_Sn_nS. refl.
  Qed.

  (***********************************************************************)
  (** hints *)

  Global Hint Rewrite vector_plus_zero_l vector_plus_zero_r add_vectors_cons : arith.

End VectorArith.

(***********************************************************************)
(** product ordering on vectors *)

Module OrdVectorArith (OSRT : OrdSemiRingType).

  Module Export VA := VectorArith OSRT.SR.
  Module Export OSR := OrdSemiRing OSRT.

(***********************************************************************)
(** [ge] on vectors *)

  Infix ">=v" := (Vforall2 ge) (at level 70).

  Global Instance vec_ge_mor n :
    Proper (Vforall2 eqA ==> Vforall2 eqA ==> iff) (Vforall2 ge (n:=n)).

  Proof. apply Vforall2_aux_Proper. class. Qed.

  Arguments vec_ge_mor [n x y] _ [x0 y0] _ : rename.

  Lemma vec_plus_ge_compat : forall n (vl vl' vr vr' : vec n), 
    vl >=v vl' -> vr >=v vr' -> vl [+] vr >=v vl' [+] vr'.

  Proof.
    unfold vector_plus. intros. apply Vforall2_intro_nth.
    intros. simpl. rewrite !Vnth_map2.
    apply plus_ge_compat.
    apply Vforall2_elim_nth. hyp.
    apply Vforall2_elim_nth. hyp.
  Qed.

  Lemma vec_plus_ge_compat_r : forall n (vl vl' vr : vec n), 
    vl >=v vl' -> vl [+] vr >=v vl' [+] vr.

  Proof. intros. apply vec_plus_ge_compat. hyp. refl. Qed.

  Lemma vec_plus_ge_compat_l : forall n (vl vr vr' : vec n), 
    vr >=v vr' -> vl [+] vr >=v vl [+] vr'.

  Proof. intros. apply vec_plus_ge_compat. refl. hyp. Qed.

End OrdVectorArith.
