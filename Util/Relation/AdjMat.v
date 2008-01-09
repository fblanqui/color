(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Leo Ducas, 2007-08-06

AdjMat
*)

(** Describe the morphism between graph restricted to [[0,n-1]]
and the boolean matrix of size n*n *)

Set Implicit Arguments.

Require Export Matrix.
Require Export SemiRing.
Require Export Bool.
Require Import Omega.
Require Export Path.
Require Export Iter.
Require Export SCC.
Require Export ListExtras.

Module BMatrix := Matrix BOrdSemiRingT.
Export BMatrix.

(** Definition of th Graph of a boolean matrix *)
Section GraphofMat.

Variable dim : nat.


Variable M : (matrix dim dim).

Definition mat_unbound M (i j :nat) :=
match le_gt_dec dim i with
  |left _ => false
  |right hi =>
  match le_gt_dec dim j with
    |left _ => false
    |right hj => Vnth (Vnth M hi) hj
    end
  end.

Notation "z [[ x , y ]] " :=(@mat_unbound z x y) (at level 70).

Definition gofmat x y := M[[x,y]] =true.

(** Some usefull lemma *)
Lemma gofmat_true_bounds :forall x y, gofmat x y -> x<dim /\ y < dim.
intros.
split;unfold gofmat in H;unfold mat_unbound in H;
destruct (le_gt_dec dim x);
destruct (le_gt_dec dim y);try discriminate;auto with *.
Qed.

Lemma gofmat_dec x y: {gofmat x y} + {~gofmat x y}.
Proof.
intros;unfold gofmat;apply (bool_dec (M[[x,y]]) true).
Qed.

Lemma gofmat_restricted : is_restricted gofmat (nfirst_list dim).
unfold is_restricted;intros x y.
repeat rewrite nfirst_exact.
intro.
unfold gofmat in H.
unfold mat_unbound in *.
destruct (le_gt_dec dim x);auto.
discriminate.
destruct (le_gt_dec dim y);auto.
discriminate.
Qed.

End GraphofMat.



Notation "z [[ x , y ]] " :=(@mat_unbound _ z x y) (at level 70).

(* Addition of matrix is union of relation *)

Section GofMat_union.
Variable dim : nat.

Variable N M : (matrix dim dim).
Lemma orb_matadd : forall x y : nat, (M <+> N [[x, y]]) = (M [[x, y]]) || (N [[x, y]]).
intros.
unfold mat_unbound.
destruct (le_gt_dec dim x);auto.
destruct (le_gt_dec dim y);auto.
unfold mat_plus.
unfold vec_plus.
mat_get_simpl.
Qed.


Lemma Gmorph_plus :forall x y,@gofmat dim (M <+> N ) x y <->
 ((@gofmat dim M) U (@gofmat dim N)) x y.
Proof.
intros.
assert (gofmat (M <+> N) x y <-> (gofmat M x y \/ gofmat N x y)).
unfold gofmat.
rewrite orb_matadd.
split;intro.
eapply orb_prop;auto.
destruct H;auto with *.
auto.
Qed.
End GofMat_union.

(* Product of matrix is composition of relation *)
Section GofMat_Compose.
Variable dim : nat.

Variable N M : (matrix dim dim).

Lemma existandb_dotprod : forall n (v w : vec n), dot_product v w = true <-> 
exists z, exists hz : z< n,Is_true (andb (Vnth v hz) (Vnth w hz)).
Proof.
induction n;intros;unfold dot_product in *;unfold Vfold_left.
simpl;unfold A0;split;intro.
discriminate.
destruct H;destruct H;auto with *.

assert (v = Vcons (Vhead v) (Vtail v)) as Hv.
apply VSn_eq.
assert (w = Vcons (Vhead w) (Vtail w)) as Hw.
apply VSn_eq.

simpl;unfold Aplus;split;intros.
apply orb_prop in H.
destruct H.
unfold dot_product in IHn.
rewrite IHn in H;repeat destruct H.
exists (S x);exists (lt_n_S x0);clear IHn.

rewrite Hv;rewrite Hw.
rewrite (Vnth_cons  (Vtail v) (Vhead v) (lt_n_S x0) x0).
rewrite (Vnth_cons  (Vtail w) (Vhead w) (lt_n_S x0) x0).
auto.

exists 0;exists (lt_O_Sn n);rewrite Hv;rewrite Hw;repeat rewrite Vnth_head;auto.
unfold Amult in *;auto with *.

repeat destruct H; unfold Amult; apply Is_true_eq_true; apply orb_prop_intro.

destruct x.
right.
rewrite <- (Vnth_head (Vhead v) (Vtail v) x0);auto.
rewrite <-Hv.
rewrite <- (Vnth_head (Vhead w) (Vtail w) x0);auto.
rewrite <-Hw.
auto.

left.
rewrite Hv in H;rewrite Hw in H;generalize (lt_S_n x0);intro.
rewrite (Vnth_cons  (Vtail v) (Vhead v) x0 H0) in H.
rewrite (Vnth_cons  (Vtail w) (Vhead w) x0 H0) in H.
apply Is_true_eq_left; rewrite IHn; exists x; exists H0; trivial.
Qed.


Lemma existandb_matmult : forall x y : nat, (M <*> N [[x, y]]) = true <->
exists z, andb (M[[x,z]]) (N[[z,y]]) =true.
intros.
unfold mat_unbound.
destruct (le_gt_dec dim x).
simpl;intuition.
discriminate.
destruct H;tauto.

destruct (le_gt_dec dim y).
intuition.
discriminate.
destruct H.
destruct (le_gt_dec dim x0).
trivial.
destruct H; symmetry;apply andb_false_r.
unfold mat_mult;rewrite mat_build_nth;unfold get_row;unfold get_col.
split;intros.
rewrite existandb_dotprod in H;repeat destruct H;exists x0.

destruct (le_gt_dec dim x0);auto with *.
apply Is_true_eq_true;unfold gt in g1;generalize (lt_unique x1 g1); intro;subst.
rewrite Vnth_map in H;auto.
destruct H;destruct (le_gt_dec dim x0).
simpl in *;discriminate.
rewrite existandb_dotprod.
exists x0;exists g1;rewrite Vnth_map;auto with *.
Qed.



Lemma Gmorph_mult :forall x y, gofmat (M <*> N ) x y <->
  ((gofmat M) @ (gofmat N)) x y .
Proof.
intros.
unfold gofmat;unfold compose.
rewrite (existandb_matmult).
intuition;destruct H as [z];exists z;auto with *.
Qed.
End GofMat_Compose. 


(* exponentiation of matrix is iteration of relation *)
Section Mat_expp.
Variable dim : nat.

Fixpoint mat_expp_fast (M : matrix dim dim) n :=
 match n with 
  |O => M
  |S i => let N := (@mat_expp_fast M i) in
	(N <+> (id_matrix dim)) <*> N
  end.

End Mat_expp.

Section GofMat_Iter_le.


Variable dim : nat.
Variable M : matrix dim dim.

Lemma mat_id_spec : forall x y, (id_matrix dim)[[x,y]] = true <-> x=y /\ x<dim /\ y<dim.
intros.
split;intro.
unfold mat_unbound in H.
destruct (le_gt_dec dim x).
discriminate.
destruct (le_gt_dec dim y).
discriminate.
unfold id_matrix in H;rewrite Vbuild_nth in H.
unfold id_vec in H;rewrite Vbuild_nth in H.
unfold A0, A1 in *;destruct (eq_nat_dec x y);auto.
discriminate.
destruct H;destruct H0;unfold mat_unbound.
destruct (le_gt_dec dim x);auto with *.
destruct (le_gt_dec dim y);auto with *.
unfold id_matrix;rewrite Vbuild_nth.
unfold id_vec;rewrite Vbuild_nth.
unfold A0, A1 in *;destruct (eq_nat_dec x y);auto.
Qed.

Lemma G_morph_id : forall x y, gofmat (id_matrix dim) x y <-> x=y /\ x<dim /\ y<dim.
Proof.
intros.
unfold gofmat.
apply mat_id_spec.
Qed.

Lemma Gmorph_iter_le_fast : forall n x y, gofmat (mat_expp_fast M n) x y <->
 (iter_le_fast (gofmat M) n) x y.
induction n;intros.
simpl;auto;tauto.
simpl;split;intros.
rewrite Gmorph_mult in H.
unfold compose in H;destruct H as [z];destruct H.
rewrite Gmorph_plus in H. destruct H.
left;unfold compose;exists z;rewrite IHn in *;auto with *.
right;unfold gofmat in H;rewrite mat_id_spec in H.
destruct H;destruct H1;subst; rewrite IHn in H0; auto with *.


rewrite Gmorph_mult.
unfold compose in *;destruct H.
destruct H as [z];exists z;destruct H.
rewrite Gmorph_plus;split;
try left;auto; rewrite IHn;auto.
exists x;split;rewrite <- IHn in H;auto.
generalize (gofmat_true_bounds H);intros.
rewrite Gmorph_plus;right;unfold gofmat;rewrite mat_id_spec;
intuition;auto with *.
Qed.



End GofMat_Iter_le.

(* high enough exponetation is transitive closure *)
Section GofMat_trans_closure.

Variable dim : nat.
Variable M : matrix dim dim.


Lemma Gmorph_clos_trans :forall x y, gofmat (mat_expp_fast M (S (log2 dim))) x y <-> (gofmat M)! x y.
Proof.
split;intros.
rewrite Gmorph_iter_le_fast in H;rewrite  iter_le_fast_exp2_same in H.
rewrite iter_le_spec in H;destruct H as [p];destruct H.
deduce (iter_tc _ _ _ _ H0);trivial.

deduce(eq_dec_midex eq_nat_dec).
deduce (clos_trans_bound_path H0 (@gofmat_restricted dim M) ).
rewrite nfirst_length in H1;unfold inclusion in H1.
deduce (H1 _ _ H); deduce (bound_path_iter_le H2).
rewrite Gmorph_iter_le_fast;rewrite iter_le_fast_spec.
rewrite iter_le_spec in H3.
destruct H3 as [p];exists p. intuition.
deduce (exp2_log2 dim).
omega.
Qed.

End GofMat_trans_closure.

(* tranposition of matrix is transposition of relation *)
Section GofMat_transpose.
Variable dim : nat.
Variable M : matrix dim dim.

Lemma transp_mat_unbound :forall x y, M [[x,y]] = ((mat_transpose M)[[y,x]]).
Proof.
intros;unfold mat_unbound.
destruct (le_gt_dec dim x); auto;destruct (le_gt_dec dim y); auto.
unfold mat_transpose;rewrite mat_build_nth;trivial.
Qed.


Lemma Gmorph_transpose :forall x y, gofmat (mat_transpose M) x y <-> transp (gofmat M) x y.
Proof.
intros;unfold gofmat;unfold transp;rewrite transp_mat_unbound;tauto.
Qed.

End GofMat_transpose.


(* and of matrix (element by element) is intersection of relation *)
Section GofMat_intersection.
Variable dim : nat.
Variable M N: matrix dim dim.

Definition mat_andb := (Vmap2 ( (Vmap2 andb) dim)) dim.

Lemma andb_mat_unbound : forall x y, (mat_andb M N)[[x,y]] = (M[[x,y]] &&  (N[[x,y]])).
Proof.
intros;unfold mat_unbound.
destruct  (le_gt_dec dim x);auto with *.
destruct  (le_gt_dec dim y);auto with *.
unfold mat_andb; repeat rewrite Vmap2_nth; auto.
Qed.

Lemma Gmorph_intersect : forall x y, gofmat (mat_andb M N) x y <->
 gofmat M x y /\ gofmat N x y.
Proof.
intros;unfold gofmat.
rewrite andb_mat_unbound.
destruct (M [[x, y]]); destruct (M [[x, y]]);intuition;simpl.
Qed.

End GofMat_intersection.

(* exponentation, transposition, AND, of the matrix, gives the SCC of the relation*)
Section GofMat_SCC.
Variable dim : nat.

Definition SCC_mat M:=
  let N := mat_expp_fast M (S(log2 dim)) in
  mat_andb N (@mat_transpose dim dim N).

Variable M : matrix dim dim.


Theorem gofmat_SCC :forall x y, gofmat (SCC_mat M) x y <-> SCC (gofmat M) x y.
Proof.
unfold SCC_mat in *; split; intros; rewrite Gmorph_intersect in *; 
try rewrite Gmorph_transpose in *; unfold transp in *;
repeat rewrite Gmorph_clos_trans in *; unfold SCC in *;
trivial.
Qed.

End GofMat_SCC.



Section matofG.
Variable dim : nat.
Variable R : relation nat.

Definition matofG (R_dec : forall x y, {R x y} + {~ R x y}) :=
  mat_build
  (fun x y (g : x < dim) (g': y < dim) => match R_dec x y with
  |left _ => true
  |right _ => false 
  end).
  
Lemma mat_G_isom R_dec : (forall x y, R x y -> x < dim /\ y < dim) ->
 forall x y, (gofmat (matofG R_dec) x y <-> R x y).
intros;unfold gofmat,mat_unbound;split;intros;
destruct (le_gt_dec dim x);destruct (le_gt_dec dim y);
try deduce (H _ _ H0);
auto;intuition;try omega;try tauto;try discriminate.
unfold matofG in H0; rewrite mat_build_nth in H0.
destruct (R_dec x y);auto;try discriminate.
unfold matofG; rewrite mat_build_nth.
destruct (R_dec x y);auto with *.
Qed.
End matofG.




