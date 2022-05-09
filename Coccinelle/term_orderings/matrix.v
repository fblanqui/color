Set Implicit Arguments. 
From Coq Require Import Lia List Setoid Le Peano_dec Eqdep_dec Ring Zwf Morphisms ZArith.
From CoLoR Require Import interp.

Lemma exist_pi:  forall (A:Type) (P: A -> Prop), (forall a (H1 H2:P a), H1=H2) ->
  forall a H1 H2,
    exist P a H1 = exist P a H2.
  intros.
  rewrite (H a H1 H2).
  reflexivity.
Qed.


(** We have unicity of the proofs of le for nat
    Source: Coq-club
*)


Lemma nat_dec : forall n m:nat, n=m \/ n<>m.
intros; destruct (eq_nat_dec n m); [left|right]; auto.
Qed.

Scheme le_rec := Induction for le Sort Prop.

Lemma le_inversion :
  forall (x y:nat) (P:le x y),
    (exists H:x=y, P = (eq_rect x (le x) (le_n x) y H)) \/
    (exists y':nat, exists R:(S y') = y, exists H:(le x y'),
        P = (eq_rect (S y') (le x) (le_S x y' H) y R)).
Proof.
intros x y P.
case P.
left.
exists (eq_refl x); auto.
intros m H.
right.
exists m.
exists (eq_refl (S m)).
exists H; auto.
Qed.

Lemma le_eq : forall (x y:nat) (p1 p2: x <= y), p1 = p2.
Proof.
intros x y p1.
elim p1 using le_rec.
intros p2.
destruct (@le_inversion x x p2) as [(x0,H0)|(x0,(x1,(x2,_)))].
rewrite H0.
rewrite (eq_proofs_unicity nat_dec x0 (eq_refl x)); auto.
subst.
absurd (S x0 <= x0); auto with arith.

intros.
destruct (@le_inversion x (S m) p2) as [(x0,H0)|(x0,(x1,(x2,H0)))].
absurd (S m <= m); auto with arith.
rewrite <- x0.
assumption.

injection x1; intros; subst.
rewrite (H x2).
rewrite (eq_proofs_unicity nat_dec x1 (eq_refl (S m))); auto.
Qed.


Lemma lt_pi: forall n m (H1 H2: n < m), H1=H2.
Proof.
  intros.
  apply le_eq.
Qed.

Lemma exist_lt_pi : forall n dim H1 H2,
  exist (fun n1 => n1 < dim) n H1 = exist
  (fun n1 => n1 < dim) n H2.
Proof.
  intros n dim H1 H2.
  rewrite exist_pi with (a:=n) (P:=fun n1 => n1 < dim)  (H2:=H2).
  reflexivity.
  intros.
  apply lt_pi.
Qed.



(** basic definitions of types and basic operations *)
Section Definitions.
  Variable A:Type.

  Variable eq: A -> A -> Prop.
  Local Notation "x == y" := (eq x y) (at level 70, no associativity).
  Variable eq_Equivalence : Equivalence eq.
  Existing Instance eq_Equivalence.

  Hypothesis plus : A -> A -> A.
  Hypothesis plus_comm: forall a b, plus a b == plus b a.
  Hypothesis plus_assoc: 
    forall a b c, plus (plus a b) c == plus a (plus b c).

  Hypothesis mult : A -> A -> A.
  Hypothesis mult_comm: forall a b, mult a b == mult b a.
  Hypothesis mult_assoc: 
    forall a b c, mult (mult a b) c == mult a (mult b c).
  Hypothesis mult_distrib_left : 
    forall a b c, 
      mult (plus a  b) c == plus (mult a c) (mult b c).
  Hypothesis mult_distrib_right : 
    forall a b c, 
      mult a (plus b  c) == plus (mult a b) (mult a c).

  Hypothesis plus_morph : Proper (eq ==> eq ==> eq) plus.

  Hypothesis mult_morph : Proper (eq ==> eq ==> eq) mult.

  (** a vector of size n is simply a (n+1)-tuple of elements 
     of A*)

  Fixpoint  vector (n:nat) {struct n} : Type := 
  match n with 
    | 0  => A
    | S n => (A*(vector n))%type 
  end.

  Lemma vector_rect : 
    forall (P: forall dim, vector dim -> Type)  
      (f1: forall v, P 0 v) 
      (f2: forall dim a v, P _ v -> P (S dim) (a,v))
      dim v, P dim v.
  Proof.
    intros P f1 f2.
    fix vector_rect 1;intros [|dim].
    exact f1.
    simpl.
    intros [a v].
    apply f2.
    apply vector_rect.
  Qed.
     
  Lemma vector_ind : 
    forall (P: forall dim, vector dim -> Prop)  
      (f1: forall v, P 0 v) 
      (f2: forall dim a v, P _ v -> P (S dim) (a,v))
      dim v, P dim v.
  Proof.
    intros P f1 f2 dim v.
    apply vector_rect;assumption.
  Qed.

  Lemma vector_rec : 
    forall (P: forall dim, vector dim -> Type)  
      (f1: forall v, P 0 v) 
      (f2: forall dim a v, P _ v -> P (S dim) (a,v))
      dim v, P dim v.
  Proof.
    intros P f1 f2 dim v.
    apply vector_rect;assumption.
  Qed.


  Definition eq_vec {dim} : vector dim -> vector dim -> Prop.
  Proof.
    revert dim.
    fix eq_vec 1.
    intros [|dim].
    simpl; exact eq.
    simpl.
    intros [a1 v1] [a2 v2].
    refine (and _ _).
    exact (eq a1 a2).
    exact (eq_vec _ v1 v2).
  Defined.

  Local Notation "x ==v y" := (eq_vec x y) (at level 70, no associativity).

  Lemma eq_vec_refl dim : forall (v:vector dim), eq_vec v v. 
  Proof.
    induction v as [a | dim a v] using vector_ind.
    reflexivity.
    split;auto.
    reflexivity.
  Qed.

  Lemma eq_vec_trans dim : forall (v1 v2 v3:vector dim),
    v1 ==v v2 -> v2 ==v v3 -> v1 ==v v3.
  Proof.
    induction v1 as [a|dim a1 v1] using vector_ind.

    simpl;intros v2 v3;intros;transitivity v2;assumption.

    simpl;intros [a2 v2] [a3 v3].
    intuition.
    transitivity  a2;assumption.
    apply IHv1 with v2;assumption.
 Qed.

  Lemma eq_vec_sym dim : forall (v1 v2:vector dim),
    v1 ==v v2 -> v2 ==v v1.
  Proof.
    induction dim.
    simpl;intros.
    symmetry;assumption.
    simpl;intros [a1 v1] [a2 v2] [a3 v3].
    intuition.
  Qed.

  Global Instance eq_vec_Equivalence dim : Equivalence (@eq_vec dim).

  Proof.
    split; intro x.
    apply eq_vec_refl.
    apply eq_vec_sym.
    apply eq_vec_trans.
  Qed.

  (** 
     [create_vec a n] 
     return a vector of size [n] with all elements equal 
     to [a]
     *)
  Fixpoint create_vec (n:nat) (a:A) {struct n}: vector n := 
    match n  as u return vector u with 
      | 0 => a
      | S n' => (a,@create_vec n' a)
    end.

  Global Instance create_vec_morph dim : Proper (eq ==> eq_vec) (create_vec dim).
  Proof.
    intros a b ab; revert dim a b ab; induction dim.
    simpl;tauto.
    simpl;intros;split;auto.
  Qed.

  (** Sum of vectors and its properties *)
  
  Definition sum_vector : forall dim (v1 v2: vector dim), vector dim.
  Proof.
    fix sum_vector 1.
    intros [|dim].

    simpl;  intros a b;exact (plus a b).

    simpl.
    intros [a1 v1] [a2 v2].
    refine (pair _ _).
    exact (plus a1 a2).
    exact (sum_vector dim v1 v2).
  Defined.

  Global Instance sum_vector_morph dim :
    Proper (eq_vec ==> eq_vec ==> eq_vec) (sum_vector dim).
  Proof.
    revert dim. induction dim.
    simpl.
    intros x y H x0 y0 H0.
    rewrite H;rewrite H0;reflexivity.
    simpl.
    intros [a1 v1] [a2 v2] [h1 h2] 
      [a3 v3] [a4 v4] [h3 h4].
    split. 
    rewrite h1;rewrite h3;reflexivity.
    apply IHdim.
    exact h2. exact h4. 
  Qed. 

  Lemma sum_vector_comm: 
    forall (dim:nat) (v1 v2: vector dim), 
      sum_vector _ v1 v2 ==v sum_vector _ v2 v1.
  Proof.
    fix sum_vector_comm 1.
    intros [|dim].
    simpl.
    intros v1 v2.
    apply plus_comm.

    simpl.
    intros [c1 v1] [c2 v2].
    split.
    apply plus_comm.
    apply sum_vector_comm.
  Qed.

  Lemma sum_vector_assoc: 
    forall (dim:nat) (v1 v2 v3: vector dim), 
      sum_vector _ (sum_vector _ v1 v2) v3 ==v
      sum_vector _ v1 (sum_vector _ v2 v3).
  Proof.
    fix sum_vector_assoc 1.
    intros [|dim].
    simpl.
    intros v1 v2 v3.
    apply plus_assoc.

    simpl.
    intros [c1 v1] [c2 v2] [c3 v3].
    split.
    apply plus_assoc.
    apply sum_vector_assoc.
  Qed.

    (** scalar product of a vector *)
  
  Definition prod_scal_vec : 
    forall dim (a:A)(v:vector dim), 
      vector dim.
  Proof.
    fix prod_scal_vec 1.
    intros [|dim].
        (* dim = 0 *)
    simpl.
    intros a b;exact (mult a b).
    
        (* dim <> 0 *)
    simpl.
    intros c [a1 v1].
    refine (pair _ _).
    exact (mult c a1).
    apply (prod_scal_vec dim c v1).
  Defined.

  Global Instance psv_morph dim :
    Proper (eq ==> eq_vec ==> eq_vec) (prod_scal_vec dim).
  Proof.
    revert dim; induction dim.
    simpl; apply mult_morph.
    simpl.
    intros a b h1 [a1 v1] [a2 v2] [h2 h3].
    split.
    rewrite h1; rewrite h2;reflexivity.
    apply IHdim;assumption.
  Qed.
  
      (** prod_scal_vec is distributive w.r.t sum of vectors *) 
  
  Lemma psv_distrib_left :
    forall dim c1 c2 (r:vector dim), 
      prod_scal_vec _ (plus c1 c2) r ==v
      sum_vector _ (prod_scal_vec  dim c1 r) (prod_scal_vec _ c2 r).
  Proof.
    fix psv_distrib_left 1.
    intros [|dim].
    simpl. intros. 
    apply mult_distrib_left.
    
    simpl vector.
    intros c1 c2 [a r].
    simpl.
    split.
    apply mult_distrib_left.
    apply psv_distrib_left.
  Qed.
  
  Lemma psv_distrib_right :
    forall dim c (r1 r2:vector dim), 
      prod_scal_vec _ c (sum_vector _ r1 r2)  ==v
      sum_vector _ (prod_scal_vec  dim c r1) (prod_scal_vec _ c r2).
  Proof.
    fix psv_distrib_right 1.
    intros [|dim].
    simpl. intros. 
    apply mult_distrib_right.
    
    simpl vector.
    intros c1 [a1 r1] [a2 r2].
    simpl.
    split.
    apply mult_distrib_right. 
    apply psv_distrib_right.
  Qed.

  Lemma psv_assoc :
    forall dim c1 c2 (r:vector dim), 
      prod_scal_vec _ c1  (prod_scal_vec _  c2 r) ==v 
      prod_scal_vec _ (mult c1 c2) r .
  Proof.
    fix psv_assoc 1.
    intros [|dim].
    simpl. intros. 
    symmetry; apply mult_assoc.
    
    simpl vector.
    intros c1 c2 [a r].
    simpl.
    split.
    symmetry; apply mult_assoc.
    apply psv_assoc.
  Qed.
  
  Lemma psv_comm : 
    forall dim (a1 a2:A) (v:vector dim), 
      prod_scal_vec _ a1 (prod_scal_vec _ a2 v) ==v
      prod_scal_vec _ a2 (prod_scal_vec _ a1 v).
  Proof.
    fix psv_comm 1.
    intros [|dim].
    (* dim = 0 *)
    simpl.
    intros.
    rewrite <- mult_assoc.
    rewrite (mult_comm a1). 
    apply mult_assoc.
  
  (* dim <>  0 *)
    simpl vector.
    intros a1 a2 [c1 v1].
    simpl.
    split.
    rewrite <- mult_assoc.
    rewrite (mult_comm a1). 
    apply mult_assoc.
    apply psv_comm.
  Qed.

      (** product of a row by a column *)

  Definition prod_row_col : 
    forall dim (v1 v2:vector dim), A.
  Proof.
    fix prod_row_col 1.
    intros [|dim].
        (* dim = 0 *)
    simpl.
    intros a b;exact (mult a b).
    
        (* dim <> 0 *)
    simpl.
    intros [a1 v1] [a2 v2].
    refine (plus _ _).
    exact (mult a1 a2).
    apply (prod_row_col dim v1 v2).
  Defined.

  Global Instance prc_morph dim : Proper (eq_vec ==> eq_vec ==> eq) (prod_row_col dim).
  Proof.
    revert dim. induction dim.
    simpl; apply mult_morph.
    simpl.
    intros [a1 v1] [a2 v2] [h1 h2] [a3 v3] [a4 v4] [h3 h4].
    rewrite (IHdim _ _ h2 _ _ h4). 
    rewrite h1; rewrite h3;reflexivity.
  Qed.

      (* prod_row_col commutes with prod_scal_vec *)
  Lemma prc_comm_sv_right : 
    forall dim (r c : vector dim) (a:A), 
      prod_row_col _ r (prod_scal_vec _ a c) ==
      mult a  (prod_row_col _ r c).
  Proof.
    fix prc_comm_sv_right 1.
    intros [|dim].
        (* dim = 0 *)
    simpl.
    intros;rewrite <- mult_assoc.
    rewrite (mult_comm r  a).
    apply mult_assoc.
        (* dim <> 0 *)
    simpl vector. 
    intros [a1 r1] [a2 c2] a.
    simpl.
    rewrite prc_comm_sv_right.
    rewrite <- mult_assoc.
    rewrite (mult_comm a1 a).
    rewrite mult_assoc.
    rewrite mult_distrib_right. 
    reflexivity.
  Qed.

  Lemma prc_comm_sv_left : 
    forall dim (r c : vector dim) (a:A), 
      prod_row_col _ (prod_scal_vec _ a r) c ==
      mult a  (prod_row_col _ r c).
  Proof.
    fix prc_comm_sv_left 1.
    intros [|dim].
        (* dim = 0 *)
    simpl.
    intros;apply mult_assoc.      
        (* dim <> 0 *)
    simpl vector. 
    intros [a1 r1] [a2 c2] a.
    simpl.
    rewrite prc_comm_sv_left.
    rewrite mult_distrib_right. 
    rewrite mult_assoc.
    reflexivity.
  Qed.

      (* prod_row_col is distributive wrt vector sum *)
  Lemma prc_distrib_left :
    forall dim c1 c2 (r:vector dim), 
      prod_row_col _ (sum_vector _ c1  c2) r ==
      plus (prod_row_col  dim c1 r) (prod_row_col _ c2 r).
  Proof.
    fix prc_distrib_left 1.
    intros [|dim].
        (* dim = 0 *)
    simpl. intros. 
    apply mult_distrib_left.
    
    simpl vector.
    intros [a1 c1] [a2 c2] [a r].
    simpl.
    rewrite prc_distrib_left.
    repeat rewrite mult_distrib_left.
    repeat rewrite plus_assoc.
    rewrite <- 
      (plus_assoc 
        (mult a2 a) 
        (prod_row_col dim c1 r)
      ).
    rewrite 
      (plus_comm
        (mult a2 a) 
        (prod_row_col dim c1 r)
      ).
    repeat rewrite plus_assoc.
    reflexivity.
  Qed.
  
  Lemma prc_distrib_right :
    forall dim c (r1 r2:vector dim), 
      prod_row_col _ c (sum_vector _ r1  r2) ==
      plus (prod_row_col  dim c r1) (prod_row_col _ c r2).
  Proof.
    fix prc_distrib_right 1.
    intros [|dim].
        (* dim = 0 *)
    simpl. intros. 
    apply mult_distrib_right.
    
    simpl vector.
    intros [a1 c1] [a2 c2] [a r].
    simpl.
    rewrite prc_distrib_right.
    repeat rewrite mult_distrib_right.
    repeat rewrite plus_assoc.
    rewrite <- 
      (plus_assoc
        (prod_row_col dim c1 c2)
        (mult a1 a)
      )
      .
    rewrite (plus_comm
      (prod_row_col dim c1 c2)
      (mult a1 a)
    )
      .
    repeat rewrite plus_assoc.
    reflexivity.
  Qed.
  


(** The type a matrix. 
   A matrix of size (n+1) has the form: 
   
   a r
   c m
   
   where a is a coef 
   r is a vector of size n
   c is a vector of size n
   m is a matrix of size n
*)

  Fixpoint matrix (n:nat) {struct n} : Type := 
    match n with 
      | 0%nat  => A
      | S n => (A*((vector n)*((vector n) * (matrix n))))%type 
    end.
 

  Lemma matrix_rect : 
    forall (P: forall dim, matrix dim -> Type)  
      (f1: forall m, P 0 m) 
      (f2: forall dim a r c m, P _ m -> P (S dim) (a,(r,(c,m))))
      dim m, P dim m.
  Proof.
    intros P f1 f2.
    fix matrix_rect 1;intros [|dim].
    exact f1.
    simpl.
    intros [a [r [c v]]].
    apply f2.
    apply matrix_rect.
  Qed.
     
  Lemma matrix_ind : 
    forall (P: forall dim, matrix dim -> Prop)  
      (f1: forall m, P 0 m) 
      (f2: forall dim a r c m, P _ m -> P (S dim) (a,(r,(c,m))))
      dim m, P dim m.
  Proof.
    intros P f1 f2 dim m.
    apply matrix_rect;assumption.
  Qed.

  Lemma matrix_rec : 
    forall (P: forall dim, matrix dim -> Type)  
      (f1: forall m, P 0 m) 
      (f2: forall dim a r c m, P _ m -> P (S dim) (a,(r,(c,m))))
      dim m, P dim m.
  Proof.
    intros P f1 f2 dim m.
    apply matrix_rect;assumption.
  Qed.

  Definition eq_mat {dim} : matrix dim -> matrix dim -> Prop.
  Proof.
    revert dim. fix eq_mat 1.
    intros [|dim].
    simpl; exact eq.
    simpl.
    intros [a1 [r1 [c1 m1]]] [a2 [r2 [c2 m2]]].
    refine (and _ (and _ (and _ _))).
    exact (eq a1 a2).
    exact (eq_vec r1 r2).
    exact (eq_vec c1 c2).
    exact (eq_mat _ m1 m2).
  Defined.

  Local Notation "x ==m y" := (eq_mat x y) (at level 70, no associativity).

  Lemma eq_mat_refl dim : forall (v:matrix dim), v ==m v. 
  Proof.
    induction v as [a| dim a r c m] using matrix_ind.
    reflexivity.
    repeat split;try reflexivity.
    apply IHm.
  Qed.

  Lemma eq_mat_trans dim : forall (v1 v2 v3:matrix dim),
    v1 ==m v2 -> v2 ==m v3 -> v1 ==m v3.
  Proof.
    induction dim.
    simpl;intros.
    transitivity v2;assumption.
    simpl;intros [a1 [r1 [c1 m1]]] [a2 [r2 [c2 m2]]] [a3 [r3 [c3 m3]]].
    intuition.
    transitivity  a2;assumption.
    transitivity  r2;assumption.
    transitivity  c2;assumption.
    apply IHdim with m2;assumption.
 Qed.

  Lemma eq_mat_sym dim : forall (v1 v2:matrix dim),
    v1 ==m v2 -> v2 ==m v1.
  Proof.
    induction dim.
    simpl;intros.
    symmetry;assumption.
    simpl;intros [a1 [r1 [c1 m1]]] [a2 [r2 [c2 m2]]] [a3 [r3 [c3 m3]]].
    intuition try symmetry;auto.
  Qed.

  Global Instance eq_mat_Equivalence dim : Equivalence (@eq_mat dim).

  Proof.
    split; intro x. apply eq_mat_refl. apply eq_mat_sym. apply eq_mat_trans.
  Qed.

  (** sum of two matrix *)
  Ltac full_rewrite := 
    repeat match goal with 
             | H: _ == _ |- _ => try (rewrite H)||fail 1
             | H: _ ==v _ |- _ => try (rewrite H)|| fail 1
             | H: _ ==m _ |- _=> try (rewrite H)|| fail 1
           end.


  (** 
     [create_mat a n] 
     return a matrix of size [n] with all elements equal 
     to [a]
     *)
  Fixpoint create_mat (n:nat) (a:A) {struct n}: matrix n := 
    match n  as u return matrix u with 
      | 0 => a
      | S n' => (a,(@create_vec n' a, (create_vec n' a,create_mat n' a)))
    end.

  Global Instance create_mat_morph dim : Proper (eq ==> eq_mat) (create_mat dim).
  Proof.
    intro x; revert dim x; induction dim.
    simpl;tauto.
    simpl;intros;repeat split;auto.
    apply create_vec_morph;assumption.
    apply create_vec_morph;assumption.
  Qed.

  Definition sum_matrix : forall dim (m1 m2:matrix dim), matrix dim.
  Proof.
    fix sum_matrix 1.
    intros [|dim].
    simpl.
    intros a b;exact (plus a b).
    
    simpl.
    intros [a1 [l1 [c1 m1]]] [a2 [l2 [c2 m2]]]. 
    refine (pair _ (pair _ (pair _ _))).
    exact (plus a1 a2).
    exact (sum_vector _ l1 l2).
    exact (sum_vector _ c1 c2).
    exact (sum_matrix _ m1 m2).
  Defined.

  Global Instance sum_matrix_morph dim :
    Proper (eq_mat ==> eq_mat ==> eq_mat) (sum_matrix dim).
  Proof.
    revert dim; induction dim.
    simpl. apply plus_morph.

    simpl.
    intros [a1 [r1 [c1 m1]]] [a2 [r2 [c2 m2]]] Heq 
      [a3 [r3 [c3 m3]]]  [a4 [r4 [c4 m4]]] Heq'.
    intuition.
    apply plus_morph;assumption.
    apply sum_vector_morph;assumption.
    apply sum_vector_morph;assumption.
    apply IHdim; assumption.
  Qed.

  (* sum of matrix is commutative *)
  Lemma sum_matrix_comm : 
    forall dim m1 m2, sum_matrix dim m1 m2 ==m sum_matrix dim m2 m1.
  Proof.
    fix sum_matrix_comm 1.
    intros [|dim]. 
    (* dim = 0 *) 
    simpl; apply plus_comm.

    (* dim <> 0 *)
    simpl matrix.
    intros [a1 [r1 [c1 m1]]] [a2 [r2 [c2 m2]]].
    simpl.
    refine (conj _ (conj _ (conj _ _ ))). 
    apply plus_comm.
    apply sum_vector_comm.
    apply sum_vector_comm.
    apply sum_matrix_comm.
  Qed.

  Lemma sum_matrix_assoc : 
    forall dim m1 m2 m3, 
      sum_matrix dim (sum_matrix _ m1 m2) m3 ==m 
      sum_matrix dim m1 (sum_matrix _ m2 m3).
  Proof.
    fix sum_matrix_assoc 1.
    intros [|dim]. 
    (* dim = 0 *) 
    simpl; apply plus_assoc.

    (* dim <> 0 *)
    simpl matrix.
    intros [a1 [r1 [c1 m1]]] [a2 [r2 [c2 m2]]] [a3 [r3 [c3 m3]]].
    simpl.
    refine (conj _ (conj _ (conj _ _ ))).
    apply plus_assoc.
    apply sum_vector_assoc.
    apply sum_vector_assoc.
    apply sum_matrix_assoc.
  Qed.

  (** scalar product for matrices *)
  Definition prod_scal_mat : 
    forall dim (a:A)(v:matrix dim), 
      matrix dim.
  Proof.
    fix prod_scal_mat 1.
    intros [|dim].
        (* dim = 0 *)
    simpl.
    intros a b;exact (mult a b).
    
        (* dim <> 0 *)
    simpl.
    intros c [a1 [r1 [c1 m1]]].
    refine (pair _ (pair _ (pair _ _))).
    exact (mult c a1).
    apply (prod_scal_vec dim c r1).
    apply (prod_scal_vec dim c c1).
    apply (prod_scal_mat _ c m1).
  Defined.

  Global Instance psm_morph dim :
    Proper (eq ==> eq_mat ==> eq_mat) (prod_scal_mat dim).
  Proof.
    revert dim; induction dim.
    simpl. apply mult_morph.

    simpl.
    intros a1 a2 Heq [a3 [r3 [c3 m3]]]  [a4 [r4 [c4 m4]]] Heq'.
    intuition.
    apply mult_morph;assumption.
    apply psv_morph;assumption.
    apply psv_morph;assumption.
    apply IHdim;assumption.
  Qed.
  
  (** prod_scal_mat is distributive w.r.t sum of vectors *) 
  
  Lemma psm_distrib_left :
    forall dim c1 c2 (m:matrix dim), 
      prod_scal_mat _ (plus c1 c2) m ==m
      sum_matrix _ 
      (prod_scal_mat  dim c1 m)
      (prod_scal_mat _ c2 m).
  Proof.
    fix psm_distrib_left 1.
    intros [|dim].
    simpl. intros. 
    apply mult_distrib_left.
    
    simpl matrix.
    intros c1 c2 [a [r [l m]]].
    simpl.
    refine (conj _ (conj _ (conj _ _ ))).
    apply mult_distrib_left.
    apply psv_distrib_left.
    apply psv_distrib_left.
    apply psm_distrib_left.
  Qed.
  
  Lemma psm_distrib_right :
    forall dim c (r1 r2:matrix dim), 
      prod_scal_mat _ c (sum_matrix _ r1 r2) ==m 
      sum_matrix _ (prod_scal_mat  dim c r1) (prod_scal_mat _ c r2).
  Proof.
    fix psm_distrib_right 1.
    intros [|dim].
    simpl. intros. 
    apply mult_distrib_right.
    
    simpl matrix.
    intros c [a1 [ r1 [c1 m1]]] [a2 [r2 [c2 m2]]].
    simpl.
    refine (conj _ (conj _ (conj _ _ ))).
    apply mult_distrib_right. 
    apply psv_distrib_right.
    apply psv_distrib_right.
    apply psm_distrib_right.
  Qed.

  Lemma psm_assoc :
    forall dim c1 c2 (r:matrix dim), 
      prod_scal_mat _ c1  (prod_scal_mat _  c2 r) ==m 
      prod_scal_mat _ (mult c1 c2) r .
  Proof.
    fix psm_assoc 1.
    intros [|dim].
    simpl. intros. 
    symmetry; apply mult_assoc.
    
    simpl matrix.
    intros c1 c2 [a [r [c m]]].
    simpl.
    refine (conj _ (conj _ (conj _ _ ))).
    symmetry; apply mult_assoc.
    apply psv_assoc.
    apply psv_assoc.
    apply psm_assoc.
  Qed.
  
  Lemma psm_comm : 
    forall dim (a1 a2:A) (v:matrix dim), 
      prod_scal_mat _ a1 (prod_scal_mat _ a2 v) ==m 
      prod_scal_mat _ a2 (prod_scal_mat _ a1 v).
  Proof.
    fix psm_comm 1.
    intros [|dim].
    (* dim = 0 *)
    simpl.
    intros.
    rewrite <- mult_assoc.
    rewrite (mult_comm a1). 
    apply mult_assoc.
  
  (* dim <>  0 *)
    simpl vector.
    intros a1 a2 [a [r [c m]]].
    simpl.
    refine (conj _ (conj _ (conj _ _ ))).
    rewrite <- mult_assoc.
    rewrite (mult_comm a1). 
    apply mult_assoc.
    apply psv_comm.
    apply psv_comm.
    apply psm_comm.
  Qed.

  (* product of a col by a row *)
  Definition prod_col_row : forall (dim:nat) (c r:vector dim), matrix dim.
  Proof.
    fix prod_col_row 1.
    intros [|dim].
    simpl.
    intros a b;exact (mult a b).
    
    simpl.
    intros [a1 c1] [a2 r2].
    refine (pair _ (pair _ (pair _ _))).
    exact (mult a1 a2).
    exact (prod_scal_vec _ a1 r2).
    exact (prod_scal_vec _ a2 c1).
    exact (prod_col_row _ c1 r2).
  Defined.

  Global Instance pcr_morph dim :
    Proper (eq_vec ==> eq_vec ==> eq_mat) (prod_col_row dim).
  Proof.
    revert dim; induction dim.
    simpl. apply mult_morph.

    simpl.
    intros [a1 v1] [a2 v2] Heq 
      [a3 v3]  [a4 v4] Heq'.
    intuition.
    apply mult_morph;assumption.
    apply psv_morph;assumption.
    apply psv_morph;assumption.
    apply IHdim;assumption.
  Qed.

  Lemma pcr_comm_sv_right : 
    forall dim (c r : vector dim) (a:A), 
      prod_col_row _ c (prod_scal_vec _ a r) ==m 
      prod_scal_mat _ a  (prod_col_row _ c r).
  Proof.
    fix pcr_comm_sv_right 1.
    intros [|dim].
        (* dim = 0 *)
    simpl.
    intros;rewrite <- mult_assoc.
    rewrite (mult_comm c). 
    apply mult_assoc.
        (* dim <> 0 *)
    simpl vector. 
    intros [a1 r1] [a2 c2] a.
    simpl.
    rewrite pcr_comm_sv_right.
    rewrite <- mult_assoc.
    rewrite (mult_comm a1).
    rewrite mult_assoc.
    refine (conj _ (conj _ (conj _ _))).
    reflexivity.
    apply psv_comm.
    symmetry. apply psv_assoc.
    reflexivity.
  Qed.

  Lemma pcr_comm_sv_left : 
    forall dim (c r : vector dim) (a:A), 
      prod_col_row _ (prod_scal_vec _ a r) c ==m
      prod_scal_mat _ a  (prod_col_row _ r c).
  Proof.
    fix pcr_comm_sv_left 1.
    intros [|dim].
        (* dim = 0 *)
    simpl.
    intros;rewrite <- mult_assoc.
    reflexivity.
    (* dim <> 0 *)
    simpl vector. 
    intros [a1 r1] [a2 c2] a.
    simpl.
    refine (conj _ (conj _ (conj _ _ ))).
    apply mult_assoc.
    symmetry; apply psv_assoc.
    rewrite psv_assoc.
    rewrite mult_comm.
    symmetry;apply psv_assoc.
    apply pcr_comm_sv_left.
  Qed.

  (* prod_row_col is distributive wrt vector sum *)
  Lemma pcr_distrib_left :
    forall dim c1 c2 (r:vector dim), 
      prod_col_row _ (sum_vector _ c1  c2) r ==m
      sum_matrix _
      (prod_col_row dim c1 r) (prod_col_row _ c2 r).
  Proof.
    fix pcr_distrib_left 1.
    intros [|dim].
        (* dim = 0 *)
    simpl. intros. 
    apply mult_distrib_left.
    
    simpl vector.
    intros [a1 c1] [a2 c2] [a r].
    simpl.
    refine (conj _ (conj _ (conj _ _ ))).
    apply mult_distrib_left.
    apply psv_distrib_left.
    apply psv_distrib_right.
    apply pcr_distrib_left.
  Qed.
  
  Lemma pcr_distrib_right :
    forall dim c (r1 r2:vector dim), 
      prod_col_row _ c (sum_vector _ r1  r2) ==m
      sum_matrix _ (prod_col_row  dim c r1) (prod_col_row _ c r2).
  Proof.
    fix pcr_distrib_right 1.
    intros [|dim].
        (* dim = 0 *)
    simpl. intros. 
    apply mult_distrib_right.
    
    simpl vector.
    intros [a1 c1] [a2 c2] [a r].
    simpl.
    refine (conj _ (conj _ (conj _ _ ))).
    apply mult_distrib_right.
    apply psv_distrib_right.
    apply psv_distrib_left.
    apply pcr_distrib_right.
  Qed.

  (** product of a row by a matrix *)
  
  Definition prod_row_mat : forall (dim:nat) (r:vector dim)  (m:matrix dim), vector dim.
  Proof.
    fix prod_row_mat 1.
    intros [|dim].
    simpl.
    intros a b;exact (mult a b).
    
    simpl.
    intros [a1 r1] [a2 [r2 [c2 m2]]].
    refine (pair _ _).
    refine (plus _ _).
    exact (mult a1 a2). 
    exact (prod_row_col _ r1 c2).
    refine (sum_vector dim _ _).
    exact (prod_scal_vec _ a1 r2).
    apply (prod_row_mat _ r1 m2).
  Defined.

  Global Instance prm_morph dim :
    Proper (eq_vec ==> eq_mat ==> eq_vec) (prod_row_mat dim).
  Proof.
    revert dim; induction dim.
    simpl. apply mult_morph.

    simpl.
    intros [a1 v1] [a2 v2] Heq 
      [a3 [r3 [c3 m3]]]  [a4 [r4 [c4 m4]]] Heq'.
    intuition.
    apply plus_morph. apply mult_morph;assumption. apply prc_morph;assumption.
    full_rewrite;reflexivity.
  Qed.

  Lemma prm_comm_sv_right : 
    forall dim (r : vector dim) (m:matrix dim) (a:A), 
      prod_row_mat _ r (prod_scal_mat _ a m) ==v 
      prod_scal_vec _ a  (prod_row_mat _ r m).
  Proof.
    fix prm_comm_sv_right 1.
    intros [|dim].
    (* dim = 0 *)
    simpl.
    intros;rewrite <- mult_assoc.
    rewrite (mult_comm r a).
    apply mult_assoc.
        (* dim <> 0 *)
    simpl vector;simpl matrix. 
    intros [a1 r1] [a2 [r2 [c2 m2]]] a.
    simpl.
    f_equal.
    rewrite prc_comm_sv_right.
    repeat rewrite mult_distrib_right.
    refine (conj _ _).
    rewrite <- mult_assoc.
    rewrite (mult_comm a1 a).
    rewrite mult_assoc.
    reflexivity.
    rewrite psv_distrib_right.
    rewrite psv_comm. 
    rewrite prm_comm_sv_right.
    reflexivity.
  Qed.



  Lemma prm_comm_sv_left : 
    forall dim (r : vector dim) (m:matrix dim) (a:A), 
      prod_row_mat _ (prod_scal_vec _ a r) m ==v
      prod_scal_vec _ a  (prod_row_mat _ r m).
  Proof.
    fix prm_comm_sv_left 1.
    intros [|dim].
    (* dim = 0 *)
    simpl.
    intros;rewrite <- mult_assoc.
    reflexivity.
    (* dim <> 0 *)
    simpl vector;simpl matrix.
    intros [a1 r1] [a2 [r2 [c2 m2]]] a.
    simpl.
    refine (conj _ _).
    rewrite prc_comm_sv_left.
    repeat rewrite mult_distrib_right.
    rewrite mult_assoc.
    reflexivity.
    rewrite psv_distrib_right.
    rewrite psv_assoc.
    rewrite prm_comm_sv_left. reflexivity.
  Qed.

  (* prod_row_col is distributive wrt vector sum *)
  Lemma prm_distrib_left :
    forall dim r1 r2 (m:matrix dim), 
      prod_row_mat _ (sum_vector _ r1 r2) m ==v 
      sum_vector _
      (prod_row_mat dim r1 m) (prod_row_mat _ r2 m).
  Proof.
    fix prm_distrib_left 1.
    intros [|dim].
        (* dim = 0 *)
    simpl. intros. 
    apply mult_distrib_left.
    
    simpl vector;simpl matrix.
    intros [a1 c1] [a2 c2] [a [r [c m]]].
    simpl.
    constructor.
    repeat rewrite mult_distrib_left.
    rewrite prc_distrib_left.
    repeat rewrite plus_assoc. 
    rewrite <- plus_assoc.
    rewrite (plus_comm (mult a2 a)).
    rewrite plus_assoc. 
    rewrite (plus_comm (mult a2 a)). 
    rewrite plus_assoc;reflexivity.
    
    rewrite prm_distrib_left.
    rewrite psv_distrib_left.
    repeat rewrite sum_vector_assoc.
    rewrite <- (sum_vector_assoc _ (prod_scal_vec dim a2 r)).
    rewrite (sum_vector_comm _  (prod_scal_vec _ a2 r)).
    rewrite sum_vector_assoc.
    reflexivity.
  Qed.
  
  Lemma prm_distrib_right :
    forall dim r (m1 m2:matrix dim), 
      prod_row_mat _ r (sum_matrix _ m1  m2) ==v 
      sum_vector _ (prod_row_mat  dim r m1) (prod_row_mat _ r m2).
  Proof.
    fix prm_distrib_right 1.
    intros [|dim].
        (* dim = 0 *)
    simpl. intros. 
    apply mult_distrib_right.
    
    simpl vector;simpl matrix.
    intros [a1 c1] [a2 [r2 [c2 m2]]] [a [r [c m]]].
    simpl.
    f_equal.
    repeat rewrite mult_distrib_right.
    rewrite prc_distrib_right.
    repeat rewrite plus_assoc. 
    constructor.
    rewrite <- (plus_assoc (mult a1 a)).
    rewrite (plus_comm (mult a1 a)).
    rewrite plus_assoc. reflexivity.
    rewrite prm_distrib_right.
    rewrite psv_distrib_right.
    repeat rewrite sum_vector_assoc.
    rewrite <- (sum_vector_assoc _(prod_scal_vec dim a1 r)) .
    rewrite (sum_vector_comm _ (prod_scal_vec _ a1 r)).
    rewrite sum_vector_assoc;reflexivity.
  Qed.

  (** product of a matrix by a column *)
  
  Definition prod_mat_col : forall (dim:nat) (m:matrix dim) (c:vector dim), vector dim.
  Proof.
    fix prod_mat_col 1.
    intros [|dim].
    simpl.
    intros a b;exact (mult a b).
    
    simpl.
    intros [a1 [r1 [c1 m1]]] [a2 c2] .
    refine (pair _ _).
    refine (plus _ _).
    exact (mult a1 a2).
    exact (prod_row_col _ r1 c2).
    refine (sum_vector dim _ _).
    exact (prod_scal_vec _ a2 c1).
    apply (prod_mat_col _ m1 c2).
  Defined.

  Global Instance pmc_morph dim :
    Proper (eq_mat ==> eq_vec ==> eq_vec) (prod_mat_col dim).
  Proof.
    revert dim; induction dim.
    simpl. apply mult_morph.

    simpl.
    intros  
      [a3 [r3 [c3 m3]]]  [a4 [r4 [c4 m4]]] Heq' [a1 v1] [a2 v2] Heq.
    intuition.
    apply plus_morph. apply mult_morph;assumption. apply prc_morph;assumption.
    full_rewrite;reflexivity.
  Qed.

  Lemma pmc_comm_sv_right : 
    forall dim (m:matrix dim) (c : vector dim) (a:A), 
      prod_mat_col _ m (prod_scal_vec _ a c) ==v 
      prod_scal_vec _ a  (prod_mat_col _ m c).
  Proof.
    fix pmc_comm_sv_right 1.
    intros [|dim].
    (* dim = 0 *)
    simpl.
    intros;rewrite <- mult_assoc.
    rewrite (mult_comm m);apply mult_assoc.
    (* dim <> 0 *)
    simpl vector;simpl matrix. 
    intros [a1 [r1 [c1 m1]]] [a2 r2] a.
    simpl.
    repeat rewrite mult_distrib_right.
    constructor.
    rewrite <- (mult_assoc a1).
    rewrite (mult_comm  a1);
      rewrite mult_assoc.
    rewrite prc_comm_sv_right. reflexivity.

    repeat rewrite psv_distrib_right.
    rewrite <- psv_assoc. 
    rewrite pmc_comm_sv_right. reflexivity.
  Qed.

  Lemma pmc_comm_sv_left : 
    forall dim (m:matrix dim) (c : vector dim)  (a:A), 
      prod_mat_col _ (prod_scal_mat _ a m) c ==v 
      prod_scal_vec _ a  (prod_mat_col _ m c).
  Proof.
    fix pmc_comm_sv_left 1.
    intros [|dim].
    (* dim = 0 *)
    simpl.
    intros;apply mult_assoc.
    (* dim <> 0 *)
    simpl vector;simpl matrix. 
    intros [a1 [r1 [c1 m1]]] [a2 r2] a.
    simpl.
    repeat rewrite mult_distrib_right.
    constructor.
    rewrite mult_assoc.
    rewrite prc_comm_sv_left;reflexivity.
    repeat rewrite psv_distrib_right.
    rewrite psv_comm. 
    rewrite pmc_comm_sv_left. reflexivity.
  Qed.

  (* prod_row_col is distributive wrt vector sum *)
  Lemma pmc_distrib_left :
    forall dim m1 m2 (c:vector dim), 
      prod_mat_col _ (sum_matrix _ m1 m2) c ==v 
      sum_vector _
      (prod_mat_col dim m1 c) (prod_mat_col _ m2 c).
  Proof.
    fix pmc_distrib_left 1.
    intros [|dim].
        (* dim = 0 *)
    simpl. intros. 
    apply mult_distrib_left.
    
    simpl vector;simpl matrix.
    intros [a1 [r1 [c1 m1]]] [a2 [r2 [c2 m2]]] [a3 c3].
    simpl.
    constructor.
    repeat rewrite mult_distrib_left.
    rewrite prc_distrib_left.
    repeat rewrite plus_assoc. 
    rewrite <- (plus_assoc (mult a2 a3)).
    rewrite (plus_comm (mult a2 a3)).
    rewrite plus_assoc. reflexivity.
    rewrite pmc_distrib_left.
    rewrite psv_distrib_right.
    repeat rewrite sum_vector_assoc.
    rewrite <- (sum_vector_assoc _ (prod_scal_vec _ a3 c2)).
    rewrite (sum_vector_comm _(prod_scal_vec _ a3 c2)).
    rewrite sum_vector_assoc. reflexivity.
  Qed.
  
  Lemma pmc_distrib_right :
    forall dim m (c1 c2:vector dim), 
      prod_mat_col _ m (sum_vector _ c1  c2) ==v
      sum_vector _ (prod_mat_col  dim m c1) (prod_mat_col _ m c2).
  Proof.
    fix pmc_distrib_right 1.
    intros [|dim].
        (* dim = 0 *)
    simpl. intros. 
    apply mult_distrib_right.
    
    simpl vector;simpl matrix.
    intros [a1 [r1 [c1 m1]]] [a2 c2] [a3 c3].
    simpl.
    constructor.
    repeat rewrite mult_distrib_right.
    rewrite prc_distrib_right.
    repeat rewrite plus_assoc. 
    rewrite <- (plus_assoc (mult a1 a3)).
    rewrite (plus_comm (mult a1 a3)).
    rewrite plus_assoc. reflexivity.
    rewrite pmc_distrib_right.
    rewrite psv_distrib_left.
    repeat rewrite sum_vector_assoc.
    rewrite <- (sum_vector_assoc _ (prod_scal_vec _ a3 c1)).
    rewrite (sum_vector_comm _ (prod_scal_vec _ a3 c1)).
    rewrite sum_vector_assoc. reflexivity.
  Qed.

  (** 
     product of two matrices 
     *)

  Definition prod_matrix : forall (dim:nat) (m1 m2:matrix dim), matrix dim. 
  Proof.
    fix prod_matrix 1.
    intros [|dim].
    intros a b;exact (mult a b).

    simpl.
    intros [a1 [r1 [c1 m1]]] [a2 [r2 [c2 m2]]].
    refine (pair _ (pair _ (pair _ _))).
    refine (plus _ _).
    exact (mult a1  a2).
    exact (prod_row_col _ r1 c2).
    refine (sum_vector dim _ _).
    exact (prod_scal_vec _ a1 r2).
    exact (prod_row_mat _ r1 m2).
    refine (sum_vector dim _ _).
    exact (prod_scal_vec _ a2 c1).
    exact (prod_mat_col _ m1 c2).
    refine (sum_matrix dim _ _).
    exact (prod_col_row _ c1 r2).
    exact (prod_matrix _ m1 m2).
  Defined.

  Global Instance pm_morph dim :
    Proper (eq_mat ==> eq_mat ==> eq_mat) (prod_matrix dim).
  Proof.
    revert dim; induction dim.
    simpl. apply mult_morph.

    simpl.
    intros [a1 [r1 [c1 m1]]] [a2 [r2 [c2 m2]]] Heq [a3 [r3 [c3 m3]]]  [a4 [r4 [c4 m4]]] Heq'.
    intuition.
    full_rewrite. reflexivity.
    full_rewrite;reflexivity.
    full_rewrite;reflexivity.
    apply sum_matrix_morph. apply pcr_morph;assumption. apply IHdim;assumption.
  Qed.

  Lemma pm_comm_sv_right : 
    forall dim (m1 m2:matrix dim) (a:A), 
      prod_matrix _ (prod_scal_mat _ a m1) m2 ==m
      prod_scal_mat _ a  (prod_matrix _ m1 m2).
  Proof.
    fix pm_comm_sv_right 1.
    intros [|dim].
    (* dim = 0 *)
    simpl.
    intros;apply mult_assoc.
    (* dim <> 0 *)
    simpl vector;simpl matrix. 
    intros [a1 [r1 [c1 m1]]] [a2 [r2 [c2 m2]]] a.
    simpl.
    refine (conj _ (conj _ (conj _ _ ))).

    repeat rewrite mult_distrib_right.
    rewrite mult_assoc.
    rewrite prc_comm_sv_left. reflexivity.

    repeat rewrite psv_distrib_right.
    rewrite <- psv_assoc. 
    rewrite prm_comm_sv_left. reflexivity.

    repeat rewrite psv_distrib_right.
    rewrite psv_comm.
    rewrite pmc_comm_sv_left. reflexivity.

    repeat rewrite psm_distrib_right.
    rewrite pcr_comm_sv_left.
    rewrite pm_comm_sv_right. reflexivity.
  Qed.

  Lemma pm_comm_sv_left : 
    forall dim (m1 m2:matrix dim) (a:A), 
      prod_matrix _ m1 (prod_scal_mat _ a m2) ==m
      prod_scal_mat _ a  (prod_matrix _ m1 m2).
  Proof.
    fix pm_comm_sv_left 1.
    intros [|dim].
    (* dim = 0 *)
    simpl.
    intros; rewrite <- mult_assoc.
    rewrite (mult_comm m1).
    apply mult_assoc.
    (* dim <> 0 *)
    simpl vector;simpl matrix. 
    intros [a1 [r1 [c1 m1]]] [a2 [r2 [c2 m2]]] a.
    simpl.
    refine (conj _ (conj _ (conj _ _ ))).

    repeat rewrite mult_distrib_right.
    rewrite <- mult_assoc.
    rewrite (mult_comm a1).
    rewrite mult_assoc.
    rewrite prc_comm_sv_right.  reflexivity.

    repeat rewrite psv_distrib_right.
    rewrite psv_comm. 
    rewrite prm_comm_sv_right. reflexivity.

    repeat rewrite psv_distrib_right.
    rewrite <- psv_assoc.
    rewrite pmc_comm_sv_right. reflexivity.

    repeat rewrite psm_distrib_right.
    rewrite pcr_comm_sv_right.
    rewrite pm_comm_sv_left. reflexivity.
  Qed.

  (* prod_matrix is distributive wrt matrix sum *)
  Lemma pm_distrib_left :
    forall dim m1 m2 (m3:matrix dim), 
      prod_matrix _ (sum_matrix _ m1 m2) m3 ==m 
      sum_matrix _
      (prod_matrix dim m1 m3) (prod_matrix _ m2 m3).
  Proof.
    fix pm_distrib_left 1.
    intros [|dim].
        (* dim = 0 *)
    simpl. intros. 
    apply mult_distrib_left.
    
    simpl matrix.
    intros [a1 [r1 [c1 m1]]] [a2 [r2 [c2 m2]]] [a3 [r3 [c3 m3]]].
    simpl.
    refine (conj _ (conj _ (conj _ _ ))).

    repeat rewrite mult_distrib_left.
    rewrite prc_distrib_left.
    repeat rewrite plus_assoc. 
    rewrite <- (plus_assoc (mult a2 a3)).
    rewrite (plus_comm (mult a2 a3)).
    rewrite plus_assoc. reflexivity.

    rewrite psv_distrib_left.  
    rewrite prm_distrib_left.  
    repeat rewrite sum_vector_assoc.
    rewrite <- (sum_vector_assoc _ (prod_scal_vec dim a2 r3)).
    rewrite (sum_vector_comm _ (prod_scal_vec dim a2 r3)).
    rewrite sum_vector_assoc. reflexivity.

    repeat rewrite psv_distrib_right.
    repeat rewrite pmc_distrib_left.
    repeat rewrite sum_vector_assoc.

    rewrite <- (sum_vector_assoc _ (prod_scal_vec dim a3 c2)).
    rewrite (sum_vector_comm _ (prod_scal_vec dim a3 c2)).
    rewrite sum_vector_assoc.
    repeat rewrite pcr_distrib_left.
    repeat rewrite pm_distrib_left.
    repeat rewrite sum_matrix_assoc. reflexivity.

    rewrite <- sum_matrix_assoc.
    rewrite <- (sum_matrix_comm _ ((prod_col_row dim c2 r3))).
    rewrite sum_matrix_assoc.
    rewrite (sum_vector_comm _ c1).
    rewrite pcr_distrib_left.
    rewrite pm_distrib_left.
    repeat rewrite sum_matrix_assoc. reflexivity.
  Qed.

  Lemma pm_distrib_right :
    forall dim m1 m2 (m3:matrix dim), 
      prod_matrix _ m1 (sum_matrix _ m2 m3) ==m 
      sum_matrix _
      (prod_matrix dim m1 m2) (prod_matrix _ m1 m3).
  Proof.
    fix pm_distrib_right 1.
    intros [|dim].
        (* dim = 0 *)
    simpl. intros. 
    apply mult_distrib_right.
    
    simpl matrix.
    intros [a1 [r1 [c1 m1]]] [a2 [r2 [c2 m2]]] [a3 [r3 [c3 m3]]].
    simpl.
    refine (conj _ (conj _ (conj _ _ ))).

    repeat rewrite mult_distrib_right.
    rewrite prc_distrib_right.
    repeat rewrite plus_assoc. 
    rewrite <- (plus_assoc (mult a1 a3)).
    rewrite (plus_comm (mult a1 a3)).
    rewrite plus_assoc. reflexivity.

    rewrite psv_distrib_right.  
    rewrite prm_distrib_right.  
    repeat rewrite sum_vector_assoc.
    rewrite <- (sum_vector_assoc _ (prod_scal_vec dim a1 r3)).
    rewrite (sum_vector_comm _ (prod_scal_vec dim a1 r3)).
    rewrite sum_vector_assoc. reflexivity.

    repeat rewrite psv_distrib_left.
    repeat rewrite pmc_distrib_right.
    repeat rewrite sum_vector_assoc.
    rewrite <- (sum_vector_assoc _ (prod_scal_vec dim a3 c1)).
    rewrite (sum_vector_comm _ (prod_scal_vec dim a3 c1)).
    rewrite sum_vector_assoc. reflexivity.

    repeat rewrite pcr_distrib_right.
    repeat rewrite pm_distrib_right.
    repeat rewrite sum_matrix_assoc.
    rewrite <- (sum_matrix_assoc _ (prod_col_row dim c1 r3)).
    rewrite (sum_matrix_comm _ (prod_col_row dim c1 r3)).
    rewrite sum_matrix_assoc. reflexivity.
  Qed.



  Lemma prm_pmc_comm : 
    forall dim r m c, 
      prod_row_col dim (prod_row_mat _ r m) c == 
      prod_row_col dim r (prod_mat_col _ m c).
  Proof.
    fix prm_pmc_comm 1.
    intros [|dim].
    (* dim = 0 *)
    simpl;intros;apply mult_assoc.
    (* dim <> 0 *)
    simpl; intros [a1 r1] [a2 [r2 [c2 m2]]] [a3 c3].
    repeat rewrite mult_distrib_right.
    repeat rewrite mult_distrib_left.
    repeat rewrite prc_distrib_right.
    repeat rewrite prc_distrib_left.
    repeat rewrite plus_assoc.
    rewrite mult_assoc.
    assert ( Heq: (plus (mult (prod_row_col dim r1 c2) a3)
      (plus (prod_row_col dim (prod_scal_vec dim a1 r2) c3)
        (prod_row_col dim (prod_row_mat dim r1 m2) c3))) == (plus (mult a1 (prod_row_col dim r2 c3))
        (plus (prod_row_col dim r1 (prod_scal_vec dim a3 c2))
           (prod_row_col dim r1 (prod_mat_col dim m2 c3)))));
    [|rewrite Heq;reflexivity]. 
    rewrite <- plus_assoc.  
    rewrite (plus_comm (mult (prod_row_col dim r1 c2) a3)).
    rewrite plus_assoc.
    rewrite prc_comm_sv_left.
    assert (Heq:(plus (mult (prod_row_col dim r1 c2) a3)
        (prod_row_col dim (prod_row_mat dim r1 m2) c3))==
    (plus (prod_row_col dim r1 (prod_scal_vec dim a3 c2))
      (prod_row_col dim r1 (prod_mat_col dim m2 c3))));
    [|rewrite Heq;reflexivity].
    rewrite prc_comm_sv_right.
    rewrite mult_comm.
    rewrite prm_pmc_comm. reflexivity.
  Qed.

  Lemma pcr_prc_comm : 
    forall dim c1 r c2, 
      prod_mat_col dim (prod_col_row _ c1 r) c2 ==v  
      prod_scal_vec _ (prod_row_col _ r c2) c1.
  Proof.
    fix pcr_prc_comm 1.
    intros [|dim].
    intros;simpl.
    rewrite (mult_comm c1).
    do 2 rewrite mult_assoc.
    rewrite (mult_comm c1). reflexivity.

    simpl;
    intros [a1 c1] [a2 r2] [a3 r3].
    constructor.

    repeat rewrite mult_distrib_right.
    repeat rewrite prc_distrib_right.
    repeat rewrite prc_comm_sv_right.
    repeat rewrite mult_distrib_right.
    repeat rewrite mult_distrib_left.
    repeat rewrite plus_assoc.

    rewrite (mult_comm a1).
    do 2 rewrite mult_assoc.
    rewrite (mult_comm a1).
    
    rewrite prc_comm_sv_left.
    rewrite (mult_comm a1). reflexivity.

    rewrite psv_assoc.
    rewrite pcr_prc_comm.
    rewrite psv_distrib_left.
    rewrite mult_comm. reflexivity.
  Qed.
    

  Lemma pm_assoc_pmc : 
    forall dim m1 m2 c, 
    prod_mat_col dim m1 (prod_mat_col _ m2 c) ==v 
    prod_mat_col _ (prod_matrix _ m1 m2) c. 
  Proof.
    fix pm_assoc_pmc 1.
    intros [|dim].
    (* dim = 0 *)
    intros;simpl.
    symmetry;apply mult_assoc.
    (* dim <> 0 *)
    simpl;
      intros [a1 [r1 [c1 m1]]] [a2 [r2 [l2 m2]]] [a3 c3].
    f_equal.

    repeat rewrite mult_distrib_right.
    repeat rewrite prc_distrib_right.
    repeat rewrite prc_comm_sv_right.
    repeat rewrite mult_distrib_right.
    repeat rewrite mult_distrib_left.
    repeat rewrite plus_assoc.
    constructor.

    rewrite <- mult_assoc.
    rewrite <- (plus_assoc (mult a1 (prod_row_col dim r2 c3))).
    rewrite (plus_comm (mult a1 (prod_row_col dim r2 c3))).
    rewrite plus_assoc .
    match goal with 
      |- plus _ ?t == plus _ ?t' => 
        assert (Heq: t == t');[|rewrite Heq;reflexivity]
    end.
    rewrite mult_comm.
    match goal with 
      |- plus _ ?t == plus _ ?t' => 
        assert (Heq: t == t');[|rewrite Heq;reflexivity]
    end.
    rewrite prc_distrib_left.
    rewrite prc_comm_sv_left.
    rewrite prm_pmc_comm.
    reflexivity.

    repeat rewrite psv_distrib_right.
    repeat rewrite psv_assoc.
    repeat rewrite pmc_distrib_left.
    repeat rewrite pmc_distrib_right.
    repeat rewrite psv_distrib_left.
    repeat rewrite sum_vector_assoc.
    match goal with 
      |- sum_vector _ ?a ?b ==v sum_vector _ ?a' ?b' => 
        assert (Heq1: a ==v a');[|
          assert (Heq2: b ==v b');[|rewrite Heq1;rewrite Heq2;reflexivity]
        ]
    end.
    rewrite mult_comm. reflexivity.
    rewrite pcr_prc_comm.
    rewrite <- sum_vector_assoc.
    rewrite (sum_vector_comm _ (prod_scal_vec dim (prod_row_col dim r2 c3) c1)).
    rewrite sum_vector_assoc.
    rewrite pmc_comm_sv_right.
    rewrite pm_assoc_pmc. reflexivity.
  Qed.

End Definitions.

Arguments eq_vec [A] _ {dim} _ _.
Arguments eq_mat [A] _ {dim} _ _.

Definition split_vector : 
  forall A B dim,  vector (A * B) dim -> vector A dim * vector B dim.
Proof.
  intros A B.
  fix split_vector 1;intros [|dim].
  simpl.
  intros res;exact res.
  simpl. 
  intros [[a b] v].
  destruct (split_vector _ v) as [va vb].
  refine (pair _ _).
  exact (a,va).
  exact (b,vb).
Defined.
Definition combine_vector : 
  forall A B dim,   vector A dim  -> vector B dim -> vector (A * B) dim.
Proof.
  intros A B.
  fix combine_vector 1;intros [|dim].
  simpl.
  intros a b;exact (a,b).

  simpl. 
  intros [a va] [b vb].
  exact (pair (a,b) (combine_vector _ va vb)).
Defined.  

Lemma split_combine_comm : 
  forall A B dim va vb, split_vector _ _ _ (combine_vector A B dim va vb) = (va,vb).
Proof.
  intros A B.
  induction dim.
  
  vm_compute;reflexivity.
  
  simpl;intros [a va] [b vb].
  rewrite IHdim;reflexivity.
Qed.  

Lemma combine_split_comm : 
  forall A B dim v, let (va,vb) := split_vector A B dim v in 
    (combine_vector A B dim va vb) = v.
Proof.
  intros A B.
  induction dim.
  
  vm_compute. intros [a b]; simpl; reflexivity.
  
  simpl;intros [[a b] v].
  simpl.
  generalize  (IHdim v). 
  case (split_vector  _ _ dim v).
  intros;subst;reflexivity.
Qed.  

Definition matrix_from_vector_of_vectors : forall A dim, (vector (vector A dim) dim) -> 
  matrix A dim.
Proof.
  intros A. 
  fix matrix_from_vector_of_vectors 1.
  intros [|dim].
  
  intros a;exact a.
  
  simpl.
  intros [[a' c] sm].
  destruct (split_vector _ _ _ sm) as [r m].
  refine (pair _ (pair _ (pair _ _))).
  exact a'.
  exact r.
  exact c.
  exact (matrix_from_vector_of_vectors _ m).
Defined.

Definition vector_of_vectors_from_matrix : 
  forall A dim, matrix A dim -> vector (vector A dim) dim.
Proof.
  intros A.
  fix vector_of_vectors_from_matrix 1;intros [|dim].
  intros a;exact a.
  simpl.
  intros [a [r [c m]]].
  refine (pair _ _).
  exact (a,c).
  generalize (vector_of_vectors_from_matrix _ m).
  intros v.
  exact (combine_vector _ _ _ r v).
Defined.

Module Type TRing. 
Parameter A:Type.
Parameter eq : A -> A -> Prop.
Parameter  rO rI : A. 
Parameter plus mult sub : A -> A -> A.
Parameter opp : A -> A. 
#[global] Declare Instance eq_Equivalence : Equivalence eq.
Parameter Ath : ring_theory rO rI plus mult sub opp eq.
Parameter Aeqe : ring_eq_ext plus mult opp eq.
End TRing.

Module Make(R:TRing).
  Import R.
  Local Notation "x == y" := (eq x y) (at level 70, no associativity).

  #[global] Instance plus_morph : Proper (eq ==> eq ==> eq) plus.
  Proof. exact (Radd_ext Aeqe). Qed.

  #[global] Instance mult_morph : Proper (eq ==> eq ==> eq) mult.
  Proof. exact (Rmul_ext Aeqe). Qed.
 
  #[global] Instance opp_morph : Proper (eq ==> eq) opp.
  Proof. exact (Ropp_ext Aeqe). Qed.

  Add Ring Rring : Ath.

  (** a vector of size n is simply a (n+1)-tuple of elements 
     of A*)

  Definition vector : nat -> Type.
  apply (vector A).
  Defined.

  Definition eq_vec {dim} : vector dim -> vector dim -> Prop.
  Proof.
    apply (@eq_vec A eq).
  Defined.

  Local Notation "x ==v y" := (eq_vec x y) (at level 70, no associativity).

  Lemma eq_vec_refl : forall dim (v:vector dim), eq_vec v v. 
  Proof.
    exact (@eq_vec_refl _ eq eq_Equivalence).
  Qed.

  Lemma eq_vec_trans : forall dim (v1 v2 v3:vector dim),
    v1 ==v v2 -> v2 ==v v3 -> v1 ==v v3.
  Proof.
    exact (eq_vec_trans eq_Equivalence).
 Qed.

  Lemma eq_vec_sym : forall dim (v1 v2:vector dim),
    v1 ==v v2 -> v2 ==v v1.
  Proof.
    exact (eq_vec_sym eq_Equivalence).
  Qed.

  #[global] Instance eq_vec_Equivalence dim : Equivalence (@eq_vec dim).

  Proof. apply eq_vec_Equivalence. apply eq_Equivalence. Qed.

  (** 
     [create a n] 
     return a vector of size [n] with all elements equal 
     to [a]
     *)
  
  Definition create_vec : forall (n:nat) (a:A), vector n.
  Proof.
    apply create_vec.
  Defined.

  #[global] Instance create_vec_morph dim : Proper (eq ==> eq_vec) (create_vec dim).
  Proof.
    apply create_vec_morph.
  Qed.

  (** Sum of vectors and its properties *)
  
  Definition sum_vector : forall (dim:nat) (v1 v2: vector dim), vector dim.
  Proof.
    apply (sum_vector plus).
  Defined.

  #[global] Instance sum_vector_morph dim :
    Proper (eq_vec ==> eq_vec ==> eq_vec) (sum_vector dim).
  Proof.
    apply sum_vector_morph with (eq:=eq) (plus:=plus).
    exact eq_Equivalence.
    apply plus_morph.
  Qed. 

  Lemma sum_vector_comm: 
    forall (dim:nat) (v1 v2: vector dim), 
      sum_vector _ v1 v2 ==v sum_vector _ v2 v1.
  Proof.
    apply sum_vector_comm with (eq:=eq) (plus:=plus).
    intros;ring.
  Qed.

  Lemma sum_vector_assoc: 
    forall (dim:nat) (v1 v2 v3: vector dim), 
      sum_vector _ (sum_vector _ v1 v2) v3 ==v
      sum_vector _ v1 (sum_vector _ v2 v3).
  Proof.
    apply sum_vector_assoc with (eq:=eq) (plus:=plus);intros;ring.
  Qed.

    (** scalar product of a vector *)
  
  Definition prod_scal_vec : 
    forall dim (a:A)(v:vector dim), 
      vector dim.
  Proof.
    apply (prod_scal_vec mult).
  Defined.
  
  #[global] Instance psv_morph dim :
    Proper (eq ==> eq_vec ==> eq_vec) (prod_scal_vec dim).
  Proof.
    apply (psv_morph eq_Equivalence) with (mult:=mult);intros. apply mult_morph;assumption.
  Qed.
  
      (** prod_scal_vec is distributive w.r.t sum of vectors *) 
  
  Lemma psv_distrib_left :
    forall dim c1 c2 (r:vector dim), 
      prod_scal_vec _ (plus c1 c2) r ==v
      sum_vector _ (prod_scal_vec  dim c1 r) (prod_scal_vec _ c2 r).
  Proof.
    apply psv_distrib_left with (eq:=eq) (plus:=plus) (mult:=mult);intros;ring.
  Qed.
  
  Lemma psv_distrib_right :
    forall dim c (r1 r2:vector dim), 
      prod_scal_vec _ c (sum_vector _ r1 r2)  ==v
      sum_vector _ (prod_scal_vec  dim c r1) (prod_scal_vec _ c r2).
  Proof.
    apply psv_distrib_right with (eq:=eq) (plus:=plus) (mult:=mult);intros;ring.
  Qed.

  Lemma psv_assoc :
    forall dim c1 c2 (r:vector dim), 
      prod_scal_vec _ c1  (prod_scal_vec _  c2 r) ==v 
      prod_scal_vec _ (mult c1 c2) r .
  Proof.
    apply (psv_assoc eq_Equivalence) with (mult:=mult); intros; ring.
  Qed.
  
  Lemma psv_comm : 
    forall dim (a1 a2:A) (v:vector dim), 
      prod_scal_vec _ a1 (prod_scal_vec _ a2 v) ==v
      prod_scal_vec _ a2 (prod_scal_vec _ a1 v).
  Proof.
    apply (psv_comm eq_Equivalence) with (mult:=mult);try (intros;ring).
    apply mult_morph. 
  Qed.

      (** product of a row by a column *)

  Definition prod_row_col : 
    forall dim (v1 v2:vector dim), A.
  Proof.
    apply (prod_row_col plus mult).
  Defined.


  #[global] Instance prc_morph dim : Proper (eq_vec ==> eq_vec ==> eq) (prod_row_col dim).
  Proof.
    apply prc_morph with (eq:=eq) (plus:=plus) (mult:=mult).
    apply eq_Equivalence.
    apply plus_morph.
    apply mult_morph.
  Qed.

      (* prod_row_col commutes with prod_scal_vec *)
  Lemma prc_comm_sv_right : 
    forall dim (r c : vector dim) (a:A), 
      prod_row_col _ r (prod_scal_vec _ a c) ==
      mult a  (prod_row_col _ r c).
  Proof.
    apply prc_comm_sv_right with (eq:=eq) (plus:=plus) (mult:=mult).
    apply eq_Equivalence.
    intros;ring.
    intros;ring.
    intros;ring.
    apply plus_morph.
    apply mult_morph.
  Qed.

  Lemma prc_comm_sv_left : 
    forall dim (r c : vector dim) (a:A), 
      prod_row_col _ (prod_scal_vec _ a r) c ==
      mult a  (prod_row_col _ r c).
  Proof.
    apply prc_comm_sv_left with (eq:=eq) (plus:=plus) (mult:=mult).
    apply eq_Equivalence.
    intros;ring.
    intros;ring.
    apply plus_morph.
  Qed.

      (* prod_row_col is distributive wrt vector sum *)
  Lemma prc_distrib_left :
    forall dim c1 c2 (r:vector dim), 
      prod_row_col _ (sum_vector _ c1  c2) r ==
      plus (prod_row_col  dim c1 r) (prod_row_col _ c2 r).
  Proof.
    apply prc_distrib_left with (eq:=eq) (plus:=plus) (mult:=mult).
    apply eq_Equivalence.
    intros;ring.
    intros;ring.
    intros;ring.
    apply plus_morph. 
  Qed.
  
  Lemma prc_distrib_right :
    forall dim c (r1 r2:vector dim), 
      prod_row_col _ c (sum_vector _ r1  r2) ==
      plus (prod_row_col  dim c r1) (prod_row_col _ c r2).
  Proof.
    apply prc_distrib_right with (eq:=eq) (plus:=plus) (mult:=mult).
    apply eq_Equivalence.
    intros;ring.
    intros;ring.
    intros;ring.
    apply plus_morph. 
  Qed.
  


(** The type a matrix. 
   A matrix of size (n+1) has the form: 
   
   a r
   c m
   
   where a is a coef 
   r is a vector of size n
   c is a vector of size n
   m is a matrix of size n
*)

  Definition matrix : nat -> Type. 
  Proof.
    apply (matrix A).
  Defined.

  Definition eq_mat {dim} : matrix dim -> matrix dim -> Prop.
  Proof.
    apply (@eq_mat _ eq).
  Defined.

  Local Notation "x ==m y" := (eq_mat x y) (at level 70, no associativity).

  Lemma eq_mat_refl dim : forall (v:matrix dim), v ==m v. 
  Proof.
    apply eq_mat_refl with (eq:=eq).
    apply eq_Equivalence.
  Qed.

  Lemma eq_mat_trans dim : forall (v1 v2 v3:matrix dim),
    v1 ==m v2 -> v2 ==m v3 -> v1 ==m v3.
  Proof.
    apply eq_mat_trans with (eq:=eq). apply eq_Equivalence.
  Qed.

  Lemma eq_mat_sym dim : forall (v1 v2:matrix dim),
    v1 ==m v2 -> v2 ==m v1.
  Proof.
    apply eq_mat_sym with (eq:=eq). apply eq_Equivalence.
  Qed.

  #[global] Instance eq_mat_Equivalence dim : Equivalence (@eq_mat dim).

  Proof. apply eq_mat_Equivalence. apply eq_Equivalence. Qed.

  (** sum of two matrix *)
  Ltac full_rewrite := 
    repeat match goal with 
             | H: _ == _ |- _ => try (rewrite H)||fail 1
             | H: _ ==v _ |- _ => try (rewrite H)|| fail 1
             | H: _ ==m _ |- _=> try (rewrite H)|| fail 1
           end.


  Definition sum_matrix : forall (dim:nat) (m1 m2:matrix dim), matrix dim.
  Proof.
    apply (sum_matrix plus). 
  Defined.

  #[global] Instance sum_matrix_morph dim :
    Proper (eq_mat ==> eq_mat ==> eq_mat) (sum_matrix dim).
  Proof.
    apply sum_matrix_morph with (eq:=eq) (plus:=plus).
    apply eq_Equivalence.
    apply plus_morph.
  Qed.

  
  (** 
     [create_mat a n] 
     return a matrix of size [n] with all elements equal 
     to [a]
     *)
  Definition create_mat : forall (n:nat) (a:A), matrix n.
  Proof.
    apply create_mat.
  Defined.

  #[global] Instance create_mat_morph dim : Proper (eq ==> eq_mat) (create_mat dim).
  Proof.
    apply create_mat_morph.
  Qed.


  (* sum of matrix is commutative *)
  Lemma sum_matrix_comm : 
    forall dim m1 m2, sum_matrix dim m1 m2 ==m sum_matrix dim m2 m1.
  Proof.
    apply sum_matrix_comm with (eq:=eq) (plus:=plus).
    intros;ring.
  Qed.

  Lemma sum_matrix_assoc : 
    forall dim m1 m2 m3, 
      sum_matrix dim (sum_matrix _ m1 m2) m3 ==m 
      sum_matrix dim m1 (sum_matrix _ m2 m3).
  Proof.
    apply sum_matrix_assoc with (eq:=eq) (plus:=plus).
    intros;ring.
  Qed.

  (** scalar product for matrices *)
  Definition prod_scal_mat : 
    forall dim (a:A)(v:matrix dim), 
      matrix dim.
  Proof.
    apply prod_scal_mat.
    apply mult.
  Defined.

  #[global] Instance psm_morph dim :
    Proper (eq ==> eq_mat ==> eq_mat) (prod_scal_mat dim).
  Proof.
    apply psm_morph with (eq:=eq) (mult:=mult).
    apply eq_Equivalence.
    apply mult_morph.
  Qed.
  
  (** prod_scal_mat is distributive w.r.t sum of vectors *) 
  
  Lemma psm_distrib_left :
    forall dim c1 c2 (m:matrix dim), 
      prod_scal_mat _ (plus c1 c2) m ==m
      sum_matrix _ 
      (prod_scal_mat  dim c1 m)
      (prod_scal_mat _ c2 m).
  Proof.
    apply psm_distrib_left with (eq:=eq) (plus:=plus) (mult:=mult).
    intros;ring.
  Qed.
  
  Lemma psm_distrib_right :
    forall dim c (r1 r2:matrix dim), 
      prod_scal_mat _ c (sum_matrix _ r1 r2) ==m 
      sum_matrix _ (prod_scal_mat  dim c r1) (prod_scal_mat _ c r2).
  Proof.
    apply psm_distrib_right with (eq:=eq) (plus:=plus) (mult:=mult).
    intros;ring.
  Qed.

  Lemma psm_assoc :
    forall dim c1 c2 (r:matrix dim), 
      prod_scal_mat _ c1  (prod_scal_mat _  c2 r) ==m 
      prod_scal_mat _ (mult c1 c2) r .
  Proof.
    apply psm_assoc with (eq:=eq) (mult:=mult).
    apply eq_Equivalence.
    intros;ring.
  Qed.
  
  Lemma psm_comm : 
    forall dim (a1 a2:A) (v:matrix dim), 
      prod_scal_mat _ a1 (prod_scal_mat _ a2 v) ==m 
      prod_scal_mat _ a2 (prod_scal_mat _ a1 v).
  Proof.
    apply psm_comm with (eq:=eq) (mult:=mult).
    apply eq_Equivalence.
    intros;ring.
    intros;ring.
    apply mult_morph.
  Qed.

  (* product of a col by a row *)
  Definition prod_col_row : forall (dim:nat) (c r:vector dim), matrix dim.
  Proof.
    apply (prod_col_row mult).
  Defined.

  #[global] Instance pcr_morph dim :
    Proper (eq_vec ==> eq_vec ==> eq_mat) (prod_col_row dim).
  Proof.
    apply pcr_morph with (eq:=eq) (mult:=mult).
    apply eq_Equivalence.
    apply mult_morph.
  Qed.

  Lemma pcr_comm_sv_right : 
    forall dim (c r : vector dim) (a:A), 
      prod_col_row _ c (prod_scal_vec _ a r) ==m 
      prod_scal_mat _ a  (prod_col_row _ c r).
  Proof.
    apply pcr_comm_sv_right with (eq:=eq) (mult:=mult).
    apply eq_Equivalence.
    intros;ring.
    intros;ring.
    apply mult_morph.
  Qed.

  Lemma pcr_comm_sv_left : 
    forall dim (c r : vector dim) (a:A), 
      prod_col_row _ (prod_scal_vec _ a r) c ==m
      prod_scal_mat _ a  (prod_col_row _ r c).
  Proof.
    apply pcr_comm_sv_left with (eq:=eq) (mult:=mult).
    apply eq_Equivalence.
    intros;ring.
    intros;ring.
    apply mult_morph.
  Qed.

  (* prod_row_col is distributive wrt vector sum *)
  Lemma pcr_distrib_left :
    forall dim c1 c2 (r:vector dim), 
      prod_col_row _ (sum_vector _ c1  c2) r ==m
      sum_matrix _
      (prod_col_row dim c1 r) (prod_col_row _ c2 r).
  Proof.
    apply pcr_distrib_left with (eq:=eq) (plus:=plus) (mult:=mult).
    intros;ring.
    intros;ring.
  Qed.
  
  Lemma pcr_distrib_right :
    forall dim c (r1 r2:vector dim), 
      prod_col_row _ c (sum_vector _ r1  r2) ==m
      sum_matrix _ (prod_col_row  dim c r1) (prod_col_row _ c r2).
  Proof.
    apply pcr_distrib_right with (eq:=eq) (plus:=plus) (mult:=mult).
    intros;ring.
    intros;ring.
  Qed.

  (** product of a row by a matrix *)
  
  Definition prod_row_mat : forall (dim:nat) (r:vector dim) (m:matrix dim), vector dim.
  Proof.
    apply (prod_row_mat plus mult).
  Defined.

  #[global] Instance prm_morph dim :
    Proper (eq_vec ==> eq_mat ==> eq_vec) (prod_row_mat dim).
  Proof.
    apply prm_morph with (eq:=eq) (plus:=plus) (mult:=mult).
    apply eq_Equivalence.
    apply plus_morph.
    apply mult_morph.
  Qed.

  Lemma prm_comm_sv_right : 
    forall dim (r : vector dim) (m:matrix dim) (a:A), 
      prod_row_mat _ r (prod_scal_mat _ a m) ==v 
      prod_scal_vec _ a  (prod_row_mat _ r m).
  Proof.
    apply prm_comm_sv_right with (eq:=eq) (plus:=plus) (mult:=mult).
    apply eq_Equivalence.
    intros;ring.
    intros;ring.
    intros;ring.
    apply plus_morph.
    apply mult_morph.
  Qed.

  Lemma prm_comm_sv_left : 
    forall dim (r : vector dim) (m:matrix dim) (a:A), 
      prod_row_mat _ (prod_scal_vec _ a r) m ==v
      prod_scal_vec _ a  (prod_row_mat _ r m).
  Proof.
    apply prm_comm_sv_left with (eq:=eq) (plus:=plus) (mult:=mult).
    apply eq_Equivalence.
    intros;ring.
    intros;ring.
    apply plus_morph.
  Qed.

  (* prod_row_col is distributive wrt vector sum *)
  Lemma prm_distrib_left :
    forall dim r1 r2 (m:matrix dim), 
      prod_row_mat _ (sum_vector _ r1 r2) m ==v 
      sum_vector _
      (prod_row_mat dim r1 m) (prod_row_mat _ r2 m).
  Proof.
    apply prm_distrib_left with (eq:=eq) (plus:=plus) (mult:=mult).
    apply eq_Equivalence.
    intros;ring.
    intros;ring.
    intros;ring.
    apply plus_morph.
  Qed.
  
  Lemma prm_distrib_right :
    forall dim r (m1 m2:matrix dim), 
      prod_row_mat _ r (sum_matrix _ m1  m2) ==v 
      sum_vector _ (prod_row_mat  dim r m1) (prod_row_mat _ r m2).
  Proof.
    apply prm_distrib_right with (eq:=eq) (plus:=plus) (mult:=mult).
    apply eq_Equivalence.
    intros;ring.
    intros;ring.
    intros;ring.
    apply plus_morph.
  Qed.

  (** product of a matrix by a column *)
  
  Definition prod_mat_col : forall (dim:nat) (m:matrix dim) (c:vector dim), vector dim.
  Proof.
    apply (prod_mat_col plus mult).
  Defined.

  #[global] Instance pmc_morph dim :
    Proper (eq_mat ==> eq_vec ==> eq_vec) (prod_mat_col dim).
  Proof.
    apply pmc_morph with (eq:=eq) (plus:=plus) (mult:=mult).
    apply eq_Equivalence.
    apply plus_morph.
    apply mult_morph.
  Qed.

  Lemma pmc_comm_sv_right : 
    forall dim (m:matrix dim) (c : vector dim) (a:A), 
      prod_mat_col _ m (prod_scal_vec _ a c) ==v 
      prod_scal_vec _ a  (prod_mat_col _ m c).
  Proof.
    apply pmc_comm_sv_right with (eq:=eq) (plus:=plus) (mult:=mult).
    apply eq_Equivalence.
    intros;ring.
    intros;ring.
    intros;ring.
    apply plus_morph.
    apply mult_morph.
  Qed.

  Lemma pmc_comm_sv_left : 
    forall dim (m:matrix dim) (c : vector dim)  (a:A), 
      prod_mat_col _ (prod_scal_mat _ a m) c ==v 
      prod_scal_vec _ a  (prod_mat_col _ m c).
  Proof.
    apply pmc_comm_sv_left with (eq:=eq) (plus:=plus) (mult:=mult).
    apply eq_Equivalence.
    intros;ring.
    intros;ring.
    intros;ring.
    apply plus_morph.
    apply mult_morph.
  Qed.

  (* prod_row_col is distributive wrt vector sum *)
  Lemma pmc_distrib_left :
    forall dim m1 m2 (c:vector dim), 
      prod_mat_col _ (sum_matrix _ m1 m2) c ==v 
      sum_vector _
      (prod_mat_col dim m1 c) (prod_mat_col _ m2 c).
  Proof.
    apply pmc_distrib_left with (eq:=eq) (plus:=plus) (mult:=mult).
    apply eq_Equivalence.
    intros;ring.
    intros;ring.
    intros;ring.
    intros;ring.
    apply plus_morph.
  Qed.
  
  Lemma pmc_distrib_right :
    forall dim m (c1 c2:vector dim), 
      prod_mat_col _ m (sum_vector _ c1  c2) ==v
      sum_vector _ (prod_mat_col  dim m c1) (prod_mat_col _ m c2).
  Proof.
    apply pmc_distrib_right with (eq:=eq) (plus:=plus) (mult:=mult).
    apply eq_Equivalence.
    intros;ring.
    intros;ring.
    intros;ring.
    intros;ring.
    apply plus_morph.
  Qed.

  (** 
     product of two matrices 
     *)

  Definition prod_matrix : forall (dim:nat) (m1 m2:matrix dim), matrix dim. 
  Proof.
    apply (prod_matrix plus mult).
  Defined.

  #[global] Instance pm_morph dim :
    Proper (eq_mat ==> eq_mat ==> eq_mat) (prod_matrix dim).
  Proof.
    apply pm_morph with (eq:=eq) (plus:=plus) (mult:=mult).
    apply eq_Equivalence.
    apply plus_morph.
    apply mult_morph.
  Qed.

  Lemma pm_comm_sv_right : 
    forall dim (m1 m2:matrix dim) (a:A), 
      prod_matrix _ (prod_scal_mat _ a m1) m2 ==m
      prod_scal_mat _ a  (prod_matrix _ m1 m2).
  Proof.
    apply pm_comm_sv_right with (eq:=eq) (plus:=plus) (mult:=mult).
    apply eq_Equivalence.
    intros;ring.
    intros;ring.
    intros;ring.
    apply plus_morph.
    apply mult_morph.
  Qed.

  Lemma pm_comm_sv_left : 
    forall dim (m1 m2:matrix dim) (a:A), 
      prod_matrix _ m1 (prod_scal_mat _ a m2) ==m
      prod_scal_mat _ a  (prod_matrix _ m1 m2).
  Proof.
    apply pm_comm_sv_left with (eq:=eq) (plus:=plus) (mult:=mult).
    apply eq_Equivalence.
    intros;ring.
    intros;ring.
    intros;ring.
    apply plus_morph.
    apply mult_morph.
  Qed.

  (* prod_matrix is distributive wrt matrix sum *)
  Lemma pm_distrib_left :
    forall dim m1 m2 (m3:matrix dim), 
      prod_matrix _ (sum_matrix _ m1 m2) m3 ==m 
      sum_matrix _
      (prod_matrix dim m1 m3) (prod_matrix _ m2 m3).
  Proof.
    apply pm_distrib_left with (eq:=eq) (plus:=plus) (mult:=mult).
    apply eq_Equivalence.
    intros;ring.
    intros;ring.
    intros;ring.
    intros;ring.
    apply plus_morph.
    apply mult_morph.
  Qed.

  Lemma pm_distrib_right :
    forall dim m1 m2 (m3:matrix dim), 
      prod_matrix _ m1 (sum_matrix _ m2 m3) ==m 
      sum_matrix _
      (prod_matrix dim m1 m2) (prod_matrix _ m1 m3).
  Proof.
    apply pm_distrib_right with (eq:=eq) (plus:=plus) (mult:=mult).
    apply eq_Equivalence.
    intros;ring.
    intros;ring.
    intros;ring.
    intros;ring.
    apply plus_morph.
  Qed.

  Lemma prm_pmc_comm : 
    forall dim r m c, 
      prod_row_col dim (prod_row_mat _ r m) c == 
      prod_row_col dim r (prod_mat_col _ m c).
  Proof.
    apply prm_pmc_comm with (eq:=eq) (plus:=plus) (mult:=mult).
    apply eq_Equivalence.
    intros;ring.
    intros;ring.
    intros;ring.
    intros;ring.
    intros;ring.
    intros;ring.
    apply plus_morph.
    apply mult_morph.
  Qed.

  Lemma pcr_prc_comm : 
    forall dim c1 r c2, 
      prod_mat_col dim (prod_col_row _ c1 r) c2 ==v  
      prod_scal_vec _ (prod_row_col _ r c2) c1.
  Proof.
    apply pcr_prc_comm with (eq:=eq) (plus:=plus) (mult:=mult).
    apply eq_Equivalence.
    intros;ring.
    intros;ring.
    intros;ring.
    intros;ring.
    apply plus_morph.
    apply mult_morph.
  Qed.
    
  Lemma pm_assoc_pmc : 
    forall dim m1 m2 c, 
    prod_mat_col dim m1 (prod_mat_col _ m2 c) ==v 
    prod_mat_col _ (prod_matrix _ m1 m2) c. 
  Proof.
    apply pm_assoc_pmc with (eq:=eq) (plus:=plus) (mult:=mult).
    apply eq_Equivalence.
    intros;ring.
    intros;ring.
    intros;ring.
    intros;ring.
    intros;ring.
    intros;ring.
    apply plus_morph.
    apply mult_morph.
  Qed.

  Definition null_vector dim := create_vec dim rO.
  Definition null_matrix dim := create_mat dim rO.

  Lemma rO_nullify_psv : 
    forall dim v, prod_scal_vec _ rO v ==v null_vector dim .
  Proof.
    induction dim.
    intros; vm_compute;ring.
    unfold null_vector in *;simpl;intros [a v]. 
    rewrite IHdim. split;try ring. reflexivity.
  Qed.
    

  Lemma rI_neutral_psv : 
    forall dim v, prod_scal_vec dim rI v ==v v.
  Proof.
    induction dim.
    intros; vm_compute;ring.
    unfold null_vector in *;simpl;intros [a v]. 
    rewrite IHdim. split;try ring. reflexivity.
  Qed.

  Lemma nv_nullify_psv : 
    forall dim a, prod_scal_vec _ a (null_vector _)  ==v null_vector dim .
  Proof.
    induction dim.
    intros; vm_compute;ring.
    unfold null_vector in *;simpl;intros a. 
    rewrite IHdim. split;try ring. reflexivity.
  Qed.

  Lemma nv_neutral_left_sv : 
    forall dim v, sum_vector dim  (null_vector dim) v ==v v.
  Proof.
    induction dim.
    simpl. unfold null_vector. simpl. intros;ring.
    simpl.
    intros [a v].
    split;try ring.
    apply IHdim.
  Qed.

  Lemma nv_neutral_right_sv : 
    forall dim v, sum_vector dim v (null_vector dim) ==v v.
  Proof.
    induction dim.
    simpl. unfold null_vector. simpl. intros;ring.
    simpl.
    intros [a v].
    split;try ring.
    apply IHdim.
  Qed.

  Lemma nv_nullify_prc_left : 
    forall dim c, prod_row_col _ (null_vector dim) c == rO.
  Proof.
    induction dim.
    vm_compute;intros. ring.

    simpl. intros [a v].
    rewrite IHdim. ring.
  Qed.

  Lemma nv_nullify_prc_right : 
    forall dim r, prod_row_col _ r (null_vector dim) == rO.
  Proof.
    induction dim.
    vm_compute;intros. ring.

    simpl. intros [a v]. 
    unfold null_vector;simpl.
    rewrite IHdim. ring.
  Qed.


  Lemma rO_nullify_psm : 
    forall dim v, prod_scal_mat _ rO v ==m null_matrix dim .
  Proof.
    induction dim.
    intros; vm_compute;ring.
    unfold null_matrix in *;simpl;intros [a [r[c m]]]. 
    rewrite IHdim. repeat split;try ring. 
    apply rO_nullify_psv.
    apply rO_nullify_psv.
    reflexivity.
  Qed.
    

  Lemma rI_neutral_psm : 
    forall dim m, prod_scal_mat dim rI m ==m m.
  Proof.
    induction dim.
    intros; vm_compute;ring.
    unfold null_matrix in *;simpl;intros [a [r [c m]]]. 
    rewrite IHdim. repeat split;try ring. 
    apply rI_neutral_psv. 
    apply rI_neutral_psv. 
    reflexivity.
  Qed.

  Lemma nm_nullify_psm : 
    forall dim a, prod_scal_mat _ a (null_matrix _)  ==m null_matrix dim .
  Proof.
    induction dim.
    intros; vm_compute;ring.
    unfold null_matrix in *;simpl;intros a. 
    rewrite IHdim. repeat split;try ring. 
    apply nv_nullify_psv. 
    apply nv_nullify_psv. 
    reflexivity.
  Qed.

  Lemma nv_nullify_pcr_left : 
    forall dim c, prod_col_row _ (null_vector dim) c ==m (null_matrix dim).
  Proof.
    induction dim.
    vm_compute;intros. ring.

    simpl. intros [a v]. 
    unfold null_matrix;simpl.
    rewrite IHdim. 
    repeat split. ring.
    apply rO_nullify_psv.
    apply nv_nullify_psv.
    reflexivity.
  Qed.

  Lemma nv_nullify_pcr_right : 
    forall dim r, prod_col_row _ r (null_vector dim) ==m (null_matrix dim).
  Proof.
    induction dim.
    vm_compute;intros. ring.

    simpl. intros [a v]. 
    unfold null_vector;simpl.
    repeat split.
    ring.
    rewrite nv_nullify_psv. reflexivity.
    rewrite rO_nullify_psv;reflexivity.
    rewrite IHdim. reflexivity.
  Qed.

  Lemma nm_nullify_prm : 
    forall dim v, prod_row_mat _ v (null_matrix _)  ==v null_vector dim .
  Proof.
    induction dim.
    intros; vm_compute;ring.
    unfold null_matrix,null_vector in *;simpl;intros [a v]. 
    rewrite IHdim. repeat split. 
    rewrite nv_nullify_prc_right. ring.
    rewrite nv_nullify_psv. 
    rewrite nv_neutral_right_sv. reflexivity.
  Qed.

  Lemma nv_nullify_prm : 
    forall dim m, prod_row_mat _ (null_vector _) m  ==v null_vector dim .
  Proof.
    induction dim.
    intros; vm_compute;ring.
    unfold null_matrix,null_vector in *;simpl;intros [a [r [c m]]]. 
    rewrite IHdim. repeat split. 
    rewrite nv_nullify_prc_left. ring.
    rewrite rO_nullify_psv. 
    rewrite nv_neutral_left_sv. reflexivity.
  Qed.

  Lemma nm_nullify_pmc : 
    forall dim v, prod_mat_col _ (null_matrix _) v  ==v null_vector dim .
  Proof.
    induction dim.
    intros; vm_compute;ring.
    unfold null_matrix,null_vector in *;simpl;intros [a v]. 
    rewrite IHdim. repeat split. 
    rewrite nv_nullify_prc_left. ring.
    rewrite nv_nullify_psv. 
    rewrite nv_neutral_right_sv. reflexivity.
  Qed.

  Lemma nv_nullify_pmc : 
    forall dim m, prod_mat_col _ m (null_vector _) ==v null_vector dim .
  Proof.
    induction dim.
    intros; vm_compute;ring.
    unfold null_matrix,null_vector in *;simpl;intros [a [r [c m]]]. 
    rewrite IHdim. repeat split. 
    rewrite nv_nullify_prc_right. ring.
    rewrite rO_nullify_psv. 
    rewrite nv_neutral_left_sv. reflexivity.
  Qed.

  Lemma nm_neutral_left_sum_matrix : 
    forall dim v, sum_matrix dim  (null_matrix dim) v ==m v.
  Proof.
    induction dim.
    simpl. unfold null_matrix. simpl. intros;ring.
    simpl.
    intros [a [r [c m]]].
    repeat split;try ring.
    apply nv_neutral_left_sv.
    apply nv_neutral_left_sv.
    apply IHdim.
  Qed.

  Lemma nm_neutral_right_sum_matrix : 
    forall dim v, sum_matrix dim v  (null_matrix dim) ==m v.
  Proof.
    induction dim.
    simpl. unfold null_matrix. simpl. intros;ring.
    simpl.
    intros [a [r [c m]]].
    repeat split;try ring.
    apply nv_neutral_right_sv.
    apply nv_neutral_right_sv.
    apply IHdim.
  Qed.

  Definition id_matrix : forall dim, matrix dim .
  Proof.
    fix id_matrix 1.
    intros [|dim].
    exact rI.
    simpl.
    constructor;[|constructor;[|constructor]].
    exact rI.
    exact (null_vector dim).
    exact (null_vector dim).
    exact (id_matrix dim).
  Defined.

  Lemma im_neutral_pmc : 
    forall dim c, prod_mat_col _ (id_matrix dim) c ==v c.
  Proof.
    induction dim.
    simpl;intros;ring.

    simpl.
    unfold null_vector;intros [a v].
    split.
   
    rewrite nv_nullify_prc_left. ring.

    rewrite nv_nullify_psv. rewrite nv_neutral_left_sv. rewrite IHdim. reflexivity. 
  Qed.


  Lemma im_neutral_prm : 
    forall dim c, prod_row_mat _ c (id_matrix dim) ==v c.
  Proof.
    induction dim.
    simpl;intros;ring.

    simpl.
    unfold null_vector;intros [a v].
    split.
   
    rewrite nv_nullify_prc_right. ring.

    rewrite nv_nullify_psv. rewrite nv_neutral_left_sv. rewrite IHdim. reflexivity. 
  Qed.

  Lemma id_matrix_neutral_left_pm : 
    forall dim m, prod_matrix dim  (id_matrix dim) m ==m m.
  Proof.
    induction dim.
    simpl. unfold null_matrix. simpl. intros;ring.
    simpl.
    intros [a [r [c m]]].
    repeat split. 

    rewrite (nv_nullify_prc_left);ring.

    rewrite rI_neutral_psv.
    rewrite nv_nullify_prm.
    rewrite nv_neutral_right_sv.
    reflexivity.
  
    rewrite nv_nullify_psv.
    rewrite nv_neutral_left_sv.
    rewrite im_neutral_pmc.
    reflexivity.


    rewrite nv_nullify_pcr_left.
    rewrite nm_neutral_left_sum_matrix.
    apply IHdim.
  Qed.

  Lemma id_matrix_neutral_right_pm : 
    forall dim m, prod_matrix dim m  (id_matrix dim) ==m m.
  Proof.
    induction dim.
    simpl. unfold null_matrix. simpl. intros;ring.
    simpl.
    intros [a [r [c m]]].
    repeat split. 

    rewrite (nv_nullify_prc_right);ring.

    rewrite nv_nullify_psv.
    rewrite nv_neutral_left_sv.
    rewrite im_neutral_prm.
    reflexivity.
  
    rewrite nv_nullify_pmc.
    rewrite nv_neutral_right_sv.
    rewrite rI_neutral_psv. reflexivity.

    rewrite nv_nullify_pcr_right.
    rewrite nm_neutral_left_sum_matrix.
    apply IHdim.
  Qed.

End Make.



Module Type Ordered_Ring. 
  Include TRing.
  Parameter lt le : A -> A -> Prop.
  Parameter o : ordering_pair eq lt le.
  Parameter lt_wf : well_founded lt.
End Ordered_Ring.


Module Make_Ordered(R:Ordered_Ring).
  Import R.
  Include Make(R). 

  #[global] Instance lt_morph : Proper (eq ==> eq ==> iff) lt.
  Proof.
    exact o.(lt_morph).
  Qed.
  #[global] Instance le_morph : Proper (eq ==> eq ==> iff) le.
  Proof.
    exact o.(le_morph).
  Qed.

  Definition vec_order_large : forall dim, vector dim -> vector dim -> Prop.
  Proof.
    fix vec_order_large 1;intros [|dim].
    exact le.
    simpl;intros [a1 v1] [a2 v2]. 
    refine (and _ _).
    exact (le a1 a2).
    apply (vec_order_large _ v1 v2).
  Defined.

  Definition vec_order_strict : forall dim, vector dim -> vector dim -> Prop.
  Proof.
    fix vec_order_strict 1;intros [|dim].
    exact lt.
    simpl;intros [a1 v1] [a2 v2]. 
    refine (and _ _).
    exact (lt a1 a2).
    apply (vec_order_large _ v1 v2).
  Defined.


  Lemma vec_order_large_morph dim : 
    forall x x' : vector dim, eq_vec x x' -> forall y y', eq_vec y y' -> 
      (vec_order_large _ x y <-> vec_order_large _ x' y').
  Proof.
    induction dim.
    simpl. 
    intros.
    rewrite H;rewrite H0;reflexivity.

    simpl. intros [a1 v1] [a1' v1'] [Heq1 Heq2] [a2 v2] [a2' v2'] [Heq3 Heq4].
    rewrite Heq1;rewrite Heq3.
    destruct (IHdim _ _ Heq2 _ _ Heq4) as [IH1 IH2].
    intuition.
  Defined.

  #[global] Instance vol_morph dim :
    Proper (eq_vec ==> eq_vec ==> iff) (vec_order_large dim).
  Proof.
    intros a b ab c d cd. apply vec_order_large_morph; assumption.
  Qed.

  Lemma vec_order_strict_morph dim : 
    forall x x' : vector dim, eq_vec x x' -> forall y y', eq_vec y y' -> 
      (vec_order_strict _ x y <-> vec_order_strict _ x' y').
  Proof.
    induction dim.
    simpl. 
    intros.
    rewrite H;rewrite H0;reflexivity.

    simpl. intros [a1 v1] [a1' v1'] [Heq1 Heq2] [a2 v2] [a2' v2'] [Heq3 Heq4].
    rewrite Heq1;rewrite Heq3.
    destruct (IHdim _ _ Heq2 _ _ Heq4) as [IH1 IH2].
    rewrite Heq2.
    rewrite Heq4. 
    intuition.
  Defined.

  #[global] Instance vos_morph dim :
    Proper (eq_vec ==> eq_vec ==> iff) (vec_order_strict dim).
  Proof.
    intros a b ab c d cd. apply vec_order_strict_morph; assumption.
  Qed.

  Lemma vec_order_large_refl dim: 
    forall x, vec_order_large dim x x.
  Proof.
    induction dim.
    simpl. apply o.(le_refl).
    simpl;intros [a v];split;[apply o.(le_refl)|apply IHdim].
  Defined.

  Lemma vec_order_large_trans dim  : 
    forall v1 v2 v3, vec_order_large dim v1 v2 -> vec_order_large _ v2 v3 -> 
      vec_order_large _ v1 v3.
  Proof.
    induction dim.
    simpl. 
    intros. apply o.(le_trans) with v2; assumption.
    simpl;intros [a1 v1] [a2 v2] [a3 v3] [H1 H2] [H3 H4];split.
    apply o.(le_trans) with a2;assumption.
    apply IHdim with v2;assumption.
  Defined.
    

  Definition o_vec : forall dim, ordering_pair eq_vec (vec_order_strict dim) (vec_order_large dim).
  Proof.
    intros.
    apply mk_ordering_pair.
    (* vector_strict morph *)
    destruct dim as [|dim].
    simpl.
    intros x x' Heq1 y y' Heq2;rewrite Heq1;rewrite Heq2;reflexivity.
    simpl;intros [a1 v1] [a1' v1'] [Heq1 Heq2] [a2 v2] [a2' v2'] [Heq3 Heq4]. 
    rewrite Heq1; rewrite Heq3;rewrite (vec_order_large_morph _ _ _ Heq2 _ _ Heq4).
    reflexivity.
    (* lt irrefl *)
    destruct dim as [|dim].
    simpl. apply o.(lt_irrefl).
    simpl;intros [a v]. intros [abs _].
    apply (o.(lt_irrefl) _ abs).
    (* lt_antisym *)
    destruct dim as [|dim].
    simpl. intros x y H. apply (o.(lt_antisym) _ _ H).
    simpl;intros [a1 v1] [a2 v2] [H1 _].
    intros [abs _]. 
    apply (o.(lt_antisym) _ _ H1 abs).
    (* lt_trans *)
    destruct dim as [|dim].
    simpl. intros x y z H1 H2. apply o.(lt_trans) with y;assumption.
    simpl. intros [a1 v1] [a2 v2] [a3 v3] [H1 H2] [H3 H4];split.
    apply o.(lt_trans) with a2;assumption.
    apply vec_order_large_trans with v2;assumption.
    (* le morph *) 
    apply vec_order_large_morph.
    (* le_refl *)
    apply vec_order_large_refl.
    (* le antisym *)
    induction dim.
    simpl.
    apply o.(le_antisym).
    simpl;intros [a1 v1] [a2 v2] [H1 H2] [H3 H4];split.
    apply o.(le_antisym);assumption.
    apply IHdim;assumption.
    (* le trans *)
    apply vec_order_large_trans.
    (* le_lt_compat_left *)
    destruct dim as [|dim].
    simpl. apply o.(le_lt_compat_left).
    simpl;intros [a1 v1] [a2 v2] [a3 v3] [H1 H2] [H3 H4];split.
    apply o.(le_lt_compat_left) with a2;assumption.
    apply vec_order_large_trans with v2;assumption.
    (* le_lt_compat_right *)
    destruct dim as [|dim].
    simpl. apply o.(le_lt_compat_right).
    simpl;intros [a1 v1] [a2 v2] [a3 v3] [H1 H2] [H3 H4];split.
    apply o.(le_lt_compat_right) with a2;assumption.
    apply vec_order_large_trans with v2;assumption.
    (* lt_included_le *)
    destruct dim.
    simpl;apply o.(lt_included_le).
    simpl; intros [a1 v1] [a2 v2] [H1 H2];split.
    apply o.(lt_included_le);assumption.
    assumption.
  Defined.
    
  Lemma vec_order_strict_wf : 
    forall dim, well_founded (vec_order_strict dim).
  Proof.
    destruct dim as [|dim].
    simpl. apply lt_wf.
    simpl. intros [a v].
    revert v.
    pattern a.
    apply well_founded_ind with (1:=lt_wf). 
    clear a.
    intros a1 IHa1 v1.
    constructor.
    intros [a2 v2] [H1 _].
    apply IHa1 ; assumption.
  Qed.    

(********)


  Definition mat_order_large : forall dim, matrix dim -> matrix dim -> Prop.
  Proof.
    fix mat_order_large 1;intros [|dim].
    exact le.
    simpl;intros [a1 [l1 [c1 m1]]] [a2 [l2 [c2 m2]]]. 
    refine (and _ (and _ (and _ _))).
    exact (le a1 a2).
    apply (vec_order_large _ l1 l2).
    apply (vec_order_large _ c1 c2).
    apply (mat_order_large _ m1 m2).
  Defined.

  Definition mat_order_strict : forall dim, matrix dim -> matrix dim -> Prop.
  Proof.
    fix mat_order_strict 1;intros [|dim].
    exact lt.
    simpl;intros [a1 [l1 [c1 m1]]] [a2 [l2 [c2 m2]]]. 
    refine (and _ (and _ (and _ _))).
    exact (lt a1 a2).
    apply (vec_order_large _ l1 l2).
    apply (vec_order_large _ c1 c2).
    apply (mat_order_large _ m1 m2).
  Defined.


  Lemma mat_order_large_morph dim  : 
    forall x x' : matrix dim, eq_mat x x' -> forall y y', eq_mat y y' -> 
      (mat_order_large _ x y <-> mat_order_large _ x' y').
  Proof.
    induction dim.
    simpl. 
    intros.
    rewrite H;rewrite H0;reflexivity.

    simpl. intros [a1 [l1 [c1 m1]]] [a1' [l1' [c1' m1']]] [Heq1 [Heq2 [Heq3 Heq4]]]  [a2 [l2 [c2 m2]]] 
    [a2' [l2' [c2' m2']]] [Heq5 [Heq6 [Heq7 Heq8]]].
    rewrite Heq1;rewrite Heq5.
    destruct (IHdim _ _ Heq4 _ _ Heq8) as [IH1 IH2].
    rewrite Heq2; rewrite Heq3; rewrite Heq7; rewrite Heq6.
    intuition.
  Defined.

  #[global] Instance mol_morph dim :
    Proper (eq_mat ==> eq_mat ==> iff) (mat_order_large dim).
  Proof.
    intros a b ab c d cd. apply mat_order_large_morph; assumption.
  Qed.

  Lemma mat_order_strict_morph dim : 
    forall x x' : matrix dim, eq_mat x x' -> forall y y', eq_mat y y' -> 
      (mat_order_strict _ x y <-> mat_order_strict _ x' y').
  Proof.
    induction dim.
    simpl. 
    intros.
    rewrite H;rewrite H0;reflexivity.

    simpl. intros [a1 [l1 [c1 m1]]] [a1' [l1' [c1' m1']]] [Heq1 [Heq2 [Heq3 Heq4]]]  [a2 [l2 [c2 m2]]] 
    [a2' [l2' [c2' m2']]] [Heq5 [Heq6 [Heq7 Heq8]]].
    rewrite Heq1;rewrite Heq5.
    destruct (IHdim _ _ Heq4 _ _ Heq8) as [IH1 IH2].
    rewrite Heq2; rewrite Heq3; rewrite Heq7; rewrite Heq6.
    intuition.
    rewrite <- Heq8;rewrite <- Heq4;assumption.
    rewrite  Heq8;rewrite Heq4;assumption.
  Defined.

  #[global] Instance mos_morph dim :
    Proper (eq_mat ==> eq_mat ==> iff) (mat_order_strict dim).
  Proof.
    intros a b ab c d cd. apply mat_order_strict_morph; assumption.
  Qed.

  Lemma mat_order_large_refl dim: 
    forall x, mat_order_large dim x x.
  Proof.
    induction dim.
    simpl. apply o.(le_refl).
    simpl;intros [a [c [l v]]];repeat split. apply o.(le_refl). 
    apply (o_vec dim).(le_refl). 
    apply (o_vec dim).(le_refl). 
    apply IHdim.
  Defined.

  Lemma mat_order_large_trans dim  : 
    forall v1 v2 v3, mat_order_large dim v1 v2 -> mat_order_large _ v2 v3 -> 
      mat_order_large _ v1 v3.
  Proof.
    induction dim.
    simpl. 
    intros. apply o.(le_trans) with v2; assumption.
    simpl;intros [a1 [l1 [c1 m1]]] [a2 [l2 [c2 m2]]] [a3 [l3 [c3 m3]]] [H1 [H2 [H3 H4]]] 
      [H5 [H6 [H7 H8]]];repeat split.
    apply o.(le_trans) with a2;assumption.
    apply (o_vec dim).(le_trans) with l2;assumption.
    apply (o_vec dim).(le_trans) with c2;assumption.
    apply IHdim with m2;assumption.
  Defined.
    

  Definition o_mat : forall dim, ordering_pair eq_mat (mat_order_strict dim) (mat_order_large dim).
  Proof.
    intros.
    apply mk_ordering_pair.
    (* vector_strict morph *)
    destruct dim as [|dim].
    simpl.
    intros x x' Heq1 y y' Heq2;rewrite Heq1;rewrite Heq2;reflexivity.
    simpl;intros [a1 [l1 [c1 m1]]] [a1' [l1' [c1' m1']]] [Heq1 [Heq2 [Heq3 Heq4]]] 
      [a2 [l2 [c2 m2]]] [a2' [c2' [l2' m2']]] [Heq5 [Heq6 [Heq7 Heq8]]]. 
    rewrite Heq1; rewrite Heq2; rewrite Heq3;
    rewrite Heq5; rewrite Heq6; rewrite Heq7;
      rewrite (mat_order_large_morph _ _ _ Heq4 _ _ Heq8).
    reflexivity.
    (* lt irrefl *)
    destruct dim as [|dim].
    simpl. apply o.(lt_irrefl).
    simpl;intros [a [c [l m]]]. intros [abs _].
    apply (o.(lt_irrefl) _ abs).
    (* lt_antisym *)
    destruct dim as [|dim].
    simpl. intros x y H. apply (o.(lt_antisym) _ _ H).
    simpl;intros [a1 [l1 [c1 m1]]] [a2 [l2 [c2 m2]]] [H1 _].
    intros [abs _]. 
    apply (o.(lt_antisym) _ _ H1 abs).
    (* lt_trans *)
    destruct dim as [|dim].
    simpl. intros x y z H1 H2. apply o.(lt_trans) with y;assumption.
    simpl. intros [a1 [l1 [c1 m1]]] [a2 [l2 [c2 m2]]] [a3 [l3 [c3 m3]]] 
    [H1 [H2 [H3 H4]]] [H5 [H6 [H7 H8]]];repeat split.
    apply o.(lt_trans) with a2;assumption.
    apply (o_vec dim).(le_trans) with l2;assumption.
    apply (o_vec dim).(le_trans) with c2;assumption.
    apply mat_order_large_trans with m2;assumption.
    (* le morph *) 
    apply mat_order_large_morph.
    (* le_refl *)
    apply mat_order_large_refl.
    (* le antisym *)
    induction dim.
    simpl.
    apply o.(le_antisym).
    simpl;intros [a1 [l1 [c1 m1]]] [a2 [l2 [c2 m2]]] [H1 [H2 [H3 H4]]] [H5 [H6 [H7 H8]]]
      ;repeat split.
    apply o.(le_antisym);assumption.
    apply (o_vec dim).(le_antisym);assumption.
    apply (o_vec dim).(le_antisym);assumption.
    apply IHdim;assumption.
    (* le trans *)
    apply mat_order_large_trans.
    (* le_lt_compat_left *)
    destruct dim as [|dim].
    simpl. apply o.(le_lt_compat_left).
    simpl;intros [a1 [l1 [c1 m1]]] [a2 [l2 [c2 m2]]] [a3 [l3 [c3 m3]]] [H1 [H2 [H3 H4]]] 
      [H5 [H6 [H7 H8]]];repeat split.
    apply o.(le_lt_compat_left) with a2;assumption.
    apply (o_vec dim).(le_trans) with l2;assumption.
    apply (o_vec dim).(le_trans) with c2;assumption.
    apply mat_order_large_trans with m2;assumption.
    (* le_lt_compat_right *)
    destruct dim as [|dim].
    simpl. apply o.(le_lt_compat_right).
    simpl;intros [a1 [l1 [c1 m1]]] [a2 [l2 [c2 m2]]] [a3 [l3 [c3 m3]]] [H1 [H2 [H3 H4]]] 
      [H5 [H6 [H7 H8]]];repeat split.
    apply o.(le_lt_compat_right) with a2;assumption.
    apply (o_vec dim).(le_trans) with l2;assumption.
    apply (o_vec dim).(le_trans) with c2;assumption.
    apply mat_order_large_trans with m2;assumption.
    (* lt_included_le *)
    destruct dim.
    simpl;apply o.(lt_included_le).
    simpl; intros [a1 [l1 [c1 m1]]] [a2 [l2 [c2 m2]]] [H1 [H2 [H3 H4]]];repeat split.
    apply o.(lt_included_le);assumption.
    assumption.
    assumption.
    assumption.
  Defined.
    
  Lemma mat_order_strict_wf : 
    forall dim, well_founded (mat_order_strict dim).
  Proof.
    destruct dim as [|dim].
    simpl. apply lt_wf.
    simpl. intros [a [l [c m]]].
    revert l c m.
    pattern a.
    apply well_founded_ind with (1:=lt_wf). 
    clear a.
    intros a1 IHa1 l1 c1 m1.
    constructor.
    intros [a2 [l2 [c2 m2]]] [H1 _].
    apply IHa1 ; assumption.
  Qed.    





(*****************************)



(* dim=1 *)

  Lemma matrix_1_ind :
    forall (P:(matrix 1) -> Type), 
      forall (H:forall x_0_0 x_0_1,
        forall x_1_0 x_1_1,
                P (x_0_0,
                  ((x_0_1,(x_1_0,x_1_1))))), forall (m:matrix 1), P m.
  Proof.
    intros .
    refine match m with
             | (_,(_,(_,_))) => _
           end;
    vm_compute in *|-  ;
    repeat (match goal with
              | H:_*_ |- _ => clear H
            end);
    apply H.
  Defined.
  
  Lemma le_matrix_1_ind :
    forall (P:forall (m1 m2:matrix 1), (mat_order_large _ m1 m2) ->Prop), 
      forall (H:
        forall  x_0_0 x_0_1,
          forall x_1_0 x_1_1,
            forall  y_0_0 y_0_1,
              forall y_1_0 y_1_1,
                forall (H_0_0:le x_0_0 y_0_0), 
                  forall (H_0_1:le x_0_1 y_0_1), 
                    forall (H_1_0:le x_1_0 y_1_0), 
                      forall (H_1_1:le x_1_1 y_1_1), 
                        P (x_0_0,
                          (x_0_1,
                            (x_1_0,x_1_1)))
                        (y_0_0,
                          (y_0_1,
                            (y_1_0, y_1_1)))
                        (conj H_0_0 
                          (conj H_0_1 
                            (conj H_1_0 H_1_1)))
      ), 
      forall (m1 m2:matrix 1), forall (H:mat_order_large _ m1 m2), P m1 m2 H.
  Proof.
    intros .
    induction m1 using matrix_1_ind.
    induction m2 using matrix_1_ind.
    simpl in H0|-.
    
    refine match H0 with
             | (conj _ (conj _ (conj _ _))) => _
           end.
    apply H.
  Qed.

  Lemma decompose_le_matrix_1 :
    forall  x_0_0 x_0_1,
      forall x_1_0 x_1_1,
        forall  y_0_0 y_0_1,
          forall y_1_0 y_1_1,
            forall (H_0_0:le x_0_0 y_0_0), 
              forall (H_0_1:le x_0_1 y_0_1), 
                forall (H_1_0:le x_1_0 y_1_0), 
                  forall (H_1_1:le x_1_1 y_1_1), 
                    mat_order_large 1 (x_0_0,
                      (x_0_1,
                        (x_1_0,x_1_1)))
                    (y_0_0,
                      (y_0_1,
                        (y_1_0, y_1_1))).
  Proof.
    intros.     
    refine (conj _ (conj _ (conj _ _)));assumption.
  Qed.

  Lemma decompose_lt_matrix_1 :
    forall x_0_0 x_0_1,
      forall x_1_0 x_1_1,
        forall y_0_0 y_0_1,
          forall y_1_0 y_1_1,
            forall (H_0_0:lt x_0_0 y_0_0), 
              forall (H_0_1:le x_0_1 y_0_1), 
                forall (H_1_0:le x_1_0 y_1_0), 
                  forall (H_1_1:le x_1_1 y_1_1), 
                    mat_order_strict 1
                    (x_0_0,
                      (x_0_1,
                        (x_1_0,x_1_1)))
                    (y_0_0,
                      (y_0_1,
                        (y_1_0, y_1_1))).
  Proof.
    intros.     
    refine (conj _ (conj _ (conj _ _)));assumption.
  Qed.

  Lemma decompose_le_null_matrix_1 :
    forall x_0_0 x_0_1,
      forall x_1_0 x_1_1 ,
        forall (P:forall (m:matrix 1), 
          (mat_order_large 1 (null_matrix 1) m) ->Prop), 
        forall (H:
          forall (H_0_0:le rO x_0_0), 
            forall (H_0_1:le rO x_0_1), 
              forall (H_1_0:le rO x_1_0), 
                forall (H_1_1:le rO x_1_1), 
                  P (x_0_0,(x_0_1,(x_1_0,x_1_1)))
                  (conj H_0_0 
                    (conj H_0_1 
                      (conj H_1_0 H_1_1)))), 
                forall (H:mat_order_large _ (null_matrix 1) (x_0_0,(x_0_1,(x_1_0,x_1_1)))), 
                  P (x_0_0,(x_0_1,(x_1_0,x_1_1))) H.
  Proof.
    intros .
    
    refine match H0 with
             | (conj _ (conj _ (conj _ _))) => _
           end.
    apply H.
  Qed.



(* dim = 2 *)



  Lemma matrix_2_ind :
    forall (P:(matrix 2) -> Type), 
      forall (H:forall x_0_0 x_0_1 x_0_2, 
        forall x_1_0 x_1_1 x_1_2, 
          forall x_2_0 x_2_1 x_2_2, 
                P (x_0_0,
                  ((x_0_1,x_0_2),((x_1_0,x_2_0),
                    (x_1_1,
                        (x_1_2, (x_2_1,x_2_2))))))
      ), forall (m:matrix 2), P m.
  Proof.
    intros .
    
    refine match m with
             | (_,((_,_),((_,_),(_,(_,(_,_)))))) => _
           end;
    apply H.
  Defined.
  
  Lemma le_matrix_2_ind :
    forall (P:forall (m1 m2:matrix 2), (mat_order_large _ m1 m2) ->Prop), 
      forall (H:forall x_0_0 x_0_1 x_0_2,
        forall x_1_0 x_1_1 x_1_2,
          forall x_2_0 x_2_1 x_2_2,
            forall y_0_0 y_0_1 y_0_2,
              forall y_1_0 y_1_1 y_1_2,
                forall y_2_0 y_2_1 y_2_2,
                  forall (H_0_0:le x_0_0 y_0_0), 
                    forall (H_0_1:le x_0_1 y_0_1), 
                      forall (H_0_2:le x_0_2 y_0_2), 
                        forall (H_1_0:le x_1_0 y_1_0), 
                          forall (H_1_1:le x_1_1 y_1_1), 
                            forall (H_1_2:le x_1_2 y_1_2), 
                              forall (H_2_0:le x_2_0 y_2_0), 
                                forall (H_2_1:le x_2_1 y_2_1), 
                                  forall (H_2_2:le x_2_2 y_2_2), 
                                    P (x_0_0,
                                      ((x_0_1,x_0_2),((x_1_0,x_2_0),
                                        (x_1_1,
                                          (x_1_2, (x_2_1,x_2_2))))))
                                    (y_0_0,
                                      ((y_0_1,y_0_2),((y_1_0,y_2_0),
                                        (y_1_1,
                                          (y_1_2, (y_2_1,y_2_2))))))
                                    (conj H_0_0 
                                      (conj (conj H_0_1 H_0_2)
                                        (conj (conj H_1_0 H_2_0)
                                          (conj H_1_1 
                                            (conj H_1_2 
                                              (conj H_2_1 H_2_2))))))
      ), 
      forall (m1 m2:matrix 2), forall (H:mat_order_large 2 m1 m2), P m1 m2 H.
  Proof.
    intros .
    induction m1 using matrix_2_ind.
    induction m2 using matrix_2_ind.
    simpl in H0|-.
    
    refine match H0 with
             | (conj _ 
               (conj (conj _ _) (conj (conj _ _) (conj _ (conj _ (conj _ _))))))
               => _
           end.
    apply H.
  Qed.

  Lemma decompose_le_matrix_2 :
    forall x_0_0 x_0_1 x_0_2,
      forall x_1_0 x_1_1 x_1_2,
        forall x_2_0 x_2_1 x_2_2,
          forall y_0_0 y_0_1 y_0_2,
            forall y_1_0 y_1_1 y_1_2,
              forall y_2_0 y_2_1 y_2_2,
                forall (H_0_0:le x_0_0 y_0_0), 
                  forall (H_0_1:le x_0_1 y_0_1), 
                    forall (H_0_2:le x_0_2 y_0_2), 
                      forall (H_1_0:le x_1_0 y_1_0), 
                        forall (H_1_1:le x_1_1 y_1_1), 
                          forall (H_1_2:le x_1_2 y_1_2), 
                            forall (H_2_0:le x_2_0 y_2_0), 
                              forall (H_2_1:le x_2_1 y_2_1), 
                                forall (H_2_2:le x_2_2 y_2_2), 
                                  mat_order_large 2 
                                  (x_0_0,
                                      ((x_0_1,x_0_2),((x_1_0,x_2_0),
                                        (x_1_1,
                                          (x_1_2, (x_2_1,x_2_2))))))
                                    (y_0_0,
                                      ((y_0_1,y_0_2),((y_1_0,y_2_0),
                                        (y_1_1,
                                          (y_1_2, (y_2_1,y_2_2)))))).
    Proof.
      intros.    
      refine (conj _ 
                  (conj (conj _ _) 
                    (conj (conj _ _) (conj _ (conj _ (conj _ _))))))
             ;assumption.
  Qed.
  

  Lemma decompose_lt_matrix_2 :
    forall x_0_0 x_0_1 x_0_2,
      forall x_1_0 x_1_1 x_1_2,
        forall x_2_0 x_2_1 x_2_2,
          forall y_0_0 y_0_1 y_0_2,
            forall y_1_0 y_1_1 y_1_2,
              forall y_2_0 y_2_1 y_2_2,
                forall (H_0_0:lt x_0_0 y_0_0), 
                  forall (H_0_1:le x_0_1 y_0_1), 
                    forall (H_0_2:le x_0_2 y_0_2), 
                      forall (H_1_0:le x_1_0 y_1_0), 
                        forall (H_1_1:le x_1_1 y_1_1), 
                          forall (H_1_2:le x_1_2 y_1_2), 
                            forall (H_2_0:le x_2_0 y_2_0), 
                              forall (H_2_1:le x_2_1 y_2_1), 
                                forall (H_2_2:le x_2_2 y_2_2), 
                                  mat_order_strict 2 
                                  (x_0_0,
                                      ((x_0_1,x_0_2),((x_1_0,x_2_0),
                                        (x_1_1,
                                          (x_1_2, (x_2_1,x_2_2))))))
                                    (y_0_0,
                                      ((y_0_1,y_0_2),((y_1_0,y_2_0),
                                        (y_1_1,
                                          (y_1_2, (y_2_1,y_2_2)))))).
    Proof.
      intros.    
      refine (conj _ 
                  (conj (conj _ _) 
                    (conj (conj _ _) (conj _ (conj _ (conj _ _))))))
             ; try assumption.
  Qed.

  
  Lemma decompose_le_null_matrix_2 :
    forall x_0_0 x_0_1 x_0_2,
      forall x_1_0 x_1_1 x_1_2,
        forall x_2_0 x_2_1 x_2_2,
          forall (P:forall (m:matrix 2), mat_order_large _ (null_matrix 2) m ->Prop), 
            forall (H:
              forall (H_0_0:le rO x_0_0), 
                forall (H_0_1:le rO x_0_1), 
                  forall (H_0_2:le rO x_0_2), 
                    forall (H_1_0:le rO x_1_0), 
                      forall (H_1_1:le rO x_1_1), 
                        forall (H_1_2:le rO x_1_2), 
                          forall (H_2_0:le rO x_2_0), 
                            forall (H_2_1:le rO x_2_1), 
                              forall (H_2_2:le rO x_2_2), 
                                P (x_0_0,
                                  ((x_0_1,x_0_2),((x_1_0,x_2_0),
                                    (x_1_1,
                                      (x_1_2, (x_2_1,x_2_2))))))
                                (conj H_0_0 
                                  (conj (conj H_0_1 H_0_2)
                                    (conj (conj H_1_0 H_2_0)
                                      (conj H_1_1 
                                        (conj H_1_2 
                                          (conj H_2_1 H_2_2))))))
            ),
            forall (H:mat_order_large _ (null_matrix 2) (x_0_0,
                                  ((x_0_1,x_0_2),((x_1_0,x_2_0),
                                    (x_1_1,
                                      (x_1_2, (x_2_1,x_2_2))))))), 
            P (x_0_0,
              ((x_0_1,x_0_2),((x_1_0,x_2_0),
                (x_1_1,
                  (x_1_2, (x_2_1,x_2_2)))))) H.
  Proof.
    intros .
    
    refine match H0 with
             | (conj _ 
               (conj (conj _ _) 
                 (conj (conj _ _) (conj _ (conj _ (conj _ _))))))
             => _
           end.
    apply H.
  Qed.

(* dim = 3 *)
  Lemma matrix_3_ind :
    forall (P:(matrix 3) -> Type), 
      forall (H:forall x_0_0 x_0_1 x_0_2 x_0_3, 
        forall x_1_0 x_1_1 x_1_2 x_1_3 , 
          forall x_2_0 x_2_1 x_2_2 x_2_3, 
            forall x_3_0 x_3_1 x_3_2 x_3_3, 
                P (x_0_0,
                  ((x_0_1,(x_0_2,x_0_3)),
                    ((x_1_0,(x_2_0,x_3_0)),
                      (x_1_1,
                        ((x_1_2,x_1_3),
                          ((x_2_1,x_3_1),
                            (x_2_2,
                              (x_2_3,
                                (x_3_2,x_3_3)))))))))),
                 forall (m:matrix 3), P m.
  Proof.
    intros .
    
    refine match m with
             | (_,
                     ((_,(_,_)),((_,(_,_)),(_,((_,_),((_,_),(_,(_,(_,_)))))))))
             => _
           end;
    apply H.
  Defined.
  
  Lemma le_matrix_3_ind :
    forall (P:forall (m1 m2:matrix 3), (mat_order_large _ m1 m2) ->Prop), 
      forall (H:forall x_0_0 x_0_1 x_0_2 x_0_3, 
        forall x_1_0 x_1_1 x_1_2 x_1_3, 
          forall x_2_0 x_2_1 x_2_2 x_2_3, 
            forall x_3_0 x_3_1 x_3_2 x_3_3, 
              forall y_0_0 y_0_1 y_0_2 y_0_3, 
                forall y_1_0 y_1_1 y_1_2 y_1_3 , 
                  forall y_2_0 y_2_1 y_2_2 y_2_3, 
                    forall y_3_0 y_3_1 y_3_2 y_3_3, 
                      forall (H_0_0:le x_0_0 y_0_0), 
                        forall (H_0_1:le x_0_1 y_0_1), 
                          forall (H_0_2:le x_0_2 y_0_2), 
                            forall (H_0_3:le x_0_3 y_0_3), 
                              forall (H_1_0:le x_1_0 y_1_0), 
                                forall (H_1_1:le x_1_1 y_1_1), 
                                  forall (H_1_2:le x_1_2 y_1_2), 
                                    forall (H_1_3:le x_1_3 y_1_3), 
                                      forall (H_2_0:le x_2_0 y_2_0), 
                                        forall (H_2_1:le x_2_1 y_2_1), 
                                          forall (H_2_2:le x_2_2 y_2_2), 
                                            forall (H_2_3:le x_2_3 y_2_3), 
                                              forall (H_3_0:le x_3_0 y_3_0), 
                                                forall (H_3_1:le x_3_1 y_3_1), 
                                                  forall (H_3_2:le x_3_2 y_3_2), 
                                                    forall (H_3_3:le x_3_3 y_3_3), 
                                                      P 
                                                      (x_0_0,
                                                        ((x_0_1,(x_0_2,x_0_3)),
                                                          ((x_1_0,(x_2_0,x_3_0)),
                                                            (x_1_1,
                                                              ((x_1_2,x_1_3),
                                                                ((x_2_1,x_3_1),
                                                                  (x_2_2,
                                                                    (x_2_3,
                                                                      (x_3_2,x_3_3))))))))) 
                                                      (y_0_0,
                                                        ((y_0_1,(y_0_2,y_0_3)),
                                                          ((y_1_0,(y_2_0,y_3_0)),
                                                            (y_1_1,
                                                              ((y_1_2,y_1_3),
                                                                ((y_2_1,y_3_1),
                                                                  (y_2_2,
                                                                    (y_2_3,
                                                                      (y_3_2,y_3_3)))))))))
                                                      (conj H_0_0 
                                                        (conj (conj H_0_1 
                                                          (conj H_0_2 
                                                            H_0_3)) 
                                                        (conj (conj H_1_0 
                                                          (conj 
                                                            H_2_0 
                                                            H_3_0)) 
                                                        (conj H_1_1 
                                                          (conj (conj 
                                                            H_1_2 
                                                            H_1_3) 
                                                          (conj (conj 
                                                            H_2_1 
                                                            H_3_1) 
                                                          (conj 
                                                            H_2_2 
                                                            (conj 
                                                              H_2_3 
                                                              (conj 
                                                                H_3_2 
                                                                H_3_3)))))))))
      ), 
      forall (m1 m2:matrix 3), forall (H:mat_order_large _ m1 m2), P m1 m2 H.
  Proof.
    intros .
    induction m1 using matrix_3_ind.
    induction m2 using matrix_3_ind.
    refine match H0 with
             | (conj _ 
                     (conj (conj _ (conj _ _)) 
                       (conj (conj _ (conj _ _)) 
                         (conj _ 
                           (conj (conj _ _) 
                             (conj (conj _ _) (conj _ (conj _ (conj _ _))))))
                       ))) => _
           end.
    apply H.
  Qed.

  Lemma decompose_lt_matrix_3 :
    forall x_0_0 x_0_1 x_0_2 x_0_3, 
      forall x_1_0 x_1_1 x_1_2 x_1_3, 
        forall x_2_0 x_2_1 x_2_2 x_2_3, 
          forall x_3_0 x_3_1 x_3_2 x_3_3 , 
            forall y_0_0 y_0_1 y_0_2 y_0_3, 
              forall y_1_0 y_1_1 y_1_2 y_1_3, 
                forall y_2_0 y_2_1 y_2_2 y_2_3 , 
                  forall y_3_0 y_3_1 y_3_2 y_3_3 , 
                    forall (H_0_0:lt x_0_0 y_0_0), 
                      forall (H_0_1:le x_0_1 y_0_1), 
                        forall (H_0_2:le x_0_2 y_0_2), 
                          forall (H_0_3:le x_0_3 y_0_3), 
                            forall (H_1_0:le x_1_0 y_1_0), 
                              forall (H_1_1:le x_1_1 y_1_1), 
                                forall (H_1_2:le x_1_2 y_1_2), 
                                  forall (H_1_3:le x_1_3 y_1_3), 
                                    forall (H_2_0:le x_2_0 y_2_0), 
                                      forall (H_2_1:le x_2_1 y_2_1), 
                                        forall (H_2_2:le x_2_2 y_2_2), 
                                          forall (H_2_3:le x_2_3 y_2_3), 
                                            forall (H_3_0:le x_3_0 y_3_0), 
                                              forall (H_3_1:le x_3_1 y_3_1), 
                                                forall (H_3_2:le x_3_2 y_3_2), 
                                                  forall (H_3_3:le x_3_3 y_3_3), 
                                                    mat_order_strict 3
                                                    (x_0_0,
                                                      ((x_0_1,(x_0_2,x_0_3)),
                                                        ((x_1_0,(x_2_0,x_3_0)),
                                                          (x_1_1,
                                                            ((x_1_2,x_1_3),
                                                              ((x_2_1,x_3_1),
                                                                (x_2_2,
                                                                  (x_2_3,
                                                                    (x_3_2,x_3_3))))))))) 
                                                    (y_0_0,
                                                      ((y_0_1,(y_0_2,y_0_3)),
                                                        ((y_1_0,(y_2_0,y_3_0)),
                                                          (y_1_1,
                                                            ((y_1_2,y_1_3),
                                                              ((y_2_1,y_3_1),
                                                                (y_2_2,
                                                                  (y_2_3,
                                                                    (y_3_2,y_3_3)))))))))
                                                    .
    intros;
      refine (conj _ 
            (conj (conj _ (conj _ _)) 
              (conj (conj _ (conj _ _)) 
                (conj _ 
                  (conj (conj _ _) 
                    (conj (conj _ _) (conj _ (conj _ (conj _ _))))))
              )));assumption.
  Qed.

  Lemma decompose_le_matrix_3 :
    forall x_0_0 x_0_1 x_0_2 x_0_3, 
      forall x_1_0 x_1_1 x_1_2 x_1_3, 
        forall x_2_0 x_2_1 x_2_2 x_2_3, 
          forall x_3_0 x_3_1 x_3_2 x_3_3 , 
            forall y_0_0 y_0_1 y_0_2 y_0_3, 
              forall y_1_0 y_1_1 y_1_2 y_1_3, 
                forall y_2_0 y_2_1 y_2_2 y_2_3 , 
                  forall y_3_0 y_3_1 y_3_2 y_3_3 , 
                    forall (H_0_0:le x_0_0 y_0_0), 
                      forall (H_0_1:le x_0_1 y_0_1), 
                        forall (H_0_2:le x_0_2 y_0_2), 
                          forall (H_0_3:le x_0_3 y_0_3), 
                            forall (H_1_0:le x_1_0 y_1_0), 
                              forall (H_1_1:le x_1_1 y_1_1), 
                                forall (H_1_2:le x_1_2 y_1_2), 
                                  forall (H_1_3:le x_1_3 y_1_3), 
                                    forall (H_2_0:le x_2_0 y_2_0), 
                                      forall (H_2_1:le x_2_1 y_2_1), 
                                        forall (H_2_2:le x_2_2 y_2_2), 
                                          forall (H_2_3:le x_2_3 y_2_3), 
                                            forall (H_3_0:le x_3_0 y_3_0), 
                                              forall (H_3_1:le x_3_1 y_3_1), 
                                                forall (H_3_2:le x_3_2 y_3_2), 
                                                  forall (H_3_3:le x_3_3 y_3_3), 
                                                    mat_order_large 3 
                                                    (x_0_0,
                                                      ((x_0_1,(x_0_2,x_0_3)),
                                                        ((x_1_0,(x_2_0,x_3_0)),
                                                          (x_1_1,
                                                            ((x_1_2,x_1_3),
                                                              ((x_2_1,x_3_1),
                                                                (x_2_2,
                                                                  (x_2_3,
                                                                    (x_3_2,x_3_3))))))))) 
                                                    (y_0_0,
                                                      ((y_0_1,(y_0_2,y_0_3)),
                                                        ((y_1_0,(y_2_0,y_3_0)),
                                                          (y_1_1,
                                                            ((y_1_2,y_1_3),
                                                              ((y_2_1,y_3_1),
                                                                (y_2_2,
                                                                  (y_2_3,
                                                                    (y_3_2,y_3_3)))))))))
                                                    .
    intros;
      refine (conj _ 
            (conj (conj _ (conj _ _)) 
              (conj (conj _ (conj _ _)) 
                (conj _ 
                  (conj (conj _ _) 
                    (conj (conj _ _) (conj _ (conj _ (conj _ _))))))
              )));assumption.
  Qed.
  


  
  Lemma decompose_le_null_matrix_3 :
    forall x_0_0 x_0_1 x_0_2 x_0_3, 
      forall x_1_0 x_1_1 x_1_2 x_1_3, 
        forall x_2_0 x_2_1 x_2_2 x_2_3, 
          forall x_3_0 x_3_1 x_3_2 x_3_3 , 
            forall (P:forall (m:matrix 3), (mat_order_large _ (null_matrix 3)  m) ->Prop), 
              forall (H:
                forall (H_0_0:le rO x_0_0), 
                  forall (H_0_1:le rO x_0_1), 
                    forall (H_0_2:le rO x_0_2), 
                      forall (H_0_3:le rO x_0_3), 
                        forall (H_1_0:le rO x_1_0), 
                          forall (H_1_1:le rO x_1_1), 
                            forall (H_1_2:le rO x_1_2), 
                              forall (H_1_3:le rO x_1_3), 
                                forall (H_2_0:le rO x_2_0), 
                                  forall (H_2_1:le rO x_2_1), 
                                    forall (H_2_2:le rO x_2_2), 
                                      forall (H_2_3:le rO x_2_3), 
                                        forall (H_3_0:le rO x_3_0), 
                                          forall (H_3_1:le rO x_3_1), 
                                            forall (H_3_2:le rO x_3_2), 
                                              forall (H_3_3:le rO x_3_3), 
                                                P (x_0_0,
                                                        ((x_0_1,(x_0_2,x_0_3)),
                                                          ((x_1_0,(x_2_0,x_3_0)),
                                                            (x_1_1,
                                                              ((x_1_2,x_1_3),
                                                                ((x_2_1,x_3_1),
                                                                  (x_2_2,
                                                                    (x_2_3,
                                                                      (x_3_2,x_3_3))))))))) 
                                                
                                                (conj H_0_0 
                                                  (conj (conj H_0_1 
                                                    (conj H_0_2 
                                                      H_0_3)) 
                                                  (conj (conj H_1_0 
                                                    (conj 
                                                      H_2_0 
                                                      H_3_0)) 
                                                  (conj H_1_1 
                                                    (conj (conj 
                                                      H_1_2 
                                                      H_1_3) 
                                                    (conj (conj 
                                                      H_2_1 
                                                      H_3_1) 
                                                    (conj 
                                                      H_2_2 
                                                      (conj 
                                                        H_2_3 
                                                        (conj 
                                                          H_3_2 
                                                          H_3_3)))))))))
                ), 
                forall (H:mat_order_large _ (null_matrix 3) 
                  (x_0_0,
                    ((x_0_1,(x_0_2,x_0_3)),
                      ((x_1_0,(x_2_0,x_3_0)),
                        (x_1_1,
                          ((x_1_2,x_1_3),
                            ((x_2_1,x_3_1),
                              (x_2_2,
                                (x_2_3,
                                  (x_3_2,x_3_3))))))))) ), 
                P                 
                (x_0_0,
                  ((x_0_1,(x_0_2,x_0_3)),
                    ((x_1_0,(x_2_0,x_3_0)),
                      (x_1_1,
                        ((x_1_2,x_1_3),
                          ((x_2_1,x_3_1),
                            (x_2_2,
                              (x_2_3,
                                (x_3_2,x_3_3))))))))) 
                H.
  Proof.
    intros .
    
    refine match H0 with
             |(conj _ 
                     (conj (conj _ (conj _ _)) 
                       (conj (conj _ (conj _ _)) 
                         (conj _ 
                           (conj (conj _ _) 
                             (conj (conj _ _) (conj _ (conj _ (conj _ _))))))
                       ))) =>
               _
           end.
    apply H.
  Qed.

(* dim = 4 *)



  Lemma matrix_4_ind :
    forall (P:(matrix 4) -> Type), 
      forall (H:forall x_0_0 x_0_1 x_0_2 x_0_3 x_0_4, 
        forall x_1_0 x_1_1 x_1_2 x_1_3 x_1_4, 
          forall x_2_0 x_2_1 x_2_2 x_2_3 x_2_4, 
            forall x_3_0 x_3_1 x_3_2 x_3_3 x_3_4, 
              forall x_4_0 x_4_1 x_4_2 x_4_3 x_4_4, 
                P (x_0_0,
                  ((x_0_1,(x_0_2,(x_0_3,x_0_4))),
                    ((x_1_0,(x_2_0,(x_3_0,x_4_0))),
                      (x_1_1,
                        ((x_1_2,(x_1_3,x_1_4)),
                          ((x_2_1,(x_3_1,x_4_1)),
                            (x_2_2,
                              ((x_2_3,x_2_4),
                                ((x_3_2,x_4_2),(x_3_3,(x_3_4,(x_4_3,x_4_4))))))))
                      ))))), forall (m:matrix 4), P m.
  Proof.
    intros .
    
    refine match m with
             | (_,
               ((_,(_,(_,_))),
                 ((_,(_,(_,_))),
                   (_,
                     ((_,(_,_)),((_,(_,_)),(_,((_,_),((_,_),(_,(_,(_,_))))))))))
               )) =>
             _
           end.
    apply H.
  Defined.
  
  Lemma le_matrix_4_ind :
    forall (P:forall (m1 m2:matrix 4), (mat_order_large _ m1 m2) ->Prop), 
      forall (H:forall x_0_0 x_0_1 x_0_2 x_0_3 x_0_4, 
        forall x_1_0 x_1_1 x_1_2 x_1_3 x_1_4, 
          forall x_2_0 x_2_1 x_2_2 x_2_3 x_2_4, 
            forall x_3_0 x_3_1 x_3_2 x_3_3 x_3_4, 
              forall x_4_0 x_4_1 x_4_2 x_4_3 x_4_4, 
                forall y_0_0 y_0_1 y_0_2 y_0_3 y_0_4, 
                  forall y_1_0 y_1_1 y_1_2 y_1_3 y_1_4, 
                    forall y_2_0 y_2_1 y_2_2 y_2_3 y_2_4, 
                      forall y_3_0 y_3_1 y_3_2 y_3_3 y_3_4, 
                        forall y_4_0 y_4_1 y_4_2 y_4_3 y_4_4, 
                          forall (H_0_0:le x_0_0 y_0_0), 
                            forall (H_0_1:le x_0_1 y_0_1), 
                              forall (H_0_2:le x_0_2 y_0_2), 
                                forall (H_0_3:le x_0_3 y_0_3), 
                                  forall (H_0_4:le x_0_4 y_0_4), 
                                    forall (H_1_0:le x_1_0 y_1_0), 
                                      forall (H_1_1:le x_1_1 y_1_1), 
                                        forall (H_1_2:le x_1_2 y_1_2), 
                                          forall (H_1_3:le x_1_3 y_1_3), 
                                            forall (H_1_4:le x_1_4 y_1_4), 
                                              forall (H_2_0:le x_2_0 y_2_0), 
                                                forall (H_2_1:le x_2_1 y_2_1), 
                                                  forall (H_2_2:le x_2_2 y_2_2), 
                                                    forall (H_2_3:le x_2_3 y_2_3), 
                                                      forall (H_2_4:le x_2_4 y_2_4), 
                                                        forall (H_3_0:le x_3_0 y_3_0), 
                                                          forall (H_3_1:le x_3_1 y_3_1), 
                                                            forall (H_3_2:le x_3_2 y_3_2), 
                                                              forall (H_3_3:le x_3_3 y_3_3), 
                                                                forall (H_3_4:le x_3_4 y_3_4), 
                                                                  forall (H_4_0:le x_4_0 y_4_0), 
                                                                    forall (H_4_1:le x_4_1 y_4_1), 
                                                                      forall (H_4_2:le x_4_2 y_4_2), 
                                                                        forall (H_4_3:le x_4_3 y_4_3), 
                                                                          forall (H_4_4:le x_4_4 
                                                                            y_4_4), 
                                                                          P (x_0_0,
                                                                            ((x_0_1,
                                                                              (x_0_2,(x_0_3,x_0_4))),
                                                                            ((x_1_0,
                                                                              (x_2_0,(x_3_0,x_4_0))),
                                                                            (x_1_1,
                                                                              ((x_1_2,
                                                                                (x_1_3,x_1_4)),
                                                                              ((x_2_1,
                                                                                (x_3_1,x_4_1)),
                                                                              (x_2_2,
                                                                                ((x_2_3,x_2_4),
                                                                                  ((x_3_2,x_4_2),
                                                                                    (x_3_3,
                                                                                      (x_3_4,
                                                                                        (x_4_3,x_4_4))))
                                                                                )))))))) 
                                                                          (y_0_0,
                                                                            ((y_0_1,
                                                                              (y_0_2,(y_0_3,y_0_4))),
                                                                            ((y_1_0,
                                                                              (y_2_0,(y_3_0,y_4_0))),
                                                                            (y_1_1,
                                                                              ((y_1_2,(y_1_3,y_1_4)),
                                                                                ((y_2_1,
                                                                                  (y_3_1,y_4_1)),
                                                                                (y_2_2,
                                                                                  ((y_2_3,y_2_4),
                                                                                    ((y_3_2,y_4_2),
                                                                                      (y_3_3,
                                                                                        (y_3_4,
                                                                                          (y_4_3,y_4_4)))))
                                                                                ))))))) 
                                                                          (conj H_0_0 
                                                                            (conj (conj H_0_1 
                                                                              (conj H_0_2 
                                                                                (conj 
                                                                                  H_0_3 
                                                                                  H_0_4))) 
                                                                            (conj (conj H_1_0 
                                                                              (conj 
                                                                                H_2_0 
                                                                                (conj 
                                                                                  H_3_0 
                                                                                  H_4_0))) 
                                                                            (conj H_1_1 
                                                                              (conj (conj 
                                                                                H_1_2 
                                                                                (conj 
                                                                                  H_1_3 
                                                                                  H_1_4)) 
                                                                              (conj (conj 
                                                                                H_2_1 
                                                                                (conj 
                                                                                  H_3_1 
                                                                                  H_4_1)) 
                                                                              (conj 
                                                                                H_2_2 
                                                                                (conj 
                                                                                  (conj 
                                                                                    H_2_3 
                                                                                    H_2_4) 
                                                                                  (conj 
                                                                                    (conj 
                                                                                      H_3_2 
                                                                                      H_4_2) 
                                                                                    (conj 
                                                                                      H_3_3 
                                                                                      (conj 
                                                                                        H_3_4 
                                                                                        (conj 
                                                                                          H_4_3 
                                                                                          H_4_4))))))
                                                                              ))))))), 
      forall (m1 m2:matrix 4), forall (H:mat_order_large _ m1 m2), P m1 m2 H.
  Proof.
    intros .
    induction m1 using matrix_4_ind.
    induction m2 using matrix_4_ind.
    refine match H0 with
             | conj _ 
               (conj (conj _ (conj _ (conj _ _))) 
                 (conj (conj _ (conj _ (conj _ _))) 
                   (conj _ 
                     (conj (conj _ (conj _ _)) 
                       (conj (conj _ (conj _ _)) 
                         (conj _ 
                           (conj (conj _ _) 
                             (conj (conj _ _) (conj _ (conj _ (conj _ _))))))
                       ))))) =>
               _
           end.
    apply H.
  Qed.

  Lemma decompose_le_matrix_4  :
    forall x_0_0 x_0_1 x_0_2 x_0_3 x_0_4, 
      forall x_1_0 x_1_1 x_1_2 x_1_3 x_1_4, 
        forall x_2_0 x_2_1 x_2_2 x_2_3 x_2_4, 
          forall x_3_0 x_3_1 x_3_2 x_3_3 x_3_4, 
            forall x_4_0 x_4_1 x_4_2 x_4_3 x_4_4, 
              forall y_0_0 y_0_1 y_0_2 y_0_3 y_0_4, 
                forall y_1_0 y_1_1 y_1_2 y_1_3 y_1_4, 
                  forall y_2_0 y_2_1 y_2_2 y_2_3 y_2_4, 
                    forall y_3_0 y_3_1 y_3_2 y_3_3 y_3_4, 
                      forall y_4_0 y_4_1 y_4_2 y_4_3 y_4_4, 
                        forall (H_0_0:le x_0_0 y_0_0), 
                          forall (H_0_1:le x_0_1 y_0_1), 
                            forall (H_0_2:le x_0_2 y_0_2), 
                              forall (H_0_3:le x_0_3 y_0_3), 
                                forall (H_0_4:le x_0_4 y_0_4), 
                                  forall (H_1_0:le x_1_0 y_1_0), 
                                    forall (H_1_1:le x_1_1 y_1_1), 
                                      forall (H_1_2:le x_1_2 y_1_2), 
                                        forall (H_1_3:le x_1_3 y_1_3), 
                                          forall (H_1_4:le x_1_4 y_1_4), 
                                            forall (H_2_0:le x_2_0 y_2_0), 
                                              forall (H_2_1:le x_2_1 y_2_1), 
                                                forall (H_2_2:le x_2_2 y_2_2), 
                                                  forall (H_2_3:le x_2_3 y_2_3), 
                                                    forall (H_2_4:le x_2_4 y_2_4), 
                                                      forall (H_3_0:le x_3_0 y_3_0), 
                                                        forall (H_3_1:le x_3_1 y_3_1), 
                                                          forall (H_3_2:le x_3_2 y_3_2), 
                                                            forall (H_3_3:le x_3_3 y_3_3), 
                                                              forall (H_3_4:le x_3_4 y_3_4), 
                                                                forall (H_4_0:le x_4_0 y_4_0), 
                                                                  forall (H_4_1:le x_4_1 y_4_1), 
                                                                    forall (H_4_2:le x_4_2 y_4_2), 
                                                                      forall (H_4_3:le x_4_3 y_4_3), 
                                                                        forall (H_4_4:le x_4_4 y_4_4), 
                                                                          mat_order_large 4 (x_0_0,
                                                                            ((x_0_1,
                                                                              (x_0_2,(x_0_3,x_0_4))),
                                                                            ((x_1_0,
                                                                              (x_2_0,(x_3_0,x_4_0))),
                                                                            (x_1_1,
                                                                              ((x_1_2,
                                                                                (x_1_3,x_1_4)),
                                                                              ((x_2_1,
                                                                                (x_3_1,x_4_1)),
                                                                              (x_2_2,
                                                                                ((x_2_3,x_2_4),
                                                                                  ((x_3_2,x_4_2),
                                                                                    (x_3_3,
                                                                                      (x_3_4,
                                                                                        (x_4_3,x_4_4))))
                                                                                )))))))) 
                                                                          (y_0_0,
                                                                            ((y_0_1,
                                                                              (y_0_2,(y_0_3,y_0_4))),
                                                                            ((y_1_0,
                                                                              (y_2_0,(y_3_0,y_4_0))),
                                                                            (y_1_1,
                                                                              ((y_1_2,(y_1_3,y_1_4)),
                                                                                ((y_2_1,
                                                                                  (y_3_1,y_4_1)),
                                                                                (y_2_2,
                                                                                  ((y_2_3,y_2_4),
                                                                                    ((y_3_2,y_4_2),
                                                                                      (y_3_3,
                                                                                        (y_3_4,
                                                                                          (y_4_3,y_4_4)))))
                                                                                ))))))) .
    intros x_0_0 x_0_1 x_0_2 x_0_3 x_0_4 x_1_0 x_1_1 x_1_2 x_1_3 x_1_4 x_2_0 x_2_1 x_2_2.
    intros x_2_3 x_2_4 x_3_0 x_3_1 x_3_2 x_3_3 x_3_4 x_4_0 x_4_1 x_4_2 x_4_3 x_4_4 y_0_0.
    intros y_0_1 y_0_2 y_0_3 y_0_4 y_1_0 y_1_1 y_1_2 y_1_3 y_1_4 y_2_0 y_2_1 y_2_2 y_2_3.
    intros y_2_4 y_3_0 y_3_1 y_3_2 y_3_3 y_3_4 y_4_0 y_4_1 y_4_2 y_4_3 y_4_4 H_0_0 H_0_1.
    intros H_0_2 H_0_3 H_0_4 H_1_0 H_1_1 H_1_2 H_1_3 H_1_4 H_2_0 H_2_1 H_2_2 H_2_3 H_2_4.
    intros H_3_0 H_3_1 H_3_2 H_3_3 H_3_4 H_4_0 H_4_1 H_4_2 H_4_3 H_4_4.
    refine (conj _ 
      (conj (conj _ (conj _ (conj _ _))) 
        (conj (conj _ (conj _ (conj _ _))) 
          (conj _ 
            (conj (conj _ (conj _ _)) 
              (conj (conj _ (conj _ _)) 
                (conj _ 
                  (conj (conj _ _) 
                    (conj (conj _ _) (conj _ (conj _ (conj _ _))))))
              ))))));assumption.
  Qed.
  


  
  Lemma decompose_le_null_matrix_4 :
    forall x_0_0 x_0_1 x_0_2 x_0_3 x_0_4, 
      forall x_1_0 x_1_1 x_1_2 x_1_3 x_1_4, 
        forall x_2_0 x_2_1 x_2_2 x_2_3 x_2_4, 
          forall x_3_0 x_3_1 x_3_2 x_3_3 x_3_4, 
            forall x_4_0 x_4_1 x_4_2 x_4_3 x_4_4, 
              forall (P:forall (m:matrix 4), (mat_order_large _ (null_matrix 4) m) ->Prop), 
                forall (H:forall (H_0_0:le rO x_0_0), 
                  forall (H_0_1:le rO x_0_1), 
                    forall (H_0_2:le rO x_0_2), 
                      forall (H_0_3:le rO x_0_3), 
                        forall (H_0_4:le rO x_0_4), 
                          forall (H_1_0:le rO x_1_0), 
                            forall (H_1_1:le rO x_1_1), 
                              forall (H_1_2:le rO x_1_2), 
                                forall (H_1_3:le rO x_1_3), 
                                  forall (H_1_4:le rO x_1_4), 
                                    forall (H_2_0:le rO x_2_0), 
                                      forall (H_2_1:le rO x_2_1), 
                                        forall (H_2_2:le rO x_2_2), 
                                          forall (H_2_3:le rO x_2_3), 
                                            forall (H_2_4:le rO x_2_4), 
                                              forall (H_3_0:le rO x_3_0), 
                                                forall (H_3_1:le rO x_3_1), 
                                                  forall (H_3_2:le rO x_3_2), 
                                                    forall (H_3_3:le rO x_3_3), 
                                                      forall (H_3_4:le rO x_3_4), 
                                                        forall (H_4_0:le rO x_4_0), 
                                                          forall (H_4_1:le rO x_4_1), 
                                                            forall (H_4_2:le rO x_4_2), 
                                                              forall (H_4_3:le rO x_4_3), 
                                                                forall (H_4_4:le rO x_4_4), 
                                                                  P (x_0_0,
                                                                    ((x_0_1,
                                                                      (x_0_2,(x_0_3,x_0_4))),
                                                                    ((x_1_0,
                                                                      (x_2_0,(x_3_0,x_4_0))),
                                                                    (x_1_1,
                                                                      ((x_1_2,(x_1_3,x_1_4)),
                                                                        ((x_2_1,(x_3_1,x_4_1)),
                                                                          (x_2_2,
                                                                            ((x_2_3,x_2_4),
                                                                              ((x_3_2,x_4_2),
                                                                                (x_3_3,
                                                                                  (x_3_4,
                                                                                    (x_4_3,x_4_4)))))))))
                                                                    ))) 
                                                                  (conj H_0_0 
                                                                    (conj (conj H_0_1 
                                                                      (conj H_0_2 
                                                                        (conj H_0_3 H_0_4))) 
                                                                    
                                                                    (conj (conj H_1_0 
                                                                      (conj H_2_0 
                                                                        (conj H_3_0 H_4_0))
                                                                    ) 
                                                                    (conj H_1_1 
                                                                      (conj (conj H_1_2 
                                                                        (conj H_1_3 
                                                                          H_1_4)) 
                                                                      (conj (conj H_2_1 
                                                                        (conj 
                                                                          H_3_1 
                                                                          H_4_1)) 
                                                                      (conj H_2_2 
                                                                        (conj (conj 
                                                                          H_2_3 
                                                                          H_2_4) 
                                                                        (conj (conj 
                                                                          H_3_2 
                                                                          H_4_2) 
                                                                        (conj 
                                                                          H_3_3 
                                                                          (conj 
                                                                            H_3_4 
                                                                            (conj 
                                                                              H_4_3 
                                                                              H_4_4))))))
                                                                      ))))))), 
                forall (H:mat_order_large _ (null_matrix 4)  (x_0_0,
                  ((x_0_1,(x_0_2,(x_0_3,x_0_4))),
                    ((x_1_0,(x_2_0,(x_3_0,x_4_0))),
                      (x_1_1,
                        ((x_1_2,(x_1_3,x_1_4)),
                          ((x_2_1,(x_3_1,x_4_1)),
                            (x_2_2,
                              ((x_2_3,x_2_4),
                                ((x_3_2,x_4_2),
                                  (x_3_3,(x_3_4,(x_4_3,x_4_4))))))
                          ))))))), 
                P (x_0_0,
                  ((x_0_1,(x_0_2,(x_0_3,x_0_4))),
                    ((x_1_0,(x_2_0,(x_3_0,x_4_0))),
                      (x_1_1,
                        ((x_1_2,(x_1_3,x_1_4)),
                          ((x_2_1,(x_3_1,x_4_1)),
                            (x_2_2,
                              ((x_2_3,x_2_4),
                                ((x_3_2,x_4_2),(x_3_3,(x_3_4,(x_4_3,x_4_4)))))))))))) 
                H.
  Proof.
    intros .
    
    refine match H0 with
             | conj _ 
               (conj (conj _ (conj _ (conj _ _))) 
                 (conj (conj _ (conj _ (conj _ _))) 
                   (conj _ 
                     (conj (conj _ (conj _ _)) 
                       (conj (conj _ (conj _ _)) 
                         (conj _ 
                           (conj (conj _ _) 
                             (conj (conj _ _) (conj _ (conj _ (conj _ _))))))
                       ))))) =>
               _
           end.
    apply H.
  Qed.



   Lemma decompose_lt_matrix_4 :
     forall x_0_0 x_0_1 x_0_2 x_0_3 x_0_4, 
       forall x_1_0 x_1_1 x_1_2 x_1_3 x_1_4, 
         forall x_2_0 x_2_1 x_2_2 x_2_3 x_2_4, 
           forall x_3_0 x_3_1 x_3_2 x_3_3 x_3_4, 
             forall x_4_0 x_4_1 x_4_2 x_4_3 x_4_4, 
               forall y_0_0 y_0_1 y_0_2 y_0_3 y_0_4, 
                 forall y_1_0 y_1_1 y_1_2 y_1_3 y_1_4, 
                   forall y_2_0 y_2_1 y_2_2 y_2_3 y_2_4, 
                     forall y_3_0 y_3_1 y_3_2 y_3_3 y_3_4, 
                       forall y_4_0 y_4_1 y_4_2 y_4_3 y_4_4, 
                         forall (H_0_0:lt x_0_0 y_0_0), 
                           forall (H_0_1:le x_0_1 y_0_1), 
                             forall (H_0_2:le x_0_2 y_0_2), 
                               forall (H_0_3:le x_0_3 y_0_3), 
                                 forall (H_0_4:le x_0_4 y_0_4), 
                                   forall (H_1_0:le x_1_0 y_1_0), 
                                     forall (H_1_1:le x_1_1 y_1_1), 
                                       forall (H_1_2:le x_1_2 y_1_2), 
                                         forall (H_1_3:le x_1_3 y_1_3), 
                                           forall (H_1_4:le x_1_4 y_1_4), 
                                             forall (H_2_0:le x_2_0 y_2_0), 
                                               forall (H_2_1:le x_2_1 y_2_1), 
                                                 forall (H_2_2:le x_2_2 y_2_2), 
                                                   forall (H_2_3:le x_2_3 y_2_3), 
                                                     forall (H_2_4:le x_2_4 y_2_4), 
                                                       forall (H_3_0:le x_3_0 y_3_0), 
                                                         forall (H_3_1:le x_3_1 y_3_1), 
                                                           forall (H_3_2:le x_3_2 y_3_2), 
                                                             forall (H_3_3:le x_3_3 y_3_3), 
                                                               forall (H_3_4:le x_3_4 y_3_4), 
                                                                 forall (H_4_0:le x_4_0 y_4_0), 
                                                                   forall (H_4_1:le x_4_1 y_4_1), 
                                                                     forall (H_4_2:le x_4_2 y_4_2), 
                                                                       forall (H_4_3:le x_4_3 y_4_3), 
                                                                         forall (H_4_4:le x_4_4 y_4_4), 
                                                                           mat_order_strict 4 (x_0_0,
                                                         ((x_0_1,
                                                           (x_0_2,(x_0_3,x_0_4))),
                                                         ((x_1_0,
                                                           (x_2_0,(x_3_0,x_4_0))),
                                                         (x_1_1,
                                                           ((x_1_2,
                                                             (x_1_3,x_1_4)),
                                                           ((x_2_1,
                                                             (x_3_1,x_4_1)),
                                                           (x_2_2,
                                                             ((x_2_3,x_2_4),
                                                               ((x_3_2,x_4_2),
                                                                 (x_3_3,
                                                                   (x_3_4,
                                                                     (x_4_3,x_4_4))))
                                                             )))))))) 
                                                       (y_0_0,
                                                         ((y_0_1,
                                                           (y_0_2,(y_0_3,y_0_4))),
                                                         ((y_1_0,
                                                           (y_2_0,(y_3_0,y_4_0))),
                                                         (y_1_1,
                                                           ((y_1_2,(y_1_3,y_1_4)),
                                                             ((y_2_1,
                                                               (y_3_1,y_4_1)),
                                                             (y_2_2,
                                                               ((y_2_3,y_2_4),
                                                                 ((y_3_2,y_4_2),
                                                                   (y_3_3,
                                                                     (y_3_4,
                                                                       (y_4_3,y_4_4)))))
                                                             ))))))) .
     intros x_0_0 x_0_1 x_0_2 x_0_3 x_0_4 x_1_0 x_1_1 x_1_2 x_1_3 x_1_4 x_2_0 x_2_1 x_2_2.
     intros x_2_3 x_2_4 x_3_0 x_3_1 x_3_2 x_3_3 x_3_4 x_4_0 x_4_1 x_4_2 x_4_3 x_4_4 y_0_0.
     intros y_0_1 y_0_2 y_0_3 y_0_4 y_1_0 y_1_1 y_1_2 y_1_3 y_1_4 y_2_0 y_2_1 y_2_2 y_2_3.
     intros y_2_4 y_3_0 y_3_1 y_3_2 y_3_3 y_3_4 y_4_0 y_4_1 y_4_2 y_4_3 y_4_4 H H_0_0 H_0_1.
     intros H_0_2 H_0_3 H_0_4 H_1_0 H_1_1 H_1_2 H_1_3 H_1_4 H_2_0 H_2_1 H_2_2 H_2_3 H_2_4.
     intros H_3_0 H_3_1 H_3_2 H_3_3 H_3_4 H_4_0 H_4_1 H_4_2 H_4_3.
        refine (conj _
                 (conj (conj _ (conj _ (conj _ _))) 
                   (conj (conj _ (conj _ (conj _ _))) 
                     (conj _ 
                       (conj (conj _ (conj _ _)) 
                         (conj (conj _ (conj _ _)) 
                           (conj _ 
                             (conj (conj _ _) 
                               (conj (conj _ _) (conj _ (conj _ (conj _ _))))))
                            ))))));try assumption.
      Qed.



End Make_Ordered.


From Coq Require ZArithRing.

Module ZRing <: TRing . 
Definition A := Z.
Definition eq := (@eq Z).
Definition  rO := 0%Z. 
Definition rI := 1%Z.
Definition  plus := Zplus. 
Definition mult := Zmult.
Definition sub := Zminus.
Definition opp := Z.opp. 
Definition eq_Equivalence := Zsth. 
Definition Ath := Zth. 
Definition Aeqe := Zeqe.
Definition lt := (Zwf.Zwf 0).
Definition le := Z.le.
Definition o:ordering_pair eq  (Zwf.Zwf 0) Z.le .
Proof.
  apply mk_ordering_pair.
  intros.
  unfold eq in *;subst;reflexivity.
  intros x [H1 H2]. abstract lia.
  intros x y [H1 H2] [H3 H4];abstract lia.
  intros x y z [H1 H2] [H4 H5];split; abstract lia.
  unfold eq;intros;subst;reflexivity.
  intros;abstract lia.
  unfold eq;intros;abstract lia.
  intros;abstract lia.
  intros x y z H1 [H2 H3];split;abstract lia.
  intros x y z [H2 H3] H1;split;abstract lia.
  intros x y [H1 H2];abstract lia.
Defined.

Definition lt_wf : well_founded (Zwf.Zwf 0). 
simpl. apply Zwf.Zwf_well_founded. 
Qed.
End ZRing.


Module ZMatrix := Make_Ordered(ZRing).
