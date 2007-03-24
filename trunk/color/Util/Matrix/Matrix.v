(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski and Hans Zantema, 2007-03

  Matrices as a functor.
*)

Require Import MatrixCarrier.
Require Import VecUtil.

Set Implicit Arguments.

(** module type structure for matrices *)
Module Type TMatrix.

  Declare Module C : Carrier.
  Notation A := C.A.
  Notation A0 := C.A0.
  Notation Aplus := C.Aplus.
  Notation Amult := C.Amult.
  Notation vec := (vector A).

  Parameter matrix : nat -> nat -> Set.
  Definition row_matrix n := matrix 1 n.
  Definition col_matrix n := matrix n 1.  
  Parameter vector_to_row_matrix : forall n (v : vec n), row_matrix n.
  Parameter vector_to_col_matrix : forall n (v : vec n), col_matrix n.
  Parameter row_matrix_to_vector : forall n (m : row_matrix n), vec n.
  Parameter col_matrix_to_vector : forall n (m : col_matrix n), vec n.

  Parameter mat_build : forall m n (f : forall i j, i < m -> j < n -> A), matrix m n.
  Parameter mat_transpose : forall m n, matrix m n -> matrix n m.
  Parameter mat_add : forall m n, matrix m n -> matrix m n -> matrix m n.
  Parameter mat_mult : forall m n p, matrix m n -> matrix n p -> matrix m p.

  Parameter get_elem : forall m n, matrix m n -> forall i j, i < m -> j < n -> A.
  Parameter get_row : forall m n, matrix m n -> forall i, i < m -> vector A n.
  Parameter get_col : forall m n, matrix m n -> forall i, i < n -> vector A m.

End TMatrix.

(** functor building matrices structure given a carrier *)
Module Matrix (C : Carrier) <: TMatrix with Module C := C.

  Module C := C.

   (** basic definitions *)
  Notation A := C.A.
  Notation A0 := C.A0.
  Notation Aplus := C.Aplus.
  Notation Amult := C.Amult.

  Notation "x *A y" := (Amult x y) (at level 50).
  Notation "x +A y" := (Aplus x y) (at level 40).
  Notation vec := (vector A).

   (* Matrix represented by a vector of vectors (in a row-wise fashion) *)
  Definition matrix m n := vector (vec n) m.

   (** accessors *)
  Definition get_row m n (M : matrix m n) i (i_ok : i < m) := Vnth M i_ok.

  Definition get_col m n (M : matrix m n) i (i_ok : i < n) :=
    Vmap (fun v => Vnth v i_ok) M.

  Definition get_elem m n (M : matrix m n) i j (i_ok : i < m) (j_ok : j < n) :=
    Vnth (get_row M i_ok) j_ok.

   (** matrix construction *)
  Definition Vbuild : forall n (gen : forall i, i < n -> A), vec n.
  Proof.
    induction n; intros.
    exact Vnil.
    set (gen' := fun i H => gen (S i) (lt_n_S H)).
    set (access0 := lt_O_Sn n).
    exact (Vcons(gen 0 access0) (IHn gen')).
  Defined.

  Definition mat_build : forall m n (gen : forall i j, i < m -> j < n -> A), matrix m n.
  Proof.
    induction m; intros.
    exact Vnil.
    set (gen_1 := fun j => gen 0 j (lt_O_Sn m)).
    set (gen' := fun i j H => gen (S i) j (lt_n_S H)).
    exact (Vcons (Vbuild gen_1) (IHm n gen')).
  Defined.

   (** 1-row and 1-column matrices *)

  Definition row_matrix n := matrix 1 n.
  Definition col_matrix n := matrix n 1.

  Definition vector_to_row_matrix n (v : vec n) : row_matrix n := mat_build (fun i j _ H => Vnth v H).
  Definition vector_to_col_matrix n (v : vec n) : col_matrix n := mat_build (fun i j H _ => Vnth v H).

  Definition access_0 : 0 < 1 := le_n 1.

  Definition row_matrix_to_vector n (m : row_matrix n) := get_row m access_0.
  Definition col_matrix_to_vector n (m : col_matrix n) := get_col m access_0.

   (** matrix operations *)

   (* transposition *)
  Definition mat_transpose m n (M : matrix m n) := mat_build (fun _ _ i j => get_elem M j i).

   (* addition *)
  Definition vec_add n (L R : vec n) := Vmap2 Aplus L R.

  Definition mat_add m n (L R : matrix m n) :=  Vmap2 (@vec_add n) L R.

   (* multiplication *)
  Definition dot_product n (l r : vec n) := Vfold_left Aplus A0 (Vmap2 Amult l r).

  Definition vect_matr_prod n p (v : vec n) (M : matrix n p) := 
    Vmap (dot_product v) (mat_transpose M).

  Definition mat_mult m n p (L : matrix m n) (R : matrix n p) :=
    Vmap (fun v => vect_matr_prod v R) L.

End Matrix.

Module NMatrix := Matrix NCarrier.
