(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-04-20
- Frederic Blanqui, 2005-02-24

polynomials with multiple variables and integer coefficients
*)

Set Implicit Arguments.

From CoLoR Require Import VecUtil LogicUtil NatUtil.
From Stdlib Require Import Arith List Lia.
From Stdlib Require Export ZArith.

(** monomials with n variables *)

Notation monom := (vector nat).

Lemma monom_eq_dec : forall n (m1 m2 : monom n), {m1=m2} + {~m1=m2}.

Proof. intros. eapply eq_vec_dec. apply eq_nat_dec. Defined.

(** polynomials with n variables *)

Definition poly n := list (Z * monom n).

Declare Scope poly_scope.
Delimit Scope poly_scope with poly.
Bind Scope poly_scope with poly.

(** coefficient of monomial m in polynomial p *)

Local Open Scope Z_scope.

Fixpoint coef n (m : monom n) (p : poly n) : Z :=
  match p with
    | nil => 0
    | cons (c,m') p' =>
      match monom_eq_dec m m' with
	| left _ => c + coef m p'
	| right _ => coef m p'
      end
  end.

(***********************************************************************)
(** simple polynomials *)

(* monomial 1 *)

Notation mone := (Vconst O).

(* monomial x_i for i<n *)

Fixpoint mxi (n : nat) : forall i, lt i n -> monom n :=
  match n as n return forall i, lt i n -> monom n with
    | O => fun i h => False_rec (monom O) (Nat.nlt_0_r h)
    | S n' => fun i =>
      match i as i return lt i (S n') -> monom (S n') with
	| O => fun _ => Vcons (S O) (mone n')
	| S _ => fun h => Vcons O (mxi (NatCompat.lt_S_n h))
      end
  end.

(* polynomial x_i for i<n *)

Definition pxi n i (h : lt i n) := (1, mxi h) :: nil.

(* null polynomial *)

Definition pzero (n : nat) : poly n := nil.

(* constant polynomial c *)

Definition pconst n (c : Z) : poly n := (c, mone n) :: nil.

(***********************************************************************)
(** multiplication by a constant *)

Definition cpmult c n (p : poly n) := map (fun cm => (c * fst cm, snd cm)) p.

Definition popp n (p : poly n) := map (fun cm => (- fst cm, snd cm)) p.

Notation "'-' p" := (popp p) (at level 35, right associativity) : poly_scope.

(***********************************************************************)
(** addition *)

Fixpoint mpplus n (c : Z) (m : monom n) (p : poly n) : poly n :=
  match p with
    | nil => (c,m) :: nil
    | cons (c',m') p' =>
      match monom_eq_dec m m' with
	| left _ => (c+c',m) :: p'
	| right _ => (c',m') :: mpplus c m p'
      end
  end.

Fixpoint pplus n (p1 p2 : poly n) : poly n :=
  match p1 with
    | nil => p2
    | cons (c,m) p' => mpplus c m (pplus p' p2)
  end.

Infix "+" := pplus : poly_scope.

Local Open Scope poly_scope.

Definition pminus n (p1 p2 : poly n) := p1 + (- p2).

Infix "-" := pminus : poly_scope.

(***********************************************************************)
(** multiplication *)

Definition mmult n (m1 m2 : monom n) := Vmap2 plus m1 m2.

Definition mpmult n c (m : monom n) (p : poly n) :=
  map (fun cm => (c * fst cm, mmult m (snd cm))) p.

Fixpoint pmult n (p1 p2 : poly n) : poly n :=
  match p1 with
    | nil => nil
    | cons (c,m) p' => mpmult c m p2 + pmult p' p2
  end.

Infix "*" := pmult : poly_scope.

(***********************************************************************)
(** power *)

Fixpoint ppower n (p : poly n) (k : nat) : poly n :=
  match k with
    | O => pconst n 1
    | S k' => p * ppower p k'
  end.

Infix "^" := ppower : poly_scope.

(***********************************************************************)
(** composition *)

Fixpoint mcomp (n : nat) : monom n -> forall k, vector (poly k) n -> poly k :=
  match n as n return monom n -> forall k, vector (poly k) n -> poly k with
    | O => fun _ k _ => pconst k 1
    | S _ => fun m _ ps => Vhead ps ^ Vhead m * mcomp (Vtail m) (Vtail ps)
  end.

Fixpoint pcomp n (p : poly n) k (ps : vector (poly k) n) : poly k :=
  match p with
    | nil => nil
    | cons (c,m) p' => cpmult c (mcomp m ps) + pcomp p' ps
  end.

Local Close Scope poly_scope.

(***********************************************************************)
(** evaluation *)

Notation vec := (vector Z).

From CoLoR Require Import ZUtil.

Open Scope Z_scope.

Fixpoint meval (n : nat) : monom n -> vec n -> Z :=
  match n as n return monom n -> vec n -> Z with
    | O => fun _ _ => 1
    | S _ => fun m v => power (Vhead v) (Vhead m) * meval (Vtail m) (Vtail v)
  end.

Fixpoint peval n (p : poly n) (v : vec n) : Z :=
  match p with
    | nil => 0
    | cons (c,m) p' => c * meval m v + peval p' v
  end.

Lemma meval_app : forall n1 (m1 : monom n1) (v1 : vec n1)
  n2 (m2 : monom n2) (v2 : vec n2),
  meval (Vapp m1 m2) (Vapp v1 v2) = meval m1 v1 * meval m2 v2.

Proof.
induction m1. intros. VOtac. simpl. apply zeqr.
intros. VSntac v1. simpl. rewrite IHm1. ring.
Qed.

Lemma meval_one : forall n (v : vec n), meval (mone n) v = 1.

Proof. induction v; simpl. refl. rewrite IHv. refl. Qed.

Lemma meval_xi : forall n i (H : lt i n) (v : vec n),
  meval (mxi H) v = Vnth v H.

Proof.
induction n. intros. absurd (lt i 0). lia. hyp.
intro. destruct i; intros; VSntac v.
simpl. rewrite meval_one. ring. simpl. rewrite IHn. apply zeql.
Qed.

Lemma peval_const : forall n c (v : vec n), peval (pconst n c) v = c.

Proof. intros. simpl. rewrite meval_one. ring. Qed.

Lemma peval_app : forall n (p1 p2 : poly n) (v : vec n),
  peval (p1 ++ p2) v = peval p1 v + peval p2 v.

Proof.
intros. elim p1. auto. intros (c,m). intros. simpl. rewrite H. ring.
Qed.

Lemma peval_opp : forall n (p : poly n) (v : vec n),
  peval (- p) v = - peval p v.

Proof.
intros. elim p. auto. intros (c,m). intros. simpl. rewrite H. ring.
Qed.

Lemma peval_mpplus : forall n c (m : monom n) (p : poly n) (v : vec n),
  peval (mpplus c m p) v = c * meval m v + peval p v.

Proof.
intros. elim p. auto. intros (c',m'). intros. simpl.
case (monom_eq_dec m m'); simpl; intro. subst m'. ring. rewrite H. ring.
Qed.  

Lemma peval_plus n (p1 p2 : poly n) (v : vec n) :
  peval (p1 + p2) v = peval p1 v + peval p2 v.

Proof.
elim p1. auto. intros (c,m). intros. simpl. rewrite peval_mpplus, H. ring.
Qed.

Lemma peval_minus n (p1 p2 : poly n) (v : vec n) :
  peval (p1 - p2) v = peval p1 v - peval p2 v.

Proof. unfold pminus. rewrite peval_plus, peval_opp. ring. Qed.

Lemma meval_mult : forall n (m1 m2 : monom n) (v : vec n),
  meval (mmult m1 m2) v = meval m1 v * meval m2 v.

Proof.
induction n; intros. VOtac. refl. VSntac m1. VSntac m2.
simpl. unfold mmult in IHn. rewrite IHn, power_plus. ring.
Qed.

Lemma peval_mpmult : forall n c (m : monom n) (p : poly n) (v : vec n),
  peval (mpmult c m p) v = c * meval m v * peval p v.

Proof.
induction p; intros; simpl. ring.
destruct a. simpl. rewrite IHp, meval_mult. ring.
Qed.

Lemma peval_mult : forall n (p1 p2 : poly n) (v : vec n),
  peval (p1 * p2) v = peval p1 v * peval p2 v.

Proof.
induction p1; intros; simpl. refl. destruct a. simpl.
rewrite peval_plus, peval_mpmult, IHp1. ring.
Qed.

Lemma peval_power : forall n (p : poly n) (k : nat) (v : vec n),
  peval (ppower p k) v = power (peval p v) k.

Proof.
induction k; intros; simpl. rewrite meval_one. ring.
rewrite peval_mult, IHk. refl.
Qed.

Lemma peval_mcomp : forall n k (m : monom n) (ps : vector (poly k) n)
  (v : vec k), peval (mcomp m ps) v = meval m (Vmap (fun p => peval p v) ps).

Proof.
induction n; intros. VOtac. simpl. rewrite zeql, meval_one. ring.
VSntac m. VSntac ps. simpl. rewrite peval_mult, peval_power, IHn. refl.
Qed.

Lemma peval_cpmult : forall n c (p : poly n) (v : vec n),
  peval (cpmult c p) v = c * peval p v.

Proof.
induction p; intros; simpl. ring. destruct a. simpl. rewrite IHp. ring.
Qed.

Lemma peval_comp : forall n k (p : poly n) (ps : vector (poly k) n)
  (v : vec k), peval (pcomp p ps) v = peval p (Vmap (fun p => peval p v) ps).

Proof.
induction p; intros; simpl. refl. destruct a.
rewrite peval_plus, peval_cpmult, IHp, peval_mcomp. refl.
Qed.
