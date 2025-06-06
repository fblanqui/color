(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-02-09

interpretation of algebraic terms with arity
*)

Set Implicit Arguments.

From CoLoR Require Export ATerm.
From Stdlib Require Import List.
From CoLoR Require Import LogicUtil NaryFunction VecUtil VecMax NatUtil.

Section S.

  Variable Sig : Signature.

  Notation term := (term Sig). Notation terms := (vector term).

(***********************************************************************)
(** interpretation of symbols *)

  Record interpretation : Type := mkInterpretation {
    domain :> Type;
    some_elt : domain;
    fint : forall f : Sig, naryFunction1 domain (arity f)
  }.

  Variable I : interpretation.

(***********************************************************************)
(** valuations *)

  Definition valuation := variable -> domain I.

  Definition val_of_vec n (v : vector I n) : valuation := fun x =>
    match le_lt_dec n x with
      | left _ => (* n <= x *) some_elt I
      | right h => (* x < n *) Vnth v h
    end.

  (*REMARK: alternative more efficient definition*)
  Fixpoint val_of_vec2 n (v : vector I n) : valuation := fun x =>
    match x, v with
      | _, Vnil => some_elt I
      | 0, Vcons a _ => a
      | S x', Vcons _ v' => val_of_vec2 v' x'
    end.

  Lemma val_of_vec_eq : forall n (v : vector I n) x (h : x < n),
    val_of_vec v x = Vnth v h.

  Proof.
    intros. unfold val_of_vec. case (le_lt_dec n x); intro.
    absurd (x<n); lia. apply Vnth_eq. refl.
  Qed.

  Section vec_of_val.

    Variable xint : valuation.

    (*FIXME: use instead
       Definition restrict n : valuation :=
       fun x => if bgt_nat n x then xint x else some_elt I.*)

    Definition restrict n : valuation := fun x =>
      match le_lt_dec n x with
        | left _ => (* n <= x *) some_elt I
        | right _ => (* x < n *) xint x
      end.

    Fixpoint vec_of_val (n : nat) : vector I n :=
      match n as n return vector _ n with
        | O => Vnil
        | S n' => Vadd (vec_of_val n') (xint n')
      end.

    (*REMARK: attempt for being more efficient but we need casts...
       Fixpoint vec_of_val_aux k (acc : vector I k) n : vector I (n+k) :=
       match n as n return vector I (n+k) with
       | 0 => acc
       | S n' => Vcast (vec_of_val_aux (Vcons (xint n') acc) n')
       (sym_eq (plus_Snm_nSm n' k))
       end.

       Definition vec_of_val := Vcast (vec_of_val Vnil) ...*)

    Lemma Vnth_vec_of_val : forall n x (H : x < n),
      Vnth (vec_of_val n) H = xint x.

    Proof.
      intro n. elim n.
      intros x Hx. exfalso. apply (Nat.nlt_0_r Hx).
      intros p Hrec x H0. simpl vec_of_val.
      case (le_lt_eq_dec (le_S_n H0)); intro H1.
      rewrite (Vnth_addl (vec_of_val p) (xint p) H0 H1). apply Hrec.
      rewrite Vnth_addr. 2: hyp. rewrite H1. refl.
    Qed.

    (*REMARK: equivalent to restrict but less efficient*)
    Definition fval n := val_of_vec (vec_of_val n).

  End vec_of_val.

(***********************************************************************)
(** interpretation of terms *)

  Section term_int.

    Variable xint : valuation.

    Fixpoint term_int t :=
      match t with
        | Var x => xint x
        | Fun f ts => fint I f (Vmap term_int ts)
      end.

  End term_int.

  Lemma term_int_eq : forall xint1 xint2 t,
    (forall x, In x (vars t) -> xint1 x = xint2 x) ->
    term_int xint1 t = term_int xint2 t.

  Proof.
    intros xint1 xint2 t. pattern t; apply term_ind_forall; clear t; intros.
    simpl. apply H. simpl. intuition.
    apply (f_equal (fint I f)). apply Vmap_eq.
    apply Vforall_intro. intros. apply (Vforall_in H H1). intros. apply H0.
    rewrite vars_fun. apply (vars_vec_in H2 H1).
  Qed.

  Lemma term_int_eq_restrict_lt : forall xint t k,
    maxvar t < k -> term_int xint t = term_int (restrict xint k) t.

  Proof.
    intros xint t. pattern t; apply term_ind_forall; clear t; intros.
    simpl. unfold restrict. case (le_lt_dec k v); intro.
    simpl in H. absurd (v<k); lia. refl. simpl. apply (f_equal (fint I f)).
    apply Vmap_eq. apply Vforall_intro. intros. apply (Vforall_in H H1).
    rewrite maxvar_fun in H0.
    ded (Vin_map_intro (f:=@maxvar Sig) H1).
    ded (Vmax_in H2). unfold maxvars in H0. lia.
  Qed.

  Lemma term_int_eq_restrict : forall xint t,
    term_int xint t = term_int (restrict xint (maxvar t + 1)) t.

  Proof.
    intros. apply term_int_eq_restrict_lt. lia.
  Qed.

  Lemma term_int_eq_fval_lt : forall xint t k,
    maxvar t < k -> term_int xint t = term_int (fval xint k) t.

  Proof.
    intros xint t. pattern t; apply term_ind_forall; clear t; intros.
    simpl in *. unfold fval, val_of_vec. case (le_lt_dec k v); intro.
    absurd (v<k); lia. rewrite Vnth_vec_of_val. refl.
    simpl. apply (f_equal (fint I f)).
    apply Vmap_eq. apply Vforall_intro. intros. apply (Vforall_in H H1).
    rewrite maxvar_fun in H0.
    ded (Vin_map_intro (B:=nat) (f:=maxvar (Sig:=Sig)) H1).
    ded (Vmax_in H2). unfold maxvars in H0. lia.
  Qed.

  Lemma term_int_eq_fval : forall xint t,
    term_int xint t = term_int (fval xint (maxvar t + 1)) t.

  Proof.
    intros. apply term_int_eq_fval_lt. lia.
  Qed.

  Lemma Vmap_term_int_fval : forall v n k (ts : terms k),
    n > maxvars ts -> Vmap (term_int (fval v n)) ts = Vmap (term_int v) ts.

  Proof.
    induction ts. refl. simpl. rewrite maxvars_cons, gt_max. intuition.
    rewrite H, <- term_int_eq_fval_lt. refl. hyp.
  Qed.

End S.

Arguments mkInterpretation [Sig domain] _ _.
