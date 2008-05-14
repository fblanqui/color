(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-04-28
- Frederic Blanqui, 2005-01-28

terms whose variable indexes are bounded
*)

(* $Id: ABterm.v,v 1.6 2008-05-14 14:30:54 blanqui Exp $ *)

Set Implicit Arguments.

Section S.

Require Export ASignature.

Variable Sig : Signature.

Require Export ATerm.

Notation term := (term Sig).
Notation terms := (vector term).

Section bterm.

Variable k : nat.

Inductive bterm : Set :=
  | BVar : forall x : nat, x<=k -> bterm
  | BFun : forall f : Sig, vector bterm (arity f) -> bterm.

(***********************************************************************)
(** induction principles *)

Reset bterm_rect.

Notation bterms := (vector bterm).

Section bterm_rect_def.

Variables
  (P : bterm -> Type)
  (Q : forall n : nat, bterms n -> Type).

Hypotheses
  (H1 : forall x (h : x<=k), P (BVar h))
  (H2 : forall (f : Sig) (v : bterms (arity f)), Q v -> P (BFun f v))
  (H3 : Q Vnil)
  (H4 : forall (t : bterm) n (v : bterms n), P t -> Q v -> Q (Vcons t v)).

Fixpoint bterm_rect (t : bterm) : P t :=
  match t as t return P t with
    | BVar x h => H1 h
    | BFun f v =>
      let fix bterms_rect n (v : bterms n) {struct v} : Q v :=
        match v as v return Q v with
          | Vnil => H3
          | Vcons t' n' v' => H4 (bterm_rect t') (bterms_rect n' v')
        end
	in H2 f (bterms_rect (arity f) v)
  end.

End bterm_rect_def.

Definition bterm_ind (P : bterm -> Prop) (Q : forall n, bterms n -> Prop) :=
  bterm_rect P Q.

Definition bterm_rec (P : bterm -> Set) (Q : forall n, bterms n -> Set) :=
  bterm_rect P Q.

(***********************************************************************)
(** injection of bterm into term *)

Fixpoint term_of_bterm (bt : bterm) : term :=
  match bt with
    | BVar v _ => Var v
    | BFun f bts =>
      let fix terms_of_bterms n (bts : bterms n) {struct bts} : terms n :=
	match bts in vector _ n return terms n with
	  | Vnil => Vnil
	  | Vcons bt n' bts' => Vcons (term_of_bterm bt) (terms_of_bterms n' bts')
	end
	in Fun f (terms_of_bterms (arity f) bts)
  end.

Lemma term_of_bterm_fun : forall f (bts : bterms (arity f)),
  term_of_bterm (BFun f bts) = Fun f (Vmap term_of_bterm bts).

Proof.
intros. reflexivity.
Qed.

(***********************************************************************)
(** injection of term into bterm *)

Notation max_le := (maxvar_le k).

Fixpoint inject_term (t : term) : max_le t -> bterm :=
  match t as t0 return max_le t0 -> bterm with
    | Var x => fun H => BVar (maxvar_var H)
    | Fun f ts => fun H =>
      let fix inject_terms n (ts : terms n) {struct ts} : 
        Vforall max_le ts -> bterms n :=
	match ts as v in vector _ n0
	  return Vforall max_le v -> bterms n0 with
          | Vnil => fun _ => Vnil
          | Vcons t' p' ts' => fun H =>
	    Vcons (inject_term (proj1 H)) (inject_terms p' ts' (proj2 H))
	end
      in BFun f (inject_terms (arity f) ts (maxvar_le_fun H))
  end.

Fixpoint inject_terms (n : nat) (ts : terms n) {struct ts} : 
  Vforall max_le ts -> bterms n :=
  match ts as v in vector _ n0
    return Vforall max_le v -> bterms n0 with
    | Vnil => fun _ => Vnil
    | Vcons t' p' ts' => fun H =>
      Vcons (inject_term (proj1 H)) (inject_terms ts' (proj2 H))
  end.

Implicit Arguments inject_terms [n ts].

Lemma inject_term_eq : forall f ts (H : max_le (Fun f ts)),
  inject_term H = BFun f (inject_terms (maxvar_le_fun H)).

Proof.
intros. simpl. auto.
Qed.

Lemma inject_terms_nth : forall i n (ts : terms n) (H : Vforall max_le ts)
  (ip : i < n), 
  Vnth (inject_terms H) ip = inject_term (Vforall_nth max_le ts ip H).

Proof.
  induction i; intros.
  destruct ts. elimtype False. omega. simpl. 
  match goal with |- inject_term ?Hl = inject_term ?Hr =>
    rewrite (le_unique Hl Hr) end. refl.
  destruct ts. elimtype False. omega.
  simpl. rewrite IHi.
  match goal with |- inject_term ?Hl = inject_term ?Hr =>
    rewrite (le_unique Hl Hr) end. refl.
Qed.

(***********************************************************************)
(** interpretation of bterm's *)

Require Export AInterpretation.

Variables (I : interpretation Sig) (xint : valuation I).

Notation D := (domain I).
Notation fint := (fint I).

Fixpoint bterm_int (t : bterm) { struct t } : D :=
  match t with
    | BVar x _ => xint x
    | BFun f v =>
      let fix bterms_int (n : nat) (v : bterms n) { struct v } : vector D n :=
        match v in vector _ n return vector D n with
          | Vnil => Vnil
          | Vcons t' n' v' => Vcons (bterm_int t') (bterms_int n' v')
        end
      in fint f (bterms_int (arity f) v)
  end.

Definition bterms_int (n : nat) (ts : bterms n) : vector D n :=
  Vmap bterm_int ts.

Lemma bterm_int_fun : forall (f : Sig) (v : bterms (arity f)),
    bterm_int (BFun f v) = fint f (bterms_int v).

Proof.
intros. simpl.
apply (f_equal (fint f)).
induction v.
 auto.
 rewrite IHv. auto.
Qed.

End bterm.

Implicit Arguments inject_terms [k n ts].

(***********************************************************************)
(** relation between bterm_int and term_int *)

Section term_int.

Variables (I : interpretation Sig) (xint : valuation I).

Notation D := (domain I).

Let P (t : term) := forall (k : nat) (H : maxvar_le k t),
  bterm_int xint (inject_term H) = term_int xint t.

Let Q (n1 : nat) (ts : terms n1) :=
  forall (k : nat) (H : Vforall (maxvar_le k) ts),  
    (fix bterms_int (n0 : nat) (v : vector (bterm k) n0) {struct v}
      : vector D n0 :=
      match v in vector _ n1 return vector D n1 with
	| Vnil => Vnil
	| Vcons t' n' v' => Vcons (bterm_int xint t') (bterms_int n' v')
      end)
    n1 (inject_terms H) = Vmap (term_int xint) ts.

Lemma term_int_eq_bterm_int : forall t, P t.

Proof.
intro t. apply (term_ind P Q).
 intro x. unfold P. simpl. intros. reflexivity.

 intros f ts. unfold Q. intro H. unfold P.
 intros n Hn.
 rewrite inject_term_eq. simpl bterm_int. rewrite term_int_fun.
 apply (f_equal (fint I f)).
 generalize (maxvar_le_fun Hn). intro H0.
 generalize (H _ H0). intro H1. assumption.

 unfold Q, P. simpl. auto.

 intros t' n' v'. unfold P, Q. intros H1 H2. intros n H3.
 simpl in H3. generalize H3. clear H3.
 intro H3.
 generalize (H1 _ (proj1 H3)). clear H1. intro H1.
 generalize (H2 _ (proj2 H3)). clear H2. intro H2.
 simpl. unfold Vforall in H1, H2. rewrite H1. rewrite H2. reflexivity.
Qed.
 
End term_int.

Implicit Arguments inject_terms [k n ts].

(***********************************************************************)
(** lemmas about bterm *)

Implicit Arguments le_trans [n m p].

Fixpoint bterm_le k (bt : bterm k) l (h0 : k <= l) {struct bt} : bterm l :=
  match bt with
    | BVar x h => BVar (le_trans h h0)
    | BFun f bts =>
      let fix bterms_le k n (bts : vector (bterm k) n) l (h0 : k <= l)
	{struct bts} : vector (bterm l) n :=
	match bts in vector _ n return vector (bterm l) n with
	  | Vnil => Vnil
	  | Vcons bt n' bts' => Vcons (bterm_le bt h0) (bterms_le k n' bts' l h0)
	end
	in BFun f (bterms_le k (arity f) bts l h0)
  end.

Fixpoint bterms_le k n (bts : vector (bterm k) n) l (h0 : k <= l) {struct bts}
  : vector (bterm l) n :=
  match bts in vector _ n return vector (bterm l) n with
    | Vnil => Vnil
    | Vcons bt n' bts' => Vcons (bterm_le bt h0) (bterms_le bts' h0)
  end.

Definition bterm_plus k bt l := bterm_le bt (le_plus k l).

Definition bterms_plus k n (bts : vector (bterm k) n) l
  := bterms_le bts (le_plus k l).

End S.

Implicit Arguments BVar [Sig k x].
Implicit Arguments BFun [Sig k].
Implicit Arguments inject_terms [Sig k n ts].
