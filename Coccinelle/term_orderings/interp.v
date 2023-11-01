From Coq Require Import List ZArith Lia.
From Coq Require Zwf.

From CoLoR Require Import weaved_relation equational_theory term_spec terminaison.

Set Implicit Arguments.

Record ordering_pair (A:Type) (eq:A -> A -> Prop)   (lt le : A -> A -> Prop)
:= mk_ordering_pair {
  lt_morph: forall x x', eq x x' -> forall y y', eq y y' -> (lt x y <-> lt x' y');
  lt_irrefl : forall x, ~ lt x x;
  lt_antisym : forall x y, lt x y -> ~lt y x;
  lt_trans : forall x y z, lt x y -> lt y z -> lt x z;
  le_morph : forall x x', eq x x' -> forall y y', eq y y' -> (le x y <-> le x' y');
  le_refl : forall x, le x x;
  le_antisym : forall x y, le x y -> le y x -> eq x y;
  le_trans : forall x y z, le x y -> le y z -> le x z;
  le_lt_compat_left : forall x y z, le x y -> lt y z -> lt x z;
  le_lt_compat_right : forall x y z, lt x y -> le y z -> lt x z;
  lt_included_le : forall x y, lt x y -> le x y
}.


Definition o_Z : forall m, ordering_pair (@eq Z) (Zwf.Zwf m) Z.le.
Proof.
  intros m.
  constructor.
  intros;subst;reflexivity.
  intros x;intro abs;destruct abs;lia.
  intros x y H;destruct H;intro abs;destruct abs;lia. 
  intros x y z H1 H2;destruct H1; destruct H2;constructor;lia. 
  intros;subst;reflexivity.
  intros x;lia.
  intros x y  H1 H2;lia. 
  intros x y z H1 H2;lia. 
  intros x y z H1 H2;destruct H2;split;lia. 
  intros x y z H1 H2;destruct H1;split;lia. 
  intros x y H1;destruct H1;lia. 
Defined.


Module Interp(EQT:equational_theory_spec.EqTh).
  Import EQT.
  Import T.
  Import F.
  
 Section S.
   Hypothesis A : Type.
 
   Hypothesis Ale Alt Aeq : A -> A -> Prop.

   Hypothesis Aop : ordering_pair Aeq Alt Ale.

   Hypothesis A0 : A.
   Fixpoint Pol_type (n:nat) := 
     match n with 
       | 0 => A 
       | S n => A -> Pol_type n
     end.

   Definition get_arity f := 
     match arity f with 
       | term_spec.Free n => n 
       | _ => 2
     end.
 
   Fixpoint Pol_null (n:nat) : Pol_type n := 
     match n with 
       | 0 => A0 
       | S n => (fun _ : A => Pol_null n)
     end.


   Hypothesis Pols : forall f, Pol_type (get_arity f).

   Definition measure : term -> A. 
   Proof.
     fix measure 1.
     intros [a | f l].
     exact A0.
     assert (f_pol := Pols f).
     clear Pols.
     set (n:= get_arity f) in *.
     clearbody n.
     revert l n f_pol.
     fix measure_list 1.
     intros [| t l].
     intros [| n].
     intros a;exact a.
     intros _;exact A0.
     intros [| n].
     intros _;exact A0.
     simpl.
     intros.
     apply measure_list with (n:=n).
     apply l.
     apply f_pol.
     apply (measure t).
   Defined.

   Fixpoint measure_list (l: list term) : forall n0 : nat, Pol_type n0 -> A := 
     match l with
       | nil =>
         fun n0 : nat =>
           match n0 as n1 return (Pol_type n1 -> A) with
             | 0 => fun a : Pol_type 0 => a
             | S n1 => fun _ : Pol_type (S n1) => A0
           end
       | t0 :: l1 =>
         fun n0 : nat =>
           match n0 as n1 return (Pol_type n1 -> A) with
             | 0 => fun _ : Pol_type 0 => A0
             | S n1 =>
               fun f_pol0 : A -> Pol_type n1 =>
                 measure_list l1 n1 (f_pol0 (measure t0))
           end
     end.

   Local Notation "a <= b" := (Ale a b).
   Local Notation "a < b" := (Alt a b).
     

   Fixpoint monotonic_aux n : Pol_type n -> Pol_type n -> Prop:=
     match n as m return Pol_type m -> Pol_type m -> Prop with 
       | 0 => fun a b => Ale a b
       | S n => fun P1 P2 => 
         forall x1 x2, (A0<=x1) /\ (x1 <= x2) -> monotonic_aux n (P1 x1) (P2 x2)
     end.

   Definition monotonic f (Pols:Pol_type (get_arity f)) := 
     monotonic_aux (get_arity f) Pols Pols.
   Hypothesis All_monotonic : forall f, monotonic f (Pols f).
 

   Fixpoint bounded_aux n : Pol_type n -> Type:=
     match n as m return Pol_type m -> Type with 
       | 0 => fun a => Ale A0 a
       | S n => fun P1 => 
         forall x1, (A0<=x1) -> bounded_aux n (P1 x1) 
     end.

   Definition bounded f (Pols : forall f, Pol_type (get_arity f))
     := bounded_aux (get_arity f) (Pols f).
   Hypothesis All_bounded : forall f, bounded f Pols.

   Lemma measure_bounded : forall t, A0 <= measure t.
   Proof.
     fix measure_bounded 1.
     intros [a | f l].
     simpl.
     apply Aop.(le_refl).
     unfold measure.
     generalize (All_bounded f).
     unfold bounded.
     set (f_pol := Pols f).
     clearbody f_pol.
     revert f_pol.
     generalize (get_arity f).
     revert l .
     fix measure_bounded_list 1.
     intros [|t l].
     intros [|n].
     intros a.
     simpl. intros p;exact p.
     intros _ _;apply Aop.(le_refl).
     intros [|n] f_pol Hb.
     apply Aop.(le_refl).
     simpl in f_pol,Hb|-.
     apply measure_bounded_list.
     apply Hb.
     apply measure_bounded.
   Qed.

   Hypothesis rules : term -> term -> Prop.
   Hypothesis rules_monotonic :
    forall l r, 
     (EQT.axiom rules r l) -> measure r <= measure l.


Lemma measure_monotonic_aux : 
  forall l 
    (IHl : forall t : term, In t l -> 
           forall r : term, one_step rules r t -> measure r <= measure t)
      k1, one_step_list (one_step rules) k1 l ->
  forall n (P1 P2 : Pol_type n), monotonic_aux n P1 P2 ->
           measure_list k1 n P1 <= measure_list l n P2.
Proof.
intros l IHl k1 H1.
destruct (one_step_in_list H1) as [t1 [t2 [l1 [l2 [K [K1 K2]]]]]].
assert (Ht : measure t2 <= measure t1).
apply IHl; [subst; apply in_or_app; right; left; apply eq_refl | assumption].
subst l k1.
clear IHl H1 K.
induction l1 as [ | a1 l1]; intros [ | n] P1 P2 Hmon; simpl.
apply Aop.(le_refl).
simpl in P1, P2, Hmon.
set (P1':=P1 (measure t2)).
set (P2':=P2 (measure t1)).
assert (Hmon':monotonic_aux n P1' P2').
unfold P1', P2'.
apply Hmon with (x1:=measure t2) (x2:=measure t1).
split; [apply measure_bounded | assumption].
clearbody P1';clearbody P2'.
clear P1 P2 Hmon.
revert n P1' P2' Hmon'.
induction l2 as [|t l];intros n P1 P2 Hmon.
simpl.
destruct n.
simpl in *.
apply Hmon.
apply Aop.(le_refl).
simpl.
destruct n.
apply Aop.(le_refl).
apply IHl.
apply Hmon.
split;[apply measure_bounded| apply Aop.(le_refl)].
apply Aop.(le_refl).

apply IHl1; trivial.
simpl in P1, P2, Hmon.
apply Hmon.
split;[apply measure_bounded| apply Aop.(le_refl)].
Qed.

Lemma measure_monotonic :
    forall l r, 
     (EQT.one_step rules r l) -> measure r <= measure l.
   Proof.
   intro l; pattern l; apply term_rec3; clear l.
   (* 1/2 variable case *)
   intros v r H; inversion H as [t1 t2 H1 | ]; clear H; subst.
   apply rules_monotonic; assumption.
   (* 1/2 compound term case *)
   intros f l IHl r H.
   inversion H as [t1 t2 H1 | g k1 k2 H1 H2 H3];
   clear H; subst.
   apply rules_monotonic; assumption.
   assert (IH : forall n (P1 P2 : Pol_type n), monotonic_aux n P1 P2 ->
           measure_list k1 n P1 <= measure_list l n P2).
   apply measure_monotonic_aux; trivial.
   simpl; apply IH; apply All_monotonic.
   Qed.

   Lemma measure_list_monotonic :
    forall l1 l2, 
     (one_step_list (one_step rules) l1 l2) -> 
     forall n (P1 P2:Pol_type n), monotonic_aux  n P1 P2 -> 
       measure_list l1 n P1 <= measure_list l2 n P2.
   Proof.
     intros l1 l2 H.
     apply measure_monotonic_aux; trivial.
     intros t t_in_l2; apply measure_monotonic.
   Qed.

      Lemma measure_star_monotonic :
    forall l r, 
     (refl_trans_clos (EQT.one_step rules) r l) ->
      measure r <= measure l.
   Proof.
     intros.
     destruct H as [x | r l H].
     apply Aop.(le_refl).
     induction H.
     apply measure_monotonic; assumption.
     apply Aop.(le_trans) with (measure y).
     apply measure_monotonic; assumption.
     assumption.
   Qed.

   Hypothesis Marked_pols : forall f, (defined rules f) -> Pol_type (get_arity f).
   Hypothesis defined_dec : forall f, {defined rules f} + {~defined rules f}.
   Hypothesis Marked_pols_monononic : forall f (H:defined rules f), monotonic f (Marked_pols H).

   Definition marked_measure : term -> A.
   Proof.
     fix marked_measure 1.
     intros [a|f l].
     exact (measure (Var a)).
     case (defined_dec f).
     intros Hdef.
     apply (measure_list l (get_arity f) (Marked_pols Hdef)).
     intros _ ;apply (measure (Term f l)).
   Defined.

   Lemma marked_measure_monotonic : 
    forall f l1 l2, 
     (one_step_list (one_step rules) l2 l1) -> 
     marked_measure (Term f l2) <= marked_measure (Term f l1).
   Proof.
     intros f l1 l2 H.
     simpl.
     case (defined_dec f);[intro Hdef|intro Hconst].
     apply measure_list_monotonic. assumption.
     apply Marked_pols_monononic.

     apply measure_list_monotonic. assumption.
     apply All_monotonic.
   Qed.

   Lemma marked_measure_star_monotonic : 
    forall f l1 l2, 
      refl_trans_clos (one_step_list (one_step rules)) l2 l1 -> 
     marked_measure (Term f l2) <= marked_measure (Term f l1).
   Proof.
     intros .
     destruct H as [x | r l H].
     apply Aop.(le_refl).
     induction H.
     apply marked_measure_monotonic; assumption.
     apply Aop.(le_trans) with (marked_measure (Term f y)).
     apply marked_measure_monotonic; assumption.
     assumption.
   Qed.

   Hypothesis rules_ref : 
     forall s t : term,
       rules s t -> forall x : variable, In x (var_list s) -> In x (var_list t).
 
   Hypothesis  rules_non_var: forall (v : variable) (t : term), ~ rules t (Var v) .

   Hypothesis rules_well_formed :
     forall s t : term, rules s t -> well_formed s /\ well_formed t.
   
   Hypothesis inject : nat -> variable. 
   Hypothesis inject_inv : variable -> nat.
   
   Hypothesis inject_inverse : forall n : nat, inject_inv (inject n) = n.

   Hypothesis rules_strictly_monotonic :
     forall l r, 
       (EQT.axiom rules r l) -> 
       well_formed l -> measure r < measure l.

   Fixpoint monotonic_strict_aux b n : Pol_type n -> Pol_type n -> Prop:=
     match n as m return Pol_type m -> Pol_type m -> Prop with 
       | 0 => fun a b => Alt a b
       | S n => 
         match b with 
           | true => 
             fun P1 P2 => 
               forall x1 x2, (A0<=x1) /\ (x1 <= x2) -> monotonic_strict_aux true n (P1 x1) (P2 x2)
           | false => 
             fun P1 P2 => 
               (forall x1 x2, (A0<=x1) /\ (x1 <= x2) -> monotonic_strict_aux false n (P1 x1) (P2 x2))/\
               (forall x1 x2, (A0<=x1) /\ (x1 < x2) -> monotonic_strict_aux true n (P1 x1) (P2 x2))
         end
     end.
   
   Hypothesis All_strictly_monotonic : forall f, 
     match get_arity f with 
       | 0 => True 
       | _ => monotonic_strict_aux false (get_arity f) (Pols f) (Pols f)
     end.

Lemma measure_strictly_monotonic_aux :
  forall l2  (IHl2 : forall t : term, In t l2 -> 
           forall r : term, one_step rules r t -> well_formed t -> measure r < measure t),
  forall l1, one_step_list (one_step rules) l1 l2 -> (forall t, In t l2 -> well_formed t) ->
  forall n (P1 P2 : Pol_type n), length l2 = n -> monotonic_strict_aux false n P1 P2 ->
  measure_list l1 n P1 < measure_list l2 n P2.
Proof.
intros l IHl k1 H1 Wl.
destruct (one_step_in_list H1) as [t1 [t2 [l1 [l2 [K [K1 K2]]]]]].
assert (Ht : measure t2 < measure t1).
apply IHl; [idtac | assumption | apply Wl]; subst; apply in_or_app; right; left; apply eq_refl.
subst l k1.
clear IHl H1 K Wl.
induction l1 as [ | a1 l1]; intros [ | n] P1 P2 L Hmon; simpl.
discriminate.
simpl in P1, P2, Hmon, L; injection L; clear L; intro L.
set (P1':=P1 (measure t2)).
set (P2':=P2 (measure t1)).
assert (Hmon' : monotonic_strict_aux true n P1' P2').
unfold P1', P2'.
destruct Hmon as [_ Hmon].
apply Hmon with (x1:=measure t2) (x2:=measure t1).
split; [apply measure_bounded | assumption].
clearbody P1'; clearbody P2'.
clear P1 P2 Hmon.
revert n P1' P2' Hmon' L.
induction l2 as [ | t l]; intros n P1 P2 Hmon L.
simpl in *; subst n; apply Hmon.
destruct n.
discriminate L.
simpl in *; apply IHl.
apply Hmon; split;[apply measure_bounded| apply Aop.(le_refl)].
injection L; intro; assumption.
discriminate L.
apply IHl1.
injection L; intro; assumption.
apply Hmon; split;[apply measure_bounded| apply Aop.(le_refl)].
Qed.


   Lemma measure_strictly_monotonic :
    forall l r, (EQT.one_step rules r l) -> well_formed l -> measure r < measure l.
   Proof.
   Proof.
   intro l; pattern l; apply term_rec3; clear l.
   (* 1/2 variable case *)
   intros v r H; inversion H as [t1 t2 H1 | ]; clear H; subst.
   apply rules_strictly_monotonic; assumption.
   (* 1/2 compound term case *)
   intros f l IHl r H W.
   inversion H as [t1 t2 H1 | g k1 k2 H1 H2 H3];
   clear H; subst.
   apply rules_strictly_monotonic; assumption.
   assert (L : length l = get_arity f).
   unfold well_formed in W; simpl in W; rewrite Bool.andb_true_iff in W; destruct W as [_ W].
   apply Nat.eqb_eq; unfold get_arity; destruct (arity f) as [ | | n]; assumption.
   apply measure_strictly_monotonic_aux; trivial.
   apply (well_formed_unfold W).
   generalize (All_strictly_monotonic f); 
   set (f_pol:=Pols f).
   clearbody f_pol.
   revert f_pol.
   rewrite <- L.
   revert H1; case l; [intro H1; inversion H1 | intros a1 l1  _; intros; assumption].
   Qed.

   Lemma measure_list_strictly_monotonic :
     forall l1 l2 (H : one_step_list (one_step rules) l1 l2),
       (forall t, In t l2 -> well_formed t) -> 
       forall n (P1 P2:Pol_type n), length l2 =  n -> monotonic_strict_aux false n P1 P2 -> 
         measure_list l1 n P1 < measure_list l2 n P2.
   Proof.
     intros l1 l2 H Wl2.
     apply measure_strictly_monotonic_aux; [idtac | assumption | assumption].
     intros; apply measure_strictly_monotonic; assumption.
   Qed.

 End S.

End Interp.
