From Stdlib Require Import Relations List Setoid.
From Stdlib Require Inclusion.
From CoLoR Require Import weaved_relation closure equational_theory_spec dp modular_dp terminaison.



Module Make(E:EqTh) .

Module Import MDP := modular_dp.MakeModDP(E).
Import E.
Import T.
Import Dp.

Lemma Empty_R_neutral_union_r : forall R x y, 
  union _ Empty_R R x y <-> R x y.
Proof.
  intros R x y.
  split;[idtac|intro H;right;assumption].
  inversion_clear 1;trivial.
  case H0.
Qed.

Lemma Empty_R_neutral_union_l : forall R x y, 
  union _ R Empty_R  x y <-> R x y.
Proof.
  intros R x y.
  rewrite union_sym.
  apply Empty_R_neutral_union_r.
Qed.

Section S. 

Variable R1 R2 R3 R4: relation term.
Hypothesis R1_equiv_R2 : forall l r, R1 r l <-> R2 r l.
Hypothesis R3_equiv_R4 : forall l r, R3 r l <-> R4 r l.

Lemma defined_equiv : forall f , defined R1 f <-> defined R2 f.
Proof.
split.
inversion 1;subst.
rewrite R1_equiv_R2 in H0.
econstructor; eassumption.
inversion 1;subst.
rewrite <- R1_equiv_R2 in H0.
econstructor; eassumption.
Qed.

Lemma dp_equiv : forall l r, dp R1 r l <-> dp R2 r l.
Proof.
split.
inversion 1.
rewrite R1_equiv_R2 in H0.
econstructor; try eassumption. 
rewrite defined_equiv in H2;exact H2.
inversion 1.
rewrite <- R1_equiv_R2 in H0.
econstructor; try eassumption. 
rewrite <- defined_equiv in H2;exact H2.
Qed.

Lemma axiom_ddp_equiv : forall l r, axiom (ddp R1) r l <-> axiom (ddp R2) r l.
Proof.
split.
inversion 1.
destruct H0 as [H0 Sub].
rewrite dp_equiv in H0.
constructor; split; assumption.
inversion 1.
destruct H0 as [H0 Sub].
rewrite <- dp_equiv in H0.
constructor; split; assumption.
Qed.

Lemma one_step_equiv : forall r l, one_step R3 r l <-> one_step R4 r l.
Proof.
  intros r l.
  split; apply one_step_incl.
  intros; rewrite <- R3_equiv_R4; assumption.
  intros; rewrite R3_equiv_R4; assumption.
Qed.

Lemma one_step_list_equiv : forall r l, one_step_list (one_step R3) r l <-> one_step_list (one_step R4) r l.
Proof.
  intros r l.
  split; apply one_step_list_incl.
  intros; rewrite <- one_step_equiv; assumption.
  intros; rewrite one_step_equiv; assumption.
Qed.

Lemma rwr_equiv : forall r l, rwr R3 r l <-> rwr R4 r l.
Proof.
  intros r l.
  split; apply trans_incl.
  intros t1 t2 H; rewrite <- one_step_equiv; assumption.
  intros t1 t2 H; rewrite one_step_equiv; assumption.
Qed.

Lemma rwr_list_equiv : forall l1 l2, 
  refl_trans_clos (one_step_list  (one_step R3)) l1 l2 <-> refl_trans_clos (one_step_list (one_step R4)) l1 l2.
Proof.
  intros l1 l2; split; apply refl_trans_incl.
  intros k1 k2 H; rewrite <- one_step_list_equiv; assumption.
  intros k1 k2 H; rewrite one_step_list_equiv; assumption.
Qed.

Lemma dp_step_equiv_aux_1 : forall r l , 
  rdp_step (axiom (ddp R1)) R3 r l <->   rdp_step (axiom (ddp R2)) R3 r l.
Proof.
  intros r l.
  split.
  inversion 1;subst.
  rewrite axiom_ddp_equiv in H1.
  constructor 1 with l2; assumption.
  inversion 1;subst.
  rewrite <- axiom_ddp_equiv in H1.
  constructor 1 with l2; assumption.
Qed.

Lemma dp_step_equiv_aux_2 : forall  r l, 
  rdp_step (axiom (ddp R2)) R3 r l <->   rdp_step (axiom (ddp R2)) R4 r l.
Proof.
  intros r l.
  split.

  inversion 1;subst.
  rewrite rwr_list_equiv in H0.
  constructor 1 with l2; assumption.

  inversion 1;subst.
  rewrite <- rwr_list_equiv in H0.
  constructor 1 with l2; assumption.
Qed.

Lemma rdp_step_equiv : forall r l, rdp_step (axiom (ddp R1)) R3 r l <->  rdp_step (axiom (ddp R2)) R4 r l.
Proof.
  intros r l.
  transitivity  (rdp_step (axiom (ddp R2)) R3 r l).
  apply dp_step_equiv_aux_1.
  apply dp_step_equiv_aux_2.
Qed.

Lemma Empty_R_equiv_list : forall l r : term, Empty_R r l <-> In (l,r) nil.
Proof.
  split.
  inversion 1.
  inversion 1.
Qed.

End S.

Section S'.

Variable R1 R2 R3 : relation term.

Lemma rdp_step_equiv_strong : 
  forall R1 R2 R3 R4 
    (R1_dp_equiv_R2: forall l r, dp R1 r l <-> dp R2 r l)
    (R3_equiv_R4 : forall l r, R3 r l <-> R4 r l)
    r l,
    
    rdp_step (axiom (ddp R1)) R3 r l <->   rdp_step (axiom (ddp R2)) R4 r l.
Proof.
  intros R0 R4 R5 R6 R1_dp_equiv_R2 R3_equiv_R4 r l.
  split;intros H;case H;clear H;  clear l r.
  intros f l1 l2 v H1 H2.
  inversion H2 as [t1 t2 sigma H2']; inversion H2' as [H2'' Sub].
  constructor 1 with l2.
  rewrite <- (@rwr_list_equiv _ _ R3_equiv_R4); assumption.
  rewrite <- H0; constructor 1; split.
  rewrite <- R1_dp_equiv_R2; assumption.
  assumption.

  intros f l1 l2 v H1 H2.
  inversion H2 as [t1 t2 sigma H2']; inversion H2' as [H2'' Sub].
  constructor 1 with l2.
  rewrite (@rwr_list_equiv _ _ R3_equiv_R4); assumption.
  rewrite <- H0; constructor 1; split.
  rewrite R1_dp_equiv_R2; assumption.
  assumption.
Qed.

Lemma module_Empty_R : module R1 Empty_R.
Proof.
constructor.
intros f2 s t def_f2 s_t. 
inversion def_f2;subst.
inversion H.
Qed.
  
Lemma one_step_union_sym : 
  forall l r, one_step  (union _ R1 R2) r l <-> 
    one_step (union _  R2 R1) r l.
Proof.
  intros l r.
  apply one_step_equiv.
  intros.
  apply (union_sym R1 R2).
Qed.

Lemma one_step_list_union_sym : 
  forall l1 l2, one_step_list  (one_step (union _ R1 R2)) l1 l2 <-> 
    one_step_list (one_step (union _  R2 R1)) l1 l2.
Proof.
  intros l1 l2.
  apply one_step_list_equiv.
  intros.
  apply (union_sym R1 R2).
Qed.
  
Lemma one_step_union_rotate : 
  forall l r, one_step (union _ (union _ R1 R2) R3) r l <-> 
    one_step (union _ (union _ R3 R1) R2) r l.
Proof.
  intros l r.
  apply one_step_equiv.
  clear.
  intros l r.
  rewrite union_sym.
  rewrite union_assoc.
  reflexivity.
Qed.

Lemma one_step_list_union_rotate : 
  forall l1 l2, one_step_list (one_step (union _ (union _ R1 R2) R3)) l1 l2 <-> 
    one_step_list (one_step (union _ (union _ R3 R1) R2)) l1 l2.
Proof.
  intros l r.
  apply one_step_list_equiv.
  clear.
  intros l r.
  rewrite union_sym.
  rewrite union_assoc.
  reflexivity.
Qed.

Lemma one_step_union_assoc : 
  forall l r, one_step (union _ (union _ R1 R2) R3) r l <-> one_step (union _  R1 (union _ R2 R3)) r l.
Proof.
  intros l r.
  apply one_step_equiv.
  clear.
  intros l r.
  rewrite union_assoc.
  reflexivity.
Qed.

End S'.

Lemma one_step_union_insert : 
  forall R1 R2 l r,
     (one_step (union _ R1 R2) r l <-> 
       one_step (union _ (union _ R1 Empty_R) R2) r l).
Proof.
  intros R1 R2 l r.
  apply one_step_equiv;clear;intros l r.
  rewrite (union_sym (union _ R1 Empty_R)).
  rewrite <- union_assoc.
  rewrite Empty_R_neutral_union_l.
  apply union_sym.
Qed.

Lemma one_step_list_union_insert : 
  forall R1 R2 l r,
     (one_step_list (one_step (union _ R1 R2)) r l <-> 
       one_step_list (one_step (union _ (union _ R1 Empty_R) R2)) r l).
Proof.
  intros R1 R2 l r.
  apply one_step_list_equiv;clear;intros l r.
  rewrite (union_sym (union _ R1 Empty_R)).
  rewrite <- union_assoc.
  rewrite Empty_R_neutral_union_l.
  apply union_sym.
Qed.

Lemma star_equiv : forall (A:Type) (R1 R2: A -> A -> Prop), (forall l r, R1 r l <-> R2 r l) -> 
  forall l r, star _ R1 r l <-> star _ R2 r l.
Proof.
  intros A R1 R2 H l r.
  split;induction 1;try constructor.
  constructor 2 with y;auto.
  rewrite H in H1;assumption.
  constructor 2 with y;auto.
  rewrite H;assumption.
Qed.

Lemma star_list_equiv_empty : forall R1 R2 l r, 
  star _ (one_step_list (one_step (union _ (union _ R1 Empty_R) R2))) r l <-> 
  star _ (one_step_list (one_step (union _ R1 R2))) r l.
Proof.
  intros R1 R2 l r.
  apply star_equiv.
  clear;intros l r.
  apply one_step_list_equiv;clear.
  intros l r.
  rewrite (union_sym (union _ R1 Empty_R)).
  rewrite <- union_assoc.
  rewrite Empty_R_neutral_union_l.
  apply union_sym.
Qed.

Lemma is_primary_pi_not_subrule:
  forall (R:relation term) pi (Hpi:is_primary_pi pi R) t1 t2 p l, 
  R t2 t1 -> subterm_at_pos t2 p = Some (Term pi l) -> False.
Proof.
  intros R pi Hpi t1 t2 p l H H0.
  unfold is_primary_pi in Hpi. 
  destruct (Hpi _ _ H pi) as [ F _].
  elim F;trivial.
  clear - H0.
  revert t2 H0.
  induction p.
  intros t2 H2.  simpl in H2.
  injection H2;clear H2;intros;subst t2. simpl.
  generalize (F.Symb.eq_bool_ok pi pi); case ( F.Symb.eq_bool pi pi);trivial.
  intro abs;elim abs;trivial.
  
  intros t2 H2;simpl in H2.
  destruct t2.
  discriminate H2.
  case_eq (nth_error l0 a);intros.
  rewrite H in H2.
  simpl.
   generalize (F.Symb.eq_bool_ok pi a0); case ( F.Symb.eq_bool pi a0);trivial.
  intros.
  revert a H.
  induction l0.
  intros a H;destruct a;  simpl in H; discriminate.
  intros a' H;destruct a'. simpl in *.
  injection H;intros;subst.
  rewrite IHp. trivial. assumption.

  simpl in *.
  rewrite (IHl0 a');trivial.
  auto with *.
  rewrite H in H2;discriminate.
Qed.


Lemma pi_no_dp : forall (R:relation term) pi v1 v2 (Hpi:is_primary_pi pi R) x y, 
  dp (union _ R (Pi pi v1 v2))  x y <-> dp R x y.
Proof.
  intros R pi v1 v2 Hpi x y.
  split.

  intros H.
  inversion H;clear H;subst.
  inversion H0;clear H0.
  constructor 1 with t2 p;auto.
  inversion H2; subst.
  inversion H0; clear H0.
  constructor 1 with l t; exact H3.

  inversion H3; subst f2; subst; clear H3.
  apply False_ind. eapply is_primary_pi_not_subrule; try eassumption.

  apply False_ind. eapply is_primary_pi_not_subrule; try eassumption.

  inversion H;clear H;subst.
  destruct p;simpl in H2;discriminate. 
  destruct p;simpl in H2;discriminate.

  intro H.
  inversion H;clear H;subst.
  constructor 1 with t2 p;trivial.
  left;exact H0.
  inversion H2; subst f2; subst.
  constructor 1 with l t.
  left; exact H.
Qed.

Lemma dp_equiv_empty_pi : forall (R:relation term) pi v1 v2 (Hpi:is_primary_pi pi R) x y, 
  dp (union _ (union _ R Empty_R) (Pi pi v1 v2))  x y <-> dp R x y.
Proof.
  intros R pi v1 v2 Hpi x y.
  rewrite pi_no_dp.
  apply dp_equiv; clear.
  intros l r.
  apply Empty_R_neutral_union_l.
  intros s t H f. 
  inversion_clear H.
  apply Hpi; exact H0.
  inversion H0.
Qed.


Lemma rdp_equiv_empty_l : forall (R R':relation term) x y, 
  rdp_step (axiom (ddp (union _ R Empty_R))) R' x y <-> rdp_step (axiom (ddp R)) R' x y.
Proof.
  intros R R' x y.
  apply rdp_step_equiv_strong.  
  clear;intros;apply dp_equiv.
  clear;  intros l r;apply Empty_R_neutral_union_l.
  reflexivity.
Qed.


Lemma rdp_equiv_empty_pi : forall (R R':relation term) pi v1 v2 (Hpi:is_primary_pi pi R) x y, 
  rdp_step  (axiom (ddp (union _ (union _ R Empty_R) (Pi pi v1 v2)))) R'  x y <-> rdp_step (axiom (ddp R)) R' x y.
Proof.
  intros R R' pi v1 v2 Hpi x y.
  apply rdp_step_equiv_strong.  
  intros;rewrite pi_no_dp. 
  apply dp_equiv.
  clear;  intros l r;apply Empty_R_neutral_union_l.
  intros s t H f. 
  inversion_clear H.
  apply Hpi;exact H0.
  inversion H0.
  reflexivity.
Qed.



Lemma Empty_R_no_dp : forall x y, dp Empty_R x y -> False.
Proof.
  intros. 
  inversion H.
  inversion H0.
Qed.

Lemma Empty_R_no_rdp_step : forall R x y, rdp_step (axiom (ddp Empty_R)) R x y -> False.
Proof.
  intros. 
  inversion H.
  inversion H1.
  destruct H6.
  apply Empty_R_no_dp with (1:=H6).
Qed.

Lemma well_founded_equiv : forall (A:Type) R R' (H:forall x y, R x y <-> R' x y),
  @well_founded A R <-> well_founded R'.
Proof.
  intros A R R' H.
  split;intro H';apply Inclusion.wf_incl with (2:=H').
  red;intros;rewrite H;auto.
  red;intros;rewrite <- H;auto.
Qed.
               
       
Ltac prove_equiv_union := 
  match goal with 
    | |- ?R  <-> ?R  => reflexivity
    | |- union _ Empty_R _ _ _ <-> _ => rewrite Empty_R_neutral_union_r;prove_equiv_union
    | |- _ <-> union _ Empty_R _ _ _ => rewrite Empty_R_neutral_union_r;prove_equiv_union
    | |- union _ _ Empty_R  _ _ <-> _ => rewrite Empty_R_neutral_union_l;prove_equiv_union
    | |- _ <-> union _ _ Empty_R  _ _  => rewrite Empty_R_neutral_union_l;prove_equiv_union
    | |- union _ ?R1 ?R2 _ _ <-> _ => 
      let tac b R Rs := 
        match R with 
          | context CR [union _ Empty_R ?R'] =>
           let H := fresh "H" in 
           let H' := fresh "H" in 
             let e := context CR [R'] in 
             (assert (H:forall x y, R x y <-> e x y);
               [intros;prove_equiv_union|
                 assert (H':forall x y, Rs x y <-> Rs x y) by reflexivity;
                   match b with 
                     | true => rewrite (union_equiv _ _ _ _ _ H H')
                     | false => rewrite (union_equiv _ _ _ _ _ H' H)
                   end
               ]
             )
          | context CR [union _ ?R' Empty_R] =>
           let H := fresh "H" in 
           let H' := fresh "H" in 
             let e := context CR [R'] in 
             (assert (H:forall x y, R x y <-> e x y);
               [intros;prove_equiv_union|
                 assert (H':forall x y, Rs x y <-> Rs x y) by reflexivity;
                   match b with 
                     | true => rewrite (union_equiv _ _ _ _ _ H H')
                     | false => rewrite (union_equiv _ _ _ _ _ H' H)
                   end
               ]
             )
        end
        in
        ((progress  (tac true R1 R2))||(tac false R2 R1));prove_equiv_union
    | |- union _ ?R1 ?R2 _ _ <-> _ => 
      match R2 with 
        context [R1] => rewrite union_idem_strong;[intros;auto with *|intros;try prove_equiv_union]
      end
    | |- union _ ?R1 _ <-> ?R2 => 
      match R2 with 
        context C [union _ R1 ?R2'] => 
        let e := context C[R2'] in 
        setoid_replace R2 with (union _ R1 e);[idtac|idtac]
        |context C [union _ ?R2' R1] => 
        let e := context C[R2'] in 
          setoid_replace R2 with (union _ R1 e);[idtac|idtac]
      end
  end.


Lemma union_equiv_list : forall R1 R1_list R2 R2_list (H1: forall l r, R1 r l <-> In (l,r) R1_list) (H2: forall l r, R2 r l <-> In (l,r) R2_list),
  forall l r,
   union term R1 R2 r l <->
   In (l, r) (R1_list ++ R2_list).
Proof.
  intros R1 R1_list R2 R2_list H1 H2 l r.

  split.
  intros [H|H];apply in_or_app;[rewrite <- H1|rewrite <- H2];auto with *.
  intros H;destruct  (@in_app_or _ _ _ _ H) as [H' | H']; [left;rewrite  H1|right;rewrite  H2];auto with *.

Qed.


Lemma pi_reg : forall pi v0 v1 s t (H : MDP.Pi pi v0 v1 s t) x,
  In x (E.T.var_list s) -> In x (E.T.var_list t).
Proof.
  intros pi v0 v1 s t H x H0.
  inversion H;subst;simpl in H0|-*.
  destruct H0;auto with *.
  destruct H0;auto with *.

Qed.

Definition Pi_as_list pi v1 v2 := 
  ((Term pi (Var v1 :: Var v2 :: nil)),Var v1)::
  ((Term pi (Var v1 :: Var v2 :: nil)),Var v2)::nil.
Lemma Pi_equiv_list : forall pi v1 v2 l r, MDP.Pi pi v1 v2 r l <-> In (l,r) (Pi_as_list pi v1 v2). 
Proof.
  intros pi v1 v2 l r.
  split. 
  inversion 1;subst;simpl;auto with *.
  inversion 1;subst. injection H0;intros;subst;constructor.
  inversion H0.
  injection H1;intros;subst;constructor.
  case H1.
Qed.
  

End Make.
