(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: Newman.v 9245 2006-10-17 12:53:34Z notin $ i*)
From CoLoR Require Import weaved_relation closure terminaison.
From Stdlib Require List.


Section Newman.

Variable A : Type. 
Variable R : A -> A -> Prop.

Definition coherence (x y:A) := 
  exists z, star _ R z x/\ star _ R z y.

Theorem coherence_intro :
  forall x y z:A, star _ R z x -> star _ R z y -> coherence x y.
Proof.
  intros x y z Hzx Hzy.
  exists z;auto. 
Qed.
  
(** A very simple case of coherence : *)

Lemma Rstar_coherence : 
  forall x y:A, star _ R x y -> 
    coherence x y.
Proof.
  intros x y H.  
  apply coherence_intro with x.
  refine (star_refl _ _ _ ).
  exact H.
Qed.  

(** coherence is symmetric *)
Lemma coherence_sym : 
  forall x y:A, 
    coherence x y -> 
    coherence y x.
Proof.
  intros x y H.
  destruct H as [z [H1 H2]].
  exists z;split;assumption.
Qed.

Definition confluence (x:A) :=
  forall y z:A, star _ R y x -> star _ R z x -> coherence y z.  
  
Definition local_confluence (x:A) :=
  forall y z:A, R y x -> R z x -> coherence y z.  
  
(* Definition noetherian := *)
(*   forall (x:A) (P:A -> Prop), *)
(*     (forall y:A, (forall z:A, R y z -> P z) -> P y) -> P x.   *)
  
Section Newman_section.

  (** The general hypotheses of the theorem *)

  Hypothesis Hyp1 : well_founded  R.
  Hypothesis Hyp2 : forall x:A, local_confluence x.  
  
  (** The induction hypothesis *)

  Section Induct.
    Variable x : A.
    Hypothesis hyp_ind : 
      forall u:A, 
        R u x -> 
        confluence u.  
  
    (** Confluence in [x] *)

    Variables y z : A.  
    Hypothesis h1 : star _ R y x.  
    Hypothesis h2 : star _ R z x.  
  
    (** particular case [x->u] and [u->*y]   *)
    Section Newman_.
      Variable u : A.  
      Hypothesis t1 : R u x.  
      Hypothesis t2 : star _ R y u.  
      
      (** In the usual diagram, we assume also [x->v] and [v->*z] *)
      
      Theorem Diagram : 
        forall (v:A) (u1:R v x) (u2:star _ R z v), 
          coherence y z.
      Proof.
        intros v u1 u2.
        assert (H:=Hyp2 x u v t1 u1).
        induction H as [w [s1 s2]].
        assert (H':=(hyp_ind u t1 y w t2 s1)).
        induction H' as  [a [v1 v2]].
        assert (H'':=(hyp_ind v u1 a z (star_trans _ _ a w v v2 s2) u2)).
        induction H'' as [b [w1 w2]].
        apply coherence_intro with b.
        apply star_trans with a;assumption.
        assumption.
      Qed.

      Theorem caseRxy : coherence y z.
      Proof.
        inversion h2.
        subst.
        exists y;split. apply star_refl.  assumption.

        subst. 
        apply Diagram with y0;assumption.
      Qed.
    End Newman_.

    Theorem Ind_proof : coherence y z.
    Proof.
      inversion h1.
      subst.
      apply coherence_sym;apply Rstar_coherence;assumption.
      subst.
      apply caseRxy with y0;auto.
    Qed.
  End Induct.

  Theorem Newman : forall x:A, confluence x.
  Proof.
    intro x;pattern x.
    apply well_founded_ind with (1:=Hyp1).
    clear x;intros x IHx.
    red.
    intros y z Hy Hz.
    eapply Ind_proof with (1:=IHx);assumption.
  Qed.

End Newman_section.


End Newman.
From CoLoR Require Import equational_theory_spec.

Module Confluence(Eqt:EqTh).
Import Eqt.
Import T.
Section Rew.
Variable R : term -> term -> Prop.
Variable wf_R : well_founded (Eqt.one_step R).
Variable no_need_of_instance : forall (t2 t1 : term),
       axiom R t1 t2 -> R t1 t2.
Variable R_non_var : 
  forall y v, ~ R y (Var v).

Variable head_down_confl : forall x y z, one_step R z x -> R y x -> 
   coherence term (one_step R) y z.

Lemma star_list : forall f l l', star _ (one_step_list (one_step R)) l' l -> 
  star _ (one_step R) (Term f l') (Term f l).
Proof.
  intros f l l' H.
  induction H.
  
  constructor.
  apply star_trans with (Term f y);auto.
  apply star_R. auto. constructor 2.  auto. 
Qed.

Import List.

Lemma star_cons : forall t l t' l', 
  star _ (one_step R) t' t -> star _ (one_step_list (one_step R)) l' l -> 
  star _ (one_step_list (one_step R)) (t'::l') (t::l).
Proof.
  intros t l t' l' H H0.

  apply star_trans with (t::l').
  clear H0;induction H.
  constructor.
  apply star_trans with (y::l').
  assumption.
  apply star_R;constructor;assumption.

  clear H;induction H0.
  constructor.
  apply star_trans with (t::y).
  assumption.
  apply star_R;constructor;assumption.
Qed.

Lemma confluence :
forall x, confluence _ (Eqt.one_step R) x.
Proof. 
apply Newman.
exact wf_R.

intros x.
induction x using term_rec4 
  with (Pl:=fun lx => local_confluence _ (one_step_list (one_step R)) lx).

(* Variable reduction *)
intros y z H H0.
inversion H; clear H;subst.
apply no_need_of_instance in H1.
elim (R_non_var _ _ H1).

(* Algebraic reduction *)
intros y z Hy Hz.
inversion Hy;subst.
apply no_need_of_instance in H. 
apply head_down_confl with (1:=Hz) (2:=H).

inversion Hz;clear Hz;subst.
apply no_need_of_instance in H.

apply coherence_sym.
apply head_down_confl with (1:=Hy) (2:=H).

destruct (IHx _ _ H1 H2) as [lz [Hlz1 Hlz2]].
exists (Term f lz);split.
apply star_list;assumption.
apply star_list;assumption.

(* list *)


revert H;induction l.

intros;red;intros;inversion H0.

intros;red;intros.
inversion H0;inversion H1;clear H0 H1;subst.

assert (coherence _ (one_step R) t0 t1).
apply H with a;simpl;auto.
destruct H0 as [t [h1 h2]].
exists (t::l);split;apply star_cons;
try constructor;auto.

exists (t1::l1);split;auto using star_cons;
apply star_R;constructor;auto.

exists (t1::l1);split;auto using star_cons;
apply star_R;constructor;auto.


assert (coherence _ (one_step_list (one_step R)) l1 l0).
apply IHl;simpl in H;auto.
destruct H0 as [lz [h1 h2]].
exists (a::lz);split;apply star_cons;auto;constructor.
Qed.



End Rew.
Import List.
Ltac reduce_term head_reduction t := 
  match t with 
    | ?Term ?f ?l => 
      let l':= reduce_list head_reduction l in 
        match l' with 
          | l => head_reduction t
          | _ => constr:(Term f l')
        end
    | _ => constr:(t)
  end
with reduce_list head_reduction l := 
  match l with 
    | nil => 
      constr:(l)
    | ?t::?l => 
      let t' := reduce_term head_reduction t in 
        match t' with 
          | t => 
            let l' := reduce_list head_reduction l in 
              constr:(t::l')
          | _ => constr:(t'::l)
        end
  end
.

Ltac prove_red_star head_reduction no_need_of_instance'  := 
  constructor || 
    match goal with 
      |- star _ _ _ ?t => 
        let t' := reduce_term head_reduction t in 
          transitivity t';
            [prove_red_star head_reduction no_need_of_instance'|
              repeat
                (solve [apply star_R;constructor 1;apply no_need_of_instance';constructor] (* head reduction *) || 
                  reflexivity ||
                    (apply star_list;repeat apply star_cons))
            ]
    end.

Ltac normalize_term head_reduction t := 
  let t' := reduce_term head_reduction t in 
    match t' with 
      | t => constr:(t)
      | _ => normalize_term head_reduction t'
    end.

Ltac prove_critical_pair head_reduction no_need_of_instance' := 
match goal with 
  | H: ?axiom _ _ _ |- _ => fail 1
  | H: _ = _ |- _ => fail 1
  | |- _ _ _ ?t _ => 
    let e := normalize_term head_reduction t in 
      exists e;split;prove_red_star head_reduction no_need_of_instance'
end.

End Confluence.
