From Stdlib Require Import List Bool.
From CoLoR Require Import TransClosure.
From CoLoR Require term terminaison.

Module Make(M:term_spec.Term).
  Import M.


Ltac find_replacement l := 
  match l with 
    | nil => constr:(@nil term) 
    | ?x::?l => 
      let l':=find_replacement l in 
        let e := 
          match goal with 
            | H: refl_trans_clos _ ?x' x |- _ => 
              constr:(x')
      | |- _ => constr:(x)
          end
          in
          constr:(e::l')
  end.


  Ltac is_closed_list is_closed l := 
    match l with 
      | nil => idtac
      | ?t::?l => 
        is_closed t;
        is_closed_list is_closed l 
    end
    .
  
  Ltac is_closed t := 
    match t with 
      | Term _ ?l => is_closed_list ltac:(is_closed l)
      | Var _ => idtac
      | _ => 
        (match goal with 
           | H:_ |- _ => 
             match t with 
               | H  => idtac
             end
         end)
    end 
    .

  Ltac star_refl' := 
    repeat (match goal with 
              | H:_ |- _ => clear H|| revert H
            end);intros;  
    match goal with 
      | |- refl_trans_clos _ ?t2 ?t1  => 
        (is_closed t1 ; econstructor 1) || (is_closed t2; econstructor 1)
    end.


  Definition eq_term_term_bool t1_t2 t1'_t2' : bool := 
    match t1_t2,t1'_t2' with 
      | (t1,t2),(t1',t2') => andb (M.eq_bool t1 t1') (M.eq_bool t2 t2')
    end.

  Lemma eq_term_term_bool_ok : forall t1_t2 t1'_t2', 
    if eq_term_term_bool t1_t2 t1'_t2' then t1_t2 = t1'_t2' else t1_t2 <> t1'_t2'.
  Proof.
    intros [t1 t2] [t1' t2'].
    simpl.
    generalize (M.eq_bool_ok t1 t1').
    case (eq_bool t1 t1').
    generalize (M.eq_bool_ok t2 t2').
    case (eq_bool t2 t2').
    intros;subst;reflexivity.
    intros t2_neq_t2' _ abs;elim t2_neq_t2';injection abs;intros;assumption.
    intros t1_neq_t1' abs;elim t1_neq_t1';injection abs;intros;assumption.
  Defined.



  Lemma term_eq_bool_equiv : 
    forall f g : M.term, f = g <-> M.eq_bool f g = true.
  Proof.
    intros f g.
    generalize (M.eq_bool_ok f g).
    case (eq_bool f g).
    tauto.
    intuition discriminate.
  Qed.



End Make.


Module IntVars.
Definition A := nat.
Fixpoint eq_bool (n1 n2:nat) : bool := 
  match n1,n2 with 
    | 0,0 => true 
    | S n1,S n2 => eq_bool n1 n2
    | _,_ => false
  end.

Lemma eq_bool_ok : forall n1 n2, if eq_bool n1 n2 then n1=n2 else n1<>n2.
Proof.
  induction n1 as [|n1];intros [|n2];simpl in *. 
  
  exact (eq_refl _).
  intro abs;discriminate abs. 
  intro abs;discriminate abs. 
  generalize (IHn1 n2).
  case (eq_bool n1 n2).
  intro Heq;f_equal;assumption.
  intros Hneq abs;elim Hneq;injection abs;intro H;exact H.
Defined.
End IntVars.
