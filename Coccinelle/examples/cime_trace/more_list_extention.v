From CoLoR Require Import more_list decidable_set list_set.
From Stdlib Require Import List Lia FunInd.
From Stdlib Require Recdef.

Module Type S.
  Parameter A : Type.
End S.

Module Make(AX:S)(X:decidable_set.ES with Definition A:=AX.A with Definition eq_A:=@eq AX.A).

  Module XSet :=  list_set.Make(X).

  Import XSet.
  Import X.
  Import AX.

  Lemma mem_bool_app : 
    forall x l1 l2, 
       (mem_bool eq_bool x (l1++l2)) = orb (mem_bool eq_bool x l1) (mem_bool eq_bool x l2).
  Proof.
    intros x l1.
    functional induction (mem_bool eq_bool x l1).
    
    simpl;reflexivity.
    simpl.
    intros l2;rewrite IHb0. auto with bool. 
  Qed.

  Section S.
    Hypothesis order : A -> A -> bool.

    Function split (l : list A) (x: A) {struct l} : list A * list A   := 
      match l with 
        | nil => (nil,nil)
        | y::l' => 
          let (l1,l2) := split l' x in 
            if order y x 
              then (y::l1,l2)
              else (l1,y::l2)
      end.

    Lemma split_length : 
      forall x l, 
        let (l1,l2) := split l x in 
          List.length l1 + List.length l2 = List.length l.
    Proof.
      clear.
      intros x l.
      functional induction (split l x).
      reflexivity.
      simpl.
      rewrite e0 in IHp. lia.
      simpl;rewrite e0 in IHp. lia.
    Qed.
    Import Recdef.
    Function qs (l:list A) {measure length } : list A := 
      match l with 
        | nil => nil
        | x::l' => 
          let (l1,l2) := split l' x in 
            (qs l1)++x::(qs l2)
      end.
    Proof.
      abstract(intros;generalize (split_length x l');  
        rewrite teq0;  simpl;  intros; lia).
      abstract(intros;generalize (split_length x l');  
        rewrite teq0;  simpl;  intros; lia).
    Defined.

    Lemma split_mem_bool : 
      forall x y l l1 l2, split l x = (l1,l2) -> 
        mem_bool eq_bool y l = orb (mem_bool eq_bool y l1) (mem_bool eq_bool y l2).
    Proof.
      intros x y l;
        functional induction (split l x);
          intros l1' l2' H;injection H;clear H;intros h1 h2;subst;simpl.
      reflexivity.
      rewrite IHp with (1:=e0);auto with bool.
      rewrite IHp with (1:=e0);auto with bool.
      case (eq_bool y y0);case (mem_bool eq_bool y l1'); case (mem_bool eq_bool y l2);
        reflexivity.
    Qed.

    Lemma qs_valid : forall f l, 
      more_list.mem_bool eq_bool f l = more_list.mem_bool eq_bool f (qs l).
    Proof.
      intros f l.
      functional induction (qs l).
      reflexivity.
      simpl.
      rewrite mem_bool_app.
      simpl.
      rewrite <- IHl0.
      rewrite <- IHl1.
      rewrite split_mem_bool with (1:=e0).
      case (eq_bool f x);case (mem_bool eq_bool f l1); case (mem_bool eq_bool f l2);
        reflexivity.
    Qed.
  End S.

  Lemma change_in : 
    forall order f l, 
      In f l -> 
      more_list.mem_bool eq_bool f (qs order (remove_red l)) = true.
  Proof.
    intros order f l H.
    apply (more_list.in_impl_mem (@eq A) 
     (fun a => eq_refl a)) in H.
     apply XSet.remove_red_included in H.     
     generalize (more_list.mem_bool_ok _ _ eq_bool_ok f (remove_red l)).
     case_eq (more_list.mem_bool eq_bool f (remove_red l)).
     clear H;intros H _.
     2:clear -H;intros _ abs;contradiction.
     rewrite (qs_valid order) in H.
     exact H.
   Qed.
End Make.
