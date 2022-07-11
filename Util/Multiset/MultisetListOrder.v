(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Solange Coupet-Grimal and William Delobel, 2005-09

This file provides an order on lists derived from the order on
multisets, along with some properties of this order.
*)

From Coq Require Import List Permutation Arith Morphisms Basics.
From CoLoR Require Import MultisetOrder RelExtras MultisetCore MultisetList
  MultisetTheory AccUtil RelUtil LogicUtil.
From CoLoR Require Import AccUtil ListUtil.

Module MultisetListOrder (ES : Eqset_dec).

(* Instantiation of MultiSets of elements of A as Lists of elements of A *)

  Module Export FMultisetList := MultisetList ES.

(* The basic relation on A needs not to be known at this point *)

  Module Export MOrder := MultisetOrder FMultisetList.
  Export MSet.

(* Order on lists of elements of A derived from multiset order *)

  Section MultisetListOrderFacts.

    Variable r : relation A.

    Variable r_eqA_compat :
      forall x x' y y', x =A=x' -> y=A=y' -> r x y -> r x' y'.

    Lemma r_eqA : Proper (eqA ==> eqA ==> impl) r.

    Proof.
      intros a b ab c d cd ac. eapply r_eqA_compat. apply ab. apply cd. hyp.
    Qed.

    Variable In_eqA_compat : forall ss x x',
      In x' ss -> x =A= x' -> In x ss.

    Definition mult ss ts :=
      MultisetLT r (list2multiset ss) (list2multiset ts). 
    
    Lemma mult2element : forall ss ts, mult ss ts -> 
      forall s, In s ss -> ex (fun t => In t ts /\ (t =A= s \/ r t s)).

    Proof.
      unfold mult; intros ss ts Hmult s s_in_ss; inversion Hmult.
      cut (s in (list2multiset ss)).
      intro s_in_mult_ss.
      cut (s in Z \/ s in Y).
      intro case_s; elim case_s; clear case_s; intro case_s. 
	(* case s in Z : *)
      exists s; split.
      elim (member_multiset_list ts) with s; trivial.
      apply In_eqA_compat.
      rewrite H0.
      apply member_member_union; hyp.
      left; auto with multisets.
      auto with sets.
        (* case s in Y : *)
      elim (H2 s case_s); intros t' t'_in_X Ht'.
      exists t'; split.
      elim (member_multiset_list ts) with t'; trivial.
      apply In_eqA_compat.
      rewrite H0, (union_comm Z X).
      apply member_member_union; hyp.
      right; hyp.
      apply member_union.
      rewrite <- H1; apply member_list_multiset; hyp.
      apply member_list_multiset; hyp.
    Qed.

    Lemma transp_trans_to_mult_trans : forall us, 
      (forall u, In u us -> forall t s,
        transp r u t -> transp r t s -> transp r u s) ->
      forall ts ss, mult us ts -> mult ts ss -> mult us ss.

    Proof.
      intros us Hsub ts ss; unfold mult, MultisetLT, transp; intros H1 H2.
      assert (Hsub' : forall p, p in (list2multiset us) ->
        forall x y, r x p -> r y x -> r y p).
      intros p p_in_us x y H H'.
      elim (member_multiset_list us p_in_us); intros p' p'_in_us p'eq.
      apply r_eqA_compat with y p'; auto with multisets.
      auto with sets. auto with sets.
      gen (Hsub p' p'_in_us x y); unfold transp; simpl; intro Hsub';
        apply Hsub'; trivial.
      apply r_eqA_compat with x p; auto with multisets.
      auto with sets.
      apply (sub_transp_trans_2_mOrd_trans Hsub') with (list2multiset ts);
        trivial.
    Qed.

    Lemma nonempty_mset_ind : forall (P : Multiset -> Prop), 
      (forall M N, P M -> M =mul= N -> P N)  -> 
      (forall a, P {{a}}) -> (forall a M, P M -> P (M+{{a}})) -> 
      forall M : Multiset, M <>mul empty -> P M.

    Proof.
      intros P P_morph Ha HMa M; induction M using mset_ind.
      intro H; elim H; auto with multisets.
      intros H; clear H.
      elim (empty_dec M); intro case_M.
        (* case M empty : *)
      apply (P_morph {{a}}).
      apply Ha.
      rewrite case_M; solve_meq.
        (* case M not empty : *)
      apply HMa; apply IHM; hyp.
    Qed.

    Lemma self_dom : transitive r -> forall X, X <>mul empty ->
      (forall x, x in X -> ex (fun x' => x' in X /\ r x' x)) -> 
      ex (fun x => x in X /\ r x x).

    Proof.
      intro Htrans.
      apply (nonempty_mset_ind (fun (X : Multiset) => 
        (forall (x : A), x in X -> ex (fun (x' : A) => x' in X /\ r x' x)) -> 
        ex (fun (x : A) => x in X /\ r x x))).
        (* Property is a morphism : *)
      intros M N HM Heq H1.
      assert (H : exists x : A, x in M /\ r x x).
      apply HM.
      intros x x_in_M; assert (H : x in N).
      rewrite <- Heq; auto with multisets.
      elim (H1 x H); intros x' Hx'; elim Hx'; clear Hx'; intros Hx'1 Hx'2;
	exists x'; split; trivial.  
      rewrite Heq; auto with multisets.
      elim H; clear H; intros x H; elim H; clear H; intros H H'; exists x;
        split; trivial.
      rewrite <- Heq; auto with multisets.
        (* Property true on singletons : *)
      intros a Ha; exists a; split; auto with multisets.
      elim (Ha a (singleton_member a)); intros x' Hx'; elim Hx'; clear Hx';
        intros Hx'1 Hx'2.
      apply (r_eqA_compat x' a a a).
      apply member_singleton. hyp. auto with sets. hyp.
        (* Property preserved by adding an element : *)
      intros a M HM H.
      assert (H' : a in (M + {{a}})); auto with multisets.
      elim (H a H'); intros x' Hx'; elim Hx'; clear Hx'; intros Hx'1 Hx'2.
      elim (member_union Hx'1); intro case_x'.
          (* case x in M : *)
      assert (H'' : exists x : A, x in M /\ r x x).
      apply HM.
      intros x x_in_M; assert (H'' : x in (M + {{a}})); auto with multisets.
      elim (H x H''); intros x0 Hx0; elim Hx0; clear Hx0; intros Hx01 Hx02.
      elim (member_union Hx01); intro case_x0.
      exists x0; split; trivial.
      exists x'; split; trivial.
      apply Htrans with a; trivial.
      apply (r_eqA_compat x0 a x x); auto with sets multisets.
      elim H''; intros x Hx; elim Hx; clear Hx; intros Hx1 Hx2.
      exists x; split; trivial.
      auto with multisets.
          (* case x = a : *)
      exists a; split; auto with multisets.
      apply (r_eqA_compat x' a a a); auto with sets multisets.
    Qed.

    Lemma self_dom2 : forall X,  X <>mul empty ->
      (forall x, x in X -> forall y z, r y x -> r z y -> r z x) ->
      (forall x, x in X -> ex (fun x' => x' in X /\ r x' x)) ->
      ex (fun x => x in X /\ r x x).

    Proof.
      apply (nonempty_mset_ind (fun X =>
	(forall x, x in X -> forall y z, r y x -> r z y -> r z x) ->
        (forall x, x in X -> ex (fun x' => x' in X /\ r x' x)) ->
        ex (fun x => x in X /\ r x x))).
        (* Property is a morphism : *)
      intros M N HM Heq Htrans H1.
      assert (H : exists x : A, x in M /\ r x x).
          (* Proof of H : *)
      apply HM.
      intros x x_in_M; assert (H : x in N).
      rewrite <- Heq; auto with multisets.
      apply Htrans; trivial.
      intros x x_in_M; assert (H : x in N).
      rewrite <- Heq; auto with multisets.
      elim (H1 x H); intros x' Hx'; elim Hx'; clear Hx'; intros Hx'1 Hx'2;
        exists x'; split; trivial.
      rewrite Heq; auto with multisets.
          (* H proved *)
      elim H; clear H; intros x H; elim H; clear H; intros H H'; exists x;
        split; trivial.
      rewrite <- Heq; auto with multisets.
        (* Property true on singletons : *)
      intros a H Ha; exists a; split; auto with multisets.
      elim (Ha a (singleton_member a)); intros x' Hx'; elim Hx'; clear Hx';
        intros Hx'1 Hx'2.
      apply (r_eqA_compat x' a a a); auto with sets multisets.
        (* Property preserved by adding an element : *)
      intros a M HM Htrans H.
      assert (H' : a in (M + {{a}})); auto with multisets.
      elim (H a H'); intros x' Hx'; elim Hx'; clear Hx'; intros Hx'1 Hx'2.
      elim (member_union Hx'1); intro case_x'.
          (* case x in M : *)
      assert (H'' : exists x : A, x in M /\ r x x).
      apply HM.
      intros x x_in_M; assert (H'' : x in (M + {{a}})); auto with multisets.
      apply Htrans; trivial.
      (* H' proved *)
      intros x x_in_M; assert (H'' : x in (M + {{a}})); auto with multisets.
      elim (H x H''); intros x0 Hx0; elim Hx0; clear Hx0; intros Hx01 Hx02.
      elim (member_union Hx01); intro case_x0.
      exists x0; split; trivial.
      exists x'; split; trivial.
      apply Htrans with a; trivial.
      apply (r_eqA_compat x0 a x x); auto with multisets.
      (* H'' proved *)
      elim H''; intros x Hx; elim Hx; clear Hx; intros Hx1 Hx2.
      exists x; split; trivial.
      auto with multisets.
          (* case x = a : *)
      exists a; split; auto with multisets.
      apply (r_eqA_compat x' a a a); auto with multisets.
    Qed.

    Lemma irrefl_to_MultisetGT_irrefl : transitive r -> forall M,
      (forall m, m in M -> r m m -> False) -> MultisetGT r M M -> False.

    Proof.
      intros Htrans M Hsub HM.
      inversion HM.
      assert (H' : X =mul= Y).
      apply meq_union_meq with Z.
      rewrite (union_comm X Z), (union_comm Y Z), <- H1, <- H0.
      auto with multisets.
      assert (H'' : forall (x : A), x in X ->
        ex (fun (x' : A) => x' in X /\ r x' x)).
      intros x x_in_X; assert (x_in_Y : x in Y). 
      rewrite <- H'; trivial.
      elim (H2 x x_in_Y); intros x' Hx'1 Hx'2.
      exists x'; split; trivial.
      elim (self_dom Htrans X H H''); intros x Hx.
      elim Hx; clear Hx; intros Hx1 Hx2.
      apply (Hsub x); trivial.
      rewrite H0, (union_comm Z X); auto with multisets.
    Qed.

    Lemma irrefl_to_mult_irrefl : transitive r -> 
      forall ss, (forall s, In s ss -> r s s -> False) -> mult ss ss -> False.

    Proof.
      unfold mult; intros Htrans ss Hsub H. 
      apply (irrefl_to_MultisetGT_irrefl Htrans (list2multiset ss)).
      intros m m_in_ss Hm; apply (Hsub m); trivial.
      elim (member_multiset_list ss m_in_ss).
      apply In_eqA_compat. 
      gen H; unfold MultisetLT; simpl; trivial.
    Qed.

    Lemma transp_SPO_to_mult_SPO : forall us,
      (forall u, In u us ->
        ((forall t s, transp r u t -> transp r t s -> transp r u s)
	  /\ (transp r u u -> False))) ->
	(forall ts ss, mult us ts -> mult ts ss -> mult us ss)
        /\ (mult us us -> False).

    Proof.
      intros us Hsub; unfold mult, MultisetLT, transp; split.
      (* Transitivity : *)
      intros ts ss.
      assert (Hsub' : forall p, p in (list2multiset us) ->
        forall x y, r x p -> r y x -> r y p).
      intros p p_in_us x y H H'.
      elim (member_multiset_list us p_in_us); intros p' p'_in_us p'eq.
      apply r_eqA_compat with y p'; auto with multisets.
      auto with sets. auto with sets.
      elim (Hsub p' p'_in_us); intros Hsub' Hsub''; gen (Hsub' x y);
        unfold transp; simpl; clear Hsub'; intro Hsub'; apply Hsub'; trivial.
      apply r_eqA_compat with x p; auto with multisets.
      auto with sets.
      (* Hsub' proved *)
      intros; apply (sub_transp_trans_2_mOrd_trans Hsub')
        with (list2multiset ts); trivial.
      (* Irreflexivity : *)
      intro HM; inversion HM.
      assert (H' : X =mul= Y).
      apply meq_union_meq with Z.
      rewrite (union_comm X Z), (union_comm Y Z), <- H1, <- H0.
      auto with multisets.
      (* H' proved *)
      assert (H'' : forall (x : A), x in X ->
        ex (fun (x' : A) => x' in X /\ r x' x)).
      intros x x_in_X; assert (x_in_Y : x in Y).
      rewrite <- H'; trivial.
      elim (H2 x x_in_Y); intros x' Hx'1 Hx'2.
      exists x'; split; trivial.
      (* H'' proved *)
      assert (Htrans : forall x, x in X ->
        forall y z, r y x -> r z y -> r z x).
      intros x x_in_X; assert (x_in_us : In x us).
      assert (x_in_usM : x in (list2multiset us)).
      rewrite H0, (union_comm Z X); apply member_member_union; trivial.
      elim (member_multiset_list us x_in_usM); intros; apply In_eqA_compat
        with x0; trivial.
      elim (Hsub x x_in_us); intros H3 H4; unfold transp in H3; simpl in H3;
        apply H3.
      (* Htrans proved *)
      elim (self_dom2 X H Htrans H''); intros x Hx.
      elim Hx; clear Hx; intros Hx1 Hx2.
      assert (x_in_us : In x us).
      assert (x_in_usM : x in (list2multiset us)).
      rewrite H0, (union_comm Z X); apply member_member_union; trivial.
      elim (member_multiset_list us x_in_usM); intros; apply In_eqA_compat
        with x0; trivial.
      elim (Hsub x x_in_us); intros H3 H4; unfold transp in H4; simpl in H4;
        apply H4; trivial.
    Qed.

    (* Equivalence between accessibility of lists and multisets *) 

    Lemma Acc_multiset_list : transitive r -> forall ss,
      Acc (MultisetLt r) (list2multiset ss) -> Acc mult ss.

    Proof.
      intros r_trans ss Hacc.
      unfold mult; apply (Acc_inverse_image (list A) Multiset
        (MultisetLT r) list2multiset ss).
      gen Hacc; apply Acc_eq_rel.
      unfold MultisetLt,MultisetLT,transp; simpl; intros a b;
        apply red_eq_direct; trivial.
      intros x y xy u v uv xu. eapply r_eqA_compat. apply xy. apply uv. hyp.
    Qed.

     Lemma Acc_list_multiset : transitive r -> forall ss, 
      Acc mult ss -> Acc (MultisetLt r) (list2multiset ss).

    Proof.
      intros r_trans ss Hacc.
      apply (Acc_iso (MultisetLt r) (list2multiset ss) 
        (fun (l : list A) (M : Multiset) => list2multiset l =mul= M) 
        (R := fun ss ts : list A =>
          MultisetLt r (list2multiset ss) (list2multiset ts))
        (x := ss)); trivial.
      (* proof of iso_comp : *)
      intros ts M N Hts HMN. 
      exists (multiset2list M).
      gen HMN; unfold MultisetLt,transp; simpl. 
      apply MultisetGt_morph.
      rewrite Hts; auto with multisets.
      rewrite (double_convertion M); auto with multisets.
      exact (double_convertion M).
      auto with multisets.
      (* *)
      gen Hacc; unfold mult; apply Acc_eq_rel; trivial.
      intros a b; elim (red_eq_direct r_trans r_eqA
        (list2multiset b) (list2multiset a));
        split; trivial.
    Qed.  

    (* Using the fundamental lemma on multiset order WF *)

    Lemma HAccTermsToTermlist : forall ss, 
      (forall s, In s ss -> Acc (transp r) s) -> Acc mult ss.

    Proof.
      intros ss Hsub; cut (Acc (MultisetLT r) (list2multiset ss)).
      unfold mult;
        apply (Acc_inverse_image (list A) Multiset (MultisetLT r)
          list2multiset ss).
      cut (Acc (MultisetLt r) (list2multiset ss)).
      apply Inclusion.Acc_incl; intros M N; unfold MultisetLT, MultisetLt, transp;
        simpl; apply direct_subset_red; trivial.
      apply r_eqA.
      apply mord_acc with (gtA := r) (M := list2multiset ss); trivial.
      apply r_eqA.
      intros x Hx; apply (Hsub x).
      elim (member_multiset_list ss Hx).
      apply In_eqA_compat. 
    Qed.

    Lemma HAccTermlistToTerms : transitive r -> forall ss : list A, 
      Acc mult ss -> (forall s, In s ss -> Acc (transp r) s).

    Proof.
      intros r_trans ss acc_ss.
      intros s s_in_ss; apply acc_mord 
        with (gtA := r) (M := list2multiset ss); try hyp.
      apply r_eqA. apply Acc_list_multiset; trivial.
      gen s_in_ss; apply member_list_multiset.
    Qed.

  End MultisetListOrderFacts.

  Import AccUtil ListUtil.

  Lemma mult_lifting : forall (r : relation A),
    (forall x x' y y', x =A= x' -> y =A= y' -> r x y -> r x' y') ->
    (forall l x x', In x' l -> x =A= x' -> In x l) ->
    forall l, Accs r l -> Restricted_acc (Accs r) (mult (transp r)) l.

  Proof.
    intros r C1 C2 l Accs_l.
    elim (Restricted_acc_eq_acc (Accs r) (mult (transp r)) l); intros H1 H2.
    apply H1; clear H1 H2.
    apply Inclusion.Acc_incl with (mult (transp r)).
    intros a b H; elim H; trivial.
    apply HAccTermsToTermlist; trivial.
    unfold transp; simpl; intros x x' y y' Hxy Hx'y'.
    apply (C1 y  y' x x'); trivial.
  Qed.

  Section Mult_and_one_less.

    Lemma mult_insert : forall r l l' h,
      mult (transp r) l l' -> mult (transp r) (h :: l) (h :: l').

    Proof.
      intros r l l' h Hm.
      unfold mult,MultisetLT, transp in *; simpl.
      inversion Hm.
      constructor 1 with (X := X) (Y := Y) (Z := insert h Z);
        auto with multisets.
      rewrite H0; try_solve_meq.
      rewrite H1; try_solve_meq.
    Qed.

    Lemma one_less2mult : forall r : relation A,
      (forall x x' y y', x =A=x' -> y=A=y' -> r x y -> r x' y') ->
      forall l l', one_less r l l' -> mult (transp r) l l'.

    Proof.
      intros r r_eqA_compat l l' H1; inversion H1; subst.
      generalize dependent l; induction p as [ | p]; intros l Hl H1.
      (* case p = 0 : *)
      destruct l as [|h l];inversion H1.
      subst; simpl; simpl in H1.
      unfold mult, MultisetLT, transp; simpl.
      constructor 1 with (X := {{a'}}) (Y :={{a}}) (Z := (list2multiset l));
        [auto with multisets|..].
      unfold insert; simpl.
      rewrite union_comm; auto with multisets.
      unfold insert; simpl.
      rewrite union_comm; auto with multisets.
      intros y Hy; assert (HY : y =A= a).
      apply (member_singleton Hy).
      exists a'; auto with multisets.
      apply r_eqA_compat with a a'; auto with sets multisets.
      (* case p > 0 : *)
      destruct l as [|h l]; inversion H1. (* case l = nil done *)
      subst; simpl.
      assert (Hml : mult (transp r) l (l [p := a'])).
      apply IHp; trivial.
      apply (@one_less_cons _ r l (l [p := a']) p a a'); trivial.
      apply mult_insert; trivial.
    Qed.

  End Mult_and_one_less.

End MultisetListOrder.

