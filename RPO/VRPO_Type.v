(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Solange Coupet-Grimal and William Delobel, 2006-01-09

Axiomatic definition of RPO, and hypotheses taken to prove
strict order, monotonicity, well-foundedness
*)

From CoLoR Require Import VPrecedence ListUtil VTerm RelMidex LogicUtil AccUtil.
From Stdlib Require Import Relations Morphisms Basics.
From CoLoR Require AccUtil ListUtil MultisetListOrder ListLex.

Module Type RPO_Model.

  Declare Module Export P : VPrecedenceType.

  Parameter tau : Sig -> relation term -> relation terms.

  Parameter tau_dec : forall f R ts ss,
    (forall t s, In t ts -> In s ss -> {R t s} + {~R t s}) ->
    {tau f R ts ss} + {~tau f R ts ss}.

  Parameter status_eq : forall f g, f =F= g -> tau f = tau g.

  Parameter lt : relation term.

  Parameter lt_roots : forall f g, g <F f -> 
    forall ss ts, (forall t, In t ts -> lt t (Fun f ss)) -> 
      lt (Fun g ts) (Fun f ss).
    
  Parameter lt_status : forall f g, f =F= g -> 
    forall ss ts, (forall t, In t ts -> lt t (Fun f ss)) ->       
      tau f lt ts ss -> lt (Fun g ts) (Fun f ss).

  Parameter lt_subterm : forall f ss t, 
    ex (fun s => In s ss /\ (s = t \/ lt t s)) -> lt t (Fun f ss).

  Parameter lt_decomp : forall s t, lt s t -> 
    ((ex (fun f => ex (fun g => ex (fun ss => ex (fun ts =>
      ltF f g /\
      (forall s, In s ss -> lt s (Fun g ts)) /\
      s = Fun f ss /\
      t = Fun g ts
    )))))
    \/
    ex (fun f => ex (fun g => ex (fun ss => ex (fun ts => 
      f =F= g /\
      (forall s, In s ss -> lt s (Fun g ts)) /\
      tau f lt ss ts /\
      s = Fun f ss /\ 
      t = Fun g ts)))))
    \/
    ex (fun f => ex (fun ts => ex (fun t' =>
      In t' ts /\ (s = t' \/ lt s t')) /\ t = Fun f ts)).

  Parameter SPO_to_status_SPO : forall f (r : relation term) ss, 
    (forall s, In s ss -> (forall t u, r s t -> r t u -> r s u)
      /\ (r s s -> False)) ->
    (forall ts us, tau f r ss ts -> tau f r ts us -> tau f r ss us)
    /\ (tau f r ss ss -> False).

  Parameter mono_axiom : forall f (r : relation term), 
    forall ss ts, one_less r ss ts -> tau f r ss ts.

  Import AccUtil ListUtil.

  Definition lifting R := forall l, Accs lt l -> Restricted_acc (Accs lt) R l.

  Parameter leF_dec : rel_dec leF.

  Parameter wf_ltF : well_founded ltF.
    
  Parameter status_lifting : forall f, lifting (tau f lt).

(*
  Parameter status_homomorphic : forall F ss ts f,
    (forall s t, In s ss -> In t ts -> lt s t -> lt (F s) (F t)) ->
    tau f lt ss ts -> tau f lt (map F ss) (map F ts).
*)
    
  Ltac lt_inversion_cases H :=
    match type of H with
      | lt ?s ?t =>
        let Hr := (fresh "case_roots") in
          let Hs := (fresh "case_status") in
            let Ht := (fresh "case_subterm") in
              let Hdum := (fresh "case_hdum") in
              (elim (lt_decomp s t H);
                [intro Hdum; elim Hdum; clear Hdum;
                  [intro Hr | intro Hs] | intro Ht])
      | _ => fail 10 "Hyp should be ~ lt s t"
    end.
 
  Ltac inversion_case_root H :=
    let f := fresh "f" in let g := fresh "g" in
      let ss := fresh "ss" in let ts := fresh "ts" in
        let ltFfg := fresh "ltFfg" in let Hsub := fresh "Hsub" in
          let s_is := fresh "s_is" in let t_is := fresh "t_is" in
            (elim H; clear H; intros f H;
              elim H; clear H; intros g H;
                elim H; clear H; intros ss H;
                  elim H; clear H; intros ts H;
                    elim H; clear H; intros ltFfg H;
                      elim H; clear H; intros Hsub H;
                        elim H; clear H; intros s_is t_is).

  Ltac inversion_case_status H :=
    let f := fresh "f" in let g := fresh "g" in
      let ss := fresh "ss" in let ts := fresh "ts" in
        let eqFfg := fresh "eqFfg" in let Hsub := fresh "Hsub" in
          let Hstat := fresh "Hstat" in let s_is := fresh "s_is" in
            let t_is := fresh "t_is" in
              (elim H; clear H; intros f H;
                elim H; clear H; intros g H;
                  elim H; clear H; intros ss H;
                    elim H; clear H; intros ts H;
                      elim H; clear H; intros eqFfg H;
                        elim H; clear H; intros Hsub H;
                          elim H; clear H; intros Hstat H;
                            elim H; clear H; intros s_is t_is).
 
  Ltac inversion_case_subterm H :=
    let f := fresh "f" in let ts := fresh "ts" in
      let Hex := fresh "Hex" in let t' := fresh "t'" in
        let Ht' := fresh "Ht'" in let t'_in_ts := fresh "t'_in_ts" in
          let t_is := fresh "t_is" in
            (elim H; clear H; intros f H;
              elim H; clear H; intros ts H;
                elim H; clear H; intros Hex t_is;
                  elim Hex; clear Hex; intros t' Ht';
                    elim Ht'; clear Ht'; intros t'_in_ts Ht').

  Ltac lt_inversion H :=
    match type of H with
      | lt ?s ?t =>
        let Hr := (fresh "case_roots") in
          let Hs := (fresh "case_status") in
            let Ht := (fresh "case_subterm") in
              let Hdum := (fresh "case_hdum") in
              (elim (lt_decomp s t H);
                [intro Hdum; elim Hdum; clear Hdum;
                  [intro Hr | intro Hs] | intro Ht];
                [(* Hr : *)
                  inversion_case_root Hr
                  | (* Hs : *)
                    inversion_case_status Hs
                  | (* Ht : *)
                    inversion_case_subterm Ht
                ])
      | _ => fail 10 "Hyp should be ~ lt s t"
    end.

End RPO_Model.

Module Status (PT : VPrecedenceType).

  Module Export P := VPrecedence PT.

  Import MultisetListOrder.
  Module Export LMO := MultisetListOrder Term_dec.

  Import ListLex.
  Module Export LO := LexOrder Term.

  Section Decidability.

    Variable R : relation Term.A.
    Variables ts ss : terms.

    Lemma lex_status_dec : 
      (forall t s, In t ts -> In s ss -> {R t s} + {~R t s}) ->
      {lex R ts ss} + {~lex R ts ss}.
      
    Proof.
      intros. apply lex_dec.
      intros. destruct (term_eq_dec a b); intuition.
      hyp.
    Defined.

    Lemma mul_status_dec : 
      (forall t s, In t ts -> In s ss -> {R t s} + {~R t s}) ->
      {mult (transp R) ts ss} + {~mult (transp R) ts ss}.

    Proof.    
      intros.
      assert (eq_comp : Proper (eq ==> eq ==> impl) (transp R)).
      intros a b ab c d cd. subst. fo.
      destruct (@mOrd_dec_aux
        (transp R) eq_comp (list2multiset ss) (list2multiset ts)).
      assert (R_transp_dec : forall t s, In t ts -> In s ss ->
        {(transp R) s t} + {~(transp R) s t}).
      intros. destruct (X t s); intuition.
      intros. apply R_transp_dec. 
      destruct (member_multiset_list ts H0). compute in H2. rewrite H2. hyp.
      destruct (member_multiset_list ss H). compute in H2. rewrite H2. hyp.
      intuition. intuition.
    Defined.

  End Decidability.

(*FIXME: unfinished proof

  Section Homomorphism.

    Variable R : relation Term.A.
    Variable F : Term.A -> Term.A.
    Variables ts ss : terms.

    Lemma mul_status_homomorphic : 
      (forall s t, In s ss -> In t ts -> R s t -> R (F s) (F t)) ->
      mult (transp R) ss ts -> mult (transp R) (map F ss) (map F ts).

    Proof.
      intros. unfold mult, MultisetLT, transp. 
      apply mord_list_sim with R ts ss; unfold eqA, Term.eqA; trivial.
      congruence. 
      unfold order_compatible. intros. split.
      destruct (proj1 (in_map_iff F ts x') H2) as [x'' [x''x' x''ts]].
      destruct (proj1 (in_map_iff F ss y') H5) as [y'' [y''y' y''ss]].
      subst x'. subst y'. intro. apply H; try hyp. 
    Abort.

  End Homomorphism.*)

End Status.
