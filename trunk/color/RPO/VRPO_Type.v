(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Solange Coupet-Grimal and William Delobel, 2006-01-09

Axiomatic definition of RPO, and Hypotheses taken to prove
strict order, monotonicity, well-foundedness
*)

(* $Id: VRPO_Type.v,v 1.7 2007-06-01 19:32:08 koper Exp $ *)

Require Export VPrecedence.

Module Type RPO_Model.

  Declare Module P : VPrecedenceType.
  Export P.

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

  Require Export AccUtil.
  Require Export ListUtil.

  Definition lifting R := forall l, accs lt l -> Restricted_acc (accs lt) R l.

  Parameter leF_dec : rel_dec leF.

  Parameter wf_ltF : well_founded ltF.
    
  Parameter status_lifting : forall f, lifting (tau f lt).

  Ltac lt_inversion_cases H :=
    match type of H with
      | lt ?s ?t =>
        let Hr := (fresh "case_roots") in
          let Hs := (fresh "case_status") in
            let Ht := (fresh "case_subterm") in
              (elim (lt_decomp s t H);
                [intro Hdum; elim Hdum; clear Hdum;
                  [intro Hr | intro Hs] | intro Ht])
      | _ => fail "Hyp should be ~ lt s t"
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
      | _ => fail "Hyp should be ~ lt s t"
    end.

End RPO_Model.
