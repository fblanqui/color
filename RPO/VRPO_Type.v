(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Solange Coupet-Grimal and William Delobel, 2006-01-09

Axiomatic definition of RPO, and Hypotheses taken to prove
strict order, monotonicity, well-foundedness
*)

(* $Id: VRPO_Type.v,v 1.3 2007-02-07 12:44:06 blanqui Exp $ *)

Require Export Signature.

Module Type RPO_Axioms_Type.

  Parameter tau : Sig -> relation term -> relation terms.

  Axiom status_eq : forall f g, f =F= g -> tau f = tau g.

  Parameter lt : relation term.

  Axiom lt_roots : forall f g, g <F f -> 
    forall ss ts, (forall t, In t ts -> lt t (Fun f ss)) -> 
      lt (Fun g ts) (Fun f ss).
    
  Axiom lt_status : forall f g, f =F= g -> 
    forall ss ts, (forall t, In t ts -> lt t (Fun f ss)) ->       
      tau f lt ts ss -> lt (Fun g ts) (Fun f ss).

  Axiom lt_subterm : forall f ss t, 
    ex (fun s => In s ss /\ (s = t \/ lt t s)) -> lt t (Fun f ss).

  Axiom lt_decomp : forall s t, lt s t -> 
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

End RPO_Axioms_Type.

(***********************************************************************)

Module Type RPO_MSO_Type.

  Declare Module Base : RPO_Axioms_Type.
  Export Base.
  
  Axiom SPO_to_status_SPO : forall f (r : relation term) ss, 
    (forall s, In s ss -> (forall t u, r s t -> r t u -> r s u)
      /\ (r s s -> False)) ->
    (forall ts us, tau f r ss ts -> tau f r ts us -> tau f r ss us)
    /\ (tau f r ss ss -> False).

  Axiom mono_axiom : forall f (r : relation term), 
    forall ss ts, one_less r ss ts -> tau f r ss ts.

End RPO_MSO_Type.

(***********************************************************************)

Module Type RPO_Wf_Type.

  Declare Module Base : RPO_Axioms_Type.
  Export Base.

  Require Export AccUtil.
  Require Export ListUtil.

  Definition lifting R := forall l, accs lt l -> Restricted_acc (accs lt) R l.

  Axiom wf_ltF : well_founded ltF.
    
  Axiom status_lifting : forall f, lifting (tau f lt).

End RPO_Wf_Type.
