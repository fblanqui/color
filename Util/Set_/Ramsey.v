(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2014-12-11

* Infinite Ramsey theorem

After "On a Problem of Formal Logic", F. P. Ramsey, London
Math. Soc. s2-30(1):264-286, 1930, doi:10.1112/plms/s2-30.1.264. *)

Set Implicit Arguments.

From Stdlib Require Import Morphisms Basics Setoid.
From CoLoR Require Import ClassicUtil IotaUtil EpsilonUtil DepChoice
     LogicUtil SetUtil FinSet InfSet NatUtil.

Section S.

  Variables (A : Type) (W : set A).

(****************************************************************************)
(** Infinite pigeon-hole principle with two holes. *)

  Lemma IPHP_with_2_holes (P : Pinf W) (f : elts P -> bool) :
    exists b (Q : Pinf P), forall x (i : mem x Q), f (elt (Pinf_sub Q _ i)) = b.

  Proof.
    destruct P as [P [PW Pinf]]; simpl in *.
    (* We first prove that P is the union of f^-1(true) and f^-1(false). *)
    assert (e : P [=] union (fiber f true) (fiber f false)).
    intro x. repeat unfold mem, union, fiber. split.
    intro xP. case_eq (f (elt xP)); intro f_x.
    left. ex xP. hyp. right. ex xP. hyp.
    intros [[xP _]|[xP _]]; hyp.
    (* Then either f^-1(true) or f^-1(false) is infinite. *)
    rewrite e, infinite_union in Pinf.
    destruct Pinf as [f_true_inf|f_false_inf].
    (* Case f^-1(true) is infinite. *)
    assert (h : fiber f true [<=] P). fo. ex true (mk_Pinf h f_true_inf).
    intros x [xP hx]. rewrite (proof_irrelevance _ _ xP). hyp.
    (* Case f^-1(false) is infinite *)
    assert (h : fiber f false [<=] P). fo. ex false (mk_Pinf h f_false_inf).
    intros x [xP hx]. rewrite (proof_irrelevance _ _ xP). hyp.
  Qed.

(****************************************************************************)
(** Ramsey theorem with 2 colors only. *)

  (* Let [g] be the function that, given a function f from [Pcard P 1]
  to bool, maps every element of [P] to [f (singleton x)]. *)
  Definition g (P : Pinf W) (f : Pcard P 1 -> bool) : elts P -> bool.

  Proof.
    intros [x_val x]. apply f. ex (Pf_singleton x_val). split.
    intro y. simpl. unfold impl. fo. subst. hyp. apply card_singleton.
  Defined.

  (* Let [i] be the function which maps [X] in [Pcard V n] to [add a X]
  in [Pcard P (S n)] provided that [a] is in [P] but not in [V]. *)
  Definition i n P (Q : Pinf P) (U : Pinf Q) V (a : A)
    (aU : mem a U) (VU_a : V [<=] rem a U) : Pcard V n -> Pcard P (S n).

  Proof.
    intro X. ex (Pf_add a X). split.
    simpl. destruct X as [X [XV cXm]]; simpl. rewrite XV, VU_a, add_rem.
    destruct U as [U [UQ Uinf]]; simpl. destruct Q as [Q [QP Qinf]]; simpl.
    trans Q; hyp. apply eq_dec. hyp.
    rewrite card_add. destruct X as [X [XV cXm]]; simpl. rewrite cXm.
    destruct (dec (mem a X)). fo. lia.
  Defined.

  Arguments i [n P Q U V a] _ _ _.

  Lemma i_eq n P (Q : Pinf P) (U : Pinf Q) V (a : A)
        (VU_a : V [<=] rem a U) (aU : mem a U) (X : Pcard V n) :
    i aU VU_a X [=] add a X.

  Proof. refl. Qed.

  (* Let j be the function mapping every X in [Pcard T' n] to (add a X)
  in [Pcard P (S n)]. *) 
  Definition j n (P : Pinf W) a (T' : Pinf W) :
    mem a P -> ~mem a T' -> T' [<=] P -> Pcard T' n -> Pcard P (S n).

  Proof.
    intros aP naT TP [X [XT cXn]]. ex (Pf_add a X). split.
    simpl. intro x. unfold impl, mem, add. fo. subst. fo.
    rewrite card_add, cXn. destruct (dec (mem a X)). fo. lia.
  Defined.

  Arguments j n [P a T'] _ _ _ _.

  Lemma j_eq n (P : Pinf W) a (T' : Pinf W) (aP : mem a P) (naT : ~mem a T')
        (TP : T' [<=] P) X : j n aP naT TP X [=] add a X.

  Proof. destruct X as [X [XT cXn]]. refl. Qed.

  Theorem ramsey_with_2_colors : forall n (P : Pinf W)
    (f : Pcard P (S n) -> bool), Proper (Pcard_equiv ==> eq) f ->
    exists b (Q : Pinf P), forall X : Pcard Q (S n), f (Pcard_subset Q X) = b.

  Proof.
    (* We proceed by induction on [n]. *)
    induction n; intros P f f_eq.

    (* Case n=0. *)

    (* We apply the infinite pigeon hole principle. *) 
    destruct (IPHP_with_2_holes P (g P f)) as [b [Q h]].
    ex b Q. intros [X [XQ cX1]].
    destruct (card_S cX1) as [a [Y [XaY [naY cY0]]]].
    assert (aQ : mem a Q). apply XQ. change (mem a X); rewrite XaY. simpl. fo.
    rewrite <- (h _ aQ). unfold g; simpl. apply f_eq.
    unfold Pcard_equiv; simpl. rewrite Pf_singleton_eq, XaY, (card_0 cY0). refl.

    (* Case n>0. *)
    revert IHn P f f_eq. generalize (S n); clear n; intros n IH P f f_eq.

    (* Given Q in [Pinf P] and c, we consider the following relation
    on [Pinf Q]. *)
    set (R (Q : Pinf P) c := fun U V : Pinf Q =>
      exists a (aU : mem a U) (VU_a : V [<=] rem a U),
        forall X : Pcard V n, f (i aU VU_a X) = c).

    (* We prove the following key lemma L:
    if [R Q c] is total, then there is T infinite such that
    f is equal to c on [Pcard T (S n)]. *)
    assert (L : forall (Q : Pinf P) c, (forall U, exists V, R Q c U V) ->
      exists T : Pinf P, forall X : Pcard T (S n), f (Pcard_subset T X) = c).
    intros Q c RQc_total.

    (* We apply the axiom of dependent choice to get an infinite
    [R Q c]-sequence V. *)
    destruct (@dep_choice _ (Pinf_self Q) (R Q c) RQc_total) as [V [hV V0]].

    (* V_k is included in P. *)
    assert (VP : forall k, V k [<=] P). intro k. simpl. trans (Pinf_val Q).
    destruct (V k) as [Vk [VkQ Vkinf]]; hyp. destruct Q as [Q [QP Qinf]]; hyp.

    (* Let b_k be the sequence of elements of V_k such that
    V_{k+1} [<=] rem b_k V_k. *)
    assert (b_spec : forall k, exists b (bVk : mem b (V k))
      (VSkVk_b : V (S k) [<=] rem b (V k)),
      forall X : Pcard (V (S k)) n, f (i bVk VSkVk_b X) = c).
    intro k. destruct (hV k) as [b [bVk [VSkVk_b h]]]. ex b bVk VSkVk_b. hyp.
    set (b := fun k => proj1_sig (cid (b_spec k))).

    (* b_k is element of V_k. *)
    assert (bV : forall k, mem (b k) (V k)).
    intro k. unfold b. destruct (cid (b_spec k)) as [a [a1 [a2 a3]]]. hyp.

    (* V_{k+1} [<=] rem b_k V_k. *)
    assert (VSV_b : forall k, V (S k) [<=] rem (b k) (V k)).
    intro k. unfold b. destruct (cid (b_spec k)) as [a [a1 [a2 a3]]]. hyp.

    (* [f o i] is equal to c on Pcard (V (S k)) n. *)
    assert (Vf : forall k
      (X : Pcard (V (S k)) n), f (i (bV k) (VSV_b k) X) = c).
    intros k X. case_eq (cid (b_spec k)); intros a [a1 [a2 a3]] e.
    rewrite <- (a3 X). apply f_eq. unfold Pcard_equiv, Pf_equiv.
    rewrite !i_eq. unfold b. rewrite e; simpl. refl.

    (* b_k is not element of V_{k+1}. *)
    assert (nbVS : forall k, ~mem (b k) (V (S k))).
    intros k h. rewrite VSV_b in h. revert h. apply notin_rem.

    (* V is anti-monotone: the sets V_k are decreasing. *)
    assert (Vle : Proper (le --> subset) V).
    intros l k. unfold flip. revert k l. intro k. induction l; intro hl.
    assert (k=0). lia. subst. refl.
    destruct (le_dec k l) as [kl|nkl]. trans (Pinf_val (V l)).
    2: apply IHl; hyp. rewrite VSV_b. apply subset_rem.
    assert (k=S l). lia. subst. refl.

    (* V_{k+1} is strictly included in V_k. *)
    assert (VSlt : forall k, V (S k) [<] V k).
    intro k. rewrite VSV_b. apply strict_subset_rem. apply bV.
 
    (* If k < l, then b_l is not element of V_k. *)
    assert (lt_nbV : forall k l, k < l -> ~mem (b k) (V l)).
    intros k l kl h. apply Vle in kl. apply kl in h. revert h. apply nbVS.

    (* Let B be the set of all of the b_k's. *)
    set (B := fun x => exists k, x = b k).

    (* b_k is element of B. *)
    assert (bB : forall k, mem (b k) B). intro k. ex k. refl.

    (* B is included in P. *)
    assert (BP : B [<=] P). intros x [k e]. subst. eapply VP. apply bV.

    (* B is infinite. *)
    assert (Binf : infinite B).
    apply infinite_inj. ex (fun k => elt (bB k)).
    intros k l e. apply sig_eq in e; simpl in e.
    destruct (lt_dec k l) as [kl|nkl].
    apply lt_nbV in kl. rewrite e in kl. gen (bV l). contr.
    destruct (lt_dec l k) as [lk|nlk].
    apply lt_nbV in lk. rewrite <- e in lk. gen (bV k). contr.
    lia.

    (* The solution is [B]. *)
    set (B' := mk_Pinf BP Binf). ex B'.

    (* We now prove that f equals c on [Pcard B' (S n)]. *)
    intro X'. case_eq X'; intros [X X_fin] [XB cXSn] Xeq; rewrite <- Xeq.

    (* Let k0 be the smallest k such that b_k belongs to X. *) 
    destruct (card_S cXSn) as [a [Y [XaY [naY cYn]]]].
    unfold Pf_equiv in XaY; simpl in XaY.
    assert (aX : mem a X). rewrite XaY. apply mem_add.
    gen aX; intro aX'. rewrite XB in aX'. destruct aX' as [kd abkd]. subst a.
    set (D := fun k => mem (b k) X). set (k0 := smallest (dec1 D) kd).
    gen (smallest_ok (dec1 D) aX). fold k0. intro bk0X. clear Y XaY naY cYn.

    (* Let Y be X - b_k0. *)
    set (Y := Pf_rem (b k0) X_fin).

    (* Y is included in V_{k0+1}. *)
    assert (YVSk0 : Y [<=] V (S k0)).
    intro x. unfold Y; simpl. unfold rem, mem. intros [nxbk0 xX].
    gen xX; intro xX'. apply XB in xX'. destruct xX' as [k xbk]. subst x.
    assert (k0k : k0 < k).
      assert (k0k' : k0 <= k). unfold k0. apply smallest_comp; hyp.
      destruct (eq_nat_dec k0 k). rewrite e in nxbk0. cong.
      lia.
    unfold lt in k0k. apply (Vle _ _ k0k). apply bV.

    (* card Y = n. *)
    assert (cYm : card Y = n).
    unfold Y. rewrite card_rem. unfold mk_Pf. rewrite cXSn. simpl.
    destruct (dec (mem (b k0) X)). lia. contr.

    set (Y' := mk_Pcard YVSk0 cYm).
    rewrite <- (Vf k0 Y'). apply f_eq. unfold Pcard_equiv, Pf_equiv.
    rewrite i_eq. apply Pcard_subset_equiv. rewrite Xeq.
    unfold Y', mk_Pcard; simpl. sym. apply add_rem. apply eq_dec. hyp.
    (* This ends the proof of lemma L. *)

    set (P' := Pinf_self P). 
    destruct (classic (forall U, exists V, R P' true U V))
      as [R_P_true_total|R_P_true_not_total].

    (* Case [R P true] is total. *)
    ex true. eapply L. apply R_P_true_total.

    (* Case [R P true] is not total. *)
    rewrite not_forall_eq in R_P_true_not_total.
    destruct R_P_true_not_total as [E' hE].
    revert hE. rewrite not_exists_eq.
    case_eq E'; intros E [EP Einf] Eeq; rewrite <- Eeq. intro hE.

    (* We now prove that [R E false] is total. *)
    assert (R_E_false_total : forall U, exists V, R E' false U V).
    intro U'. case_eq U'; intros U [UE' Uinf] Ueq; rewrite <- Ueq.
    gen UE'; intro UE. rewrite Eeq in UE. simpl in UE.

    (* Let a be any element of U and let T be U - a. *)
    destruct (infinite_not_empty Uinf) as [a aU]. set (T := rem a U).
    assert (TW : T [<=] W). unfold T. trans U. apply subset_rem.
    trans E; auto. trans (Pinf_val P'); auto. unfold P'; simpl.
    destruct P as [P [PW Pinf]]; hyp.
    assert (Tinf : infinite T). unfold T. rewrite infinite_rem. hyp.
    set (T' := mk_Pinf TW Tinf).

    (* Properties of a and T. *)
    assert (aP : mem a P). rewrite UE, EP in aU. hyp.
    assert (naT : ~mem a T'). simpl. unfold T. apply notin_rem.
    assert (TP : T' [<=] P). simpl. unfold T. rewrite subset_rem. trans E; hyp.

    (* Let g be the function [f o j]. *)
    set (g := fun X : Pcard T' n => f (j n aP naT TP X)).

    assert (g_equiv : Proper (Pcard_equiv ==> eq) g).
    intros X Y. unfold Pcard_equiv, Pf_equiv. intro XY. unfold g. apply f_eq.
    unfold Pcard_equiv, Pf_equiv. rewrite !j_eq. rewrite XY. refl.

    (* By the induction hypothesis on g, there are b and Q such that f
    equals b on [Pcard Q n]. *) 
    destruct (IH _ _ g_equiv) as [b [Q hQ]]. destruct b.

    (* Case b = true is absurd since [R P true] is not total. *)
    exfalso. set (Q' := Pinf_subset TP Q). eapply hE with (x := Q'). unfold R.

    assert (aE' : mem a E'). apply UE'. hyp.

    assert (QE'_a : Q' [<=] rem a E'). unfold Q', Pinf_subset.
    destruct Q as [Q [QT Qinf]]; simpl. trans (Pinf_val T'). hyp.
    simpl. unfold T. rewrite UE'. refl.

    ex a aE' QE'_a. intro X.

    assert (Q'Q : Q' [<=] Q). unfold Q', Pinf_subset.
    destruct Q as [Q [QT Qinf]]; simpl. refl.

    rewrite <- (hQ (Pcard_subset Q'Q X)). unfold g. apply f_eq.
    unfold Pcard_equiv, Pf_equiv. rewrite i_eq, j_eq. apply add_equiv.
    refl. unfold Pcard_subset. destruct X as [X [XQ' cXn]]; simpl. refl.

    (* Case b = false. *)
    assert (T'E' : T' [<=] E'). simpl. unfold T. rewrite subset_rem. hyp.
    set (Q' := Pinf_subset T'E' Q). ex Q'. unfold R.

    assert (aU' : mem a U'). rewrite Ueq. hyp.

    assert (Q'U'_a : Q' [<=] rem a U'). unfold Q', Pinf_subset.
    destruct Q as [Q [QT Qinf]]; simpl. trans (Pinf_val T'). hyp.
    simpl. unfold T. rewrite Ueq. refl.

    ex a aU' Q'U'_a. intro X.

    assert (Q'Q : Q' [<=] Q). unfold Q', Pinf_subset.
    destruct Q as [Q [QT Qinf]]; simpl. refl.

    rewrite <- (hQ (Pcard_subset Q'Q X)). unfold g. apply f_eq.
    unfold Pcard_equiv, Pf_equiv. rewrite i_eq, j_eq. apply add_equiv.
    refl. unfold Pcard_subset. destruct X as [X [XQ' cXn]]; simpl. refl.

    (* Conclusion. *)
    ex false. eapply L. apply R_E_false_total.
  Qed.

End S.

Arguments ramsey_with_2_colors [A W n P f] _.

(****************************************************************************)
(** Ramsey theorem with a finite set of colors. *)

Theorem ramsey A (W : set A) n (P : Pinf W) B : forall (C : Pf B)
  (f : Pcard P (S n) -> elts C), Proper (Pcard_equiv ==> elts_eq) f ->
  exists c (Q : Pinf P), forall X : Pcard Q (S n), f (Pcard_subset Q X) = c.

Proof.
  (* We proceed by induction on the cardinal of C (number of colors). *)
  intro C; pattern C; apply card_ind; clear C; induction n0 as [|k IH];
    intros C cardC f f_eq.
  (* card C = 0 *)
  exfalso. apply card_0 in cardC. destruct (f (Pcard_of_inf P n)) as [a aC].
  unfold Pf_equiv in cardC. simpl in cardC. rewrite cardC in aC. fo.
  (* card C = k+1 *)
  destruct (card_S cardC) as [c [D [CaD [naD cardD]]]].
  assert (cC : mem c C). rewrite CaD. apply mem_add. set (c' := elt cC).
  destruct k.
  (* Case k = 0: there is only one color. *)
  ex c'. set (Q := Pinf_self P). ex Q.
  intro X. destruct (f (Pcard_subset Q X)). apply sig_eq; simpl.
  apply card_0 in cardD. rewrite CaD, cardD in m. simpl in m. fo.
  (* Case k>0: there is more than one color. *)
  destruct (card_S cardD) as [d [E [DdE _]]].
  assert (dD : mem d D). rewrite DdE. apply mem_add. clear E DdE.
  (* Let g be function mapping every element X of [Pcard P (S n)] to D
  such that g(X)=f(X) if f(X) is in D, and g(X)=d otherwise. It
  identifies the colors c and d because, if f(X) is not in D, then
  f(X)=c since f(X) is in C and C is [add c D]. *)
  set (g := fun X : Pcard P (S n) =>
              match dec (Pf_val D (elt_val (f X))) with
                | left fXD => elt fXD
                | _ => elt dD
              end).
  assert (g_eq : Proper (Pcard_equiv ==> elts_eq) g).
  intros X Y XY. unfold g. apply f_eq in XY. rewrite XY.
  destruct (dec (Pf_val D (elt_val (f Y)))); refl.
  (* The induction hypothesis on g gives us a color e and a set Q. *)
  destruct (IH _ cardD _ g_eq) as [[e eD] [Q h1]]. destruct (dec (e=d)).
  (* Case e = d. *)
  subst e.
  (* Let j be the function mapping every X in [Pcard Q (S n)] to true
  if f(X)=c, and false otherwise. *)
  set (j := fun X : Pcard Q (S n) =>
    if eq_dec (elt_val (f (Pcard_subset Q X))) c then true else false).
  assert (j_eq : Proper (Pcard_equiv ==> eq) j).
  intros X Y XY. unfold j. case_eq (f (Pcard_subset Q X)); intros b bC fXb.
  apply sig_eq in fXb. rewrite (f_eq _ (Pcard_subset Q Y)) in fXb.
  apply sig_eq in fXb. rewrite fXb. refl. apply Pcard_subset_inj. hyp.
  (* With j, the Ramsey theorem with 2 colors gives us a color b and a set R. *)
  destruct (ramsey_with_2_colors j_eq) as [b [[R [RQ Rinf]] h2]]. simpl in h2.
  assert (RP : R [<=] P).
  trans (Pinf_val Q). hyp. destruct Q as [Q [QP Qinf]]; hyp.
  set (R' := mk_Pinf RP Rinf). destruct b.
  (* Case b = true. Then, f is equal to c on [Pcard R (S n)]. *)
  ex c' R'. intro X. gen (h2 X). unfold j.
  destruct (eq_dec (elt_val (f (Pcard_subset Q (Pcard_subset RQ X)))) c).
  2: discr. intros _. apply sig_eq. simpl. rewrite <- e. apply f_eq.
  unfold Pcard_equiv, Pf_equiv; simpl. apply Pcard_subset_inj.
  sym. apply Pcard_subset_equiv. refl.
  (* Case b = false. Then, f is equal to d on [Pcard R (S n)]. *)
  assert (dC : mem d C). rewrite CaD. simpl. unfold mem, add. auto.
  set (d' := elt dC). ex d' R'. intro X. 
  gen (h1 (Pcard_subset RQ X)). gen (h2 X). unfold g, j.
  set (X' := Pcard_subset Q (Pcard_subset RQ X)).
  destruct (eq_dec (elt_val (f X')) c). discr. intros _.
  destruct (dec (Pf_val D (elt_val (f X')))).
  intro e. apply sig_eq in e; simpl in e. apply sig_eq; simpl.
  rewrite <- e. apply f_eq. apply Pcard_subset_equiv. unfold X'.
  sym. do 2 apply Pcard_subset_equiv. refl.
  exfalso. apply n1. revert n0. case_eq (f X'); intros b bC _.
  gen bC; intro bC'. rewrite CaD in bC. simpl. clear -bC. simpl in bC. fo.
  (* Case e <> d. Then, f is equal to e on [Pcard Q (S n)]. *)
  assert (eC : mem e C). rewrite CaD. simpl. unfold mem, add. auto.
  set (e' := elt eC). ex e' Q. intro X. gen (h1 X). unfold g.
  set (X' := Pcard_subset Q X).
  destruct (dec (Pf_val D (elt_val (f X'))));
    intro a; apply sig_eq in a; simpl in a;
    apply sig_eq; simpl; rewrite <- a.
  apply f_eq. refl. firstorder auto with exfalso.
Qed.
