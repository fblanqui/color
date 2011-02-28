(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Cedric Auger, 2010-01-28
- Pierre-Yves Strub, 2009-04-09

Wrapper for Coq's FMaps definition + facts
*)

Set Implicit Arguments.

Require Import LogicUtil FMaps FMapAVL FMapFacts RelUtil.

Module Make (X : OrderedType).

  Module Export XMap := FMapAVL.Make X.
  Module Export XMapProps := Properties XMap.
  Module Export XMapFacts := Facts XMap.
  Module Export XMapOrdProps := OrdProperties XMap.

  Import X.

  Lemma t_morphism : forall A beq,
    equivalence A (rel beq) -> equivalence (XMap.t A) (Equivb beq).

  Proof. (* by Cedric Auger *)
  intros A beq [Refl Trans Sym]; split.
    intro m; split.
     now split; auto.
    intros k e e' H H'.
    generalize (XMap.find_1 H').
    rewrite (XMap.find_1 H).
    intro Heq; inversion_clear Heq.
    exact (Refl e').
   intros m1 m2 m3 [H12 K12] [H23 K23]; split; intro.
    generalize (H23 k); generalize (H12 k); clear.
    now intros [] []; split; auto.
   intros e e' H H'.
   destruct (proj1 (H12 k) (ex_intro (fun _ => _) e H)) as [e_ He_].
   generalize (Trans e e_ e').
   generalize (K23 _ _ _ He_ H').
   generalize (K12 _ _ _ H He_).
   clear; unfold Cmp, rel.
   now auto.
  intros m1 m2 [K H]; split.
   intro k; split; intro L.
    exact (proj2 (K k) L).
   exact (proj1 (K k) L).
  intros k e e' H1 H2.
  generalize (Sym e' e).
  generalize (H _ _ _ H2 H1).
  clear; unfold Cmp, rel.
  now auto.
  Qed.

  Instance add_m : forall A beq,
    Proper (XMap.E.eq ==> rel beq ==> XMap.Equiv (rel beq)
      ==> XMap.Equiv (rel beq)) (@XMap.add A).

  Proof. (* by Cedric Auger *)
  intros A beq k1 k2 Hk e1 e2 He m1 m2 Hm.
  split.
   intro k.
   generalize (proj1 Hm k); clear -Hm Hk.
   intros [Hm1 Hm2]; split; intros [a_ Ha_].
    destruct (XMap.E.eq_dec k2 k).
     split with e2.
     now apply XMap.add_1.
    destruct Hm1.
     split with a_.
     apply XMap.add_3 with k1 e1; auto.
     intro H; destruct n.
     now apply XMap.E.eq_trans with k1; auto.
    split with x.
    now apply XMap.add_2; auto.
   destruct (XMap.E.eq_dec k1 k).
    split with e1.
    now apply XMap.add_1.
   destruct Hm2.
    split with a_.
    apply XMap.add_3 with k2 e2; auto.
    intro H; destruct n.
    now apply XMap.E.eq_trans with k2; auto.
   split with x.
   now apply XMap.add_2; auto.
  intro k.
  destruct (XMap.E.eq_dec k2 k).
   intros e_ e_' H H'.
   revert He.
   generalize (XMap.find_1 H').
   rewrite (XMap.find_1 (XMap.add_1 _ _ e)).
   generalize (XMap.find_1 H).
   rewrite (XMap.find_1 (XMap.add_1 _ _ (XMap.E.eq_trans Hk e))).
   clear.
   intro H; inversion_clear H.
   intro H; inversion_clear H.
   now auto.
  intros e_ e_' H H'.
  generalize (XMap.add_3 n H').
  cut (not (XMap.E.eq k1 k)).
   intro n'; generalize (XMap.add_3 n' H).
   exact (proj2 Hm k e_ e_').
  clear -n Hk.
  intro H; destruct n.
  now apply XMap.E.eq_trans with k1; auto.
  Qed.


End Make.
