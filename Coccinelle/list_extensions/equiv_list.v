(**************************************************************************)
(*           *                                                            *)
(*     _     *   The Coccinelle Library / Evelyne Contejean               *)
(*    <o>    *          CNRS-LRI-Universite Paris Sud                     *)
(*  -/@|@\-  *                   A3PAT Project                            *)
(*  -@ | @-  *                                                            *)
(*  -\@|@/-  *      This file is distributed under the terms of the       *)
(*    -v-    *      CeCILL-C licence                                      *)
(*           *                                                            *)
(**************************************************************************)

From Stdlib Require Import List Relations Setoid.

Lemma equiv_in_list :
  forall (A : Type) (R : relation A) s ll, (forall s t, In (s,t) ll -> R s t) ->
  In s (map (fun st => fst st) ll) ->
  exists t, exists ll1, exists ll2, R s t /\ ll = ll1 ++ (s,t) :: ll2.
Proof.
intros A R s ll E_ll s_in_ll1; rewrite in_map_iff in s_in_ll1;
destruct s_in_ll1 as [[s' t] [s'_eq_s st_in_ll]]; simpl in s'_eq_s; subst s';
destruct (In_split _ _ st_in_ll) as [ll1 [ll2 H]];
exists t; exists ll1; exists ll2; split; trivial.
apply E_ll; trivial.
Qed.

Lemma equiv_in_list_2 :
  forall (A : Type) (R : relation A) s ll, (forall s t, In (s,t) ll -> R s t) ->
  In s (map (fun st => snd st) ll) ->
  exists t, exists ll1, exists ll2, R t s /\ ll = ll1 ++ (t,s) :: ll2.
Proof.
intros A R s ll E_ll s_in_ll2; rewrite in_map_iff in s_in_ll2;
destruct s_in_ll2 as [[t s'] [s'_eq_s ts_in_ll]]; simpl in s'_eq_s; subst s';
destruct (In_split _ _ ts_in_ll) as [ll1 [ll2 H]];
exists t; exists ll1; exists ll2; split; trivial.
apply E_ll; trivial.
Qed.

Lemma equiv_swap :
  forall (A : Type) (R : relation A), 
  forall ll, (forall s t, In (s,t) ll -> R s t) ->
  exists ll', (forall s t, In (s,t) ll' -> R t s) /\
                map (fun st => fst st) ll = map (fun st => snd st) ll' /\
                map (fun st => snd st) ll = map (fun st => fst st) ll' /\
                (forall s t, In (s,t) ll <-> In (t,s) ll').
Proof. 
intros A R ll; induction ll as [ | [s t] ll]; intro E_ll. 
exists (@nil (A * A)); repeat split; trivial; contradiction. 
destruct IHll as [ll' [E_ll' [H1 [H2 H3]]]].
intros; apply E_ll; right; trivial.
exists ((t,s) :: ll'); repeat split.
intros t' s' [t's'_eq_ts | t's'_in_ll'].
injection t's'_eq_ts; intros; subst; apply E_ll; left; trivial.
apply E_ll'; trivial.
simpl; rewrite H1; trivial.
simpl; rewrite H2; trivial.
intros [st_eq_st | st_in_ll].
injection st_eq_st; intros; subst; left; trivial.
right; rewrite <- H3; trivial.
intros [ts_eq_ts | ts_in_ll].
injection ts_eq_ts; intros; subst; left; trivial.
right; rewrite H3; trivial.
Qed.









