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


Set Implicit Arguments.

From Coq Require Import Relations Setoid List Multiset Arith Recdef Morphisms.
From CoLoR Require Import more_list list_permut ordered_set.

Ltac dummy a b a_eq_b :=
assert (Dummy : a = b); [exact a_eq_b | clear a_eq_b; rename Dummy into a_eq_b].

Module Type Sort.

Declare Module Import DOS : ordered_set.S.

Declare Module Import LPermut  :  
  list_permut.S with Definition EDS.A := DOS.A
                      with Definition EDS.eq_A := @eq DOS.A.

(** *** Decomposition of the list wrt a pivot. *)
Function partition (pivot : A) (l : list A) {struct l} : (list A) * (list A) :=
  match l with 
  | nil => (nil, nil)
  | a :: l' => 
	match partition pivot l' with (l1,l2) =>
	 if o_bool a pivot then (a :: l1, l2) else (l1, a :: l2)
        end
end.

Parameter quicksort : list A -> list A.

Function remove_list (la l : list A) {struct l} : option (list A) :=
  match la with
  | nil => Some l
  | a :: la' => 
	match l with 
	| nil => None
	| b :: l' => 
	   if eq_bool a b 
	   then remove_list la' l'
	   else 
	     match remove_list la l' with
	     | None => None
	     | Some rmv => Some (b :: rmv)
	     end
        end
  end.

(** *** Definition of a sorted list. *)
Inductive is_sorted : list A -> Prop :=
  | is_sorted_nil : is_sorted nil
  | is_sorted_cons1 : forall t, is_sorted (t :: nil)
  | is_sorted_cons2 :
      forall t1 t2 l, o t1 t2 -> is_sorted (t2 :: l) -> is_sorted (t1 :: t2 :: l).

#[global] Hint Constructors is_sorted : core.

Parameter in_remove_list :
  forall l la, is_sorted la -> is_sorted l -> 
  match remove_list la l with
  | None => forall rmv, ~ (permut (la ++ rmv) l)
  | Some rmv => permut (la ++ rmv) l
  end.

Parameter quicksort_equation : forall l : list A,
       quicksort l =
       match l with
       | nil => nil (A:=A)
       | h :: tl =>
           let (l1, l2) := partition h tl in
           quicksort l1 ++ h :: quicksort l2
       end.

Parameter quick_permut : forall l, permut l (quicksort l).

Parameter quick_permut_bis :
 forall l1 l2, permut l1 l2 -> permut (quicksort l1) l2.

Parameter length_quicksort : forall l, length (quicksort l) = length l.

Parameter in_quick_in : forall a l, In a l <-> In a (quicksort l).

Parameter sorted_tl_sorted : forall e l, is_sorted (e :: l) -> is_sorted l.

Parameter quick_sorted : forall l, is_sorted (quicksort l).

Parameter sort_is_unique :
  forall l1 l2, is_sorted l1 -> is_sorted l2 -> permut l1 l2 -> l1 = l2.

End Sort.

(** ** Definition of quicksort over lists. *)
Module Make (DOS1 : ordered_set.S) <: Sort with Module DOS := DOS1.

Module Import DOS := DOS1.

Module EDS := decidable_set.Convert(DOS1).

Module Import LPermut   <:  
  list_permut.S with Definition EDS.A := DOS.A
                      with Definition EDS.eq_A := @eq DOS.A :=
list_permut.Make EDS.

  Global Instance mem_morph : Proper (eq ==> permut ==> iff) (mem EDS.eq_A).

  Proof. intros a b ab c d cd. subst. apply mem_permut_mem; trivial. Qed.

  Global Instance add_A_morph : Proper (eq ==> permut ==> permut) (List.cons (A:=A)).

  Proof. intros a b e l1 l2 P. rewrite <- permut_cons; trivial. Qed.

Global Instance length_morph : Proper (permut ==> eq) (length (A:=A)).

Proof. intros a b ab. eapply permut_length. apply ab. Qed.

(** *** Decomposition of the list wrt a pivot. *)
Function partition (pivot : A) (l : list A) {struct l} : (list A) * (list A) :=
  match l with 
  | nil => (nil, nil)
  | a :: l' => 
	match partition pivot l' with (l1,l2) =>
	 if o_bool a pivot then (a :: l1, l2) else (l1, a :: l2)
        end
end.

Function quicksort (l : list A) { measure (@length A) l} : list A :=
   match l with
	| nil => nil
	| h :: tl => 
             match partition h tl with (l1, l2) =>
             quicksort l1 ++ h :: quicksort l2
        end
    end. 
Proof. 
(* 1 Second recursive call *)
intros e_l e l e_l_eq_e_l; subst e_l;
functional induction (partition e l)
   as [|H1 e' l' H2 IH l1 l2 rec_res e'_lt_e|H1 e' l' H2 IH l1 l2 rec_res H3];
intros ll1 ll2 Hpart; injection Hpart; intros H H'; subst.
(* 1.1 l = nil *)
simpl; auto with arith.
(* 1.2 l = _ :: _ *)
apply lt_trans with (length (e :: l')); [apply (IH _ _ rec_res) | auto with arith].
simpl; apply lt_n_S; apply (IH _ _ rec_res).

(* 2 First recursive call *)
intros e_l e l e_l_eq_e_l; subst e_l;
functional induction (partition e l)
   as [|H1 e' l' H2 IH l1 l2 rec_res e'_lt_e|H1 e' l' H2 IH l1 l2 rec_res H3];
intros ll1 ll2 Hpart; injection Hpart; intros H H'; subst.
(* 2.1 l = nil *)
simpl; auto with arith.
(* 2.2 l = _ :: _ *)
simpl; apply lt_n_S; apply (IH _ _ rec_res).
apply lt_trans with (length (e :: l')); [apply (IH _ _ rec_res) | auto with arith].
Defined.

(** *** The result of quicksort is a permutation of the original list. *)
Lemma partition_list_permut1 :
 forall e l, let (l1,l2) := partition e l in permut (l1 ++ l2) l.
Proof.
intros e l; functional induction (partition e l)
   as [|H1 e' l' H2 IH l1 l2 rec_res e'_lt_e|H1 e' l' H2 IH l1 l2 rec_res H3].
 (* l = nil *)
auto.
(* l = a :: l' /\ o_A a e *)
simpl app; rewrite rec_res in IH; rewrite IH; auto.
 (* l = a::l' /\ ~o_A a e *)
simpl app; rewrite rec_res in IH;
apply permut_sym; rewrite <- permut_cons_inside; auto.
reflexivity.
Qed.

Theorem quick_permut : forall l, permut l (quicksort l).
Proof.
intros l; functional induction (quicksort l)
   as [ | l a' l' l_eq_a'_l' l1 l2 H S1 S2]; auto.
(* 2.1 l = nil *)
rewrite <- permut_cons_inside.
assert (P := partition_list_permut1 a' l'); rewrite H in P.
rewrite <- P; rewrite <- S1; rewrite <- S2; auto.
reflexivity.
Qed.

Theorem quick_permut_bis :
 forall l1 l2, permut l1 l2 -> permut (quicksort l1) l2.
Proof.
intros l1 l2 P; apply permut_trans with l1; trivial;
apply permut_sym; apply quick_permut.
Qed.

(** *** Definition of a sorted list. *)
Inductive is_sorted : list A -> Prop :=
  | is_sorted_nil : is_sorted nil
  | is_sorted_cons1 : forall t, is_sorted (t :: nil)
  | is_sorted_cons2 :
      forall t1 t2 l, o t1 t2 -> is_sorted (t2 :: l) -> is_sorted (t1 :: t2 :: l).

#[global] Hint Constructors is_sorted : core.

(** *** The result of quicksort is a sorted list. *)
Lemma sorted_tl_sorted :
  forall e l, is_sorted (e :: l) -> is_sorted l.
Proof.
intros e l S; inversion S; auto.
Qed.

Lemma quick_sorted_aux1 :
  forall l1 l2 e, is_sorted l1 -> is_sorted l2 ->
  (forall a, mem EDS.eq_A a l1 -> o a e) ->
  (forall a, mem EDS.eq_A a l2 -> o e a) -> 
  is_sorted (l1 ++ e :: l2).
Proof.
induction l1 as [ | e1 l1 ]; intros l2 e S1 S2 L1 L2.
simpl; destruct l2 as [ | e2 l2]; intros; 
[apply is_sorted_cons1 | apply is_sorted_cons2 ]; trivial;
apply (L2 e2); simpl; left; reflexivity.
destruct l1 as [ | e1' l1] ; simpl; intros; apply is_sorted_cons2.
apply L1; left; reflexivity.
simpl in IHl1; apply IHl1; trivial; contradiction.
inversion S1; trivial.
rewrite app_comm_cons; apply IHl1; trivial.
inversion S1; trivial.
intros; apply L1; trivial; right; trivial.
Qed.

Lemma quick_sorted_aux3 :
  forall l e, let (l1,_) := partition e l in forall a, mem EDS.eq_A a l1 -> o a e.
Proof.
intros l e;
  functional induction (partition e l) as
    [|l a' l' l_eq_a'_l' IH l1' l2' H a'_lt_e
     |l a' l' l_eq_a'_l' IH l1' l2' H _H].
contradiction.
intros a [a_eq_a' | a_in_l1']; [idtac | rewrite H in IH; apply IH; trivial].
generalize (o_bool_ok a' e); dummy a a' a_eq_a'; subst; rewrite a'_lt_e; trivial.
intros; rewrite H in IH; apply IH; trivial.
Qed.

Lemma quick_sorted_aux4 :
  forall l e, let (_,l2) := partition e l in forall a, mem EDS.eq_A a l2 -> o e a.
Proof.
intros l e;
functional induction (partition e l) 
  as [|l a' l' l_eq_a'_l' IH l1' l2' H a'_lt_e
      |l a' l' l_eq_a'_l' IH l1' l2' H a'_ge_e].
contradiction.
intros; rewrite H in IH; apply IH; trivial.
intros a [a_eq_a' | a_in_l1']; [subst | rewrite H in IH; apply IH]; trivial.
dummy a a' a_eq_a'; subst; trivial.
generalize (o_bool_ok a' e); rewrite a'_ge_e; intro a'_ge_e'.
destruct (o_total e a'); intros.
assumption.
absurd (DOS.o a' e); assumption.
Qed.

Theorem quick_sorted : forall l, is_sorted (quicksort l).
Proof.
intros l; 
functional induction (quicksort l)
   as [ | l a' l' l_eq_a'_l' l1 l2 H S1 S2].
auto.
apply quick_sorted_aux1; trivial.
intros a a_in_ql1; 
assert (H1 := quick_sorted_aux3 l' a'); rewrite H in H1; apply H1.
rewrite (mem_permut_mem a (quick_permut l1)); trivial.
intros a a_in_ql2; 
assert (H2 := quick_sorted_aux4 l' a'); rewrite H in H2;
apply H2; rewrite (mem_permut_mem a (quick_permut l2)); trivial.
Qed.

(** ***  There is a unique sorted list equivalent up to a permutation to a given list.*)
Lemma sorted_cons_min : 
 forall l e, is_sorted (e :: l) -> (forall e', mem EDS.eq_A e' (e :: l) -> o e e').
Proof.
simpl; intros l e S e' [e'_eq_e | e'_in_l].
dummy e' e e'_eq_e; subst; trivial.
generalize o_proof; intro O; inversion O as [R _ _]; apply R.
generalize e S e' e'_in_l; clear e S e' e'_in_l; induction l as [ | a l ].
intros e _ e' e'_in_nil; elim e'_in_nil.
simpl; intros e S e' [e'_eq_a | e'_in_l].
dummy e' a e'_eq_a; subst e'; inversion S; trivial.
generalize o_proof; intro O; inversion O as [ _ T _ ]; apply T with a.
inversion S; trivial.
apply IHl; trivial; inversion S; trivial.
Qed.

Theorem sort_is_unique :
  forall l1 l2, is_sorted l1 -> is_sorted l2 -> permut l1 l2 -> l1 = l2.
Proof.
induction l1 as [ | e1 l1 ]; intros l2 S1 S2 P.
inversion P; trivial.
inversion P as [ | a b l k1 k2 a_eq_b P' H1 H']; dummy e1 b a_eq_b; subst.
destruct k1 as [ | a1 k1].
rewrite (IHl1 k2); trivial.
inversion S1; trivial.
inversion S2; trivial.
assert (e1_eq_a1 : b = a1).
assert (O:= o_proof); inversion O as [ _ _ AS ]; apply AS; clear O AS.
apply (sorted_cons_min S1); rewrite P; left; reflexivity.
apply (sorted_cons_min S2); rewrite <- P; left; reflexivity.
subst a1; rewrite (IHl1 (k1 ++ b :: k2)); trivial.
apply sorted_tl_sorted with b; trivial.
apply sorted_tl_sorted with b; trivial.
simpl in P; rewrite <- permut_cons in P; trivial.
reflexivity.
Qed.

(** Some usefull properties on the result of quicksort. *)
Lemma length_quicksort : forall l, length (quicksort l) = length l.
Proof.
intro l; apply permut_length with EDS.eq_A;
apply permut_sym; apply quick_permut.
Qed.

Lemma in_quick_in : forall a l, In a l <-> In a (quicksort l).
Proof.
intros a l; apply in_permut_in.
apply quick_permut.
Qed.

Lemma in_quicksort_cons : forall a l, In a (quicksort (a :: l)).
Proof.
intros a l; rewrite <- in_quick_in; left; trivial.
Qed.

(** What happens when a sorted list is removed from another one.*)
Function remove_list (la l : list A) {struct l} : option (list A) :=
  match la with
  | nil => Some l
  | a :: la' => 
	match l with 
	| nil => None
	| b :: l' => 
	   if eq_bool a b
	   then remove_list la' l'
	   else 
	     match remove_list la l' with
	     | None => None
	     | Some rmv => Some (b :: rmv)
	     end
        end
  end.

Lemma in_remove_list :
  forall l la, is_sorted la -> is_sorted l -> 
  match remove_list la l with
  | None => forall rmv, ~ (permut (la ++ rmv) l)
  | Some rmv => permut (la ++ rmv) l
  end.
Proof.
fix in_remove_list 1.
intro l; case l; clear l.
(* l = [] *)
intro la; simpl; case la; clear la.
intros _ _; apply Pnil.
intros a la Sla _ rmv P; assert (H := permut_length P); discriminate.
(* l = _ :: _ *)
intros e l la; simpl; case la; clear la.
intros _ _; reflexivity.
intros a la Sala Sel ; assert (Sl := sorted_tl_sorted Sel).
assert (Sla := sorted_tl_sorted Sala).
generalize (eq_bool_ok a e); case (eq_bool a e).
intros a_eq_e; generalize (in_remove_list l la Sla Sl); case (remove_list la l).
intros rmv P; simpl; rewrite <- permut_cons; assumption.
intros H rmv P; apply (H rmv); simpl in P; rewrite <- permut_cons in P; assumption.
intros a_diff_e; generalize (in_remove_list l (a :: la) Sala Sl); case (remove_list (a :: la) l).
intros rmv P; symmetry; rewrite <- permut_cons_inside.
symmetry; assumption.
reflexivity.
intros H rmv P.
assert (e_in_larm : mem EDS.eq_A e ((a :: la) ++ rmv)).
rewrite (mem_permut_mem e P); left; reflexivity.
simpl in e_in_larm; case e_in_larm; clear e_in_larm.
intro e_eq_a; apply a_diff_e; symmetry; assumption.
rewrite <- mem_or_app; intro e'_in_larm; case e'_in_larm; clear e'_in_larm.
intro e_in_la; apply a_diff_e;
assert (O := o_proof); inversion_clear O as [ _ _ AS]; apply AS.
apply sorted_cons_min with la; [apply Sala | right; trivial].
apply sorted_cons_min with l; [apply Sel | rewrite <- P; left; reflexivity].
intro e_in_rmv; case (mem_split_set _ _ eq_bool_ok _ _ e_in_rmv);
intros e' M; case M; clear M.
intros l1 M; case M; clear M.
intros l2 M; case M; clear M.
intros e_eq_e' M; case M; clear M.
intros M _; subst rmv.
apply (H (l1 ++ l2)).
rewrite ass_app in P; simpl in P.
assert (P' := permut_add_inside ((a :: la) ++ l1) l2 nil l (sym_eq e_eq_e')); simpl in P'.
rewrite <- P' in P.
rewrite ass_app; simpl; assumption.
Qed.

End Make.

(*
(** *** The lists resulting from the partition are not longer than the original one. *)
Lemma length_fst_partition :
 forall n, forall pivot, forall l,
  length l <= n -> length (fst (partition pivot l)) < S n.
Proof.
induction n; intros pivot l; destruct l as [ | e l ]; simpl; auto with arith.
intro H; generalize (le_Sn_O (length l) H); intros; contradiction.
intro L'; assert (L : length l <= n).
apply le_S_n; trivial.
generalize (IHn pivot l L); destruct (partition pivot l);
destruct (o_elt_dec e pivot); simpl; auto with arith.
Qed.

Lemma length_snd_partition :
 forall n, forall pivot, forall l, 
  length l <= n -> length (snd (partition pivot l)) < S n.
Proof.
induction n; intros pivot l; destruct l as [ | e l ]; simpl; auto with arith.
intro H; generalize (le_Sn_O (length l) H); intros; contradiction.
intro L'; assert (L : length l <= n).
apply le_S_n; trivial.
generalize (IHn pivot l L); destruct (partition pivot l);
destruct (o_elt_dec e pivot); simpl; auto with arith.
Qed.

(** *** Definition of a step of quicksort. *)
Definition F_quick : 
  forall l : list elt, (forall y : list elt , o_length y l -> list elt) -> list elt.
Proof.
destruct l as [ | e l ].
intros; exact nil.
intro qrec;
set (pl := partition e l);
exact 
((qrec (fst pl) (length_fst_partition e l (le_n (length l)))) ++
 e :: (qrec (snd pl) (length_snd_partition e l (le_n (length l))))).
Defined.

(** *** Definition of quicksort. *)
Definition quicksort : forall (l : list elt), (list elt) :=
Fix (@well_founded_length elt) (fun l => list elt) F_quick.

(** *** A more practical equivalent definition of quicksort. *)
Lemma quicksort_unfold : forall l : list elt,
quicksort l = @F_quick l (fun y _ => quicksort y).
Proof.
intros; unfold quicksort;
apply Fix_eq with (P:= (fun _:list elt => list elt)).
unfold F_quick; destruct x; simpl; auto.
intros f g H; do 2 rewrite H; trivial.
Save.

(** *** Sorting the empty list yields the empty list. *)
Lemma quick_nil : quicksort nil = nil.
Proof.
rewrite quicksort_unfold; unfold F_quick; simpl; trivial.
Qed.

(** *** The usual equality on quicksort. *)
Lemma quick_cons_aux1 : 
  forall e l, quicksort (e :: l) = 
              let pl := partition e l in 
              (quicksort (fst pl)) ++ e :: (quicksort (snd pl)).
Proof.
intros e l; rewrite quicksort_unfold; unfold F_quick; simpl; trivial.
Qed.

Theorem quick_cons : 
 forall e l, let (l1,l2) := partition e l in 
 quicksort (e :: l) = (quicksort l1) ++ e :: (quicksort l2).
Proof.
intros; generalize (quick_cons_aux1 e l); destruct (partition e l).
trivial.
Save.

Extract Constant eq_elt_dec => eq.
Extract Constant o_elt_dec => le.
Extract Constant elt => int.
Extraction split_list.
Extraction partition.
Extraction NoInline partition.
Extraction quicksort.
*)

