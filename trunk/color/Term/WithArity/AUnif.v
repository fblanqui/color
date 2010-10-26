(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2008-01-22

syntactic unification
*)

Set Implicit Arguments.

Require Import ASubstitution.
Require Import ATerm.
Require Import EqUtil.
Require Import ListUtil.
Require Import LogicUtil.
Require Import VecUtil.
Require Import AVariables.
Require Import BoolUtil.
Require Import ListForall.
Require Import NatUtil.
Require Import Relations.
Require Import SN.

Section S.

Variable Sig : Signature.

Notation term := (term Sig). Notation terms := (vector term).
Notation substitution := (substitution Sig).

Ltac case_beq_symb := ASignature.case_beq_symb Sig.

(***********************************************************************)
(** unification problem *)

Definition eqn := ((term * term)%type).
Definition eqns := (list eqn).

Definition eqn_sub s (e : eqn) := (sub s (fst e), sub s (snd e)).

Definition solved_eqn := ((variable * term)%type).
Definition solved_eqns := (list solved_eqn).

Definition problem := (option ((solved_eqns * eqns)%type)).

Definition solved (p : problem) :=
  match p with
  | None
  | Some (_, nil) => true
  | _ => false
  end.

Definition successfull (p : problem) :=
  match p with
  | Some (_, nil) => true
  | _ => false
  end.

Lemma successfull_solved : forall p, successfull p = true -> solved p = true.

Proof.
destruct p. destruct p. destruct e. refl. discr. discr.
Qed.

(***********************************************************************)
(** variables of a list of equations *)

Require Import AVariables.

Definition vars_eqn (e : eqn) := union (vars (fst e)) (vars (snd e)).

Fixpoint vars_eqns l :=
  match l with
    | nil => empty
    | e :: l' => union (vars_eqn e) (vars_eqns l')
  end.

Lemma vars_eqns_app : forall l m,
  vars_eqns (l ++ m) [=] union (vars_eqns l) (vars_eqns m).

Proof.
induction l; simpl; intros. symmetry. apply union_empty_left.
transitivity (union (vars_eqn a) (union (vars_eqns l) (vars_eqns m))).
apply union_m. refl. apply IHl. symmetry. apply union_assoc.
Qed.

Lemma vars_eqns_combine : forall n (us vs : terms n),
  vars_eqns (combine (list_of_vec vs) (list_of_vec us))
  [=] union (vars_vec vs) (vars_vec us).

Proof.
induction us; simpl; intros. VOtac. simpl. symmetry. apply union_empty_left.
VSntac vs. clear H. set (x := Vhead vs). set (ts := Vtail vs). simpl.
unfold vars_eqn. simpl.
transitivity
  (union (union (vars x) (vars a)) (union (vars_vec ts) (vars_vec us))).
apply union_m. refl. apply IHus. Equal_tac; union.
Qed.

Lemma mem_vars_sub_single : forall n (u : term) x v,
  mem n (vars u) = false -> mem n (vars v) = false ->
  mem n (vars (sub (single x v) u)) = false.

Proof.
intros. transitivity (mem n
  (if mem x (vars u) then union (vars v) (remove x (vars u)) else vars u)).
apply mem_m. refl. apply vars_single.
case_eq (mem x (vars u)). mem. rewrite H0. rewrite H. refl.
hyp.
Qed.

Lemma mem_vars_sub_single' : forall n (u v : term),
  mem n (vars v) = false -> mem n (vars (sub (single n v) u)) = false.

Proof.
intros. transitivity (mem n
  (if mem n (vars u) then union (vars v) (remove n (vars u)) else vars u)).
apply mem_m. refl. apply vars_single.
case_eq (mem n (vars u)). mem. rewrite H0. rewrite H. refl.
hyp.
Qed.

Lemma vars_eqn_sub : forall x v e,
  vars_eqn (eqn_sub (single x v) e) [=]
  if mem x (vars_eqn e) then union (vars v) (remove x (vars_eqn e))
    else vars_eqn e.

Proof.
intros. destruct e as [l r]. unfold vars_eqn, eqn_sub. simpl.
transitivity (union
  (if mem x (vars l) then union (vars v) (remove x (vars l)) else vars l)
  (if mem x (vars r) then union (vars v) (remove x (vars r)) else vars r)).
apply union_m; apply vars_single. mem.
case_eq (mem x (vars l)); case_eq (mem x (vars r)); bool.
transitivity (union (vars v) (union (remove x (vars l)) (remove x (vars r)))).
apply union_idem_3. apply union_m. refl. symmetry. apply remove_union.
transitivity (union (vars v) (union (remove x (vars l)) (vars r))).
apply union_assoc. apply union_m. refl.
transitivity (union (remove x (vars l)) (remove x (vars r))).
apply union_m. refl. symmetry. apply remove_equal. apply mem_4. hyp.
symmetry. apply remove_union.
transitivity (union (vars v) (union (vars l) (remove x (vars r)))).
apply union_sym_2. apply union_m. refl.
transitivity (union (remove x (vars l)) (remove x (vars r))).
apply union_m. symmetry. apply remove_equal. apply mem_4. hyp. refl.
symmetry. apply remove_union. refl.
Qed.

Lemma vars_eqns_subs : forall x v l,
  vars_eqns (map (eqn_sub (single x v)) l) [=]
  if mem x (vars_eqns l) then union (vars v) (remove x (vars_eqns l))
    else vars_eqns l.

Proof.
induction l; simpl; intros. refl. mem.
transitivity (union
  (if mem x (vars_eqn a) then union (vars v) (remove x (vars_eqn a))
    else vars_eqn a) (if mem x (vars_eqns l)
      then union (vars v) (remove x (vars_eqns l)) else vars_eqns l)).
apply union_m. apply vars_eqn_sub. exact IHl.
case_eq (mem x (vars_eqn a)); case_eq (mem x (vars_eqns l)); bool.
transitivity
  (union (vars v) (union (remove x (vars_eqn a)) (remove x (vars_eqns l)))).
apply union_idem_3. apply union_m. refl. symmetry. apply remove_union.
transitivity (union (vars v) (union (remove x (vars_eqn a)) (vars_eqns l))).
apply union_assoc. apply union_m. refl.
transitivity (union (remove x (vars_eqn a)) (remove x (vars_eqns l))).
apply union_m. refl. symmetry. apply remove_equal. apply mem_4. hyp.
symmetry. apply remove_union.
transitivity (union (vars v) (union (vars_eqn a) (remove x (vars_eqns l)))).
apply union_sym_2. apply union_m. refl.
transitivity (union (remove x (vars_eqn a)) (remove x (vars_eqns l))).
apply union_m. symmetry. apply remove_equal. apply mem_4. hyp. refl.
symmetry. apply remove_union. refl.
Qed.

(***********************************************************************)
(** well-formed unification problems *)

Definition notin_eqn x (e : eqn) :=
  mem x (vars (fst e)) = false /\ mem x (vars (snd e)) = false.

Definition notin_solved_eqn x (e : solved_eqn) :=
  x <> fst e /\ mem x (vars (snd e)) = false.

Definition notin_vars_solved_eqn (v : term) (e : solved_eqn) :=
  mem (fst e) (vars v) = false.

Fixpoint solved_eqns_wf (l : solved_eqns) :=
  match l with
    | nil => True
    | (x, v) :: l' => mem x (vars v) = false
      /\ lforall (notin_solved_eqn x) l' /\ solved_eqns_wf l'
      /\ lforall (notin_vars_solved_eqn v) l'
  end.

Definition notin l2 (e : solved_eqn) := lforall (notin_eqn (fst e)) l2.
 
Definition problem_wf (p : problem) :=
  match p with
    | Some (l1, l2) => solved_eqns_wf l1 /\ lforall (notin l2) l1
    | _ => True
  end.

Definition solved_eqn_sub s (e : solved_eqn) := (fst e, sub s (snd e)).

(***********************************************************************)
(** properties of well-formed problems *)

Lemma lforall_notin_solved_eqn_1 : forall n t, mem n (vars t) = false ->
  forall l' l, lforall (notin ((t, Var n) :: l')) l -> 
    lforall (notin_solved_eqn n) (map (solved_eqn_sub (single n t)) l).

Proof.
induction l; simpl. auto. destruct a. simpl. unfold notin_eqn. simpl.
mem. intros. unfold notin_solved_eqn. simpl. intuition.
subst n0. rewrite (beq_refl beq_nat_ok) in H4. discriminate.
apply mem_vars_sub_single'; hyp.
Qed.

Lemma lforall_notin_solved_eqn_1' : forall n t, mem n (vars t) = false ->
  forall l' l, lforall (notin ((Var n, t) :: l')) l -> 
    lforall (notin_solved_eqn n) (map (solved_eqn_sub (single n t)) l).

Proof.
induction l; simpl. auto. destruct a. simpl. unfold notin_eqn. simpl.
mem. intros. unfold notin_solved_eqn. simpl. intuition.
subst n0. rewrite (beq_refl beq_nat_ok) in H1. discriminate.
apply mem_vars_sub_single'; hyp.
Qed.

Lemma lforall_notin_solved_eqn_2 : forall n t, mem n (vars t) = false ->
  forall x l, lforall (notin_solved_eqn n) l -> 
      lforall (notin_solved_eqn n) (map (solved_eqn_sub (single x t)) l).

Proof.
induction l; simpl. auto. destruct a. intuition. unfold notin_solved_eqn in H1.
simpl in H1. unfold notin_solved_eqn. simpl. intuition.
apply mem_vars_sub_single; hyp.
Qed.

Lemma lforall_notin_vars_solved_eqn_1 : forall n t0 t1 l' l,
  lforall (notin ((Var n, t0) :: l')) l ->
  lforall (notin_vars_solved_eqn t1) l ->
  lforall (notin_vars_solved_eqn (sub (single n t0) t1))
  (map (solved_eqn_sub (single n t0)) l).

Proof.
induction l; simpl. auto. destruct a.
unfold solved_eqn_sub at 1, notin_vars_solved_eqn at 1 3, notin_eqn. simpl.
intuition. apply mem_vars_sub_single; hyp.
Qed.

Lemma lforall_notin_vars_solved_eqn_1' : forall n t0 t1 l' l,
  lforall (notin ((t0, Var n) :: l')) l ->
  lforall (notin_vars_solved_eqn t1) l ->
  lforall (notin_vars_solved_eqn (sub (single n t0) t1))
  (map (solved_eqn_sub (single n t0)) l).

Proof.
induction l; simpl. auto. destruct a.
unfold solved_eqn_sub at 1, notin_vars_solved_eqn at 1 3, notin_eqn. simpl.
intuition. apply mem_vars_sub_single; hyp.
Qed.

Lemma lforall_notin_vars_solved_eqn_2 : forall n u l' l,
  lforall (notin ((Var n, u) :: l')) l ->
  lforall (notin_vars_solved_eqn u) (map (solved_eqn_sub (single n u)) l).

Proof.
induction l; simpl. auto. destruct a.
unfold notin_vars_solved_eqn at 1, notin_eqn, notin at 1. simpl.
mem. intuition.
Qed.

Lemma lforall_notin_vars_solved_eqn_2' : forall n u l' l,
  lforall (notin ((u, Var n) :: l')) l ->
  lforall (notin_vars_solved_eqn u) (map (solved_eqn_sub (single n u)) l).

Proof.
induction l; simpl. auto. destruct a.
unfold notin_vars_solved_eqn at 1, notin_eqn, notin at 1. simpl.
mem. intuition.
Qed.

Lemma solved_eqns_wf_map : forall n t, mem n (vars t) = false ->
  forall l' l, solved_eqns_wf l -> lforall (notin ((Var n, t) :: l')) l ->
    solved_eqns_wf (map (solved_eqn_sub (single n t)) l).

Proof.
induction l; simpl. auto. destruct a. simpl. unfold notin_eqn. simpl.
mem. intuition.
apply mem_vars_sub_single; hyp. apply lforall_notin_solved_eqn_2; hyp.
apply lforall_notin_vars_solved_eqn_1 with l'; hyp.
Qed.

Lemma solved_eqns_wf_map' : forall n t, mem n (vars t) = false ->
  forall l' l, solved_eqns_wf l -> lforall (notin ((t, Var n) :: l')) l ->
    solved_eqns_wf (map (solved_eqn_sub (single n t)) l).

Proof.
induction l; simpl. auto. destruct a. simpl. unfold notin_eqn. simpl.
mem. intuition.
apply mem_vars_sub_single; hyp. apply lforall_notin_solved_eqn_2; hyp.
apply lforall_notin_vars_solved_eqn_1' with l'; hyp.
Qed.

Lemma notin_map : forall x t, mem x (vars t) = false ->
  forall l, notin (map (eqn_sub (single x t)) l) (x, t).

Proof.
induction l; simpl. trivial. destruct a. unfold notin_eqn. simpl. intuition.
transitivity (mem x
  (if mem x (vars t1) then union (vars t0) (remove x (vars t1)) else vars t1)).
apply mem_m. refl. apply vars_single.
case_eq (mem x (vars t1)). mem. rewrite H. rewrite H0.
refl. hyp.
transitivity (mem x
  (if mem x (vars t2) then union (vars t0) (remove x (vars t2)) else vars t2)).
apply mem_m. refl. apply vars_single.
case_eq (mem x (vars t2)). mem. rewrite H. rewrite H0.
refl. hyp.
Qed.

Lemma lforall_notin_eqn : forall x t, mem x (vars t) = false ->
  forall n l, lforall (notin_eqn x) l ->
      lforall (notin_eqn x) (map (eqn_sub (single n t)) l).

Proof.
induction l; simpl; intuition. destruct a. unfold eqn_sub. simpl.
unfold notin_eqn. simpl. unfold notin_eqn in H1. simpl in H1. intuition.
transitivity (mem x
  (if mem n (vars t1) then union (vars t0) (remove n (vars t1)) else vars t1)).
apply mem_m. refl. apply vars_single.
case_eq (mem n (vars t1)). mem. rewrite H. rewrite H3. refl.
hyp.
transitivity (mem x
  (if mem n (vars t2) then union (vars t0) (remove n (vars t2)) else vars t2)).
apply mem_m. refl. apply vars_single.
case_eq (mem n (vars t2)). mem. rewrite H. rewrite H4. refl.
hyp.
Qed.

Lemma lforall_notin_r : forall x t l' l,
  lforall (notin ((t, Var x) :: l')) l ->
  lforall (notin (map (eqn_sub (single x t)) l'))
  (map (solved_eqn_sub (single x t)) l).

Proof.
induction l; simpl. auto. destruct a. simpl. unfold notin_eqn. simpl.
mem. intuition. unfold notin. simpl.
unfold notin in H2. simpl in H2. apply lforall_notin_eqn; hyp.
Qed.

Lemma lforall_notin_l : forall x t l' l,
  lforall (notin ((Var x, t) :: l')) l ->
  lforall (notin (map (eqn_sub (single x t)) l'))
  (map (solved_eqn_sub (single x t)) l).

Proof.
induction l; simpl. auto. destruct a. simpl. unfold notin_eqn. simpl.
mem. intuition. unfold notin. simpl.
unfold notin in H2. simpl in H2. apply lforall_notin_eqn; hyp.
Qed.

Lemma lforall_notin_eqn_combine : forall x n (v1 v2 : terms n),
  mem x (vars_vec v1) = false -> mem x (vars_vec v2) = false ->
  lforall (notin_eqn x) (combine (list_of_vec v1) (list_of_vec v2)).

Proof.
induction v1; simpl; intros. trivial. VSntac v2. simpl.
autorewrite with mem in H. destruct (orb_false_elim H).
assert (mem x (vars (Vhead v2)) = false
  /\ mem x (vars_vec (Vtail v2)) = false). rewrite H1 in H0. simpl in H0.
autorewrite with mem in H0. destruct (orb_false_elim H0). intuition.
intuition. unfold notin_eqn. simpl. intuition.
Qed.

(***********************************************************************)
(** step function *)

Notation beq_symb := (@beq_symb Sig).

Definition step (p : problem) :=
  match p with
    | Some (l1, e :: l2) =>
      match e with
        | (v, Var x) =>
          if beq_term v (Var x) then Some (l1, l2)
            else if mem x (vars v) then None
              else Some ((x, v) :: List.map (solved_eqn_sub (single x v)) l1,
              List.map (eqn_sub (single x v)) l2)
        | (Var x, v) =>
          if beq_term v (Var x) then Some (l1, l2)
            else if mem x (vars v) then None
              else Some ((x, v) :: List.map (solved_eqn_sub (single x v)) l1,
              List.map (eqn_sub (single x v)) l2)
        | (Fun f vs, Fun g us) =>
          if beq_symb f g then
            Some (l1, List.combine (list_of_vec vs) (list_of_vec us) ++ l2)
            else None
      end
    | _ => p
  end.

Fixpoint iter_step k (p : problem) {struct k} :=
  match k with
    | 0 => p
    | S k' => step (iter_step k' p)
  end.

(***********************************************************************)
(** basic properties *)

Lemma iter_step_commut : forall k (p : problem),
  iter_step k (step p) = step (iter_step k p).

Proof.
induction k. refl. simpl. intro. rewrite IHk. refl.
Qed.

Lemma successfull_elim : forall k p, successfull (iter_step k p) = true ->
  exists l, iter_step k p = Some (l, nil).

Proof.
intros. destruct (iter_step k p). destruct p0. destruct e. exists s. refl.
discr. discr.
Qed.

Implicit Arguments successfull_elim [k p].

Lemma successfull_preserved : forall k p,
  successfull (iter_step k p) = true ->
  forall l, l > k -> successfull (iter_step l p) = true.

Proof.
cut (forall k p, successfull (iter_step k p) = true ->
  forall l, successfull (iter_step (l+k) p) = true); intros.
destruct (gt_plus H1). subst. apply H. hyp. elim l; clear l; simpl. hyp.
intros. destruct (successfull_elim H0). rewrite H1. refl.
Qed.

Lemma unsuccessfull_preserved : forall k p,
  iter_step k p = None -> forall l, l > k -> iter_step l p = None.

Proof.
cut (forall k p, iter_step k p = None -> forall l, iter_step (l+k) p = None);
intros. destruct (gt_plus H1). subst. apply H. hyp.
elim l; clear l; simpl. hyp. intros. rewrite H0. refl.
Qed.

Implicit Arguments unsuccessfull_preserved [k p l].

Lemma successfull_inv : forall k p,
  successfull (iter_step k p) = true ->
  forall l, l < k -> iter_step l p <> None.

Proof.
intros. intro. ded (unsuccessfull_preserved H1 H0). rewrite H2 in H. discr.
Qed.

(***********************************************************************)
(** size-based multiset ordering on equations *)

Notation nb_symb_occs := (@nb_symb_occs Sig).

Definition size e := nb_symb_occs (fst e) + nb_symb_occs (snd e).

Require Import MultisetNat.

Definition sizes l := list2multiset (List.map size l).

Definition sizes_lt l1 l2 := MultisetLt gt (sizes l1) (sizes l2).

Require Import Wellfounded.

Lemma wf_sizes_lt : well_founded sizes_lt.

Proof.
unfold sizes_lt. apply wf_inverse_image with (B := Multiset).
apply mord_wf. unfold eqA. intros. subst. hyp. exact lt_wf.
Qed.

(***********************************************************************)
(** number of distinct variables in equations *)

Definition nb_vars_lt l1 l2 :=
  cardinal (vars_eqns l1) < cardinal (vars_eqns l2).

Lemma wf_nb_vars_lt : well_founded nb_vars_lt.

Proof.
unfold nb_vars_lt. apply wf_inverse_image with (B := nat). exact lt_wf.
Qed.

Definition nb_vars_eq l1 l2 :=
  cardinal (vars_eqns l1) = cardinal (vars_eqns l2).

Require Import AVariables.

Lemma lt_card_vars_eqns_subs_l : forall x v l, mem x (vars v) = false ->
  cardinal (vars_eqns (map (eqn_sub (single x v)) l)) <
  cardinal (vars_eqns ((Var x, v) :: l)).

Proof.
intros. simpl. unfold vars_eqn. simpl. apply subset_cardinal_lt with x.
apply subset_trans with
  (if mem x (vars_eqns l) then union (vars v) (remove x (vars_eqns l))
    else vars_eqns l). apply subset_equal. apply vars_eqns_subs.
case_eq (mem x (vars_eqns l)); Subset_tac. In_intro. unfold not. intro.
rewrite (In_m (refl_equal x) (vars_eqns_subs x v l)) in H0. gen H0.
case_eq (mem x (vars_eqns l)); intros; In_elim; ded (mem_4 _ _ H).
contradiction. absurd (E.eq x x). hyp. refl.
ded (mem_4 _ _ H0). contradiction.
Qed.

Lemma lt_card_vars_eqns_subs_r : forall x v l, mem x (vars v) = false ->
  cardinal (vars_eqns (map (eqn_sub (single x v)) l)) <
  cardinal (vars_eqns ((v, Var x) :: l)).

Proof.
intros. simpl. unfold vars_eqn. simpl. apply subset_cardinal_lt with x.
apply subset_trans with
  (if mem x (vars_eqns l) then union (vars v) (remove x (vars_eqns l))
    else vars_eqns l). apply subset_equal. apply vars_eqns_subs.
case_eq (mem x (vars_eqns l)); Subset_tac. In_intro. unfold not. intro.
rewrite (In_m (refl_equal x) (vars_eqns_subs x v l)) in H0. gen H0.
case_eq (mem x (vars_eqns l)); intros; In_elim; ded (mem_4 _ _ H).
contradiction. absurd (E.eq x x). hyp. refl.
ded (mem_4 _ _ H0). contradiction.
Qed.

(***********************************************************************)
(** wellfounded ordering on equations *)

Require Import Lexico.

Definition lex_lt : relation (eqns * eqns) :=
  transp (lexp (transp nb_vars_lt) nb_vars_eq (transp sizes_lt)).

Lemma wf_lex_lt : well_founded lex_lt.

Proof.
unfold lex_lt. apply WF_wf_transp. apply WF_lexp.
unfold inclusion, transp, nb_vars_eq, nb_vars_lt. intros. do 2 destruct H.
rewrite H. hyp.
apply wf_WF_transp. exact wf_sizes_lt.
unfold Relation_Definitions.transitive, nb_vars_eq. intros.
transitivity (cardinal (vars_eqns y)); hyp.
apply wf_WF_transp. exact wf_nb_vars_lt.
Qed.

Definition Lt l1 l2 := lex_lt (l1, l1) (l2, l2).

Lemma wf_Lt : well_founded Lt.

Proof.
unfold Lt. apply wf_inverse_image with (f := fun l : eqns => (l, l)).
exact wf_lex_lt.
Qed.

Lemma Lt_eqns_subs_l : forall x v l, mem x (vars v) = false ->
  Lt (map (eqn_sub (single x v)) l) ((Var x, v) :: l).

Proof.
intros. unfold Lt, lex_lt, transp. apply lexp_intro. left.
unfold nb_vars_lt. apply lt_card_vars_eqns_subs_l. hyp.
Qed.

Lemma Lt_eqns_subs_r : forall x v l, mem x (vars v) = false ->
  Lt (map (eqn_sub (single x v)) l) ((v, Var x) :: l).

Proof.
intros. unfold Lt, lex_lt, transp. apply lexp_intro. left.
unfold nb_vars_lt. apply lt_card_vars_eqns_subs_r. hyp.
Qed.

Lemma Lt_cons : forall x l, Lt l (x :: l).

Proof.
intros. unfold Lt, lex_lt, transp. apply lexp_intro.
unfold nb_vars_eq, nb_vars_lt. simpl.
set (X := vars_eqns l). set (Y := vars_eqn x).
assert (cardinal X <= cardinal (XSet.union Y X)).
apply subset_cardinal. Subset_tac.
case (eq_nat_dec (cardinal X) (cardinal (XSet.union Y X))); intro. right.
intuition. unfold sizes_lt. unfold sizes. simpl.
unfold MultisetLt, transp. apply t_step. set (M := list2multiset (map size l)).
apply MSetRed with (X := M) (a := size x) (Y := MSetCore.empty). solve_meq.
solve_meq. intros. apply False_rec. eapply not_empty. apply H0. refl.
left. omega.
Qed.

Lemma Lt_combine : forall f vs g us l, beq_symb f g = true ->
  Lt (combine (list_of_vec vs) (list_of_vec us) ++ l)
     ((Fun f vs, Fun g us) :: l).

Proof.
intros. unfold Lt, lex_lt, transp. apply lexp_intro. right. split.
unfold nb_vars_eq, nb_vars_lt. simpl. unfold vars_eqn. simpl fst. simpl snd.
repeat rewrite vars_fun. rewrite vars_eqns_app. rewrite beq_symb_ok in H.
subst. rewrite vars_eqns_combine. refl.
unfold sizes_lt, MultisetLt, transp. apply t_step. unfold sizes. simpl.
rewrite map_app. set (M := list2multiset (map size l)).
apply MSetRed with (X := M) (a := size (Fun f vs, Fun g us))
  (Y := list2multiset (map size (combine (list_of_vec vs) (list_of_vec us)))).
solve_meq. rewrite list2multiset_app. unfold M. solve_meq.
intros. unfold size. simpl fst. simpl snd. repeat rewrite nb_symb_occs_fun.
destruct (member_multiset_list _ H0). destruct (in_map_elim H1). destruct H3.
subst. destruct x0. ded (in_combine_l H3). ded (in_combine_r H3).
ded (in_list_of_vec H4). ded (in_list_of_vec H5).
ded (Vin_nb_symb_occs_terms_ge H6). ded (Vin_nb_symb_occs_terms_ge H7).
rewrite H2. unfold size. unfold fst, snd. repeat rewrite nb_symb_occs_fun.
omega.
Qed.

Definition Lt' (p1 p2 : problem) :=
  match p1, p2 with
  | None, Some _ => True
  | Some (_, l1), Some (_, l2) => Lt l1 l2
  | _, _ => False
  end.

Lemma wf_Lt' : well_founded Lt'.

Proof.
intro. destruct a. destruct p. gen s. ded (wf_Lt e). elim H; clear H e; intros.
apply Acc_intro. destruct y. destruct p. intro. apply H0. hyp.
intro. apply Acc_intro. destruct y. destruct p; contradiction. contradiction.
apply Acc_intro. destruct y. destruct p; contradiction. contradiction.
Qed.

(***********************************************************************)
(** termination of iter_step *)

Lemma Lt_step : forall p, solved p = false -> Lt' (step p) p.

Proof.
destruct p. destruct p. destruct e. simpl. discr. intro. destruct e.
destruct t0; destruct t1.
(* var-var *)
simpl. mem. case_beq_nat n n0; unfold Lt'. apply Lt_cons.
apply Lt_eqns_subs_r. simpl. mem. hyp.
(* var-fun *)
unfold step. rewrite vars_fun. simpl. case_eq (mem n (vars_vec v)); unfold Lt'.
trivial. apply Lt_eqns_subs_l. hyp.
(* fun-var *)
unfold step. rewrite vars_fun. simpl. case_eq (mem n (vars_vec v)); unfold Lt'.
trivial. apply Lt_eqns_subs_r. hyp.
(* fun-fun *)
simpl. case_eq (beq_symb f f0); unfold Lt'. apply Lt_combine. hyp. trivial.
simpl. discr.
Qed.

Implicit Arguments Lt_step [p].

Lemma solved_inv : forall p, solved (step p) = false -> solved p = false.

Proof.
destruct p. 2: discr. destruct p. destruct e. discr. destruct e. refl.
Qed.

Implicit Arguments solved_inv [p].

Lemma wf_iter_step : forall p, exists k, solved (iter_step k p) = true.

Proof.
intro. ded (wf_Lt' p). elim H; clear H p; intros.
destruct x. 2: exists 0; refl. destruct p. destruct e. exists 0; refl.
set (p := Some (s, e::e0)). case_eq (solved (step p)).
exists 1. unfold iter_step. hyp.
destruct (H0 (step p) (Lt_step (solved_inv H1))). exists (S x).
simpl. rewrite <- iter_step_commut. hyp.
Qed.

(***********************************************************************)
(** the step function preserves well-formedness *)

Lemma step_wf : forall p, problem_wf p -> problem_wf (step p).

Proof.
intro. destruct p. 2: auto. destruct p. destruct e. auto. destruct e.
destruct t0; destruct t1.
(* var-var *)
simpl. mem. case_beq_nat n n0; simpl.
intuition. gen H1. elim s; simpl; intuition.
mem. rewrite H. intuition.
eapply lforall_notin_solved_eqn_1. simpl. mem. hyp. apply H2.
eapply solved_eqns_wf_map'. simpl. mem. hyp. hyp. apply H2.
gen H2. elim s; simpl; intuition. unfold notin_vars_solved_eqn. simpl.
unfold notin_eqn in H2. simpl in H2. intuition.
apply notin_map. simpl. mem. hyp.
apply lforall_notin_r. hyp.
(* var-fun *)
Opaque vars. simpl. set (u := Fun f v). intuition.
case_eq (mem n (vars u)); simpl; intuition.
eapply lforall_notin_solved_eqn_1'. hyp. apply H1.
eapply solved_eqns_wf_map. hyp. hyp. apply H1.
apply lforall_notin_vars_solved_eqn_2 with e0. hyp.
apply notin_map. hyp.
apply lforall_notin_l. hyp.
(* fun-var *) (* about the same proof *)
simpl. set (u := Fun f v). intuition.
case_eq (mem n (vars u)); simpl; intuition.
eapply lforall_notin_solved_eqn_1. hyp. apply H1.
eapply solved_eqns_wf_map'. hyp. hyp. apply H1.
apply lforall_notin_vars_solved_eqn_2' with e0. hyp.
apply notin_map. hyp.
apply lforall_notin_r. hyp.
(* fun-fun *)
simpl. case_beq_symb f f0; simpl; intuition.
gen H1. elim s; simpl; intuition. gen H1. unfold notin_eqn. simpl.
do 2 rewrite vars_fun. gen H4. unfold notin. simpl. rewrite lforall_app.
intuition. apply lforall_notin_eqn_combine; hyp. Transparent vars.
Qed.

Lemma iter_step_wf : forall p k, problem_wf p -> problem_wf (iter_step k p).

Proof.
induction k; simpl; intuition. apply step_wf. hyp.
Qed.

(***********************************************************************)
(** solutions of an unification problem *)

Definition is_sol_eqn s (e : eqn) := sub s (fst e) = sub s (snd e).
Definition is_sol_solved_eqn s (e : solved_eqn) := s (fst e) = sub s (snd e).

Definition is_sol_eqns s := lforall (is_sol_eqn s).
Definition is_sol_solved_eqns s := lforall (is_sol_solved_eqn s).

Definition is_sol s p :=
  match p with
    | None => False
    | Some (l1, l2) => is_sol_solved_eqns s l1 /\ is_sol_eqns s l2
  end.

Lemma is_sol_eqn_sub : forall s s' e,
  is_sol_eqn s e -> is_sol_eqn (sub_comp s' s) e.

Proof.
intros s s' e. destruct e. unfold is_sol_eqn. simpl. intro.
do 2 rewrite <- sub_sub. apply (f_equal (sub s')). hyp.
Qed.

Lemma is_sol_solved_eqns_sub : forall s s' l,
  is_sol_solved_eqns s l -> is_sol_solved_eqns (sub_comp s' s) l.

Proof.
induction l; simpl; intuition. destruct a. gen H0. unfold is_sol_solved_eqn.
simpl. intro. rewrite <- sub_sub. rewrite <- H0. refl.
Qed.

Lemma is_sol_sub : forall s s' p, is_sol s p -> is_sol (sub_comp s' s) p.

Proof.
intros s s' p. destruct p. 2: auto. destruct p. destruct l0.
simpl. intuition. apply is_sol_solved_eqns_sub. hyp.
destruct e. simpl. intuition. apply is_sol_solved_eqns_sub. hyp.
apply is_sol_eqn_sub. hyp. gen H2. elim l0; clear l0; simpl; intuition.
apply is_sol_eqn_sub. hyp.
Qed.

(***********************************************************************)
(** the step function preserves solutions *)

Lemma is_sol_solved_eqns_map : forall s n u, s n = sub s u ->
  forall l, is_sol_solved_eqns s (map (solved_eqn_sub (single n u)) l)
    <-> is_sol_solved_eqns s l.

Proof.
induction l; simpl. intuition. destruct a. unfold is_sol_solved_eqn. simpl.
intuition. rewrite H3. rewrite sub_sub. apply sub_eq. intros.
unfold sub_comp, single. case_beq_nat n x; auto.
rewrite H3. rewrite sub_sub. apply sub_eq. intros.
unfold sub_comp, single. case_beq_nat n x; auto.
Qed.

Lemma is_sol_eqns_map : forall s x u, s x = sub s u ->
  forall l, is_sol_eqns s (map (eqn_sub (single x u)) l) <-> is_sol_eqns s l.

Proof.
induction l; simpl. intuition. destruct a. unfold is_sol_eqn. simpl.
intuition. do 2 rewrite sub_sub in H3.
transitivity (sub (sub_comp s (single x u)) t0). symmetry.
apply sub_comp_single. hyp. rewrite H3. apply sub_comp_single. hyp.
do 2 rewrite sub_sub. transitivity (sub s t0). apply sub_comp_single. hyp.
rewrite H3. symmetry. apply sub_comp_single. hyp.
Qed.

Lemma lforall_is_sol_solved_eqn : forall s x u, s x = sub s u -> forall l,
  lforall (is_sol_solved_eqn s) (map (solved_eqn_sub (single x u)) l)
  <-> lforall (is_sol_solved_eqn s) l.

Proof.
induction l; simpl. intuition. destruct a. intuition.
gen H3. unfold is_sol_solved_eqn, solved_eqn_sub. simpl. rewrite sub_sub.
intro. rewrite H3. apply sub_comp_single. hyp.
gen H3. unfold is_sol_solved_eqn, solved_eqn_sub. simpl. rewrite sub_sub.
intro. rewrite H3. symmetry. apply sub_comp_single. hyp.
Qed.

Lemma lforall_is_sol_eqn_combine : forall s n (v v0 : terms n),
  lforall (is_sol_eqn s) (combine (list_of_vec v) (list_of_vec v0))
  <-> Vmap (sub s) v = Vmap (sub s) v0.

Proof.
induction v; simpl; intros. VOtac. simpl. intuition. VSntac v0. simpl.
unfold is_sol_eqn at 1. simpl. rewrite IHv. intuition. rewrite H1. rewrite H2.
refl. Veqtac. hyp. Veqtac. hyp.
Qed.

Lemma step_correct : forall s p, is_sol s p <-> is_sol s (step p).

Proof.
intros s p. destruct p. 2: simpl; intuition. destruct p. destruct l0.
simpl. intuition. destruct e. destruct t0; destruct t1.
(* var-var *)
simpl. unfold is_sol_eqn. mem. simpl.
case_beq_nat n n0; simpl. intuition. unfold is_sol_solved_eqn. simpl. intuition.
rewrite is_sol_solved_eqns_map; auto. rewrite is_sol_eqns_map; auto.
rewrite is_sol_solved_eqns_map in H3; auto.
rewrite is_sol_eqns_map in H2; auto.
(* var-fun *)
Opaque vars. simpl. set (u := Fun f v). unfold is_sol_eqn. simpl fst.
simpl snd.
simpl sub at 1. case_eq (mem n (vars u)). intuition; try contradiction.
ded (wf_term_var H0 H). discriminate. unfold is_sol, is_sol_solved_eqns.
simpl lforall. unfold is_sol_solved_eqn at 2. simpl fst. simpl snd. intuition.
rewrite lforall_is_sol_solved_eqn; auto. rewrite is_sol_eqns_map; auto.
rewrite lforall_is_sol_solved_eqn in H3; hyp.
rewrite is_sol_eqns_map in H2; hyp.
(* fun-var *) (* same proof *)
simpl. set (u := Fun f v). unfold is_sol_eqn. simpl fst. simpl snd.
simpl sub at 2. case_eq (mem n (vars u)). intuition; try contradiction.
symmetry in H0. ded (wf_term_var H0 H). discriminate.
unfold is_sol, is_sol_solved_eqns.
simpl lforall. unfold is_sol_solved_eqn at 2. simpl fst. simpl snd. intuition.
rewrite lforall_is_sol_solved_eqn; auto. rewrite is_sol_eqns_map; auto.
rewrite lforall_is_sol_solved_eqn in H3; hyp.
rewrite is_sol_eqns_map in H2; hyp.
(* fun-fun *)
simpl. unfold is_sol_eqn. unfold fst, snd. repeat rewrite sub_fun.
case_beq_symb f f0. simpl. unfold is_sol_eqns at 2. rewrite lforall_app.
rewrite lforall_is_sol_eqn_combine. intuition. Funeqtac. hyp.
apply args_eq. hyp. intuition; try contradiction. Funeqtac.
rewrite (beq_refl (@beq_symb_ok Sig)) in H. discriminate. Transparent vars.
Qed.

Lemma iter_step_correct : forall s p k,
  is_sol s p <-> is_sol s (iter_step k p).

Proof.
induction k; simpl. intuition. rewrite <- step_correct. hyp.
Qed.

(***********************************************************************)
(** extension of a substitution *)

Lemma is_sol_solved_eqns_extend : forall s n v l,
  lforall (notin_solved_eqn n) l ->
  is_sol_solved_eqns s l -> is_sol_solved_eqns (extend s n v) l.

Proof.
induction l; simpl. auto. destruct a.
unfold notin_solved_eqn at 1, is_sol_solved_eqn. simpl. intuition.
unfold extend at 1. case_beq_nat n0 n. change (n0<>n0) in H0. irrefl.
rewrite H. symmetry. apply sub_extend_notin. rewrite in_vars_mem.
rewrite H4. discr.
Qed.

Lemma is_sol_eqn_extend : forall s x (v : term) e,
   is_sol_eqn s (eqn_sub (single x v) e) <->
   is_sol_eqn (extend s x (sub s v)) e.

Proof.
destruct e. unfold is_sol_eqn. simpl. repeat rewrite sub_sub.
repeat rewrite sub_comp_single_extend. tauto.
Qed.

Lemma is_sol_eqns_extend : forall s x (v : term) l,
   is_sol_eqns s (map (eqn_sub (single x v)) l) <->
   is_sol_eqns (extend s x (sub s v)) l.

Proof.
induction l; simpl; intuition.
clear H H1 H3. gen H2. unfold is_sol_eqn. simpl. repeat rewrite sub_sub.
repeat rewrite sub_comp_single_extend. auto.
clear H3 H0 H1. gen H2. unfold is_sol_eqn. simpl. repeat rewrite sub_sub.
repeat rewrite sub_comp_single_extend. auto.
Qed.

(***********************************************************************)
(** substitution corresponding to solved equations *)

Fixpoint subst_of_solved_eqns (l : solved_eqns) :=
  match l with
    | (x, v) :: l' => extend (subst_of_solved_eqns l') x v
    | nil => id Sig
  end.

Fixpoint dom (l : solved_eqns) :=
  match l with
    | (x, _) :: l' => add x (dom l')
    | nil => empty
  end.

Lemma dom_subst_of_solved_eqns : forall x l,
  mem x (dom l) = false -> subst_of_solved_eqns l x = Var x.

Proof.
induction l; simpl. mem. refl. destruct a.
mem. intro. destruct (orb_false_elim H). unfold extend.
rewrite (beq_com beq_nat_ok) in H0. rewrite H0. auto.
Qed.

Implicit Arguments dom_subst_of_solved_eqns [x l].

Lemma lforall_notin_vars_solved_eqn_dom : forall x u l,
  lforall (notin_vars_solved_eqn u) l ->
  mem x (vars u) = true -> mem x (dom l) = false.

Proof.
induction l; simpl. mem. refl. destruct a.
unfold notin_vars_solved_eqn at 1. simpl. mem. intuition.
case_beq_nat n x; simpl. rewrite H1 in H0. discriminate. hyp.
Qed.

Implicit Arguments lforall_notin_vars_solved_eqn_dom [x u l].

Lemma lforall_notin_vars_solved_eqn_mem : forall x u l,
  lforall (notin_vars_solved_eqn u) l ->
  mem x (dom l) = true -> mem x (vars u) = false.

Proof.
induction l. simpl. mem. intros. discriminate. destruct a. simpl. mem.
unfold notin_vars_solved_eqn at 1. simpl. intuition.
destruct (orb_true_elim H0). rewrite beq_nat_ok in e. subst n. hyp. auto.
Qed.

Implicit Arguments lforall_notin_vars_solved_eqn_mem [x u l].

Lemma sub_eq' : forall s1 s2 (t : term),
  (forall x, mem x (vars t) = true -> s1 x = s2 x) -> sub s1 t = sub s2 t.

Proof.
intros. apply sub_eq. intro. rewrite in_vars_mem. auto.
Qed.

Lemma sub_eq_id' : forall s (t : term),
  (forall x, mem x (vars t) = true -> s x = Var x) -> sub s t = t.

Proof.
intros. apply sub_eq_id. intro. rewrite in_vars_mem. auto.
Qed.

Lemma lforall_notin_solved_eqn_mem : forall n x l,
  lforall (notin_solved_eqn n) l -> beq_nat x n = false ->
  mem n (vars (subst_of_solved_eqns l x)) = false.

Proof.
induction l. simpl. mem. auto. simpl. destruct a. unfold notin_solved_eqn at 1.
simpl. intuition. unfold extend. case_beq_nat x n0; hyp.
Qed.

Implicit Arguments lforall_notin_solved_eqn_mem [n x l].

Lemma subst_of_solved_eqns_correct : forall l, solved_eqns_wf l ->
  is_sol_solved_eqns (subst_of_solved_eqns l) l.

Proof.
induction l; simpl. auto. set (s := subst_of_solved_eqns l). destruct a.
unfold is_sol_solved_eqn. simpl. intuition. unfold extend at 1. simpl.
rewrite (beq_refl beq_nat_ok). rewrite sub_extend_notin.
symmetry. apply sub_eq_id'. intros.
ded (lforall_notin_vars_solved_eqn_dom H3 H4).
ded (dom_subst_of_solved_eqns H5). hyp.
rewrite in_vars_mem. rewrite H0. discr.
apply is_sol_solved_eqns_extend; hyp.
Qed.

Lemma subst_of_solved_eqns_correct_problem : forall p l k, problem_wf p ->
  iter_step k p = Some (l, nil) -> is_sol (subst_of_solved_eqns l) p.

Proof.
intros. set (s := subst_of_solved_eqns l).
rewrite (@iter_step_correct s p k). rewrite H0. simpl. intuition. 
apply subst_of_solved_eqns_correct.
assert (problem_wf (Some (l, nil))). rewrite <- H0. apply iter_step_wf. hyp.
simpl in H1. intuition.
Qed.

Implicit Arguments subst_of_solved_eqns_correct_problem [p l k].

Lemma successfull_is_sol : forall k p, problem_wf p ->
  successfull (iter_step k p) = true -> exists s, is_sol s p.

Proof.
intros. destruct (successfull_elim H0). exists (subst_of_solved_eqns x).
eapply subst_of_solved_eqns_correct_problem. hyp. apply H1.
Qed.

(***********************************************************************)
(** most generality *)

Definition theta l (s : substitution) y :=
  if mem y (dom l) then Var y else s y.

Lemma subst_of_solved_eqns_most_general :
  forall s l, solved_eqns_wf l -> is_sol_solved_eqns s l ->
    forall x, s x = sub (theta l s) (subst_of_solved_eqns l x).

Proof.
induction l. refl. destruct a. unfold is_sol_solved_eqns. simpl.
unfold is_sol_solved_eqn at 1. simpl. intuition. unfold extend.
case_beq_nat x n. rewrite H. apply sub_eq'. intros. unfold theta. simpl. mem.
case_beq_nat x x0; simpl. rewrite H1 in H4. discriminate.
case_eq (mem x0 (dom l)). ded (lforall_notin_vars_solved_eqn_mem H5 H8).
rewrite H4 in H9. discriminate. refl. rewrite H6. apply sub_eq'. intros.
unfold theta. simpl. mem. case_beq_nat n x0. simpl.
ded (lforall_notin_solved_eqn_mem H0 H4). rewrite H7 in H8. discriminate.
simpl. refl.
Qed.

Lemma iter_step_None :
  forall p k, iter_step k p = None -> forall s, ~is_sol s p.

Proof.
intros. intro. rewrite (iter_step_correct s p k) in H0.
rewrite H in H0. hyp.
Qed.

Lemma iter_step_solved_eqn_wf : forall p l k, problem_wf p ->
  iter_step k p = Some (l, nil) -> solved_eqns_wf l.

Proof.
intros. ded (iter_step_wf p k H). rewrite H0 in H1. simpl in H1. intuition.
Qed.

Lemma iter_step_Some : forall p l k, problem_wf p ->
  iter_step k p = Some (l, nil) -> is_sol (subst_of_solved_eqns l) p.

Proof.
intros. rewrite (iter_step_correct (subst_of_solved_eqns l) p k).
rewrite H0. simpl. intuition. apply subst_of_solved_eqns_correct.
eapply iter_step_solved_eqn_wf; eassumption.
Qed.

Implicit Arguments iter_step_Some [p l k].

Lemma iter_step_most_general : forall p l k, problem_wf p ->
  iter_step k p = Some (l, nil) -> forall s, is_sol s p ->
    forall x, s x = sub (theta l s) (subst_of_solved_eqns l x).

Proof.
intros. apply subst_of_solved_eqns_most_general.
eapply iter_step_solved_eqn_wf; eassumption.
cut (is_sol s (Some (l, nil))). simpl. intuition.
rewrite <- H0. rewrite <- iter_step_correct. hyp.
Qed.

Lemma iter_step_complete : forall p, problem_wf p ->
  (exists s, is_sol s p) -> exists k, successfull (iter_step k p) = true.

Proof.
intros. destruct H0 as [s]. destruct (wf_iter_step p) as [k]. exists k.
rewrite (iter_step_correct s p k) in H0. destruct (iter_step k p).
destruct p0. destruct e. refl. discr. contradiction.
Qed.

Lemma iter_step_complete2 : forall p, problem_wf p ->
  (forall s, ~is_sol s p) -> exists k, iter_step k p = None.

Proof.
intros. destruct (wf_iter_step p) as [k]. exists k.
case_eq (iter_step k p). 2: refl. rewrite H2 in H1. destruct p0. destruct e.
ded (iter_step_Some H H2). ded (H0 (subst_of_solved_eqns s)). contradiction.
discr.
Qed.

(***********************************************************************)
(** unifiability of two terms *)

Definition mk_problem u v : problem := Some (nil, (u,v)::nil).

Lemma wf_mk_problem : forall u v, problem_wf (mk_problem u v).

Proof.
unfold mk_problem. simpl. auto.
Qed.

Definition unifiable u v := exists s, is_sol s (mk_problem u v).

Notation In := List.In.
Notation In_dec := (List.In_dec eq_nat_dec).
Notation vars := (@ATerm.vars Sig).

Lemma sub_eq_is_sol : forall s1 t1 s2 t2,
  (forall x, In x (vars t1) -> In x (vars t2) -> False) ->
  sub s1 t1 = sub s2 t2 -> unifiable t1 t2.

Proof.
intros. set (s := fun x => match In_dec x (vars t1) with
  | left _ => s1 x | right _ => s2 x end). exists s.
unfold is_sol, mk_problem. simpl. intuition. unfold is_sol_eqn. simpl.
transitivity (sub s1 t1). apply sub_eq. intros. unfold s.
case (In_dec x (vars t1)). refl. contradiction.
rewrite H0. apply sub_eq. intros. unfold s. case (In_dec x (vars t1)).
intro. apply False_rec. exact (H x i H1). refl.
Qed.

End S.

Implicit Arguments iter_step_complete [Sig p].
Implicit Arguments successfull_elim [Sig k p].
Implicit Arguments successfull_preserved [Sig k p l].
Implicit Arguments unsuccessfull_preserved [Sig k p l].
Implicit Arguments successfull_inv [Sig k p l].
Implicit Arguments successfull_is_sol [Sig k p].
