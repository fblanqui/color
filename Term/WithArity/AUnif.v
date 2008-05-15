(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2008-01-22

syntactic unification
*)

(* $Id: AUnif.v,v 1.1 2008-05-15 14:58:04 blanqui Exp $ *)

Set Implicit Arguments.

Require Export ASubstitution.

Section S.

Variable Sig : Signature.

Notation term := (term Sig).
Notation terms := (vector term).
Notation substitution := (substitution Sig).

Ltac case_symb_eq f g := case_beq (@beq_symb_ok Sig) (@beq_symb Sig f g).

(***********************************************************************)
(* equations *)

Notation eqn := ((term * term)%type).
Notation eqns := (list eqn).

Definition eqn_app s (e : eqn) := (app s (fst e), app s (snd e)).

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
  [=] union (vars_terms vs) (vars_terms us).

Proof.
induction us; simpl; intros. VOtac. simpl. symmetry. apply union_empty_left.
VSntac vs. clear H. set (x := Vhead vs). set (ts := Vtail vs). simpl.
unfold vars_eqn. simpl.
transitivity (union (union (vars x) (vars a)) (union (vars_terms ts) (vars_terms us))). apply union_m. refl. apply IHus. Equal; union.
Qed.

Lemma vars_eqn_subs : forall x v e,
  vars_eqn (eqn_app (single x v) e) [=]
  if mem x (vars_eqn e) then union (vars v) (remove x (vars_eqn e))
    else vars_eqn e.

Proof.
intros. destruct e as [l r]. unfold vars_eqn, eqn_app. simpl.
(*FIXME*)transitivity (union (if mem x (vars l) then union (vars v) (remove x (vars l)) else vars l) (if mem x (vars r) then union (vars v) (remove x (vars r)) else vars r)). apply union_m; apply vars_subs. autorewrite with mem.
case_eq (mem x (vars l)); case_eq (mem x (vars r)); autorewrite with bool.
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
  vars_eqns (map (eqn_app (single x v)) l) [=]
  if mem x (vars_eqns l) then union (vars v) (remove x (vars_eqns l))
    else vars_eqns l.

Proof.
induction l; simpl; intros. refl. autorewrite with mem.
(*FIXME*)transitivity (union (if mem x (vars_eqn a) then union (vars v) (remove x (vars_eqn a)) else vars_eqn a) (if mem x (vars_eqns l)
          then union (vars v) (remove x (vars_eqns l))
          else vars_eqns l)). apply union_m. apply vars_eqn_subs. exact IHl.
case_eq (mem x (vars_eqn a)); case_eq (mem x (vars_eqns l));
  autorewrite with bool.
transitivity (union (vars v) (union (remove x (vars_eqn a)) (remove x (vars_eqns l)))). apply union_idem_3. apply union_m. refl. symmetry. apply remove_union.
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

Notation solved_eqn := ((variable * term)%type).
Notation solved_eqns := (list solved_eqn).
Notation problem := (option ((solved_eqns * eqns)%type)).

Definition notin_eqn x (e : eqn) :=
  mem x (vars (fst e)) = false /\ mem x (vars (snd e)) = false.

Definition notin_solved_eqn x (e : solved_eqn) :=
  x <> fst e /\ mem x (vars (snd e)) = false.

Fixpoint solved_eqns_wf (l : solved_eqns) :=
  match l with
    | nil => True
    | (x, v) :: l' => mem x (vars v) = false
      /\ lforall (notin_solved_eqn x) l' /\ solved_eqns_wf l'
  end.

Definition notin l2 (e : solved_eqn) := lforall (notin_eqn (fst e)) l2.
 
Definition problem_wf (p : problem) :=
  match p with
    | Some (l1, l2) => solved_eqns_wf l1 /\ lforall (notin l2) l1
    | _ => True
  end.

Definition solved_eqn_app s (e : solved_eqn) := (fst e, app s (snd e)).

(***********************************************************************)
(** properties of well-formed problems *)

Lemma lforall_notin_solved_eqn_1 : forall n t, mem n (vars t) = false ->
  forall l' l, lforall (notin ((t, Var n) :: l')) l -> 
    lforall (notin_solved_eqn n) (map (solved_eqn_app (single n t)) l).

Proof.
induction l; simpl. auto. destruct a. simpl. unfold notin_eqn. simpl.
autorewrite with mem. intros. unfold notin_solved_eqn. simpl. intuition.
subst n0. rewrite (beq_refl beq_nat_ok) in H4. discriminate.
transitivity (mem n (if mem n (vars t1) then union (vars t0) (remove n (vars t1)) else vars t1)). apply mem_m. refl. apply vars_subs.
case_eq (mem n (vars t1)). autorewrite with mem bool. hyp. hyp.
Qed.

Lemma lforall_notin_solved_eqn_1' : forall n t, mem n (vars t) = false ->
  forall l' l, lforall (notin ((Var n, t) :: l')) l -> 
    lforall (notin_solved_eqn n) (map (solved_eqn_app (single n t)) l).

Proof.
induction l; simpl. auto. destruct a. simpl. unfold notin_eqn. simpl.
autorewrite with mem. intros. unfold notin_solved_eqn. simpl. intuition.
subst n0. rewrite (beq_refl beq_nat_ok) in H1. discriminate.
transitivity (mem n (if mem n (vars t1) then union (vars t0) (remove n (vars t1)) else vars t1)). apply mem_m. refl. apply vars_subs.
case_eq (mem n (vars t1)). autorewrite with mem bool. hyp. hyp.
Qed.

Lemma lforall_notin_solved_eqn_2 : forall n t, mem n (vars t) = false ->
  forall x, beq_nat x n = false ->
    forall l, lforall (notin_solved_eqn n) l -> 
      lforall (notin_solved_eqn n) (map (solved_eqn_app (single x t)) l).

Proof.
induction l; simpl. auto. destruct a. intuition. unfold notin_solved_eqn in H2.
simpl in H2. unfold notin_solved_eqn. simpl. intuition.
transitivity (mem n (if mem x (vars t1) then union (vars t0) (remove x (vars t1)) else vars t1)). apply mem_m. refl. apply vars_subs.
case_eq (mem x (vars t1)). autorewrite with mem. rewrite H0. rewrite H5.
rewrite H. refl. hyp.
Qed.

Lemma solved_eqns_wf_map : forall n t, mem n (vars t) = false ->
  forall l' l, solved_eqns_wf l -> lforall (notin ((Var n, t) :: l')) l ->
    solved_eqns_wf (map (solved_eqn_app (single n t)) l).

Proof.
induction l; simpl. auto. destruct a. simpl. unfold notin_eqn. simpl.
autorewrite with mem. intuition.
transitivity (mem n0 (if mem n (vars t1) then union (vars t0) (remove n (vars t1)) else vars t1)). apply mem_m. refl. apply vars_subs.
case_eq (mem n (vars t1)). autorewrite with mem. rewrite H7. rewrite H2.
rewrite H0. refl. hyp. apply lforall_notin_solved_eqn_2; hyp.
Qed.

Lemma solved_eqns_wf_map' : forall n t, mem n (vars t) = false ->
  forall l' l, solved_eqns_wf l -> lforall (notin ((t, Var n) :: l')) l ->
    solved_eqns_wf (map (solved_eqn_app (single n t)) l).

Proof.
induction l; simpl. auto. destruct a. simpl. unfold notin_eqn. simpl.
autorewrite with mem. intuition.
transitivity (mem n0 (if mem n (vars t1) then union (vars t0) (remove n (vars t1)) else vars t1)). apply mem_m. refl. apply vars_subs.
case_eq (mem n (vars t1)). autorewrite with mem. rewrite H7. rewrite H2.
rewrite H0. refl. hyp. apply lforall_notin_solved_eqn_2; hyp.
Qed.

Lemma notin_map : forall x t, mem x (vars t) = false ->
  forall l, notin (map (eqn_app (single x t)) l) (x, t).

Proof.
induction l; simpl. trivial. destruct a. unfold notin_eqn. simpl. intuition.
transitivity (mem x (if mem x (vars t1) then union (vars t0) (remove x (vars t1)) else vars t1)). apply mem_m. refl. apply vars_subs.
case_eq (mem x (vars t1)). autorewrite with mem. rewrite H. rewrite H0.
refl. hyp.
transitivity (mem x (if mem x (vars t2) then union (vars t0) (remove x (vars t2)) else vars t2)). apply mem_m. refl. apply vars_subs.
case_eq (mem x (vars t2)). autorewrite with mem. rewrite H. rewrite H0.
refl. hyp.
Qed.

Lemma lforall_notin_eqn : forall x t, mem x (vars t) = false ->
  forall n, beq_nat n x = false ->
    forall l, lforall (notin_eqn x) l ->
      lforall (notin_eqn x) (map (eqn_app (single n t)) l).

Proof.
induction l; simpl; intuition. destruct a. unfold eqn_app. simpl.
unfold notin_eqn. simpl. unfold notin_eqn in H2. simpl in H2. intuition.
transitivity (mem x (if mem n (vars t1) then union (vars t0) (remove n (vars t1)) else vars t1)). apply mem_m. refl. apply vars_subs.
case_eq (mem n (vars t1)). autorewrite with mem. rewrite H. rewrite H0.
rewrite H4. refl. hyp.
transitivity (mem x (if mem n (vars t2) then union (vars t0) (remove n (vars t2)) else vars t2)). apply mem_m. refl. apply vars_subs.
case_eq (mem n (vars t2)). autorewrite with mem. rewrite H. rewrite H0.
rewrite H5. refl. hyp.
Qed.

Lemma lforall_notin : forall x t l' l,
  lforall (notin ((t, Var x) :: l')) l ->
  lforall (notin (map (eqn_app (single x t)) l'))
  (map (solved_eqn_app (single x t)) l).

Proof.
induction l; simpl. auto. destruct a. simpl. unfold notin_eqn. simpl.
autorewrite with mem. intuition. unfold notin. simpl.
unfold notin in H2. simpl in H2. apply lforall_notin_eqn; hyp.
Qed.

Lemma lforall_notin' : forall x t l' l,
  lforall (notin ((Var x, t) :: l')) l ->
  lforall (notin (map (eqn_app (single x t)) l'))
  (map (solved_eqn_app (single x t)) l).

Proof.
induction l; simpl. auto. destruct a. simpl. unfold notin_eqn. simpl.
autorewrite with mem. intuition. unfold notin. simpl.
unfold notin in H2. simpl in H2. apply lforall_notin_eqn; hyp.
Qed.

Lemma lforall_notin_eqn_combine : forall x n (v1 v2 : terms n),
  mem x (vars_terms v1) = false -> mem x (vars_terms v2) = false ->
  lforall (notin_eqn x) (combine (list_of_vec v1) (list_of_vec v2)).

Proof.
induction v1; simpl; intros. trivial. VSntac v2. simpl.
autorewrite with mem in H. destruct (orb_false_elim H).
assert (mem x (vars (Vhead v2)) = false
  /\ mem x (vars_terms (Vtail v2)) = false). rewrite H1 in H0. simpl in H0.
autorewrite with mem in H0. destruct (orb_false_elim H0). intuition.
intuition. unfold notin_eqn. simpl. intuition.
Qed.

(***********************************************************************)
(** step function *)

Notation beq_symb := (@beq_symb Sig).
Notation beq_symb_ok := (@beq_symb_ok Sig).

Definition step (p : problem) :=
  match p with
    | Some (l1, e :: l2) =>
      match e with
        | (v, Var x) | (Var x, v) =>
          if beq_term v (Var x) then Some (l1, l2)
            else if mem x (vars v) then None
              else Some ((x, v) :: List.map (solved_eqn_app (single x v)) l1,
              List.map (eqn_app (single x v)) l2)
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
    | S k' => iter_step k' (step p)
  end.

(***********************************************************************)
(** the step function preserves well-formedness *)

Lemma step_wf : forall p, problem_wf p -> problem_wf (step p).

Proof.
intro. destruct p. 2: auto. destruct p. destruct l0. auto. destruct p.
destruct t0; destruct t1.
(* var-var *)
simpl. autorewrite with mem. case_nat_eq n n0; simpl.
intuition. gen H1. elim l; simpl; intuition.
autorewrite with mem. rewrite H. intuition.
eapply lforall_notin_solved_eqn_1. simpl. autorewrite with mem. hyp.
apply H2.
eapply solved_eqns_wf_map'. simpl. autorewrite with mem. hyp.
hyp. apply H2.
apply notin_map. simpl. autorewrite with mem. hyp.
apply lforall_notin. hyp.
(* var-fun *)
Opaque vars. simpl. rewrite vars_fun. intuition.
case_eq (mem n (vars_terms v)). simpl. trivial.
simpl. rewrite vars_fun. intuition.
eapply lforall_notin_solved_eqn_1'. rewrite vars_fun. hyp. apply H1.
eapply solved_eqns_wf_map. rewrite vars_fun. hyp. hyp. apply H1.
apply notin_map. rewrite vars_fun. hyp.
apply lforall_notin'. hyp.
(* fun-var *)
simpl. rewrite vars_fun. intuition.
case_eq (mem n (vars_terms v)). simpl. trivial.
simpl. rewrite vars_fun. intuition.
eapply lforall_notin_solved_eqn_1. rewrite vars_fun. hyp. apply H1.
eapply solved_eqns_wf_map'. rewrite vars_fun. hyp. hyp. apply H1.
apply notin_map. rewrite vars_fun. hyp.
apply lforall_notin. hyp.
(* fun-fun *)
simpl. case_symb_eq f f0; simpl; intuition.
gen H1. elim l; simpl; intuition. gen H1. unfold notin_eqn. simpl.
do 2 rewrite vars_fun. gen H4. unfold notin. simpl. rewrite lforall_app.
intuition. apply lforall_notin_eqn_combine; hyp. Transparent vars.
Qed.

(***********************************************************************)
(** solutions of an unification problem *)

Definition is_sol_eqn s (e : eqn) := app s (fst e) = app s (snd e).
Definition is_sol_solved_eqn s (e : solved_eqn) := s (fst e) = app s (snd e).

Definition is_sol_eqns s := lforall (is_sol_eqn s).
Definition is_sol_solved_eqns s := lforall (is_sol_solved_eqn s).

Definition is_sol s p :=
  match p with
    | None => False
    | Some (l1, l2) => is_sol_solved_eqns s l1 /\ is_sol_eqns s l2
  end.

(***********************************************************************)
(** the step function preserves solutions *)

Lemma is_sol_solved_eqns_map : forall s n u, s n = app s u ->
  forall l, is_sol_solved_eqns s (map (solved_eqn_app (single n u)) l)
    <-> is_sol_solved_eqns s l.

Proof.
induction l; simpl. intuition. destruct a. unfold is_sol_solved_eqn. simpl.
intuition. rewrite H3. rewrite app_app. apply app_eq. intros.
unfold comp, single. case_nat_eq n x; auto.
rewrite H3. rewrite app_app. apply app_eq. intros.
unfold comp, single. case_nat_eq n x; auto.
Qed.

Lemma app_comp_single : forall s x u, s x = app s u ->
  forall t : term, app (comp s (single x u)) t = app s t.

Proof.
intros. set (s' := comp s (single x u)). pattern t0.
apply term_ind with (Q := fun n (ts : terms n) =>
  Vmap (app s') ts = Vmap (app s) ts); clear t0.
intro. unfold s', comp, single. simpl. case_nat_eq x x0; auto.
intros f v IH. repeat rewrite app_fun. apply (f_equal (Fun f)). hyp.
refl. intros. simpl. apply Vcons_eq; hyp.
Qed.

Lemma is_sol_eqns_map : forall s x u, s x = app s u ->
  forall l, is_sol_eqns s (map (eqn_app (single x u)) l) <-> is_sol_eqns s l.

Proof.
induction l; simpl. intuition. destruct a. unfold is_sol_eqn. simpl.
intuition. do 2 rewrite app_app in H3.
transitivity (app (comp s (single x u)) t0). symmetry. apply app_comp_single.
hyp. rewrite H3. apply app_comp_single. hyp.
do 2 rewrite app_app. transitivity (app s t0). apply app_comp_single. hyp.
rewrite H3. symmetry. apply app_comp_single. hyp.
Qed.

Lemma lforall_is_sol_solved_eqn : forall s x u, s x = app s u -> forall l,
  lforall (is_sol_solved_eqn s) (map (solved_eqn_app (single x u)) l)
  <-> lforall (is_sol_solved_eqn s) l.

Proof.
induction l; simpl. intuition. destruct a. intuition.
gen H3. unfold is_sol_solved_eqn, solved_eqn_app. simpl. rewrite app_app.
intro. rewrite H3. apply app_comp_single. hyp.
gen H3. unfold is_sol_solved_eqn, solved_eqn_app. simpl. rewrite app_app.
intro. rewrite H3. symmetry. apply app_comp_single. hyp.
Qed.

Lemma lforall_is_sol_eqn_combine : forall s n (v v0 : terms n),
  lforall (is_sol_eqn s) (combine (list_of_vec v) (list_of_vec v0))
  <-> Vmap (app s) v = Vmap (app s) v0.

Proof.
induction v; simpl; intros. VOtac. simpl. intuition. VSntac v0. simpl.
unfold is_sol_eqn at 1. simpl. rewrite IHv. intuition. rewrite H1. rewrite H2.
refl. Veqtac. hyp. Veqtac. hyp.
Qed.

Lemma step_correct_complete : forall s p, is_sol s p <-> is_sol s (step p).

Proof.
intros s p. destruct p. 2: simpl; intuition. destruct p. destruct l0.
simpl. intuition. destruct p. destruct t0; destruct t1.
(* var-var *)
simpl. unfold is_sol_eqn. autorewrite with mem. simpl.
case_nat_eq n n0; simpl. intuition. unfold is_sol_solved_eqn. simpl. intuition.
rewrite is_sol_solved_eqns_map; auto. rewrite is_sol_eqns_map; auto.
rewrite is_sol_solved_eqns_map in H3; auto. rewrite is_sol_eqns_map in H2; auto.
(* var-fun *)
Opaque vars. simpl. set (u := Fun f v). unfold is_sol_eqn. simpl fst. simpl snd.
simpl app at 1. case_eq (mem n (vars u)). intuition; try contradiction.
ded (term_wf H0 H). discriminate. unfold is_sol, is_sol_solved_eqns.
simpl lforall. unfold is_sol_solved_eqn at 2. simpl fst. simpl snd. intuition.
rewrite lforall_is_sol_solved_eqn; auto. rewrite is_sol_eqns_map; auto.
rewrite lforall_is_sol_solved_eqn in H3; hyp.
rewrite is_sol_eqns_map in H2; hyp.
(* fun-var *) (* same proof *)
simpl. set (u := Fun f v). unfold is_sol_eqn. simpl fst. simpl snd.
simpl app at 2. case_eq (mem n (vars u)). intuition; try contradiction.
symmetry in H0. ded (term_wf H0 H). discriminate.
unfold is_sol, is_sol_solved_eqns.
simpl lforall. unfold is_sol_solved_eqn at 2. simpl fst. simpl snd. intuition.
rewrite lforall_is_sol_solved_eqn; auto. rewrite is_sol_eqns_map; auto.
rewrite lforall_is_sol_solved_eqn in H3; hyp.
rewrite is_sol_eqns_map in H2; hyp.
(* fun-fun *)
simpl. unfold is_sol_eqn. simpl fst. simpl snd. repeat rewrite app_fun.
case_symb_eq f f0. simpl. unfold is_sol_eqns at 2. rewrite lforall_app.
rewrite lforall_is_sol_eqn_combine. intuition. Funeqtac. hyp.
apply args_eq. hyp. intuition; try contradiction. Funeqtac.
rewrite (beq_refl beq_symb_ok) in H. discriminate. Transparent vars.
Qed.

(***********************************************************************)
(** substitution corresponding to solved equations *)

Definition extend (s : substitution) x (v : term) : substitution :=
  fun y => if beq_nat x y then v else s y.

Fixpoint subst_of_solved_eqns (l : solved_eqns) :=
  match l with
    | (x, v) :: l' => extend (subst_of_solved_eqns l') x v
    | nil => @id Sig
  end.

End S.
