(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2004-12-22

cap of undefined symbols and aliens of defined symbols
*)

Set Implicit Arguments.

From Coq Require Import Sumbool.
From CoLoR Require Import LogicUtil ACalls ATrs VecUtil ListUtil NatUtil EqUtil.

Section S.

Variable Sig : Signature.

Notation term := (term Sig). Notation terms := (vector term).

(***********************************************************************)
(** we first defined a generic cap as a triple (k,f,v) where
- k is the number of aliens
- f is a function which, given a vector v of k terms, returns the cap
with the ith alien replaced by the ith term of v
- v is the vector of the k aliens

the generic cap of a term is computed by the function capa below
its property is: if capa(t) = (k,f,v) then f(v)=t

f acts as an abstract context with k holes *)

Local Open Scope type_scope.
Definition Cap := {k : nat & (terms k -> term) * terms k }.

Notation Caps := (vector Cap).

Definition mkCap := @existT nat (fun k => ((terms k -> term) * terms k)).

Definition fcap (c : Cap) := fst (projT2 c).
Definition aliens (c : Cap) := snd (projT2 c).
Definition fcap_aliens (c : Cap) := fcap c (aliens c).

(* total number of aliens of a vector of caps *)

Local Open Scope nat_scope.

Fixpoint sum n (cs : Caps n) : nat :=
  match cs with
    | Vnil => 0
    | Vcons c cs' => projT1 c + sum cs'
  end.

(* concatenation of all the aliens of a vector of caps *)

Fixpoint conc n (cs : Caps n) : terms (sum cs) :=
  match cs as cs return terms (sum cs) with
    | Vnil => Vnil
    | Vcons c cs' => Vapp (aliens c) (conc cs')
  end.

Lemma in_conc : forall u n (cs : Caps n), Vin u (conc cs) ->
  exists c, Vin c cs /\ Vin u (aliens c).

Proof.
induction cs; simpl; intros. contr.
assert (Vin u (aliens h) \/ Vin u (conc cs)). apply Vin_app. hyp.
destruct H0. exists h. auto.
assert (exists c, Vin c cs /\ Vin u (aliens c)). apply IHcs. hyp.
destruct H1 as [c]. exists c. intuition.
Qed.

Arguments in_conc [u n cs] _.

(* given a vector cs of caps and a vector ts of (sum cs) terms, this
function breaks ts in vectors of size the number of aliens of every
cap of cs, apply every fcap to the corresponding vector, and
concatenate all the results *)

Fixpoint Vmap_sum n (cs : Caps n) : terms (sum cs) -> terms n :=
  match cs as cs in vector _ n return terms (sum cs) -> terms n with
    | Vnil => fun _ => Vnil
    | Vcons c cs' => fun ts =>
      let (hd,tl) := Vbreak ts in Vcons (fcap c hd) (Vmap_sum cs' tl)
  end.

(***********************************************************************)
(** function computing the generic cap of a term *)

Notation rule := (@rule Sig). Notation rules := (list rule).

Variable R : rules.

Fixpoint capa (t : term) : Cap :=
  match t with
    | Var x => mkCap (fun _ => t, Vnil)
    | Fun f ts =>
      if defined f R then
	mkCap (fun v => Vnth v (Nat.lt_0_succ 0), Vcons t Vnil)
      else
	let cs := Vmap capa ts in
	mkCap (fun v => Fun f (Vmap_sum cs v), conc cs)
  end.

(* number of aliens of a term *)

Definition nb_aliens t := projT1 (capa t).

(* proof of the capa property: if c = capa t then fcap c (aliens c) = t *)

Lemma Vmap_sum_conc_forall : forall n (ts : terms n),
  (Vforall (fun t => fcap_aliens (capa t) = t) ts)
  -> Vmap_sum (Vmap capa ts) (conc (Vmap capa ts)) = ts.

Proof.
induction ts; simpl; intros. refl. destruct H. rewrite Vbreak_app.
unfold fcap_aliens in H. rewrite H. apply Vtail_eq. apply IHts. hyp.
Qed.

Lemma sub_capa : forall t, fcap_aliens (capa t) = t.

Proof.
intro. pattern t. apply term_ind_forall; intros. refl.
unfold fcap_aliens, fcap, aliens. simpl. case (defined f R); simpl. refl.
apply args_eq. change (Vmap_sum (Vmap capa v) (conc (Vmap capa v)) = v).
rewrite Vmap_sum_conc_forall. refl. hyp.
Qed.

Lemma Vmap_sum_conc : forall n (ts : terms n),
  Vmap_sum (Vmap capa ts) (conc (Vmap capa ts)) = ts.

Proof.
intros. apply Vmap_sum_conc_forall. apply Vforall_intro. intros.
apply sub_capa.
Qed.

(***********************************************************************)
(** aliens are subterms *)

Lemma in_aliens_subterm : forall u t,
  Vin u (aliens (capa t)) -> subterm_eq u t.

Proof.
intros u t. pattern t. apply term_ind_forall.
simpl. intros. contr.
intros f ts H. simpl. case (defined f R).
simpl. intro. destruct H0. subst u. refl. contr.
change (Vin u (conc (Vmap capa ts)) -> subterm_eq u (Fun f ts)). intro.
assert (exists c, Vin c (Vmap capa ts) /\ Vin u (aliens c)). apply in_conc.
hyp. destruct H1 as [c]. destruct H1.
assert (exists t, Vin t ts /\ c = capa t). apply Vin_map. hyp.
destruct H3 as [t']. destruct H3. subst c.
assert (Vin u (aliens (capa t')) -> subterm_eq u t').
pattern t'. eapply Vforall_in with (n := arity f). apply H. hyp.
apply subterm_strict. eapply subterm_trans_eq1 with (u := t').
apply H4. hyp. apply subterm_fun. hyp.
Qed.

(***********************************************************************)
(** concrete cap: it is obtained by applying fcap to a sequence of fresh
variables greater than the biggest variable in t *)

Notation maxvar := (@maxvar Sig). Notation fresh := (@fresh Sig).

Definition fresh_for (t : term) := fresh (S (maxvar t)).

Definition cap t :=
  match capa t with
    | @existT _ _ n (f,_) => f (fresh_for t n)
  end.

Lemma cap_eq : forall t,
  cap t = fcap (capa t) (fresh (S (maxvar t)) (nb_aliens t)).

Proof.
intro. unfold cap, fcap, fresh_for, nb_aliens. destruct (capa t). destruct p.
refl.
Qed.

(***********************************************************************)
(** variables of the cap *)

Lemma vars_fcap_fresh_inf : forall x t m, maxvar t <= m
  -> In x (vars (fcap (capa t) (fresh (S m) (nb_aliens t))))
  -> x <= m -> In x (vars t).

Proof.
intro. set (Q := fun n (ts : terms n) =>
  forall m, maxvars ts <= m ->
  In x (vars_vec (Vmap_sum (Vmap capa ts) (fresh (S m) (sum (Vmap capa ts)))))
  -> x <= m -> In x (vars_vec ts)).
intro. pattern t. apply term_ind with (Q := Q); clear t; intros.
(* var *)
hyp.
(* fun *)
rewrite vars_fun. unfold nb_aliens in H1. simpl in H1.
destruct (defined f R); simpl in H1. destruct H1.
absurd (x<=m); lia. contr. apply H with (m := m); hyp.
(* nil *)
unfold Q. simpl. intros. contr.
(* cons *)
unfold Q. simpl. set (m := max (maxvar t) (maxvars v)).
intros m0 H1.
rewrite fresh_plus, Vbreak_app. simpl. intros. ded (in_app_or H2).
destruct H4.
(* head *)
apply in_appl. apply H with (m := m0).
eapply le_max_elim_l. unfold m in H1. rewrite maxvars_cons in H1. apply H1.
unfold nb_aliens. hyp. hyp.
(* tail *)
apply in_appr. unfold Q in H0. apply H0 with (m := m0 + projT1 (capa t)).
assert (maxvars v <= m0). eapply le_max_elim_r. unfold m in H1.
rewrite maxvars_cons in H1. apply H1. lia. hyp. lia.
Qed.

Lemma vars_cap_inf : forall x t,
  In x (vars (cap t)) -> x <= maxvar t -> In x (vars t).

Proof.
intros. apply vars_fcap_fresh_inf with (m := maxvar t). apply Nat.le_refl.
rewrite cap_eq in H. hyp. hyp.
Qed.

Lemma vars_cap_sup : forall x t,
  In x (vars (cap t)) -> x > maxvar t -> In x (vars t) -> False.

Proof.
intros x t. pattern t. apply term_ind_forall; clear t; simpl; intros.
intuition. change (In x (vars_vec v)) in H2.
change (x > maxvars v) in H1.
ded (in_vars_vec_elim H2). destruct H3 as [t]. destruct H3.
ded (vars_max H4). ded (maxvar_in _ _ H5 H3). lia.
Qed.

Lemma vars_fcap_fresh : forall x t m, maxvar t <= m
  -> In x (vars (fcap (capa t) (fresh (S m) (nb_aliens t))))
  -> x <= m + nb_aliens t.

Proof.
intro. set (Q := fun n (ts : terms n) =>
  forall m, maxvars ts <= m ->
  In x (vars_vec (Vmap_sum (Vmap capa ts) (fresh (S m) (sum (Vmap capa ts)))))
  -> x <= m + sum (Vmap capa ts)).
intro. pattern t. apply term_ind with (Q := Q); clear t.
(* var *)
simpl. intros. destruct H0. subst x0. lia. contr.
(* fun *)
intros f ts H m H0. unfold nb_aliens. simpl.
case (defined f R); simpl; intros. destruct H1. lia. contr.
apply H; hyp.
(* nil *)
unfold Q. simpl. intros. contr.
(* cons *)
intros. unfold Q. simpl. intros m H1. rewrite fresh_plus, Vbreak_app.
simpl. intro. ded (in_app_or H2). destruct H3.
assert (x <= m + projT1 (capa t)). apply H. eapply le_max_elim_l.
rewrite maxvars_cons in H1. apply H1. hyp. lia.
rewrite Nat.add_assoc. apply H0. assert (maxvars v <= m).
eapply le_max_elim_r. rewrite maxvars_cons in H1. apply H1. lia. hyp.
Qed.

Lemma vars_cap : forall x t,
  In x (vars (cap t)) -> x <= maxvar t + nb_aliens t.

Proof.
intros. apply vars_fcap_fresh. apply Nat.le_refl. rewrite cap_eq in H. hyp.
Qed.

(***********************************************************************)
(** properties of the cap wrt calls *)

Notation calls := (calls R).
Definition vcalls := vcalls R.

Lemma calls_capa : forall t m,
  calls (fcap (capa t) (fresh m (nb_aliens t))) = nil.

Proof.
set (Q := fun n (ts : terms n) => forall m, vcalls (Vmap_sum (Vmap capa ts)
  (fresh m (sum (Vmap capa ts)))) = nil).
intro. pattern t. apply term_ind with (Q := Q); clear t; intros.
(* var *)
refl.
(* fun *)
unfold nb_aliens. simpl.
pattern (defined f R). apply bool_eq_ind; intros; simpl. refl.
rewrite H0. apply H.
(* nil *)
unfold Q. refl.
(* cons *)
unfold Q. simpl. intro. rewrite fresh_plus, Vbreak_app. simpl.
apply app_nil. apply H. apply H0.
Qed.

Lemma calls_cap t : calls (cap t) = nil.

Proof. rewrite cap_eq. apply calls_capa. Qed.

Lemma aliens_incl_calls : forall u t,
  Vin u (aliens (capa t)) -> In u (calls t).

Proof.
intros u t. pattern t. apply term_ind_forall; clear t. simpl. auto.
intros f ts H. rewrite calls_fun. simpl. case (defined f R); simpl.
intuition. unfold aliens. simpl. intro. ded (in_conc H0). do 2 destruct H1.
ded (Vin_map H1). do 2 destruct H3. subst x. ded (Vforall_in H H3).
eapply in_vcalls. apply H4. hyp. hyp.
Qed.

(***********************************************************************)
(** concrete alien substitution:
it gives t when applied to the concrete cap of t *)

Definition alien_sub t := fsub (maxvar t) (aliens (capa t)).

Lemma alien_sub_var : forall x, alien_sub (Var x) x = Var x.

Proof.
intro. unfold alien_sub, fsub. simpl. case (le_lt_dec x x). auto.
intro. absurd (x < x). apply Nat.lt_irrefl. hyp.
Qed.

Lemma app_fcap : forall m s, (forall x, x <= m -> s x = Var x)
  -> forall t, maxvar t <= m
  -> forall v, sub s (fcap (capa t) v) = fcap (capa t) (Vmap (sub s) v).

Proof.
intros until t. pattern t.
set (Q := fun n (ts : terms n) => maxvars ts <= m
  -> forall v, Vmap (sub s) (Vmap_sum (Vmap capa ts) v)
               = Vmap_sum (Vmap capa ts) (Vmap (sub s) v)).
apply term_ind with (Q := Q); clear t.
intros. unfold fcap. simpl. apply H. hyp.
intros f ts IH H0. simpl. unfold fcap.
case (defined f R); simpl; intros.
VSntac v. refl.
apply args_eq. apply IH. hyp.
unfold Q. auto.
intros. unfold Q. simpl. intros.
gen (Vbreak_eq_app v0). intro. rewrite H3, Vmap_app, !Vbreak_app. simpl.
rewrite maxvars_cons in H2. apply Vcons_eq_intro.
apply H0. eapply le_max_elim_l. apply H2.
apply H1. eapply le_max_elim_r. apply H2.
Qed.

Lemma Vmap_map_sum : forall m s, (forall x, x <= m -> s x = Var x)
  -> forall n (ts : terms n), maxvars ts <= m
  -> forall v, Vmap (sub s) (Vmap_sum (Vmap capa ts) v)
               = Vmap_sum (Vmap capa ts) (Vmap (sub s) v).

Proof.
induction ts; simpl; intros. refl.
gen (Vbreak_eq_app v). intro. rewrite H1, Vmap_app, !Vbreak_app. simpl.
rewrite maxvars_cons in H0. apply Vcons_eq_intro.
eapply app_fcap. apply H. eapply le_max_elim_l. apply H0.
apply IHts. eapply le_max_elim_r. apply H0.
Qed.

Lemma alien_sub_cap : forall t, sub (alien_sub t) (cap t) = t.

Proof.
intro. pattern t. apply term_ind_forall; intros.
(* var *)
simpl. apply alien_sub_var.
(* fun *)
unfold alien_sub, cap, fresh_for. set (m := maxvar (Fun f v)).
simpl. case (defined f R).
(* f defined *)
change (fsub m (Vcons (Fun f v) Vnil) (S m) = Fun f v).
apply fsub_cons. lia.
(* f undefined *)
set (cs := Vmap capa v).
change (let (n,p) := mkCap (fun ts => Fun f (Vmap_sum cs ts), conc cs) in
  let (f0,v0) := p in sub (fsub m v0) (f0 (fresh (S m) n)) = Fun f v).
set (s := mkCap (fun ts => Fun f (Vmap_sum cs ts), conc cs)).
assert (s = mkCap (fun ts => Fun f (Vmap_sum cs ts), conc cs)). refl.
destruct s. destruct p as [f0 v0]. injection H0. intros. subst x.
assert (v0 = conc cs).
apply (@inj_existT _ eq_nat_dec (fun x => terms x)). hyp.
assert (f0 = fun ts => Fun f (Vmap_sum cs ts)).
apply (@inj_existT _ eq_nat_dec (fun x => terms x -> term)). hyp.
subst f0. rewrite sub_fun. apply f_equal with (f := Fun f).
set (s := fsub m v0). set (v1 := fresh (S m) (sum cs)).
assert (Vmap (sub s) (Vmap_sum cs v1) = Vmap_sum cs (Vmap (sub s) v1)).
unfold cs. eapply Vmap_map_sum with (m := m).
unfold s. apply fsub_inf. apply Nat.le_refl. rewrite H4.
assert (Vmap (sub s) v1 = conc cs). unfold s, v1. rewrite H3, Vmap_fsub_fresh.
refl.
rewrite H5. unfold cs. apply Vmap_sum_conc.
Qed.

End S.

Arguments vars_cap_inf [Sig] _ [x t] _ _.
Arguments vars_cap_sup [Sig] _ [x t] _ _ _.
Arguments vars_cap [Sig] _ [x t] _.
