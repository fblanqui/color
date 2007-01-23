(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2004-12-22

cap of undefined symbols and aliens of defined symbols
*)

(* $Id: ACap.v,v 1.3 2007-01-23 16:42:56 blanqui Exp $ *)

Set Implicit Arguments.

Require Export LogicUtil.

Section S.

Require Export ASignature.

Variable Sig : Signature.

Require Export ATerm.

Notation term := (term Sig).
Notation terms := (vector term).

(***********************************************************************)
(** we first defined a generic cap as a triple (k,f,v) where
- k is the number of aliens
- f is a function which, given a vector v of k terms, returns the cap
with the ith alien replaced by the ith term of v
- v is the vector of the k aliens

the generic cap of a term is computed by the function capa below
its property is: if capa(t) = (k,f,v) then f(v)=t

f acts as an abstract context with k holes *)

Definition Cap := sigS (fun k => ((terms k -> term) * terms k)%type).

Notation Caps := (vector Cap).

Definition sigc := @existS nat (fun k => ((terms k -> term) * terms k)%type).

Definition fcap (c : Cap) := fst (projS2 c).
Definition aliens (c : Cap) := snd (projS2 c).
Definition fcap_aliens (c : Cap) := fcap c (aliens c).

(* total number of aliens of a vector of caps *)

Fixpoint sum n (cs : Caps n) {struct cs} : nat :=
  match cs with
    | Vnil => 0
    | Vcons c _ cs' => projS1 c + sum cs'
  end.

(* concatenation of all the aliens of a vector of caps *)

Fixpoint conc n (cs : Caps n) {struct cs} : terms (sum cs) :=
  match cs as cs return terms (sum cs) with
    | Vnil => Vnil
    | Vcons c _ cs' => Vapp (aliens c) (conc cs')
  end.

Lemma in_conc : forall u n (cs : Caps n), Vin u (conc cs) ->
  exists c, Vin c cs /\ Vin u (aliens c).

Proof.
induction cs; simpl; intros. contradiction.
assert (Vin u (aliens a) \/ Vin u (conc cs)). apply Vin_app. assumption.
destruct H0. exists a. auto.
assert (exists c, Vin c cs /\ Vin u (aliens c)). apply IHcs. assumption.
destruct H1 as [c]. exists c. intuition.
Qed.

Implicit Arguments in_conc [u n cs].

(* given a vector cs of caps and a vector ts of (sum cs) terms, this function
breaks ts in vectors of size the number of aliens of every cap of cs,
apply every fcap to the corresponding vector, and concatenate all the results *)

Fixpoint Vmap_sum n (cs : Caps n) {struct cs} : terms (sum cs) -> terms n :=
  match cs as cs in vector _ n return terms (sum cs) -> terms n with
    | Vnil => fun _ => Vnil
    | Vcons c _ cs' => fun ts =>
      let (hd,tl) := Vbreak ts in Vcons (fcap c hd) (Vmap_sum cs' tl)
  end.

(***********************************************************************)
(** function computing the generic cap of a term *)

Require Export ACalls.

Notation rule := (@rule Sig).
Notation rules := (list rule).

Variable R : rules.

Fixpoint capa (t : term) : Cap :=
  match t with
    | Var x => sigc (fun _ => t, Vnil)
    | Fun f ts =>
      let fix capas n (ts : terms n) {struct ts} : Caps n :=
	match ts in vector _ n return Caps n with
	  | Vnil => Vnil
	  | Vcons t n' ts' => Vcons (capa t) (capas n' ts')
	end
	in match defined f R with
	     | true => sigc (fun v => Vnth v (lt_O_Sn 0), Vcons t Vnil)
	     | false => let cs := capas (arity f) ts in
	       sigc (fun v => Fun f (Vmap_sum cs v), conc cs)
	   end
  end.

Lemma capa_fun : forall f ts, capa (Fun f ts) =
 match defined f R with
   | true => sigc (fun v => Vnth v (lt_O_Sn 0), Vcons (Fun f ts) Vnil)
   | false => let cs := Vmap capa ts in
     sigc (fun v => Fun f (Vmap_sum cs v), conc cs)
 end.

Proof.
intros. reflexivity.
Qed.

(* number of aliens of a term *)

Definition nb_aliens t := projS1 (capa t).

(* proof of the capa property: if c = capa t then fcap c (aliens c) = t *)

Lemma Vmap_sum_conc_forall : forall n (ts : terms n),
  (Vforall (fun t => fcap_aliens (capa t) = t) ts)
  -> Vmap_sum (Vmap capa ts) (conc (Vmap capa ts)) = ts.

Proof.
induction ts; simpl; intros. reflexivity. destruct H. rewrite Vbreak_app.
unfold fcap_aliens in H. rewrite H. apply Vcons_eq_tail. apply IHts. assumption.
Qed.

Lemma sub_capa : forall t, fcap_aliens (capa t) = t.

Proof.
intro. pattern t. apply term_ind_forall; intros. reflexivity.
unfold fcap_aliens, fcap, aliens. simpl. case (defined f R); simpl. refl.
apply f_equal with (f := Fun f).
change (Vmap_sum (Vmap capa v) (conc (Vmap capa v)) = v).
rewrite Vmap_sum_conc_forall. reflexivity. assumption.
Qed.

Lemma Vmap_sum_conc : forall n (ts : terms n),
  Vmap_sum (Vmap capa ts) (conc (Vmap capa ts)) = ts.

Proof.
intros. apply Vmap_sum_conc_forall. apply Vforall_intro_ext. apply sub_capa.
Qed.

(***********************************************************************)
(** aliens are subterms *)

Lemma in_aliens_subterm : forall u t, Vin u (aliens (capa t)) -> subterm_eq u t.

Proof.
intros u t. pattern t. apply term_ind_forall.
simpl. intros. contradiction.
intros f ts H. rewrite capa_fun. case (defined f R).
simpl. intro. destruct H0. subst u. apply subterm_eq_refl. contradiction.
change (Vin u (conc (Vmap capa ts)) -> subterm_eq u (Fun f ts)). intro.
assert (exists c, Vin c (Vmap capa ts) /\ Vin u (aliens c)). apply in_conc.
assumption. destruct H1 as [c]. destruct H1.
assert (exists t, Vin t ts /\ c = capa t). apply Vin_map. assumption.
destruct H3 as [t']. destruct H3. subst c.
assert (Vin u (aliens (capa t')) -> subterm_eq u t').
pattern t'. eapply Vforall_in with (n := arity f). apply H. assumption.
apply subterm_strict. eapply subterm_trans_eq1 with (u := t').
apply H4. assumption. apply subterm_fun. assumption.
Qed.

(***********************************************************************)
(** concrete cap: it is obtained by applying fcap to a sequence of fresh
variables greater than the biggest variable in t *)

Notation maxvar := (@maxvar Sig).
Notation fresh := (fresh Sig).

Definition fresh_for (t : term) := fresh (S (maxvar t)).

Definition cap t :=
  match capa t with
    | existS n (f,_) => f (fresh_for t n)
  end.

Lemma cap_eq : forall t,
  cap t = fcap (capa t) (fresh (S (maxvar t)) (nb_aliens t)).

Proof.
intro. unfold cap, fcap, fresh_for, nb_aliens. destruct (capa t). destruct p.
reflexivity.
Qed.

(***********************************************************************)
(** variables of the cap *)

Lemma vars_fcap_fresh_inf : forall x t m, maxvar t <= m
  -> In x (vars (fcap (capa t) (fresh (S m) (nb_aliens t))))
  -> x <= m -> In x (vars t).

Proof.
intro. set (Q := fun n (ts : terms n) => forall m, Vmax (Vmap maxvar ts) <= m
  -> In x (vars_vec (Vmap_sum (Vmap capa ts) (fresh (S m) (sum (Vmap capa ts)))))
  -> x <= m -> In x (vars_vec ts)).
intro. pattern t. apply term_ind with (Q := Q); clear t; intros.
(* var *)
assumption.
(* fun *)
rewrite vars_fun. unfold nb_aliens in H1. rewrite capa_fun in H1.
destruct (defined f R); simpl in H1. destruct H1.
absurd (x<=m); omega. contradiction. apply H with (m := m); assumption.
(* nil *)
unfold Q. simpl. intros. contradiction.
(* cons *)
unfold Q. simpl. set (m := max (maxvar t) (Vmax (Vmap maxvar v))). intros m0 H1.
rewrite Vbreak_fresh. rewrite Vbreak_app. simpl. intros. deduce (in_app_or H2).
destruct H4.
(* head *)
apply in_appl. apply H with (m := m0).
eapply intro_max_l. unfold m in H1. apply H1.
unfold nb_aliens. assumption. assumption.
(* tail *)
apply in_appr. unfold Q in H0. apply H0 with (m := m0 + projS1 (capa t)).
assert (Vmax (Vmap maxvar v) <= m0). eapply intro_max_r. unfold m in H1. apply H1.
omega. assumption. omega.
Qed.

Lemma vars_cap_inf : forall x t,
  In x (vars (cap t)) -> x <= maxvar t -> In x (vars t).

Proof.
intros. apply vars_fcap_fresh_inf with (m := maxvar t). apply le_refl.
rewrite cap_eq in H. assumption. assumption.
Qed.

Lemma vars_cap_sup : forall x t,
  In x (vars (cap t)) -> x > maxvar t -> In x (vars t) -> False.

Proof.
intros x t. pattern t. apply term_ind_forall; clear t; simpl; intros.
intuition. change (In x (vars_vec v)) in H2.
set (m := Vmax (Vmap maxvar v)). change (x > m) in H1.
deduce (in_vars_vec_elim H2). destruct H3 as [t]. destruct H3.
deduce (vars_max H4). deduce (maxvar_in _ _ H5 H3).
fold m in H6. absurd (x>m); omega.
Qed.

Lemma vars_fcap_fresh : forall x t m, maxvar t <= m
  -> In x (vars (fcap (capa t) (fresh (S m) (nb_aliens t))))
  -> x <= m + nb_aliens t.

Proof.
intro. set (Q := fun n (ts : terms n) => forall m, Vmax (Vmap maxvar ts) <= m
  -> In x (vars_vec (Vmap_sum (Vmap capa ts) (fresh (S m) (sum (Vmap capa ts)))))
  -> x <= m + sum (Vmap capa ts)).
intro. pattern t. apply term_ind with (Q := Q); clear t.
(* var *)
simpl. intros. destruct H0. subst x0. omega. contradiction.
(* fun *)
intros f ts H m H0. unfold nb_aliens. rewrite capa_fun.
case (defined f R); simpl; intros. destruct H1. omega. contradiction.
apply H; assumption.
(* nil *)
unfold Q. simpl. intros. contradiction.
(* cons *)
intros. unfold Q. simpl. intros m H1. rewrite Vbreak_fresh. rewrite Vbreak_app.
simpl. intro. deduce (in_app_or H2). destruct H3.
assert (x <= m + projS1 (capa t)). apply H. eapply intro_max_l. apply H1.
assumption. omega.
rewrite plus_assoc. apply H0. assert (Vmax (Vmap maxvar v) <= m).
eapply intro_max_r. apply H1. omega. assumption.
Qed.

Lemma vars_cap : forall x t,
  In x (vars (cap t)) -> x <= maxvar t + nb_aliens t.

Proof.
intros. apply vars_fcap_fresh. apply le_refl. rewrite cap_eq in H.
assumption.
Qed.

(***********************************************************************)
(** properties of the cap wrt calls *)

Notation calls := (calls R).
Definition vcalls := vcalls R.

Lemma calls_capa : forall t m, calls (fcap (capa t) (fresh m (nb_aliens t))) = nil.

Proof.
set (Q := fun n (ts : terms n) => forall m, vcalls (Vmap_sum (Vmap capa ts)
  (fresh m (sum (Vmap capa ts)))) = nil).
intro. pattern t. apply term_ind with (Q := Q); clear t; intros.
(* var *)
reflexivity.
(* fun *)
unfold nb_aliens. rewrite capa_fun.
pattern (defined f R). apply bool_eq_ind; intros; simpl. reflexivity.
rewrite H0. apply H.
(* nil *)
unfold Q. reflexivity.
(* cons *)
unfold Q. simpl. intro. rewrite Vbreak_fresh. rewrite Vbreak_app. simpl.
apply app_nil. apply H. apply H0.
Qed.

Lemma calls_cap : forall t, calls (cap t) = nil.

Proof.
intro. rewrite cap_eq. apply calls_capa.
Qed.

Lemma aliens_incl_calls : forall u t, Vin u (aliens (capa t)) -> In u (calls t).

Proof.
intros u t. pattern t. apply term_ind_forall; clear t. simpl. auto.
intros f ts H. rewrite calls_fun. rewrite capa_fun. case (defined f R); simpl.
intuition. unfold aliens. simpl. intro. deduce (in_conc H0). do 2 destruct H1.
deduce (Vin_map H1). do 2 destruct H3. subst x. deduce (Vforall_in H H3).
eapply in_vcalls. apply H4. assumption. assumption.
Qed.

(***********************************************************************)
(** concrete alien substitution:
it gives t when applied to the concrete cap of t *)

Definition alien_sub t := fsub (maxvar t) (aliens (capa t)).

Lemma alien_sub_var : forall x, alien_sub (Var x) x = Var x.

Proof.
intro. unfold alien_sub, fsub. simpl. case (le_lt_dec x x). auto.
intro. absurd (x < x). apply lt_irrefl. assumption.
Qed.

Implicit Arguments in_app_or [A l m a].

Lemma app_fcap : forall m s, (forall x, x <= m -> s x = Var x)
  -> forall t, maxvar t <= m
  -> forall v, app s (fcap (capa t) v) = fcap (capa t) (Vmap (app s) v).

Proof.
intros until t. pattern t.
set (Q := fun n (ts : terms n) => Vmax (Vmap maxvar ts) <= m
  -> forall v, Vmap (app s) (Vmap_sum (Vmap capa ts) v)
               = Vmap_sum (Vmap capa ts) (Vmap (app s) v)).
apply term_ind with (Q := Q); clear t.
intros. unfold fcap. simpl. apply H. assumption.
intros f ts IH H0. rewrite capa_fun. unfold fcap. case (defined f R); simpl; intros.
VSntac v. reflexivity.
apply (f_equal (Fun f)). apply IH. assumption.
unfold Q. auto.
intros. unfold Q. simpl. intros.
generalize (Vbreak_eq_app v0). intro. rewrite H3. rewrite Vmap_app.
do 2 rewrite Vbreak_app. simpl. apply Vcons_eq.
apply H0. eapply intro_max_l. apply H2.
apply H1. eapply intro_max_r. apply H2.
Qed.

Lemma Vmap_map_sum : forall m s, (forall x, x <= m -> s x = Var x)
  -> forall n (ts : terms n), Vmax (Vmap maxvar ts) <= m
  -> forall v, Vmap (app s) (Vmap_sum (Vmap capa ts) v)
               = Vmap_sum (Vmap capa ts) (Vmap (app s) v).

Proof.
induction ts; simpl; intros. reflexivity.
generalize (Vbreak_eq_app v). intro. rewrite H1. rewrite Vmap_app.
do 2 rewrite Vbreak_app. simpl. apply Vcons_eq.
eapply app_fcap. apply H. eapply intro_max_l. apply H0.
apply IHts. eapply intro_max_r. apply H0.
Qed.

Lemma alien_sub_cap : forall t, app (alien_sub t) (cap t) = t.

Proof.
intro. pattern t. apply term_ind_forall; intros.
(* var *)
simpl. apply alien_sub_var.
(* fun *)
unfold alien_sub, cap, fresh_for. set (m := maxvar (Fun f v)). rewrite capa_fun.
case (defined f R).
(* f defined *)
change (fsub m (Vcons (Fun f v) Vnil) (S m) = Fun f v).
apply fsub_cons. omega.
(* f undefined *)
set (cs := Vmap capa v).
change (let (n,p) := sigc (fun ts => Fun f (Vmap_sum cs ts), conc cs) in
  let (f0,v0) := p in app (fsub m v0) (f0 (fresh (S m) n)) = Fun f v).
set (s := sigc (fun ts => Fun f (Vmap_sum cs ts), conc cs)).
assert (s = sigc (fun ts => Fun f (Vmap_sum cs ts), conc cs)). reflexivity.
destruct s. destruct p as [f0 v0]. injection H0. intros. subst x.
assert (v0 = conc cs).
apply (inj_pair2 nat (fun x => terms x)). assumption.
assert (f0 = fun ts => Fun f (Vmap_sum cs ts)).
apply (inj_pair2 nat (fun x => terms x -> term)). assumption. subst f0.
rewrite app_fun. apply f_equal with (f := Fun f).
set (s := fsub m v0). set (v1 := fresh (S m) (sum cs)).
assert (Vmap (app s) (Vmap_sum cs v1) = Vmap_sum cs (Vmap (app s) v1)).
unfold cs. eapply Vmap_map_sum with (m := m).
unfold s. apply fsub_inf. apply le_refl. rewrite H4.
assert (Vmap (app s) v1 = conc cs). unfold s, v1. rewrite H3.
rewrite Vmap_fsub_fresh. reflexivity.
rewrite H5. unfold cs. apply Vmap_sum_conc.
Qed.

End S.

Implicit Arguments vars_cap_inf [Sig x t].
Implicit Arguments vars_cap_sup [Sig x t].
Implicit Arguments vars_cap [Sig x t].