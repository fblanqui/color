(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-05-06

list of reducts of a term and proof that rewriting is finitely branching
*)

Set Implicit Arguments.

Require Import LogicUtil.
Require Import ATrs.
Require Import RelUtil.
Require Import ListUtil.
Require Import VecUtil.
Require Import AMatching.
Require Import NatUtil.

Section S.

Variable Sig : Signature.

Notation term := (term Sig). Notation terms := (vector term).
Notation rule := (rule Sig). Notation rules := (list rule).

(***********************************************************************)
(** top reducts *)

Definition top_reduct (t : term) lr :=
  match matches (lhs lr) t with
    | Some s => Some (sub s (rhs lr))
    | None => None
  end.

Lemma top_reduct_correct : forall R lr t u,
  In lr R -> top_reduct t lr = Some u -> hd_red R t u.

Proof.
intros R0 lr t u hlr. unfold top_reduct. destruct lr as [l r]. simpl.
case_eq (matches l t). ded (matches_correct H). subst. inversion H0.
apply hd_red_rule. hyp. discr.
Qed.

Definition top_reducts R t := filter_opt (top_reduct t) R.

Lemma top_reducts_correct : forall t u R,
  In u (top_reducts R t) -> hd_red R t u.

Proof.
induction R; simpl. contradiction.
assert (h : List.incl R (a::R)). unfold List.incl. simpl. auto.
case_eq (top_reduct t a). simpl in H0. intuition. subst. 
eapply top_reduct_correct with (lr := a). simpl. auto. hyp.
eapply inclusion_elim. apply hd_red_incl with (x := R). hyp. hyp.
eapply inclusion_elim. apply hd_red_incl with (x := R). hyp. apply IHR. hyp.
Qed.

Implicit Arguments top_reducts_correct [t u R].

Lemma top_reducts_correct_red : forall t u R,
  In u (top_reducts R t) -> red R t u.

Proof.
intros. ded (top_reducts_correct H).
eapply inclusion_elim. apply hd_red_incl_red. hyp.
Qed.

Lemma top_reducts_complete : forall t u R,
  rules_preserv_vars R -> hd_red R t u -> In u (top_reducts R t).

Proof.
induction R; intros; redtac. hyp. simpl in lr.
assert (h0 : rules_preserv_vars R). eapply rules_preserv_vars_incl.
2: apply H. apply incl_tl. apply incl_refl. intuition.
(* In (mkRule l r) R *)
Focus 2. simpl.  assert (h1 : hd_red R t u). subst. apply hd_red_rule. hyp.
case (top_reduct t a). right. apply H1; hyp. apply H1; hyp.
(* a = mkRule l r *)
subst a. simpl. unfold top_reduct. simpl. case_eq (matches l t).
ded (matches_correct H0). left. subst u. apply sub_eq. intros.
eapply subeq_inversion. rewrite xl in H2. apply H2.
unfold rules_preserv_vars in H. unfold List.incl in H. eapply H. simpl. auto.
hyp. symmetry in xl. ded (matches_complete xl). rewrite H0 in H2. irrefl.
Qed.

(***********************************************************************)
(** list of reducts of a term *)

Variable R : rules.

Lemma reducts_aux1 : forall k n, S k <= n -> k <= n.

Proof.
intros. omega.
Qed.

Lemma reducts_aux2 : forall k n, S k <= n -> n - S k < n.

Proof.
intros. omega.
Qed.

Fixpoint reducts t :=
  match t with
    | Var _ => top_reducts R t
    | Fun f ts =>
      let fix reducts_vec k (us : terms k) {struct us}
        : k <= arity f -> list term :=
        match us in vector _ k return k <= arity f -> list term with
          | Vnil => fun _ => nil
          | Vcons u1 k' us' => fun h =>
            map (fun x => Fun f (Vreplace ts (reducts_aux2 h) x)) (reducts u1)
            ++ reducts_vec k' us' (reducts_aux1 h)
        end
        in top_reducts R t ++ reducts_vec (arity f) ts (le_refl (arity f))
  end.

Fixpoint reducts_vec f ts k (us : terms k) {struct us}
  : k <= arity f -> list term :=
  match us in vector _ k return k <= arity f -> list term with
    | Vnil => fun _ => nil
    | Vcons u1 k' us' => fun h =>
      map (fun x => Fun f (Vreplace ts (reducts_aux2 h) x)) (reducts u1)
      ++ reducts_vec f ts us' (reducts_aux1 h)
  end.

Lemma fix_reducts_vec : forall f ts k us h,
  (fix reducts_vec (k : nat) (us : terms k) {struct us} :
    k <= arity f -> list term :=
    match us in (vector _ k0) return (k0 <= arity f -> list term) with
      | Vnil => fun _ : 0 <= arity f => nil
      | Vcons u1 k' us' => fun h : S k' <= arity f =>
        map (fun x => Fun f (Vreplace ts (reducts_aux2 h) x)) (reducts u1)
        ++ reducts_vec k' us' (reducts_aux1 h)
    end) k us h = reducts_vec f ts us h.

Proof.
induction us; simpl; intros. refl. apply app_eq. refl. apply IHus.
Qed.

Lemma reducts_fun : forall f ts, reducts (Fun f ts)
  = top_reducts R (Fun f ts) ++ reducts_vec f ts ts (le_refl (arity f)).

Proof.
intros. simpl. rewrite <- fix_reducts_vec. refl.
Qed.

(***********************************************************************)
(** properties *)

Lemma reducts_vec_pi : forall f ts k (us : terms k) h h',
  reducts_vec f ts us h = reducts_vec f ts us h'.

Proof.
intros. assert (h=h'). apply le_unique. subst h'. refl.
Qed.

Lemma reducts_vec_cast : forall f ts k (us : terms k) h k' (e : k = k') h',
  reducts_vec f ts (Vcast us e) h' = reducts_vec f ts us h.

Proof.
induction us; intros; destruct k'. refl. discr. discr. simpl.
inversion e. subst k'.
apply app_eq. apply map_eq. intros. apply args_eq. apply Vreplace_pi.
omega. apply IHus.
Qed.

Implicit Arguments reducts_vec_cast [f ts k us k' e h'].

Lemma In_reducts_vec_elim_aux : forall v' f ts k (us : terms k),
  (forall i (p : i < k), exists r : arity f - k + i < arity f,
    Vnth us p = Vnth ts r) -> forall h, In v' (reducts_vec f ts us h) ->
  exists i, exists p : i < arity f, exists u',
    In u' (reducts (Vnth ts p)) /\ v' = Fun f (Vreplace ts p u').

Proof.
induction us.
(* Vnil *)
contradiction.
(* Vcons *)
intros E h H. simpl in H. rewrite in_app in H. intuition.
(* case 1 *)
ded (in_map_elim H0). decomp H. destruct (E 0 (lt_O_Sn n)). simpl in H.
exists (arity f - S n + 0). exists x0. exists x. rewrite <- H. intuition.
rewrite H3. apply args_eq. apply Vreplace_pi. omega.
(* case 2 *)
assert (E' : forall (i : nat) (p : i < n),
  exists r : arity f - n + i < arity f, Vnth us p = Vnth ts r). intros.
assert (p' : S i < S n). omega. destruct (E (S i) p'). simpl in H.
assert (lt_S_n p' = p). apply lt_unique. rewrite H1 in H. rewrite H.
assert (r : arity f - n + i < arity f). omega. exists r. apply Vnth_eq. omega.
assert (h' : n <= arity f). omega. rewrite reducts_vec_pi with (h':=h') in H0.
apply IHus with (h:=h'); hyp.
Qed.

Implicit Arguments In_reducts_vec_elim_aux [v' f ts k us h].

Lemma In_reducts_vec_elim : forall v' f ts,
  In v' (reducts_vec f ts ts (le_refl (arity f))) ->
  exists i, exists p : i < arity f, exists u',
    In u' (reducts (Vnth ts p)) /\ v' = Fun f (Vreplace ts p u').

Proof.
intros. apply In_reducts_vec_elim_aux
  with (k := arity f) (us := ts) (h := le_refl (arity f)).
intros. assert (r : arity f - arity f + i < arity f). omega. exists r.
apply Vnth_eq. omega. hyp.
Qed.

Implicit Arguments In_reducts_vec_elim [v' f ts].

Lemma In_reducts_vec_intro_aux : forall f ts k (us : terms k)
  (h : k <= arity f) t i (p : i < k) (q : arity f - k + i < arity f),
  In t (reducts (Vnth us p)) ->
  In (Fun f (Vreplace ts q t)) (reducts_vec f ts us h).

Proof.
induction us.
(* Vnil *)
intros. absurd_arith.
(* Vcons *)
intros h t. simpl.
set (F := fun x : term => Fun f (Vreplace ts (reducts_aux2 h) x)).
destruct i; intros p q; rewrite in_app.
(* i = 0 *)
left. assert (e : arity f - S n + 0 = arity f - S n). omega.
rewrite (Vreplace_pi ts q (reducts_aux2 h) t e).
apply in_map with (f:=F). hyp.
(* i > 0 *)
right. assert (q' : arity f - n + i < arity f). omega.
assert (Vreplace ts q t = Vreplace ts q' t). apply Vreplace_pi. omega.
rewrite H0. apply IHus with (p := lt_S_n p). hyp.
Qed.

Implicit Arguments In_reducts_vec_intro_aux [k us i p].

Lemma In_reducts_vec_intro : forall f ts t i (p : i < arity f),
  In t (reducts (Vnth ts p)) ->
  In (Fun f (Vreplace ts p t)) (reducts_vec f ts ts (le_refl (arity f))).

Proof.
intros. assert (q : arity f - arity f + i < arity f). omega.
assert (Vreplace ts p t = Vreplace ts q t). apply Vreplace_pi. omega.
rewrite H0. apply In_reducts_vec_intro_aux with (p := p). hyp.
Qed.

(***********************************************************************)
(** alternative definition (Pierre-Yves Strub) *)

Fixpoint reducts2 t :=
  match t with
    | Var _ => top_reducts R t
    | Fun f ts =>
      let fix reducts2_vec k (us : terms k) {struct us} : list (terms k) :=
        match us with
          | Vnil => nil
          | Vcons u1 _ us' => map (fun x => Vcons x us') (reducts2 u1)
            ++ map (fun x => Vcons u1 x) (reducts2_vec _ us')
        end
        in top_reducts R t ++ map (Fun f) (reducts2_vec (arity f) ts)
  end.

Fixpoint reducts2_vec k (us : terms k) {struct us} : list (terms k) :=
  match us with
    | Vnil => nil
    | Vcons u1 _ us' => map (fun x => Vcons x us') (reducts2 u1)
      ++ map (fun x => Vcons u1 x) (reducts2_vec us')
  end.

Lemma reducts2_fun : forall f ts, reducts2 (Fun f ts)
  = top_reducts R (Fun f ts) ++ map (Fun f) (reducts2_vec ts).

Proof.
intros. simpl. apply app_eq. refl. apply map_eq. refl.
Qed.

Lemma In_reducts2_vec_elim : forall n (vs ts : terms n),
  In vs (reducts2_vec ts) -> exists i, exists p : i < n, exists u,
    In u (reducts2 (Vnth ts p)) /\ vs = Vreplace ts p u.

Proof.
induction ts; intros.
(* Vnil *)
contradiction.
(* Vcons *)
simpl in H. rewrite in_app in H. intuition.
(* case 1 *)
ded (in_map_elim H0); clear H0. decomp H.
exists 0. set (p := lt_O_Sn n). exists p. exists x. simpl. auto.
(* case 2 *)
ded (in_map_elim H0); clear H0. decomp H.
ded (IHts x H1); clear IHts. decomp H.
exists (S x0). assert (p : S x0<S n). omega. exists p. exists x2. simpl.
assert (lt_S_n p = x1). apply lt_unique. rewrite H. subst x. auto. 
Qed.

Implicit Arguments In_reducts2_vec_elim [n vs ts].

Lemma In_reducts2_vec_intro : forall n (ts : terms n) t i (p : i < n),
  In t (reducts2 (Vnth ts p)) -> In (Vreplace ts p t) (reducts2_vec ts).

Proof.
induction ts.
(* Vnil *)
intros. absurd_arith.
(* Vcons *)
destruct i; simpl; intro; rewrite in_app.
left. apply in_map with (f := fun x => Vcons x ts). hyp.
right. apply in_map with (f := fun x => Vcons a x). apply IHts. hyp.
Qed.

(***********************************************************************)
(** correctness *)

Lemma reducts_correct : forall t u, In u (reducts t) -> red R t u.

Proof.
intro t. pattern t; apply term_ind_forall; clear t.
(* Var *)
intros. apply top_reducts_correct_red. hyp.
(* Fun *)
intros f ts IH u. rewrite reducts_fun. rewrite in_app. intuition.
apply hd_red_incl_red. apply top_reducts_correct. hyp.
rename H0 into h. ded (In_reducts_vec_elim h). decomp H.
ded (Vforall_nth x0 IH _ H1). redtac. unfold red. exists l. exists r.
assert (h1 : 0+x<=arity f). omega. set (v1 := Vsub ts h1).
assert (h2 : S x+(arity f-S x)<=arity f). omega. set (v2 := Vsub ts h2).
assert (e : x+S(arity f-S x)=arity f). omega.
exists (Cont f e v1 c v2). exists s. intuition. simpl. apply args_eq.
rewrite <- xl. unfold v2. rewrite Vcons_nth. unfold v1. apply Veq_app_cons_aux.
simpl. rewrite H2. apply args_eq. apply Veq_nth; intros. rewrite Vnth_cast.
rewrite Vnth_app. destruct (le_gt_dec x i).
(* 1) x <= i *)
destruct (eq_nat_dec x i).
(* a) x = i *)
set (q := Vnth_app_aux (S (arity f - S x)) (Vnth_cast_aux e ip) l0). gen q.
assert (i - x = 0). omega. rewrite H. intro. simpl.
transitivity (Vnth (Vreplace ts x0 x1) x0). apply Vnth_eq. auto.
rewrite Vnth_replace. hyp.
(* b) x <> i *)
rewrite Vnth_replace_neq. 2: hyp. rewrite (Veq_app_cons ts x0).
rewrite Vnth_cast. rewrite Vnth_app. destruct (le_gt_dec x i). 2: absurd_arith.
set (p1 := Vnth_app_aux (S (arity f - S x))
  (Vnth_cast_aux (Veq_app_cons_aux3 x0) ip) l1). gen p1.
set (p2 := Vnth_app_aux (S (arity f - S x)) (Vnth_cast_aux e ip) l0). gen p2.
assert (i-x = S(pred(i-x))). omega. rewrite H. intros.
assert (p2=p1). apply lt_unique. subst p2.
repeat rewrite Vnth_cons. assert (Vsub ts (Veq_app_cons_aux2 x0) = v2).
unfold v2. apply Veq_nth; intros. repeat rewrite Vnth_sub.
apply Vnth_eq. refl. rewrite H0. apply Vnth_eq. refl.
(* 2) x > i *)
rewrite Vnth_replace_neq. 2: omega. rewrite (Veq_app_cons ts x0).
rewrite Vnth_cast. rewrite Vnth_app. destruct (le_gt_dec x i). absurd_arith.
assert (g0 = g). apply lt_unique. subst g0.
assert (Vsub ts (Veq_app_cons_aux1 x0) = v1). unfold v1.
apply (f_equal (@Vsub _ _ ts _ _)). apply le_unique. rewrite H. refl.
Qed.

(***********************************************************************)
(** completeness *)

Lemma reducts_complete : rules_preserv_vars R ->
  forall t u, red R t u -> In u (reducts t).

Proof.
intros H t; pattern t; apply term_ind_forall; clear t; intros.
(* Var *)
ded (red_case H0). intuition.
simpl. apply top_reducts_complete; hyp.
decomp H2. discr.
(* Fun *)
rewrite reducts_fun. rewrite in_app. ded (red_case H1). intuition.
left. apply top_reducts_complete; hyp.
right. decomp H3. Funeqtac. subst x0.
ded (Vforall_nth x2 H0 _ H2). subst u. apply In_reducts_vec_intro. hyp.
Qed.

(***********************************************************************)
(** rewriting is finitely branching *)

Lemma fin_branch : rules_preserv_vars R -> finitely_branching (red R).

Proof.
unfold finitely_branching. intros. exists (reducts x). intuition.
apply reducts_complete; hyp. apply reducts_correct. hyp.
Qed.

End S.
