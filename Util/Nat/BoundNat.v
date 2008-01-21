(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Leo Ducas, 2007-08-06

type of natural numbers smaller than some constant
*)

Set Implicit Arguments.

Require Export NatUtil.

Section S.

Variable dim : nat.

Definition bnat := {x : nat | x < dim}. 

Definition mkbnat x (h : x<dim) := exist (fun x => x<dim) x h.

Lemma eq_bnat_dec : forall x y : bnat, {x = y} + {x <> y}.

Proof.
intros.
destruct (eq_nat_dec (proj1_sig x) (proj1_sig y)); unfold proj1_sig in *.
destruct x. destruct y. subst; simpl. left.
cut (l=l0). intro; subst. intuition. apply lt_unique.
destruct x. destruct y. right; intuition; inversion H; tauto.
Defined.

Lemma bnat_spec : forall x, x < dim <-> exists y : bnat, proj1_sig y = x.

Proof.
split; intro.
Focus 2. destruct H. destruct x0. simpl in *. intuition.
exists (mkbnat H). simpl. refl.
Qed.

Require Export ListExtras.

Fixpoint bnats_of_nats l :=
  match l with
    | nil => nil
    | x::q =>
      match lt_ge_dec x dim with 
        | left H => mkbnat H :: bnats_of_nats q
        | right _ => bnats_of_nats q
     end
  end.

Lemma bnats_of_nats_spec : forall x l (H : x<dim),
  In x l -> In (mkbnat H) (bnats_of_nats l).

Proof.
intros. induction l. simpl in H0; tauto.
simpl. destruct(lt_ge_dec a dim). simpl. simpl in H0; destruct H0. subst.
left. deduce (lt_unique l0 H); subst; auto.
right; tauto.
simpl in H0; destruct H0. subst. cut False; try tauto; try omega.
tauto.
Qed.

Definition nfirst_bnats := bnats_of_nats (nfirst dim).

Lemma bnatlist_exact : forall x, In x nfirst_bnats.

Proof.
intros. unfold nfirst_bnats. destruct x. fold (mkbnat l).
apply bnats_of_nats_spec. rewrite nfirst_exact. auto.
Qed.

Require Export SortUtil.

Lemma map_lelistA_bnat_to_nat : forall R (a : bnat) l,
  lelistA (fun x y => R (proj1_sig x) (proj1_sig y)) a l ->
  lelistA R (proj1_sig a) (map (fun y => proj1_sig y) l).

Proof.
induction l; intros. simpl; apply nil_leA.
simpl. inversion H; subst. apply cons_leA; auto.
Qed.

Lemma map_sort_bnat_to_nat : forall R l,
  sort (fun x y : bnat => R (proj1_sig x) (proj1_sig y)) l ->
  sort R (map (fun y : bnat => proj1_sig y) l).

Proof.
induction l; intros. simpl; apply nil_sort.
simpl. inversion H; apply cons_sort; try tauto.
apply map_lelistA_bnat_to_nat. intuition.
Qed.

Lemma nfirst_multiplicity : forall n i,
  multiplicity (list_contents (@eq nat) eq_nat_dec (nfirst n)) i
  = if lt_ge_dec i n then 1 else 0.

Proof. 
induction n; intros. simpl. destruct (lt_ge_dec i 0); omega.
simpl. rewrite IHn. destruct (lt_ge_dec i n); destruct (eq_nat_dec n i);
destruct (lt_ge_dec i (S n)); try omega.
Qed.

Lemma bnfirst_multiplicity n (i : bnat) :
  multiplicity
  (list_contents (@eq bnat) eq_bnat_dec (bnats_of_nats (nfirst n))) i
  = if lt_ge_dec (proj1_sig i) n then 1 else 0.

Proof.
destruct i as [i hi]. fold (mkbnat hi). simpl. induction n.
simpl. destruct (lt_ge_dec i 0); omega.
simpl. destruct (lt_ge_dec n dim); simpl; rewrite IHn; destruct(eq_nat_dec n i);
destruct(lt_ge_dec i n); destruct(lt_ge_dec i (S n)); subst; simpl; try omega;
try congruence.
destruct (eq_bnat_dec (mkbnat l) (mkbnat hi)); try omega.
deduce (lt_unique l hi); subst; congruence.
destruct (eq_bnat_dec (mkbnat l) (mkbnat hi)); try omega.
unfold mkbnat in * |-; congruence.
destruct (eq_bnat_dec (mkbnat l) (mkbnat hi)); try omega.
unfold mkbnat in * |-; congruence.
Qed.

Lemma map_multiplicity : forall a (h : a<dim) mb,
  multiplicity (list_contents (@eq bnat) eq_bnat_dec mb) (mkbnat h)
  = multiplicity (list_contents (@eq nat) eq_nat_dec
    (map (fun y : bnat => proj1_sig y) mb)) a.

Proof.
induction mb. simpl; auto.
simpl. rewrite IHmb. destruct (eq_nat_dec (proj1_sig a0) a);
destruct (eq_bnat_dec a0 (mkbnat h)); try omega; try congruence.
destruct a0. simpl in *. subst. deduce (lt_unique h l).
unfold mkbnat in n. congruence.
destruct a0. simpl in *. unfold mkbnat in e. congruence.
Qed.

Lemma lemme_foo : forall a (H:a>=dim) mb, 
  multiplicity (list_contents (eq (A:=nat)) eq_nat_dec
    (map (fun y : bnat => proj1_sig y) mb)) a = 0.

Proof.
induction mb. simpl; auto.
simpl. destruct(eq_nat_dec (proj1_sig a0) a).
destruct a0; simpl in *; subst; omega. simpl. apply IHmb.
Qed.

End S.
