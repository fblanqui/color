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


From Coq Require Import Relations List Arith Morphisms.
From CoLoR Require Import more_list list_permut list_sort term_spec term_o equational_theory_spec equational_theory.

Set Implicit Arguments.

Module Type S.              

  Declare Module Import EqTh : equational_theory_spec.EqTh.

  Import T.
  Import F.

  Declare Module TO : ordered_set.S with Definition A := term.
  Declare Module Import Sort : list_sort.Sort with Module DOS := TO.
  Import LPermut.

(** ** Definition of AC. *)
Inductive ac_one_step_at_top : term -> term -> Prop :=
  | a_axiom :
      forall (f:symbol) (t1 t2 t3:term),
        arity f = AC ->
        ac_one_step_at_top
          (Term f ((Term f (t1 :: t2 :: nil)) :: t3 :: nil))
          (Term f (t1 :: ((Term f (t2 :: t3 :: nil)) :: nil)))
  | c_axiom :
      forall (f:symbol) (t1 t2:term),
        arity f = C \/ arity f = AC ->
        ac_one_step_at_top (Term f (t1 :: t2 :: nil))
          (Term f (t2 :: t1 :: nil)).

#[global] Hint Constructors ac_one_step_at_top : core.

Definition ac := th_eq ac_one_step_at_top.

Fixpoint flatten (f : symbol) (l : list term) : list term :=
  match l with
  | nil => nil
  | (Var _ as t) :: tl => t :: (flatten f tl)
  | (Term g ll as t) :: tl =>
           if F.Symb.eq_bool f g 
           then ll ++ (flatten f tl)
 	   else t :: (flatten f tl)
   end.

Fixpoint canonical_form (t : term) : term :=
  match t with
  | Var _ => t
  | Term f l =>
    Term f
      (match arity f with
      | Free _ => map canonical_form l
      | C => quicksort (map canonical_form l)
      | AC => quicksort (flatten f (map canonical_form l))
      end)
end.

 Fixpoint well_formed_cf (t:term) : Prop :=
  match t with
  | Var _ => True
  | Term f l =>
     let wf_cf_list :=
       (fix wf_cf_list (l:list term) : Prop :=
       match l with
       | nil => True
       | h :: tl => well_formed_cf h /\ wf_cf_list tl
       end) in
       wf_cf_list l /\
     (match arity f with
     | Free n => length l = n 
     | C => length l = 2 /\ is_sorted l
     | AC => length l >= 2 /\ 
             is_sorted l /\
             (forall s, In s l -> match s with
                                  | Var _ => True
                                  | Term g _ => f<>g
                                  end)
     end)
  end.

Definition build (f : symbol) l :=
  match l with
  | t :: nil => t
  | _ => Term f (quicksort l)
  end.

(*  Definition is_subst_canonical_form *)
(* Definition well_formed_cf_subst *)
Definition well_formed_cf_subst sigma := 
  forall v, match find X.eq_bool v sigma with
	    | None => True
	    | Some t => well_formed_cf t
	    end.

(* Definition apply_cf_subst *)
 Fixpoint apply_cf_subst (sigma : substitution) (t : term) {struct t} : term :=
  match t with
  | Var v => 
    match find X.eq_bool v sigma with
    | None => t
    | Some v_sigma => v_sigma
    end
  | Term f l => 
     let l_sigma := 
       match arity f with
       | AC => quicksort (flatten f (map (apply_cf_subst sigma) l))
       | C => quicksort (map (apply_cf_subst sigma) l)
       | Free _ => map (apply_cf_subst sigma) l
     end in
   Term f l_sigma
 end.

(* Definition ac_size *)
 Fixpoint ac_size (t:term) : nat :=
  match t with
  | Var v => 1
  | Term f l => 
       let ac_size_list :=
         (fix ac_size_list (l : list term) {struct l} : nat :=
            match l with
            | nil => 0
            | t :: lt => ac_size t + ac_size_list lt
            end) in
     (match arity f with
      | AC => (length l) - 1
      | C => 1
      | Free _ => 1
      end) + ac_size_list l
   end.

(* Theorem no_need_of_instance *)
 (* Theorem l_assoc *)
 Parameter l_assoc :
  forall f t1 t2 t3, arity f = AC ->
  ac (Term f (Term f (t1 :: t2 :: nil) :: t3 :: nil))
       (Term f (t1 :: (Term f (t2 :: t3 :: nil)) :: nil)).

(* Theorem r_assoc *)
Parameter r_assoc :
  forall f t1 t2 t3, arity f = AC ->
  ac (Term f (t1 :: (Term f (t2 :: t3 :: nil)) :: nil))
       (Term f (Term f (t1 :: t2 :: nil) :: t3 :: nil)).

(* Theorem comm *)
Parameter comm :
  forall f t1 t2, arity f = C \/ arity f = AC ->
  ac (Term f (t1 :: t2 :: nil)) (Term f (t2 :: t1 :: nil)).

(* Theorem ac_one_step_at_top_top_eq *)
(* Theorem ac_one_step_top_eq *)
(* Theorem ac_top_eq *)
Parameter ac_top_eq : 
  forall t1 t2, ac t1 t2 ->
  match t1, t2 with
   | Var x1, Var x2 => x1 = x2
   | Term _ _, Var _ => False
   | Var _, Term _ _ => False
   | Term f1 _, Term f2 _ => f1 = f2
   end. 	

(* Theorem well_formed_cf_unfold *)
Parameter well_formed_cf_unfold : forall t,
 well_formed_cf t -> match t with
                    | Var _ => True
                    | Term f l =>
                      (forall u, In u l -> well_formed_cf u) /\
                      (match arity f with
                       | AC => length l >= 2 /\ is_sorted l /\
                               (forall u, In u l -> match u with
                                                    | Var _ => True
                                                    | Term g _ => f <> g
                                                    end)
                       | C => length l = 2 /\ is_sorted l
                       | Free n => length l = n
                       end)
                       end.

(* Theorem well_formed_cf_subterms *)
Parameter well_formed_cf_subterms :
 forall f l, well_formed_cf (Term f l) -> (forall t, In t l -> well_formed_cf t).

(* Theorem well_formed_cf_length *)
Parameter well_formed_cf_length :
 forall f l, arity f = AC -> well_formed_cf (Term f l) -> 2 <= length l.

 (* Theorem well_formed_cf_sorted *)
Parameter well_formed_cf_sorted :
 forall f l, arity f = AC -> well_formed_cf (Term f l) -> is_sorted l.

 (* Theorem well_formed_cf_alien *)
Parameter well_formed_cf_alien :
 forall f l, arity f = AC -> well_formed_cf (Term f l) ->
 (forall t, In t l -> match t with 
                          | Var _ => True
                          | Term g _ => f <> g
                          end).

 (* Theorem well_formed_cf_fold *)
 (* Theorem flatten_app *)
 Parameter flatten_app : 
  forall f l1 l2, flatten f (l1 ++ l2) = (flatten f l1) ++ (flatten f l2).

(* Theorem list_permut_flatten *)
Parameter list_permut_flatten :
  forall f l1 l2, permut l1 l2 -> permut (flatten f l1) (flatten f l2).

(* Theorem well_formed_cf_is_well_formed_cf *)
 (* Theorem length_flatten_bis *)
Parameter length_flatten_bis :
forall f, arity f = AC ->
  forall l, (forall t, In t l -> well_formed_cf t) ->
 (length l) <= length (flatten f l).

 (* Theorem length_flatten *)
 (* Theorem well_formed_cf_is_well_formed_cf_conv *)
 (* Theorem flatten_cf *)
Parameter flatten_cf :
 forall f t1 t2, arity f = AC -> well_formed_cf t1 -> well_formed_cf t2 ->
 permut (flatten f (t1 :: nil)) (flatten f (t2 :: nil)) ->
 t1 = t2.

(* Theorem flatten_cf_cf *)
 Parameter flatten_cf_cf :
 forall f t1 t2, arity f = AC -> well_formed t1 -> well_formed t2 ->
 permut (flatten f (canonical_form t1 :: nil))
 (flatten f (canonical_form t2 :: nil)) ->
 canonical_form t1 = canonical_form t2.

(* Theorem build_eq_Term *)
Parameter build_eq_Term :
forall f l, 2 <= length l -> build f l = Term f (quicksort l).

 (* Theorem well_formed_cf_build *)
Parameter well_formed_cf_build :
 forall f l, arity f = AC ->
 1 <= length l ->
 (forall t, In t l -> well_formed_cf t) ->
 (forall t, In t l -> match t with | Var _ => True | Term g _ => f <> g end) ->
 well_formed_cf (build f l).

 (* Theorem well_formed_cf_build_cons *)
Parameter well_formed_cf_build_cons :
 forall f t l, arity f = AC -> 
 well_formed_cf (Term f (t :: l)) -> well_formed_cf (build f l).

 (* Theorem well_formed_cf_build_inside *)
Parameter well_formed_cf_build_inside :
forall f t l1 l2, arity f = AC -> 
 well_formed_cf (Term f (l1 ++ t :: l2)) -> well_formed_cf (build f (l1 ++ l2)).

 (* Theorem flatten_build *)
Parameter flatten_build :
 forall f l, arity f = AC -> 
 (forall t, In t l -> match t with | Var _ => True | Term g _ => f <> g end) ->
 permut (flatten f ((build f l) :: nil)) l.

 (* Theorem flatten_build_cons *)
Parameter flatten_build_cons :
 forall f t l, arity f = AC -> well_formed_cf (Term f (t :: l)) -> 
 permut (flatten f ((build f l) :: nil)) l.

 (* Theorem flatten_build_inside *)
Parameter flatten_build_inside :
 forall f t l1 l2, arity f = AC -> 
 well_formed_cf (Term f (l1 ++ t :: l2)) ->
 permut (flatten f ((build f (l1 ++ l2)) :: nil)) (l1 ++ l2).

 (* Theorem is_subst_cf_is_subst_cf *)
 (* Theorem well_formed_cf_subst_is_well_formed_cf_subst_aux *)
 (* Theorem well_formed_cf_subst_is_well_formed_cf_subst *)
 (* Theorem flatten_apply_cf_subst *)
Parameter flatten_apply_cf_subst :
 forall sigma f l, arity f = AC ->
  permut (flatten f (map (apply_cf_subst sigma) l))
  (flatten f (apply_cf_subst sigma (build f l) :: nil)).

 (* Theorem apply_cf_subst_is_sound *)
 (* Theorem well_formed_cf_apply_subst *)
Parameter well_formed_cf_apply_subst :
  forall sigma, well_formed_cf_subst sigma -> 
  forall t, well_formed_cf t -> well_formed_cf (apply_cf_subst sigma t).

 (* Theorem length_flatten_ter *)
Parameter length_flatten_ter :
forall f sigma, arity f = AC -> well_formed_cf_subst sigma ->
  forall l, (forall t, In t l -> well_formed_cf t) ->
  length l <= length (flatten f (map (apply_cf_subst sigma) l)).

 (* Theorem ac_one_step_at_top_cf_eq *)
 (* Theorem sym_refl_ac_one_step_at_top_cf_eq *)
 (* Theorem ac_one_step_cf_eq *)
 (* Theorem ac_cf_eq *)
Parameter ac_cf_eq :  forall t1 t2, ac t1 t2 -> canonical_form t1 = canonical_form t2.
 (* Theorem ac_one_step_at_top_size_eq *)
 (* Theorem sym_refl_ac_one_step_at_top_size_eq *)
 (* Theorem ac_one_step_size_eq *)
 (* Theorem ac_size_eq *)
Parameter ac_size_eq :  forall t1 t2, ac t1 t2 -> size t1 = size t2.

 (* Theorem ac_size_unfold *)
Parameter ac_size_unfold :
  forall t, 
  ac_size t = match t with
              | Var _ => 1
              | Term f l =>
                (match arity f with
                | AC => (length l) - 1
                | C => 1
                | Free _ => 1
                end) + list_size ac_size l
               end.

(* Theorem size_size_aux2 *)
(* Theorem size_size_aux3 *)
 Parameter size_size_aux3 :
 forall f t, arity f = AC -> well_formed t ->
 1 <= length (A:=term) (flatten f (canonical_form t :: nil)).

(* Theorem size_size *)
Parameter size_size :
 forall t, well_formed t -> size t = ac_size (canonical_form t).

 (* Theorem ac_size_ge_one *)
Parameter ac_size_ge_one : forall t, well_formed_cf t -> 1 <= ac_size t.
End S.

Module Make' (T1: Term) 
(OF1 : ordered_set.S with Definition A := T1.symbol) 
(OX1 : ordered_set.S with Definition A := T1.variable) <: 
S with Module EqTh.T := T1. 

Module T := T1.
Module EqTh := equational_theory.Make (T).
Import EqTh T1 T1.F.

(** ** Definition of AC. *)
Inductive ac_one_step_at_top : term -> term -> Prop :=
  | a_axiom :
      forall (f:symbol) (t1 t2 t3:term),
        arity f = AC ->
        ac_one_step_at_top
          (Term f ((Term f (t1 :: t2 :: nil)) :: t3 :: nil))
          (Term f (t1 :: ((Term f (t2 :: t3 :: nil)) :: nil)))
  | c_axiom :
      forall (f:symbol) (t1 t2:term),
        arity f = C \/ arity f = AC ->
        ac_one_step_at_top (Term f (t1 :: t2 :: nil))
          (Term f (t2 :: t1 :: nil)).

#[global] Hint Constructors ac_one_step_at_top : core.

Definition ac := th_eq ac_one_step_at_top.

Lemma no_need_of_instance :
  forall t1 t2, axiom (sym_refl ac_one_step_at_top) t1 t2 -> 
                     (sym_refl ac_one_step_at_top) t1 t2.
Proof.
unfold sym_refl; intros t1 t2 H. 
inversion_clear H as [ u1 u2 sigma H']; destruct H' as [H' | [H' | H']].
inversion_clear H'.
left; simpl; apply a_axiom; trivial.
left; simpl; apply c_axiom; trivial.
inversion_clear H'.
right; left; simpl; apply a_axiom; trivial.
right; left; simpl; apply c_axiom; trivial.
right; right; subst; trivial.
Qed.

Lemma l_assoc :
  forall f t1 t2 t3, arity f = AC ->
  ac (Term f (Term f (t1 :: t2 :: nil) :: t3 :: nil))
       (Term f (t1 :: (Term f (t2 :: t3 :: nil)) :: nil)).
Proof.
intros f t1 t2 t3 Af.
unfold ac, th_eq.
do 2 left.
rewrite <- (empty_subst_is_id (Term f (Term f (t1 :: t2 :: nil) :: t3 :: nil))).
rewrite <- (empty_subst_is_id (Term f (t1 :: Term f (t2 :: t3 :: nil) :: nil))).
apply instance.
left; apply a_axiom; trivial.
Qed.

Lemma r_assoc :
  forall f t1 t2 t3, arity f = AC ->
  ac (Term f (t1 :: (Term f (t2 :: t3 :: nil)) :: nil))
       (Term f (Term f (t1 :: t2 :: nil) :: t3 :: nil)).
Proof.
intros f t1 t2 t3 Af.
unfold ac, th_eq.
do 2 left.
rewrite <- (empty_subst_is_id (Term f (Term f (t1 :: t2 :: nil) :: t3 :: nil))).
rewrite <- (empty_subst_is_id (Term f (t1 :: Term f (t2 :: t3 :: nil) :: nil))).
apply instance.
right; left; apply a_axiom; trivial.
Qed.

Lemma comm :
  forall f t1 t2, arity f = C \/ arity f = AC ->
  ac (Term f (t1 :: t2 :: nil)) (Term f (t2 :: t1 :: nil)).
Proof.
intros f t1 t2 Af.
unfold ac, th_eq.
do 2 left.
rewrite <- (empty_subst_is_id (Term f (t1 :: t2 :: nil))).
rewrite <- (empty_subst_is_id (Term f (t2 :: t1 :: nil))).
apply instance.
left; apply c_axiom; trivial.
Qed.

Lemma ac_one_step_at_top_top_eq :
  forall t1 t2, (sym_refl ac_one_step_at_top) t1 t2 ->
   match t1, t2 with
   | Var x1, Var x2 => x1 = x2
   | Term _ _, Var _ => False
   | Var _, Term _ _ => False
   | Term f1 _, Term f2 _ => f1 = f2
   end. 	
Proof.
unfold sym_refl; intros t1 t2 [Ac | [Ac | t1_eq_t2]].
inversion_clear Ac; simpl; trivial.
inversion_clear Ac; simpl; trivial.
subst t2; destruct t1; trivial.
Qed.

Lemma ac_one_step_top_eq :
  forall t1 t2 : term, one_step (sym_refl ac_one_step_at_top) t1 t2 ->    
  match t1, t2 with
   | Var x1, Var x2 => x1 = x2
   | Term _ _, Var _ => False
   | Var _, Term _ _ => False
   | Term f1 _, Term f2 _ => f1 = f2
   end. 	
Proof.
intros t1 t2 Ac; inversion Ac; trivial.
apply ac_one_step_at_top_top_eq;
apply no_need_of_instance; trivial.
Qed.

Lemma ac_top_eq : 
  forall t1 t2 : term, ac t1 t2 ->
  match t1, t2 with
   | Var x1, Var x2 => x1 = x2
   | Term _ _, Var _ => False
   | Var _, Term _ _ => False
   | Term f1 _, Term f2 _ => f1 = f2
   end. 	
Proof.
intros t1 t2 Ac; induction Ac.
(* one step *)
inversion H as [ H1 H2 H' H4 H5 | f l1 l2 H' H1 H2]; subst; trivial.
apply ac_one_step_top_eq; assumption.
(* th_trans *)
generalize (ac_one_step_top_eq H).
destruct x as [ v1 | f1 l1 ]; 
destruct y as [ v2 | f2 l2 ]; 
destruct z as [ v3 | f3 l3 ]; trivial.
intro; apply trans_eq with v2; assumption.
contradiction.
contradiction.
intro; apply trans_eq with f2; trivial.
Qed.

(* Definition of canonical forms *)
Module Import TO := term_o.Make (T1) (OF1) (OX1).

Module Import Sort :=  list_sort.Make (TO).
Import LPermut.

Fixpoint flatten (f : symbol) (l : list term) : list term :=
  match l with
  | nil => nil
  | (Var _ as t) :: tl => t :: (flatten f tl)
  | (Term g ll as t) :: tl =>
           if F.Symb.eq_bool f g 
           then ll ++ (flatten f tl)
 	   else t :: (flatten f tl)
   end.

Fixpoint canonical_form (t : term) : term :=
  match t with
  | Var _ => t
  | Term f l =>
    Term f
      (match arity f with
      | Free _ => map canonical_form l
      | C => quicksort (map canonical_form l)
      | AC => quicksort (flatten f (map canonical_form l))
      end)
end.

(* Properties of canonical forms and well-formed terms *)

Fixpoint well_formed_cf (t:term) : Prop :=
  match t with
  | Var _ => True
  | Term f l =>
     let wf_cf_list :=
       (fix wf_cf_list (l:list term) : Prop :=
       match l with
       | nil => True
       | h :: tl => well_formed_cf h /\ wf_cf_list tl
       end) in
       wf_cf_list l /\
     (match arity f with
     | Free n => length l = n 
     | C => length l = 2 /\ is_sorted l
     | AC => length l >= 2 /\ 
             is_sorted l /\
             (forall s, In s l -> match s with
                                  | Var _ => True
                                  | Term g _ => f<>g
                                  end)
     end)
  end.

Lemma well_formed_cf_unfold : forall t,
 well_formed_cf t -> match t with
                    | Var _ => True
                    | Term f l =>
                      (forall u, In u l -> well_formed_cf u) /\
                      (match arity f with
                       | AC => length l >= 2 /\ is_sorted l /\
                               (forall u, In u l -> match u with
                                                    | Var _ => True
                                                    | Term g _ => f <> g
                                                    end)
                       | C => length l = 2 /\ is_sorted l
                       | Free n => length l = n
                       end)
                       end.
Proof.
intro t; destruct t as [v | f l]; simpl; trivial; intros [Wl Ll]; split; trivial.
clear Ll; induction l as [ | t l].
contradiction.
intros u [u_eq_t | In_u]; subst; intuition.
Qed.

Lemma well_formed_cf_subterms :
 forall f l, well_formed_cf (Term f l) -> (forall t, In t l -> well_formed_cf t).
Proof.
intros f l W; elim (well_formed_cf_unfold _ W); trivial.
Qed.

Lemma well_formed_cf_length :
 forall f l, arity f = AC -> well_formed_cf (Term f l) -> 2 <= length l.
Proof.
intros f l Af [_ Ll]; rewrite Af in Ll; intuition.
Qed.

Lemma well_formed_cf_sorted :
 forall f l, arity f = AC -> well_formed_cf (Term f l) -> is_sorted l.
Proof.
intros f l Af [_ Ll]; rewrite Af in Ll; intuition.
Qed.

Lemma well_formed_cf_alien :
 forall f l, arity f = AC -> well_formed_cf (Term f l) ->
 (forall t, In t l -> match t with 
                          | Var _ => True
                          | Term g _ => f <> g
                          end).
Proof.
intros f l Af [_ Ll]; rewrite Af in Ll; intuition.
Qed.

Lemma well_formed_cf_fold : 
forall t, (match t with
                    | Var _ => True
                    | Term f l =>
                      (forall u, In u l -> well_formed_cf u) /\
                      (match arity f with
                       | AC => length l >= 2 /\ is_sorted l /\
                               (forall u, In u l -> match u with
                                                    | Var _ => True
                                                    | Term g _ => f <> g
                                                    end)
                       | C => length l = 2 /\ is_sorted l
                       | Free n => length l = n
                       end)
                       end) -> well_formed_cf t.
Proof.
intro t; destruct t as [v | f l]; trivial.
intros [Wl Hl]; split; trivial; clear Hl; 
induction l as [ | t l]; intuition; 
apply IHl; intros; apply Wl; right; trivial.
Qed.

Lemma flatten_app : 
  forall f l1 l2, flatten f (l1 ++ l2) = (flatten f l1) ++ (flatten f l2).
Proof.
intros f l1; induction l1 as [ | [v1 | g1 ll1]]; simpl; trivial.
intros l2; rewrite IHl1; trivial.
intros l2; rewrite IHl1; generalize (F.Symb.eq_bool_ok f g1); case (F.Symb.eq_bool f g1); [intro f_eq_g1 | intro f_diff_g1].
rewrite app_ass; trivial.
simpl; trivial.
Qed.

Lemma list_permut_flatten :
  forall f l1 l2, permut l1 l2 -> permut (flatten f l1) (flatten f l2).
Proof.
intros f l1; induction l1 as [ | t1 l1]; intros l2 P.
rewrite (permut_nil (permut_sym P)); apply permut_refl.
assert (In_t1 : mem (@eq _) t1 l2). rewrite <- P; left; reflexivity.
destruct (mem_split_set _ _ eq_bool_ok _ _ In_t1) as [t1' [l2' [l2'' [t1_eq_t1' [H _]]]]]; 
simpl in t1_eq_t1'; simpl in H; subst l2;
assert (P' : permut (flatten f l1) (flatten f (l2' ++ l2''))).
apply IHl1.
rewrite <- permut_cons_inside in P; trivial.
dummy t1 t1' t1_eq_t1'; subst t1'.
rewrite flatten_app; simpl; destruct t1 as [v1 | f1 ll1].
rewrite <- permut_cons_inside.
rewrite <- flatten_app; trivial.
reflexivity.
generalize (F.Symb.eq_bool_ok f f1); case (F.Symb.eq_bool f f1); [intro f_eq_f1; subst f1 | intros _].
transitivity (ll1 ++ flatten f (l2' ++ l2'')).
rewrite <- permut_app1; trivial.
rewrite flatten_app; do 2 rewrite <- app_ass; 
rewrite <- permut_app2;
apply list_permut_app_app.
rewrite <- permut_cons_inside.
rewrite <- flatten_app; trivial.
reflexivity.
Qed.

Lemma well_formed_cf_is_well_formed_cf :
 forall cf, well_formed_cf cf -> exists t, well_formed t /\ cf = canonical_form t.
Proof.
intros cf Wcf; generalize (well_formed_cf_unfold _ Wcf);
pattern cf; apply term_rec3; clear cf Wcf.
intros v _; exists (Var v); unfold well_formed; simpl; split; trivial.
intros f l Hrec [Wl Ll]; 
assert (Wl' : forall u, In u l -> exists s, well_formed s /\ u = canonical_form s).
intros u In_u; apply Hrec; trivial; 
apply well_formed_cf_unfold; apply Wl; trivial.
destruct_arity f n Af.
(* AC *)
revert Ll; intros [Ll [Sl Al]]; induction l as [ | t1 l].
absurd (0 >= 2); trivial; unfold ge; auto with arith.
destruct l as [ | t2 l].
absurd (1 >= 2); trivial; unfold ge; auto with arith.
elim (Wl' t1). intros u1 [Wu1 Hu1] .
elim (Wl' t2). intros u2 [Wu2 Hu2] .
assert (At1 : match t1 with Var _ => True | Term g _ => f <> g end).
apply Al; left; trivial.
assert (At2 : match t2 with Var _ => True | Term g _ => f <> g end).
apply Al; right; left; trivial.
destruct l as [ | t3 l].
exists (Term f (u2 :: u1 :: nil)); split.
apply well_formed_fold; rewrite Af; split; trivial.
intros u In_u; elim In_u; clear In_u; intro In_u; try subst u; trivial;
elim In_u; clear In_u; intro In_u; try subst u; trivial; contradiction.
simpl; rewrite Af; rewrite <- Hu1; rewrite <- Hu2.
destruct t1 as [v1 | g1 ll1]; destruct t2 as [v2 | g2 ll2].
apply (f_equal (fun l => Term f l)); apply sort_is_unique; trivial.
apply quick_sorted.
apply permut_sym; apply quick_permut_bis; 
apply (list_permut_app_app (Var v2 :: nil) (Var v1 :: nil)).
generalize (F.Symb.eq_bool_ok f g2); case (F.Symb.eq_bool f g2); [intro f_eq_g2 | intro f_diff_g2].
absurd (f=g2); trivial.
apply (f_equal (fun l => Term f l)); apply sort_is_unique; trivial.
apply quick_sorted.
apply permut_sym; apply quick_permut_bis; 
apply (list_permut_app_app (Term g2 ll2 :: nil) (Var v1 :: nil)).
generalize (F.Symb.eq_bool_ok f g1); case (F.Symb.eq_bool f g1); [intro f_eq_g1 | intro f_diff_g1].
absurd (f=g1); trivial.
apply (f_equal (fun l => Term f l)); apply sort_is_unique; trivial.
apply permut_sym; apply quick_permut_bis; 
apply (list_permut_app_app (Var v2 :: nil) (Term g1 ll1 :: nil)).
generalize (F.Symb.eq_bool_ok f g2); case (F.Symb.eq_bool f g2); [intro f_eq_g2 | intro f_diff_g2].
absurd (f=g2); trivial.
generalize (F.Symb.eq_bool_ok f g1); case (F.Symb.eq_bool f g1); [intro f_eq_g1 | intro f_diff_g1].
absurd (f=g1); trivial.
apply (f_equal (fun l => Term f l)); apply sort_is_unique; trivial.
apply quick_sorted.
apply permut_sym; apply quick_permut_bis; 
apply (list_permut_app_app (Term g2 ll2 :: nil) (Term g1 ll1 :: nil)).
elim IHl.
intros s2 [Ws2 Hs2]; exists (Term f (s2 :: u1 :: nil)); split.
apply well_formed_fold; rewrite Af; split; trivial.
intros u In_u; elim In_u; clear In_u; intro In_u; try subst u; trivial;
elim In_u; clear In_u; intro In_u; try subst u; trivial; contradiction.
simpl; rewrite Af; rewrite <- Hu1; rewrite <- Hs2.
generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); [intros _ | intro f_diff_f; apply False_rect; apply f_diff_f; reflexivity].
destruct t1 as [v1 | g1 ll1].
apply (f_equal (fun l => Term f l)); apply sort_is_unique; trivial.
apply quick_sorted.
apply permut_sym; apply quick_permut_bis;
apply permut_sym; rewrite <- permut_cons_inside.
rewrite <- app_nil_end; apply permut_refl.
reflexivity.
generalize (F.Symb.eq_bool_ok f g1); case (F.Symb.eq_bool f g1); [intro f_eq_g1 | intro f_diff_g1].
absurd (f=g1); trivial.
apply (f_equal (fun l => Term f l)); apply sort_is_unique; trivial.
apply quick_sorted.
apply permut_sym; apply quick_permut_bis;
apply permut_sym; rewrite <- permut_cons_inside.
rewrite <- app_nil_end; apply permut_refl.
reflexivity.
intros; apply Hrec; trivial; right; trivial.
intros; apply Wl; right; trivial.
intros; apply Wl'; right; trivial.
simpl; auto with arith.
apply sorted_tl_sorted with t1; trivial.
intros; apply Al; right; trivial.
right; left; trivial.
left; trivial.
(* C *)
generalize Ll; clear Ll; intros [Ll Sl]; destruct l as [ | t1 l].
absurd (0 = 2); auto with arith.
destruct l as [ | t2 l].
absurd (1 = 2); auto with arith.
destruct l as [ | t3 l].
elim (Wl' t1). intros u1 [Wu1 Hu1] .
elim (Wl' t2). intros u2 [Wu2 Hu2] .
exists (Term f (u1 :: u2 :: nil)); split.
apply well_formed_fold; rewrite Af; split; trivial.
intros u In_u; elim In_u; clear In_u; intro In_u; try subst u; trivial;
elim In_u; clear In_u; intro In_u; try subst u; trivial; contradiction.
simpl; rewrite Af; subst; apply (f_equal (fun l => Term f l));
apply sort_is_unique; trivial;
[ apply quick_sorted | apply quick_permut ].
right; left; trivial.
left; trivial.
absurd (S(S(S(length l))) = 2); auto.
(* Free n *)
assert (H : exists l', (forall s, In s l' -> well_formed s) /\ 
                               map canonical_form l' = l).
generalize l Wl'; clear l Hrec Wl Wl' Ll; induction l as [ | t l].
intros _; exists (nil (A := term)); split; trivial; contradiction.
intros Wl; elim IHl.
intros l' [Wl' Hl']; elim (Wl t).
intros t' [Wt' Ht']; exists (t' :: l'); split; trivial.
intros s [ s_eq_t' | In_s]; try subst s; trivial; apply Wl'; trivial.
simpl; subst; trivial.
left; trivial.
intros; apply Wl; right; trivial.
elim H; clear H; intros l' [Wl'' Hl']; exists (Term f l'); split.
apply well_formed_fold; rewrite Af; subst; rewrite length_map; split; trivial.
simpl; rewrite Af; subst; trivial.
Qed.

Lemma length_flatten_bis :
forall f, arity f = AC ->
  forall l, (forall t, In t l -> well_formed_cf t) ->
 (length l) <= length (flatten f l).
Proof.
intros f Af l Wl; induction l as [ | t l].
simpl; auto with arith.
simpl; destruct t as [v | g ll].
simpl; apply le_n_S; apply IHl; intros; apply Wl; right; trivial.
generalize (F.Symb.eq_bool_ok f g); case (F.Symb.eq_bool f g); [intro f_eq_g | intro f_diff_g].
rewrite length_app; replace (S (length l)) with (1 + length l); trivial;
apply Nat.add_le_mono.
assert (Wt : well_formed_cf (Term g ll)). apply Wl; left; trivial.
unfold well_formed_cf in Wt; subst g; rewrite Af in Wt;
destruct Wt as [_ [Lll _]]; auto with arith.
apply IHl; intros; apply Wl; right; trivial.
simpl; apply le_n_S; apply IHl; intros; apply Wl; right; trivial.
Qed.

Lemma length_flatten :
  forall f, forall l, arity f = AC -> (forall u, In u l -> well_formed u) -> 
  length l <= length (flatten f (map canonical_form l)).
Proof.
intros f l; pattern l; apply (list_rec3 size); clear l; induction n;
destruct l as [ | t l]. 
simpl; trivial.
simpl; intro S_l; absurd (1 <= 0); auto with arith;
apply Nat.le_trans with (size t + list_size size l); trivial.
apply Nat.le_trans with (2 := Nat.le_add_r _ _), size_ge_one.
simpl; trivial.
intros Sl Af Wl;
replace (t :: l) with ((t :: nil) ++ l); trivial;
rewrite map_app; rewrite flatten_app; do 2 rewrite length_app;
apply Nat.add_le_mono.
assert (Wt : well_formed t). apply Wl; left; trivial.
destruct t as [v | g ll]; simpl; auto with arith.
generalize (F.Symb.eq_bool_ok f g); case (F.Symb.eq_bool f g); [intro f_eq_g | intro f_diff_g].
subst g; rewrite <- app_nil_end; rewrite Af; rewrite length_quicksort;
apply Nat.le_trans with (length ll).
elim (well_formed_unfold Wt); rewrite Af; intros _ Lll; rewrite Lll; auto with arith.
apply IHn; trivial.
apply le_S_n; 
apply Nat.le_trans with (size (Term f ll) + list_size size l); trivial;
rewrite size_unfold; simpl; apply le_n_S; apply Nat.le_add_r.
elim (well_formed_unfold Wt); rewrite Af; trivial.
apply le_n.
apply IHn; trivial.
apply Nat.add_le_mono_l with 1; 
apply Nat.le_trans with (size t + list_size size l); trivial;
apply Nat.add_le_mono_r; apply size_ge_one.
intros; apply Wl; right; trivial.
Qed.

Lemma well_formed_cf_is_well_formed_cf_conv :
 forall cf, (exists t, well_formed t /\ cf = canonical_form t) -> well_formed_cf cf.
Proof.
intros cf [t [Wt Ct]]; subst; generalize Wt; clear Wt.
pattern t; apply term_rec2; clear t; induction n as [ | n ];
intros t St Wt.
absurd (1 <= 0); auto with arith; 
apply Nat.le_trans with (size t); trivial; apply size_ge_one.
apply well_formed_cf_fold; destruct t as [ v | f l ]; simpl; trivial.
generalize (well_formed_unfold Wt); intros [Wl L].
assert (Wl' : forall t, In t (map canonical_form l)  -> well_formed_cf t).
clear Wt L; rewrite size_unfold in St; induction l as [ | t1 l ].
contradiction.
intros t In_t; elim In_t; clear In_t; intro In_t; subst.
apply IHn;
[ apply Nat.le_trans with (list_size size (t1 :: l)); simpl; auto with arith
| apply Wl; left; trivial ].
apply IHl; trivial;
[ apply Nat.le_trans with (1 + list_size size (t1 :: l)); simpl; auto with arith
| intros; apply Wl; right; trivial].
destruct_arity f a Af.
(* AC *)
split; [idtac | split; [idtac | split]].
intros u In_u; rewrite <- in_quick_in in In_u.
generalize (map canonical_form l) Wl' In_u;
clear l St Wt Wl L Wl' In_u;
intro l; induction l as [ | t l ]; intros Wl In_u.
contradiction.
assert (H:=flatten_app f (t :: nil) l); simpl app in H; rewrite H in In_u; clear H;
elim (in_app_or _ _ _ In_u); clear In_u; intro In_u.
assert (Wt : well_formed_cf t). apply Wl; left; trivial.
destruct t as [v | g h].
elim In_u; clear In_u; intro In_u; subst; trivial; contradiction.
revert In_u; generalize (F.Symb.eq_bool_ok f g); case (F.Symb.eq_bool f g); [intros f_eq_g In_u | intros f_diff_g In_u].
rewrite <- app_nil_end in In_u; apply (well_formed_cf_subterms Wt); trivial.
elim In_u; clear In_u; intro In_u; subst; trivial; contradiction.
apply IHl; trivial; intros; apply Wl; right; trivial.
rewrite length_quicksort; rewrite <- L; unfold ge; apply length_flatten; trivial.
apply quick_sorted.
intros u In_u; rewrite <- in_quick_in in In_u. 
generalize (map canonical_form l) In_u Wl'; clear l St Wt Wl L Wl' In_u; 
intro l; pattern l; apply (list_rec3 size); clear l; 
induction n0 as [ | m]; destruct l as [ | t l ].
contradiction.
intro H; absurd (1 <= 0); auto with arith; 
apply Nat.le_trans with (list_size size (t :: l)); trivial;
apply Nat.le_trans with (size t); simpl; auto with arith; apply size_ge_one.
contradiction.
assert (H:=flatten_app f (t :: nil) l); simpl app in H; rewrite H; clear H.
intros Sl In_u Wl; elim (in_app_or _ _ _ In_u); clear In_u; intro In_u.
assert (Wt : well_formed_cf t). apply Wl; left; trivial.
destruct t as [ v | g ll ].
elim In_u; clear In_u; intro In_u; subst; trivial; contradiction.
revert In_u; generalize (F.Symb.eq_bool_ok f g); case (F.Symb.eq_bool f g); [intros f_eq_g In_u | intros f_diff_g In_u].
subst g; rewrite <- app_nil_end in In_u;
apply well_formed_cf_alien with ll; trivial.
elim In_u; clear In_u; intro In_u; subst; trivial; contradiction.
apply (IHm l); trivial.
apply le_S_n; apply Nat.le_trans with (1 + list_size size l); auto with arith;
apply Nat.le_trans with (size t + list_size size l); trivial;
apply Nat.add_le_mono_r; apply size_ge_one.
intros; apply Wl; right; trivial.
(* C *)
split; [idtac | split].
intros u In_u; rewrite <- in_quick_in in In_u.
apply Wl'; trivial.
rewrite length_quicksort; rewrite length_map; trivial.
apply quick_sorted.
(* Free a *)
split; trivial; rewrite length_map; trivial.
Qed.

Lemma flatten_cf :
 forall f t1 t2, arity f = AC -> well_formed_cf t1 -> well_formed_cf t2 ->
 permut (flatten f (t1 :: nil)) (flatten f (t2 :: nil)) -> t1 = t2.
Proof.
intros f t1 t2 Af Wt1 Wt2; destruct t1 as [v1 | f1 l1]; destruct t2 as [v2 | f2 l2].
(* t1 = Var v1; t2 = Var v2 *)
simpl; intros; apply permut_length_1; trivial.
(* t1 = Var v1; t2 = Term f2 l2 *)
simpl; generalize (F.Symb.eq_bool_ok f f2); case (F.Symb.eq_bool f f2); [intros f_eq_f2; subst f2 | intros f_diff_f2].
rewrite <- app_nil_end; intro P; absurd (2 <= 1); auto with arith.
generalize (permut_length P); simpl;
intro L; pattern 1 at 2; rewrite L; auto with arith;
apply well_formed_cf_length with f; trivial.
intro P; apply permut_length_1; trivial.
(* t1 = Term f1 l1; t2 = Var v2 *)
simpl; generalize (F.Symb.eq_bool_ok f f1); case (F.Symb.eq_bool f f1); [intros f_eq_f1; subst f1 | intros f_diff_f1].
rewrite <- app_nil_end; intro P; absurd (2 <= 1); auto with arith.
generalize (permut_length P); simpl;
intro L; pattern 1 at 2; rewrite <- L; auto with arith;
apply well_formed_cf_length with f; trivial.
intro P; apply permut_length_1; trivial.
(* t1 = Term f1 l1; t2 = Term f2 l2 *)
simpl; generalize (F.Symb.eq_bool_ok f f1); case (F.Symb.eq_bool f f1); [intros f_eq_f1; subst f1 | intros f_diff_f1];
(generalize (F.Symb.eq_bool_ok f f2); case (F.Symb.eq_bool f f2); [intros f_eq_f2 P; subst f2 | intros f_diff_f2 P]).
(* f = f1; f = f2 *)
apply (f_equal (fun l => Term f l));
do 2 rewrite <- app_nil_end in P;
apply sort_is_unique; trivial; apply well_formed_cf_sorted with f; trivial.
(*  f = f1; f <> f2 *)
absurd (2 <= 1); auto with arith.
rewrite <- app_nil_end in P; generalize (permut_length P); simpl;
intro L; pattern 1 at 2; rewrite <- L; auto with arith;
apply well_formed_cf_length with f; trivial.
(* f <> f1; f = f2 *)
absurd (2 <= 1); auto with arith.
rewrite <- app_nil_end in P; generalize (permut_length P); simpl;
intro L; pattern 1 at 2; rewrite L; auto with arith;
apply well_formed_cf_length with f; trivial.
apply permut_length_1; trivial.
Qed.

Lemma flatten_cf_cf :
 forall f t1 t2, arity f = AC -> well_formed t1 -> well_formed t2 ->
 permut (flatten f (canonical_form t1 :: nil))
 (flatten f (canonical_form t2 :: nil)) ->
 canonical_form t1 = canonical_form t2.
Proof.
intros f t1 t2 Af Wt1 Wt2 P; 
apply flatten_cf with f; trivial.
apply well_formed_cf_is_well_formed_cf_conv; exists t1; split; trivial.
apply well_formed_cf_is_well_formed_cf_conv; exists t2; split; trivial.
Qed.

Definition build (f : symbol) l :=
  match l with
  | t :: nil => t
  | _ => Term f (quicksort l)
  end.

Lemma build_eq_Term :
forall f l, 2 <= length l -> build f l = Term f (quicksort l).
Proof.
intros f l Ll; destruct l as [ | u [ | v l]]; simpl; trivial.
simpl in Ll; absurd (2 <= 1); auto with arith.
Qed.

Lemma well_formed_cf_build :
 forall f l, arity f = AC ->
 1 <= length l ->
 (forall t, In t l -> well_formed_cf t) ->
 (forall t, In t l -> match t with | Var _ => True | Term g _ => f <> g end) ->
 well_formed_cf (build f l).
Proof.
intros f l Af Ll Wl Al; destruct l as [ | t1 [ | t2 l]].
simpl in Ll; absurd (1 <= 0); trivial; auto with arith.
apply Wl; left; trivial.
rewrite build_eq_Term; [idtac | simpl; auto with arith].
apply well_formed_cf_fold; split.
intros u In_u; rewrite <- in_quick_in in In_u.
apply Wl; trivial.
rewrite Af; split; [idtac | split].
rewrite length_quicksort; simpl; auto with arith.
apply quick_sorted.
intros u In_u; rewrite <- in_quick_in in In_u.
apply Al; trivial.
Qed.

Lemma well_formed_cf_build_cons :
 forall f t l, arity f = AC -> 
 well_formed_cf (Term f (t :: l)) -> well_formed_cf (build f l).
Proof.
intros f t l Af W; apply well_formed_cf_build; trivial.
apply le_S_n; replace (S (length l)) with (length (t :: l)); trivial;
apply well_formed_cf_length with f; trivial.
intros; apply (well_formed_cf_subterms W); right; trivial.
intros; apply (well_formed_cf_alien Af W); right; trivial.
Qed.

Lemma well_formed_cf_build_inside :
forall f t l1 l2, arity f = AC -> 
 well_formed_cf (Term f (l1 ++ t :: l2)) -> well_formed_cf (build f (l1 ++ l2)).
Proof.
intros f t l1 l2 Af W; 
assert (H : forall u, In u (l1 ++ l2) -> In u (l1 ++ t :: l2)).
intros u In_u; elim (in_app_or _ _ _ In_u); clear In_u; intro In_u; 
apply in_or_app; [ left | right; right ]; trivial.
apply well_formed_cf_build; trivial.
apply le_S_n; replace (S (length (l1 ++ l2))) with (length (l1 ++ t :: l2)).
apply well_formed_cf_length with f; trivial.
do 2 rewrite length_app; rewrite Nat.add_comm; simpl; 
rewrite Nat.add_comm; trivial.
intros u In_u; apply (well_formed_cf_subterms W); apply H; trivial.
intros u In_u; apply (well_formed_cf_alien Af W); apply H; trivial.
Qed.

Lemma flatten_build :
 forall f l, arity f = AC -> 
 (forall t, In t l -> match t with | Var _ => True | Term g _ => f <> g end) ->
 permut (flatten f ((build f l) :: nil)) l.
Proof.
intros f [ | t1 [ | t2 l]] Af Al.
simpl; generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); [intros _; apply Pnil | intro f_diff_f; apply False_rect; apply f_diff_f; reflexivity].
assert (Al_t1 := Al _ (or_introl _ (eq_refl _))).
simpl; destruct t1 as [ | g]; [auto | idtac].
generalize (F.Symb.eq_bool_ok f g); case (F.Symb.eq_bool f g); [intros f_eq_g | intros _].
apply False_rect; apply Al_t1; assumption.
reflexivity.
simpl; generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); [intros _ | intro f_diff_f; apply False_rect; apply f_diff_f; reflexivity].
rewrite <- app_nil_end; apply quick_permut_bis; auto.
Qed.

Lemma flatten_build_cons :
 forall f t l, arity f = AC -> well_formed_cf (Term f (t :: l)) -> 
 permut (flatten f ((build f l) :: nil)) l.
Proof.
intros f t l Af W; apply flatten_build; trivial.
intros; apply (well_formed_cf_alien Af W); right; trivial.
Qed.

Lemma flatten_build_inside :
 forall f t l1 l2, arity f = AC -> 
 well_formed_cf (Term f (l1 ++ t :: l2)) ->
 permut (flatten f ((build f (l1 ++ l2)) :: nil)) (l1 ++ l2).
Proof.
intros f t l1 l2 Af W; 
apply flatten_build; trivial.
intros u In_u; apply (well_formed_cf_alien Af W);
elim (in_app_or _ _ _ In_u); clear In_u; 
intro In_u; apply in_or_app; [left | right; right]; trivial.
Qed.

(** ** Substitutions modulo AC *)
Definition is_subst_canonical_form sigma sigma_cf :=
  forall v, match find X.eq_bool v sigma with
    | None => find X.eq_bool v sigma_cf = None
    | Some v_sigma => 
        find X.eq_bool v sigma_cf = Some (canonical_form v_sigma)
  end.

Lemma is_subst_cf_is_subst_cf :
  forall sigma, is_subst_canonical_form sigma (map_subst (fun _ t => canonical_form t) sigma).
Proof.
intros sigma; unfold is_subst_canonical_form.
intro v; rewrite subst_comp_is_subst_comp_aux1.
destruct (find X.eq_bool v sigma); trivial.
Qed.

Definition well_formed_cf_subst sigma := 
  forall v, match find X.eq_bool v sigma with
	    | None => True
	    | Some t => well_formed_cf t
	    end.

Lemma well_formed_cf_subst_is_well_formed_cf_subst_aux :
 forall sigma, well_formed_cf_subst sigma ->
 (forall v, nb_occ X.eq_bool v sigma <= 1) ->
  exists sigma', well_formed_subst sigma' /\ 
  is_subst_canonical_form sigma' sigma.
Proof.
unfold well_formed_cf_subst, is_subst_canonical_form; 
intros sigma Wsigma Nb_occ_sigma; induction sigma as [ | [v1 t1] sigma].
exists (nil : substitution); split; trivial; intro v; simpl; trivial.
elim IHsigma.
intros sigma' [Wsigma' Hsigma']; assert (Wt1 : well_formed_cf t1).
generalize (Wsigma v1); simpl; 
generalize (X.eq_bool_ok v1 v1); case (X.eq_bool v1 v1); [ intros _ | intros v1_diff_v1]; trivial; 
absurd (v1=v1); trivial.
elim (well_formed_cf_is_well_formed_cf _ Wt1); intros u1 [Wu1 Hu1];
exists ((v1,u1)::sigma'); split; intro v; simpl; case (X.eq_bool v v1); trivial.
apply Wsigma'.
subst; trivial.
apply Hsigma'.

intro v; generalize (Wsigma v) (Nb_occ_sigma v); simpl; case (X.eq_bool v v1); trivial.
generalize (some_nb_occ_Sn X.eq_bool v sigma); case (find X.eq_bool v sigma).
intros t H; generalize (H _ (eq_refl _)); clear H; intros H _ H'.
destruct (nb_occ X.eq_bool v sigma) as [ | no];
[ absurd (1 <= 0) | absurd (S(S no) <= 1) ]; auto with arith.
intros; exact I.
intro v; generalize (Nb_occ_sigma v); simpl;
case (X.eq_bool v v1); trivial; auto with arith.
Qed.

Lemma well_formed_cf_subst_is_well_formed_cf_subst :
 forall sigma, well_formed_cf_subst sigma ->
  exists sigma', well_formed_subst sigma' /\ 
                        is_subst_canonical_form sigma' sigma.
Proof.
assert (E : equivalence _ (@eq variable)).
repeat split.
intros t1 t2 t3 H1 H2; subst; reflexivity.
intros t1 t2 H; subst; reflexivity.
intros sigma Wsigma;
elim (reduce_assoc_list _ X.eq_bool_ok E sigma);
intros sigma1 [Nb_occ H];
elim (well_formed_cf_subst_is_well_formed_cf_subst_aux (sigma := sigma1));
trivial.
intros sigma' [Wsigma' H']; exists sigma'; split; trivial;
intro v; rewrite H; apply H'.
intro v; rewrite <- H; apply Wsigma. 
Qed.

Fixpoint apply_cf_subst (sigma : substitution) (t : term) {struct t} : term :=
  match t with
  | Var v => 
    match find X.eq_bool v sigma with
    | None => t
    | Some v_sigma => v_sigma
    end
  | Term f l => 
     let l_sigma := 
       match arity f with
       | AC => quicksort (flatten f (map (apply_cf_subst sigma) l))
       | C => quicksort (map (apply_cf_subst sigma) l)
       | Free _ => map (apply_cf_subst sigma) l
     end in
   Term f l_sigma
 end.

Lemma flatten_apply_cf_subst :
 forall sigma f l, arity f = AC ->
  permut (flatten f (map (apply_cf_subst sigma) l))
  (flatten f (apply_cf_subst sigma (build f l) :: nil)).
Proof.
intros sigma f l Af; induction l as [ | t1 l].
simpl; generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); [intros _ | intro f_diff_f; apply False_rect; apply f_diff_f; reflexivity].
rewrite Af; repeat rewrite quicksort_equation; simpl; auto.
destruct l as [ | t2 l]; auto.
simpl; rewrite Af; 
generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); [intros _ | intro f_diff_f; apply False_rect; apply f_diff_f; reflexivity].
rewrite <- app_nil_end; apply permut_sym; 
apply quick_permut_bis;
transitivity (flatten f (map (apply_cf_subst sigma) (t1 :: t2 :: l))); auto;
apply list_permut_flatten.
apply permut_map with (@eq term).
intros; subst; reflexivity.
apply permut_sym; apply quick_permut.
Qed.

Theorem apply_cf_subst_is_sound :
  forall sigma sigma_cf, is_subst_canonical_form sigma sigma_cf ->
  forall t, apply_cf_subst sigma_cf (canonical_form t) = 
               canonical_form (apply_subst sigma t).
Proof.
intros sigma sigma_cf H t; pattern t; apply term_rec3; clear t.

intro v; generalize (H v); simpl; 
destruct (find X.eq_bool v sigma) as [t | ]; 
intro H_v; rewrite H_v; trivial.

intros f l IH; 
assert (IHl : map (apply_cf_subst sigma_cf) (map canonical_form l) =
 map canonical_form (map (apply_subst sigma) l)). 
induction l as [ | t l]; trivial.
simpl map; rewrite IHl. rewrite IH; [ idtac | left ]; trivial.
intros; apply IH; right; trivial.
simpl; apply (f_equal (fun l => Term f l)).
destruct_arity f a Af.
(* AC*)
apply sort_is_unique; [apply quick_sorted | apply quick_sorted | idtac];
apply quick_permut_bis; apply permut_sym; apply quick_permut_bis;
transitivity
  (flatten f (map (apply_cf_subst sigma_cf) 
             (flatten f (map canonical_form l)))).
rewrite <- IHl; generalize (map canonical_form l); clear l IHl IH.
intro l; induction l as [ | t l]; auto.
replace (t :: l) with ((t :: nil) ++ l); trivial.
rewrite map_app; do 2 rewrite flatten_app; 
rewrite map_app; rewrite flatten_app;
transitivity 
  (flatten f (map (apply_cf_subst sigma_cf) (t :: nil)) ++
   flatten f (map (apply_cf_subst sigma_cf) (flatten f l))).
rewrite <- permut_app1; apply IHl.
rewrite <- permut_app2.
destruct t as [ v | g ll]; simpl; auto.
generalize (F.Symb.eq_bool_ok f g); case (F.Symb.eq_bool f g); [intros f_eq_g; subst g | intros f_diff_g].
rewrite Af; do 2 rewrite <- app_nil_end; 
apply permut_sym; apply quick_permut.
simpl; generalize (F.Symb.eq_bool_ok f g); case (F.Symb.eq_bool f g); [intros f_eq_g; subst g | intros _].
apply False_rect; apply f_diff_g; reflexivity.
reflexivity.
apply list_permut_flatten; apply permut_map with (@eq term).
intros; subst; reflexivity.
apply quick_permut.
(* C *)
apply sort_is_unique; [apply quick_sorted | apply quick_sorted | idtac];
do 2 (apply quick_permut_bis; apply permut_sym); rewrite <- IHl.
apply permut_map with (@eq term).
intros; subst; reflexivity.
apply quick_permut_bis; auto.
(* Free a *)
trivial.
Qed.

Theorem well_formed_cf_apply_subst :
  forall sigma, well_formed_cf_subst sigma -> 
  forall t, well_formed_cf t -> well_formed_cf (apply_cf_subst sigma t).
Proof.
intros sigma Wsigma t Wt;
elim (well_formed_cf_is_well_formed_cf _ Wt); 
intros u [Wu Hu]; subst;
elim (well_formed_cf_subst_is_well_formed_cf_subst Wsigma);
intros tau [Wtau Htau];
rewrite apply_cf_subst_is_sound with tau sigma u; trivial;
apply well_formed_cf_is_well_formed_cf_conv;
exists (apply_subst tau u); split; trivial;
apply well_formed_apply_subst; trivial.
Qed.

Lemma length_flatten_ter :
forall f sigma, arity f = AC -> well_formed_cf_subst sigma ->
  forall l, (forall t, In t l -> well_formed_cf t) ->
  length l <= length (flatten f (map (apply_cf_subst sigma) l)).
Proof.
intros f sigma Af Wsigma l Wl; induction l as [ | t l]; trivial.
replace (t::l) with ((t::nil) ++ l); trivial;
rewrite map_app; rewrite flatten_app; 
do 2 rewrite length_app; apply Nat.add_le_mono.
assert (Wtsigma : well_formed_cf (apply_cf_subst sigma t)).
apply well_formed_cf_apply_subst; trivial; apply Wl; left; trivial.
simpl map;
destruct (apply_cf_subst sigma t) as [ v | g ll ]; simpl; trivial;
simpl; generalize (F.Symb.eq_bool_ok f g); case (F.Symb.eq_bool f g); [intros f_eq_g; subst g | intros _]; trivial.
rewrite <- app_nil_end;
apply Nat.le_trans with 2; auto with arith;
apply well_formed_cf_length with f; trivial.
apply IHl; intros; apply Wl; right; trivial.
Qed.

(** ** Canonical forms and equality modulo AC *)
Lemma ac_one_step_at_top_cf_eq :
  forall t1 t2, ac_one_step_at_top t1 t2 -> canonical_form t1 = canonical_form t2.
Proof.
assert (P12 : forall t1 t2, permut (t1 :: t2 :: nil) (t2 :: t1 :: nil)). 
intros t1 t2; 
replace (t1 :: t2 :: nil) with ((t1 :: nil) ++ (t2 :: nil)); trivial;
replace (t2 :: t1 :: nil) with ((t2 :: nil) ++ (t1 :: nil)); trivial;
apply list_permut_app_app.
assert (Ccase : forall f, arity f = C \/ arity f = AC -> forall t1 t2,
canonical_form (Term f (t1 :: t2 :: nil)) =
canonical_form (Term f (t2 :: t1 :: nil))).
intros f [Af | Af] t1 t2; simpl; rewrite Af; apply (f_equal (fun l => Term f l));
apply sort_is_unique; try apply quick_sorted; 
do 2 (apply quick_permut_bis; apply permut_sym).
(* C case *) 
apply P12.
(* AC case *)
destruct (canonical_form t1) as [v1 | f1 ll1];
destruct (canonical_form t2) as [v2 | f2 ll2].
apply P12.
case (F.Symb.eq_bool f f2);
[ rewrite <- permut_cons_inside; auto 
| apply P12 ].
reflexivity.
case (F.Symb.eq_bool f f1);
[ apply permut_sym; rewrite <- permut_cons_inside; auto 
| apply P12 ].
reflexivity.
case (F.Symb.eq_bool f f1); case (F.Symb.eq_bool f f2).
do 2 rewrite <- app_nil_end; apply list_permut_app_app.
apply permut_sym; rewrite <- permut_cons_inside; auto.
reflexivity.

rewrite <- permut_cons_inside; auto.
reflexivity.
apply P12.

assert (ACcase : forall f, arity f = AC -> forall t1 t2 t3,
canonical_form (Term f (Term f (t1 :: t2 :: nil) :: t3 :: nil)) =
canonical_form (Term f (t1 :: Term f (t2 :: t3 :: nil) :: nil))).
intros f Af t1 t2 t3; simpl; rewrite Af; 
generalize (F.Symb.eq_bool_ok f f); case (F.Symb.eq_bool f f); [intros _ | intro f_diff_f; apply False_rect; apply f_diff_f; reflexivity].
apply (f_equal (fun l => Term f l)); apply sort_is_unique.
apply quick_sorted.
apply quick_sorted.
do 2 (apply quick_permut_bis; apply permut_sym).
generalize (canonical_form t1) (canonical_form t2) (canonical_form t3);
clear t1 t2 t3; intros t1 t2 t3; rewrite <- app_nil_end.
transitivity ((flatten f (t1 :: t2 :: nil)) ++ (flatten f (t3 :: nil))). 
rewrite <- permut_app2.
apply permut_sym; apply quick_permut.
transitivity ((flatten f (t1 :: nil)) ++ (flatten f (t2 :: t3 :: nil))). 
do 2 rewrite <- flatten_app; simpl app; apply permut_refl.
destruct t1 as [v1 | g1 ll1].
simpl; rewrite <- permut_cons.
apply quick_permut.
reflexivity.
simpl; case (F.Symb.eq_bool f g1).
rewrite <- app_nil_end; rewrite <- permut_app1; apply quick_permut.
simpl; rewrite <- permut_cons.
apply quick_permut.
reflexivity. 
intros t1 t2 H; destruct H; auto; apply sym_eq; auto.
Qed.

Lemma sym_refl_ac_one_step_at_top_cf_eq :
  forall t1 t2, (sym_refl ac_one_step_at_top) t1 t2 -> canonical_form t1 = canonical_form t2.
Proof.
intros t1 t2; unfold sym_refl; intros [H | [H | H]].
apply ac_one_step_at_top_cf_eq; trivial.
apply sym_eq; apply ac_one_step_at_top_cf_eq; trivial.
subst; trivial.
Qed.

Lemma ac_one_step_cf_eq :
  forall t1 t2, one_step (sym_refl ac_one_step_at_top) t1 t2 -> canonical_form t1 = canonical_form t2.
Proof.
intros t1; pattern t1; apply term_rec3; clear t1.
intros v1 t2 H; inversion_clear H as [H1 H2 H' | f l1 l2 H']. 
apply sym_refl_ac_one_step_at_top_cf_eq; apply no_need_of_instance; trivial.
intros f l1 IHl1 t2 H; 
inversion_clear H as [ H1 H2 Hroot | H1 H2 l2 Hsub].
apply sym_refl_ac_one_step_at_top_cf_eq; apply no_need_of_instance; trivial.
assert (H : map canonical_form l1 = map canonical_form l2).
generalize l2 Hsub; clear l2 Hsub; induction l1 as [ | t1 l1]; 
intros l2 Hsub; inversion_clear Hsub.
simpl; apply (f_equal (fun t => t :: map canonical_form l1));
apply IHl1; trivial; left; trivial.
simpl; apply (f_equal (fun l => canonical_form t1 :: l));
apply IHl0; trivial; intros; apply IHl1; trivial; right; trivial.

simpl; rewrite H; trivial.
Qed.

Theorem ac_cf_eq :
  forall t1 t2, ac t1 t2 -> canonical_form t1 = canonical_form t2.
Proof.
unfold ac, th_eq;
intros t1 t2 H.
refine (rwr_inv _ _ _ _ (@trans_eq term) _ _ _ H).
clear t1 t2 H; intros t1 t2 H; apply ac_one_step_cf_eq; trivial.
Qed.

Lemma ac_one_step_at_top_size_eq :
  forall t1 t2, ac_one_step_at_top t1 t2 -> size t1 = size t2.
Proof.
intros t1 t2 H; destruct H; simpl; repeat rewrite Nat.add_0_r; auto with arith;
rewrite (Nat.add_comm (size t1) (S (size t2 + size t3))); simpl;
apply (f_equal (fun n => S (S n)));
rewrite <- (Nat.add_assoc (size t1) (size t2) (size t3)); apply Nat.add_comm.
Qed.

Lemma sym_refl_ac_one_step_at_top_size_eq :
  forall t1 t2, (sym_refl ac_one_step_at_top) t1 t2 -> size t1 = size t2.
Proof.
intros t1 t2; unfold sym_refl; intros [H | [H | H]].
apply ac_one_step_at_top_size_eq; trivial.
apply sym_eq; apply ac_one_step_at_top_size_eq; trivial.
subst; trivial.
Qed.

Lemma ac_one_step_size_eq :
  forall t1 t2, one_step (sym_refl ac_one_step_at_top) t1 t2 -> size t1 = size t2.
Proof.
intros t1; pattern t1; apply term_rec3; clear t1.
intros v1 t2 H; inversion_clear H as [H1 H2 H' | f l1 l2 H']. 
apply sym_refl_ac_one_step_at_top_size_eq; apply no_need_of_instance; trivial.
intros f l1 IHl1 t2 H; 
inversion_clear H as [ H1 H2 Hroot | H1 H2 l2 Hsub].
apply sym_refl_ac_one_step_at_top_size_eq; apply no_need_of_instance; trivial.
assert (H : list_size size l1 = list_size size l2).
generalize l2 Hsub; clear l2 Hsub; induction l1 as [ | t1 l1]; 
intros l2 Hsub; inversion_clear Hsub.
simpl; apply (f_equal (fun n => n + list_size size l1));
apply IHl1; trivial; left; trivial.
simpl; apply (f_equal (fun n => size t1 + n));
apply IHl0; trivial; intros; apply IHl1; trivial; right; trivial.
do 2 rewrite size_unfold; rewrite H; trivial.
Qed.

Lemma ac_size_eq :
  forall t1 t2, ac t1 t2 -> size t1 = size t2.
Proof.
intros t1 t2 H; refine (rwr_inv _ _ _ _ (@trans_eq nat) _ _ _ H).
intros; apply ac_one_step_size_eq; trivial.
Qed.

Fixpoint ac_size (t:term) : nat :=
  match t with
  | Var v => 1
  | Term f l => 
       let ac_size_list :=
         (fix ac_size_list (l : list term) {struct l} : nat :=
            match l with
            | nil => 0
            | t :: lt => ac_size t + ac_size_list lt
            end) in
     (match arity f with
      | AC => (length l) - 1
      | C => 1
      | Free _ => 1
      end) + ac_size_list l
   end.

Lemma ac_size_unfold :
  forall t, 
  ac_size t = match t with
              | Var _ => 1
              | Term f l =>
                (match arity f with
                | AC => (length l) - 1
                | C => 1
                | Free _ => 1
                end) + list_size ac_size l
               end.
Proof.
intro t; destruct t as [v | f l]; trivial; simpl.
apply (f_equal (fun n => (match arity f with
                                        | AC => length l - 1
                                        | C => 1 
                                        | Free _ => 1
                                        end) + n)); 
induction l as [ | t l]; trivial.
simpl; rewrite <- IHl; generalize (ac_size t);
clear f t IHl; induction l as [ | t l]; simpl; trivial;
intro n; rewrite (IHl (n + ac_size t)); rewrite (IHl (ac_size t));
auto with arith.
Qed.

Lemma size_size_aux2 :
 forall f t, arity f = AC -> well_formed t ->
 ac_size (canonical_form t) = 
 list_size ac_size (flatten f (canonical_form t :: nil)) +
 (length (flatten f (canonical_form t :: nil))) - 1.
Proof.
intros f t Af Wt; assert (Wu : well_formed_cf (canonical_form t)).
apply well_formed_cf_is_well_formed_cf_conv; exists t; split; trivial.
generalize (canonical_form t) Wu; clear t Wt Wu; intros u Wu.
destruct u as [v | g l]; trivial; simpl.
simpl; generalize (F.Symb.eq_bool_ok f g); case (F.Symb.eq_bool f g); [intros f_eq_g; subst g | intros f_diff_g].
rewrite Af; rewrite <- app_nil_end;
generalize (well_formed_cf_length Af Wu); intro Ll;
destruct (length l) as [ | n].
absurd (2 <= 0); auto with arith.
rewrite (Nat.add_comm (list_size ac_size l)); simpl;
do 2 rewrite Nat.sub_0_r; trivial.
simpl; rewrite (list_size_fold ac_size); trivial.
simpl; rewrite Nat.add_0_r; apply sym_eq;
rewrite Nat.add_comm; simpl;
rewrite Nat.sub_0_r; trivial.
Qed.

Lemma size_size_aux3 :
 forall f t, arity f = AC -> well_formed t ->
 1 <= length (A:=term) (flatten f (canonical_form t :: nil)).
Proof.
intros f t Ar Wt; apply (length_flatten (t :: nil) Ar);
intros u In_u; elim In_u; clear In_u; intro In_u.
subst u; trivial.
contradiction.
Qed.

Lemma size_size :
 forall t, well_formed t -> size t = ac_size (canonical_form t).
Proof.
intros t; pattern t; apply term_rec3; clear t.
intros v _; trivial.
intros f l H Wt; destruct (well_formed_unfold Wt) as [Wl Ll].
assert (Hl : forall t, In t l -> size t = ac_size (canonical_form t)).
intros; apply H; trivial; apply Wl; trivial.
clear H Wt;
assert (Hl' : list_size size l = list_size ac_size (map canonical_form l)).
clear Ll; induction l as [ | t l]; trivial.
simpl; rewrite (Hl t (or_introl _ (eq_refl _))); rewrite IHl; trivial.
intros; apply Wl; right; trivial.
intros; apply Hl; right; trivial.
simpl; rewrite (list_size_fold size); rewrite (list_size_fold ac_size);
destruct_arity f n Af.
assert (Dummy : DOS.A = term).
apply eq_refl.
rewrite length_quicksort.
assert (Dummy2 : forall l, @length DOS.A l = @length term l).
intro k; apply eq_refl.
rewrite Dummy2.
replace (list_size ac_size (quicksort (flatten f (map canonical_form l))))
with (list_size ac_size (flatten f (map canonical_form l))).
destruct l as [ | t1 [ | t2 [ | t3 l]]];
[absurd (0 = 2) | absurd (1 = 2) | idtac | absurd (S(S(S(length l))) = 2)];
auto with arith.
simpl map; simpl list_size;
rewrite Nat.add_0_r;
rewrite (Hl t1 (or_introl _ (eq_refl _)));
rewrite (Hl t2 (or_intror _ (or_introl _ (eq_refl _)))).
assert (W1 : well_formed_cf (canonical_form t1)).
apply well_formed_cf_is_well_formed_cf_conv; 
exists t1; split; trivial; apply Wl; left; trivial.
assert (W2 : well_formed_cf (canonical_form t2)).
apply well_formed_cf_is_well_formed_cf_conv; 
exists t2; split; trivial; apply Wl; right; left; trivial.
destruct (canonical_form t1) as [v1 | f1 ll1];
destruct (canonical_form t2) as [v2 | f2 ll2]; trivial.
simpl flatten;
generalize (F.Symb.eq_bool_ok f f2); case (F.Symb.eq_bool f f2); [intros f_eq_f2; subst f2 | intros f_diff_f2].
simpl; rewrite <- app_nil_end; simpl; rewrite Af.
rewrite (list_size_fold ac_size); rewrite Nat.sub_0_r.
generalize (well_formed_cf_length Af W2).
intro Lll2; destruct (length ll2) as [ | n2].
absurd (2 <= 0); auto with arith.
simpl; rewrite Nat.sub_0_r;
apply sym_eq; rewrite Nat.add_comm; simpl; rewrite Nat.add_comm; trivial.
simpl; rewrite Nat.add_0_r; trivial.
simpl flatten;
generalize (F.Symb.eq_bool_ok f f1); case (F.Symb.eq_bool f f1); [intros f_eq_f1; subst f1 | intros f_diff_f1].
simpl; rewrite Af; rewrite (list_size_fold ac_size).
generalize (well_formed_cf_length Af W1);
intro Lll1; rewrite length_app; destruct (length ll1) as [ | n1].
absurd (2 <= 0); auto with arith.
rewrite list_size_app; simpl; do 2 rewrite Nat.sub_0_r;
rewrite (Nat.add_comm n1 1); simpl; rewrite Nat.add_assoc; trivial.
trivial.
replace (flatten f (Term f1 ll1 :: Term f2 ll2 :: nil)) with
   ((flatten f (Term f1 ll1 :: nil)) ++ (flatten f (Term f2 ll2 :: nil))).
rewrite length_app.
simpl; generalize (F.Symb.eq_bool_ok f f1); case (F.Symb.eq_bool f f1); [intros f_eq_f1; subst f1 | intros f_diff_f1];
(generalize (F.Symb.eq_bool_ok f f2); case (F.Symb.eq_bool f f2); [intros f_eq_f2; subst f2 | intros f_diff_f2]).
do 2 rewrite <- app_nil_end; rewrite Af;
do 2 rewrite (list_size_fold ac_size); rewrite list_size_app.
unfold DOS.A in *; generalize (well_formed_cf_length Af W1);
intro Lll1; destruct (length ll1) as [ | n1].
absurd (2 <= 0); auto with arith.
unfold DOS.A in *; generalize (well_formed_cf_length Af W2);
intro Lll2; destruct (length ll2) as [ | n2].
absurd (2 <= 0); auto with arith.
simpl; do 3 rewrite Nat.sub_0_r;
rewrite (Nat.add_comm n1 (S n2)); simpl; rewrite (Nat.add_comm n2 n1);
do 2 rewrite <- Nat.add_assoc; apply (f_equal (fun n => S (n1 + n)));
rewrite Nat.add_comm; rewrite <- Nat.add_assoc;
apply (f_equal (fun n => n2 + n)); apply Nat.add_comm.

rewrite Af; rewrite <- app_nil_end; rewrite list_size_app; simpl;
do 2 rewrite (list_size_fold ac_size); simpl; rewrite Nat.add_0_r;
rewrite (Nat.add_comm (length ll1) 1); simpl; rewrite Nat.sub_0_r;
unfold DOS.A in *; generalize (well_formed_cf_length Af W1);
intro Lll1; destruct (length ll1) as [ | n1].
absurd (2 <= 0); auto with arith.
simpl; rewrite Nat.sub_0_r; rewrite <- Nat.add_assoc; trivial.

rewrite Af; rewrite <- app_nil_end.
do 2 rewrite (list_size_fold ac_size).
unfold DOS.A in *; generalize (well_formed_cf_length Af W2);
intro Lll2; destruct (length ll2) as [ | n2].
absurd (2 <= 0); auto with arith.
simpl minus;  rewrite Nat.sub_0_r; simpl plus; do 3 rewrite Nat.add_assoc;
apply (f_equal (fun n => S (n + list_size ac_size ll2))).
rewrite Nat.add_comm; rewrite Nat.add_assoc; rewrite (list_size_fold ac_size); trivial.

simpl; rewrite Nat.add_0_r; trivial.
rewrite <- flatten_app; simpl app; trivial.
apply permut_size with (@eq term).
intros; subst; trivial.
apply quick_permut.

rewrite Hl'; simpl; apply (f_equal S).
apply permut_size with (@eq term).
intros; subst; trivial.
apply quick_permut.
rewrite Hl'; simpl; trivial.
Qed.

Lemma ac_size_ge_one :
  forall t, well_formed_cf t -> 1 <= ac_size t.
Proof.
intros t Wt; elim (well_formed_cf_is_well_formed_cf _ Wt);
intros u [Wu Hu]; subst; rewrite <- size_size; trivial;
apply size_ge_one.
Qed.

End Make'.

Module Make (T1: Term) 
(OF1 : ordered_set.S with Definition A := T1.symbol) 
(OX1 : ordered_set.S with Definition A := T1.variable) : 
S with Module EqTh.T := T1 := Make' T1 OF1 OX1. 
