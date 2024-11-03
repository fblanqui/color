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


From Coq Require Import Sumbool Arith Wf_nat Wellfounded List Multiset Relations.
From CoLoR Require Import closure decidable_set ordered_set more_list list_permut list_set list_sort dickson term_spec term.

Lemma Dummy_bool : forall b, negb b = true <-> b = false.
Proof.
intros [ | ]; intuition.
Qed.

Module Make (T1: Term) 
(OF1 : ordered_set.S with Definition A := T1.symbol) 
(OX1 : ordered_set.S with Definition A := T1.variable).

Module T := T1.
Import T1.

Import F.
Import X.

Inductive exc (A : Type) : Type :=
  | Normal : A -> exc A
  | Not_appliable : A -> exc A
  | No_solution : exc A.

Definition bind (A : Type) (f : A -> exc A)  (x : exc A) : (exc A) :=
  match x with
  | Normal _ a => f a
  | Not_appliable _ a => Not_appliable A a
  | No_solution _ => @No_solution A
  end.

Record unification_problem : Type :=
  mk_pb 
  {
    solved_part : substitution;
    unsolved_part : list (term * term)
  }.

Fixpoint combine A (l : list (A * A))  (l1 l2 : list A) {struct l1} : list (A * A) :=
  match l1, l2 with
  | nil, _ => l
  | _, nil => l
  | (a1 :: l1), (a2 :: l2) => combine _ ((a1,a2) :: l) l1 l2
  end.

Definition lt_ge_dec : forall x y, {x < y} + {x >= y} :=
  fun n m => Sumbool.sumbool_not _ _ (le_lt_dec m n).

Definition decomposition_step (pb : unification_problem) : exc unification_problem :=
   match pb.(unsolved_part) with
   | nil => @Not_appliable _ pb
   | (s,t) :: l =>
      if T.eq_bool s t 
      then Normal _ (mk_pb pb.(solved_part) l)
      else
      match s, t with
      | Var x, Var y => 
        let x_maps_to_y := (x, t) :: nil in
        let solved_part' := 
            map_subst (fun _ v_sigma => apply_subst ((x,t) :: nil) v_sigma) 
                              pb.(solved_part) in
        let l' := map (fun uv => 
                              match uv with
                              | (u, v) => (apply_subst ((x,t) :: nil) u,
                                                  apply_subst ((x,t) :: nil) v)
                             end) l in
         match find X.eq_bool x solved_part' with
         | Some x_val => Normal _ (mk_pb ((x, t) :: solved_part') ((t, x_val) :: l'))
         | None => Normal _ (mk_pb ((x, t) :: solved_part') l')
         end
      | Var x, (Term _ _ as u) => 
       match find X.eq_bool x pb.(solved_part) with
        | None => Normal _ (mk_pb ((x,u) :: pb.(solved_part)) l)
        | Some x_val => 
          if lt_ge_dec (T.size u) (T.size x_val) 
          then (* u < x_val *) Normal _ (mk_pb ((x,u) :: pb.(solved_part)) ((x_val,u) :: l))
          else (* x_val <= u *) Normal _ (mk_pb pb.(solved_part) ((x_val,u) :: l))
        end
      | (Term _ _ as u), Var x => 
        match find X.eq_bool x pb.(solved_part) with
        | None => Normal _ (mk_pb ((x,u) :: pb.(solved_part)) l)
        | Some x_val => 
          if lt_ge_dec (T.size u)  (T.size x_val) 
          then Normal _ (mk_pb ((x,u) :: pb.(solved_part)) ((x_val,u) :: l))
          else Normal _ (mk_pb pb.(solved_part) ((x_val,u) :: l))
        end
      | Term f l1, Term g l2 => 
         if F.Symb.eq_bool f g
         then 
             match Nat.eqb (length l1) (length l2) with
             | true => Normal _ (mk_pb pb.(solved_part) (combine _ l l1 l2))
             | false => @No_solution _
             end
         else @No_solution _
      end
   end.

Definition is_a_solution pb theta :=
  (forall s t, In (s,t) pb.(unsolved_part) -> apply_subst theta s = apply_subst theta t)
  /\
 (forall x, match find X.eq_bool x pb.(solved_part) with
               | Some x_val => apply_subst theta (Var x) = apply_subst theta x_val
               | None => True
               end).

Module DecVar := decidable_set.Convert (X).
Module VSet <: list_set.S with Definition EDS.A := variable :=
   list_set.Make (DecVar).

Ltac destruct_set S S1 S2 :=  
destruct (VSet.union_12 _ _ _ S) as [S1 | S2]; clear S.

Fixpoint set_of_variables (t : term) : VSet.t := 
  match t with
  | Var v => VSet.singleton v
  | Term _ l => 
        let set_of_variables_list :=
        (fix set_of_variables_list (l : list term) {struct l} : VSet.t :=
        match l with
        | nil => VSet.empty
        | t :: lt => VSet.union (set_of_variables t) (set_of_variables_list lt)
        end) in
        set_of_variables_list l
end.

Fixpoint set_of_variables_list (l : list term) : VSet.t :=
  match l with
  | nil => VSet.empty
  | t :: lt => VSet.union (set_of_variables t) (set_of_variables_list lt)
  end.

Fixpoint set_of_variables_in_unsolved_part (l : list (term * term)) : VSet.t :=
  match l with
  | nil => VSet.empty
  | (s,t) :: l => VSet.union (VSet.union (set_of_variables s) (set_of_variables t)) 
                           (set_of_variables_in_unsolved_part l)
  end.

Fixpoint domain_of_subst (sigma : substitution) : VSet.t :=
   match sigma with
   | nil => VSet.empty
   | (x,_) :: sigma => VSet.add x (domain_of_subst sigma)
   end.

Fixpoint set_of_variables_in_range_of_subst (sigma : substitution) : VSet.t :=
   match sigma with
   | nil => VSet.empty
   | (_,t) :: sigma => VSet.union (set_of_variables t) 
                                       (set_of_variables_in_range_of_subst sigma)
   end.

Lemma var_in_domain_of_subst :
  forall v sigma,
   VSet.mem v (domain_of_subst sigma) <-> (find X.eq_bool v sigma <> None).
Proof.
intros v sigma; induction sigma as [ | [x t] sigma]; simpl; split; intro H.
contradiction.
apply H; reflexivity.
generalize (X.eq_bool_ok v x); case (X.eq_bool v x); [intro v_eq_x | intro v_diff_x].
discriminate.
rewrite <- IHsigma.
destruct (VSet.add_12 _ _ _ H) as [v_eq_x | v_in_dom]; [idtac | assumption].
absurd (v = x); trivial.
revert H; generalize (X.eq_bool_ok v x); case (X.eq_bool v x); [intros v_eq_x _ | intros v_diff_x H].
subst x; apply VSet.add_1.
apply VSet.add_2; rewrite IHsigma; assumption.
Qed.

Lemma apply_subst_outside_dom :
  forall sigma t, VSet.eq_set (VSet.inter (domain_of_subst sigma) (set_of_variables t))
                            VSet.empty ->
                        apply_subst sigma t = t.
Proof.
intros sigma t; pattern t; apply term_rec3; clear t.
intros v; induction sigma as [ | [x t] sigma]; trivial.
intro; simpl.
generalize (X.eq_bool_ok v x); case (X.eq_bool v x); [intro v_eq_x | intro v_diff_x].
subst v; assert (H' : VSet.mem x VSet.empty).
rewrite <-  (H x); apply VSet.inter_12; 
[ simpl; apply VSet.add_1 | left; reflexivity].
contradiction.
apply IHsigma; intro z; split; [intro z_in_x_dom_sig | intro z_in_empty].
rewrite <- (H z); apply VSet.inter_12.
simpl; apply VSet.add_2; apply (VSet.inter_1 _ _ _ z_in_x_dom_sig).
apply (VSet.inter_2 _ _ _ z_in_x_dom_sig).
contradiction.
intros f l IH H; simpl; simpl in H;  apply (f_equal (fun l => Term f l)); induction l as [ | s l].
trivial.
simpl; rewrite (IH s); [rewrite IHl; trivial | left; trivial | idtac ].
intros; apply IH; trivial; right; trivial.
intro z; split; [intro z_in_dom_sig_l | intro z_in_empty].
rewrite <- (H z); apply VSet.inter_12.
simpl; apply (VSet.inter_1 _ _ _ z_in_dom_sig_l).
apply VSet.union_2; apply (VSet.inter_2 _ _ _ z_in_dom_sig_l).
contradiction.
intro z; split; [intro z_in_dom_sig_s | intro z_in_empty].
rewrite <- (H z); apply VSet.inter_12.
simpl; apply (VSet.inter_1 _ _ _ z_in_dom_sig_s).
apply VSet.union_1; apply (VSet.inter_2 _ _ _ z_in_dom_sig_s).
contradiction.
Qed.

Lemma occ_var_is_a_subterm_at_pos :
  forall x t, VSet.mem x (set_of_variables t) -> 
  exists p, subterm_at_pos t p = Some (Var x).
Proof.
intros x t; pattern t; apply term_rec3; clear t.
intros v; simpl; intros [x_eq_v | x_in_nil]; [idtac | contradiction].
exists (@nil nat); 
unfold VSet.LP.EDS.eq_A, VSet.EDS.eq_A , DecVar.eq_A in *; subst; trivial.
intros f l IH x_in_l; 
assert (H : exists s, exists i, In s l /\ nth_error l i = Some s 
                                                /\ VSet.mem x (set_of_variables s)).
clear IH; simpl in x_in_l; induction l as [ | t l]; [contradiction | idtac].
destruct_set x_in_l x_in_t x_in_l'.
exists t; exists 0; split; [left; trivial | split; trivial; simpl].
destruct (IHl x_in_l') as [s [i [s_in_l [s_eq_li  x_in_s]]]]; exists s; exists (S i).
split; [right; trivial | split; trivial].
destruct H as [s [i [s_in_l [s_eq_li x_in_s]]]].
destruct (IH s s_in_l x_in_s) as [p H].
exists (i :: p); simpl; rewrite s_eq_li; rewrite H; trivial.
Qed.

Lemma find_map_subst :
  forall x y t sigma, 
      match find X.eq_bool x sigma with
      | None => 
         find X.eq_bool x
            (map_subst
              (fun (_ : variable) v_sigma =>
                apply_subst ((y, t) :: nil) v_sigma) sigma) = None
      | Some x_val =>
            find X.eq_bool x 
              (map_subst
                (fun (_ : variable) v_sigma  =>
                  apply_subst ((y, t) :: nil) v_sigma) sigma) = 
             Some (apply_subst ((y, t) :: nil) x_val)
     end.
Proof.
intros x y s sigma; generalize x y s; clear x y s;
induction sigma as [ | [z u] sigma]; intros x y s; simpl; trivial.
generalize (X.eq_bool_ok x z); case (X.eq_bool x z); [intro x_eq_z; trivial | intro x_diff_z].
apply IHsigma.
Qed.

Lemma decomposition_step_is_complete :
 forall l sigma theta, is_a_solution (mk_pb sigma l) theta ->
  match decomposition_step (mk_pb sigma l)  with
  | Normal _ pb' => is_a_solution pb' theta
  | No_solution _ => False
  | Not_appliable _ pb' => is_a_solution pb' theta
  end.
Proof.
intros [ | [s t] l]  sigma theta; 
unfold decomposition_step; simpl unsolved_part; cbv iota beta; trivial.
generalize (T.eq_bool_ok s t); case (T.eq_bool s t); [intro s_eq_t | intro s_diff_t].
(* 1/2 remove trivial eq *)
unfold is_a_solution; simpl solved_part; simpl unsolved_part;
intros [Hl Hsigma]; split; [intros; apply Hl; right | intros; apply Hsigma]; trivial.

destruct s as [ x | f l1 ]; destruct t as [ y | g l2 ]. 
(* 1/4 Coalesce *)
assert (Hx := find_map_subst x x (Var y) sigma).
case_eq (find X.eq_bool x sigma); [intros x_val x_sigma | intro x_sigma]; 
rewrite x_sigma in Hx.
unfold is_a_solution; simpl solved_part; simpl unsolved_part;
intros [Hl Hsigma]; 
assert (Htheta : forall t, apply_subst theta t = apply_subst theta (apply_subst ((x, Var y) :: nil) t)).
intro t; pattern t; apply term_rec3; clear t; [intros v | intros f l'].
simpl; generalize (X.eq_bool_ok v x); case (X.eq_bool v x); [intro v_eq_x; subst v | intro v_diff_x].
apply (Hl (Var x) (Var y) (or_introl _ (eq_refl _))).
trivial.
intros IH; simpl; apply (f_equal (fun l => Term f l)); induction l' as [ | s' l']; trivial.
simpl; rewrite (IH s' (or_introl _ (eq_refl _))); rewrite IHl'; trivial;
intros; apply IH; right; trivial.

rewrite Hx; split.
intros s t H; destruct (in_inv H) as [s_t_eq_y_x_val' | s_t_in_l']; clear H.
assert (H':=Hsigma x); rewrite x_sigma in H';
injection s_t_eq_y_x_val'; clear s_t_eq_y_x_val'; intros; subst s t;
rewrite <-  (Hl _ _ (or_introl _ (eq_refl _))); rewrite H'; apply Htheta.
rewrite in_map_iff in s_t_in_l'; destruct s_t_in_l' as [[s' t'] [H s'_t'_in_l]];
injection H; intros; subst; clear H; do 2 rewrite <- Htheta;
apply Hl; right; trivial.

intro z; simpl.
generalize (X.eq_bool_ok z x); case (X.eq_bool z x); [intro z_eq_x; subst z | intro z_diff_x].
apply (Hl (Var x) (Var y) (or_introl _ (eq_refl _))).
assert (Hz := find_map_subst z x (Var y) sigma).
case_eq (find X.eq_bool z sigma); [ intros z_val z_sigma | intro z_sigma ];
rewrite z_sigma in Hz; rewrite Hz.
rewrite <- Htheta; generalize (Hsigma z); rewrite z_sigma; trivial.
exact I.

unfold is_a_solution; simpl solved_part; simpl unsolved_part;
intros [Hl Hsigma]; 
assert (Htheta : forall t, apply_subst theta t = apply_subst theta (apply_subst ((x, Var y) :: nil) t)).
intro t; pattern t; apply term_rec3; clear t; [intros v | intros f l'].
simpl; generalize (X.eq_bool_ok v x); case (X.eq_bool v x); [intro v_eq_x; subst v | intro v_diff_x].
apply (Hl (Var x) (Var y) (or_introl _ (eq_refl _))).
trivial.
intros IH; simpl; apply (f_equal (fun l => Term f l)); induction l' as [ | s' l']; trivial.
simpl; rewrite (IH s' (or_introl _ (eq_refl _))); rewrite IHl'; trivial;
intros; apply IH; right; trivial.

rewrite Hx; simpl; split.
intros s t s_t_in_l'; rewrite in_map_iff in s_t_in_l';
destruct s_t_in_l' as [[s' t'] [H s'_t'_in_l]]; 
injection H; intros; subst; clear H; do 2 rewrite <- Htheta;
apply Hl; right; trivial.

intro z; simpl.
generalize (X.eq_bool_ok z x); case (X.eq_bool z x); [intro z_eq_x; subst z | intro z_diff_x].
apply (Hl (Var x) (Var y) (or_introl _ (eq_refl _))).
assert (Hz := find_map_subst z x (Var y) sigma).
case_eq (find X.eq_bool z sigma); [ intros z_val z_sigma | intro z_sigma ];
rewrite z_sigma in Hz; rewrite Hz.
rewrite <- Htheta; generalize (Hsigma z); rewrite z_sigma; trivial.
exact I.

(* 1/3  Merge *)
unfold is_a_solution; simpl solved_part; simpl unsolved_part;
case_eq (find X.eq_bool x sigma); [intros x_val x_sigma| intro x_sigma].
intros [Hl Hsigma].
destruct (lt_ge_dec (T.size (Term g l2)) (T.size x_val)) as [L | L].
simpl; split.
intros s t [s_t_eq_x_val_g_l2 | s_t_in_l].
injection s_t_eq_x_val_g_l2; intros; subst s t; apply trans_eq with (apply_subst theta (Var x)).
generalize (Hsigma x); rewrite x_sigma; intro; apply sym_eq; trivial.
apply Hl; left; trivial.
apply Hl; right; trivial.
intro z; simpl.
generalize (X.eq_bool_ok z x); case (X.eq_bool z x); [intro z_eq_x; subst z | intro z_diff_x].
apply (Hl _ _ (or_introl _ (eq_refl _))).
apply (Hsigma z).
simpl; split.
intros s t [s_t_eq_x_val_g_l2 | s_t_in_l].
injection s_t_eq_x_val_g_l2; intros; subst s t; apply trans_eq with (apply_subst theta (Var x)).
generalize (Hsigma x); rewrite x_sigma; intro; apply sym_eq; trivial.
apply Hl; left; trivial.
apply Hl; right; trivial.
intro z; apply (Hsigma z).
simpl; split.
intros s t s_t_in_l.
apply H; right; trivial.
intro z; simpl.
generalize (X.eq_bool_ok z x); case (X.eq_bool z x); [intro z_eq_x; subst z | intro z_diff_x].
apply ((proj1 H) _ _ (or_introl _ (eq_refl _))).
apply ((proj2 H) z).

(* 1/2 Merge (sym) *)
unfold is_a_solution; simpl solved_part; simpl unsolved_part;
case_eq (find X.eq_bool y sigma); [intros y_val y_sigma | intro y_sigma].
intros [Hl Hsigma].
destruct (lt_ge_dec (T.size (Term f l1)) (T.size y_val)) as [L | L].
simpl; split.
intros s t [s_t_eq_y_val_f_l1 | s_t_in_l].
injection s_t_eq_y_val_f_l1; intros; subst s t; apply trans_eq with (apply_subst theta (Var y)).
generalize (Hsigma y); rewrite y_sigma; intro; apply sym_eq; trivial.
apply sym_eq; apply Hl; left; trivial.
apply Hl; right; trivial.
intro z; simpl.
generalize (X.eq_bool_ok z y); case (X.eq_bool z y); [intro z_eq_y; subst z | intro z_diff_y].
apply sym_eq; apply (Hl _ _ (or_introl _ (eq_refl _))).
apply (Hsigma z).
simpl; split.
intros s t [s_t_eq_y_val_f_l1 | s_t_in_l].
injection s_t_eq_y_val_f_l1; intros; subst s t; apply trans_eq with (apply_subst theta (Var y)).
generalize (Hsigma y); rewrite y_sigma; intro; apply sym_eq; trivial.
apply sym_eq; apply Hl; left; trivial.
apply Hl; right; trivial.
intro z; apply (Hsigma z).
simpl; split.
intros s t s_t_in_l.
apply (proj1 H); right; trivial.
intro z; simpl.
generalize (X.eq_bool_ok z y); case (X.eq_bool z y); [intro z_eq_y; subst z | intro z_diff_y].
apply sym_eq; apply ((proj1 H) _ _ (or_introl _ (eq_refl _))).
apply ((proj2 H) z).

(* 1/1 Decomposition *)
generalize (F.Symb.eq_bool_ok f g); case (F.Symb.eq_bool f g); [intro f_eq_g | intro f_diff_g].
generalize (beq_nat_ok (length l1) (length l2)); case (Nat.eqb (length l1) (length l2)); intro L.
unfold is_a_solution; simpl solved_part; simpl unsolved_part; 
intros [Hl Hsigma].
split; trivial.
assert (Hl' : forall s t, In (s,t) l -> apply_subst theta s = apply_subst theta t).
intros; apply Hl; right; trivial.
assert (Hl12 : map (apply_subst theta) l1 = map (apply_subst theta) l2).
generalize (Hl _ _ (or_introl _ (eq_refl _))); simpl;
intro H; injection H; intros; trivial.
clear Hsigma; generalize l2 l L Hl' Hl12; clear s_diff_t l2 l L Hl Hl' Hl12; 
induction l1 as [ | s1 l1]; intros [ | s2 l2] l L Hl Hl12.
intros s t; simpl; intros s_t_in_l; apply Hl; trivial.
discriminate.
discriminate.
simpl.
intros s t s_t_in_l'; refine (IHl1 l2 _ _ _ _ _ _ s_t_in_l'); clear s t s_t_in_l'.
injection L; intro; assumption.
intros s t [s_t_eq_s1_s2 | s_t_in_l].
injection s_t_eq_s1_s2; simpl in Hl12; injection Hl12; intros; subst s t; trivial.
apply Hl; trivial.
simpl in Hl12; injection Hl12; intros; trivial.
unfold is_a_solution; simpl solved_part; simpl unsolved_part.
intros [Hl _]; generalize (Hl _ _ (or_introl _ (eq_refl _))); simpl; intro H; injection H; intros H' _.
apply L; rewrite <- (length_map (apply_subst theta)); rewrite H'; apply length_map.
intros [Hl _]; generalize (Hl _ _ (or_introl _ (eq_refl _))); simpl; intro H; injection H; intros _ H'.
apply f_diff_g; assumption.
Qed.

Lemma decomposition_step_is_sound :
 forall l sigma theta, 
  match decomposition_step (mk_pb sigma l)  with
  | Normal _ pb' => is_a_solution pb' theta -> is_a_solution (mk_pb sigma l) theta
  | No_solution _ => is_a_solution (mk_pb sigma l)  theta -> False
  | Not_appliable _ pb' => is_a_solution pb' theta -> is_a_solution (mk_pb sigma l) theta
  end.
Proof.
intros [ | [s t] l]  sigma theta; 
unfold decomposition_step; simpl unsolved_part; cbv iota beta; trivial.
generalize (T.eq_bool_ok s t); case (T.eq_bool s t); [intro s_eq_t | intro s_diff_t].

(* 1/2 remove trivial eq *)
unfold is_a_solution; simpl solved_part; simpl unsolved_part;
intros [Hl Hsigma]; split; [idtac | intros; apply Hsigma; trivial].
intros s' t' [s'_t'_eq_s_t | s'_t'_in_l]; [idtac | apply Hl; trivial].
injection s'_t'_eq_s_t; intros; subst s s' t'; trivial.

destruct s as [ x | f l1 ]; destruct t as [ y | g l2 ]. 
(* 1/4 Coalesce *)
assert (Hx := find_map_subst x x (Var y) sigma).
case_eq (find X.eq_bool x sigma); [intros x_val x_sigma | intro x_sigma]; 
rewrite x_sigma in Hx.
simpl solved_part; rewrite Hx.
unfold is_a_solution; simpl solved_part; simpl unsolved_part;
intros [Hl Hsigma].
assert (x_theta_eq_y_theta : apply_subst theta (Var x) = apply_subst theta (Var y)).
generalize (Hsigma x); simpl.
generalize (X.eq_bool_ok x x); case (X.eq_bool x x); [intros _; trivial | intro x_diff_x; apply False_rect; apply x_diff_x; reflexivity].
assert (Htheta : forall t, apply_subst theta t = apply_subst theta (apply_subst ((x, Var y) :: nil) t)).
intro t; pattern t; apply term_rec3; clear t; [intros v | intros f l'].
simpl; generalize (X.eq_bool_ok v x); case (X.eq_bool v x); [intro v_eq_x; subst v | intro v_diff_x]; trivial.
intros IH; simpl; apply (f_equal (fun l => Term f l)); induction l' as [ | s' l']; trivial.
simpl; rewrite (IH s' (or_introl _ (eq_refl _))); rewrite IHl'; trivial;
intros; apply IH; right; trivial.
split.
intros s t [s_t_eq_x_y | s_t_in_l].
injection s_t_eq_x_y; intros; subst; trivial.
do 2 (apply sym_eq; rewrite Htheta).
apply Hl; right.
apply (in_map (B:= term*term) 
                                  (fun (uv : term * term) => 
                                    let (u,v) := uv in
                                      (apply_subst ((x,Var y) :: nil) u,
                                       apply_subst ((x,Var y) :: nil) v)) _ _ s_t_in_l).
intro z; generalize (Hsigma z); simpl; 
generalize (X.eq_bool_ok z x); case (X.eq_bool z x); [intro z_eq_x; subst z | intro z_diff_x].
rewrite x_sigma; intro H; rewrite H; 
apply sym_eq; rewrite Htheta; apply sym_eq; apply Hl; left; trivial.
assert (Hz := find_map_subst z x (Var y) sigma);
case_eq (find X.eq_bool z sigma); [ intros z_val z_sigma | intro z_sigma ]; 
rewrite z_sigma in Hz; rewrite Hz; trivial.
intro H; rewrite H; rewrite <- Htheta; trivial.
simpl; rewrite Hx.
unfold is_a_solution; simpl solved_part; simpl unsolved_part;
intros [Hl Hsigma].
assert (x_theta_eq_y_theta : apply_subst theta (Var x) = apply_subst theta (Var y)).
generalize (Hsigma x); simpl; 
generalize (X.eq_bool_ok x x); case (X.eq_bool x x); [intros _; trivial | intro x_diff_x; apply False_rect; apply x_diff_x; reflexivity].
assert (Htheta : forall t, apply_subst theta t = apply_subst theta (apply_subst ((x, Var y) :: nil) t)).
intro t; pattern t; apply term_rec3; clear t; [intros v | intros f l'].
simpl; generalize (X.eq_bool_ok v x); case (X.eq_bool v x); [intro v_eq_x; subst v | intro v_diff_x]; trivial.
intros IH; simpl; apply (f_equal (fun l => Term f l)); induction l' as [ | s' l']; trivial.
simpl; rewrite (IH s' (or_introl _ (eq_refl _))); rewrite IHl'; trivial;
intros; apply IH; right; trivial.
split.
intros s t [s_t_eq_x_y | s_t_in_l].
injection s_t_eq_x_y; intros; subst; trivial.
do 2 (apply sym_eq; rewrite Htheta).
apply Hl; 
apply (in_map (B:= term*term) 
                                  (fun (uv : term * term) => 
                                    let (u,v) := uv in
                                      (apply_subst ((x,Var y) :: nil) u,
                                       apply_subst ((x,Var y) :: nil) v)) _ _ s_t_in_l).
intro z; generalize (Hsigma z); simpl; 
generalize (X.eq_bool_ok z x); case (X.eq_bool z x); [intro z_eq_x; subst z | intro z_diff_x].
rewrite x_sigma; trivial.
assert (Hz := find_map_subst z x (Var y) sigma).
case_eq (find X.eq_bool z sigma); [intros z_val z_sigma | intro z_sigma]; 
rewrite z_sigma in Hz; rewrite Hz.
intro H; rewrite H; rewrite <- Htheta; trivial.
trivial.

(* 1/3 Merge *)
unfold is_a_solution; simpl solved_part; simpl unsolved_part;
case_eq (find X.eq_bool x sigma); [intros x_val x_sigma | intro x_sigma].
destruct (lt_ge_dec (T.size (Term g l2)) (T.size x_val)) as [L | L];
intros [Hl Hsigma].
simpl; split.
intros s t [s_t_eq_x_g_l2 | s_t_in_l].
injection s_t_eq_x_g_l2; intros; subst s t; apply trans_eq with (apply_subst theta x_val).
generalize (Hsigma x); simpl; rewrite x_sigma; 
generalize (X.eq_bool_ok x x); case (X.eq_bool x x); [intros _; trivial | intro x_diff_x; apply False_rect; apply x_diff_x; reflexivity].
intro H; rewrite H; apply sym_eq; apply Hl; left; trivial.
apply Hl; left; trivial.
apply Hl; right; trivial.
intro z; generalize (Hsigma z); simpl; 
generalize (X.eq_bool_ok z x); case (X.eq_bool z x); [intro z_eq_x; subst z | intro z_diff_x].
intro H; rewrite H; rewrite x_sigma.
apply sym_eq; apply Hl; left; trivial.
trivial.
simpl; split.
intros s t [s_t_eq_x_g_l2 | s_t_in_l].
injection s_t_eq_x_g_l2; intros; subst s t; apply trans_eq with (apply_subst theta x_val).
generalize (Hsigma x); simpl; rewrite x_sigma; intro; trivial.
apply Hl; left; trivial.
apply Hl; right; trivial.
intro z; apply (Hsigma z).
simpl; intros [Hl Hsigma]; split.
intros s t [s_t_eq_x_g_l2 | s_t_in_l].
injection s_t_eq_x_g_l2; intros; subst s t;
generalize (Hsigma x); simpl; 
generalize (X.eq_bool_ok x x); case (X.eq_bool x x); [intros _; trivial | intro x_diff_x; apply False_rect; apply x_diff_x; reflexivity].
apply Hl; trivial.
intro z; generalize (Hsigma z); simpl; 
generalize (X.eq_bool_ok z x); case (X.eq_bool z x); [intro z_eq_x; subst z | intro z_diff_x].
intro H; rewrite H; rewrite x_sigma; trivial.
trivial.

(* 1/2 Merge (sym) *)
unfold is_a_solution; simpl solved_part; simpl unsolved_part;
case_eq (find X.eq_bool y sigma); [intros y_val y_sigma | intro y_sigma].
destruct (lt_ge_dec (T.size (Term f l1)) (T.size y_val)) as [L | L];
intros [Hl Hsigma].
simpl; split.
intros s t [s_t_eq_f_l1_y | s_t_in_l].
injection s_t_eq_f_l1_y; intros; subst s t; apply trans_eq with (apply_subst theta y_val).
apply sym_eq; apply Hl; left; trivial.
generalize (Hsigma y); simpl; rewrite y_sigma; 
generalize (X.eq_bool_ok y y); case (X.eq_bool y y); [intros _; trivial | intro y_diff_y; apply False_rect; apply y_diff_y; reflexivity].
intro H; rewrite H; apply Hl; left; trivial.
apply Hl; right; trivial.
intro z; generalize (Hsigma z); simpl; 
generalize (X.eq_bool_ok z y); case (X.eq_bool z y); [intro z_eq_y; subst z | intro z_diff_y].
intro H; rewrite H; rewrite y_sigma.
apply sym_eq; apply Hl; left; trivial.
trivial.
simpl; split.
intros s t [s_t_eq_f_l1_y | s_t_in_l].
injection s_t_eq_f_l1_y; intros; subst s t; apply trans_eq with (apply_subst theta y_val).
apply sym_eq; apply Hl; left; trivial.
generalize (Hsigma y); simpl; rewrite y_sigma; simpl; intro; apply sym_eq; trivial.
apply Hl; right; trivial.
intro z; apply (Hsigma z).
simpl; intros [Hl Hsigma]; split.
intros s t [s_t_eq_f_l1_y | s_t_in_l].
injection s_t_eq_f_l1_y; intros; subst s t;
generalize (Hsigma y); simpl; 
generalize (X.eq_bool_ok y y); case (X.eq_bool y y); [intros _; trivial | intro y_diff_y; apply False_rect; apply y_diff_y; reflexivity].
simpl; intro; apply sym_eq; trivial.
apply Hl; trivial.
intro z; generalize (Hsigma z); simpl; 
generalize (X.eq_bool_ok z y); case (X.eq_bool z y); [intro z_eq_y; subst z | intro z_diff_y].
intro H; rewrite H; rewrite y_sigma; trivial.
trivial.

(* 1/1 Decomposition *)
generalize (F.Symb.eq_bool_ok f g); case (F.Symb.eq_bool f g); [intro f_eq_g | intro f_diff_g].
generalize (beq_nat_ok (length l1) (length l2)); case (Nat.eqb (length l1) (length l2)); intro L.
unfold is_a_solution; simpl solved_part; simpl unsolved_part; 
intros [Hl Hsigma].
split; trivial.
assert ((forall s t, In (s,t) l -> apply_subst theta s = apply_subst theta t) /\
             map (apply_subst theta) l1 = map (apply_subst theta) l2).
generalize l2 l L  Hl; clear l2 L l Hl s_diff_t; induction l1 as [ | s1 l1];
intros [ | s2 l2] l L Hl.
split; trivial; apply Hl; trivial.
discriminate.
discriminate.
assert (H : forall s t : term, In (s, t) ((s1,s2) :: l) -> apply_subst theta s = apply_subst theta t).
intros s t H; refine (proj1 (IHl1 l2 _ _ _) s t H); clear s t H.
injection L; intros; assumption.
intros s t H; apply Hl; trivial.
split.
intros s t s_t_in_l; apply H; right; trivial.
simpl; rewrite (H s1 s2); [apply f_equal | left; trivial].
refine (proj2 (IHl1 l2 _ _ Hl)).
injection L; intro; assumption.
intros s t [s_t_eq_f_l1_g_l2 | s_t_in_l].
injection s_t_eq_f_l1_g_l2; intros; subst; simpl; destruct H as [ _ H ]; rewrite H; subst; trivial.
destruct H as [ H _ ]; apply H; trivial.

unfold is_a_solution; simpl solved_part; simpl unsolved_part; 
intros [Hl Hsigma].
apply L; do 2 (apply sym_eq; rewrite <- (length_map (apply_subst theta)));
assert (Abs := Hl _ _ (or_introl _ (eq_refl _))); simpl in Abs; injection Abs;
intros H _; rewrite H; trivial.

unfold is_a_solution; simpl solved_part; simpl unsolved_part; 
intros [Hl Hsigma].
apply f_diff_g; assert (Abs := Hl _ _ (or_introl _ (eq_refl _))); simpl in Abs; injection Abs;
intros _ H; rewrite H; trivial.
Qed.

Definition is_a_solved_var x pb :=
  match find X.eq_bool x pb.(solved_part) with
  | None => false
  | Some _ => 
       andb  (negb (mem_bool X.eq_bool x (VSet.support (set_of_variables_in_unsolved_part pb.(unsolved_part)))))
        (negb (mem_bool X.eq_bool x (VSet.support (set_of_variables_in_range_of_subst pb.(solved_part)))))
  end.

Lemma solved_var :
  forall sigma l x, is_a_solved_var x (mk_pb sigma l) = true  <->   
     (match find X.eq_bool x sigma with
     | None => False
     | Some _ => 
       ~ (VSet.mem x (set_of_variables_in_unsolved_part l)) /\
        ~ (VSet.mem x (set_of_variables_in_range_of_subst sigma))
  end).
intros sigma l x; unfold is_a_solved_var; unfold VSet.mem; unfold DecVar.eq_A.
simpl solved_part; simpl unsolved_part.
destruct (find X.eq_bool x sigma) as [x_val | ]; split.
generalize (mem_bool_ok _ _ X.eq_bool_ok x (VSet.support (set_of_variables_in_unsolved_part l))).
case (mem_bool eq_var_bool x (VSet.support (set_of_variables_in_unsolved_part l))); intro H.
intros; discriminate.
generalize (mem_bool_ok _ _ X.eq_bool_ok x (VSet.support (set_of_variables_in_range_of_subst sigma))).
case (mem_bool eq_var_bool x (VSet.support (set_of_variables_in_range_of_subst sigma))); intro H'.
intros; discriminate.
intros; split; assumption.
intros [H G];
generalize (mem_bool_ok _ _ X.eq_bool_ok x (VSet.support (set_of_variables_in_unsolved_part l))).
case (mem_bool eq_var_bool x (VSet.support (set_of_variables_in_unsolved_part l))); intro H'.
apply False_rect; apply H; assumption.
generalize (mem_bool_ok _ _ X.eq_bool_ok x (VSet.support (set_of_variables_in_range_of_subst sigma))).
case (mem_bool eq_var_bool x (VSet.support (set_of_variables_in_range_of_subst sigma))); intro G'.
apply False_rect; apply G; assumption.
reflexivity.
discriminate.
contradiction.
Qed.

Lemma not_solved_var :
  forall sigma l x, is_a_solved_var x (mk_pb sigma l) = false  <->   
     (match find X.eq_bool x sigma with
     | None => True
     | Some _ => 
       (VSet.mem x (set_of_variables_in_unsolved_part l)) \/
        (VSet.mem x (set_of_variables_in_range_of_subst sigma))
  end).
Proof.
intros sigma l x; unfold is_a_solved_var; unfold VSet.mem; unfold DecVar.eq_A.
simpl solved_part; simpl unsolved_part.
destruct (find X.eq_bool x sigma) as [x_val | ]; split.
generalize (mem_bool_ok _ _ X.eq_bool_ok x (VSet.support (set_of_variables_in_unsolved_part l))).
case (mem_bool eq_var_bool x (VSet.support (set_of_variables_in_unsolved_part l))); intro H.
left; assumption.
generalize (mem_bool_ok _ _ X.eq_bool_ok x (VSet.support (set_of_variables_in_range_of_subst sigma))).
case (mem_bool eq_var_bool x (VSet.support (set_of_variables_in_range_of_subst sigma))); intro H'.
right; assumption.
intro Abs; apply False_rect; discriminate.
intros [H | G].
generalize (mem_bool_ok _ _ X.eq_bool_ok x (VSet.support (set_of_variables_in_unsolved_part l))).
case (mem_bool eq_var_bool x (VSet.support (set_of_variables_in_unsolved_part l))); intro H'.
reflexivity.
apply False_rect; apply H'; assumption.
generalize (mem_bool_ok _ _ X.eq_bool_ok x (VSet.support (set_of_variables_in_range_of_subst sigma))).
case (mem_bool eq_var_bool x (VSet.support (set_of_variables_in_range_of_subst sigma))); intro G'.
case (mem_bool eq_var_bool x (VSet.support (set_of_variables_in_unsolved_part l))); reflexivity.
apply False_rect; apply G'; assumption.
trivial.
trivial.
Qed.

(** ** A measure on lists based on a measure on elements. *)

Module TermMul := dickson.Make(Term_eq_dec).

Fixpoint list_size_mul (A : Type) (siz : A -> nat) (l : list A) {struct l} : list nat :=
  match l with
  | nil => @nil nat
  | h :: tl => (siz h) :: (list_size_mul A siz tl)
  end.

Definition lt_mul : (relation (list nat)) := 
   trans_clos (NatMul.multiset_extension_step lt).

Definition size_of_unsolved_part pb :=
  list_size_mul _ 
                 (fun s_t => match s_t with (s,t) => max (size s) (size t) end)
                 pb.(unsolved_part).

Definition size_of_solved_part pb :=
  list_size_mul _ 
                  (fun x => match find X.eq_bool x pb.(solved_part) with
                                               Some x_val => size x_val
                                              | None => 0
                                              end)
                 (VSet.support (domain_of_subst pb.(solved_part))).

Definition nb_var_eq_of_unsolved_part pb :=
   list_size (fun s_t => match s_t with (s,t) => match s, t with
                                      | Var _,  _ => 1
                                      | _ , Var _ => 1
                                      | _, _ => 0
                                      end end)
                   pb.(unsolved_part).

Lemma VSet_compat : 
forall pb (e e' : DecVar.A),
   DecVar.eq_A e e' ->
   (fun v : variable => negb (is_a_solved_var v pb)) e =
   (fun v : variable => negb (is_a_solved_var v pb)) e'.
Proof.
unfold VSet.EDS.eq_A, DecVar.eq_A.
intros; subst; split; intro; assumption.
Qed.

Definition phi1 pb :=
   VSet.cardinal 
     (VSet.filter (fun v : variable => negb (is_a_solved_var v pb))
        (VSet.union 
                 (set_of_variables_in_unsolved_part pb.(unsolved_part))
                 (VSet.union
                        (domain_of_subst pb.(solved_part))
                        (set_of_variables_in_range_of_subst pb.(solved_part))))
        (VSet_compat pb)).

Definition phi2 pb :=  size_of_solved_part pb ++ size_of_unsolved_part pb. 

Definition phi3 pb := nb_var_eq_of_unsolved_part pb. 

Definition measure_for_unif_pb pb := (phi1 pb, (phi2 pb, phi3 pb)).

Fixpoint lt_bool (n1 n2 : nat) {struct n1} :=
  match n1, n2 with
  | O, O => false
  | O, (S _) => true
  | (S m1), (S m2) => lt_bool m1 m2
  | (S _), O => false
  end.

Lemma lt_bool_ok : forall n1 n2, if lt_bool n1 n2 then n1 < n2 else ~n1 < n2.
Proof.
fix lt_bool_ok 1.
intro n1; case n1; clear n1.
intros [ | n2]; simpl.
apply Nat.lt_irrefl.
apply le_n_S; apply Nat.le_0_l.
intros n1 [ | n2]; simpl.
apply Nat.nle_succ_0.
generalize (lt_bool_ok n1 n2); case (lt_bool n1 n2).
intro H; apply le_n_S; assumption.
intros H1 H2; apply H1; apply le_S_n; assumption.
Defined.

Definition lt_ms_bool := 
  fun p123 q123 =>
  match p123, q123 with
  (p1,(p2,p3)), (q1,(q2,q3)) =>
    if Nat.eqb p1 q1
    then 
 	 (match dickson.NatMul.mult lt_bool p2 q2 with
  	| Less_than => true 
  	| Equivalent => lt_bool p3 q3
  	| _ => false
  	end)
   else lt_bool p1 q1
  end.

Definition lt_ms m1 m2 := lt_ms_bool m1 m2 = true.

Definition lt_pb pb pb' := 
lt_ms (measure_for_unif_pb pb) (measure_for_unif_pb pb').

Lemma lex_lt : forall p1 p2 p3 q1 q2 q3,
   p1 < q1 -> lt_ms (p1,(p2,p3)) (q1,(q2,q3)).
Proof.
intros p1 p2 p3 q1 q2 q3 p1_lt_q1; unfold lt_ms, lt_ms_bool.
generalize (beq_nat_ok p1 q1); case (Nat.eqb p1 q1); [intro p1_eq_q1 | intro p1_diff_q1]; trivial.
absurd (S p1 <= p1); subst; trivial; auto with arith.
generalize (lt_bool_ok p1 q1); case (lt_bool p1 q1).
reflexivity.
intro Abs; apply False_rect; apply Abs; assumption.
Defined.

Lemma lex_le_lt : forall p1 p2 p3 q1 q2 q3,
  p1 <= q1 -> dickson.NatMul.mult lt_bool p2 q2 = Less_than -> lt_ms (p1,(p2,p3)) (q1,(q2,q3)).
Proof.
intros p1 p2 p3 q1 q2 q3 p1_le_q1 p2_lt_q2; unfold lt_ms, lt_ms_bool.
generalize (beq_nat_ok p1 q1); case (Nat.eqb p1 q1); [intro p1_eq_q1 | intro p1_diff_q1].
rewrite p2_lt_q2; trivial.
generalize (lt_bool_ok p1 q1); case (lt_bool p1 q1).
reflexivity.
intro Abs; apply False_rect; apply p1_diff_q1.
clear p1_diff_q1; revert p1 q1 p1_le_q1 Abs ; fix lex_le_lt 1. 
intro p1; case p1; clear p1.
intros q1 _; case q1; clear q1.
intros _; reflexivity.
intros n Abs; apply False_rect; apply Abs; apply le_n_S; apply Nat.le_0_l.
intros p1 q1; case q1; clear q1.
intro Abs; inversion Abs.
intros q1 Hle Hnot_lt; apply f_equal.
apply lex_le_lt.
apply le_S_n; assumption.
intro H; apply Hnot_lt; apply le_n_S; assumption.
Defined.

Lemma lex_le_meq_lt : 
forall p1 p2 p3 q1 q2 q3,
  p1 <= q1 -> dickson.NatMul.mult lt_bool p2 q2 = Equivalent -> p3 < q3 ->
  lt_ms (p1,(p2,p3)) (q1,(q2,q3)).  
Proof.
intros p1 p2 p3 q1 q2 q3 p1_le_q1 p2_eq_q2 p3_lt_q3; unfold lt_ms, lt_ms_bool.
rewrite p2_eq_q2.
generalize (beq_nat_ok p1 q1); case (Nat.eqb p1 q1); [intro p1_eq_q1 | intro p1_diff_q1].
generalize (lt_bool_ok p3 q3); case (lt_bool p3 q3).
reflexivity.
intro Abs; apply False_rect; apply Abs; assumption.
revert p1 q1 p1_le_q1 p1_diff_q1 ; fix lex_le_meq_lt 1. 
intro p1; case p1; clear p1.
intros q1 _; case q1; clear q1.
intros Abs; apply False_rect; apply Abs; reflexivity.
intros q1 _; reflexivity.
intros p1 q1; case q1; clear q1.
intro Abs; inversion Abs.
intros q1 Hle Hdiff; simpl; apply lex_le_meq_lt.
apply le_S_n; assumption.
intro Heq; apply Hdiff; apply f_equal; assumption.
Defined.

Lemma wf_lt_ms : well_founded lt_ms.
Proof.
unfold well_founded, lt_ms, lt_ms_bool.
intros [p [q r]]; revert q r; pattern p; refine (well_founded_ind lt_wf _ _ p); clear p.
intros p IHp q; unfold lt_mul.
pattern q; apply well_founded_ind with (list nat)
  (trans_clos (NatMul.multiset_extension_step lt)); clear q.
apply closure.wf_trans; apply NatMul.dickson; apply Wf_nat.lt_wf.
intros q IHq r; pattern r; refine (well_founded_ind Wf_nat.lt_wf _ _ r); clear r.

intros r IHr; apply Acc_intro.
intros [p' [q' r']]; 
generalize (beq_nat_ok p' p); case (Nat.eqb p' p); [intro p'_eq_p | intro p'_diff_p].
subst p'; case_eq (NatMul.mult lt_bool q' q); [intro q'_eq_q | intro q'_lt_q | intro q'_gt_q  | intro q'_diff_q ].
intro r'_lt_r; generalize (lt_bool_ok r' r); rewrite  r'_lt_r; clear  r'_lt_r; intro  r'_lt_r.
assert (Acc_p_q_r' := IHr _ r'_lt_r).
apply Acc_intro; intros [p'' [q'' r'']].
generalize (beq_nat_ok p'' p); case (Nat.eqb p'' p); [intro p''_eq_p | intro p''_diff_p].
subst p''; case_eq (NatMul.mult lt_bool q'' q'); [intro q''_eq_q' | intro q''_lt_q' | intro q''_gt_q'  | intro q''_diff_q' ].
intro r''_lt_r'; refine (Acc_inv Acc_p_q_r' _ _).
rewrite (Nat.eqb_refl p).
assert (q''_eq_q : NatMul.mult lt_bool q'' q = Equivalent).
apply NatMul.mult_is_complete_equiv.
transitivity q'.
assert (H := NatMul.mult_is_sound _ _  lt_bool_ok q'' q'); rewrite q''_eq_q' in H; exact H.
assert (H := NatMul.mult_is_sound _ _ lt_bool_ok q' q); rewrite q'_eq_q in H; exact H.
rewrite q''_eq_q; assumption.
intros _; assert (q''_lt_q : NatMul.mult lt_bool q'' q = Less_than).
assert (H := NatMul.mult_is_sound _ _  lt_bool_ok q' q); rewrite q'_eq_q in H.
assert (H' := NatMul.mult_is_sound _ _ lt_bool_ok q'' q'); rewrite q''_lt_q' in H'.
assert (H'' : trans_clos (NatMul.multiset_extension_step lt) q'' q).
apply NatMul.list_permut_trans_clos_multiset_extension_step_2 with q'; trivial.
assert (H3 := NatMul.mult_is_sound _ _ lt_bool_ok q'' q).
apply NatMul.mult_is_complete_less_than with lt.
exact lt_bool_ok.
exact Nat.lt_trans.
exact Nat.lt_irrefl.
assumption.

apply IHq.
assert (H := NatMul.mult_is_sound lt _ lt_bool_ok q'' q); rewrite q''_lt_q in H; exact H.
intros; discriminate.
intros; discriminate.

intro p''_lt_p; apply IHp; generalize (lt_bool_ok p'' p); rewrite p''_lt_p; trivial.
intros _; apply IHq.
assert (H := NatMul.mult_is_sound  _ _ lt_bool_ok q' q); rewrite q'_lt_q in H; exact H.
intros; discriminate.
intros; discriminate.

intro p'_lt_p; apply IHp; generalize (lt_bool_ok p' p); rewrite p'_lt_p; trivial.
Defined.

Lemma wf_lt_pb : well_founded lt_pb.
Proof.
unfold lt_pb;
apply (wf_inverse_image unification_problem _ lt_ms measure_for_unif_pb wf_lt_ms).
Defined.

Lemma remove_trivial_eq_decreases :
  forall s l sigma,  lt_pb (mk_pb sigma l) (mk_pb sigma ((s,s) :: l)).
Proof.
intros s l sigma;
unfold lt_pb, measure_for_unif_pb; apply lex_le_lt.
(* First component phi1 *)
unfold phi1; apply VSet.cardinal_subset; apply VSet.subset_filter.
apply VSet.union_compat_subset_1.
simpl; intro v; apply VSet.union_2; trivial.
intro v; case_eq (is_a_solved_var v (mk_pb sigma l)).
intros _ Abs; discriminate.
intros H _; assert (H' : is_a_solved_var v (mk_pb sigma ((s, s) :: l)) = false).
revert H; do 2 rewrite not_solved_var.
case (find X.eq_bool v sigma); [intros _ | trivial].
intros [H | H].
left; apply VSet.union_2; trivial.
right; trivial.
rewrite H'; reflexivity.

(* Second component phi2 *)
unfold lt_mul, phi2, size_of_unsolved_part, size_of_solved_part; simpl.
refine (NatMul.mult_is_complete_less_than _ _ _ _ _).
apply lt_bool_ok.
intros n1 n2 n3; apply Nat.lt_trans.
apply Nat.lt_irrefl.
left; refine (@NatMul.rmv_case lt _ _ (list_size_mul _
     (fun x  =>
      match find X.eq_bool x sigma with
      | Some x_val => size x_val
      | None => 0
      end) (VSet.support (domain_of_subst sigma)) ++
      list_size_mul (term * term)
        (fun s_t : term * term =>
         let (s0, t) := s_t in max (size s0) (size t)) l) 
      nil (max (size s) (size s)) _ _ _).
intros; contradiction.
reflexivity.
symmetry.
rewrite <-  NatMul.LP.permut_cons_inside; reflexivity.
Defined.

Lemma domain_of_subst_map_subst :
 forall sigma f, domain_of_subst (map_subst f sigma) = domain_of_subst sigma.
Proof.
intros sigma f; 
induction sigma as [ | [x t] sigma]; simpl; trivial; rewrite IHsigma; trivial.
Qed.

Lemma solved_var_inc_not_mem :
forall x y t,  x <> y ->  
       ~ VSet.mem x (set_of_variables (apply_subst ((x, Var y) :: nil) t)).
Proof.
intros x y t x_diff_y; pattern t; apply T.term_rec3.
intros v; simpl; generalize (X.eq_bool_ok v x); case (X.eq_bool v x); [intro v_eq_x; subst v | intro v_diff_x].
intros [x_eq_y | x_in_nil] ; [apply x_diff_y; subst; trivial | contradiction].
intros [x_eq_v | x_in_nil].
unfold  VSet.LP.EDS.eq_A, VSet.EDS.eq_A, DecVar.eq_A in *;
subst; apply v_diff_x; trivial.
contradiction.
intros f l IHl x_in_l'; simpl in x_in_l'; clear f; induction l as [ | s l]; trivial.
simpl in x_in_l'; destruct_set x_in_l' x_in_s' x_in_l''.
apply (IHl s); trivial; left; trivial.
apply IHl0; trivial.
intros; apply IHl; right; trivial.
Qed.

Lemma solved_var_inc_not_mem_list :
forall x y l,  x <> y ->  
  ~ VSet.mem x
               (set_of_variables_in_unsolved_part
                  (map
                     (fun uv : term * term =>
                      let (u, v) := uv in
                      (apply_subst ((x, Var y) :: nil) u,
                      apply_subst ((x, Var y) :: nil) v)) l)).
Proof.
intros x y l x_diff_y x_in_l'; induction l as [ | [s t] l].
contradiction.
simpl set_of_variables_in_unsolved_part in x_in_l'; 
destruct_set x_in_l' x_in_s'_t' x_in_l''.
destruct_set x_in_s'_t' x_in_s' x_in_t'.
apply (solved_var_inc_not_mem _ _ _ x_diff_y x_in_s').
apply (solved_var_inc_not_mem _ _ _ x_diff_y x_in_t').
apply IHl; trivial.
Qed.

Lemma solved_var_inc_not_mem_subst :
forall x y sigma,  x <> y ->  
  ~VSet.mem x
                   (set_of_variables_in_range_of_subst
                      (map_subst
                         (fun (_ : variable) (v_sigma : term) =>
                          apply_subst ((x, Var y) :: nil) v_sigma) sigma)).
Proof.
intros x y sigma x_diff_y x_in_sigma'; induction sigma as [ | [v t] sigma].
contradiction.
simpl set_of_variables_in_range_of_subst in x_in_sigma'; 
destruct_set x_in_sigma' x_in_t' x_in_sigma''.
apply (solved_var_inc_not_mem _ _ _ x_diff_y x_in_t').
apply IHsigma; trivial.
Qed.

Lemma solved_var_inc_occ_in_subst : 
  forall x z x_val sigma, find X.eq_bool x sigma = Some x_val ->
  VSet.mem z (set_of_variables x_val) ->
  VSet.mem z (set_of_variables_in_range_of_subst sigma).
Proof.
intros x z x_val sigma; 
induction sigma as [ | [v t] sigma].
intro; discriminate.
intros x_sigma z_in_x_val; simpl in x_sigma; revert x_sigma.
 generalize (X.eq_bool_ok x v); case (X.eq_bool x v); [intro v_eq_x; subst v | intro v_diff_x].
intro x_sigma; apply VSet.union_1; injection x_sigma; intros; subst; trivial.
intros x_sigma; apply VSet.union_2; apply IHsigma; trivial.
Qed.

Lemma solved_var_inc_term :
forall x y z t, z <> y ->
                  VSet.mem z (set_of_variables (apply_subst ((x, Var y) :: nil) t)) ->
                  VSet.mem z (set_of_variables t).
Proof.
intros x y z t z_diff_y; pattern t; apply T.term_rec3.
intro v; simpl; generalize (X.eq_bool_ok v x); case (X.eq_bool v x); [intro v_eq_x; subst v | intro v_diff_x; trivial].
intros [z_eq_y | z_in_nil].
unfold  VSet.LP.EDS.eq_A, VSet.EDS.eq_A, DecVar.eq_A in *;
subst z; absurd (y=y); trivial.
contradiction.
intros f l; simpl; fold set_of_variables_list; clear f; 
induction l as [ | s l]; [trivial | idtac].
intros H_s_l z_in_s'_l'; destruct_set z_in_s'_l' z_in_s' z_in_l'.
simpl; apply VSet.union_1; apply H_s_l; trivial; left; trivial.
simpl; apply VSet.union_2; apply IHl; trivial.
intros; apply H_s_l;  [right | idtac] ; trivial.
Qed.

Lemma solved_var_inc_list :
forall x y z l,  z <> y ->  
 VSet.mem z
               (set_of_variables_in_unsolved_part
                  (map
                     (fun uv : term * term =>
                      let (u, v) := uv in
                      (apply_subst ((x, Var y) :: nil) u,
                      apply_subst ((x, Var y) :: nil) v)) l)) ->
 VSet.mem z (set_of_variables_in_unsolved_part l).
Proof.
intros x y z l z_diff_y z_in_l'; 
induction l as [ | [s t] l]; trivial; destruct_set z_in_l' z_in_s'_t' z_in_l''.
destruct_set z_in_s'_t' z_in_s' z_in_t'.
simpl set_of_variables_in_unsolved_part; do 2 apply VSet.union_1;
apply solved_var_inc_term with x y; trivial.
simpl set_of_variables_in_unsolved_part; apply VSet.union_1; apply VSet.union_2;
apply solved_var_inc_term with x y; trivial.
simpl set_of_variables_in_unsolved_part; apply VSet.union_2; apply IHl; trivial.
Qed.

Lemma solved_var_inc_subst :
forall x y z sigma,  z <> y ->  
         VSet.mem z
                   (set_of_variables_in_range_of_subst
                      (map_subst
                         (fun (_ : variable) (v_sigma : term) =>
                          apply_subst ((x, Var y) :: nil) v_sigma) sigma)) ->
      VSet.mem z (set_of_variables_in_range_of_subst sigma).
Proof.
intros x y z sigma z_diff_y z_in_sigma'; induction sigma as [ | [v t] sigma]; trivial.
destruct_set z_in_sigma' z_in_t' z_in_sigma''.
simpl set_of_variables_in_range_of_subst;
apply VSet.union_1; apply solved_var_inc_term with x y; trivial.
simpl set_of_variables_in_range_of_subst;
apply VSet.union_2; apply IHsigma; trivial.
Qed.

Lemma coalesce1_decreases :
 forall x y l sigma x_val, 
  x <> y ->
  find X.eq_bool x sigma = Some x_val ->
  lt_pb (mk_pb  ((x, Var y)
                           :: map_subst
                               (fun (_ : variable) (v_sigma : term) =>
                                    apply_subst ((x, Var y) :: nil) v_sigma) sigma)
                         ((Var y, apply_subst ((x, Var y) :: nil) x_val)
                         :: map
                            (fun uv : term * term =>
                               let (u, v) := uv in
                                  (apply_subst ((x, Var y) :: nil) u,
                                  apply_subst ((x, Var y) :: nil) v)) l))
         (mk_pb sigma ((Var x, Var y) :: l)).
Proof.
intros x y l sigma x_val x_diff_y  x_sigma; 
assert (Hx := find_map_subst x x (Var y) sigma); rewrite x_sigma in Hx.
unfold lt_pb, measure_for_unif_pb; apply lex_lt.

(* First component phi1 *)
unfold phi1; apply VSet.subset_cardinal_not_eq_not_eq_set with x.
apply VSet.subset_filter.
assert (Hy : VSet.mem y (VSet.union
     (VSet.union (VSet.union (VSet.singleton x) (VSet.singleton y))
        (set_of_variables_in_unsolved_part l))
     (VSet.union (domain_of_subst sigma)
        (set_of_variables_in_range_of_subst sigma)))).
do 2 apply VSet.union_1; apply VSet.union_2; left; subst; reflexivity.
simpl; apply VSet.subset_subset_union.
apply VSet.subset_subset_union.
apply VSet.subset_subset_union.
intros z [z_eq_y | z_in_nil].
unfold  VSet.LP.EDS.eq_A, VSet.EDS.eq_A, DecVar.eq_A in *;
subst; apply Hy.
contradiction.
intros z z_in_x_val'; 
generalize (X.eq_bool_ok z y); case (X.eq_bool z y); [intro z_eq_y; subst; apply Hy | intro z_diff_y].
do 2 apply VSet.union_2;
apply solved_var_inc_occ_in_subst with x x_val; trivial;
apply solved_var_inc_term with x y; trivial.
intros z z_in_l'; 
generalize (X.eq_bool_ok z y); case (X.eq_bool z y); [intro z_eq_y; subst; apply Hy | intro z_diff_y].
apply VSet.union_1; apply VSet.union_2; clear Hy.
apply solved_var_inc_list with x y; trivial.

apply VSet.subset_subset_union.
intros z z_in_x_dom_sig; 
destruct (VSet.add_12 _ _ _ z_in_x_dom_sig) as [z_eq_x | z_in_dom_sig].
do 3 apply VSet.union_1; left; subst; trivial.
apply VSet.union_2; apply VSet.union_1; 
rewrite domain_of_subst_map_subst in z_in_dom_sig; trivial.

apply VSet.subset_subset_union.
intros z [z_eq_y | z_in_nil].
unfold  VSet.LP.EDS.eq_A, VSet.EDS.eq_A, DecVar.eq_A in *;
subst z; apply Hy.
contradiction.
intros z z_in_sigma'; 
generalize (X.eq_bool_ok z y); case (X.eq_bool z y); [intro z_eq_y; subst; apply Hy | intro z_diff_y].
do 2 apply VSet.union_2; apply (solved_var_inc_subst _ _ _ _ z_diff_y z_in_sigma').

intros z; do 2 (rewrite Dummy_bool; rewrite not_solved_var); simpl.
generalize (X.eq_bool_ok z x); case (X.eq_bool z x); [intro z_eq_x; subst z | intro z_diff_x].
intros _; rewrite x_sigma; left;  do 2 apply VSet.union_1; left; reflexivity.
assert (Hz := find_map_subst z x (Var y) sigma).
case_eq (find X.eq_bool z sigma); [ intros z_val z_sigma| intro z_sigma]; 
rewrite z_sigma in Hz; rewrite Hz; trivial.
simpl; generalize (X.eq_bool_ok z y); case (X.eq_bool z y); [intro z_eq_y | intro z_diff_y].
intros _; left; apply VSet.union_1; apply VSet.union_2; left; subst; reflexivity.
intros [z_in_y_x_val'_l' | z_in_y_sigma'].
destruct_set z_in_y_x_val'_l' z_in_y_x_val' z_in_l'.
destruct_set z_in_y_x_val' z_in_y z_in_x_val'.
left; apply VSet.union_1; apply VSet.union_2; trivial.
right; apply solved_var_inc_occ_in_subst with x x_val; trivial.
apply solved_var_inc_term with x y; trivial.
left; apply VSet.union_2.
apply solved_var_inc_list with x y; trivial.

destruct_set z_in_y_sigma' z_in_y z_in_sigma'.
left; apply VSet.union_1; apply VSet.union_2; trivial.
right; apply solved_var_inc_subst with x y; trivial.


intro H; generalize (VSet.filter_2 _ _ _ _ H); clear H; intros [_ H].
rewrite Dummy_bool in H; rewrite not_solved_var in H; simpl in H; revert H.
generalize (X.eq_bool_ok x x); case (X.eq_bool x x); [intros _ | intro x_diff_x; apply False_rect; apply x_diff_x; reflexivity].
intros [H | H].
destruct_set H x_in_y_x_val' x_in_l'.
destruct_set x_in_y_x_val' x_in_y x_in_x_val'.
destruct x_in_y as [x_eq_y | x_in_nil]; [idtac | contradiction].
apply x_diff_y; subst; trivial.
apply (solved_var_inc_not_mem _ _ _ x_diff_y x_in_x_val').
apply (solved_var_inc_not_mem_list _ _ _ x_diff_y x_in_l').
destruct_set H x_in_y x_in_sigma'.
destruct x_in_y as [x_eq_y | x_in_nil]; [idtac | contradiction].
apply x_diff_y; subst; trivial.
apply (solved_var_inc_not_mem_subst _ _ _ x_diff_y x_in_sigma').

apply VSet.filter_1.
simpl unsolved_part; unfold set_of_variables_in_unsolved_part;
do 3 apply VSet.union_1; left; reflexivity.
rewrite Dummy_bool; rewrite not_solved_var; simpl; rewrite x_sigma.
left; do 2 apply VSet.union_1; left; reflexivity.
Defined.

Lemma coalesce2_decreases :
 forall x y l sigma, 
  x <> y -> 
  find X.eq_bool x sigma = None ->
  lt_pb
    (mk_pb
       ((x, Var y)
        :: map_subst
             (fun (_ : variable) (v_sigma : term) =>
              apply_subst ((x, Var y) :: nil) v_sigma) sigma)
       (map
          (fun uv : term * term =>
           let (u, v) := uv in
           (apply_subst ((x, Var y) :: nil) u,
           apply_subst ((x, Var y) :: nil) v)) l))
    (mk_pb sigma ((Var x, Var y) :: l)).
Proof.
intros x y l sigma x_diff_y  x_sigma; 
assert (Hx := find_map_subst x x (Var y) sigma); rewrite x_sigma in Hx.
unfold lt_pb, measure_for_unif_pb; apply lex_lt.
(* First component phi1 *)
unfold phi1; apply VSet.subset_cardinal_not_eq_not_eq_set with x.
simpl unsolved_part; simpl solved_part; simpl set_of_variables_in_unsolved_part;
simpl domain_of_subst; apply VSet.subset_filter.
apply VSet.subset_subset_union.
intros z z_in_l'; generalize (X.eq_bool_ok z y); case (X.eq_bool z y); [intro z_eq_y | intro z_diff_y].
do 2 apply VSet.union_1; apply VSet.union_2; left; subst; reflexivity.
apply VSet.union_1; apply VSet.union_2;
apply solved_var_inc_list with x y; trivial.
apply VSet.subset_subset_union.
rewrite domain_of_subst_map_subst.
intros z z_in_x_dom_sig; 
destruct (VSet.add_12 _ _ _ z_in_x_dom_sig) as [z_eq_x | z_in_dom_sig].
do 3 apply VSet.union_1; left; subst; trivial.
apply VSet.union_2; apply VSet.union_1; trivial.
intros z z_in_y_sigma'; destruct_set z_in_y_sigma' z_in_y z_in_sigma'.
do 2 apply VSet.union_1; apply VSet.union_2; trivial.
generalize (X.eq_bool_ok z y); case (X.eq_bool z y); [intro z_eq_y | intro z_diff_y].
do 2 apply VSet.union_1; apply VSet.union_2; left; subst; reflexivity.
do 2 apply VSet.union_2; apply (solved_var_inc_subst _ _ _ _ z_diff_y z_in_sigma').
intros z; do 2 rewrite Dummy_bool; do 2 rewrite not_solved_var; simpl.
generalize (X.eq_bool_ok z x); case (X.eq_bool z x); [intro z_eq_x; subst z | intro z_diff_x].
rewrite x_sigma; trivial.
case_eq (find X.eq_bool z sigma); [ intros z_val z_sigma | intro z_sigma; trivial].
assert (Hz := find_map_subst z x (Var y) sigma); 
rewrite z_sigma in Hz; rewrite Hz.
intros [z_in_l' | z_in_y_sigma'].
left; generalize (X.eq_bool_ok z y); case (X.eq_bool z y); [intro z_eq_y | intro z_diff_y].
apply VSet.union_1; apply VSet.union_2; left; subst; reflexivity.
apply VSet.union_2; apply solved_var_inc_list with x y; trivial.
destruct_set z_in_y_sigma' z_in_y z_in_sigma'.
left; apply VSet.union_1; apply VSet.union_2; trivial.
 generalize (X.eq_bool_ok z y); case (X.eq_bool z y); [intro z_eq_y | intro z_diff_y].
left; apply VSet.union_1; apply VSet.union_2; left; subst; reflexivity.
right; apply solved_var_inc_subst with x y; trivial.

intro H; destruct (VSet.filter_2 _ _ _ _ H) as [_ H1]; clear H.
rewrite Dummy_bool in H1; rewrite not_solved_var in H1; simpl in H1; revert H1.
generalize (X.eq_bool_ok x x); case (X.eq_bool x x); [intros _ | intro x_diff_x; apply False_rect; apply x_diff_x; reflexivity].
intros [x_in_l' | x_in_y_sigma'].
revert x_in_l'; apply solved_var_inc_not_mem_list; trivial.
destruct_set x_in_y_sigma' x_in_y x_in_sigma'.
apply x_diff_y; destruct x_in_y as [x_eq_y | x_in_nil]; [subst; trivial | contradiction].
apply solved_var_inc_not_mem_subst with x y sigma; trivial.
apply VSet.filter_1.
simpl set_of_variables_in_unsolved_part; 
do 3 apply VSet.union_1; left; reflexivity.
rewrite Dummy_bool; rewrite not_solved_var; simpl; rewrite x_sigma; trivial.
Defined.

Lemma list_size_mul_app:
 forall (A : Type) (siz : A -> nat) l1 l2,
 list_size_mul A siz (l1 ++ l2) = (list_size_mul A siz l1) ++ list_size_mul A siz l2.  
Proof. 
induction l1 as [ | a1 l1 ]; trivial.
intros; simpl; rewrite IHl1; trivial.
Qed.

Lemma merge1_decreases :
 forall x g l2 l sigma x_val, 
  find X.eq_bool x sigma = Some x_val ->
  size (Term g l2) < size x_val ->
   lt_pb (mk_pb ((x, Term g l2) :: sigma) ((x_val, Term g l2) :: l))
           (mk_pb sigma ((Var x, Term g l2) :: l)).
Proof.
intros x g l2 l sigma x_val x_sigma L; 
unfold lt_pb, measure_for_unif_pb; apply lex_le_meq_lt.
(*  First component : phi1 *)
generalize (Term g l2) L; clear g l2 L; intros t2 L.
unfold phi1;
apply VSet.cardinal_subset; apply VSet.subset_filter.
apply VSet.subset_subset_union.
simpl; intros z z_in_x_val_t2_l; destruct_set z_in_x_val_t2_l z_in_x_val_t2 x_in_l.
destruct_set z_in_x_val_t2 z_in_x_val z_in_t2.
do 2 apply VSet.union_2; apply (solved_var_inc_occ_in_subst _ _ _ _ x_sigma z_in_x_val).
do 2 apply VSet.union_1; apply VSet.union_2; trivial.
apply VSet.union_1; apply VSet.union_2; trivial.
simpl; intros z z_in_x_dom_sig_t2_sigma; 
destruct_set z_in_x_dom_sig_t2_sigma z_in_x_dom_sig z_in_t2_sigma.
destruct (VSet.add_12 _ _ _ z_in_x_dom_sig) as [z_in_x | z_in_dom_sig].
do 3 apply VSet.union_1; left; subst; trivial.
apply VSet.union_2; apply VSet.union_1; trivial.
destruct_set z_in_t2_sigma z_in_t2 z_in_sigma.
do 2 apply VSet.union_1; apply VSet.union_2; trivial.
do 2 apply VSet.union_2; trivial.

intros z; do 2 (rewrite Dummy_bool; rewrite not_solved_var); simpl.
generalize (X.eq_bool_ok z x); case (X.eq_bool z x); [intro z_eq_x; subst z | intro z_diff_x].
intros _; rewrite x_sigma; left; 
do 2 apply VSet.union_1; left; subst; reflexivity.
case_eq (find X.eq_bool z sigma); [ intros z_val z_sigma | intro z_sigma ].
intros [ z_in_x_val_t2_l | z_in_t2_sigma].
destruct_set z_in_x_val_t2_l z_in_x_val_t2 z_in_l.
destruct_set z_in_x_val_t2 z_in_x_val z_in_t2.
right; apply (solved_var_inc_occ_in_subst x z x_val); trivial.
left; apply VSet.union_1; apply VSet.union_2; trivial.
left; apply VSet.union_2; trivial.
destruct_set z_in_t2_sigma z_in_t2 z_in_sigma.
left; apply VSet.union_1; apply VSet.union_2; trivial.
right; trivial.
trivial.

(* Second component phi2 *)
generalize (Term g l2) L; clear g l2 L; intros t2 L.
assert (x_in_dom_sig : VSet.mem x (domain_of_subst sigma)).
unfold VSet.mem; induction sigma as [ | [y t] sigma].
discriminate.
simpl in x_sigma; revert x_sigma;
generalize (X.eq_bool_ok x y); case (X.eq_bool x y); [intro x_eq_y; subst y | intro x_diff_y].
intros _; apply VSet.add_1.
intro x_sigma; apply VSet.add_2;apply IHsigma; trivial.

destruct (mem_split_set _ _ X.eq_bool_ok _ _ x_in_dom_sig) 
      as [x' [s1 [s2 [x_eq_x' [dom_sig_eq_s1_x_s2 _]]]]];
simpl in x_eq_x'; simpl in dom_sig_eq_s1_x_s2.
unfold  VSet.LP.EDS.eq_A, VSet.EDS.eq_A, DecVar.eq_A in *; subst x'.
unfold phi2, size_of_solved_part, size_of_unsolved_part; simpl.
replace (VSet.add x (domain_of_subst sigma)) with (domain_of_subst sigma).
rewrite max_l; [idtac | auto with arith].
rewrite dom_sig_eq_s1_x_s2; do 2 rewrite list_size_mul_app.
simpl; generalize (X.eq_bool_ok x x); case (X.eq_bool x x); [intros _ | intro x_diff_x; apply False_rect; apply x_diff_x; reflexivity].
rewrite x_sigma.
generalize (size_ge_one t2); destruct (size t2) as [ | n2]; 
[intro; absurd (1 <= 0); auto with arith | intros _ ].
apply NatMul.mult_is_complete_equiv.
rewrite <- ass_app; rewrite <- app_comm_cons;
rewrite <- NatMul.LP.permut_add_inside.
rewrite <- ass_app; rewrite <- app_comm_cons; rewrite ass_app;
rewrite <- NatMul.LP.permut_add_inside.
rewrite ass_app;
rewrite <- NatMul.LP.permut_app2.
do 2 rewrite <- list_size_mul_app.
assert (x_not_in_s1_s2 : ~mem (@eq _) x (s1 ++ s2)).
assert (W := VSet.is_a_set (domain_of_subst sigma)).
rewrite dom_sig_eq_s1_x_s2 in W.
assert (P : VSet.LP.permut (x :: s1 ++ s2) (s1 ++ x :: s2)).
rewrite <- VSet.LP.permut_cons_inside; reflexivity.
assert (W'' := VSet.without_red_permut W (VSet.LP.permut_sym P)).
generalize (VSet.without_red_permut W (VSet.LP.permut_sym P)).
unfold VSet.without_red; simpl; unfold DecVar.A, DecVar.eq_bool.
generalize (mem_bool_ok _ _ X.eq_bool_ok x (s1 ++ s2)); case (mem_bool X.eq_bool x (s1 ++ s2)).
intros; discriminate.
intros; assumption.
generalize (s1 ++ s2) x_not_in_s1_s2;
intros s x_not_in_s; induction s as [ | v s].
apply NatMul.LP.permut_refl.
simpl; generalize (X.eq_bool_ok v x); case (X.eq_bool v x); [intro v_eq_x | intro v_diff_x].
absurd (mem (@eq _) x (v :: s)); trivial; subst; left; reflexivity.
rewrite <- NatMul.LP.permut_cons.
apply IHs; intro; apply x_not_in_s; right; trivial.
reflexivity. 
reflexivity. 
reflexivity. 
rewrite VSet.already_mem_add.
reflexivity.
unfold VSet.mem; rewrite dom_sig_eq_s1_x_s2.
rewrite <- mem_or_app; right; left; reflexivity.

(* Third component phi3 *)
unfold phi3, nb_var_eq_of_unsolved_part; simpl.
destruct x_val as [v | f l1].
simpl in L; assert (L' := Nat.nle_succ_0 _ (proj2 (Nat.succ_lt_mono _ _) L)); contradiction.
auto with arith.
Defined.

Definition Inv_solved_part pb :=
  forall x, match find X.eq_bool x pb.(solved_part) with 
               | Some (Var _) => is_a_solved_var x pb = true
               | _ => True
               end.

Lemma merge2_decreases :
 forall x g l2 l sigma x_val, 
 Inv_solved_part (mk_pb sigma ((Var x, Term g l2) :: l)) ->
  find X.eq_bool x sigma = Some x_val ->
  size (Term g l2) >= size x_val ->
  lt_pb (mk_pb sigma ((x_val, Term g l2) :: l)) (mk_pb sigma ((Var x, Term g l2) :: l)).
Proof.
intros x g l2 l sigma x_val Inv_pb x_sigma L; 
assert (x_in_dom_sig : VSet.mem x (domain_of_subst sigma)).
clear Inv_pb; induction sigma as [ | [y t] sigma].
discriminate.
simpl in x_sigma; revert x_sigma;
generalize (X.eq_bool_ok x y); case (X.eq_bool x y); [intro x_eq_y; subst x | intro x_diff_y].
intros _; apply VSet.add_1.
intro; apply VSet.add_2; apply IHsigma; trivial.

unfold lt_pb, measure_for_unif_pb; apply lex_le_meq_lt.
(*  First component : phi1 *)
generalize (Term g l2) L; clear g l2 L Inv_pb; intros t2 L.
unfold phi1;
apply VSet.cardinal_subset; apply VSet.subset_filter.
apply VSet.subset_subset_union.
simpl; intros z z_in_x_val_t2_l; destruct_set z_in_x_val_t2_l z_in_x_val_t2 z_in_l.
destruct_set z_in_x_val_t2 z_in_x_val z_in_t2.
do 2 apply VSet.union_2; refine (solved_var_inc_occ_in_subst _ _ _ _ x_sigma z_in_x_val).
do 2 apply VSet.union_1; apply VSet.union_2; trivial.
apply VSet.union_1; apply VSet.union_2; trivial.
apply VSet.subset_subset_union.
simpl; intros z z_in_dom_sig; apply VSet.union_2; apply VSet.union_1; trivial.
simpl; intros z z_in_sigma; do 2 apply VSet.union_2; trivial.

intros z; do 2 (rewrite Dummy_bool; rewrite not_solved_var); simpl.
destruct (find X.eq_bool z sigma) as [ z_val | ]; trivial.
intros [z_in_x_val_t2_l  | z_in_sigma].
destruct_set z_in_x_val_t2_l z_in_x_val_t2 z_in_l.
destruct_set z_in_x_val_t2 z_in_x_val z_in_t2.
right; apply (solved_var_inc_occ_in_subst x z x_val); trivial.
left; apply VSet.union_1; apply VSet.union_2; trivial.
left; apply VSet.union_2; trivial.
right; trivial.

(* Second component phi2 *)
unfold phi2, size_of_unsolved_part, size_of_solved_part.
generalize (Term g l2) L; clear g l2 L Inv_pb; intros t2 L.
simpl; rewrite max_r; [idtac | unfold ge; trivial].
generalize (size_ge_one t2); destruct (size t2) as [ | n2]; 
[intro; absurd (1<=0); auto with arith | intros _].
apply NatMul.mult_is_complete_equiv.
apply NatMul.LP.permut_refl.

(* Third component phi3 *)
destruct x_val as [ v | f l'].
apply False_rect.
generalize (Inv_pb x); simpl; rewrite x_sigma.
rewrite solved_var; rewrite x_sigma.
intros [ H _ ]; apply H; do 2 apply VSet.union_1; left; reflexivity.
auto with arith.
Defined.

Lemma move_eq_decreases :
 forall x g l2 l sigma, 
  find X.eq_bool x sigma = None ->
  lt_pb (mk_pb ((x, Term g l2) :: sigma) l) (mk_pb sigma ((Var x, Term g l2) :: l)).
Proof.
intros x g l2 l sigma x_sigma; 
unfold lt_pb, measure_for_unif_pb; apply lex_le_meq_lt.
(* First component phi1 *)
generalize (Term g l2); clear g l2; intro t2;
unfold phi1; apply VSet.cardinal_subset.
apply VSet.subset_filter.
simpl.
apply VSet.subset_subset_union.
intros z z_in_l; apply VSet.union_1; apply VSet.union_2; trivial.
apply VSet.subset_subset_union.
intros z z_in_x_dom_sig; 
destruct (VSet.add_12 _ _ _ z_in_x_dom_sig) as [z_eq_x | z_in_dom_sig].
do 3 apply VSet.union_1; left; subst; trivial.
apply VSet.union_2; apply VSet.union_1; trivial.
apply VSet.subset_subset_union.
intros z z_in_t2; do 2 apply VSet.union_1; apply VSet.union_2; trivial.
intros z z_in_sigma; do 2 apply VSet.union_2; trivial.
intros z; do 2 (rewrite Dummy_bool; rewrite not_solved_var); simpl.
generalize (X.eq_bool_ok z x); case (X.eq_bool z x); [intro z_eq_x; subst z | intro z_diff_x].
rewrite x_sigma; trivial.
destruct (find X.eq_bool z sigma) as [z_val | ]; trivial.
intros [z_in_l | z_in_t2_sigma].
left; apply VSet.union_2; trivial.
destruct_set z_in_t2_sigma z_in_t2 z_in_sigma.
left; apply VSet.union_1; apply VSet.union_2; trivial.
right; trivial.

(* Second component phi2 *)
apply NatMul.mult_is_complete_equiv.
unfold phi2, size_of_solved_part, size_of_unsolved_part.
generalize (Term g l2); intro t2; clear g l2; simpl solved_part; simpl unsolved_part.
assert (x_not_in_dom_sig : ~ VSet.mem x (domain_of_subst sigma)).
induction sigma as [ | [y t] sigma].
intro; contradiction.
simpl in x_sigma; intro x_in_y_dom_sig;
destruct (VSet.add_12 _ _ _ x_in_y_dom_sig) as [x_eq_y | x_in_dom_sig];
clear x_in_y_dom_sig.
unfold  VSet.LP.EDS.eq_A, VSet.EDS.eq_A, DecVar.eq_A in *; subst y.
revert x_sigma; generalize (X.eq_bool_ok x x); case (X.eq_bool x x); 
[intros _; discriminate | intro x_diff_x; apply False_rect; apply x_diff_x; reflexivity].
apply IHsigma; trivial.
revert x_sigma; case (X.eq_bool x y); trivial; intros; discriminate.

replace (VSet.support (domain_of_subst ((x, t2) :: sigma))) with (x :: (VSet.support (domain_of_subst sigma))). 
simpl; generalize (X.eq_bool_ok x x); case (X.eq_bool x x); [intros _ | intro x_diff_x; apply False_rect; apply x_diff_x; reflexivity].
generalize (size_ge_one t2); case (size t2).
intro Abs; apply False_rect; apply (Nat.nlt_0_r _ Abs).
intros n _; rewrite <- NatMul.LP.permut_cons_inside.
rewrite <- NatMul.LP.permut_app2.
clear l; revert x_not_in_dom_sig; unfold VSet.mem, DecVar.eq_A.
generalize (VSet.support (domain_of_subst sigma)); fix move_eq_decreases 1.
intro l; case l; clear l.
intros _; reflexivity.
simpl; intros a l x_not_in_al.
generalize (X.eq_bool_ok a x); case (X.eq_bool a x); [intro a_eq_x | intros _].
apply False_rect; apply x_not_in_al; left; symmetry; assumption.
rewrite <- NatMul.LP.permut_cons.
apply move_eq_decreases.
intro x_in_l; apply x_not_in_al; right; assumption.
reflexivity.
reflexivity.
revert x_not_in_dom_sig; simpl; apply VSet.not_already_mem_add.

(* Third component phi3 *)
unfold phi3, nb_var_eq_of_unsolved_part; simpl; auto with arith.
Defined.

Lemma decomposition_decreases :
 forall f l1 l2 l sigma,
   lt_pb (mk_pb sigma (combine term l l1 l2)) 
         (mk_pb sigma ((Term f l1, Term f l2) :: l)).
Proof.
intros f l1 l2 l sigma; unfold lt_pb, measure_for_unif_pb; apply lex_le_lt.

(* First component phi1 *)
assert (H : forall z, 
             VSet.mem z (set_of_variables_in_unsolved_part (combine term l l1 l2)) ->
             VSet.mem z (set_of_variables_in_unsolved_part ((Term f l1, Term f l2) :: l))).
unfold set_of_variables_in_unsolved_part at 2.
unfold set_of_variables.
revert l2 l; induction l1 as [ | t1 l1]; intros [ | t2 l2] l z.
simpl; intros; apply VSet.union_2; trivial.
simpl; intros; apply VSet.union_2; trivial.
simpl; intros; apply VSet.union_2; trivial.
intro H; assert (z_in_l1l2_t1t2l := IHl1 l2 ((t1,t2) :: l) z H).
destruct_set z_in_l1l2_t1t2l z_in_l1l2 z_in_t1t2l.
destruct_set z_in_l1l2 z_in_l1 z_in_l2.
apply VSet.union_1; apply VSet.union_1; apply VSet.union_2; trivial.
apply VSet.union_1; apply VSet.union_2; apply VSet.union_2; trivial.
destruct_set z_in_t1t2l z_in_t1t2 z_in_l.
destruct_set z_in_t1t2 z_in_t1 z_in_t2.
do 3 apply VSet.union_1; trivial.
apply VSet.union_1; apply VSet.union_2; apply VSet.union_1; trivial.
apply VSet.union_2; trivial.
unfold phi1; apply VSet.cardinal_subset; apply VSet.subset_filter.
apply VSet.subset_subset_union.
intros z z_in_l1_l2_l; generalize (H _ z_in_l1_l2_l); clear z_in_l1_l2_l; intro z_in_l1_l2_l.
destruct_set z_in_l1_l2_l z_in_l1_l2 z_in_l.
destruct_set z_in_l1_l2 z_in_l1 z_in_l2.
simpl; do 3 apply VSet.union_1; trivial.
simpl; do 2 apply VSet.union_1; apply VSet.union_2; trivial.
simpl; apply VSet.union_1; apply VSet.union_2; trivial.
apply VSet.subset_subset_union.
intros z z_in_dom_sig; apply VSet.union_2; apply VSet.union_1; trivial.
intros z z_in_sigma; do 2 apply VSet.union_2; trivial.

intro z; do 2 (rewrite Dummy_bool; rewrite not_solved_var);
simpl; destruct (find X.eq_bool z sigma) as [z_val | ]; trivial.
intros [H1 | H1].
left; apply H; trivial.
right; trivial.

(* Second component phi2 *)
apply NatMul.mult_is_complete_less_than with lt.
exact lt_bool_ok.
intros n1 n2 n3; apply Nat.lt_trans.
apply Nat.lt_irrefl.
unfold phi2, size_of_solved_part, size_of_unsolved_part; simpl.
unfold lt_mul; apply NatMul.context_trans_clos_multiset_extension_step_app1.
do 2 rewrite (list_size_fold size).
revert l2 l; induction l1 as [ | t1 l1]; intros [ | t2 l2] l.
left; simpl;
refine (@NatMul.rmv_case lt _ _ 
                (list_size_mul (term * term)
                (fun s_t : term * term => let (s, t) := s_t in max (size s) (size t)) l)
                nil 1 _ _ _); try apply NatMul.LP.permut_refl. 
intros; contradiction.
left; simpl;
refine (@NatMul.rmv_case lt _ _ 
                (list_size_mul (term * term)
                (fun s_t : term * term => let (s, t) := s_t in max (size s) (size t)) l)
                nil _ _ _ _); try apply NatMul.LP.permut_refl. 
intros; contradiction.
left; simpl;
refine (@NatMul.rmv_case lt _ _ 
                (list_size_mul (term * term)
                (fun s_t : term * term => let (s, t) := s_t in max (size s) (size t)) l)
                nil _ _ _ _); try apply NatMul.LP.permut_refl. 
intros; contradiction.

generalize (IHl1 l2 ((t1,t2) :: l)).
simpl list_size; simpl combine; simpl list_size_mul.
generalize (size_ge_one t1) (size_ge_one t2).
generalize (list_size_mul (term * term)
     (fun s_t : term * term => let (s, t) := s_t in max (size s) (size t))
     (combine term ((t1, t2) :: l) l1 l2))
(list_size size l1) (list_size size l2) (size t1) (size t2)
(list_size_mul (term * term)
        (fun s_t : term * term => let (s, t) := s_t in max (size s) (size t)) l).
clear t1 l1 sigma IHl1 t2 l2 l.
intros nl nl1 nl2 nt1 nt2 n H1 H2.
intro H; refine (@trans_clos_is_trans _ (NatMul.multiset_extension_step lt) _ _ _ H _).
left;
apply (NatMul.rmv_case lt 
                       (l1 := S (max nl1 nl2) :: max nt1 nt2 :: n)
                       (l2 := S (max (nt1 + nl1) (nt2 + nl2)) :: n)
                       (l := n)
                       (S (max nl1 nl2) :: max nt1 nt2 :: nil)
                       (a := S (max (nt1 + nl1) (nt2 + nl2)))).
unfold  NatMul.DS.eq_A.
intros b [b_eq | [b_eq | b_in_nil]].
subst b. apply le_n_S; apply (Nat.max_case nl1 nl2).
refine (Nat.le_trans _ _ _ _ (Nat.le_max_l _ _)); destruct nt1 as [ | nt1].
inversion H1.
simpl; apply le_n_S; apply NatCompat.le_add_l.
refine (Nat.le_trans _ _ _ _ (Nat.le_max_r _ _)); destruct nt2 as [ | nt2].
inversion H2.
simpl; apply le_n_S; apply NatCompat.le_add_l.
subst b; apply (Nat.max_case nt1 nt2).
simpl; apply le_n_S; refine (Nat.le_trans _ _ _ _ (Nat.le_max_l _ _)); apply Nat.le_add_r.
simpl; apply le_n_S; refine (Nat.le_trans _ _ _ _ (Nat.le_max_r _ _)); apply Nat.le_add_r.
contradiction.
reflexivity.
reflexivity.
Defined.

Lemma inv_solved_part :
  forall pb, Inv_solved_part pb -> 
  match decomposition_step pb with
   | Normal _ pb' => Inv_solved_part pb'
   | _ => True
   end.
Proof.
unfold Inv_solved_part, decomposition_step; simpl.
intros [sigma [ | [s t] l]] Inv_pb; simpl.
trivial.
generalize (T1.eq_bool_ok s t); case (T1.eq_bool  s t); [intros _ | intro s_diff_t].
(* 1/1 Trivial Equation *)
intros x; generalize (Inv_pb x); clear Inv_pb; simpl solved_part.
case_eq (find X.eq_bool x sigma); [idtac | trivial].
intros [y | ]; [idtac | trivial].
intro F; do 2 rewrite solved_var; rewrite F.
intros [H1 H2]; split; [idtac | assumption].
intro H; apply H1; apply VSet.union_2; trivial.

destruct s as [x | f l1]; destruct t as [y | g l2].
(* 1/4 Coalesce *)
assert (Hx := find_map_subst x x (Var y) sigma).
case_eq (find X.eq_bool x sigma); [ intros x_val x_sigma | intro x_sigma];  
rewrite x_sigma in Hx; rewrite Hx; simpl.
intro z; generalize (Inv_pb z); simpl; clear Inv_pb.
generalize (X.eq_bool_ok z x); case (X.eq_bool z x); [intro z_eq_x; subst z | intro z_diff_x].
intro Inv_pb_x; rewrite solved_var; simpl.
generalize (X.eq_bool_ok x x); case (X.eq_bool x x); [intros _; split | intro x_diff_x; apply False_rect; apply x_diff_x; reflexivity].
intro x_in_y_x_val'_l'; destruct_set x_in_y_x_val'_l' x_in_y_x_val' x_in_l'.
destruct_set x_in_y_x_val' x_in_y x_in_x_val'.
apply s_diff_t; apply f_equal; destruct x_in_y as [x_eq_y | x_in_nil]; [trivial | contradiction].
refine (solved_var_inc_not_mem _ _ _ _ x_in_x_val'); intro; apply s_diff_t; subst; trivial.
refine (solved_var_inc_not_mem_list _ _ _ _ x_in_l'); intro; apply s_diff_t; subst; trivial.
intro x_in_y_sigma'; destruct_set x_in_y_sigma' x_in_y x_in_sigma'.
apply s_diff_t; apply f_equal; destruct x_in_y as [x_eq_y | x_in_nil]; [trivial | contradiction].
refine (solved_var_inc_not_mem_subst _ _ _ _ x_in_sigma'); intro; apply s_diff_t; subst; trivial.
assert (Hz := find_map_subst z x (Var y) sigma).
case_eq (find X.eq_bool z sigma); [ intros z_val z_sigma| intro z_sigma]; 
rewrite z_sigma in Hz; rewrite Hz; [idtac | trivial].
destruct z_val as [v | f l']; simpl; [rewrite solved_var; rewrite z_sigma | trivial].
assert (H : match (if eq_var_bool v x then Some (Var y) else None) with
                       | Some v_sigma => v_sigma
                       | None => Var v
                       end = Var (if eq_var_bool v x then y else v)).
case (X.eq_bool v x); reflexivity.
rewrite H; clear H; rewrite solved_var; intros [z_not_in_x_y_l z_not_in_sigma].
simpl; generalize (X.eq_bool_ok z x); case (X.eq_bool z x); [intro z_eq_x; absurd (z=x); assumption | intros _].
rewrite Hz; split.
intro z_in_y_x_val'_l'.
destruct_set z_in_y_x_val'_l' z_in_y_x_val' z_in_l'.
destruct_set z_in_y_x_val' z_in_y z_in_x_val'.
apply z_not_in_x_y_l; apply VSet.union_1; apply VSet.union_2; trivial.
generalize (X.eq_bool_ok z y); case (X.eq_bool z y); [intro z_eq_y | intro z_diff_y].
apply z_not_in_x_y_l; apply VSet.union_1; apply VSet.union_2; left; subst; reflexivity.
apply z_not_in_sigma; apply solved_var_inc_subst with x y; trivial;
apply (solved_var_inc_occ_in_subst _ _ _ _ Hx z_in_x_val').
generalize (X.eq_bool_ok z y); case (X.eq_bool z y); [intro z_eq_y | intro z_diff_y].
apply z_not_in_x_y_l; apply VSet.union_1; apply VSet.union_2; left; subst; reflexivity.
apply z_not_in_x_y_l; apply VSet.union_2; apply solved_var_inc_list with x y; trivial.
intro z_in_y_sigma; destruct_set z_in_y_sigma z_in_y z_in_sigma.
apply z_not_in_x_y_l; unfold VSet.mem in *; apply VSet.union_1; apply VSet.union_2; trivial.
generalize (X.eq_bool_ok z y); case (X.eq_bool z y); [intro z_eq_y | intro z_diff_y].
apply z_not_in_x_y_l; unfold VSet.mem in *; apply VSet.union_1; apply VSet.union_2; left; subst; reflexivity.
apply z_not_in_sigma; apply solved_var_inc_subst with x y; trivial.

intro z; generalize (Inv_pb z); simpl; clear Inv_pb.
generalize (X.eq_bool_ok z x); case (X.eq_bool z x); [intro z_eq_x; subst z | intro z_diff_x].
intros _; rewrite solved_var; simpl.
generalize (X.eq_bool_ok x x); case (X.eq_bool x x); [intros _; split | intro x_diff_x; apply False_rect; apply x_diff_x; reflexivity].
intro x_in_l'; refine (solved_var_inc_not_mem_list _ _ _ _ x_in_l'); intro; apply s_diff_t; subst; trivial.
intro x_in_y_sigma'; destruct_set x_in_y_sigma' x_in_y x_in_sigma'.
apply s_diff_t; apply f_equal; destruct x_in_y as [x_eq_y | x_in_nil]; [trivial | contradiction].
refine (solved_var_inc_not_mem_subst _ _ _ _ x_in_sigma'); intro; apply s_diff_t; subst; trivial.
assert (Hz := find_map_subst z x (Var y) sigma).
case_eq (find X.eq_bool z sigma); [ intros z_val z_sigma | intros z_sigma];
rewrite z_sigma in Hz; rewrite Hz; [idtac | trivial].
destruct z_val as [v | f l']; simpl; [idtac | trivial].
assert (H : match (if eq_var_bool v x then Some (Var y) else None) with
                       | Some v_sigma => v_sigma
                       | None => Var v
                       end = Var (if eq_var_bool v x then y else v)).
case (X.eq_bool v x); reflexivity.
rewrite H; clear H; do 2 rewrite solved_var; rewrite z_sigma.
intros [z_not_in_x_y_l z_not_in_sigma]; simpl.
generalize (X.eq_bool_ok z x); case (X.eq_bool z x); [intro z_eq_x; subst z | intros _; rewrite Hz; split].
apply False_rect; apply z_diff_x; reflexivity.
intro z_in_l'.
generalize (X.eq_bool_ok z y); case (X.eq_bool z y); [intro z_eq_y | intro z_diff_y].
apply z_not_in_x_y_l; apply VSet.union_1; apply VSet.union_2; left; subst; reflexivity.
apply z_not_in_x_y_l; apply VSet.union_2; apply solved_var_inc_list with x y; trivial.
intro z_in_y_sigma; destruct_set z_in_y_sigma z_in_y z_in_sigma.
apply z_not_in_x_y_l; unfold VSet.mem in *; apply VSet.union_1; apply VSet.union_2; trivial.
generalize (X.eq_bool_ok z y); case (X.eq_bool z y); [intro z_eq_y | intro z_diff_y].
apply z_not_in_x_y_l; unfold VSet.mem in *; apply VSet.union_1; apply VSet.union_2; left; subst; reflexivity.
apply z_not_in_sigma; apply solved_var_inc_subst with x y; trivial.

case_eq (find X.eq_bool x sigma); [ intros x_val x_sigma | intro x_sigma].
(* 1/4 Merge *)
destruct (lt_ge_dec (T.size (Term g l2)) (T.size x_val)) as [ L | L ].
intro z; generalize (Inv_pb z); simpl; clear Inv_pb. 
simpl; generalize (X.eq_bool_ok z x); case (X.eq_bool z x); [intros _; trivial | intro z_diff_x].
case_eq (find X.eq_bool z sigma); [ intros z_val z_sigma | intros _; trivial].
destruct z_val as [v | f l']; [idtac | trivial].
do 2 rewrite solved_var; simpl find; rewrite z_sigma.
generalize (X.eq_bool_ok z x); case (X.eq_bool z x); [intros x_eq_z; absurd (z =x); assumption | intros _].
intros [z_not_in_x_t2_l z_not_in_sigma]; 
split; [intro z_in_x_val_t2_l | intro z_in_t2_sigma].
destruct_set z_in_x_val_t2_l z_in_x_val_t2 z_in_l.
destruct_set z_in_x_val_t2 z_in_x_val z_in_t2.
apply z_not_in_sigma; apply solved_var_inc_occ_in_subst with x x_val; trivial.
apply z_not_in_x_t2_l; simpl; unfold VSet.mem in *; 
apply VSet.union_1; apply VSet.union_2; trivial.
apply z_not_in_x_t2_l; simpl; unfold VSet.mem in *; apply VSet.union_2; trivial.
destruct_set z_in_t2_sigma z_in_t2 z_in_sigma.
apply z_not_in_x_t2_l; simpl; unfold VSet.mem in *; 
apply VSet.union_1; apply VSet.union_2; trivial.
apply z_not_in_sigma; trivial.
intro z; generalize (Inv_pb z); simpl; clear Inv_pb.
case_eq (find X.eq_bool z sigma); [ intros z_val z_sigma | intros _; trivial].
destruct z_val as [v | f l']; [idtac | trivial].
do 2 rewrite solved_var; rewrite z_sigma.
intros [z_not_in_x_t2_l z_not_in_sigma]; 
split; [intro z_in_x_val_t2_l | assumption].
destruct_set z_in_x_val_t2_l z_in_x_val_t2 z_in_l.
destruct_set z_in_x_val_t2 z_in_x_val z_in_t2.
apply z_not_in_sigma; apply solved_var_inc_occ_in_subst with x x_val; trivial.
apply z_not_in_x_t2_l; apply VSet.union_1; apply VSet.union_2; trivial.
apply z_not_in_x_t2_l; apply VSet.union_2; trivial.

(* 1/3 Move an equation  *)
intros z; generalize (Inv_pb z); simpl; clear Inv_pb.
generalize (X.eq_bool_ok z x); case (X.eq_bool z x); [intros z_eq_x; subst z | intro z_diff_x].
rewrite x_sigma; trivial.
case_eq (find X.eq_bool z sigma); [ intros z_val z_sigma | intros _; trivial].
destruct z_val as [v | f l']; [idtac | trivial].
do 2 rewrite solved_var; simpl find; rewrite z_sigma.
generalize (X.eq_bool_ok z x); case (X.eq_bool z x); [intros z_eq_x; absurd (z =x); trivial | intros _].
intros [z_not_in_x_t2_l z_not_in_sigma]; 
split; [intro z_in_x_val_t2_l | intro z_in_t2_sigma].
apply z_not_in_x_t2_l; apply VSet.union_2; assumption.
destruct_set z_in_t2_sigma z_in_t2 z_in_sigma.
apply z_not_in_x_t2_l; apply VSet.union_1; apply VSet.union_2; assumption.
apply z_not_in_sigma; assumption.

case_eq (find X.eq_bool y sigma); [ intros y_val y_sigma | intro y_sigma].
(* 1/3 Merge (sym) *)
destruct (lt_ge_dec (T.size (Term f l1)) (T.size y_val)) as [ L | L ].
intro z; generalize (Inv_pb z); simpl; clear Inv_pb. 
simpl; generalize (X.eq_bool_ok z y); case (X.eq_bool z y); [intros _; trivial | intro z_diff_y].
case_eq (find X.eq_bool z sigma); [ intros z_val z_sigma | intros _; trivial].
destruct z_val as [v | g l']; [idtac | trivial].
do 2 rewrite solved_var; simpl find; rewrite z_sigma.
generalize (X.eq_bool_ok z y); case (X.eq_bool z y); [intros z_eq_y; absurd (z =y); assumption | intros _].
intros [z_not_in_y_t1_l z_not_in_sigma]; 
split; [intro z_in_y_val_t1_l | intro z_in_t1_sigma].
destruct_set z_in_y_val_t1_l z_in_y_val_t1 z_in_l.
destruct_set z_in_y_val_t1 z_in_y_val z_in_t1.
apply z_not_in_sigma; apply solved_var_inc_occ_in_subst with y y_val; trivial.
apply z_not_in_y_t1_l; apply VSet.union_1; apply VSet.union_1; trivial.
apply z_not_in_y_t1_l; apply VSet.union_2; trivial.
destruct_set z_in_t1_sigma z_in_t1 z_in_sigma.
apply z_not_in_y_t1_l; apply VSet.union_1; apply VSet.union_1; trivial.
apply z_not_in_sigma; trivial.
intro z; generalize (Inv_pb z); simpl; clear Inv_pb.
case_eq (find X.eq_bool z sigma); [ intros z_val z_sigma | intros _; trivial].
destruct z_val as [v | g l']; [idtac | trivial].
do 2 rewrite solved_var; rewrite z_sigma.
intros [z_not_in_y_t1_l z_not_in_sigma]; 
split; [intro z_in_y_val_t1_l | assumption].
destruct_set z_in_y_val_t1_l z_in_y_val_t1 z_in_l.
destruct_set z_in_y_val_t1 z_in_y_val z_in_t1.
apply z_not_in_sigma; apply solved_var_inc_occ_in_subst with y y_val; trivial.
apply z_not_in_y_t1_l; apply VSet.union_1; apply VSet.union_1; trivial.
apply z_not_in_y_t1_l; apply VSet.union_2; trivial.

(* 1/2 Move an equation (sym) *)
intros z; generalize (Inv_pb z); simpl; clear Inv_pb.
generalize (X.eq_bool_ok z y); case (X.eq_bool z y); [intros z_eq_y; subst z | intro z_diff_y].
rewrite y_sigma; trivial.
case_eq (find X.eq_bool z sigma); [ intros z_val z_sigma | intros _; trivial].
destruct z_val as [v | g l']; [idtac | trivial].
do 2 rewrite solved_var; simpl find; rewrite z_sigma.
generalize (X.eq_bool_ok z y); case (X.eq_bool z y); [intros z_eq_y; absurd (z =y); trivial | intros _].
intros [z_not_in_y_t1_l z_not_in_sigma]; 
split; [intro z_in_y_val_t1_l | intro z_in_t1_sigma].
apply z_not_in_y_t1_l; apply VSet.union_2; assumption.
destruct_set z_in_t1_sigma z_in_t1 z_in_sigma.
apply z_not_in_y_t1_l; apply VSet.union_1; apply VSet.union_1; assumption.
apply z_not_in_sigma; assumption.

(* 1/1 Decomposition *)
generalize (F.Symb.eq_bool_ok f g); case (F.Symb.eq_bool f g); [intro f_eq_g; subst g | intros _; trivial].
generalize (beq_nat_ok (length l1) (length l2)); case (Nat.eqb (length l1) (length l2)); intro L; trivial.
intros z; generalize (Inv_pb z); clear Inv_pb; simpl.
case_eq (find X.eq_bool z sigma); [ intros z_val z_sigma | intros _; trivial].
destruct z_val as [v | h l']; trivial.
do 2 rewrite solved_var; rewrite z_sigma.
intros [z_not_in_t1_t2_l z_not_in_sigma]; split; [intro z_in_l1_l2_l | trivial].
apply z_not_in_t1_t2_l.
clear z_sigma z_not_in_t1_t2_l z_not_in_sigma s_diff_t.
clear L.
revert l2 l z_in_l1_l2_l; induction l1 as [ | t1 l1]; intros [ | t2 l2] l z_in_l1_l2_l.
apply VSet.union_2; trivial.
apply VSet.union_2; trivial.
apply VSet.union_2; trivial.
generalize (IHl1 l2 ((t1,t2) :: l) z_in_l1_l2_l); clear z_in_l1_l2_l; intro z_in_l1_l2_l.
destruct_set z_in_l1_l2_l z_in_t1_t2 z_in_l1_l2_l'.
destruct_set z_in_t1_t2 z_in_t1 z_in_t2.
apply VSet.union_1; apply VSet.union_1; apply VSet.union_2; trivial.
apply VSet.union_1; apply VSet.union_2; apply VSet.union_2; trivial.
destruct_set z_in_l1_l2_l' z_in_l1_l2 z_in_l.
destruct_set z_in_l1_l2 z_in_l1 z_in_l2.
do 3 apply VSet.union_1; trivial.
apply VSet.union_1; apply VSet.union_2; apply VSet.union_1; trivial.
apply VSet.union_2; trivial.
Defined.

Lemma solved_var_swapp_eq :
  forall x s t l sigma, is_a_solved_var x (mk_pb sigma ((s,t) :: l)) =
    is_a_solved_var x (mk_pb sigma ((t,s) :: l)).
Proof.
intros x s t l sigma; case_eq (is_a_solved_var x (mk_pb sigma ((s, t) :: l))).
intro x_solved; rewrite solved_var in x_solved; symmetry; rewrite solved_var.
destruct (find X.eq_bool x sigma) as [x_val | ]; trivial.
destruct x_solved as [x_not_in_s_t_l x_not_in_sigma]; split; [intros x_in_t_s_l | trivial].
apply x_not_in_s_t_l; destruct_set x_in_t_s_l x_in_t_s x_in_l.
destruct_set x_in_t_s x_in_t x_in_s.
apply VSet.union_1; apply VSet.union_2; trivial.
do 2 apply VSet.union_1; trivial.
apply VSet.union_2; trivial.
intro x_not_solved; rewrite not_solved_var in x_not_solved; symmetry; rewrite not_solved_var.
destruct (find X.eq_bool x sigma) as [x_val | ]; trivial.
destruct x_not_solved as [x_in_s_t_l | x_in_sigma]; [left | right; trivial].
destruct_set x_in_s_t_l x_in_s_t x_in_l.
destruct_set x_in_s_t x_in_s x_in_t.
apply VSet.union_1; apply VSet.union_2; trivial.
do 2 apply VSet.union_1; trivial.
apply VSet.union_2; trivial.
Defined.

Lemma measure_for_unif_pb_swapp_eq :
  forall s t l sigma,
  measure_for_unif_pb (mk_pb sigma ((s,t) :: l)) = measure_for_unif_pb (mk_pb sigma ((t,s) :: l)).
Proof.
intros s t l sigma.
assert (Phi1 : phi1 (mk_pb sigma ((s,t) :: l)) = phi1 (mk_pb sigma ((t,s) :: l))).
unfold phi1; apply VSet.cardinal_eq_set; 
intro v; split; apply VSet.subset_filter; clear v; intro v.
simpl; intro v_in_s_t_l_sigma; destruct_set  v_in_s_t_l_sigma v_in_s_t_l v_in_sigma.
destruct_set  v_in_s_t_l v_in_s_t v_in_l.
destruct_set  v_in_s_t v_in_s v_in_t.
do 2 apply VSet.union_1; apply VSet.union_2; trivial.
do 3 apply VSet.union_1; trivial.
apply VSet.union_1; apply VSet.union_2; trivial.
apply VSet.union_2; trivial.
intro H; rewrite solved_var_swapp_eq; trivial.
simpl; intro v_in_s_t_l_sigma; destruct_set  v_in_s_t_l_sigma v_in_s_t_l v_in_sigma.
destruct_set  v_in_s_t_l v_in_s_t v_in_l.
destruct_set  v_in_s_t v_in_s v_in_t.
do 2 apply VSet.union_1; apply VSet.union_2; trivial.
do 3 apply VSet.union_1; trivial.
apply VSet.union_1; apply VSet.union_2; trivial.
apply VSet.union_2; trivial.
intro H; rewrite solved_var_swapp_eq; trivial.
assert (Phi2 : phi2 (mk_pb sigma ((s,t) :: l)) = phi2 (mk_pb sigma ((t,s) :: l))).
unfold phi2, size_of_solved_part, size_of_unsolved_part; simpl;
rewrite Nat.max_comm; trivial.

assert (Phi3 : phi3 (mk_pb sigma ((s,t) :: l)) = phi3 (mk_pb sigma ((t,s) :: l))).
unfold phi3, nb_var_eq_of_unsolved_part; simpl;
destruct s; destruct t; trivial.

unfold measure_for_unif_pb; rewrite Phi1; rewrite Phi2; rewrite Phi3; trivial.
Defined.

Lemma decomposition_step_decreases :
  forall pb, Inv_solved_part pb ->
   match decomposition_step pb with
  | Normal _ pb' => lt_pb pb' pb
  | _ => True
  end.
Proof.
intros [sigma [ | [s t] l]] Inv_pb; simpl; trivial.
unfold decomposition_step; simpl unsolved_part; cbv iota beta.
generalize (T1.eq_bool_ok s t); case (T1.eq_bool s t); [intro s_eq_t | intro s_diff_t].
subst s; apply remove_trivial_eq_decreases.
destruct s as [ x | f l1 ]; destruct t as [ y | g l2].
assert (Hx := find_map_subst x x (Var y) sigma).
case_eq (find X.eq_bool x sigma); [intros x_val x_sigma | intro x_sigma ];
rewrite x_sigma in Hx; simpl solved_part; rewrite Hx.
apply coalesce1_decreases; trivial; intro; apply s_diff_t; subst; trivial.
apply coalesce2_decreases; trivial; intro; apply s_diff_t; subst; trivial.

simpl solved_part.
case_eq (find X.eq_bool x sigma); [intros x_val x_sigma | intro x_sigma ].
destruct (lt_ge_dec (T.size (Term g l2)) (T.size x_val)) as [t2_lt_x_val | t2_ge_x_val].
apply merge1_decreases; trivial.
apply merge2_decreases; trivial.
apply move_eq_decreases; trivial.

simpl solved_part.
case_eq (find X.eq_bool y sigma); [intros y_val y_sigma | intro y_sigma ].
destruct (lt_ge_dec (T.size (Term f l1)) (T.size y_val)) as [t1_lt_y_val | t1_ge_y_val].
unfold lt_pb; rewrite (measure_for_unif_pb_swapp_eq (Term f l1));
apply merge1_decreases; trivial.
unfold lt_pb; rewrite (measure_for_unif_pb_swapp_eq (Term f l1));
apply merge2_decreases; trivial.
unfold Inv_solved_part in *; simpl solved_part in *; intros x; generalize (Inv_pb x).
destruct (find X.eq_bool x sigma) as [[v | f' l'] | ]; trivial.
intro H; rewrite solved_var_swapp_eq; trivial.

unfold lt_pb; rewrite (measure_for_unif_pb_swapp_eq (Term f l1));
apply move_eq_decreases; trivial.

generalize (F.Symb.eq_bool_ok f g); case (F.Symb.eq_bool f g); [intro f_eq_g; subst g | intros _; trivial].
generalize (beq_nat_ok (length l1) (length l2)); case (Nat.eqb (length l1) (length l2)); intro L; trivial.
simpl solved_part; apply decomposition_decreases.
Defined.

(** *** Definition of a step of decomposition for the loop. *)

Definition Inv_solved_part_e e :=
  match e with
  | Normal _ pb => Inv_solved_part pb
  | Not_appliable _ pb => pb.(unsolved_part) = nil
  | No_solution _ => True
  end.

Inductive exc_pb_ok : Type :=
  | OK : forall (e : exc unification_problem), Inv_solved_part_e e -> exc_pb_ok.

Definition weight_exc_pb_ok  e := 
   match e with
   | OK (Normal _ pb)  _  => (2, measure_for_unif_pb pb)
   | OK (Not_appliable _ pb) _  => (1, measure_for_unif_pb pb)
   | OK (No_solution _) _ => (0, (0,(nil,0)))
   end.

Definition lt_weight_exc_pb_ok (w1 w2 : nat * (nat * (list nat * nat))) :=
  match w1, w2 with
  | (n1,m1), (n2,m2) =>
     if Nat.eqb n1 n2
     then lt_ms m1 m2
     else n1 < n2
end.

Definition lt_exc_pb_ok (u1 u2 : exc_pb_ok) :=
  lt_weight_exc_pb_ok (weight_exc_pb_ok u1) (weight_exc_pb_ok u2).

Lemma wf_lt_exc_pb_ok : well_founded lt_exc_pb_ok.
Proof.
apply (wf_inverse_image (exc_pb_ok) _ lt_weight_exc_pb_ok weight_exc_pb_ok).
unfold well_founded, lt_weight_exc_pb_ok.
intros [n m]; generalize m; clear m; pattern n.
refine (well_founded_ind lt_wf _ _ n).
clear n; intros n IHn m; apply Acc_intro.
intros [n' m']; generalize (beq_nat_ok n' n); case (Nat.eqb n' n); [intro n'_eq_n; subst n' | intro n'_diff_n].
revert m'; pattern m; refine (well_founded_ind wf_lt_ms _ _ m); clear m.
intros m IHm m' m'_lt_m; apply Acc_intro.
intros [n'' m'']; generalize (beq_nat_ok n'' n); case (Nat.eqb n'' n); [intro n''_eq_n | intro n''_diff_n].
subst n''; apply IHm; trivial.
intro n''_lt_n; apply IHn; trivial.
intro n'_lt_n; apply IHn; trivial.
Defined.

Lemma inv_solved_part_e : 
  forall pb, Inv_solved_part pb \/ pb.(unsolved_part) = nil -> Inv_solved_part_e (decomposition_step pb).
Proof.
intros [sigma [ | [s t] l]] [Inv_pb | l_eq_nil].
simpl; trivial.
simpl; trivial.
generalize (inv_solved_part _ Inv_pb); unfold decomposition_step; simpl.
case (T1.eq_bool  s t).
trivial.
destruct s as [x | f1 l1]; destruct t as [y | f2 l2].
case (find X.eq_bool x
             (map_subst
               (fun (_ : variable) (v_sigma : term) =>
                 apply_subst ((x, Var y) :: nil) v_sigma) sigma)); trivial.
case (find X.eq_bool x sigma); trivial.
intro x_val; case (lt_ge_dec (T.size (Term f2 l2)) (T.size x_val)); trivial.
case (find X.eq_bool y sigma); trivial.
intro y_val; case (lt_ge_dec (T.size (Term f1 l1)) (T.size y_val)); trivial.
case (F.Symb.eq_bool f1 f2); trivial.
case (Nat.eqb (length l1) (length l2)); trivial.
discriminate.
Defined.

Definition decomposition_step_e : exc_pb_ok -> exc_pb_ok.
intros [ [ pb | pb | ]  Inv_pb ].
exact (OK (decomposition_step pb) (inv_solved_part_e _ (or_introl _ Inv_pb))).
exact (OK (Not_appliable _ pb) Inv_pb).
exact (OK (No_solution _) Inv_pb).
Defined.

Lemma decomposition_e_unfold_not_app :
forall pb Inv_pb, 
  decomposition_step_e (OK (Not_appliable _ pb) Inv_pb) = OK (Not_appliable _ pb) Inv_pb. 
Proof.
intros; simpl; trivial.
Qed.

Lemma decomposition_e_unfold_no_sol :
  forall Inv_pb,
  decomposition_step_e (OK (No_solution _) Inv_pb) = OK (No_solution _) Inv_pb.
Proof.
intros; simpl; trivial.
Qed.

Lemma decomposition_e_unfold_normal :
forall pb Inv_pb, 
  decomposition_step_e (OK (Normal _ pb) Inv_pb) = 
 OK (decomposition_step pb) (inv_solved_part_e _ (or_introl _ Inv_pb)).
Proof.
intros pb Inv_pb; simpl; trivial.
Defined.

Lemma decomposition_step_decreases_e :
  forall pb (Inv_pb : Inv_solved_part pb),
  lt_exc_pb_ok (decomposition_step_e (OK (Normal _ pb) Inv_pb)) (OK (Normal _ pb) Inv_pb).
Proof. 
intros pb Inv_pb; rewrite decomposition_e_unfold_normal.
unfold lt_exc_pb_ok, lt_weight_exc_pb_ok, lt_pb; simpl.
generalize (decomposition_step_decreases pb Inv_pb). 
destruct (decomposition_step pb).
trivial.
intros _; generalize (beq_nat_ok 1 2); case (Nat.eqb 1 2); [intros; discriminate | auto with arith].
intros _; generalize (beq_nat_ok 0 2); case (Nat.eqb 0 2); [intros; discriminate | auto with arith].
Defined.

Definition F_decompose : 
  forall (u : exc_pb_ok),
 (forall u' : exc_pb_ok , lt_exc_pb_ok u' u -> exc unification_problem) -> 
 exc unification_problem.
Proof.
intros [[pb | pb | ] Inv_pb] IH.
(* 1 Normal Case *)
exact (IH _ (decomposition_step_decreases_e pb Inv_pb)).
(* 2 Not_appliable Case *)
exact (Not_appliable _ pb).
(* 3 No_solution Case *)
exact (No_solution _).
Defined.

Definition decompose :  forall (u : exc_pb_ok),  (exc unification_problem).
Proof.
intros u; exact (Fix wf_lt_exc_pb_ok (fun _ => exc unification_problem) 
                             F_decompose u).
Defined.


Lemma decompose_unfold : forall u : exc_pb_ok,
decompose u = @F_decompose u (fun u' _ => decompose u').
Proof.
intros u; unfold decompose;
apply Fix_eq with (P:= (fun _: exc_pb_ok => exc unification_problem)); clear u.
intros [ [pb | pb | ] Inv_pb] f g H; simpl; [ rewrite H | idtac | idtac ]; trivial.
Qed.

Lemma decompose_nf :
  forall e,
  match decompose e with
  | Normal _ _ => False
  | Not_appliable _ (mk_pb sigma l) => l = nil
  | No_solution _ => True
  end.
Proof. 
intros e; pattern e; apply (well_founded_ind wf_lt_exc_pb_ok); clear e.
intros [ [pb | pb | ] Inv_pb] IH; rewrite decompose_unfold; simpl.
apply IH; refine (decomposition_step_decreases_e _ Inv_pb).
simpl in Inv_pb; destruct pb; trivial.
trivial.
Qed.

Definition is_a_solution_e e sigma :=
  match e with
  | OK (Normal _ pb) _ => is_a_solution pb sigma
  | OK (Not_appliable _ pb) _ => is_a_solution pb sigma
  | OK (No_solution _) _ => False
  end.

Lemma decompose_is_sound :
  forall e sigma, 
    match decompose e with
    | Normal _ _ => False
    | Not_appliable _ pb' => is_a_solution pb' sigma -> is_a_solution_e e sigma
    | No_solution _ => True
    end.
Proof.
intro e; pattern e; apply (well_founded_ind wf_lt_exc_pb_ok); clear e.
intros [[pb | pb | ] Inv_pb] IH theta; 
rewrite decompose_unfold; unfold F_decompose; trivial.
assert (H := IH _ (decomposition_step_decreases_e _ Inv_pb) theta).
destruct pb as [sigma l].
destruct (decompose
    (decomposition_step_e (OK (Normal unification_problem (mk_pb sigma l)) Inv_pb))).
contradiction.
intros sigma_is_sol; assert (H' := H sigma_is_sol); clear H; simpl in H'; simpl.
assert (H'' := decomposition_step_is_sound l sigma theta).
destruct (decomposition_step (mk_pb sigma l)); simpl.
apply H''; trivial.
apply H''; trivial.
contradiction.
trivial.
Qed.

Lemma decompose_is_complete :
  forall e sigma, is_a_solution_e e sigma ->
    match decompose e with
    | Normal _ _ => False
    | Not_appliable _ pb' => is_a_solution pb' sigma  
    | No_solution _ => False
    end.
Proof.
intro e; pattern e; apply (well_founded_ind wf_lt_exc_pb_ok); clear e.
intros [[pb | pb | ] Inv_pb] IH theta theta_is_sol;
rewrite decompose_unfold; unfold F_decompose; trivial.
assert (H := IH _ (decomposition_step_decreases_e _ Inv_pb) theta).
destruct pb as [sigma l].
destruct (decompose
    (decomposition_step_e (OK (Normal unification_problem (mk_pb sigma l)) Inv_pb)));
apply H; simpl; simpl in theta_is_sol;
apply decomposition_step_is_complete; trivial.
Qed.

Lemma inv_solved_part_init :
  forall t1 t2, Inv_solved_part (mk_pb nil ((t1, t2) :: nil)).
Proof.
intros t1 t2; unfold Inv_solved_part; simpl; trivial.
Defined.

Lemma rep_var_is_complete :
  forall x sigma, 
  let sigma' := (x, apply_subst sigma (Var x)) :: 
                (map (fun xt => (fst xt, apply_subst ((x, apply_subst sigma (Var x)) :: nil) (snd xt))) sigma) in
    forall tau, is_a_solution (mk_pb sigma nil) tau <-> is_a_solution (mk_pb sigma' nil) tau.
Proof.
intros x sigma sigma'; subst sigma'; induction sigma as [ | [y y_val] sigma]; intros tau; unfold is_a_solution.
simpl; split.
intros; split.
intros; contradiction.
simpl; intros v.
generalize (X.eq_bool_ok v x); case (X.eq_bool v x); [intro v_eq_x; subst v; reflexivity | trivial].
intros _; split.
intros; contradiction.
trivial.

split.
intros [_ Hsol]; split.
intros; contradiction.
assert (Hsol_x := Hsol x); simpl in Hsol_x.
intro v; assert (Hsol_v := Hsol v); simpl in Hsol_v.
assert (F := find_map X.eq_bool (apply_subst ((x, (apply_subst ((y,y_val) :: sigma) (Var x))) :: nil)) v sigma).
simpl; simpl in F; revert F Hsol_x.
generalize (X.eq_bool_ok x y); case (X.eq_bool x y); [intro x_eq_y; subst y | intro x_diff_y].
(* 1/3 x = y *)
revert Hsol_v; generalize (X.eq_bool_ok v x); case (X.eq_bool v x); [intro v_eq_x; subst v; trivial | intro v_diff_x].
destruct (find X.eq_bool v sigma) as [v_val | ]; intros Hsol_v F Hsol_x; rewrite F; trivial.
rewrite Hsol_v; rewrite <- subst_comp_is_subst_comp.
rewrite <- subst_eq_vars; intros z z_in_v_val.
rewrite subst_comp_is_subst_comp; simpl.
generalize (X.eq_bool_ok z x); case (X.eq_bool z x); [intro z_eq_x; subst z | intros _]; trivial.
(* 1/2 x <> y *)
generalize (X.eq_bool_ok v x); case (X.eq_bool v x); [intro v_eq_x; subst v; trivial | intro v_diff_x].
revert Hsol_v; 
generalize (X.eq_bool_ok x y); case (X.eq_bool x y); [intro x_eq_y; absurd (x = y); trivial | intros _].
case (find X.eq_bool x sigma); trivial.
revert Hsol_v;
generalize (X.eq_bool_ok v y); case (X.eq_bool v y); [intro v_eq_y; subst v | intro v_diff_y];
intros Hsol_v F Hsol_x.
rewrite Hsol_v; rewrite <- subst_comp_is_subst_comp.
rewrite <- subst_eq_vars; intros v v_in_y_val.
rewrite subst_comp_is_subst_comp; simpl.
generalize (X.eq_bool_ok v x); case (X.eq_bool v x); [intro v_eq_x; subst v | intros _; trivial].
destruct (find X.eq_bool x sigma) as [x_val | ]; trivial.
destruct (find X.eq_bool v sigma) as [v_val | ]; rewrite F; trivial.
rewrite Hsol_v; rewrite <- subst_comp_is_subst_comp.
rewrite <- subst_eq_vars; intros z z_in_y_val.
rewrite subst_comp_is_subst_comp; simpl.
generalize (X.eq_bool_ok z x); case (X.eq_bool z x); [intro z_eq_x; subst z | intros _]; trivial.
destruct (find X.eq_bool x sigma) as [x_val | ]; trivial.

simpl; intros [_ Hsol]; split.
intros; contradiction.
intro v; 
generalize (Hsol x) (Hsol v); clear Hsol.
generalize (find_map X.eq_bool (apply_subst ((x, (apply_subst ((y,y_val) :: sigma) (Var x))) :: nil)) v sigma).
simpl; generalize (X.eq_bool_ok x x); case (X.eq_bool x x); [intros _ | intro x_diff_x; apply False_rect; apply x_diff_x; reflexivity].
generalize (X.eq_bool_ok x y); case (X.eq_bool x y); [intro x_eq_y; subst y | intros x_diff_y].
(* 1/2 x = y *)
generalize (X.eq_bool_ok v x); case (X.eq_bool v x); [intro v_eq_x; subst v; trivial | intro v_diff_x].
case_eq (find X.eq_bool v sigma); [intros v_val v_sigma | intro v_sigma]; intros Hsol_v Hsol_x F; trivial.
rewrite Hsol_v in F; rewrite F.
rewrite <- subst_comp_is_subst_comp.
rewrite <- subst_eq_vars.
intros z z_in_v_val.
rewrite subst_comp_is_subst_comp; simpl.
generalize (X.eq_bool_ok z x); case (X.eq_bool z x); [intro z_eq_x; subst z | intros _]; trivial.
rewrite Hsol_x; trivial.

(* 1/1 x <> y *)
generalize (X.eq_bool_ok v y); case (X.eq_bool v y); [intro v_eq_y; subst v | intro v_diff_y].
generalize (X.eq_bool_ok y x); case (X.eq_bool y x); [intro y_eq_x; absurd (x = y); subst; trivial | intro y_diff_x].
intros F Hsol_x Hsol_v.
rewrite Hsol_v; rewrite <- subst_comp_is_subst_comp.
rewrite <- subst_eq_vars.
intros z z_in_y_val.
rewrite subst_comp_is_subst_comp; simpl.
generalize (X.eq_bool_ok z x); case (X.eq_bool z x); [intro z_eq_x; subst z | intros _]; trivial.
rewrite Hsol_x; trivial.
generalize (X.eq_bool_ok v x); case (X.eq_bool v x); [intro v_eq_x; subst v | intro v_diff_x];
intros F Hsol_x Hsol_v.
rewrite Hsol_v; destruct (find X.eq_bool x sigma) as [x_val | ]; trivial.
destruct (find X.eq_bool v sigma) as [v_val | ]; rewrite F in Hsol_v.
rewrite Hsol_v.
rewrite <- subst_comp_is_subst_comp.
rewrite <- subst_eq_vars.
intros z z_in_v_val.
rewrite subst_comp_is_subst_comp; simpl.
generalize (X.eq_bool_ok z x); case (X.eq_bool z x); [intro z_eq_x; subst z | intros _]; trivial.
rewrite Hsol_x; trivial.
trivial.
Qed.

Fixpoint is_a_cycle sigma src current c : bool :=
match c with
| nil => 
    match find X.eq_bool current sigma with
    	| None => false
    	| Some (Var x) => false
        | Some current_val => var_in_term src current_val
    end
| next :: c' => 
    match find X.eq_bool current sigma with
    | None => false
    | Some (Var x) => false
   | Some current_val =>
	if var_in_term next current_val
        then is_a_cycle sigma src next c'
        else false
   end
end.

Lemma is_a_cycle_all_var_inst :
  forall c sigma src current, is_a_cycle sigma src current c = true ->
  forall x, In x (current :: c) -> 
  match find X.eq_bool x sigma with
  | Some (Term _ _) => True
  | _ => False
  end.
Proof.
simpl In; intros c sigma src current Hcycle x [x_eq_current | x_in_c].
subst x; destruct c; simpl in Hcycle.
destruct (find X.eq_bool current sigma) as [[ | ] | ]; trivial; discriminate.
destruct (find X.eq_bool current sigma) as [[ | ] | ]; trivial; discriminate.
revert src current Hcycle; induction c as [ | next c]; intros src current Hcycle.
contradiction.
simpl in Hcycle.
destruct (find X.eq_bool current sigma) as [[ v | f l] | ]; try discriminate.
destruct (var_in_term next (Term f l)); [idtac | discriminate].
simpl in x_in_c; destruct x_in_c as [x_eq_next | x_in_c].
subst x; destruct c; simpl in Hcycle.
destruct (find X.eq_bool next sigma) as [[v | g k] | ]; trivial; discriminate.
destruct (find X.eq_bool next sigma) as [[v | g k] | ]; trivial; discriminate.
apply (IHc x_in_c src next Hcycle).
Qed.

Lemma is_a_cycle_discard :
   forall c x x_val sigma src current,
  ~In x (current :: c) ->
  is_a_cycle sigma src current c = 
  is_a_cycle ((x,x_val) :: sigma) src current c.
Proof.
intro c; induction c as [ | next c]; intros x x_val sigma src current W; simpl.
generalize (X.eq_bool_ok current x); case (X.eq_bool current x); [intro current_eq_x | intros _; trivial].
apply False_rect; apply W; left; assumption.
rewrite (IHc x x_val).
generalize (X.eq_bool_ok current x); case (X.eq_bool current x); [intro current_eq_x | intros _; trivial].
apply False_rect; apply W; left; assumption.
intro x_in_next_c; apply W; right; trivial.
Qed.

Lemma oc_applies :
  forall c src sigma, 
  VSet.without_red (src :: c) ->
  is_a_cycle sigma src src c = true -> 
  forall tau, is_a_solution (mk_pb sigma nil) tau -> False.
Proof.
intro c; induction c as [ | next c].

(* 1/2 c = nil *)
intros src sigma W Hcycle tau [_ Hsol]; simpl in Hcycle; simpl in Hsol.
generalize (Hsol src); revert Hcycle.
case (find X.eq_bool src sigma); [intros [x | f l] | intro src_sol]; [idtac | idtac | discriminate].
intro; discriminate.
rewrite var_in_term_is_sound; intro src_in_l. 
case (var_in_subterm2 _ _ (in_impl_mem (@eq _) (fun a => eq_refl a) _ _ src_in_l)); intros [ | i p] Hsubterm.
inversion Hsubterm.
assert (Hsubterm' := subterm_at_pos_apply_subst_apply_subst_subterm_at_pos (Term f l) (i :: p) tau).
rewrite Hsubterm in Hsubterm'.
assert (Hsize := size_subterm_at_pos (apply_subst tau (Term f l)) i p).
rewrite Hsubterm' in Hsize.
intros src_sol; simpl apply_subst at 1 in Hsize; rewrite src_sol in Hsize.
apply (Nat.lt_irrefl _ Hsize).

(* 1/1 c = next :: c *)
intros src sigma W Hcycle tau.
rewrite (rep_var_is_complete src sigma tau).
apply (IHc next).
apply (VSet.without_red_remove src nil (next :: c) W).
rewrite <- is_a_cycle_discard.
clear IHc tau; revert src next W Hcycle. 
assert (H : forall x y src next : DecVar.A,
VSet.without_red (x :: next :: c) ->
var_in_term y (apply_subst sigma (Var x)) = true ->
match find X.eq_bool x sigma with
| Some (Var _) => False
| Some (Term _ _) => True
| None => False
end ->
is_a_cycle sigma x src (next :: c) = true ->
is_a_cycle
  (map
     (fun xt : variable * term =>
      (fst xt,
      apply_subst ((x, apply_subst sigma (Var x)) :: nil) (snd xt)))
     sigma) y next c = true).
induction c as [ | next' c]; intros x y src next W y_in_x_sigma Hx Hcycle.
simpl in Hcycle.
case_eq (find X.eq_bool src sigma); [intros [v | f l] | idtac]; 
intro src_sigma; rewrite src_sigma in Hcycle; [discriminate | idtac | discriminate].
case_eq (var_in_term next (Term f l)); [intro next_in_l | intro next_not_in_l].
rewrite next_in_l in Hcycle.
simpl.
assert (F := find_map X.eq_bool (apply_subst ((x, apply_subst sigma (Var x)) :: nil)) next sigma).
case_eq (find X.eq_bool next sigma); [intros [v | g k] | idtac];
intro next_sigma; rewrite next_sigma in Hcycle; [discriminate | idtac | discriminate].
rewrite next_sigma in F.
unfold DecVar.A in *; simpl apply_subst at 1 in F; rewrite F; clear F.
simpl apply_subst at 1; cbv iota beta.
rewrite var_in_term_is_sound in Hcycle.
case (var_in_subterm2 _ _ (in_impl_mem (@eq _) (fun a => eq_refl a) _ _ Hcycle)); intros [ | i p] Hsubterm.
inversion Hsubterm.
assert (Hsubterm' := subterm_at_pos_apply_subst_apply_subst_subterm_at_pos (Term g k) (i :: p)
                                       ((x, apply_subst sigma (Var x)) :: nil)).
rewrite Hsubterm in Hsubterm'.
rewrite var_in_term_is_sound.
refine (var_in_subterm y _ (i :: p) Hsubterm' _).
simpl; generalize (X.eq_bool_ok x x); case (X.eq_bool x x); [intros _ | intro x_diff_x; apply False_rect; apply x_diff_x; reflexivity].
rewrite <- var_in_term_is_sound; trivial.
rewrite next_not_in_l in Hcycle; discriminate.
assert (Hsrc := is_a_cycle_all_var_inst _ _ _ _ Hcycle src).
case_eq (find X.eq_bool src sigma); [intros [v | f l] | idtac];
intro src_sigma; rewrite src_sigma in Hsrc.
apply False_rect; apply Hsrc; left; reflexivity.
clear Hsrc.
assert (Hnext := is_a_cycle_all_var_inst _ _ _ _ Hcycle next).
case_eq (find X.eq_bool next sigma); [intros [v | g k] | idtac]; 
intro next_sigma; rewrite next_sigma in Hnext.
apply False_rect; apply Hnext; right; left; reflexivity.
clear Hnext.
revert Hcycle; pattern (next' :: c); simpl; intro Hcycle.
rewrite src_sigma in Hcycle.
rewrite next_sigma in Hcycle.
case_eq (var_in_term next (Term f l)); [intro next_in_l | intro next_not_in_l].
rewrite next_in_l in Hcycle.
case_eq (var_in_term next' (Term g k)); [intro next'_in_k | intro next'_not_in_k].
rewrite next'_in_k in Hcycle.
assert (F := find_map X.eq_bool (apply_subst ((x, apply_subst sigma (Var x)) :: nil)) next sigma).
rewrite next_sigma in F.
simpl apply_subst at 1 in F; rewrite F; clear F.
simpl apply_subst at 1; cbv iota beta.
assert (H : var_in_term next'
      (apply_subst ((x, apply_subst sigma (Var x)) :: nil) (Term g k)) = true).
rewrite var_in_term_is_sound in next'_in_k.
case (var_in_subterm2 _ _ (in_impl_mem (@eq _) (fun a => eq_refl _) _ _ next'_in_k)); intros [ | i p] Hsubterm.
inversion Hsubterm.
assert (Hsubterm' := subterm_at_pos_apply_subst_apply_subst_subterm_at_pos (Term g k) (i :: p)
                                       ((x, apply_subst sigma (Var x)) :: nil)).
rewrite Hsubterm in Hsubterm'.
rewrite var_in_term_is_sound.
refine (var_in_subterm next' _ (i :: p) Hsubterm' _).
simpl; generalize (X.eq_bool_ok next' x); case (X.eq_bool next' x); [intro next'_eq_x; subst next' | intros _; left; trivial].
assert (W' : VSet.without_red (x :: x :: c)).
apply (VSet.without_red_remove next (x :: nil) (x :: c) W).
simpl in W'; apply False_rect.
unfold VSet.without_red in W'; simpl in W'; revert W'; unfold DecVar.eq_bool.
generalize (X.eq_bool_ok x x); case (X.eq_bool x x); [intros _; discriminate | intro x_diff_x; apply False_rect; apply x_diff_x; reflexivity].
rewrite H.
refine (IHc x y next _ _ y_in_x_sigma Hx _).
apply (VSet.without_red_remove next (x :: nil) (next' :: c) W).
simpl; rewrite next_sigma.
rewrite next'_in_k; trivial.
rewrite next'_not_in_k in Hcycle; discriminate.
rewrite next_not_in_l in Hcycle; discriminate.
apply False_rect; apply Hnext; right; left; reflexivity.
apply False_rect; apply Hsrc; left; reflexivity.
intros src next W Hcycle; apply H with src; trivial.
simpl in Hcycle; simpl.
destruct (find X.eq_bool src sigma) as [[v | f l] | ].
discriminate.
destruct (var_in_term next (Term f l)); trivial; discriminate.
discriminate.
apply (is_a_cycle_all_var_inst _ _ _ _ Hcycle); left; reflexivity.

unfold VSet.without_red in W; simpl in W; revert W; unfold DecVar.eq_bool.
generalize (X.eq_bool_ok src next); case (X.eq_bool src next); [intro src_eq_next | intro src_diff_next].
intros; discriminate.
simpl; unfold DecVar.A.
generalize (mem_bool_ok _ _ X.eq_bool_ok src c); case (mem_bool X.eq_bool src c); [intro src_in_c | intro src_not_in_c].
intros; discriminate.
generalize (mem_bool_ok _ _ X.eq_bool_ok next c); case (mem_bool X.eq_bool next c); [intro next_in_c | intro next_not_in_c].
intros; discriminate.
intros _ [src_eq_next | src_in_c].
apply src_diff_next; subst; reflexivity.
apply src_not_in_c; apply in_impl_mem; trivial.
Qed.

Lemma idem_sol :
  forall sigma, 
   (forall x y, VSet.mem x (domain_of_subst sigma) -> VSet.mem y (domain_of_subst sigma) ->
  var_in_term x (apply_subst sigma (Var y)) = false) -> 
  is_a_solution (mk_pb sigma nil) sigma.
Proof.
intros sigma Idem; split.
intros; contradiction.
simpl; intros x.
case_eq (find X.eq_bool x sigma); [intro x_val | idtac]; intro x_sigma; trivial.
symmetry; apply apply_subst_outside_dom.
intro y; split; [idtac | intro; contradiction].
intro H.
assert (H1 := VSet.inter_1 _ _ _ H).
assert (H2 := VSet.inter_2 _ _ _ H).
clear H.
assert (H3 : VSet.mem x (domain_of_subst sigma)).
rewrite var_in_domain_of_subst; rewrite x_sigma; discriminate.
assert (Hi := Idem y x H1 H3).
assert (H2' : In y (var_list x_val)).
revert H2; pattern x_val; apply term_rec3; [intro v | intros f l].
unfold VSet.mem, VSet.singleton, DecVar.eq_A; simpl.
intros [H | H]; [subst; left; reflexivity | contradiction].
induction l as [ | t l].
unfold VSet.mem, VSet.singleton, DecVar.eq_A; simpl.
intros; contradiction.
intros IH y_in_tl.
unfold set_of_variables in y_in_tl.
destruct (VSet.union_12 _ _ _ y_in_tl) as [y_in_t | y_in_l].
simpl; apply in_or_app; left.
apply (IH t (or_introl _ (eq_refl _)) y_in_t).
simpl; apply in_or_app; right.
refine (IHl _ y_in_l).
intros; apply IH.
right; trivial.
trivial.
rewrite <- var_in_term_is_sound in H2'; simpl in Hi; rewrite x_sigma in Hi;
rewrite Hi in H2'; discriminate.
Qed.

Fixpoint is_a_total_oc_ordering sigma c {struct c} :=
match c with
| nil => true
| x :: c' => 
    let vx := Var x in
    let v_val := apply_subst sigma vx in
    if list_exists (fun z => var_in_term z v_val) c
    then false
    else is_a_total_oc_ordering sigma c'
end.
   
Fixpoint acc_inst c sigma {struct c} :=
match c with
| nil => sigma
| x :: c' => 
         let xxval := (x, apply_subst sigma (Var x)) in 
         let xxval_subst := xxval :: nil in
         (acc_inst c' (map_subst (fun _ t => (apply_subst xxval_subst t)) sigma))
end.

Lemma acc_inst_dom :
  forall c sigma, domain_of_subst sigma = domain_of_subst (acc_inst c sigma).
Proof.
intro c; induction c as [ | x l]; simpl; intros sigma; trivial.
rewrite <- IHl.
rewrite domain_of_subst_map_subst; reflexivity.
Qed.

Lemma elim_var_in_subst :
forall sigma v v_val z, VSet.mem z (domain_of_subst sigma) ->
var_in_term v v_val = false ->
var_in_term v (apply_subst (map_subst (fun _ t => apply_subst ((v,v_val) :: nil) t) sigma) (Var z)) = false.
Proof.
intros sigma v v_val y y_in_dom v_in_v_val.
simpl; rewrite var_in_domain_of_subst in y_in_dom.
assert (F := find_map_subst y v v_val sigma).
case_eq (find X.eq_bool y sigma); [intro y_val | idtac]; intro y_sigma; rewrite y_sigma in F; rewrite F.
assert (var_in_term v (apply_subst ((v, v_val) :: nil) y_val) <> true).
(* 1/3 a new assertion, equivalent to the goal, but easier to handle *)
intro H1; rewrite var_in_term_is_sound in H1.
destruct (var_in_subterm2 _ _ (in_impl_mem (@eq _) (fun a => eq_refl a) _ _ H1)) as [p H'''].
assert (H4 := subterm_in_instantiated_term _ _ _ H''').
case_eq (subterm_at_pos y_val p); [intros [w | f l] | idtac]; intro Hsub; rewrite Hsub in H4.
(* 1/6 y_val at position p is a variable w *)
simpl in H4; revert H4; generalize (X.eq_bool_ok w v); case (X.eq_bool w v); [intro w_eq_v | intro w_diff_v].
intro H4; subst w v_val; assert (v_in_v_val' : var_in_term v (Var v) = true).
simpl; generalize (X.eq_bool_ok v v); case (X.eq_bool v v);  [intros _; trivial | intro v_diff_v; apply False_rect; apply v_diff_v; reflexivity].
rewrite v_in_v_val in v_in_v_val'; discriminate.
intro H4; apply w_diff_v; injection H4; clear H4; intro H4; subst w; trivial.
(* 1/4 y_val at position p is a composite term *)
discriminate.
(* 1/3 y_val at position p is not defined *)
destruct H4 as [w [q [q' [H4 [H5 [H6 H7]]]]]].
simpl in H7; revert H7; generalize (X.eq_bool_ok w v); case (X.eq_bool w v); [intro w_eq_v | intro w_diff_v].
intro H7; subst w; assert (x_in_v_val := var_in_subterm v _ _ H7 (or_introl _ (eq_refl _))).
rewrite <- var_in_term_is_sound in x_in_v_val.
rewrite v_in_v_val in x_in_v_val; discriminate.
intro H7; destruct q'; [injection H7; clear H7; intro H7; subst w | discriminate].
apply w_diff_v; trivial.
(* 1/2 discharge of the "equivalent goal" *)
destruct (var_in_term v (apply_subst ((v, v_val) :: nil) y_val)); [absurd (true = true) | idtac]; trivial.
rewrite y_sigma in y_in_dom; absurd (@None term = None); trivial.
Qed.

Lemma no_var_in_term_inv :
forall x x_val y_val z, var_in_term z x_val = false -> var_in_term z y_val = false ->
var_in_term z (apply_subst ((x,x_val) :: nil) y_val) = false.
Proof.
intros x x_val w_val' z z_not_in_x_val z_not_in_w_val';
assert (var_in_term z (apply_subst ((x, x_val) :: nil) w_val') <> true).
(* 1/2 a new assertion, equivalent to the goal, but easier to handle *)
intro H1; rewrite var_in_term_is_sound in H1.
destruct (var_in_subterm2 _ _ (in_impl_mem (@eq _) (fun a => eq_refl _) _ _ H1)) as [p H'''].
assert (H4 := subterm_in_instantiated_term _ _ _ H''').
case_eq (subterm_at_pos w_val' p); [intros [u | f l] | idtac]; intro Hsub; rewrite Hsub in H4.
(* 1/4 w_val' at position p is a variable u *)
simpl in H4; revert H4; generalize (X.eq_bool_ok u x); case (X.eq_bool u x); [intro u_eq_x | intro u_diff_x].
intro H4; subst u x_val; assert (z_in_x_val' : var_in_term z (Var z) = true).
simpl; generalize (X.eq_bool_ok z z); case (X.eq_bool z z); [intros _; trivial | intro z_diff_z; apply False_rect; apply z_diff_z; trivial].
rewrite z_in_x_val' in z_not_in_x_val; discriminate.
intro H4; injection H4; clear H4; intro H4; subst u.
assert (z_in_w_val' := var_in_subterm z _ _ Hsub (or_introl _ (eq_refl _))).
rewrite <- var_in_term_is_sound in z_in_w_val'.
rewrite z_not_in_w_val' in z_in_w_val'; discriminate.
(* 1/3 w_val' at position p is a composite term *)
discriminate.
(* 1/2 w_val' at position p is not defined *)
destruct H4 as [u [q [q' [H4 [H5 [H6 H7]]]]]].
simpl in H7; revert H7; generalize (X.eq_bool_ok u x); case (X.eq_bool u x); [intro u_eq_x | intro u_diff_x].
intro H7; subst u; assert (z_in_x_val := var_in_subterm z _ _ H7 (or_introl _ (eq_refl _))).
rewrite <- var_in_term_is_sound in z_in_x_val.
rewrite z_not_in_x_val in z_in_x_val; discriminate.
intro H7; destruct q'; [injection H7; clear H7; intro H7; subst u | discriminate].
rewrite <- app_nil_end in H4; subst q.
rewrite Hsub in H6; discriminate.
(* 1/1 discharge of the "equivalent goal" *)
destruct (var_in_term z (apply_subst ((x, x_val) :: nil) w_val')); [absurd (true = true) | idtac]; trivial.
Qed.

Lemma no_var_in_subst_inv :
  forall z sigma, 
  (forall v v_val, find X.eq_bool v sigma = Some v_val -> var_in_term z v_val = false) ->
  forall c v v_val, VSet.mem v (domain_of_subst sigma) -> 
  find X.eq_bool v (acc_inst c sigma) = Some v_val -> var_in_term z v_val = false.
Proof.
intros z sigma H c; revert z sigma H; 
induction c as [ | x c]; intros z sigma H v v_val v_in_dom F.
simpl in F; apply (H v _ F).
simpl in F; refine (IHc _ _ _ _ _ _ F); clear F.
intros w w_val F.
assert (F' := find_map_subst w x (apply_subst sigma (Var x)) sigma).
simpl in F'; case_eq (find X.eq_bool w sigma); [intro w_val' | idtac]; intro w_sigma;
rewrite w_sigma in F'.
rewrite F in F'; injection F'; clear F F'; intro F'; subst w_val.
assert (z_not_in_w_val' := H _ _ w_sigma).
case_eq (find X.eq_bool x sigma); [intro x_val | idtac]; intro x_sigma.
assert (z_not_in_x_val := H _ _ x_sigma).
apply no_var_in_term_inv; trivial.
replace (apply_subst ((x, Var x) :: nil) w_val') with (apply_subst nil w_val').
rewrite empty_subst_is_id; trivial.
rewrite <- subst_eq_vars.
intros y _; simpl.
generalize (X.eq_bool_ok y x); case (X.eq_bool y x); [intro y_eq_x; subst y | intro y_diff_x]; trivial.
rewrite F in F'; discriminate.
rewrite domain_of_subst_map_subst; trivial.
Qed.

Lemma total_ordering_eq_subst :
  forall c sigma tau, (forall v, find X.eq_bool v sigma = find X.eq_bool v tau) ->
  is_a_total_oc_ordering sigma c = is_a_total_oc_ordering tau c.
Proof.
intro c; induction c as [ | v c]; intros sigma tau H; simpl.
trivial.
rewrite H; rewrite (IHc sigma tau); trivial.
Qed.

Lemma acc_inst_eq_subst :
  forall c sigma tau, (forall v, find X.eq_bool v sigma = find X.eq_bool v tau) ->
  forall v, find X.eq_bool v (acc_inst c sigma) = find X.eq_bool v (acc_inst c tau).
Proof.
intro c; induction c as [ | v c]; intros sigma tau H; simpl.
trivial.
intro x; refine (IHc _ _ _ _); clear x.
intros x.
assert (F := find_map_subst x v (apply_subst sigma (Var v)) sigma).
assert (F' := find_map_subst x v (apply_subst tau (Var v)) tau).
case_eq (find X.eq_bool x sigma); [intro x_val | idtac]; intro x_sigma; 
rewrite x_sigma in F; simpl in F; rewrite F;
rewrite H in x_sigma; rewrite x_sigma in F'; simpl in F'; rewrite F'; trivial.
rewrite H; trivial.
Qed.

Lemma tail_total_ordering :
forall sigma v v_val c,
list_exists (fun z : variable => var_in_term z v_val) c = false ->
is_a_total_oc_ordering sigma c = true ->
is_a_total_oc_ordering
  (map_subst
     (fun (_ : variable) (t : term) => apply_subst ((v, v_val) :: nil) t)
     sigma) c = true.
Proof.
intros sigma v v_val l; induction l as [ | z l]; simpl; intros H' Hoc; trivial.
assert (F := find_map_subst z v v_val sigma).
case_eq (find X.eq_bool z sigma); [intro z_val | idtac]; intro z_sigma;
rewrite z_sigma in F; rewrite z_sigma in Hoc; rewrite F.
case_eq (var_in_term z v_val); intro z_in_v_val; rewrite z_in_v_val in H'.
discriminate.
case_eq (var_in_term z z_val); intro z_in_z_val; rewrite z_in_z_val in Hoc.
discriminate.
simpl in H'; simpl in Hoc.
rewrite (no_var_in_term_inv v v_val z_val z z_in_v_val z_in_z_val).
simpl.
case_eq (list_exists (fun z : variable => var_in_term z z_val) l); 
intro Hoc'; rewrite Hoc' in Hoc; [discriminate | simpl in Hoc].
assert (Hoc'' :=  list_exists_is_complete_false _ _ Hoc').
case_eq (list_exists
      (fun z0 : variable =>
       var_in_term z0 (apply_subst ((v, v_val) :: nil) z_val)) l); intro Goc.
rewrite list_exists_is_sound in Goc.
destruct Goc as [w [w_in_l Goc']].
rewrite <- Goc'; symmetry.
apply no_var_in_term_inv.
apply (list_exists_is_complete_false _ _ H' w w_in_l).
apply (Hoc'' w w_in_l).
apply IHl; trivial.
revert Hoc; simpl; generalize (X.eq_bool_ok z z); case (X.eq_bool z z); [intros _; trivial | intro z_diff_z; apply False_rect; apply z_diff_z; trivial].
Qed.

Lemma total_acc_inst_head :
  forall c v sigma, VSet.without_red (v :: c) ->
  is_a_total_oc_ordering sigma (v :: c) = true ->
  apply_subst (acc_inst (v :: c) sigma) (Var v) = apply_subst sigma (Var v).
Proof.
intro c; induction c as [ | v' c]; intros v sigma W Hoc.
(* 1/2 basis case *)
assert (F := find_map_subst v v (apply_subst sigma (Var v)) sigma); simpl in F.
simpl; simpl in Hoc; case_eq (find X.eq_bool v sigma); [intro v_val | idtac]; 
intro v_sigma; rewrite v_sigma in Hoc; rewrite v_sigma in F; rewrite F; [idtac | reflexivity].
rewrite <- (empty_subst_is_id v_val) at 3.
rewrite <- subst_eq_vars.
intros y y_in_v_val; simpl.
generalize (X.eq_bool_ok y v); case (X.eq_bool y v); [intro y_eq_v | intro y_diff_v; reflexivity].
subst y; rewrite <- var_in_term_is_sound in y_in_v_val; rewrite y_in_v_val in Hoc; discriminate.
(* 1/1 induction step *)
simpl; simpl in Hoc; case_eq (find X.eq_bool v sigma); [intro v_val | idtac]; 
intro v_sigma; rewrite v_sigma in Hoc.

case_eq (var_in_term v v_val); intro v_in_v_val; rewrite v_in_v_val in Hoc; [discriminate | simpl in Hoc].
assert (Idem : apply_subst ((v,v_val) :: nil) v_val = v_val).
rewrite <- (empty_subst_is_id v_val) at 3.
rewrite <- subst_eq_vars.
intros y y_in_v_val; simpl.
generalize (X.eq_bool_ok y v); case (X.eq_bool y v); [intro y_eq_v | intro y_diff_v; reflexivity].
subst y; rewrite <- var_in_term_is_sound in y_in_v_val; rewrite y_in_v_val in v_in_v_val; discriminate.
assert (F' := find_map_subst v' v (apply_subst sigma (Var v)) sigma); simpl in F'.
rewrite v_sigma in F'.
case_eq (find X.eq_bool v' sigma); [intro v'_val | idtac]; intro v'_sigma;
rewrite v'_sigma in F'; rewrite F'.
assert (Switch : forall y, 
find X.eq_bool y
(map_subst
          (fun (_ : variable) (t : term) =>
           apply_subst ((v', apply_subst ((v, v_val) :: nil) v'_val) :: nil)
             t)
          (map_subst
             (fun (_ : variable) (t : term) =>
              apply_subst ((v, v_val) :: nil) t) sigma)) =
find X.eq_bool y
(map_subst
             (fun (_ : variable) (t : term) =>
              apply_subst ((v, v_val) :: nil) t)
(map_subst
          (fun (_ : variable) (t : term) =>
           apply_subst ((v', apply_subst ((v, v_val) :: nil) v'_val) :: nil)
             t) sigma))).
intro y.
assert (Fy := find_map_subst y v v_val sigma).
assert (Fy' := find_map_subst y v' (apply_subst ((v, v_val) :: nil) v'_val) 
    (map_subst
        (fun (_ : variable) (t : term) => apply_subst ((v, v_val) :: nil) t)
        sigma)).
assert (Fy'' := find_map_subst y v' (apply_subst ((v, v_val) :: nil) v'_val) sigma).
assert (Fy''' := find_map_subst y v v_val (map_subst
        (fun (_ : variable) (t : term) =>
         apply_subst ((v', apply_subst ((v, v_val) :: nil) v'_val) :: nil) t)
        sigma)).
case_eq (find X.eq_bool y sigma); [intro y_val | idtac]; intro y_sigma;
unfold DecVar.A in *; 
rewrite y_sigma in Fy; rewrite Fy in Fy'; rewrite Fy';
rewrite y_sigma in Fy''; rewrite Fy'' in Fy'''; rewrite Fy'''; [apply f_equal | reflexivity].
do 2 rewrite <- subst_comp_is_subst_comp.
rewrite <- subst_eq_vars.
intros z z_in_y_val; simpl.
generalize (X.eq_bool_ok z v); case (X.eq_bool z v); [intro z_eq_v; subst z | intro z_diff_v].
generalize (X.eq_bool_ok v v'); case (X.eq_bool v v'); [intro v_eq_v'; subst v' | intro v_diff_v'].
apply False_rect; unfold VSet.without_red in W; simpl in W; revert W.
unfold DecVar.eq_bool; generalize (X.eq_bool_ok v v); case (X.eq_bool v v); 
[intros _; discriminate | intros v_diff_v _; apply v_diff_v; reflexivity].
rewrite <- (empty_subst_is_id v_val) at 3.
rewrite <- subst_eq_vars.
intros u u_in_v_val; simpl.
generalize (X.eq_bool_ok u v'); case (X.eq_bool u v'); [intro u_eq_v'; subst v' | intros _; reflexivity].
rewrite <- var_in_term_is_sound in u_in_v_val; rewrite u_in_v_val in Hoc; 
destruct (var_in_term v v_val); simpl in Hoc; discriminate.
simpl.
generalize (X.eq_bool_ok v' v); case (X.eq_bool v' v); [intro v'_eq_v; absurd (v' = v); trivial | intros _].
revert W; unfold VSet.without_red; simpl; unfold DecVar.eq_bool.
generalize (X.eq_bool_ok v v'); case (X.eq_bool v v'); [intro v_eq_v'; intros; discriminate | intro v_diff_v'].
subst v'; intros _; assumption.
destruct (X.eq_bool z v'); [idtac | reflexivity].
rewrite <- subst_comp_is_subst_comp.
rewrite <- subst_eq_vars.
intros u u_in_val; simpl.
generalize (X.eq_bool_ok u v); case (X.eq_bool u v); [intro u_eq_v; subst v | intros _; reflexivity].
rewrite Idem; reflexivity.
rewrite (acc_inst_eq_subst c _ _ Switch); clear Switch.
assert (IH := IHc v (map_subst
             (fun (_ : variable) (t : term) =>
              apply_subst
                ((v', apply_subst ((v, v_val) :: nil) v'_val) :: nil) t)
             sigma) (VSet.without_red_remove v' (v :: nil) c W)).
simpl in IH.
assert (F := find_map_subst v v' (apply_subst ((v, v_val) :: nil) v'_val) sigma).
unfold DecVar.A in *; rewrite v_sigma in F; rewrite F in IH.
assert (Idem' : apply_subst ((v', apply_subst ((v, v_val) :: nil) v'_val) :: nil) v_val = v_val).
rewrite <- (empty_subst_is_id v_val) at 3.
rewrite <- subst_eq_vars.
intros u u_in_v_val; simpl.
generalize (X.eq_bool_ok u v'); case (X.eq_bool u v'); [intro u_eq_v'; subst v' | intros _; reflexivity].
rewrite <- var_in_term_is_sound in u_in_v_val; rewrite u_in_v_val in Hoc; discriminate.
rewrite Idem' in IH; rewrite IH; trivial.
clear IH; rewrite v_in_v_val; simpl.
case_eq (var_in_term v' v_val); intro v'_in_v_val; rewrite v'_in_v_val in Hoc; [discriminate | simpl in Hoc].
rewrite v'_sigma in Hoc.
case_eq (list_exists (fun z : variable => var_in_term z v_val) c); 
intro Hoc'; rewrite Hoc' in Hoc; [discriminate | simpl in Hoc].
case_eq (var_in_term v' v'_val); intro v'_in_v'_val; rewrite v'_in_v'_val in Hoc; [discriminate | simpl in Hoc].
case_eq (list_exists (fun z : variable => var_in_term z v'_val) c); 
intro Hoc''; rewrite Hoc'' in Hoc; [discriminate | simpl in Hoc].
apply tail_total_ordering; trivial.
assert (H : list_exists
  (fun z : variable => var_in_term z (apply_subst ((v, v_val) :: nil) v'_val))
  c <> true).
intro H; rewrite list_exists_is_sound in H; destruct H as [z [z_in_c z_in_val]].
rewrite no_var_in_term_inv in z_in_val.
discriminate.
apply (list_exists_is_complete_false _ _ Hoc' _ z_in_c).
apply (list_exists_is_complete_false _ _ Hoc'' _ z_in_c).
destruct (list_exists
      (fun z : variable =>
       var_in_term z (apply_subst ((v, v_val) :: nil) v'_val)) c); [absurd (true = true) | idtac]; trivial.

rewrite v'_sigma in Hoc.
destruct (var_in_term v' v_val); [discriminate | idtac].
destruct (list_exists (fun z : variable => var_in_term z v_val) c); [discriminate | idtac].
simpl in Hoc; revert Hoc.
generalize (X.eq_bool_ok v' v'); case (X.eq_bool v' v'); [intros _; intros; discriminate | intro v'_diff_v'; apply False_rect; apply v'_diff_v'; reflexivity].

simpl in Hoc; revert Hoc.
generalize (X.eq_bool_ok v v); case (X.eq_bool v v); [intros _ | intro v_diff_v]; [intros; discriminate | absurd (v = v); trivial].
Qed.

Lemma total_acc_inst_elim_var :
  forall c sigma v, 
  var_in_term v (apply_subst sigma (Var v)) = false ->
  (forall x x_val, find X.eq_bool x sigma = Some x_val -> var_in_term v x_val = false) ->
  forall t, var_in_term v (apply_subst (acc_inst c sigma) t) = false.
Proof.
intro c; induction c as [ | v c]; intros sigma x x_elim_x sigma_elim_x t; simpl.
pattern t; apply term_rec3; clear t.
case_eq (find X.eq_bool x sigma); [intro x_val | idtac]; 
intro x_sigma; simpl in x_elim_x; rewrite x_sigma in x_elim_x.
intros v; simpl; 
case_eq (find X.eq_bool v sigma); [intro v_val | idtac]; intro v_sigma.
apply (sigma_elim_x v v_val v_sigma).
simpl; generalize (X.eq_bool_ok v x); case (X.eq_bool v x); [intro v_eq_x | intros _; reflexivity].
subst v; rewrite x_sigma in v_sigma; discriminate.
apply False_rect; revert x_elim_x; simpl.
generalize (X.eq_bool_ok x x); case (X.eq_bool x x); [intros _; discriminate | intros x_diff_x _; apply x_diff_x; reflexivity].
intros f l; simpl; induction l as [ | t l]; intro IH.
trivial.
simpl.
generalize (apply_subst sigma t) (IH t (or_introl _ (eq_refl _))).
intros [w | g k] H; rewrite var_in_term_list_equation.
simpl in H; revert H; 
generalize (X.eq_bool_ok w x); case (X.eq_bool w x); [intros _ Abs; discriminate | intro w_diff_x].
generalize (X.eq_bool_ok x w); case (X.eq_bool x w); [intros x_eq_w _ | intros _ _].
absurd (w=x); subst; trivial.
simpl; apply IHl.
intros; apply IH; right; trivial.
simpl in H; rewrite H; simpl; apply IHl; intros; apply IH; right; trivial.

apply IHc.
simpl.
assert (F := find_map_subst x v (apply_subst sigma (Var v)) sigma).
case_eq (find X.eq_bool x sigma); [intro x_val | idtac]; 
intro x_sigma; simpl in x_elim_x; rewrite x_sigma in x_elim_x;
rewrite x_sigma in F; unfold DecVar.A in *; simpl in F; rewrite F; clear F.
apply no_var_in_term_inv.
case_eq (find X.eq_bool v sigma); [intro v_val | idtac]; intro v_sigma.
apply (sigma_elim_x v v_val v_sigma).
simpl; generalize (X.eq_bool_ok v x); case (X.eq_bool v x); [intro v_eq_x | intros _; reflexivity].
subst v; rewrite x_sigma in v_sigma; discriminate.
trivial.
trivial.

case_eq (find X.eq_bool x sigma); [intro x_val | idtac]; 
intro x_sigma; simpl in x_elim_x; rewrite x_sigma in x_elim_x.
intros y y_val' F.
assert (F' := find_map_subst y v (apply_subst sigma (Var v)) sigma).
case_eq (find X.eq_bool y sigma); [intro y_val | idtac]; intro y_sigma;
rewrite y_sigma in F'; simpl in F'; rewrite F in F'.
injection F'; clear F'; intro F'; subst y_val'; clear F.
apply no_var_in_term_inv.
assert (H := sigma_elim_x v).
case_eq (find X.eq_bool v sigma); [intro v_val | idtac]; intro v_sigma.
apply H; trivial.
simpl; generalize (X.eq_bool_ok v x); case (X.eq_bool v x); [intro v_eq_x | intros _; reflexivity].
subst v; rewrite x_sigma in v_sigma; discriminate.
apply (sigma_elim_x y); trivial.
discriminate.

revert x_elim_x; simpl; generalize (X.eq_bool_ok x x); case (X.eq_bool x x); 
[intros _; intros; discriminate | intros x_diff_x; apply False_rect; apply x_diff_x; reflexivity].
Qed.

Lemma set_of_var_list_of_var :
  forall v t, VSet.mem v (set_of_variables t) <-> var_in_term v t = true.
Proof.
intros v t; pattern t; apply term_rec3; clear t.
intros x; unfold VSet.mem; simpl; unfold DecVar.eq_A.
generalize (X.eq_bool_ok x v); case (X.eq_bool x v); [intro v_eq_x; subst v | intro v_diff_x].
intuition.
intuition.
intros f l IH; simpl.
induction l as [ | t l]; simpl.
unfold VSet.mem; simpl; intuition.
split; intro H.
destruct (VSet.union_12 _ _ _ H) as [H1 | H2].
rewrite (IH t (or_introl _ (eq_refl _))) in H1.
rewrite var_in_term_list_equation.
destruct t as [w | g k]; simpl in H1; simpl.
generalize (X.eq_bool_ok v w); case (X.eq_bool v w); [intros _; trivial | intro v_diff_w]. 
apply False_rect; apply v_diff_w.
generalize (X.eq_bool_ok w v); rewrite H1; intro; symmetry; assumption.
rewrite H1; trivial.
rewrite IHl in H2.
rewrite var_in_term_list_equation.
destruct t as [w | g k]; simpl.
generalize (X.eq_bool_ok v w); case (X.eq_bool v w); [intros _; trivial | intro v_diff_w]. 
rewrite H2; rewrite Bool.orb_true_r; trivial.
rewrite H2; rewrite Bool.orb_true_r; trivial.
intros u u_in_l; apply IH; right; trivial.

rewrite var_in_term_list_equation in H.
destruct t as [w | g k]; simpl in H; simpl.
revert H; generalize (X.eq_bool_ok v w); case (X.eq_bool v w); [intros v_eq_w _; subst w | intros v_diff_w H]. 
apply VSet.union_1; simpl; left; reflexivity.
apply VSet.union_2; rewrite IHl; trivial.
intros u u_in_l; apply IH; right; trivial.
case_eq (var_in_term_list v k); intro v_in_k; rewrite v_in_k in H; simpl in H.
apply VSet.union_1.
rewrite (IH _ (or_introl _ (eq_refl _))); trivial.
apply VSet.union_2.
rewrite IHl; trivial.
intros u u_in_l; apply IH; right; trivial.
Qed.

Lemma total_acc_inst_idem :
  forall c sigma, is_a_total_oc_ordering sigma c = true ->
  VSet.without_red c ->
  (forall x, In x c -> VSet.mem x (domain_of_subst sigma)) ->
  (forall x y, In x c -> In y c -> var_in_term x (apply_subst (acc_inst c sigma) (Var y)) = false).
Proof.
intro c; induction c as [ | v c]; intros sigma Hoc W H x y x_in_dom y_in_dom.
(* 1/2 basis case *)
contradiction.
(* 1/1 induction step *)
assert (v_case := total_acc_inst_head c v sigma W Hoc).
assert (v_in_dom := H v (or_introl _ (eq_refl _))); rewrite var_in_domain_of_subst in v_in_dom.
case_eq (find X.eq_bool v sigma); [intro v_val | idtac]; 
intro v_sigma; rewrite v_sigma in v_in_dom; [ clear v_in_dom | absurd (@None term = None); trivial].
simpl in Hoc; rewrite v_sigma in Hoc.
case_eq (var_in_term v v_val); intro v_in_v_val; rewrite v_in_v_val in Hoc; [discriminate | simpl in Hoc].
case_eq (list_exists (fun z : variable => var_in_term z v_val) c);  intro H'; rewrite H' in Hoc; [discriminate | simpl in Hoc].
simpl in y_in_dom; destruct y_in_dom as [y_eq_v | y_in_dom].
(* 1/2 v = y *)
subst y; unfold DecVar.A in *;  rewrite v_case.
simpl; rewrite v_sigma; simpl in x_in_dom; destruct x_in_dom as [x_eq_v | x_in_dom].
subst x; trivial.
apply (list_exists_is_complete_false _ _ H' _ x_in_dom).

(* 1/1 y in c *)
simpl in x_in_dom; destruct x_in_dom as [x_eq_v | x_in_dom].
(* 1/2 y in c, x = v *)
subst x.
apply (no_var_in_subst_inv v
(map_subst
            (fun (_ : variable) (t : term) =>
             apply_subst ((v, v_val) :: nil) t) sigma)) with c y.
intros z z_val F.
assert (H'' := elim_var_in_subst sigma v v_val z).
simpl in H''; rewrite F in H''.
apply H''; trivial.
assert (F' : find X.eq_bool z
      (map_subst
         (fun (_ : variable) (t : term) => apply_subst ((v, v_val) :: nil) t)
         sigma) <> None).
rewrite F; discriminate.
rewrite <- var_in_domain_of_subst in F'.
rewrite domain_of_subst_map_subst in F'; trivial.
rewrite domain_of_subst_map_subst; apply H; right; trivial.
assert (y_in_dom' : VSet.mem y (domain_of_subst (acc_inst (v :: c) sigma))).
rewrite <- acc_inst_dom; apply H; right; trivial.
rewrite var_in_domain_of_subst in y_in_dom'.
simpl in y_in_dom'; rewrite v_sigma in y_in_dom'; simpl; rewrite v_sigma.
destruct (find X.eq_bool y
  (acc_inst c
     (map_subst
        (fun (_ : variable) (t : term) => apply_subst ((v, v_val) :: nil) t)
        sigma))); [idtac | absurd (@None term = None)]; trivial.
(* 1/1 y in c, y <> v, x in c *)
apply IHc; trivial.
apply tail_total_ordering; trivial.
simpl; rewrite v_sigma; trivial.
apply (VSet.without_red_remove v nil c W).
intros w w_in_c; rewrite domain_of_subst_map_subst; apply H; right; trivial.
Qed.

Lemma total_acc_inst_sol :
 forall sigma c, VSet.without_red c ->
  is_a_total_oc_ordering sigma c = true ->
  VSet.LP.permut c (VSet.support (domain_of_subst sigma)) ->
  is_a_solution (mk_pb (acc_inst c sigma) nil) (acc_inst c sigma).
Proof.
intros sigma c W Hoc P.
apply idem_sol.
assert (H : forall z, In z c -> VSet.mem z (domain_of_subst sigma)).
intros z z_in_c; apply (VSet.LP.mem_permut_mem z P).
apply in_impl_mem; trivial.
reflexivity.
intros x y x_in_dom y_in_dom; apply total_acc_inst_idem; trivial.
rewrite <- acc_inst_dom in x_in_dom.
rewrite <- (VSet.LP.mem_permut_mem x P) in x_in_dom.
revert x_in_dom; generalize c; intro l; induction l as [ | u l]; simpl.
trivial.
unfold DecVar.eq_A; intros [x_eq_u | x_in_l]; [left; subst; reflexivity | right; apply IHl; trivial].
rewrite <- acc_inst_dom in y_in_dom.
rewrite <- (VSet.LP.mem_permut_mem y P) in y_in_dom.
revert y_in_dom; generalize c; intro l; induction l as [ | u l]; simpl.
trivial.
unfold DecVar.eq_A; intros [y_eq_u | y_in_l]; [left; subst; reflexivity | right; apply IHl; trivial].
Qed.

Lemma total_acc_inst_inv :
  forall c sigma tau, is_a_total_oc_ordering sigma c = true ->
     (is_a_solution (mk_pb (acc_inst c sigma) nil) tau <-> is_a_solution (mk_pb sigma nil) tau).
Proof.
intro c; induction c as [ | v c]; intros sigma tau Hoc.
(* 1/2 basis case *)
simpl; intuition.
(* 1/1 induction step *)
assert (equiv_sol : forall rho rho' sol, (forall v, find X.eq_bool v rho = find X.eq_bool v rho') ->
                is_a_solution (mk_pb rho nil) sol -> is_a_solution (mk_pb rho' nil) sol).
(* intros rho rho' r_eq_r' [_ Sol]. Anomaly: refined called with a dependent meta. Please report. *)
intros rho rho' sol r_eq_r' [_ Sol']; split.
intros; contradiction.
intro x; assert (Solx := Sol' x); simpl in Solx; simpl; rewrite r_eq_r' in Solx; trivial.

assert (Hoc' : 
     is_a_total_oc_ordering
      (map_subst
         (fun (_ : variable) (t : term) =>
          apply_subst ((v, apply_subst sigma (Var v)) :: nil) t) sigma) c = true).
simpl in Hoc.
destruct (var_in_term v
               match find X.eq_bool v sigma with
               | Some v_sigma => v_sigma
               | None => Var v
               end); [discriminate | idtac].
case_eq (list_exists
               (fun z : variable =>
                var_in_term z
                  match find X.eq_bool v sigma with
                  | Some v_sigma => v_sigma
                  | None => Var v
                  end) c); intro Hoc'; rewrite Hoc' in Hoc; [discriminate | simpl in Hoc].
apply tail_total_ordering; trivial.

simpl; split; intro Sol.
rewrite (IHc _ tau Hoc') in Sol.
rewrite (rep_var_is_complete v).
refine (equiv_sol _ _ _ _ Sol).
intros x; assert (F := find_map_subst x v (apply_subst sigma (Var v)) sigma).
assert (F' := find_map X.eq_bool (apply_subst ((v, apply_subst sigma (Var v)) :: nil)) x sigma).
simpl; generalize (X.eq_bool_ok x v); case (X.eq_bool x v); [intro v_eq_x; subst x | intro v_diff_x].
simpl in F; case_eq (find X.eq_bool v sigma); [intro v_val | idtac]; intro v_sigma;
rewrite v_sigma in F; rewrite F.
apply f_equal; rewrite <- (empty_subst_is_id v_val) at 3.
rewrite <- subst_eq_vars.
intros x x_in_v_val; simpl.
generalize (X.eq_bool_ok x v); case (X.eq_bool x v); [intro v_eq_x; subst x | intros _; reflexivity].
rewrite <- var_in_term_is_sound in x_in_v_val.
simpl in Hoc; rewrite v_sigma in Hoc; rewrite x_in_v_val in Hoc; discriminate.
simpl in Hoc; rewrite v_sigma in Hoc; simpl in Hoc; revert Hoc.
generalize (X.eq_bool_ok v v); case (X.eq_bool v v); [intros _ | intro v_diff_v]; [intros; discriminate | absurd (v = v); trivial].
simpl in F; simpl in F'; case_eq (find X.eq_bool x sigma); [intro x_val | idtac]; 
intro x_sigma; rewrite x_sigma in F; rewrite F; rewrite x_sigma in F'; rewrite F'; trivial.

rewrite IHc; trivial.
rewrite (rep_var_is_complete v) in Sol.
refine (equiv_sol _ _ _ _ Sol).
intros x; assert (F := find_map_subst x v (apply_subst sigma (Var v)) sigma).
assert (F' := find_map X.eq_bool (apply_subst ((v, apply_subst sigma (Var v)) :: nil)) x sigma).
simpl; generalize (X.eq_bool_ok x v); case (X.eq_bool x v); [intro v_eq_x; subst x | intros x_diff_v].
simpl in F; case_eq (find X.eq_bool v sigma); [intro v_val | idtac]; intro v_sigma;
rewrite v_sigma in F; rewrite F.
symmetry; apply f_equal; rewrite <- (empty_subst_is_id v_val) at 3.
rewrite <- subst_eq_vars.
intros x x_in_v_val; simpl.
generalize (X.eq_bool_ok x v); case (X.eq_bool x v); [intro v_eq_x; subst x | intros x_diff_v].
rewrite <- var_in_term_is_sound in x_in_v_val.
simpl in Hoc; rewrite v_sigma in Hoc; rewrite x_in_v_val in Hoc; discriminate.
trivial.
simpl in Hoc; rewrite v_sigma in Hoc; simpl in Hoc; revert Hoc.
generalize (X.eq_bool_ok v v); case (X.eq_bool v v); [intros _ | intro v_diff_v]; [intros; discriminate | absurd (v = v); trivial].
simpl in F; simpl in F'; case_eq (find X.eq_bool x sigma); [intro x_val | idtac]; 
intro x_sigma; rewrite x_sigma in F; rewrite F; rewrite x_sigma in F'; rewrite F'; trivial.
Qed.

Lemma mgu_founded :
  forall sigma c, is_a_total_oc_ordering sigma c = true ->
  VSet.without_red c ->
 (VSet.LP.permut c (VSet.support (domain_of_subst sigma))) ->
  forall tau, is_a_solution (mk_pb sigma nil) tau <->
  (exists theta, 
  (forall x, apply_subst tau (Var x) = apply_subst theta (apply_subst (acc_inst c sigma) (Var x)))).
Proof.
intros sigma c Hoc W c_in_dom tau; rewrite <- (total_acc_inst_inv c); trivial.
split; intro Sol.
exists tau.
revert Sol; generalize (acc_inst c sigma); intros rho [_ Sol].
intro x; assert (Solx := Sol x); simpl in Solx; simpl.
case_eq (find X.eq_bool x tau); [intro x_val | idtac ]; intro x_tau; rewrite x_tau in Solx.
case_eq (find X.eq_bool x rho); [intro x_val' | idtac ]; intro x_rho; rewrite x_rho in Solx.
subst x_val; reflexivity.
simpl; rewrite x_tau; reflexivity.
case_eq (find X.eq_bool x rho); [intro x_val' | idtac ]; intro x_rho; rewrite x_rho in Solx.
trivial.
simpl; rewrite x_tau; reflexivity.

destruct Sol as [theta Sol].
assert (Idem : forall x y : variable,
       VSet.mem x (domain_of_subst (acc_inst c sigma)) ->
       VSet.mem y (domain_of_subst (acc_inst c sigma)) ->
       var_in_term x (apply_subst (acc_inst c sigma) (Var y)) = false).
intros x y x_in_dom y_in_dom; apply (total_acc_inst_idem _ _ Hoc W).
intros z z_in_c; rewrite <- (VSet.LP.mem_permut_mem z c_in_dom); apply in_impl_mem; trivial.
reflexivity.
rewrite <- acc_inst_dom in x_in_dom; rewrite <- (VSet.LP.mem_permut_mem x c_in_dom) in x_in_dom.
revert x_in_dom; generalize c; unfold VSet.mem, VSet.singleton, DecVar.eq_A; simpl.
intro l; induction l as [ | z l].
intros; contradiction.
intros [x_eq_z | x_in_l]; [left; subst | right; apply IHl]; trivial.
rewrite <- acc_inst_dom in y_in_dom; rewrite <- (VSet.LP.mem_permut_mem y c_in_dom) in y_in_dom.
revert y_in_dom; generalize c; unfold VSet.mem, VSet.singleton, DecVar.eq_A; simpl.
intro l; induction l as [ | z l].
intros; contradiction.
intros [y_eq_z | y_in_l]; [left; subst | right; apply IHl]; trivial.

revert Sol Idem; generalize (acc_inst c sigma).
intros rho Sol_tau Idem.
assert (Sol_rho := idem_sol _ Idem); destruct Sol_rho as [_ Sol_rho].
split.
intros; contradiction.
intro x; 
assert (Sol_taux := Sol_tau x); simpl; simpl in Sol_taux.
assert (Sol_rhox := Sol_rho x); simpl; simpl in Sol_rhox.
case_eq (find X.eq_bool x rho); [intro x_valr | trivial ]. 
intro x_rho; rewrite x_rho in Sol_taux; rewrite x_rho in Sol_rhox.
case_eq (find X.eq_bool x tau); [intro x_valt | idtac ]; intro x_tau; rewrite x_tau in Sol_taux.
rewrite Sol_taux.
rewrite Sol_rhox at 1.
rewrite <- subst_comp_is_subst_comp.
rewrite <- subst_eq_vars.
intros v _; rewrite subst_comp_is_subst_comp.
symmetry; apply Sol_tau.
rewrite Sol_taux.
rewrite Sol_rhox at 1.
rewrite <- subst_comp_is_subst_comp.
rewrite <- subst_eq_vars.
intros v _; rewrite subst_comp_is_subst_comp.
symmetry; apply Sol_tau.
Qed.

End Make.
