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


From Stdlib Require Import Arith List Wellfounded Wf_nat.
From CoLoR Require Import more_list list_permut list_sort term_spec term_o
     equational_theory ac matching dickson matching_well_formed matching_well_founded
     matching_sound matching_complete dickson.

Module Type S.

Declare Module Import CMatching : matching_complete.S.
Import SMatching WFMMatching WFMatching Matching Cf_eq_ac Ac EqTh T Sort.

(* Inductive well_formed_matching_problem *)
Inductive well_formed_matching_problem : Type :=
  | W : forall pb, well_formed_pb pb -> well_formed_matching_problem.

(* Definition well_formed_matching_problem_rect
Definition well_formed_matching_problem_ind
Definition well_formed_matching_problem_rec *)

(* Definition wfpb_weight *)
Definition wfpb_weight wfpb :=
  match wfpb with
  | W pb _ => pb_weight pb
  end.

(* Definition o_lpb *)
Definition o_lpb lwfpb1 lwfpb2 :=
 (NatMul.multiset_extension_step lt) 
 (map wfpb_weight lwfpb1) (map wfpb_weight lwfpb2).

(* Definition build_well_formed_matching_problem_list *)
Fixpoint build_well_formed_matching_problem_list 
 (lpb : list matching_problem) :  
 (forall p, In p lpb -> well_formed_pb p) -> list well_formed_matching_problem :=
 match lpb
    return (forall p, In p lpb -> well_formed_pb p) -> 
      list well_formed_matching_problem with 
 | nil => fun _ => nil
 | pb :: tl_lpb => fun proof =>
   (W pb (proof pb (or_introl _ (eq_refl _)))) ::
   (build_well_formed_matching_problem_list tl_lpb (@tail_prop _ _ pb tl_lpb proof))
  end.

(* Parameter weight_is_weight *)

(* Definition wf_solve *)
Definition wf_solve (wpb : well_formed_matching_problem) :=
  match wpb with
  | W pb w => 
   build_well_formed_matching_problem_list (solve pb) (well_formed_solve pb w)
  end.

(* Parameter F_wf_solve_dec1 *)
Parameter F_wf_solve_dec1 :
  forall wpb lpb', o_lpb lpb' (wpb :: lpb').

(* Parameter F_wf_solve_dec2 *)
Parameter F_wf_solve_dec2 :
  forall wpb lpb', o_lpb ((wf_solve wpb) ++ lpb') (wpb :: lpb').

(* Definition F_wf_solve *)
Definition F_wf_solve (lpb : list well_formed_matching_problem) :
 (forall y, o_lpb y lpb -> list well_formed_matching_problem) -> 
 list well_formed_matching_problem :=
match lpb return
          ((forall y : list well_formed_matching_problem,
          o_lpb y lpb -> list well_formed_matching_problem) ->
          list well_formed_matching_problem)
with
| nil => fun _ => nil
| wpb :: tl_lpb => 
    match wpb return
              ((forall y : list well_formed_matching_problem,
              o_lpb y (wpb :: tl_lpb) -> list well_formed_matching_problem) ->
              list well_formed_matching_problem)
    with
    | W pb w =>
        match pb return
                 (forall w1 : well_formed_pb pb,
                 (forall y : list well_formed_matching_problem,
                 o_lpb y (W pb w1 :: tl_lpb) -> list well_formed_matching_problem) ->
                 list well_formed_matching_problem)
        with
        | mk_pb existential_vars unsolved_part solved_part partly_solved_part =>
            fun w1 srec =>
            match unsolved_part return
                          (forall w2 : well_formed_pb
                                     (mk_pb existential_vars unsolved_part solved_part
                                     partly_solved_part),
                          (forall y : list well_formed_matching_problem,
                          o_lpb y
                            (W
                               (mk_pb existential_vars unsolved_part solved_part
                               partly_solved_part) w2 :: tl_lpb) ->
                               list well_formed_matching_problem) ->
                               list well_formed_matching_problem)
            with
            | nil => fun w2 srec3 =>
                W (mk_pb existential_vars nil solved_part partly_solved_part)
                  w2
                :: srec3 tl_lpb
                     (F_wf_solve_dec1
                        (W
                           (mk_pb existential_vars nil solved_part
                              partly_solved_part) w2) tl_lpb)
            | p :: unsolved_part0 =>
                fun w2 srec3 =>
                srec3
                  (wf_solve
                     (W
                        (mk_pb existential_vars (p :: unsolved_part0)
                           solved_part partly_solved_part) w2) ++ tl_lpb)
                  (F_wf_solve_dec2
                     (W
                        (mk_pb existential_vars (p :: unsolved_part0)
                           solved_part partly_solved_part) w2) tl_lpb)
            end w1 srec
        end w 
    end
end.

(* Parameter well_founded_o_lpb *)
Parameter well_founded_o_lpb : well_founded o_lpb.

(* Definition wf_solve_loop *)
Definition wf_solve_loop :
forall (l : list well_formed_matching_problem), 
(list well_formed_matching_problem) :=
Fix well_founded_o_lpb (fun l => list well_formed_matching_problem) F_wf_solve.

(*Parameter wf_solve_loop_unfold
Parameter wf_solve_nil
Parameter wf_solve_cons
Definition is_wf_sol
Parameter wf_projection
Parameter wf_solve_is_sound
Parameter wf_solve_loop_is_sound
Definition is_wf_wf_sol
Parameter wf_solve_is_complete
Parameter wf_solve_loop_is_complete
Parameter wf_solve_loop_end *)
(* Definition init_pb *)
Definition init_pb t1 t2 := mk_pb nil ((t1,t2) :: nil) nil nil.

(*Parameter well_formed_init_pb *)
Parameter well_formed_init_pb :
  forall t1 t2, well_formed_cf t1 -> well_formed_cf t2 -> 
  well_formed_pb (init_pb t1 t2).

(* Definition extract_solution *)
Fixpoint extract_solution 
 (solved_part :  substitution) 
  (partly_solved_part : list (variable*  partly_solved_term))
  {struct partly_solved_part} : substitution :=
 match partly_solved_part with
 | nil => solved_part
 | (x,x_part_val) :: tl_partly_solved_part =>
     let f := head_symb x_part_val in
     let x_val := 
       Term f 
         (quicksort 
           (flatten f 
             ((apply_cf_subst solved_part (Var (new_var x_part_val))) ::
              (closed_term x_part_val) :: nil))) in
    extract_solution ((x, x_val) :: solved_part) tl_partly_solved_part
 end.


(*Parameter extract_solution_unfold
Parameter extract_solution_in_solved_part
Parameter new_var_occ_in_solved_part
Parameter extract_solution_in_partly_solved_part *)

(* Definition clean_sol *)
Fixpoint clean_sol 
  (existential_vars : list variable) (sigma : substitution) 
  {struct sigma} : substitution :=
  match sigma with
  | nil => nil
  | (x,x_val) :: tl_sigma =>
      if mem_bool X.eq_bool x existential_vars
      then clean_sol existential_vars tl_sigma 
      else (x, x_val) :: (clean_sol existential_vars tl_sigma)
  end.

(* Definition matching *)
Definition matching t1 t2 Wt1 Wt2 :=
  map 
    (fun wpb => 
       match wpb with
       | W pb _ => 
          clean_sol (existential_vars pb)
                    (extract_solution (solved_part pb) (partly_solved_part pb))
       end)
    (wf_solve_loop 
      ((W (init_pb t1 t2) (well_formed_init_pb t1 t2 Wt1 Wt2)) :: nil)).

(* Parameter variable_preservation
Parameter matching_step1_is_sound
Parameter matching_step2_is_sound *)

(* Parameter matching_is_sound *)
Parameter matching_is_sound :
  forall t1 t2 Wt1 Wt2 sigma,
  In sigma (matching t1 t2 Wt1 Wt2) -> apply_cf_subst sigma t1 = t2.

(*Parameter matching_step1_is_complete
Parameter matching_step2_is_complete *)

(*Parameter matching_is_complete*)
Parameter matching_is_complete :
  forall t1 t2 Wt1 Wt2 sigma, well_formed_cf_subst sigma ->
  apply_cf_subst sigma t1 = t2 ->
  (exists sigma', In sigma' (matching t1 t2 Wt1 Wt2) /\
             (forall v, occurs_in_term v t1 ->
                  apply_cf_subst sigma  (Var v) = apply_cf_subst sigma' (Var v))).

End S.

Module Make (CMatching1 : matching_complete.S) :
 S with Module CMatching := CMatching1.

Module CMatching := CMatching1.

Import CMatching1 SMatching WFMMatching WFMatching Matching Cf_eq_ac Ac EqTh T F X Sort LPermut.

Inductive well_formed_matching_problem : Type :=
  | W : forall pb, well_formed_pb pb -> well_formed_matching_problem.

Definition wfpb_weight wfpb :=
  match wfpb with
  | W pb _ => pb_weight pb
  end.

Definition o_lpb lwfpb1 lwfpb2 :=
 (NatMul.multiset_extension_step lt) 
 (map wfpb_weight lwfpb1) (map wfpb_weight lwfpb2).

Fixpoint build_well_formed_matching_problem_list 
 (lpb : list matching_problem) :  (forall p, In p lpb -> well_formed_pb p) -> list well_formed_matching_problem :=
 match lpb
    return (forall p, In p lpb -> well_formed_pb p) -> 
      list well_formed_matching_problem with 
 | nil => fun _ => nil
 | pb :: tl_lpb => fun proof =>
   (W pb (proof pb (or_introl _ (eq_refl _)))) ::
   (build_well_formed_matching_problem_list tl_lpb (@tail_prop _ _ pb tl_lpb proof))
  end.

Lemma weight_is_weight : 
 forall lpb, forall proof : (forall p, In p lpb -> well_formed_pb p),
 map wfpb_weight (build_well_formed_matching_problem_list lpb proof) =
 map pb_weight lpb.
Proof.
induction lpb.
intros; trivial.
simpl; intro proof;
rewrite IHlpb; trivial.
Qed.

Definition wf_solve (wpb : well_formed_matching_problem) :=
  match wpb with
  | W pb w => 
   build_well_formed_matching_problem_list (solve pb) (well_formed_solve pb w)
  end.

Lemma F_wf_solve_dec1 :
  forall wpb lpb', o_lpb lpb' (wpb :: lpb').
Proof.
intros wpb lpb'; unfold o_lpb.
apply (@NatMul.rmv_case lt (map wfpb_weight lpb') (map wfpb_weight (wpb :: lpb')) 
                 (map wfpb_weight lpb') nil (wfpb_weight wpb)).
contradiction.
apply NatMul.LP.permut_refl.
apply NatMul.LP.permut_refl.
Qed.

Lemma F_wf_solve_dec2 :
  forall wpb lpb', o_lpb ((wf_solve wpb) ++ lpb') (wpb :: lpb').
Proof.
intros wpb lpb'; unfold o_lpb, wf_solve; destruct wpb.
simpl; rewrite map_app; rewrite weight_is_weight.
apply (@NatMul.rmv_case lt ((map pb_weight (solve pb)) ++ map wfpb_weight lpb')
(pb_weight pb :: map wfpb_weight lpb') 
(map wfpb_weight lpb') (map pb_weight (solve pb)) (pb_weight pb)).
generalize (well_founded_solve pb w).
replace (WFMatching.Matching.solve pb) with (solve pb); [idtac | trivial].
clear w lpb'; generalize (solve pb); induction l.
contradiction.
intros H b In_b; elim In_b; clear In_b; intro In_b.
unfold NatMul.LP.EDS.eq_A, NatMul.DS.eq_A in *;
subst b; apply H; left; trivial.
apply IHl; trivial; intros; apply H; right; trivial.
apply NatMul.LP.permut_refl.
apply NatMul.LP.permut_refl.
Qed.

Definition F_wf_solve (lpb : list well_formed_matching_problem) :
 (forall y, o_lpb y lpb -> list well_formed_matching_problem) -> 
 list well_formed_matching_problem :=
match lpb return
          ((forall y : list well_formed_matching_problem,
          o_lpb y lpb -> list well_formed_matching_problem) ->
          list well_formed_matching_problem)
with
| nil => fun _ => nil
| wpb :: tl_lpb => 
    match wpb return
              ((forall y : list well_formed_matching_problem,
              o_lpb y (wpb :: tl_lpb) -> list well_formed_matching_problem) ->
              list well_formed_matching_problem)
    with
    | W pb w =>
        match pb return
                 (forall w1 : well_formed_pb pb,
                 (forall y : list well_formed_matching_problem,
                 o_lpb y (W pb w1 :: tl_lpb) -> list well_formed_matching_problem) ->
                 list well_formed_matching_problem)
        with
        | mk_pb existential_vars unsolved_part solved_part partly_solved_part =>
            fun w1 srec =>
            match unsolved_part return
                          (forall w2 : well_formed_pb
                                     (mk_pb existential_vars unsolved_part solved_part
                                     partly_solved_part),
                          (forall y : list well_formed_matching_problem,
                          o_lpb y
                            (W
                               (mk_pb existential_vars unsolved_part solved_part
                               partly_solved_part) w2 :: tl_lpb) ->
                               list well_formed_matching_problem) ->
                               list well_formed_matching_problem)
            with
            | nil => fun w2 srec3 =>
                W (mk_pb existential_vars nil solved_part partly_solved_part)
                  w2
                :: srec3 tl_lpb
                     (F_wf_solve_dec1
                        (W
                           (mk_pb existential_vars nil solved_part
                              partly_solved_part) w2) tl_lpb)
            | p :: unsolved_part0 =>
                fun w2 srec3 =>
                srec3
                  (wf_solve
                     (W
                        (mk_pb existential_vars (p :: unsolved_part0)
                           solved_part partly_solved_part) w2) ++ tl_lpb)
                  (F_wf_solve_dec2
                     (W
                        (mk_pb existential_vars (p :: unsolved_part0)
                           solved_part partly_solved_part) w2) tl_lpb)
            end w1 srec
        end w 
    end
end.

(*
Definition F_wf_solve : forall lpb : list well_formed_matching_problem,
 (forall y, o_lpb y lpb -> list well_formed_matching_problem) ->
 list well_formed_matching_problem.
Proof.
intros lpb srec; destruct lpb.
exact nil.
destruct w.
destruct pb.
destruct unsolved_part.
refine (W (mk_pb existential_vars nil solved_part partly_solved_part) w ::
        (srec lpb (F_wf_solve_dec1 _ _))).
refine (srec ((wf_solve 
                (W (mk_pb existential_vars (p :: unsolved_part) solved_part
                       partly_solved_part) w)) ++ lpb)
             (F_wf_solve_dec2  _ _)). 
Defined. 
*)

Lemma well_founded_o_lpb : well_founded o_lpb.
Proof.
unfold o_lpb;
apply (wf_inverse_image _ _ (NatMul.multiset_extension_step lt)
(map wfpb_weight) (NatMul.dickson lt_wf)).
Qed.

Definition wf_solve_loop :
forall (l : list well_formed_matching_problem), 
(list well_formed_matching_problem) :=
Fix well_founded_o_lpb (fun l => list well_formed_matching_problem) F_wf_solve.

Lemma wf_solve_loop_unfold : forall l : list well_formed_matching_problem,
wf_solve_loop l = @F_wf_solve l (fun y _ => wf_solve_loop y).
Proof.
intros; unfold wf_solve_loop;
apply Fix_eq with 
(P:= (fun _:list well_formed_matching_problem => list well_formed_matching_problem));
intros; destruct x.
trivial.
unfold F_wf_solve; destruct w as [pb w];
destruct pb as [starting_vars un_slvd_part slvd_part party_slvd_part];
destruct un_slvd_part; rewrite H; trivial.
Qed.

Lemma wf_solve_nil : 
  wf_solve_loop nil = nil. 
Proof.
rewrite wf_solve_loop_unfold; simpl; trivial.
Qed.

Lemma wf_solve_cons :
 forall wpb lpb,
 wf_solve_loop (wpb :: lpb) = match wpb with
                               | W pb w => 
                               match unsolved_part pb with
                                 | nil => wpb :: (wf_solve_loop lpb)
                                 | _ :: _ => 
                                     wf_solve_loop ((wf_solve wpb) ++ lpb) 
                                 end
                               end.
Proof.
intros wpb lpb; rewrite wf_solve_loop_unfold;
destruct wpb as [pb w]; 
destruct pb as [starting_vars un_slvd_part slvd_part party_slvd_part]; 
destruct un_slvd_part;
simpl; trivial.
Qed.

Definition is_wf_sol wpb sigma :=
 match wpb with
 | W pb _ => is_sol pb sigma
 end.

Lemma wf_projection :
 forall pb w lpb proof, 
 In (W pb w) (build_well_formed_matching_problem_list lpb proof) ->
 In pb lpb.
Proof. 
intros pb w lpb; induction lpb.
contradiction.
intros proof In_wpb; simpl in In_wpb; elim In_wpb; clear In_wpb; intro In_wpb.
injection In_wpb; intro; left; trivial.
right; apply (IHlpb _ In_wpb).
Qed.

Lemma wf_solve_is_sound :
 forall wpb p sigma, 
 In p (wf_solve wpb) -> is_wf_sol p sigma -> is_wf_sol wpb sigma. 
Proof.
intros wpb p sigma; destruct wpb; destruct p; unfold wf_solve, is_wf_sol;
intros; apply (solve_is_sound pb sigma w pb0); trivial;
apply (wf_projection _ _ _ _ H); trivial.
Qed.

Theorem wf_solve_loop_is_sound :
  forall lpb p sigma,
  In p (wf_solve_loop lpb) -> is_wf_sol p sigma ->
  exists pb, In pb lpb /\ is_wf_sol pb sigma.
Proof.
intro lpb;
refine (well_founded_ind well_founded_o_lpb
(fun lpb => forall p sigma,
  In p (wf_solve_loop lpb) -> is_wf_sol p sigma ->
  exists pb, In pb lpb /\ is_wf_sol pb sigma) _ _);
clear lpb; 
intros lpb IH p sigma In_p Is_sol_p;
destruct lpb.
rewrite wf_solve_nil in In_p; contradiction.
rewrite wf_solve_cons in In_p; destruct w; destruct (unsolved_part pb).
elim In_p; clear In_p; intro In_p.
exists p; split; trivial; left; subst p; trivial.
elim (IH lpb (F_wf_solve_dec1 _ _) p sigma In_p Is_sol_p);
intros pb0 H; elim H; clear H; 
intros In_pb0 Is_sol_pb0; 
exists pb0; split; trivial; right; trivial.
elim (IH (wf_solve (W pb w) ++ lpb) (F_wf_solve_dec2 _ _) p sigma In_p Is_sol_p);
intros pb0 H; elim H; clear H; 
intros In_pb0 Is_sol_pb0;
elim (in_app_or _ _ _ In_pb0); clear In_pb0; intro In_pb0.
exists (W pb w); split;
[ left; trivial
| apply (wf_solve_is_sound _ _ _ In_pb0 Is_sol_pb0) ].
exists pb0; split; trivial; right; trivial.
Qed.

Definition is_wf_wf_sol wpb sigma :=
 match wpb with
 | W pb _ => is_well_formed_sol pb sigma
 end.

Lemma wf_solve_is_complete :
  forall wpb sigma, is_wf_wf_sol wpb sigma ->
  match wpb with
  | W pb _ =>
    match unsolved_part pb with
    | nil => True
    | _ :: _ => exists pb, In pb (wf_solve wpb) /\ is_wf_wf_sol pb sigma
    end
  end.
Proof.
destruct wpb; unfold is_wf_wf_sol;
intros sigma Is_sol; generalize (solve_is_complete pb w sigma Is_sol);
destruct (unsolved_part pb); trivial.
unfold wf_solve.
generalize (solve pb) (well_formed_solve pb w). 
induction l0;
intros w0 H; simpl in H; elim H; clear H;
intros pb' H; elim H; clear H.
contradiction.
intros In_pb' Is_sol'; elim In_pb'; clear In_pb'; intro In_pb'; simpl.
exists 
(W a
     (w0 a
        (or_introl
           ((fix In (a0 : matching_problem) (l1 : list matching_problem)
                    {struct l1} : Prop :=
               match l1 with
               | nil => False
               | b :: m => b = a0 \/ In a0 m
               end) a l0) (eq_refl a))));
split; [ left | subst pb' ]; trivial.
cut (exists pb' : matching_problem,
          In pb' l0 /\ is_well_formed_sol pb' sigma).
intro H;
elim (IHl0 (@tail_prop _ _ a l0 w0) H); clear H;
intros pb0 H; elim H; clear H; intros In_pb0 Is_sol0;
exists pb0; split; trivial; right; trivial.
exists pb'; split; trivial.
Qed.

Theorem wf_solve_loop_is_complete :
  forall lpb p sigma,
  In p lpb -> is_wf_wf_sol p sigma ->
  exists pb, In pb (wf_solve_loop lpb) /\ is_wf_wf_sol pb sigma.
Proof.
intro lpb;
refine (well_founded_ind well_founded_o_lpb
(fun lpb => forall p sigma,
  In p lpb -> is_wf_wf_sol p sigma ->
  exists pb, In pb (wf_solve_loop lpb) /\ is_wf_wf_sol pb sigma) _ _);
clear lpb; 
intros lpb IH p sigma In_p Is_sol_p;
destruct lpb.
contradiction.
rewrite wf_solve_cons;
elim In_p; clear In_p; intro In_p.
generalize (wf_solve_is_complete p sigma Is_sol_p); subst p; simpl.
destruct w; destruct (unsolved_part pb).
intros _; exists (W pb w); split; trivial; left; trivial.
clear p; intro H; elim H; clear H; 
intros p H; elim H; clear H;
intros In_p Is_sol;
refine (IH (wf_solve (W pb w) ++ lpb) (F_wf_solve_dec2 _ _) p sigma 
(in_or_app _ _ _ (or_introl _ In_p)) Is_sol).
destruct w; destruct (unsolved_part pb).
elim (IH lpb (F_wf_solve_dec1 _ _) p sigma In_p Is_sol_p). 
intros pb0 H; elim H; clear H; intros; exists pb0; split; trivial; right; trivial.
elim (IH (wf_solve (W pb w) ++ lpb) (F_wf_solve_dec2 _ _) p sigma 
(in_or_app _ _ _ (or_intror _ In_p)) Is_sol_p).
intros pb0 H; elim H; clear H; intros; exists pb0; split; trivial; right; trivial.
Qed.

Lemma wf_solve_loop_end :
  forall lpb wpb, 
  In wpb (wf_solve_loop lpb) ->
  match wpb with
  | W pb _ => (unsolved_part pb) = nil
  end.
Proof.
intro lpb;
refine (well_founded_ind well_founded_o_lpb
(fun lpb => forall wpb,
  In wpb (wf_solve_loop lpb) ->
  match wpb with
  | W pb _ => (unsolved_part pb) = nil
  end) _ _).
clear lpb;
intros lpb IH wpb; destruct lpb.
rewrite wf_solve_nil; contradiction.
rewrite wf_solve_cons; destruct w.
cut (forall pb1, pb1 = pb -> unsolved_part pb1 = unsolved_part pb).
intro H; destruct (unsolved_part pb);
generalize (H pb (eq_refl _)); clear H; intros H In_wpb.
elim In_wpb; clear In_wpb; intro In_wpb.
subst wpb; trivial.
refine (IH lpb (F_wf_solve_dec1 _ _) _ In_wpb).
refine (IH (wf_solve (W pb w) ++ lpb) (F_wf_solve_dec2 _ _) _ In_wpb).
intros; subst pb; trivial.
Qed.

Definition init_pb t1 t2 := mk_pb nil ((t1,t2) :: nil) nil nil.

Lemma well_formed_init_pb :
  forall t1 t2, well_formed_cf t1 -> well_formed_cf t2 -> 
  well_formed_pb (init_pb t1 t2).
Proof.
intros t1 t2 Wt1 Wt2; unfold well_formed_pb, init_pb; simpl; intuition.
injection H0; intros; subst t0; trivial.
injection H0; intros; subst t3; trivial.
absurd (None = Some p); trivial; discriminate.
Qed.

Fixpoint extract_solution 
 (solved_part :  substitution) 
  (partly_solved_part : list (variable*  partly_solved_term))
  {struct partly_solved_part} : substitution :=
 match partly_solved_part with
 | nil => solved_part
 | (x,x_part_val) :: tl_partly_solved_part =>
     let f := head_symb x_part_val in
     let x_val := 
       Term f 
         (quicksort 
           (flatten f 
             ((apply_cf_subst solved_part (Var (new_var x_part_val))) ::
              (closed_term x_part_val) :: nil))) in
    extract_solution ((x, x_val) :: solved_part) tl_partly_solved_part
 end.

Lemma extract_solution_unfold :
  forall solved_part partly_solved_part x x_part_val,
  extract_solution solved_part ((x,x_part_val) :: partly_solved_part) =
  extract_solution 
    ((x, (Term (head_symb x_part_val) 
         (quicksort 
           (flatten (head_symb x_part_val)
             ((apply_cf_subst solved_part (Var (new_var x_part_val))) ::
              (closed_term x_part_val) :: nil))))) :: solved_part)
    partly_solved_part.
Proof.
intros; trivial.
Qed.

Lemma extract_solution_in_solved_part : forall solved_part partly_solved_part v t,
  nb_occ X.eq_bool v solved_part + 
  nb_occ X.eq_bool v partly_solved_part <= 1 ->
  find X.eq_bool v solved_part = Some t ->
  apply_cf_subst (extract_solution solved_part partly_solved_part) (Var v) = t.
Proof.

intros sp psp; generalize sp; clear sp; induction psp as [ | [x s] psp];
intros sp v t H v_sp.
simpl; rewrite v_sp; trivial.
rewrite extract_solution_unfold; apply IHpsp.
simpl; simpl in H; revert H; generalize (X.eq_bool_ok v x); case (X.eq_bool v x); [intro v_eq_x | intro v_diff_x]; trivial.
intro H; rewrite Nat.add_comm in H; simpl in H; rewrite Nat.add_comm in H; simpl; trivial.
revert H; simpl; generalize (X.eq_bool_ok v x); case (X.eq_bool v x); [intros _ | intro v_diff_x]; trivial.
generalize (some_nb_occ_Sn X.eq_bool v _ v_sp);
destruct (nb_occ X.eq_bool v sp) as [ | n].
intro; absurd (1 <= 0); auto with arith.
intros _ H; simpl in H; rewrite Nat.add_comm in H; simpl in H.
absurd (S(S (nb_occ X.eq_bool v psp + n)) <= 1); auto with arith.
Qed.

Lemma new_var_occ_in_solved_part :
  forall pb, unsolved_part pb = nil -> 
  well_sorted_partly_solved_part (partly_solved_part pb) ->
  (forall v p, 
    find X.eq_bool v (partly_solved_part pb) = Some p -> occurs_in_pb (new_var p) pb) ->
  match partly_solved_part pb with
  | nil => True
  | (v,p) :: _ => match find X.eq_bool (new_var p) (solved_part pb) with
                  | Some _ => True
                  | None => False
                  end
  end.
Proof.
intros [starting_vars usp sp [ | [v ps] psp]] U well_sorted new_var_occ.
trivial.
generalize (new_var_occ v ps); simpl.
generalize (X.eq_bool_ok v v); case (X.eq_bool v v); [intros _ | intro v_diff_v; apply False_rect; apply v_diff_v; reflexivity].
intro new_var_ps_occ; 
generalize (new_var_ps_occ (eq_refl _)); clear new_var_ps_occ;
unfold occurs_in_pb; simpl in U; subst usp; simpl;
intros [F | new_var_ps_occ]; [contradiction | idtac].
generalize (some_nb_occ_Sn X.eq_bool (new_var ps) psp);
destruct (find X.eq_bool (new_var ps) psp) as [new_var_ps_val | ].
intro F; generalize (F new_var_ps_val (eq_refl _)); clear F; intros F;
simpl in well_sorted; destruct well_sorted as [_ [H _]];
assert (new_var_diff_new_var := H _ F);
absurd (new_var ps = new_var ps); trivial.
revert new_var_ps_occ; generalize (X.eq_bool_ok (new_var ps) v); case (X.eq_bool (new_var ps) v); [intro new_var_ps_eq_v | intro new_var_ps_diff_v].
absurd (v  = new_var ps); [destruct well_sorted | apply sym_eq]; trivial.
intuition.
Qed.

Lemma extract_solution_in_partly_solved_part :
forall solved_part partly_solved_part ex,
 (forall v, nb_occ X.eq_bool v solved_part +
               nb_occ X.eq_bool v partly_solved_part <= 1) ->
  well_sorted_partly_solved_part partly_solved_part ->
  (forall v p, find X.eq_bool v partly_solved_part = Some p ->
              occurs_in_pb (new_var p)
                (mk_pb ex nil solved_part partly_solved_part)) ->
  forall v p, find X.eq_bool v partly_solved_part = Some p ->
  apply_cf_subst (extract_solution solved_part partly_solved_part) (Var v) = 
  Term (head_symb p) 
         (quicksort 
           (flatten (head_symb p) 
             ((apply_cf_subst (extract_solution solved_part partly_solved_part) 
                              (Var (new_var p))) ::
              (closed_term p) :: nil))).
Proof.
intros sp psp; generalize sp; clear sp; induction psp as [ | [x s] psp];
intros sp ex only_one_occ well_sorted new_var_occ y p y_psp.
discriminate.

simpl in y_psp; rewrite extract_solution_unfold.
revert y_psp; generalize (X.eq_bool_ok y x); case (X.eq_bool y x); [intros y_eq_x y_psp | intros y_diff_x y_psp].
injection y_psp; intros; subst.
assert (H :=
  (extract_solution_in_solved_part 
  ((x, (Term (head_symb p)
           (quicksort
              (flatten (head_symb p)
                 (apply_cf_subst sp (Var (new_var p))
                  :: closed_term p :: nil))))) :: sp)
   psp x
   (Term (head_symb p)
           (quicksort
              (flatten (head_symb p)
                 (apply_cf_subst sp (Var (new_var p))
                  :: closed_term p :: nil)))))).
refine (trans_eq (H _ _) _); clear H y_psp. (* instead of rewrite H, coq bug ? *)
generalize (only_one_occ x); simpl; 
generalize (X.eq_bool_ok x x); case (X.eq_bool x x); [intros _ | intro x_diff_x; apply False_rect; apply x_diff_x; reflexivity].
rewrite Nat.add_comm; simpl; rewrite Nat.add_comm; subst; trivial.
simpl; generalize (X.eq_bool_ok x x); case (X.eq_bool x x); [intros _ | intro x_diff_x; apply False_rect; apply x_diff_x; reflexivity].
reflexivity.
apply (f_equal (fun t => 
        Term (head_symb p)
            (quicksort (flatten (head_symb p) (t :: closed_term p :: nil))))).
generalize (new_var_occ_in_solved_part (mk_pb ex nil sp ((x,p) :: psp))
                          (eq_refl _) well_sorted new_var_occ).
simpl partly_solved_part; simpl solved_part.
replace (apply_cf_subst sp (Var (new_var p))) with
(match find eq_var_bool (new_var p) sp with
                | Some  new_var_p_val => new_var_p_val
                | None => Var (new_var p)
                end) by reflexivity.
case_eq (find X.eq_bool (new_var p) sp); [intros new_var_p_val F _ | intros F]; [idtac | contradiction].
assert (H:= 
   (extract_solution_in_solved_part 
     ((x, (Term (head_symb p)
           (quicksort
              (flatten (head_symb p)
                 (apply_cf_subst sp (Var (new_var p))
                  :: closed_term p :: nil))))) :: sp)
   psp (new_var p) new_var_p_val)).
rewrite <- H at 1.
simpl apply_cf_subst at 2; rewrite F; reflexivity.
generalize (only_one_occ (new_var p)); simpl;
generalize (X.eq_bool_ok (new_var p) x); case (X.eq_bool (new_var p) x); [intro new_var_p_eq_x | intro new_var_p_diff_x].
destruct well_sorted as [x_diff_new_var_p _]; 
absurd (x = new_var p); trivial; apply sym_eq; trivial.
trivial.
simpl; generalize (X.eq_bool_ok (new_var p) x); case (X.eq_bool (new_var p) x); [intro new_var_p_eq_x | intro new_var_p_diff_x].
destruct well_sorted as [x_diff_new_var_p _]; 
absurd (x = new_var p); trivial; apply sym_eq; trivial.
trivial.

refine (IHpsp _ ex _ _ _ y p y_psp).
intros z; generalize (only_one_occ z); simpl;
generalize (X.eq_bool_ok z x); case (X.eq_bool z x); [intro z_eq_x | intro z_diff_x]; trivial.
rewrite Nat.add_comm; simpl; rewrite Nat.add_comm; trivial.
inversion well_sorted; intuition.
intros z z_val z_psp; 
generalize (new_var_occ z) (only_one_occ z) 
                    (some_nb_occ_Sn X.eq_bool z psp z_psp);
simpl find; simpl nb_occ;
generalize (X.eq_bool_ok z x); case (X.eq_bool z x); [intro z_eq_x | intro z_diff_x].
intros _; subst z; destruct (nb_occ X.eq_bool x psp) as [ | n].
intros; absurd (1 <= 0); auto with arith.
rewrite Nat.add_comm; simpl plus;
intros; absurd (S (S (n + nb_occ X.eq_bool x sp)) <= 1); auto with arith.
intros H _ _; generalize (H z_val z_psp).
unfold occurs_in_pb; simpl;
intros [occ_in_usp | [occ_in_psp | occ_in_sp]].
contradiction.
right; revert occ_in_psp.
case (X.eq_bool (new_var z_val) x); [right | left]; trivial.
case (X.eq_bool (new_var z_val) x); right; right; trivial.
Qed.

Fixpoint clean_sol 
  (existential_vars : list variable) (sigma : substitution) 
  {struct sigma} : substitution :=
  match sigma with
  | nil => nil
  | (x,x_val) :: tl_sigma =>
      if mem_bool X.eq_bool x existential_vars
      then clean_sol existential_vars tl_sigma 
      else (x, x_val) :: (clean_sol existential_vars tl_sigma)
  end.

Definition matching t1 t2 Wt1 Wt2 :=
  map 
    (fun wpb => 
       match wpb with
       | W pb _ => 
          clean_sol (existential_vars pb)
                    (extract_solution (solved_part pb) (partly_solved_part pb))
       end)
    (wf_solve_loop 
      ((W (init_pb t1 t2) (well_formed_init_pb t1 t2 Wt1 Wt2)) :: nil)).

Lemma variable_preservation :
 forall v lpb, 
 (forall wpb, In wpb lpb ->
 match wpb with
 | W pb _ => (~ In v (existential_vars pb)) /\ (occurs_in_pb v pb)
 end) ->
 (forall wpb', In wpb' (wf_solve_loop lpb) ->
  match wpb' with
 | W pb' _ =>  (~ In v (existential_vars pb')) /\ (occurs_in_pb v pb')
  end).
Proof.
intros x lpb;
refine (well_founded_ind well_founded_o_lpb
    (fun lpb =>
       (forall wpb : well_formed_matching_problem, In wpb lpb ->
          match wpb with
          | W pb _ => ~ In x (existential_vars pb) /\ occurs_in_pb x pb
          end) ->
       forall wpb' : well_formed_matching_problem, In wpb' (wf_solve_loop lpb) ->
       match wpb' with
       | W pb' _ => ~ In x (existential_vars pb') /\ occurs_in_pb x pb'
       end) _ _).
clear lpb; intros lpb IH P_lpb wpb; destruct lpb as [ | [pb w_pb] lpb].
rewrite wf_solve_nil; contradiction.
rewrite wf_solve_cons; destruct pb as [ex [ | [s t] usp] sp psp];
simpl unsolved_part; cbv iota.
intros [wpb_eq_w_pb | wpb_in_loop_lpb].
subst wpb; apply (P_lpb (W (mk_pb ex nil sp psp) w_pb)); trivial; left; trivial.
refine (IH lpb (F_wf_solve_dec1 _ _) _ wpb wpb_in_loop_lpb); 
intros; apply P_lpb; right; trivial.

intro wpb_in_loop; 
refine (IH (wf_solve (W (mk_pb ex ((s, t) :: usp) sp psp) w_pb) ++ lpb) (F_wf_solve_dec2 _ _) _ wpb wpb_in_loop).
clear wpb wpb_in_loop; intros wpb wpb_in_loop.
destruct (in_app_or _ _ _ wpb_in_loop) as [wpb_in_solve_pb | wpb_in_loop_lpb];
clear wpb_in_loop; [ idtac |  apply P_lpb; right; trivial].
generalize (P_lpb _ (or_introl _ (eq_refl _))); simpl existential_vars; intros [NE O].
destruct wpb as [pb' w_pb']; generalize (wf_projection _ _ _ _ wpb_in_solve_pb).
clear lpb IH P_lpb; unfold solve; simpl unsolved_part; simpl solved_part; cbv iota beta.
destruct s as [ v | f1 l1].
(* 1: s is a variable (Var v) *)
case_eq (find X.eq_bool v sp); [intros v_val v_sp| intro v_sp].
(* 1.1 s=v has a value v_val in sp *)
generalize (T.eq_bool_ok v_val t); case (T.eq_bool v_val t); [intro v_val_eq_t | intros; contradiction].
(*  1.1.1 s=v has a value v_val in sp, which is equal to t 
vs 1.1.2 s=v has a value v_val in sp, which is NOT equal to t *)
simpl existential_vars; simpl partly_solved_part;
intros [pb'_eq_pb1 | pb'_in_nil]; [subst pb' | contradiction].
split; [trivial | idtac].
destruct O as [ O | O ]; [idtac | right; trivial].
simpl unsolved_part in O; elim O; clear O; intro O.
simpl in O; subst v; right; right; simpl; rewrite v_sp; trivial.
left; trivial.
(* 1.2 s=v has NO value in sp *)
simpl partly_solved_part;
case_eq (find X.eq_bool v psp); [intros v_pval v_psp | intro v_psp].
(* 1.2.1 s=v has NO value in sp, but has a value v_pval in psp *)
destruct t as [ | f2 l2]; [intro; contradiction | idtac].
generalize (F.Symb.eq_bool_ok (head_symb v_pval) f2); case (F.Symb.eq_bool (head_symb v_pval) f2); 
[intro top_v_pval_eq_f2 | intros; contradiction].
destruct (remove T.eq_bool (closed_term v_pval) l2); [idtac | intros; contradiction].
intros [pb'_eq_pb1 | pb'_in_nil]; [subst pb' | contradiction].
simpl existential_vars; split; [trivial | idtac].
destruct O as [ O | [ O | O ]].
simpl unsolved_part in O; elim O; clear O; intro O.
simpl in O; subst v; right; left; simpl; rewrite v_psp; trivial.
left; right; trivial.
right; trivial.
left; trivial.
right; right; trivial.
(* 1.2.2 s=v has NO value in sp, and NO value in psp *)
intros [pb'_eq_pb1 | pb'_in_nil]; [subst pb' | intros; contradiction].
simpl existential_vars; split; [trivial | idtac].
destruct O as [ [O | O] | [ O | O ]].
simpl in O; subst v; right; right; simpl; 
generalize (X.eq_bool_ok x x); case (X.eq_bool x x); [intros _; exact I | intro x_diff_x; apply False_rect; apply x_diff_x; reflexivity].
left; trivial.
right; left; trivial.
right; right; simpl; case (X.eq_bool x v); trivial.

(* 2 s is a term (Term f1 l1) *)
destruct t as [ | f2 l2]; [intros; contradiction | idtac].
generalize (F.Symb.eq_bool_ok f1 f2); case (F.Symb.eq_bool f1 f2); [intro f1_eq_f2 | intros; contradiction].
(* 2 s = Term f1 l1, t = Term f2 l2, f1 = f2 *)
subst f2; case_eq (arity f1); [ intro Af1| intro Af1 | intros n Af1].
(* 2.1 arity f1 = AC *)
destruct (le_gt_dec (length l1) (length l2)) as [L | L]; [idtac | intros; contradiction].
simpl; destruct l1 as [ | [v1 | g1 ll1] l1].
(* 2.1.1 s = Term f1 l1, t = Term f2 l2, f1 = f2, l1 = nil *)
intros [pb'_eq_pb1 | pb'_in_nil]; [subst pb' | intros; contradiction].
split.
trivial.
destruct O as [ [O | O] | O]; [contradiction | left; trivial | right; trivial].
(* 2.1.2 s = Term f1 l1, t = Term f2 l2, f1 = f2, l1 = (Var v1) :: l1 *)
simpl solved_part;
case_eq (find X.eq_bool v1 sp); [intros v1_val v1_sp | intro v1_sp].
(* 2.1.2.1 s = Term f1 l1, t = Term f2 l2, f1 = f2, l1 = (Var v1) :: l1, 
                 v1 has a value v1_val in sp *)
unfold ac_elementary_solve_term_var_with_val_term; simpl.
destruct (remove T.eq_bool v1_val l2) as [l2' | ].
(* 2.1.2.1.1 s = Term f1 l1, t = Term f2 l2, f1 = f2, l1 = (Var v1) :: l1, 
                 v1 has a value v1_val in sp, l2 ~ v1_val :: l2' *)
intros [pb'_eq_pb1 | pb'_in_nil]; [subst pb' | intros; contradiction].
split; [trivial | idtac].
destruct O as [ [[O | O] | O] | O]; [idtac | idtac | idtac | right; trivial].
simpl in O. subst x; right; right; simpl; rewrite v1_sp; trivial.
left; left; destruct l1 as [ | s1 [ | t1 l1]]; [contradiction | intuition | simpl].
apply list_permut_occurs_in_term_list with (s1 :: t1 :: l1); trivial; apply quick_permut.
left; right; trivial.
(* 2.1.2.1.2 s = Term f1 l1, t = Term f2 l2, f1 = f2, l1 = (Var v1) :: l1, 
                 v1 has a value v1_val in sp, l2 <> v1_val :: l2' *)
destruct v1_val as [ | g ll]; [intros; contradiction | idtac].
generalize (F.Symb.eq_bool_ok f1 g); case (F.Symb.eq_bool f1 g); [intros f1_eq_g; subst g | intros f1_diff_g; contradiction].
destruct (remove_list ll l2) as [l2' | ]; [idtac | intros; contradiction].
unfold EDS.A, DOS.A in *; 
destruct (le_gt_dec (length l1) (length l2')) as [L' | L']; [idtac | intros; contradiction].
intros [pb'_eq_pb1 | pb'_in_nil]; [subst pb' | intros; contradiction].
split; [trivial | idtac].
destruct O as [ [[O | O] | O] | O]; [idtac | idtac | idtac | right; trivial].
simpl in O. subst x; right; right; simpl; rewrite v1_sp; trivial.
left; left; destruct l1 as [ | s1 [ | t1 l1]]; [contradiction | intuition | simpl].
apply list_permut_occurs_in_term_list with (s1 :: t1 :: l1); trivial; apply quick_permut.
left; right; trivial.
(* 2.1.2.2 s = Term f1 l1, t = Term f2 l2, f1 = f2, l1 = (Var v1) :: l1, 
                 v1 has NO value in sp *)
case_eq (find X.eq_bool v1 psp); [intros v1_pval v1_psp| intro v1_psp].
(* 2.1.2.2.1 s = Term f1 l1, t = Term f2 l2, f1 = f2, l1 = (Var v1) :: l1, 
                 v1 has NO value in sp, v1 has a partial value v1_pval in psp *)
unfold ac_elementary_solve_term_var_with_part_val_term.
generalize (F.Symb.eq_bool_ok f1 (head_symb v1_pval)); case (F.Symb.eq_bool f1 (head_symb v1_pval)); 
[intro f1_eq_top_v1_pval | intro f1_diff_top_v1_pval].
(* 2.1.2.2.1.1 s = Term f1 l1, t = Term f2 l2, f1 = f2, l1 = (Var v1) :: l1, 
                 v1 has NO value in sp, v1 has a partial value v1_pval in psp,
                 v1_pval has top function symbol equal to f1 *)
destruct (remove T.eq_bool (closed_term v1_pval) l2) as [l2' | ]; 
[idtac | intros; contradiction].
intros [pb'_eq_pb1 | pb'_in_nil]; [subst pb' | intros; contradiction].
split; [trivial | idtac].
destruct O as [ [ [ O | O] | O] | O ]; [idtac | idtac | idtac | right; trivial].
simpl in O. subst x; right; left; simpl; rewrite v1_psp; trivial.
left; left; destruct l1 as [ | t1 l1]; [contradiction | idtac].
simpl; apply list_permut_occurs_in_term_list with ((Var (new_var v1_pval)) :: t1 :: l1);
[ apply quick_permut | right; trivial ].
left; right; trivial.
(* 2.1.2.2.1.2 s = Term f1 l1, t = Term f2 l2, f1 = f2, l1 = (Var v1) :: l1, 
                 v1 has NO value in sp, v1 has a partial value v1_pval in psp 
                 v1_pval has top function symbol different from f1 *)
intro pb'_in_lpb; pattern pb';
refine (prop_map_without_repetition _ T.eq_bool_ok  _ _ _ _ _ pb'_in_lpb);
clear pb' w_pb' pb'_in_lpb wpb_in_solve_pb; intros t2 t2_in_l2; 
destruct t2 as [ | g2 ll2 ]; [trivial | idtac].
generalize (F.Symb.eq_bool_ok g2 (head_symb v1_pval)); case (F.Symb.eq_bool g2 (head_symb v1_pval));
[intros g2_eq_top_v1_pval | intros; trivial].
destruct (remove T.eq_bool (closed_term v1_pval) ll2) as [ll2' | ]; [idtac | trivial].
destruct (remove T.eq_bool (Term g2 ll2) l2) as [l2' | ]; [idtac | trivial].
split; [trivial | idtac].
destruct O as [ [[O | O] | O] | O]; [idtac | idtac | idtac | right; trivial].
simpl in O. subst x; right; left; simpl; rewrite v1_psp; trivial.
left; right; left; destruct l1 as [ | s1 [ | t1 l1]]; [contradiction | intuition | idtac].
simpl; apply list_permut_occurs_in_term_list with (s1 :: t1 :: l1); trivial; apply quick_permut.
left; right; right; trivial.
(* 2.1.2.2.2 s = Term f1 l1, t = Term f2 l2, f1 = f2, l1 = (Var v1) :: l1, 
                 v1 has NO value in sp, and no partial value in psp *)
unfold ac_elementary_solve_term_var_without_val_term; simpl.
intro pb'_in_lpb; pattern pb';
refine (prop_map12_without_repetition _ T.eq_bool_ok _ _ _ _ _ pb'_in_lpb); 
clear pb' w_pb' pb'_in_lpb wpb_in_solve_pb; intros t2 t2_in_l2.
destruct (remove T.eq_bool t2 l2) as [l2' | ]; [idtac | trivial].
unfold EDS.A, DOS.A in *;
destruct (le_gt_dec (length l2) (length l1 + 1)) as [L' | L'].
split; [trivial | idtac].
destruct O as [ [[O | O] | O] | [ O | O]].
right; right; simpl in O; subst x; simpl;
generalize (X.eq_bool_ok v1 v1); case (X.eq_bool v1 v1); [intros _; trivial | intro v1_diff_v1; apply False_rect; apply v1_diff_v1; reflexivity].
left; left; destruct l1 as [ | s1 [ | t1 l1]]; [contradiction | intuition | idtac].
simpl; apply list_permut_occurs_in_term_list with (s1 :: t1 :: l1); trivial; apply quick_permut.
left; right; trivial.
right; left; trivial.
right; right; simpl; case (X.eq_bool x v1); trivial.
split; split; [trivial | idtac | idtac | idtac].
destruct O as [ [[O | O] | O] | [ O | O ]].
right; right; simpl in O; subst x; simpl;
generalize (X.eq_bool_ok v1 v1); case (X.eq_bool v1 v1); [trivial | intro v1_diff_v1; apply False_rect; apply v1_diff_v1; reflexivity].
left; left; destruct l1 as [ | s1 [ | t1 l1]]; [contradiction | intuition | idtac].
simpl; apply list_permut_occurs_in_term_list with (s1 :: t1 :: l1); trivial; apply quick_permut.
left; right; trivial.
right; left; trivial.
right; right; simpl; case (X.eq_bool x v1); trivial.
simpl; intros [x_is_fresh | H]; [subst x; apply (fresh_var_spec _ O) | apply NE; trivial].
destruct l1 as [ | t1 l1]; destruct O as [ [[O | O] | O] | [ O | O ]].
simpl in O; subst x; simpl.
right; left; simpl;
generalize (X.eq_bool_ok v1 v1); case (X.eq_bool v1 v1); [trivial | intro v1_diff_v1; apply False_rect; apply v1_diff_v1; reflexivity].
contradiction.
left; right; simpl; trivial.
right; left; simpl; case (X.eq_bool x v1); trivial.
right; right; trivial.
right; left; simpl in O; subst x; simpl; 
generalize (X.eq_bool_ok v1 v1); case (X.eq_bool v1 v1); [trivial | intro v1_diff_v1; apply False_rect; apply v1_diff_v1; reflexivity].
left; left; simpl; 
apply list_permut_occurs_in_term_list with 
  (Var (fresh_var
           (mk_pb ex
              ((Term f1 (Var v1 :: t1 :: l1), Term f1 l2) :: usp) sp psp)) :: t1 :: l1);
[ apply quick_permut | right; trivial ].
left; right; trivial.
right; left; simpl; case (X.eq_bool x v1); trivial.
right; right; trivial.

(* 2.1.3 s = Term f1 l1, t = Term f2 l2, f1 = f2, l1 = (Term g1 ll1) :: l1 *)
unfold ac_elementary_solve_term_term_term;
intro pb'_in_lpb; pattern pb';
refine (prop_map_without_repetition _ T.eq_bool_ok _ _ _ _ _ pb'_in_lpb); 
clear pb' w_pb' pb'_in_lpb wpb_in_solve_pb; intros t2 t2_in_l2.
destruct t2 as [ | g2 ll2 ]; [trivial | idtac].
generalize (F.Symb.eq_bool_ok g1 g2); case (F.Symb.eq_bool g1 g2);  [intro g1_eq_g2 | intros _; trivial].
destruct (remove T.eq_bool (Term g2 ll2) l2) as [l2' | ]; [idtac | trivial].
split; [trivial | idtac].
destruct O as [ [[O | O] | O] | O]; [idtac | idtac | idtac | right; trivial].
left; left; trivial.
left; right; left; destruct l1 as [ | s1 [ | t1 l1]]; [contradiction | intuition | idtac].
simpl; apply list_permut_occurs_in_term_list with (s1 :: t1 :: l1); trivial; apply quick_permut.
left; right; right; trivial.

(* 2.2 arity f1 = C *)
destruct l1 as [ | s1 [ | t1 [ | u1 l1]]]; 
  [intros; contradiction | intros; contradiction | idtac | intros; contradiction].
destruct l2 as [ | s2 [ | t2 [ | u2 l2]]]; 
  [intros; contradiction | intros; contradiction | idtac | intros; contradiction].
intros [pb'_in_pb1 | [pb'_in_pb2 | pb'_in_nil]]; [subst pb' | subst pb' | contradiction].
(* 2.2.1 arity f1 = C, syntactic decomposition *)
split; trivial.
destruct O as [ [[O | [O | O]] | O] | O ]; [idtac | idtac | idtac | idtac | right; trivial].
left; left; trivial.
left; right; left; trivial.
contradiction.
left; right; right; trivial.
(* 2.2.2 arity f1 = C, commutative decomposition *)
split; trivial.
destruct O as [ [[O | [O | O]] | O] | O ]; [idtac | idtac | idtac | idtac | right; trivial].
left; left; trivial.
left; right; left; trivial.
contradiction.
left; right; right; trivial.

(* 2.3 arity f1 = Free n *)
generalize l1 l2 usp O; clear l1 l2 usp O w_pb wpb_in_solve_pb; 
induction l1 as [ | t1 l1]; destruct l2 as [ | t2 l2]; simpl.
intros usp O [pb'_eq_pb1 | pb'_in_nil]; [subst pb' | contradiction].
split; [trivial | idtac].
destruct O as [ [O  | O] | O ]; [idtac | idtac | right; trivial].
contradiction.
left; trivial.
contradiction.
contradiction.
intros usp O; simpl.
assert (O' : occurs_in_pb x 
                     (mk_pb ex ((Term f1 l1, Term f1 l2) :: (t1,t2) :: usp) sp psp)).
destruct O as [ [[O | O] | O] | O ]; [idtac | idtac | idtac | right; trivial ].
left; right; left; trivial.
left; left; trivial.
left; right; right; trivial.
assert (H:= IHl1 l2 ((t1,t2) :: usp) O').
destruct (fold_left2
      (fun (current_list_of_eqs : list (term * term)) (t3 t4 : term) =>
       (t3, t4) :: current_list_of_eqs) ((t1, t2) :: usp) l1 l2) as [ | ]; 
[idtac | intros; contradiction].
intros pb'_in; generalize (H pb'_in); trivial.
Qed.

Lemma matching_step1_is_sound :
  forall t1 t2 Wt1 Wt2 sigma pb, is_wf_sol pb sigma -> 
     In pb (wf_solve_loop 
        ((W (init_pb t1 t2) (well_formed_init_pb t1 t2 Wt1 Wt2)) :: nil)) ->
  apply_cf_subst sigma t1 = t2. 
Proof.
intros t1 t2 Wt1 Wt2 sigma pb Is_sol In_pb.
elim (wf_solve_loop_is_sound _ _ sigma In_pb Is_sol).
clear pb Is_sol In_pb; 
intros pb H; elim H; clear H;
intros In_pb Is_sol; elim In_pb; clear In_pb; intro In_pb.
subst pb; unfold init_pb in Is_sol; simpl in Is_sol;
unfold is_sol, is_rough_sol in Is_sol; elim Is_sol; clear Is_sol;
intros sigma' H; elim H; clear H; 
intros Is_sol eq_subst; elim Is_sol; clear Is_sol;
intros Is_sol _; simpl in Is_sol;
replace (apply_cf_subst sigma t1) with (apply_cf_subst sigma' t1).
apply Is_sol; left; trivial.
simpl existential_vars in eq_subst;
clear t2 Wt2 Wt1 Is_sol. 
apply sym_eq; pattern t1; apply term_rec3.
intro v; elim (eq_subst v); [ contradiction | trivial ].
intros.
simpl; replace (map (apply_cf_subst sigma') l) with
(map (apply_cf_subst sigma) l); trivial.
induction l; trivial.
simpl; rewrite (H a).
rewrite IHl; trivial.
intros; apply H; right; trivial.
left; trivial.
contradiction.
Qed.

Lemma matching_step2_is_sound :
  forall t1 t2 Wt1 Wt2 wpb, 
  match wpb with
  | W pb _ => 
    In wpb (wf_solve_loop ((W (init_pb t1 t2) 
                           (well_formed_init_pb t1 t2 Wt1 Wt2)) :: nil)) ->
    let sigma := extract_solution (solved_part pb) (partly_solved_part pb) in 
    apply_cf_subst sigma t1 = t2
    end. 
Proof.
intros t1 t2 Wt1 Wt2 [pb w_pb]; intros pb_in_loop;
refine (matching_step1_is_sound t1 t2 Wt1 Wt2 _ _ _ pb_in_loop).
simpl; unfold is_sol;
exists (extract_solution (solved_part pb) (partly_solved_part pb)); split;
[idtac | intro; right; trivial].
assert (usp_eq_nil := wf_solve_loop_end _ _ pb_in_loop); 
destruct pb as [ex usp sp psp]; simpl unsolved_part in usp_eq_nil; subst usp.
unfold is_rough_sol; split; [idtac | split].
(* 1 sol on unsolved_part *)
contradiction.
(* 2 sol on solved_part *)
elim w_pb; intros _ [ _ [ _ [nb_occ_v [well_sorted new_var_occ]]]].
simpl partly_solved_part in *; simpl solved_part in *.
intro v; generalize (extract_solution_in_partly_solved_part sp psp ex
                        nb_occ_v well_sorted new_var_occ v).
destruct (find X.eq_bool v psp) as [v_pval | ]; [idtac | trivial].
intro H; apply H; trivial.
(* 3 sol on partly_solved_part *)
elim w_pb; intros _ [ _ [ _ [nb_occ_v _]]].
simpl partly_solved_part in *; simpl solved_part in *.
intro v; generalize (extract_solution_in_solved_part sp psp v);
destruct (find X.eq_bool v sp) as [v_val | ]; [idtac | trivial].
intro H; rewrite (H v_val); trivial.
Qed.

Lemma matching_is_sound :
  forall t1 t2 Wt1 Wt2 sigma,
  In sigma (matching t1 t2 Wt1 Wt2) -> apply_cf_subst sigma t1 = t2.
Proof.
intros t1 t2 Wt1 Wt2 sigma; unfold matching.
intro In_wpb.
cut (exists wpb, In wpb (wf_solve_loop ((W (init_pb t1 t2) 
                           (well_formed_init_pb t1 t2 Wt1 Wt2)) :: nil)) /\
    match wpb with
    | W pb _ => 
      sigma = clean_sol (existential_vars pb)
                    (extract_solution (solved_part pb) (partly_solved_part pb))
    end).
clear In_wpb; intro In_wpb; elim In_wpb; clear In_wpb;
intros wpb In_wpb; elim In_wpb; clear In_wpb;
intros In_wpb Is_sol;
generalize (matching_step2_is_sound t1 t2 Wt1 Wt2 wpb); destruct wpb;
intro H; generalize (H In_wpb); clear H; intro H;
rewrite Is_sol; rewrite <- H;
clear Is_sol H; 
generalize (extract_solution (solved_part pb) (partly_solved_part pb));
cut (forall v, occurs_in_term v t1 -> ~ In v (existential_vars pb)).
generalize (existential_vars pb); clear sigma pb w In_wpb;
intros l; pattern t1; apply term_rec3.
intros v not_occurs sigma; generalize v not_occurs; clear v not_occurs;
induction sigma.
unfold clean_sol; simpl; trivial.
intros v not_occurs; destruct a; simpl.
generalize (X.eq_bool_ok v a); case (X.eq_bool v a); [intro v_eq_a | intro v_diff_a].
subst v; assert (a_not_in_l := not_occurs a (eq_refl _)).
generalize (mem_bool_ok _ _ X.eq_bool_ok a l); case (mem_bool X.eq_bool a l).
intro a_mem_l; absurd (In a l); trivial.
apply (mem_impl_in (@eq variable)); trivial.
intros _; simpl; generalize (X.eq_bool_ok a a); case (X.eq_bool a a); [intros _; trivial | intro a_diff_a; apply False_rect; apply a_diff_a; reflexivity].
generalize (mem_bool_ok _ _ X.eq_bool_ok a l); case (mem_bool X.eq_bool a l).
intro a_mem_l; simpl in IHsigma; apply IHsigma; trivial.
intro a_not_mem_l; simpl; generalize (X.eq_bool_ok v a); case (X.eq_bool v a); [intro v_eq_a | intros _].
absurd (v=a); trivial.
simpl in IHsigma; apply IHsigma; trivial.
intros f l0 IH not_occurs sigma;
cut (map (apply_cf_subst (clean_sol l sigma)) l0 = map (apply_cf_subst sigma) l0).
intro H; simpl; rewrite H; trivial.
induction l0.
trivial.
simpl map; rewrite (IH a).
rewrite (IHl0); trivial.
intros; apply IH; trivial; right; trivial.
intros; apply not_occurs; right; trivial.
left; trivial.
intros; apply not_occurs; trivial; left; trivial.
intros v O; 
cut (let lpb:= (W (init_pb t1 t2) (well_formed_init_pb t1 t2 Wt1 Wt2) :: nil) in
forall wpb, In wpb lpb ->
match wpb with
  | W pb' _ => ~ In v (existential_vars pb') /\ occurs_in_pb v pb'
  end).
intro H; elim (variable_preservation v _ H (W pb w) In_wpb); trivial.
intros lpb wpb In_wpb'; elim In_wpb'; clear In_wpb'; intro In_wpb'.
subst wpb; unfold init_pb; simpl; split.
unfold not; trivial.
left; left; trivial.
contradiction.
generalize (wf_solve_loop
                 (W (init_pb t1 t2) (well_formed_init_pb t1 t2 Wt1 Wt2)
                  :: nil)) In_wpb; clear In_wpb; induction l;
[contradiction 
| simpl map; intro In_wpb; elim In_wpb; clear In_wpb; intro In_wpb;
[destruct a; exists (W pb w); split; trivial; [ left | apply sym_eq ]; trivial
|elim (IHl In_wpb); clear In_wpb; intros wpb H; elim H; clear H;
intros In_wpb H; exists wpb; split; trivial; right; trivial]].
Qed.

Lemma matching_step1_is_complete :
  forall t1 t2 Wt1 Wt2 sigma, well_formed_cf_subst sigma ->
  apply_cf_subst sigma t1 = t2 ->
  (exists pb, is_wf_wf_sol pb sigma /\ In pb (wf_solve_loop 
        ((W (init_pb t1 t2) (well_formed_init_pb t1 t2 Wt1 Wt2)) :: nil))).
Proof.  
intros t1 t2 Wt1 Wt2 sigma Wsigma Is_sol.
set (pb:=(W (init_pb t1 t2) (well_formed_init_pb t1 t2 Wt1 Wt2))).
elim (wf_solve_loop_is_complete (pb :: nil) pb) with sigma.
intros pb0 H; elim H; clear H; intros In_pb0 Is_sol0; 
exists pb0; split; trivial.
left; trivial.
unfold is_wf_wf_sol, is_well_formed_sol, is_rough_sol.
simpl; exists sigma; intuition.
injection H0; intros; subst t0 t3; trivial.
Qed.

Lemma matching_step2_is_complete :
  forall t1 t2 Wt1 Wt2 sigma, well_formed_cf_subst sigma ->
  apply_cf_subst sigma t1 = t2 ->
  (exists wpb, In wpb (wf_solve_loop 
        ((W (init_pb t1 t2) (well_formed_init_pb t1 t2 Wt1 Wt2)) :: nil)) /\
    match wpb with
    | W pb _ => forall v, occurs_in_term v t1 ->
         apply_cf_subst sigma  (Var v) = 
         apply_cf_subst 
           (extract_solution (solved_part pb) (partly_solved_part pb))
           (Var v)
    end).
Proof.
intros t1 t2 Wt1 Wt2 sigma Wsigma Is_sol;
elim (matching_step1_is_complete t1 t2 Wt1 Wt2 sigma Wsigma Is_sol).
clear Is_sol;
intros [pb w_pb] [Is_sol pb_in_loop].
destruct Is_sol as [sigma' [[Is_sol'_usp [Is_sol'_psp Is_sol'_sp]] [sigma_eq_sigma' Wsigma']]].
exists (W pb w_pb); split; [trivial | idtac].
intros v O.
assert (H : let lpb:= (W (init_pb t1 t2) (well_formed_init_pb t1 t2 Wt1 Wt2) :: nil) in
                  forall wpb, In wpb lpb ->
                  match wpb with
                  | W pb' _ => ~ In v (existential_vars pb') /\ occurs_in_pb v pb'
                  end).
intros lpb wpb In_wpb'; elim In_wpb'; clear In_wpb'; intro In_wpb'.
subst wpb; split; simpl.
unfold not; trivial.
unfold init_pb; left; simpl; left; trivial.
contradiction.

elim (variable_preservation v _ H (W pb w_pb) pb_in_loop); clear H;
intros E' O'.
assert (usp_eq_nil := wf_solve_loop_end _ _ pb_in_loop); 
destruct pb as [ex usp sp psp]; simpl unsolved_part in *; subst usp.
clear Is_sol'_usp; 
clear pb_in_loop; elim w_pb;
intros _ w; elim w; clear w.
intros _ w; elim w; clear w.
intros _ w; elim w; clear w.
intros nb_occ_v w; elim w; clear w.
intros well_sorted new_var_occ.
simpl partly_solved_part in *; simpl solved_part in *;
simpl existential_vars in *.
elim (sigma_eq_sigma' v); intro E_v.
absurd (In v ex); trivial.
rewrite E_v; clear sigma Wsigma sigma_eq_sigma' E_v O.
elim O'; clear O'; intro O'.
contradiction.
elim O'; clear O'; intro O'; simpl in O'.
generalize 
sp Is_sol'_psp Is_sol'_sp nb_occ_v 
well_sorted new_var_occ O' (extract_solution_in_partly_solved_part sp 
psp ex nb_occ_v well_sorted new_var_occ);
clear sp w_pb Is_sol'_psp Is_sol'_sp nb_occ_v 
well_sorted new_var_occ O' E';
induction psp.
contradiction.
intros sp Is_sol'_psp Is_sol'_sp nb_occ_v
well_sorted new_var_occ;
destruct a; generalize (Is_sol'_psp v); simpl find.
generalize (X.eq_bool_ok v a); case (X.eq_bool v a); [intros v_eq_a H _; subst a | intro v_diff_a]. 
rewrite H;
rewrite extract_solution_unfold;
rewrite (extract_solution_in_solved_part
((v,
        (Term (head_symb p)
           (quicksort
              (flatten (head_symb p)
                 (apply_cf_subst sp (Var (new_var p))
                  :: closed_term p :: nil))))) :: sp)
psp v 
(Term (head_symb p)
           (quicksort
              (flatten (head_symb p)
                 (apply_cf_subst sp (Var (new_var p))
                  :: closed_term p :: nil))))).
intros _; 
apply (f_equal (fun t => Term (head_symb p)
  (quicksort
     (flatten (head_symb p)
        (t :: closed_term p :: nil)))));
generalize 
(new_var_occ_in_solved_part 
  (mk_pb ex nil sp ((v,p) :: psp))
 (eq_refl _) well_sorted new_var_occ)
(Is_sol'_sp (new_var p)); simpl.
destruct (find X.eq_bool (new_var p) sp); trivial; contradiction.
generalize (nb_occ_v v); simpl.
generalize (X.eq_bool_ok v v); case (X.eq_bool v v); [intros _ | intro v_diff_v; apply False_rect; apply v_diff_v; reflexivity].
rewrite Nat.add_comm; simpl; rewrite Nat.add_comm; trivial.
simpl find;
generalize (X.eq_bool_ok v v); case (X.eq_bool v v); [intros _; trivial | intro v_diff_v; apply False_rect; apply v_diff_v; reflexivity].

intros; rewrite extract_solution_unfold.
apply IHpsp; trivial.
intros; generalize (Is_sol'_psp v0) (nb_occ_v v0);
simpl nb_occ; simpl find.
generalize (X.eq_bool_ok v0 a); case (X.eq_bool v0 a); [intro v0_eq_a; subst v0 | intro v0_diff_a].
generalize (some_nb_occ_Sn X.eq_bool a psp);
destruct (find X.eq_bool a psp); trivial.
intro H1; generalize (H1 p0 (eq_refl _)); clear H1; intro H1;
destruct (nb_occ X.eq_bool a psp).
absurd (1 <= 0); auto with arith.
intros _ H2; rewrite Nat.add_comm in H2; simpl in H2;
absurd (S(S(n + nb_occ X.eq_bool a sp)) <= 1); auto with arith.
trivial.
intro v1; generalize (Is_sol'_psp v1);
pattern 
(apply_cf_subst sp (Var (new_var p)) :: closed_term p :: nil); unfold find.
generalize (X.eq_bool_ok v1 a); case (X.eq_bool v1 a); [intro v1_eq_a; subst v1 | intro v1_diff_a].
intro H1; rewrite H1; 
apply (f_equal (fun t => 
Term (head_symb p)
  (quicksort
     (flatten (head_symb p)
        (t :: closed_term p :: nil))))).
generalize 
(new_var_occ_in_solved_part 
  (mk_pb ex nil sp ((a, p) :: psp))
  (eq_refl _) well_sorted new_var_occ); intro H4; simpl in H4.
generalize (Is_sol'_sp (new_var p)).
simpl; destruct (find X.eq_bool (new_var p) sp); trivial; contradiction.
intros _; apply Is_sol'_sp.
intro v1; generalize (nb_occ_v v1); simpl.
generalize (X.eq_bool_ok v1 a); case (X.eq_bool v1 a); [intro v1_eq_a; subst v1 | intro v1_diff_a; trivial].
rewrite Nat.add_comm; simpl; rewrite Nat.add_comm; trivial.
elim well_sorted; intros _ H1; elim H1; trivial.
intros v1; generalize (nb_occ_v v1) (new_var_occ v1); simpl find;
intro H'; simpl in H'; generalize H'; clear H'.
generalize (X.eq_bool_ok v1 a); case (X.eq_bool v1 a); [intro v1_eq_a; subst v1 | intro v1_diff_a].
intros H'; generalize (some_nb_occ_Sn X.eq_bool a psp).
destruct (find X.eq_bool a psp).
intro H1; generalize (H1 p0 (eq_refl _)); clear H1; intro H1.
destruct (nb_occ X.eq_bool a psp).
absurd (1 <= 0); auto with arith.
rewrite Nat.add_comm in H'; simpl in H';
absurd (S(S(n + nb_occ X.eq_bool a sp)) <= 1); auto with arith.
intros; discriminate.
intros H' H1 p0 H2; elim (H1 p0 H2); clear H1; intro H1.
contradiction.
revert H1; simpl.
generalize (X.eq_bool_ok (new_var p0) a); case (X.eq_bool (new_var p0) a); [intro new_var_p0_eq_a | intro new_var_p0_diff_a].
intros _; right; right; simpl.
generalize (X.eq_bool_ok (new_var p0) a); case (X.eq_bool (new_var p0) a); [intros _; trivial | intro new_var_p0_diff_a].
absurd (new_var p0 = a); assumption.
case_eq (find X.eq_bool (new_var p0) psp).
intros p1 F _; right; left; simpl; rewrite F; trivial.
intros F; case_eq (find X.eq_bool (new_var p0) sp).
intros t F' _; right; right; simpl.
generalize (X.eq_bool_ok (new_var p0) a); case (X.eq_bool (new_var p0) a); [intros new_var_p0_eq_a | intros _].
exact I.
rewrite F'; exact I.
intros F' [Abs | Abs]; contradiction.

intros v1 p1 F1.
refine (extract_solution_in_partly_solved_part _ _ ex _ _ _ _ _ F1).
intros v2; generalize (nb_occ_v v2); simpl.
generalize (X.eq_bool_ok v2 a); case (X.eq_bool v2 a); [intro v2_eq_a; subst v2 | intro v2_diff_a; trivial].
rewrite Nat.add_comm; simpl; rewrite Nat.add_comm; trivial.
elim well_sorted; intros _ H2; elim H2; trivial.
intros v2; generalize (nb_occ_v v2) (new_var_occ v2); simpl find;
intro H'; simpl in H'; generalize H'; clear H'.
generalize (X.eq_bool_ok v2 a); case (X.eq_bool v2 a); [intro v2_eq_a; subst v2 | intro v2_diff_a].
intros H'; generalize (some_nb_occ_Sn X.eq_bool a psp).
destruct (find X.eq_bool a psp).
intro H1; generalize (H1 p0 (eq_refl _)); clear H1; intro H1.
destruct (nb_occ X.eq_bool a psp).
absurd (1 <= 0); auto with arith.
rewrite Nat.add_comm in H'; simpl in H';
absurd (S(S(n + nb_occ X.eq_bool a sp)) <= 1); auto with arith.
intros; discriminate.
intros H' H1 p0 H2; elim (H1 p0 H2); clear H1; intro H1.
contradiction.
elim H1; clear H1; simpl find.
generalize (X.eq_bool_ok (new_var p0) a); case (X.eq_bool (new_var p0) a); [intro new_var_p0_eq_a | intro new_var_p0_diff_a].
right; right; simpl.
generalize (X.eq_bool_ok (new_var p0) a); case (X.eq_bool (new_var p0) a); [intros _; trivial | intro new_var_p0_diff_a].
absurd (new_var p0 = a); assumption.
right; left; simpl; trivial.
right; right; simpl; case (X.eq_bool (new_var p0) a); trivial.

generalize (Is_sol'_sp v) 
(extract_solution_in_solved_part sp psp v); 
destruct (find X.eq_bool v sp).
intros H0 H; generalize (H t (nb_occ_v v) (eq_refl _)); clear H;
intro H; rewrite H; rewrite H0; trivial.
contradiction.

Qed.

Lemma matching_is_complete :
  forall t1 t2 Wt1 Wt2 sigma, well_formed_cf_subst sigma ->
  apply_cf_subst sigma t1 = t2 ->
  (exists sigma', In sigma' (matching t1 t2 Wt1 Wt2) /\
             (forall v, occurs_in_term v t1 ->
                  apply_cf_subst sigma  (Var v) = apply_cf_subst sigma' (Var v))).
Proof.
intros t1 t2 Wt1 Wt2 sigma W_sigma Is_sol;
elim (matching_step2_is_complete t1 t2 Wt1 Wt2 sigma W_sigma Is_sol).
intros wpb H; elim H; clear H; intros In_wpb Is_sol';
destruct wpb.
unfold matching.
exists (clean_sol (existential_vars pb)
              (extract_solution (solved_part pb) (partly_solved_part pb))); split.
generalize In_wpb; clear In_wpb;
induction (wf_solve_loop
        (W (init_pb t1 t2) (well_formed_init_pb t1 t2 Wt1 Wt2) :: nil)).
contradiction.
intro In_wpb; elim In_wpb; clear In_wpb; intro In_wpb.
subst a; left; trivial.
right; apply IHl; trivial.
intros v O;
cut (let lpb:= (W (init_pb t1 t2) (well_formed_init_pb t1 t2 Wt1 Wt2) :: nil) in
forall wpb, In wpb lpb ->
match wpb with
  | W pb' _ => ~ In v (existential_vars pb') /\ occurs_in_pb v pb'
  end).
intro H; elim (variable_preservation v _ H (W pb w) In_wpb); clear H;
intros E' O'.
rewrite Is_sol'; trivial.
generalize (extract_solution (solved_part pb) (partly_solved_part pb)).
clear t1 t2 Wt1 Wt2 sigma W_sigma Is_sol w In_wpb Is_sol' O O';
intro sigma; induction sigma.
simpl; trivial.
destruct a; simpl.
generalize (mem_bool_ok _ _ X.eq_bool_ok a (existential_vars pb)); case (mem_bool X.eq_bool a (existential_vars pb)).
intro a_mem_ex;
generalize (X.eq_bool_ok v a); case (X.eq_bool v a); [intro v_eq_a; subst a | intro v_diff_a].
absurd (In v (existential_vars pb)); trivial.
apply mem_impl_in with (@eq _).
intros; assumption.
assumption.
simpl in IHsigma; rewrite IHsigma; trivial.
intro a_not_mem_ex; simpl;
generalize (X.eq_bool_ok v a); case (X.eq_bool v a); [intro v_eq_a; subst a; trivial | intro v_diff_a].
simpl in IHsigma; rewrite IHsigma; trivial.

intros lpb wpb In_wpb'; elim In_wpb'; clear In_wpb'; intro In_wpb'.
subst wpb; split; simpl.
unfold not; trivial.
unfold init_pb; left; simpl; left; trivial.
contradiction.
Qed.

End Make.
