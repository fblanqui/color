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


From Stdlib Require Import Arith List.
From CoLoR Require Import more_list list_sort term_spec ac cf_eq_ac.

Module Type S.

Declare Module Import Cf_eq_ac : cf_eq_ac.S.

Import Cf_eq_ac.Ac Sort EqTh EqTh.T F LPermut.

Record partly_solved_term : Type :=
  mk_pst 
  {
    head_symb : symbol;
    new_var : variable;
    closed_term : term
  }.

Record matching_problem : Type :=
  mk_pb 
  {
    existential_vars : list variable;
    unsolved_part : list (term * term);
    solved_part : substitution;
    partly_solved_part : list (variable * partly_solved_term)
  }.

Definition is_rough_sol pb sigma :=
 (forall t1 t2, In (t1,t2) pb.(unsolved_part) -> apply_cf_subst sigma t1 = t2) /\
 (forall v, match find X.eq_bool v pb.(partly_solved_part) with
            | None => True
            | Some pst =>
              let l := (apply_cf_subst sigma (Var pst.(new_var))) :: pst.(closed_term) :: nil in
              apply_cf_subst sigma (Var v) =
             Term pst.(head_symb) (quicksort (flatten pst.(head_symb) l))
             end) /\
 (forall v, match find X.eq_bool v pb.(solved_part) with
            | None => True
            | Some t => apply_cf_subst sigma (Var v) = t
            end).

Definition is_sol pb sigma :=
  exists sigma', is_rough_sol pb sigma' /\
                  (forall v, In v (existential_vars pb) \/ 
                             apply_cf_subst sigma (Var v) = apply_cf_subst sigma' (Var v)).

Fixpoint occurs_in_term (v : variable) (t : term) {struct t} : Prop :=
  match t with
  | Var v' => v=v'
  | Term _ l => 
      let occurs_in_term_list :=
       (fix occurs_in_term_list v (l : list _) {struct l} : Prop :=
        match l with
        | nil => False
        | h :: tl => (occurs_in_term v h) \/ (occurs_in_term_list v tl)
        end) in
        occurs_in_term_list v l
    end.

Fixpoint occurs_in_term_list (v : variable) (l : list term) {struct l} : Prop :=
  match l with
  | nil => False
  | cons h tl => (occurs_in_term v h) \/ (occurs_in_term_list v tl)
  end.

Definition occurs_in_pb v pb :=
 (occurs_in_term_list v (map (fun p => match p with | (t1,t2) => t1 end) pb.(unsolved_part))) \/
 (match find X.eq_bool v pb.(partly_solved_part) with
   | None => False | Some _ => True end) \/
 (match find X.eq_bool v pb.(solved_part) with
   | None => False | Some _ => True end).

Parameter fresh_var : matching_problem -> variable.
Parameter fresh_var_spec : forall pb, ~(occurs_in_pb (fresh_var pb) pb).

Definition ac_elementary_solve_term_term_term 
pb f g lg list_of_terms l' list_of_equations : list matching_problem :=
(* t1 = Term f (cons (Term g lg) list_of_terms as l); t2 = Term _ l' *) 
  map_without_repetition T.eq_bool
  (fun t =>
    match t with
    | Term h _ =>
      if F.Symb.eq_bool g h
      then 
         match remove T.eq_bool t l' with
           | None => None
           | Some rmv => 
              let t1' := build f list_of_terms in
              let t2' := build f rmv in
                Some
                  (mk_pb  (existential_vars pb)
                         (cons ((Term g lg),t) (cons (t1',t2') list_of_equations))
                         (solved_part pb)
                         (partly_solved_part pb))
          end 
       else None
    | Var _ => None
    end) 
    l'.

Definition ac_elementary_solve_term_var_with_val_term 
pb f x_val list_of_terms l' list_of_equations : list matching_problem :=
(* t1 = Term f (cons (Var x) list_of_terms as l); t2 = Term _ l' *)
  match remove T.eq_bool x_val l' with
  | None => 
     match x_val with
     | Var _ => nil
     | Term g ll =>
         if F.Symb.eq_bool f g
         then 
            match remove_list ll l' with
            | Some rmv =>
               if le_gt_dec (length list_of_terms) (length rmv)
               then 
                   let t1' := build f list_of_terms in
                   let t2' := build f rmv in
                   let new_pb := 
                   mk_pb (existential_vars pb)
                   (cons (t1',t2') list_of_equations)
                   (solved_part pb)
                   (partly_solved_part pb) in
                   cons new_pb nil
                 else nil
            | None => nil
            end
         else nil
     end
  | Some rmv =>
    let t1' := build f list_of_terms in
    let t2' := build f rmv in
    let new_pb := 
      mk_pb (existential_vars pb)
      ((t1',t2') :: list_of_equations)
            (solved_part pb)
            (partly_solved_part pb) in
      new_pb :: nil
  end.

Definition ac_elementary_solve_term_var_with_part_val_term
pb f x_part_val list_of_terms l' list_of_equations : list matching_problem :=
(* t1 = Term f (cons (Var x) list_of_terms as l); t2 = Term _ l' *)
  if (F.Symb.eq_bool f (head_symb x_part_val))
  then
      match remove T.eq_bool (closed_term x_part_val) l' with
      | None => nil
      | Some rmv =>
        let t1' := build f (cons (Var (new_var x_part_val)) list_of_terms) in
        let t2' := build f rmv in
        let new_pb := 
          mk_pb  (existential_vars pb)
                ((t1',t2') :: list_of_equations)
                (solved_part pb)
                (partly_solved_part pb) in
         new_pb :: nil  
     end
  else
      map_without_repetition T.eq_bool
       (fun t =>
          match t with
          | Term h l''' =>
              if F.Symb.eq_bool h (head_symb x_part_val)
              then
                  match remove T.eq_bool (closed_term x_part_val) l''' with
                  | None => None
                  | Some rmv =>
                    match remove T.eq_bool t l' with
                    | None => None
                    | Some rmv2 =>
                      let y := new_var x_part_val in
                      let y_val := build h rmv in
                      let t1' := build f list_of_terms in
                      let t2' := build f rmv2 in
                      let new_pb :=
                        mk_pb (existential_vars pb)
                              ((Var y, y_val) :: (t1',t2') :: list_of_equations)
                              (solved_part pb)
                              (partly_solved_part pb) in
                      Some new_pb
                    end
                  end
              else None
           | Var _ => None
           end)
         l'.

Definition ac_elementary_solve_term_var_without_val_term 
pb f x list_of_terms l' list_of_equations : list matching_problem := 
(* t1 = Term f ((Var x) :: list_of_terms as l); t2 = Term _ l' *)
  map12_without_repetition T.eq_bool
  (fun t => 
    match remove T.eq_bool t l' with
    | None => (None, None)
    | Some rmv =>
      let l'_without_t := rmv in
      let t1' := build f list_of_terms in
      let t2' := build f l'_without_t in
      let new_pb :=
        mk_pb (existential_vars pb)
              ((t1', t2') :: list_of_equations)
              ((x, t) :: (solved_part pb))
              (partly_solved_part pb) in 
       if le_gt_dec (length l') ((length list_of_terms) + 1)
       then (Some new_pb, None)
       else 
         let y := fresh_var pb in
         let t1'' := build f (Var y :: list_of_terms) in
         let new_pb' := 
           mk_pb (y :: existential_vars pb)
                 ((t1'', t2') :: list_of_equations)
                 (solved_part pb)
                 ((x, mk_pst f y t) :: (partly_solved_part pb)) in
          (Some new_pb, Some new_pb')
    end)
    l'.

Definition ac_elementary_solve pb t1 t2 list_of_equations :=
  match t1, t2 with
  | (Term f (s :: list_of_terms as l)), (Term _ l') =>
    match s with
    | Term g lg => 
        ac_elementary_solve_term_term_term 
          pb f g lg list_of_terms l' list_of_equations
    | Var x =>
      match find X.eq_bool x (solved_part pb) with
      | Some x_val => 
         ac_elementary_solve_term_var_with_val_term 
           pb f x_val list_of_terms l' list_of_equations
      | None =>
        match find X.eq_bool x (partly_solved_part pb) with
        | Some x_part_val => 
           ac_elementary_solve_term_var_with_part_val_term
             pb f x_part_val list_of_terms l' list_of_equations
        | None => 
           ac_elementary_solve_term_var_without_val_term 
             pb f x list_of_terms l' list_of_equations
        end
      end
    end
  | (Term _ nil), (Term _ _) =>
     let new_pb := 
       mk_pb (existential_vars pb)
             list_of_equations
             (solved_part pb)
             (partly_solved_part pb) in
       new_pb :: nil
  | _, _ => nil
  end.

Definition solve pb : list matching_problem :=
  match unsolved_part pb with
  | (tt1,tt2 as e) :: list_of_equations =>
    match tt1, tt2 with
    | Var x, _ =>
      match find X.eq_bool x (solved_part pb) with
      | Some x_val => 
        if T.eq_bool x_val tt2
        then 
          let new_pb := 
            mk_pb (existential_vars pb) 
            list_of_equations (solved_part pb) (partly_solved_part pb) in
          new_pb :: nil
        else nil
      | None =>
        match find X.eq_bool x (partly_solved_part pb) with
        | Some x_part_val =>
          match tt2 with
          | Var _ => nil
          | Term f2 l2 =>
            if F.Symb.eq_bool (head_symb x_part_val) f2
            then 
              let y := new_var x_part_val in
              match remove T.eq_bool (closed_term x_part_val) l2 with
              | Some rmv => 
                let y_val := build f2 rmv in
                let new_pb := 
                  mk_pb (existential_vars pb)
                        ((Var y, y_val) :: list_of_equations)
                        (solved_part pb) (partly_solved_part pb) in
                  new_pb :: nil
              | None => nil
              end
            else nil
         end
       | None =>
           let new_pb :=
             mk_pb (existential_vars pb)
             list_of_equations ((x, tt2) :: (solved_part pb)) (partly_solved_part pb) in
           new_pb :: nil
       end
     end
    | Term f1 l1, Term f2 l2 =>
        if F.Symb.eq_bool f1 f2 
        then 
            match arity f1 with
            | Free _ => 
              match fold_left2
                (fun current_list_of_eqs t1 t2 => (t1,t2) :: current_list_of_eqs)
                list_of_equations l1 l2 with
              | Some new_list_of_equations =>
                let new_pb :=
                  mk_pb (existential_vars pb)
                  new_list_of_equations (solved_part pb) (partly_solved_part pb) in
                new_pb :: nil
              | None => nil
              end
            | AC =>
              if le_gt_dec (length l1) (length l2)
              then ac_elementary_solve pb tt1 tt2 list_of_equations
              else nil
            | C =>
              match l1, l2 with
              | (s1 :: s2 :: nil), (t1 :: t2 :: nil) =>
                let new_pb1 := 
                  mk_pb (existential_vars pb)
                  ((s1,t1) :: (s2,t2) :: list_of_equations) 
                        (solved_part pb) (partly_solved_part pb) in
               let new_pb2 := 
                  mk_pb (existential_vars pb)
                  ((s1,t2) :: (s2,t1) :: list_of_equations) 
                        (solved_part pb) (partly_solved_part pb) in
                 new_pb1 :: new_pb2 :: nil
                | _, _ => nil
              end
            end
        else nil
    | _, _ => nil
    end
  | nil => nil
end.

Fixpoint well_sorted_partly_solved_part (l :  list (variable * partly_solved_term)) : Prop :=
 match l with
 | nil => True
 | (v,p) :: tl => 
    v <> new_var p /\
    (forall v', 1 <= nb_occ X.eq_bool v' tl -> v' <> new_var p) /\
    well_sorted_partly_solved_part tl
end.

Definition well_formed_pb pb :=
(forall t1 t2, In (t1,t2) pb.(unsolved_part) ->
                   well_formed_cf t1 /\ well_formed_cf t2) /\
(forall v, match (find X.eq_bool v pb.(solved_part)) with
  | None => True
  | Some t => well_formed_cf t 
  end) /\
(forall v, match (find X.eq_bool v pb.(partly_solved_part)) with
  | None => True
  | Some pst => 
      match arity pst.(head_symb) with
      | AC => well_formed_cf pst.(closed_term) /\
              match pst.(closed_term) with
              | Var _ => True
              | Term f _ => pst.(head_symb)<>f
              end
      | _ => False
      end
  end) /\
(forall v, 
  nb_occ X.eq_bool v (solved_part pb) + nb_occ X.eq_bool v (partly_solved_part pb) <= 1) /\
well_sorted_partly_solved_part (partly_solved_part pb) /\
(forall v p,
  find X.eq_bool v (partly_solved_part pb) = Some p -> occurs_in_pb (new_var p) pb).

Definition is_well_formed_sol pb sigma :=
 (exists sigma',  is_rough_sol pb sigma' /\
                  (forall v, In v (existential_vars pb) \/
                      apply_cf_subst sigma (Var v) = apply_cf_subst sigma' (Var v)) /\
                         (well_formed_cf_subst sigma')).

Parameter list_permut_occurs_in_term_list :
  forall v l1 l2, permut l1 l2 -> occurs_in_term_list v l1 ->
  occurs_in_term_list v l2.

Parameter add_new_var_to_subst :
  forall t1 v t2 sigma, ~occurs_in_term v t1 ->
  	  apply_cf_subst sigma t1 = apply_cf_subst ((v,t2) ::  sigma) t1.

Parameter add_new_var_to_rough_sol :
  forall pb sigma t, well_formed_pb pb -> is_rough_sol pb sigma ->
  (is_rough_sol pb ((fresh_var pb, t) :: sigma)).

End S.

Module Make (Cf_eq_ac1 : cf_eq_ac.S) : S with Module Cf_eq_ac := Cf_eq_ac1.

Module Cf_eq_ac := Cf_eq_ac1.
Import Cf_eq_ac1 Ac EqTh T F X Sort LPermut.

Record partly_solved_term : Type :=
  mk_pst 
  {
    head_symb : symbol;
    new_var : variable;
    closed_term : term
  }.

Record matching_problem : Type :=
  mk_pb 
  {
    existential_vars : list variable;
    unsolved_part : list (term * term);
    solved_part : substitution;
    partly_solved_part : list (variable * partly_solved_term)
  }.


Definition is_rough_sol pb sigma :=
 (forall t1 t2, In (t1,t2) pb.(unsolved_part) -> apply_cf_subst sigma t1 = t2) /\
 (forall v, match find X.eq_bool v pb.(partly_solved_part) with
            | None => True
            | Some pst =>
              let l := (apply_cf_subst sigma (Var pst.(new_var))) :: pst.(closed_term) :: nil in
              apply_cf_subst sigma (Var v) =
             Term pst.(head_symb) (quicksort (flatten pst.(head_symb) l))
             end) /\
 (forall v, match find X.eq_bool v pb.(solved_part) with
            | None => True
            | Some t => apply_cf_subst sigma (Var v) = t
            end).

Definition is_sol pb sigma :=
  exists sigma', is_rough_sol pb sigma' /\
                  (forall v, In v (existential_vars pb) \/ 
                             apply_cf_subst sigma (Var v) = apply_cf_subst sigma' (Var v)).


Fixpoint occurs_in_term (v : variable) (t : term) {struct t} : Prop :=
  match t with
  | Var v' => v=v'
  | Term _ l => 
      let occurs_in_term_list :=
       (fix occurs_in_term_list v (l : list _) {struct l} : Prop :=
        match l with
        | nil => False
        | h :: tl => (occurs_in_term v h) \/ (occurs_in_term_list v tl)
        end) in
        occurs_in_term_list v l
    end.

Fixpoint occurs_in_term_list (v : variable) (l : list term) {struct l} : Prop :=
  match l with
  | nil => False
  | cons h tl => (occurs_in_term v h) \/ (occurs_in_term_list v tl)
  end.

Definition occurs_in_pb v pb :=
 (occurs_in_term_list v (map (fun p => match p with | (t1,t2) => t1 end) pb.(unsolved_part))) \/
 (match find X.eq_bool v pb.(partly_solved_part) with
   | None => False | Some _ => True end) \/
 (match find X.eq_bool v pb.(solved_part) with
   | None => False | Some _ => True end).

Parameter fresh_var : matching_problem -> variable.
Parameter fresh_var_spec : forall pb, ~(occurs_in_pb (fresh_var pb) pb).

Definition ac_elementary_solve_term_term_term 
pb f g lg list_of_terms l' list_of_equations : list matching_problem :=
(* t1 = Term f (cons (Term g lg) list_of_terms as l); t2 = Term _ l' *) 
  map_without_repetition T.eq_bool
  (fun t =>
    match t with
    | Term h _ =>
      if F.Symb.eq_bool g h
      then 
         match remove T.eq_bool t l' with
           | None => None
           | Some rmv => 
              let t1' := build f list_of_terms in
              let t2' := build f rmv in
                Some
                  (mk_pb  (existential_vars pb)
                         (cons ((Term g lg),t) (cons (t1',t2') list_of_equations))
                         (solved_part pb)
                         (partly_solved_part pb))
          end 
       else None
    | Var _ => None
    end) 
    l'.

Definition ac_elementary_solve_term_var_with_val_term 
pb f x_val list_of_terms l' list_of_equations : list matching_problem :=
(* t1 = Term f (cons (Var x) list_of_terms as l); t2 = Term _ l' *)
  match remove T.eq_bool x_val l' with
  | None => 
     match x_val with
     | Var _ => nil
     | Term g ll =>
         if F.Symb.eq_bool f g
         then 
            match remove_list ll l' with
            | Some rmv =>
               if le_gt_dec (length list_of_terms) (length rmv)
               then 
                   let t1' := build f list_of_terms in
                   let t2' := build f rmv in
                   let new_pb := 
                   mk_pb (existential_vars pb)
                   (cons (t1',t2') list_of_equations)
                   (solved_part pb)
                   (partly_solved_part pb) in
                   cons new_pb nil
                 else nil
            | None => nil
            end
         else nil
     end
  | Some rmv =>
    let t1' := build f list_of_terms in
    let t2' := build f rmv in
    let new_pb := 
      mk_pb (existential_vars pb)
      ((t1',t2') :: list_of_equations)
            (solved_part pb)
            (partly_solved_part pb) in
      new_pb :: nil
  end.

Definition ac_elementary_solve_term_var_with_part_val_term
pb f x_part_val list_of_terms l' list_of_equations : list matching_problem :=
(* t1 = Term f (cons (Var x) list_of_terms as l); t2 = Term _ l' *)
  if (F.Symb.eq_bool f (head_symb x_part_val))
  then
      match remove T.eq_bool (closed_term x_part_val) l' with
      | None => nil
      | Some rmv =>
        let t1' := build f (cons (Var (new_var x_part_val)) list_of_terms) in
        let t2' := build f rmv in
        let new_pb := 
          mk_pb  (existential_vars pb)
                ((t1',t2') :: list_of_equations)
                (solved_part pb)
                (partly_solved_part pb) in
         new_pb :: nil  
     end
  else
      map_without_repetition T.eq_bool
       (fun t =>
          match t with
          | Term h l''' =>
              if F.Symb.eq_bool h (head_symb x_part_val)
              then
                  match remove T.eq_bool (closed_term x_part_val) l''' with
                  | None => None
                  | Some rmv =>
                    match remove T.eq_bool t l' with
                    | None => None
                    | Some rmv2 =>
                      let y := new_var x_part_val in
                      let y_val := build h rmv in
                      let t1' := build f list_of_terms in
                      let t2' := build f rmv2 in
                      let new_pb :=
                        mk_pb (existential_vars pb)
                              ((Var y, y_val) :: (t1',t2') :: list_of_equations)
                              (solved_part pb)
                              (partly_solved_part pb) in
                      Some new_pb
                    end
                  end
              else None
           | Var _ => None
           end)
         l'.

Definition ac_elementary_solve_term_var_without_val_term 
pb f x list_of_terms l' list_of_equations : list matching_problem := 
(* t1 = Term f ((Var x) :: list_of_terms as l); t2 = Term _ l' *)
  map12_without_repetition T.eq_bool
  (fun t => 
    match remove T.eq_bool t l' with
    | None => (None, None)
    | Some rmv =>
      let l'_without_t := rmv in
      let t1' := build f list_of_terms in
      let t2' := build f l'_without_t in
      let new_pb :=
        mk_pb (existential_vars pb)
              ((t1', t2') :: list_of_equations)
              ((x, t) :: (solved_part pb))
              (partly_solved_part pb) in 
       if le_gt_dec (length l') ((length list_of_terms) + 1)
       then (Some new_pb, None)
       else 
         let y := fresh_var pb in
         let t1'' := build f (Var y :: list_of_terms) in
         let new_pb' := 
           mk_pb (y :: existential_vars pb)
                 ((t1'', t2') :: list_of_equations)
                 (solved_part pb)
                 ((x, mk_pst f y t) :: (partly_solved_part pb)) in
          (Some new_pb, Some new_pb')
    end)
    l'.

Definition ac_elementary_solve pb t1 t2 list_of_equations :=
  match t1, t2 with
  | (Term f (s :: list_of_terms as l)), (Term _ l') =>
    match s with
    | Term g lg => 
        ac_elementary_solve_term_term_term 
          pb f g lg list_of_terms l' list_of_equations
    | Var x =>
      match find X.eq_bool x (solved_part pb) with
      | Some x_val => 
         ac_elementary_solve_term_var_with_val_term 
           pb f x_val list_of_terms l' list_of_equations
      | None =>
        match find X.eq_bool x (partly_solved_part pb) with
        | Some x_part_val => 
           ac_elementary_solve_term_var_with_part_val_term
             pb f x_part_val list_of_terms l' list_of_equations
        | None => 
           ac_elementary_solve_term_var_without_val_term 
             pb f x list_of_terms l' list_of_equations
        end
      end
    end
  | (Term _ nil), (Term _ _) =>
     let new_pb := 
       mk_pb (existential_vars pb)
             list_of_equations
             (solved_part pb)
             (partly_solved_part pb) in
       new_pb :: nil
  | _, _ => nil
  end.

Definition solve pb : list matching_problem :=
  match unsolved_part pb with
  | (tt1,tt2 as e) :: list_of_equations =>
    match tt1, tt2 with
    | Var x, _ =>
      match find X.eq_bool x (solved_part pb) with
      | Some x_val => 
        if T.eq_bool x_val tt2
        then 
          let new_pb := 
            mk_pb (existential_vars pb) 
            list_of_equations (solved_part pb) (partly_solved_part pb) in
          new_pb :: nil
        else nil
      | None =>
        match find X.eq_bool x (partly_solved_part pb) with
        | Some x_part_val =>
          match tt2 with
          | Var _ => nil
          | Term f2 l2 =>
            if F.Symb.eq_bool (head_symb x_part_val) f2
            then 
              let y := new_var x_part_val in
              match remove T.eq_bool (closed_term x_part_val) l2 with
              | Some rmv => 
                let y_val := build f2 rmv in
                let new_pb := 
                  mk_pb (existential_vars pb)
                        ((Var y, y_val) :: list_of_equations)
                        (solved_part pb) (partly_solved_part pb) in
                  new_pb :: nil
              | None => nil
              end
            else nil
         end
       | None =>
           let new_pb :=
             mk_pb (existential_vars pb)
             list_of_equations ((x, tt2) :: (solved_part pb)) (partly_solved_part pb) in
           new_pb :: nil
       end
     end
    | Term f1 l1, Term f2 l2 =>
        if F.Symb.eq_bool f1 f2 
        then 
            match arity f1 with
            | Free _ => 
              match fold_left2
                (fun current_list_of_eqs t1 t2 => (t1,t2) :: current_list_of_eqs)
                list_of_equations l1 l2 with
              | Some new_list_of_equations =>
                let new_pb :=
                  mk_pb (existential_vars pb)
                  new_list_of_equations (solved_part pb) (partly_solved_part pb) in
                new_pb :: nil
              | None => nil
              end
            | AC =>
              if le_gt_dec (length l1) (length l2)
              then ac_elementary_solve pb tt1 tt2 list_of_equations
              else nil
            | C =>
              match l1, l2 with
              | (s1 :: s2 :: nil), (t1 :: t2 :: nil) =>
                let new_pb1 := 
                  mk_pb (existential_vars pb)
                  ((s1,t1) :: (s2,t2) :: list_of_equations) 
                        (solved_part pb) (partly_solved_part pb) in
               let new_pb2 := 
                  mk_pb (existential_vars pb)
                  ((s1,t2) :: (s2,t1) :: list_of_equations) 
                        (solved_part pb) (partly_solved_part pb) in
                 new_pb1 :: new_pb2 :: nil
                | _, _ => nil
              end
            end
        else nil
    | _, _ => nil
    end
  | nil => nil
end.

Fixpoint well_sorted_partly_solved_part (l :  list (variable * partly_solved_term)) : Prop :=
 match l with
 | nil => True
 | (v,p) :: tl => 
    v <> new_var p /\
    (forall v', 1 <= nb_occ X.eq_bool v' tl -> v' <> new_var p) /\
    well_sorted_partly_solved_part tl
end.

Definition well_formed_pb pb :=
(forall t1 t2, In (t1,t2) pb.(unsolved_part) ->
                   well_formed_cf t1 /\ well_formed_cf t2) /\
(forall v, match (find X.eq_bool v pb.(solved_part)) with
  | None => True
  | Some t => well_formed_cf t 
  end) /\
(forall v, match (find X.eq_bool v pb.(partly_solved_part)) with
  | None => True
  | Some pst => 
      match arity pst.(head_symb) with
      | AC => well_formed_cf pst.(closed_term) /\
              match pst.(closed_term) with
              | Var _ => True
              | Term f _ => pst.(head_symb)<>f
              end
      | _ => False
      end
  end) /\
(forall v, 
  nb_occ X.eq_bool v (solved_part pb) + nb_occ X.eq_bool v (partly_solved_part pb) <= 1) /\
well_sorted_partly_solved_part (partly_solved_part pb) /\
(forall v p,
  find X.eq_bool v (partly_solved_part pb) = Some p -> occurs_in_pb (new_var p) pb).

Lemma list_permut_occurs_in_term_list :
  forall v l1 l2, permut l1 l2 -> occurs_in_term_list v l1 ->
  occurs_in_term_list v l2.
Proof.
intros v; 
cut (forall l l', occurs_in_term_list v l' -> occurs_in_term_list v (l ++ l')).
intros H l1; induction l1.
contradiction.
intros l2 P O. 
assert (a_in_l2 : In a l2).
rewrite <- (list_permut.in_permut_in P); left; trivial.
destruct (In_split _ _ a_in_l2) as [l2' [l2'' H']]; subst l2.
elim O; clear O; intro O.
apply H; left; trivial.
rewrite <- permut_cons_inside in P.
generalize (IHl1 (l2' ++ l2'') P O).
clear l1 IHl1 P O; induction l2'.
intro; right; trivial.
simpl; intro O; destruct O as [ O | O ].
left; trivial.
right; apply IHl2'; trivial; apply in_or_app; right; left; trivial.
reflexivity.
intro l; induction l; trivial; right; apply IHl; trivial.
Qed.

Lemma add_new_var_to_subst :
forall t1 v t2 sigma, ~occurs_in_term v t1 ->
      apply_cf_subst sigma t1 = apply_cf_subst ((v,t2) ::  sigma) t1.
Proof.
intro t1; pattern t1; apply term_rec3; clear t1.
intros v v0 t2 sigma O; simpl; (* rewrite find_add_spec; *)
generalize (X.eq_bool_ok v v0); case (X.eq_bool v v0); [intro v_eq_v0; subst v | intros _].
apply False_rect; apply O; unfold occurs_in_term; trivial.
reflexivity.
intros f l IH v t2 sigma O; simpl.
assert (H : map (apply_cf_subst sigma) l = map (apply_cf_subst ((v,t2) :: sigma)) l).
induction l as [ | t l].
trivial.
simpl map; rewrite <- (IH t).
rewrite <- IHl.
reflexivity.
intros; apply IH; [right | idtac]; assumption.
intro v_in_l; apply O; right; assumption.
left; reflexivity.
intro v_in_t; apply O; left; assumption.
rewrite H; reflexivity.
Qed.

Lemma add_new_var_to_rough_sol :
  forall pb sigma t, well_formed_pb pb -> is_rough_sol pb sigma ->
  (is_rough_sol pb ((fresh_var pb, t) :: sigma)).
Proof.
intros pb sigma t ; generalize (fresh_var_spec pb);
unfold occurs_in_pb, is_rough_sol;
intros O w S'; elim S'; clear S';
intros S1 S2; elim S2; clear S2;
intros S2 S3; split.
induction pb.(unsolved_part).
contradiction.
destruct a; intros t2 t3 I; elim I; clear I; intro I.
inversion I.
rewrite <- (add_new_var_to_subst t2 (fresh_var pb) t).
apply S1; left; trivial.
unfold not; intro O'; apply O.
left; left; subst t2; trivial.
apply IHl; trivial.
intro O'; apply O; destruct O' as [O' | O']; [ left | idtac ]; right; trivial.
intros; apply S1; right; trivial.
destruct w as [ _ [_ [_ [_ [_ w]]]]]; split.
intro v; generalize (S2 v); case_eq (find X.eq_bool v (partly_solved_part pb)).
intros p F; repeat rewrite <- (add_new_var_to_subst); trivial.
intro O'; apply O; simpl in O'; rewrite O'; apply (w v p F).
intro O'; apply O; simpl in O'; rewrite O'; right; left; rewrite F; trivial.
trivial.
intro v; generalize (S3 v); case_eq (find X.eq_bool v (solved_part pb)).
intros t0 F; simpl; generalize (X.eq_bool_ok v (fresh_var pb)); case (X.eq_bool v (fresh_var pb)); [intro v_eq_fresh_var | intro v_diff_fresh_var].
apply False_rect; apply O.
do 2 right; subst v; rewrite F; exact I.
intro; assumption.
intros _ _; exact I.
Qed.

Definition is_well_formed_sol pb sigma :=
 (exists sigma',  is_rough_sol pb sigma' /\
                  (forall v, In v (existential_vars pb) \/
                      apply_cf_subst sigma (Var v) = apply_cf_subst sigma' (Var v)) /\
                         (well_formed_cf_subst sigma')).

End Make.







