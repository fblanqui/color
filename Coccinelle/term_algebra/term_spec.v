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

(** * Term algebra defined as functor from a Module Signature and a Module Variable.*)


From Stdlib Require Import Recdef List Arith Setoid.
From CoLoR Require Import closure more_list list_permut list_set decidable_set.

Set Implicit Arguments.

Declare Scope term_scope.

(** The arity of a symbol contains the information about built-in theories as in CiME *)
Inductive arity_type : Type :=
  | AC : arity_type
  | C : arity_type
  | Free : nat -> arity_type.

(** * Module Type Signature. 
 There are almost no assumptions, except a decidable equality 
and an arity function. *)

Module Type Signature.
Declare Module Export Symb : decidable_set.S.
Parameter arity : Symb.A -> arity_type.
End Signature.

(** * Module Type Term built from a signature and a set of variables. *)
Module Type Term.

Declare Module Import F : Signature.
Declare Module Import X : decidable_set.S.

Notation symbol := Symb.A.
Notation eq_symb_bool := Symb.eq_bool.
Notation eq_symb_bool_ok := Symb.eq_bool_ok.
Parameter eq_symb_bool_refl : forall x, eq_symb_bool x x = true.

Notation variable := X.A.
Notation eq_var_bool := X.eq_bool.
Notation eq_var_bool_ok := X.eq_bool_ok.
Parameter eq_var_bool_refl : forall x, eq_var_bool x x = true.

Declare Module VSet : 
   list_set.S with Definition EDS.A := X.A
                 with Definition EDS.eq_A := @eq X.A.

(* Declare Module VSet : list_set.S with Definition DS.A := variable. *)

Ltac destruct_arity f n Af :=
generalize (eq_refl (arity f)); pattern f at 1; destruct (arity f) as [ |  | n]; intro Af.


(** Definition of terms. 
Arity is not taken into account, and terms may be ill-formed. *)
Inductive term : Type :=
  | Var : variable -> term
  | Term : symbol -> list term -> term.

(** Definition and a few properties of the size of a term.*)
Fixpoint size (t:term) : nat :=
  match t with
  | Var v => 1
  | Term _ l => 
       let size_list :=
         (fix size_list (l : list term) {struct l} : nat :=
            match l with
            | nil => 0
            | t :: lt => size t + size_list lt
            end) in
        1 + size_list l
   end.

Parameter size_unfold :
 forall t, size t = match t with
                             | Var _ => 1
                             | Term f l => 1 + list_size size l
                           end.

Parameter size_ge_one : forall t, 1 <= size t.

Function var_in_term_list (x : variable) (l : list term) 
{ measure (list_size size) l } : bool :=
  match l with
    | nil => false
    | (Var y) :: l => orb (eq_var_bool x y) (var_in_term_list x l) 
    | (Term _ ll) :: l => orb (var_in_term_list x ll) (var_in_term_list x l)
end.
Proof.
intros _ l t l' y H1 H2;  simpl; auto with arith.
intros _ l t l' f ll H1 H2; simpl; auto with arith.
intros _ l t l' f ll H1 H2; simpl; apply Nat.lt_le_trans with (size (Term f ll)).
rewrite size_unfold; simpl; auto with arith.
simpl; auto with arith.
Defined.

Definition var_in_term (v : variable) (t : term) : bool :=
	match t with
	| Var x =>  eq_var_bool x v
        | Term _ l => var_in_term_list v l
        end.

Fixpoint var_list (t : term) : list variable :=
  match t with
  | Var x => (x :: nil)
  | Term _ l =>
       let var_list_list :=
         (fix var_list_list (l : list term) {struct l} : list variable :=
            match l with
            | nil => @nil _
            | t :: lt => var_list t ++ var_list_list lt
            end) in
        var_list_list l
   end.

Fixpoint var_list_list (l : list term) {struct l} : list variable :=
            match l with
            | nil => nil
            | t :: lt => var_list t ++ var_list_list lt
            end.

Parameter var_list_list_app : forall l1 l2, var_list_list (l1 ++ l2) = (var_list_list l1) ++ var_list_list l2.

Parameter in_var_list_list : forall l v, In v (var_list_list l) -> exists t, In t l /\ In v (var_list t).

Parameter mem_var_list_list : forall l v, mem (@eq _) v (var_list_list l) -> exists t, In t l /\ mem (@eq _) v (var_list t).

Parameter var_list_unfold :
 forall t,
 var_list t = match t with
          | Var x => (x :: nil)
          | Term _ l => var_list_list l
          end.

Parameter var_in_term_is_sound : forall x t, var_in_term x t = true <-> In x (var_list t).

Definition direct_subterm t1 t2 : Prop :=
  match t2 with
  | Var _ => False
  | Term _ l => In t1 l
  end.

Parameter size_direct_subterm :
 forall t1 t2, direct_subterm t1 t2 -> size t1 < size t2.

Fixpoint symb_in_term (f : symbol) (t:term) : bool :=
  match t with
  | Var _ => false
  | Term g l => 
       let symb_in_term_list :=
         (fix symb_in_term_list f (l : list term) {struct l} : bool :=
            match l with
            | nil => false
            | t :: lt => orb (symb_in_term f t) (symb_in_term_list f lt)
            end) in
                 orb (eq_symb_bool f g) (symb_in_term_list f l)
   end.

Fixpoint symb_in_term_list f (l : list term) {struct l} : bool :=
            match l with
            | nil => false
            | t :: lt => orb (symb_in_term f t) (symb_in_term_list f lt)
            end.

Fixpoint symb_list (t : term) : list symbol :=
  match t with
  | Var x => nil
  | Term f l =>
       let symb_list_list :=
         (fix symb_list_list (l : list term) {struct l} : list symbol :=
            match l with
            | nil => nil
            | t :: lt => symb_list t ++ symb_list_list lt
            end) in
        f :: (symb_list_list l)
   end.

Function symb_list_list (l : list term) {struct l} : list symbol :=
            match l with
            | nil => nil
            | t :: lt => symb_list t ++ symb_list_list lt
            end.

Parameter symb_list_list_app : forall l1 l2, symb_list_list (l1 ++ l2) = (symb_list_list l1) ++ symb_list_list l2.

Parameter in_symb_list_list : forall l f, In f (symb_list_list l) -> exists t, In t l /\ In f (symb_list t).

Parameter symb_in_term_unfold :
 forall f t,  symb_in_term f t = match t with
                             | Var _ => false
                             | Term g l =>  orb (eq_symb_bool f g) (symb_in_term_list f l)
                           end.

Parameter symb_in_term_list_app :
  forall f l1 l2, symb_in_term_list f (l1 ++ l2) = 
                     orb (symb_in_term_list f l1) (symb_in_term_list f l2).

Parameter symb_in_direct_subterm :
  forall f l t g, In t l -> symb_in_term g t = true ->
         symb_in_term g (Term f l) = true.

(** ** Recursion on terms. *)
Section Recursion.
Variable P : term -> Type.
Variable Pl : list term -> Type.

Parameter term_rec2 : (forall n t, size t <= n -> P t) -> forall t, P t.
Parameter term_rec3 :
  (forall v, P (Var v)) -> (forall f l, (forall t, In t l -> P t) -> P (Term f l)) -> forall t, P t.
Parameter term_rec4 :
  (forall v, P (Var v)) -> (forall f l, Pl l -> P (Term f l)) ->
  (forall l, (forall t, In t l -> P t) -> Pl l) -> forall t, P t.
End Recursion.

(** ** Double recursion on terms. *)
Section DoubleRecursion.
Variable P2 : term -> term -> Type.
Variable Pl2 : list term -> list term -> Type.

Parameter term_rec7 :
  (forall v1 t2, P2 (Var v1) t2) ->
               (forall t1 v2, P2 t1 (Var v2)) ->
               (forall f1 f2 l1 l2, Pl2 l1 l2 -> P2 (Term f1 l1) (Term f2 l2)) ->
               (forall l1 l2, (forall t1 t2, In t1 l1 -> In t2 l2 -> P2 t1 t2) -> Pl2 l1 l2) ->
               forall t1 t2, P2 t1 t2.

Parameter term_rec8 :
  (forall v1 t2, P2 (Var v1) t2) ->
               (forall t1 v2, P2 t1 (Var v2)) ->
               (forall f1 f2 l1 l2, Pl2 l1 l2 -> P2 (Term f1 l1) (Term f2 l2)) ->
               (forall l1 l2, (forall t1 t2, In t1 l1 -> In t2 l2 -> P2 t1 t2) -> Pl2 l1 l2) ->
               forall l1 l2, Pl2 l1 l2.
End DoubleRecursion.

(** ** Equality on terms is decidable. *)
Fixpoint eq_bool (t1 t2 :term) : bool :=
  match t1, t2 with
  | Var v1, Var v2 => eq_var_bool v1 v2
  | Var _, Term _ _ => false
  | Term _ _, Var _ => false  
  | Term f1 l1, Term f2 l2 =>
       if eq_symb_bool f1 f2 
       then
       let eq_bool_list :=
         (fix eq_bool_list (l1 l2: list term) {struct l1} : bool :=
            match l1, l2 with
            | nil, nil => true
            | nil, (_ :: _) => false
            | (_::_), nil => false
            | t1 :: k1, t2 :: k2 => andb (eq_bool t1 t2) (eq_bool_list k1 k2)
            end) in
        eq_bool_list l1 l2
        else false
   end.

Parameter eq_bool_ok : forall t1 t2, match eq_bool t1 t2 with true => t1 = t2 | false => t1<> t2 end.

Parameter term_term_dec : forall x y:term*term, {x=y}+{~x=y}.

Parameter rel_dec : 
  forall (P : relation term) Plist, (forall u v, P v u <-> In (u,v) Plist) ->
  forall r l, {P r l}+{~P r l}.

Declare Module Term_eq_dec : decidable_set.S with Definition A:= term 
                                                             with Definition eq_bool := eq_bool
                                                             with Definition eq_bool_ok := eq_bool_ok.


(** ** Well-formedness of terms, according to the arity. *)
Fixpoint well_formed_bool (t:term) : bool :=
  match t with
  | Var _ => true
  | Term f l =>
     let well_formed_list :=
       (fix well_formed_list (l:list term) : bool :=
       match l with
       | nil => true
       | h :: tl => andb (well_formed_bool h)  (well_formed_list tl)
       end) in
       andb (well_formed_list l)
     (match arity f with
     | Free n => Nat.eqb (length l) n 
     | _ => Nat.eqb (length l) 2
     end)
  end.

Definition well_formed t := well_formed_bool t = true.

Parameter well_formed_unfold :
 forall t, well_formed t ->
 match t with 
 | Var _ => True
 | Term f l =>
    (forall u, In u l -> well_formed u) /\
    (match arity f with
    | Free n => length l = n
    | _ => length l = 2
    end)
 end.

Parameter well_formed_fold :
 forall t,
 match t with 
 | Var _ => True
 | Term f l =>
    (forall u, In u l -> well_formed u) /\
    (match arity f with
    | Free n => length l = n
    | _ => length l = 2
    end)
 end -> well_formed t.

(** ** Substitutions. *)
Definition substitution := list (variable * term).

Fixpoint apply_subst (sigma : substitution) (t : term) {struct t} : term :=
  match t with
  | Var v => 
    match find eq_var_bool v sigma with
    | None => t
    | Some v_sigma => v_sigma
    end
  | Term f l => Term f (map (apply_subst sigma) l)
    end.

Parameter empty_subst_is_id : forall t, apply_subst nil t = t.
Parameter empty_subst_is_id_list : forall l, map (apply_subst nil) l = l.

(** Composition of substitutions. *)
Definition map_subst (f : variable -> term -> term) sigma :=
  map (fun x =>
            match (x : variable * term) with
            | (v, v_sigma) => (v, f v v_sigma)
            end)
            sigma.

Definition subst_comp sigma1 sigma2 :=
  (map_subst (fun _ t => apply_subst sigma1 t) sigma2)
  ++ 
  (map_subst (fun v t =>
                        match find eq_var_bool v sigma2 with
                        | None => t
                        | Some v_sigma2 => apply_subst sigma1 v_sigma2
                        end)
                      sigma1).

Parameter subst_comp_is_subst_comp_aux1 :
  forall v sigma f,
  find eq_var_bool v (map_subst f sigma) =
   match find eq_var_bool v sigma with
   | None => None
   | Some t => Some (f v t)
  end.

Parameter subst_comp_is_subst_comp :
  forall sigma1 sigma2 t,
   apply_subst (subst_comp sigma1 sigma2) t =
   apply_subst sigma1 (apply_subst sigma2 t).

Parameter instantiated_subterm :
  forall u u' sigma, trans_clos direct_subterm u u' -> 
                             trans_clos direct_subterm (apply_subst sigma u) (apply_subst sigma u').

(** Well-formed substitutions. *)
Definition well_formed_subst sigma :=
  forall v, match find eq_var_bool v sigma with
            | None => True
            | Some t => well_formed t 
            end.

Parameter well_formed_apply_subst :
  forall sigma, well_formed_subst sigma -> 
  forall t, well_formed t -> well_formed (apply_subst sigma t).

Parameter well_formed_apply_subst_strong :
  forall sigma t, (forall x, var_in_term x t = true -> well_formed (apply_subst sigma (Var x))) -> 
  well_formed t -> well_formed (apply_subst sigma t).

Parameter well_formed_remove_subst :
  forall sigma t, well_formed (apply_subst sigma t) -> well_formed t.

Parameter well_formed_remove_term :
  forall sigma t, well_formed (apply_subst sigma t) ->
  forall x, var_in_term x t = true -> well_formed (apply_subst sigma (Var x)).

(** ** Positions in a term.*)
Fixpoint is_a_pos (t : term) (p : list nat) {struct p}: bool :=
  match p with
  | nil => true
  | i :: q =>
    match t with
    | Var _ => false
    | Term _ l => 
         match nth_error l i with
          | Some ti => is_a_pos ti q
          | None => false
          end
     end
  end.

Fixpoint subterm_at_pos (t : term) (p : list nat) {struct p}: option term :=
  match p with
  | nil => Some t
  | i :: q =>
    match t with
    | Var _ => None
    | Term _ l => 
         match nth_error l i with
          | Some ti => subterm_at_pos ti q
          | None => None
          end
    end
  end.

Fixpoint is_subterm (s t : term) : bool  :=
 match t with 
 | Var x => match s with Var y => eq_var_bool x y | _ => false end
 | Term f l => 
      let fix is_subterm_list (l : list term) : bool :=
         match l with
         | nil => false
         | t :: l => orb (is_subterm s t) (is_subterm_list l)
         end in
         orb (eq_bool t s) (is_subterm_list l)
 end.

Parameter is_subterm_ok_true : 
  forall s t, is_subterm s t = true -> {p : list nat | subterm_at_pos t p = Some s}.

Parameter is_subterm_ok_false : 
  forall s t, is_subterm s t = false -> forall p, subterm_at_pos t p <> Some s.

Parameter subterm_at_pos_dec :
  forall t s, {p : list nat | subterm_at_pos t p = Some s}+{forall p, subterm_at_pos t p <> Some s}.

Parameter subterm_at_pos_dec_alt :
  forall t s, {p : list nat | subterm_at_pos t p = Some s}+ {~exists p, subterm_at_pos t p = Some s}.

Parameter subterm_subterm : 
	forall t p s, subterm_at_pos t p = Some s -> (t=s) \/ (trans_clos direct_subterm s t).

Parameter size_subterm_at_pos :
  forall t i p, match subterm_at_pos t (i :: p) with
	           | Some u => size u < size t
	           | None => True
	           end.

Parameter size_strict_subterm : forall s t, trans_clos direct_subterm s t -> size s < size t.

Parameter var_in_subterm :
  forall v s t p, subterm_at_pos t p = Some s -> In v (var_list s)  -> In v (var_list t).

Parameter var_in_subterm2 :
  forall v t, mem (@eq _) v (var_list t) -> {p : list nat | subterm_at_pos t p = Some (Var v)}.

Parameter symb_in_subterm :
  forall f s t p, subterm_at_pos t p = Some s -> symb_in_term f s = true -> symb_in_term f t = true.

Parameter symb_list_ok : forall f t, In f (symb_list t) <-> symb_in_term f t = true.

Parameter symb_list_list_ok : forall f l, In f (symb_list_list l) <-> symb_in_term_list f l = true.

Parameter is_a_pos_exists_subterm :
  forall t p, is_a_pos t p = true <-> exists u, subterm_at_pos t p = Some u.

Parameter well_formed_subterm :
  forall t p s, well_formed t -> subterm_at_pos t p = Some s -> well_formed s.

Fixpoint replace_at_pos (t u : term) (p : list nat) {struct p} : term :=
  match p with
  | nil => u
  | i :: q =>
     match t with
     | Var _ => t
     | Term f l =>
        let replace_at_pos_list :=
         (fix replace_at_pos_list j (l : list term) {struct l}: list term :=
            match l with
            | nil => nil
            | h :: tl =>
                 match j with
                 | O => (replace_at_pos h u q) :: tl
                 | S k => h :: (replace_at_pos_list k tl)
                 end
            end) in
    Term f (replace_at_pos_list i l)
    end
  end.

Fixpoint replace_at_pos_list (l : list term) (u : term) (i : nat) (p : list nat) 
 {struct l}: list term :=
  match l with
  | nil => nil
  | h :: tl =>
     match i with
     | O => (replace_at_pos h u p) :: tl
     | S j => h :: (replace_at_pos_list tl  u j p)
     end
  end.

Parameter replace_at_pos_unfold :
  forall f l u i q,
   replace_at_pos (Term f l) u (i :: q) = Term f (replace_at_pos_list l u i q).

Parameter replace_at_pos_is_replace_at_pos1 :
  forall t u p, is_a_pos t p = true ->
  subterm_at_pos (replace_at_pos t u p) p = Some u.

Parameter replace_at_pos_is_replace_at_pos2 :
  forall t p u, subterm_at_pos t p = Some u -> replace_at_pos t u p = t. 

Parameter subterm_at_pos_apply_subst_apply_subst_subterm_at_pos :
  forall t p sigma, 
  match subterm_at_pos t p with
  | Some u =>
        subterm_at_pos (apply_subst sigma t) p = Some (apply_subst sigma u)
  | None => True
end.

Parameter replace_at_pos_list_replace_at_pos_in_subterm :
forall l1 ui l2 u i p, length l1 = i ->
 replace_at_pos_list (l1 ++ ui :: l2) u i p = 
 l1 ++ (replace_at_pos ui u p) :: l2.

Parameter well_formed_replace_at_pos :
   forall p t u, well_formed t -> well_formed u -> well_formed (replace_at_pos t u p).

Parameter subst_replace_at_pos : 
	forall t u p sigma, is_a_pos t p = true -> apply_subst sigma (replace_at_pos t u p) =
	replace_at_pos (apply_subst sigma t) (apply_subst sigma u) p.

Parameter subterm_in_instantiated_term :
  forall p s t sigma, subterm_at_pos (apply_subst sigma t) p = Some s ->
                    match subterm_at_pos t p with
		    | Some u' => s = apply_subst sigma u'
	            | None => exists v, exists q, exists q', p = q ++ q' /\
                                          In v (var_list t)  /\
                                         subterm_at_pos t q = Some (Var v) /\
	                                 subterm_at_pos (apply_subst sigma (Var v)) q' = Some s
	            end.	

Parameter subterm_in_subterm :
  forall p q s t u, subterm_at_pos t p = Some s -> subterm_at_pos s q = Some u ->
                          subterm_at_pos t (p ++ q) = Some u.

Parameter subterm_in_subterm2 :
  forall p q s t, subterm_at_pos t (p ++ q) = Some s ->
                      exists u, subterm_at_pos t p = Some u /\ subterm_at_pos u q = Some s.

Parameter subterm_subterm_alt : 
	forall t s, (refl_trans_clos direct_subterm s t) -> {p : list nat | subterm_at_pos t p = Some s}.  

Parameter var_in_replace_at_pos :
  forall s p u x, In x (var_list (replace_at_pos s u p)) -> In x (var_list s) \/ In x (var_list u).

Parameter remove_garbage_subst :
  forall sigma : substitution , 
     {sigma' : substitution | (forall x, find eq_var_bool x sigma = find eq_var_bool x sigma') /\
	                                 (forall x val, In (x,val) sigma' -> find eq_var_bool x sigma' = Some val) /\
                                         (forall x y val val' (tau tau' tau'' : substitution), 
                                                 sigma' = tau ++ (x,val) :: tau' ++ (y,val') :: tau'' ->
                                                 x <> y)}.

Parameter subst_eq_vars :
  forall t sigma sigma', (forall v, In v (var_list t) -> apply_subst sigma (Var v) = apply_subst sigma' (Var v)) 
                                    <-> apply_subst sigma t = apply_subst sigma' t.

Fixpoint subst_rest vars sigma : substitution :=
match sigma with
| nil => nil
| (x,u) :: sigma => 
          if mem_bool eq_var_bool x vars 
          then (x,u) :: (subst_rest vars sigma)
          else subst_rest vars sigma
end.

Parameter subst_rest_ok :
  forall vars sigma v, In v vars -> apply_subst (subst_rest vars sigma) (Var v) = apply_subst sigma (Var v).

Parameter subst_rest_rest :
  forall vars sigma v t, In (v,t) (subst_rest vars sigma) -> In v vars.

Parameter subst_rest_subst :
  forall vars sigma v t, In (v,t) (subst_rest vars sigma) -> In (v,t) sigma.

Parameter subst_rest_subst_rest :
  forall vars sigma v t, In v vars -> In (v,t) sigma -> In (v,t) (subst_rest vars sigma).

Definition extend_with_id vars sigma :=
  (map (fun x => (x,Var x)) 
                                 (filter (fun x => 
                                 negb (mem_bool X.eq_bool x (map (@fst _ _) sigma))) vars))
  ++ sigma.

Parameter subst_trivial_ext :
forall vars sigma t, apply_subst (extend_with_id vars sigma) t = apply_subst sigma t.

(** *** Definition of matching. *)
Parameter matching : list (term * term) -> option substitution.

Parameter matching_unfold2 : forall pb,
  matching pb =
  match pb with
   | nil => Some nil
   | (patt, subj) :: pb =>
        match patt with
        | Var x => 
               match matching pb with
               | Some subst => merge eq_var_bool eq_bool ((x,subj) :: nil) subst
               | None => None
               end
         | Term f l => 
             match subj with
               | Var _ => None
               | Term g m => 
                   if eq_symb_bool f g
                  then
                      match l with
                      | nil =>
                          match m with
                          | nil => matching pb
                          | sub1 :: lsub => None
                          end
                      | pat1 :: lpat => 
                           match m with
                           | nil => None
                           | sub1 :: lsub => 
                             match (matching ((pat1, sub1) :: nil)) with
                              | Some subst1 => 
                                  match  (matching ((Term f lpat, Term g lsub) :: pb)) with
                                  | Some subst => merge eq_var_bool eq_bool subst1 subst
                                  | None => None
                                  end 
                              | None => None
                              end
                           end
                      end
                  else None
               end
         end
    end.

Parameter matching_correct :
  forall pb sigma, matching pb = Some sigma ->
            ((forall v p s, In v (var_list p) -> In (p,s) pb -> find eq_var_bool v sigma <> None) /\
           (forall v, find eq_var_bool v sigma <> None -> 
                                 exists p, exists s, In (p,s) pb /\ In v (var_list p)) /\
            (forall p s, In (p,s) pb -> apply_subst sigma p = s)).

Parameter matching_complete :
  forall pb sigma, (forall p s, In (p,s) pb -> apply_subst sigma p = s) ->
  match matching pb with
  | Some tau => forall v p s, In v (var_list p) -> In (p,s) pb -> 
                                    apply_subst tau (Var v) = apply_subst sigma (Var v)
  | None => False
  end.

End Term.
