(**
CoLoR, a Coq library on rewriting and termination.

See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2013-09-17

* Termination proof of Goedel System T
*)

Set Implicit Arguments.

From CoLoR Require Import LogicUtil OrdUtil LSimple RelUtil.
From Coq Require Import Structures.Equalities Omega.
From CoLoR Require SetUtil.


(****************************************************************************)
(** ** Type constants of System T. **)

Inductive B : Type := Nat : B.

Lemma eq_B_dec : forall a b : B, {a=b}+{~a=b}.

Proof. (*COQ:decide equality*)destruct a. destruct b. auto. Qed.

(** [Typ] structure for type constants. *)

Module BTyp <: Typ.

  Definition t := B.

End BTyp.

(** [Cmp] structure for type constants. *)

Module BCmp <: Cmp.

  Include BTyp.

  Definition cmp (_ _ : B) := Eq.

  Lemma cmp_opp x y : cmp x y = CompOpp (cmp y x).

  Proof. refl. Qed.

End BCmp.

(** [CmpTransLeibniz] structure for type constants. *)

Module BCmpTransLeibniz <: CmpTransLeibniz.

  Include BCmp.

  Lemma cmp_eq x y : cmp x y = Eq -> x = y.

  Proof. destruct x; destruct y. refl. Qed.

  Lemma cmp_lt_trans x y z : cmp x y = Lt -> cmp y z = Lt -> cmp x z = Lt.
  
  Proof. fo. Qed.

End BCmpTransLeibniz.

(****************************************************************************)
(** ** Types of System T. *)

Notation TNat := (Base Nat).

(** [Cmp] structure for System T types. *)

Module Ty_Cmp := ST_Cmp BCmp.

(** [CmpTransLeibniz] structure for System T types. *)

Module Ty_CmpTransLeibniz := ST_CmpTransLeibniz BCmpTransLeibniz.

(****************************************************************************)
(** ** Function symbols of System T. *)

Inductive F : Type :=
| Zero : F
| Succ : F
| Rec : Ty B -> F.

(** Well-founded precedence on function symbols. *)

Definition prec f :=
  match f with
    | Zero => 0
    | Succ => 1
    | Rec _ => 2
  end.

(** [Cmp] structure for function symbols.

We use the lexicographic path ordering with Zero < Succ < Rec A and
Rec A < Rec B if A < B. *)

From Coq Require Import Compare_dec.

Module FCmp <: Cmp.

  Definition t := F.

  Fixpoint cmp f g :=
    match f, g with
      | Rec u, Rec v => Ty_Cmp.cmp u v
      | _, _ => Nat.compare (prec f) (prec g)
    end.

  Lemma cmp_opp f g : cmp f g = CompOpp (cmp g f).

  Proof. destruct f; destruct g; try refl. apply Ty_Cmp.cmp_opp. Qed.

End FCmp.

(** [CmpTransLeibniz] structure for function symbols. *)

Module FCmpTransLeibniz <: CmpTransLeibniz.

  Include FCmp.

  Lemma cmp_eq x y : cmp x y = Eq -> x = y.

  Proof.
    destruct x; destruct y; simpl; try (refl||discr).
    intro e. apply Ty_CmpTransLeibniz.cmp_eq in e. subst. refl.
  Qed.

  Lemma cmp_lt_trans x y z : cmp x y = Lt -> cmp y z = Lt -> cmp x z = Lt.

  Proof.
    destruct x; destruct y; destruct z; simpl; try (refl||discr).
    apply Ty_CmpTransLeibniz.cmp_lt_trans.
  Qed.

End FCmpTransLeibniz.

(** [OrderedType] structure for function symbols. *)

Module FMOT := MOT_of_CmpTransLeibniz FCmpTransLeibniz.

Module FOrd := MOT_to_OT FMOT.

(****************************************************************************)
(** ** [L] structure (term algebra) of System T. *)

From CoLoR Require Import VecUtil.

Module L_SystemT <: L_Struct.

  Definition F := F.

  Module FOrd := FOrd.

  Module Export V := NatVar.

  Notation Te := (Te F X).
  Notation Tes := (vector Te).

  Notation Var := (@Var F X).
  Notation Fun := (@Fun F X).
  Notation App := (@App F X).
  Notation Lam := (@Lam F X).

  Notation apps := (@apps F X).
  Notation fv := (@fv F X ens_X).
  Notation eq_term_dec := (@eq_term_dec F X FOrd.eq_dec XOrd.eq_dec).

  Notation FZero := (Fun Zero).
  Notation FSucc := (Fun Succ).
  Definition FRec A := Fun (Rec A).

End L_SystemT.

(****************************************************************************)
(** ** [RS] structure (rewrite rules) of System T. *)

From CoLoR Require Import LCompRewrite.
Import VectorNotations.
Local Open Scope vector_scope.

Module RS_SystemT <: RS_Struct.

  Module Export L := L_SystemT.

  (* Some variables. *)
  Definition u := Var 0.
  Definition v := Var 1.
  Definition n := Var 2.

  Inductive R : relation Te :=
  | rule_Rec_Zero : forall A, R (apps (Fun (Rec A)) [FZero; u; v]) u
  | rule_Rec_Succ : forall A, R (apps (Fun (Rec A)) [apps FSucc [n]; u; v])
                                (apps v [n; apps (FRec A) [n; u; v]]).

  Definition rule := R.

  Instance fv_rule : Proper (rule --> Subset) fv.

  Proof.
    intros a b ba. inversion ba; subst; simpl; intro x; set_iff; tauto.
  Qed.

  Definition lhs_fun l r (_ : rule l r) :=
    match head l with
      | Def.Fun f => f
      | _ => Zero (* don't care *)
    end.

  Definition lhs_nb_args l r (_ : rule l r) := 3.

  Definition lhs_args l r :=
    match l as l return forall h : rule l r, Tes (lhs_nb_args h) with
      | Def.App (Def.App (Def.App (Def.Fun _) l1) l2) l3 =>
        fun _ => [l1; l2; l3]
      | _ => fun _ => [FZero; FZero; FZero] (* don't care *)
    end.

  Lemma lhs_ok l r ( h : rule l r) : l = apps (Fun (lhs_fun h)) (lhs_args h).

  Proof. inversion h; subst; refl. Qed.

End RS_SystemT.

(****************************************************************************)
(** ** [ST] structure (types of function symbols) of System T. *)

From Coq Require FMapAVL.

Module ST_SystemT <: ST_Struct.

  Module Export L := L_SystemT.

  Definition So := B.

  Notation Ty := (Ty So).

  Notation TNat := (Base Nat).

  Fixpoint typ f :=
    match f with
      | Zero => TNat
      | Succ => TNat ~~> TNat
      | Rec A => TNat ~~> A ~~> (TNat ~~> A ~~> A) ~~> A
    end.

  Module Export XMap := FMapAVL.Make XOrd.

  Notation En := (@XMap.t Ty).
  Notation empty := (@XMap.empty Ty).
  Notation add := (@XMap.add Ty).
  Notation In := (@XMap.In Ty).
  Notation MapsTo := (@XMap.MapsTo Ty).
  Notation Equal := (@XMap.Equal Ty).
  Notation env := (mk_Env empty add In MapsTo Equal).

End ST_SystemT.

(****************************************************************************)
(** ** [DLQO] structure for the termination proof of System T.

We use [prec] to quasi-order function symbols in a wellfounded way. *)

From CoLoR Require Import SN LCall.

Module DLQO_SystemT <: DLQO_Struct.

  Module Export ST := ST_SystemT.

  Definition C := F.

  Definition code (f : F) := f.

  Import FCmp.

  Definition gtC := Rof gt prec.

  Lemma gtC_wf : WF gtC.

  Proof. apply WF_inverse. apply WF_gt. Qed.

  Definition filter_arity (_ : F) := 1.

  Definition filter (_ : F) := [0].

  Notation gt_call := (@gt_call F X C code gtC).
  Notation gt_args_lex := (@gt_args_lex F X FOrd.eq_dec XOrd.eq_dec ens_X
    var_notin C filter_arity filter).

End DLQO_SystemT.

(****************************************************************************)
(** ** Wellfounded [OrderedType] structure on type constants.

We use the empty relation to quasi-order type constants in a
wellfounded way. *)

From CoLoR Require Import EqUtil.

Module BOrdWF_MOT <: MiniOrderedType.

  Include BTyp.

  Include LeibnizFacts BTyp.

  Definition lt : relation t := empty_rel.

  Instance lt_trans : Transitive lt.

  Proof. fo. Qed.

  Lemma lt_not_eq x y : lt x y -> x <> y.

  Proof. fo. Qed.

  Lemma compare x y : Compare lt eq x y.

  Proof. apply EQ. destruct x; destruct y. refl. Qed.

End BOrdWF_MOT.

Module BOrdWF := MOT_to_OT BOrdWF_MOT.

(****************************************************************************)
(** ** [BI] structure (accessible arguments) of System T. *)

From CoLoR Require Import LCompInt.

Module BI_SystemT <: BI_Struct.

  Module Export ST := ST_SystemT.

  Module Export BOrd := BOrdWF.

  Infix "<B" := lt (at level 70).

  Lemma ltB_wf : well_founded lt.

  Proof. intro b. apply Acc_intro. fo. Qed.

  Import SetUtil.

  Inductive acc : F -> set nat :=
  | Acc_Succ : acc Succ 0.

  Definition Acc := acc.

  Lemma Acc_arity f i (hi : Acc f i) : i < arity (typ f).

  Proof. inversion hi; clear hi; subst; simpl; omega. Qed.

  Lemma Acc_ok f i (hi : Acc f i) a :
    occurs a (Vnth (inputs (typ f)) (Acc_arity hi)) ->
    a <B output_base (typ f)
    \/ (a = output_base (typ f)
      /\ pos a (Vnth (inputs (typ f)) (Acc_arity hi))).

  Proof. inversion hi; subst; simpl; clear hi. fo. Qed.

  Notation aeq := (@aeq F X FOrd.eq_dec XOrd.eq_dec ens_X var_notin).
  Notation supterm_acc := (@supterm_acc F X So typ Acc Acc_arity).

End BI_SystemT.

(****************************************************************************)
(** ** [CC] structure for the termination proof of System T. *)

From CoLoR Require Import LCompClos.

Module CC_SystemT <: CC_Struct.

  Module Export BI := BI_SystemT.

  Notation cc := (@cc F X So ens_X env typ Acc Acc_arity).

End CC_SystemT.

(****************************************************************************)
(** ** Termination proof of System T. *)

(*SLOW*)Module Export SN := SN_rewrite CC_SystemT RS_SystemT DLQO_SystemT.

From CoLoR Require Import Lexico.

Import DLQO_SystemT RS_SystemT.

Lemma tr_sn_SystemT : forall E v V, E |- v ~: V -> SN R_aeq v.

Proof.
  apply tr_sn_beta_eta_rewrite_aeq.
  intros l r h; inversion h; subst;
    unfold lhs_fun, lhs_args, lhs_nb_args; simpl.

  (* rule_Rec_Zero *)
  eapply cc_arg' with (i:=1); refl.

  (* rule_Rec_Succ *)
  set (ls := [App FSucc n; u; v]).

  assert (hn : cc gt1 (Rec A) ls ST.empty n TNat).
  eapply cc_acc' with (g:=Succ) (us:=[n]) (i:=0); simpl; try refl.
  eapply cc_arg' with (i:=0); refl.

  assert (hv : cc gt1 (Rec A) ls ST.empty v (TNat ~~> A ~~> A)).
  eapply cc_arg' with (i:=2); simpl; refl.

  assert (hu : cc gt1 (Rec A) ls ST.empty u A).
  eapply cc_arg' with (i:=1); simpl; refl.

  eapply cc_app. eapply cc_app. apply hv. hyp.
  eapply cc_call' with (g:=Rec A) (us:=[n; u; v]); try refl.
  simpl. omega.
  unfold gt1, Def.gt_call, Rof, transp. apply right_lex.
  unfold Def.gt_args_lex, Rof, lexv; simpl. apply lex1. apply opt_intro.
  unfold gt. apply clos_aeq_intro_refl. apply t_step.
  eapply stacc_intro' with (i:=0) (f:=Succ) (ts:=[n]); try refl.
  intros i i1 i2. destruct i. simpl. hyp. destruct i.
  simpl. hyp. destruct i. simpl. hyp. omega.

  Grab Existential Variables.
  apply Acc_Succ. simpl; omega. omega. simpl; omega. omega. simpl; omega.
  omega. apply Acc_Succ. simpl; omega. omega.
Qed.
