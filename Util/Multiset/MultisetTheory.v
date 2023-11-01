(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2004-09-06
- William Delobel, 2005-10-07

This file provides a development of (part of) the theory of finite
multisets.
*)

Set Implicit Arguments.

From Coq Require Import List Setoid Morphisms.
From CoLoR Require Import RelExtras MultisetCore ListPermutation NatUtil
     ListExtras LogicUtil.

Module Multiset (MC : MultisetCore).

  Export MC.

  Section NewOperations.

    Definition member x M := (x/M)%msets > 0.

    Definition insert x M : Multiset := {{x}}+M.

    Definition pair a b : Multiset := insert a {{b}}.

    Definition remove a A : Multiset := A - {{a}}.

    Fixpoint list2multiset (l : list A) : Multiset :=
      match l with
      | List.nil => empty
      | List.cons x xs => insert x (list2multiset xs)
      end.

  End NewOperations.

  Notation "{{ x , y }}" := (pair x y) (at level 5) : msets_scope.
  Notation "x 'in' M" := (member x M) (at level 10) : msets_scope.

  Ltac mset_unfold := repeat progress unfold insert,remove,pair,member.

  Ltac try_solve_meq :=
     (intros;
     match goal with 
     | |- _ =mul= _ => 
         ( apply multeq_meq
         ; intro
         ; try_solve_meq
         )
     | _ => 
         ( mset_unfold
         ; repeat progress (
	      try rewrite union_mult;
              try rewrite diff_mult;
              try rewrite empty_mult;
              try rewrite intersection_mult
           )
         ; try lia
         ; try congruence
         ; try solve [auto with multisets]
         )
     end
     ).

  Ltac solve_meq :=
   (solve [try_solve_meq] ||
   fail "Goal is not an equality between multisets or fails to prove").

  Ltac try_solve_meq_ext :=
       (
       let go x := (solve [clear x; try_solve_meq_ext]) in (
       mset_unfold;
       intros; 
       try solve_meq;
       (match goal with
       | H : ?A =mul= ?B |- _ =>
           (  (try_solve_meq; rewrite (meq_multeq H); go H)
           || (try_solve_meq; rewrite <- (meq_multeq H); go H)
           )
       | H : ?a =A= ?b |- _ =>
           (  (rewrite (singleton_mult_in H); go H)
           || (rewrite H; go H)
           || (rewrite <- H; go H)
           || (rewrite (mult_eqA_compat H); go H)
           || (rewrite <- (mult_eqA_compat H); go H)
           )
       | H : ~ ?a =A= ?b |- _ =>
           (rewrite (singleton_mult_notin H); go H)
       | |- _ =mul= _ =>
            ( apply multeq_meq; try_solve_meq_ext )
       end || try_solve_meq))).

  Ltac solve_meq_ext :=
     (solve [try_solve_meq_ext] || 
      fail "Couldn't show multisets equality"). 

  #[global] Hint Unfold member 
              insert
              pair
              remove : multisets.

  Section meq_equivalence.

    Lemma meq_refl M : M =mul= M.

    Proof. solve_meq. Qed.

    Lemma meq_trans M N P : M =mul= N -> N =mul= P -> M =mul= P.

    Proof. solve_meq_ext. Qed.

    Lemma meq_sym M N : M =mul= N -> N =mul= M.

    Proof. solve_meq_ext. Qed.

  End meq_equivalence.

  #[global] Hint Resolve meq_refl meq_trans meq_sym : multisets.

  Global Instance meq_Equivalence : Equivalence meq.

  Proof.
    split.
    intro x. apply meq_refl.
    intros x y. apply meq_sym.
    intros x y z. apply meq_trans.
  Qed.

  Global Instance union_morph : Proper (meq ==> meq ==> meq) union.

  Proof. intros a b ab c d cd. solve_meq. Qed.

  Global Instance singleton_morph : Proper (eqA ==> meq) singleton.

  Proof.
    intros x y H. try_solve_meq_ext; case (eqA_dec x0 x); intros.
    assert (x0 =A= y); [rewrite <- H; trivial | idtac].
    assert (x0/{{y}} = 1);
      assert (x0/{{x}} = 1);
      solve [auto with multisets | congruence].
    assert (~x0 =A= y); [rewrite <- H; trivial | idtac].
    assert (x0/{{x}} = 0);
      assert (x0/{{y}} = 0); 
      solve [auto with multisets | congruence].
  Qed.

  Global Instance pair_morph : Proper (eqA ==> eqA ==> meq) pair.

  Proof. intros a b ab c d cd. solve_meq_ext. Qed.

  Global Instance mult_morph : Proper (eqA ==> meq ==> eq) mult.

  Proof. intros a b ab c d cd. solve_meq_ext. Qed.

  Global Instance diff_morph : Proper (meq ==> meq ==> meq) diff.

  Proof. intros a b ab c d cd. solve_meq_ext. Qed.

  Global Instance insert_morph : Proper (eqA ==> meq ==> meq) insert.

  Proof. intros a b ab c d cd. solve_meq_ext. Qed.

  Global Instance member_morph : Proper (eqA ==> meq ==> iff) member.

  Proof. mset_unfold; intros a a0 h m m0 H. rewrite h, H. intuition. Qed.

  Global Instance remove_morph : Proper (eqA ==> meq ==> meq) remove.

  Proof. intros a b ab c d cd. solve_meq_ext. Qed.

  Global Instance intersection_morph : Proper (meq ==> meq ==> meq) intersection.

  Proof. intros a b ab c d cd. solve_meq. Qed.

  Section MultisetLemmas.

    Lemma mset_ind : forall P : Multiset -> Prop,
      P empty -> (forall M a, P M -> P (M + {{a}})) -> forall M, P M.

    Proof. exact mset_ind_type. Qed.

    Lemma mset_ind_set : forall P : Multiset -> Set,
        P empty -> (forall M a, P M -> P (M + {{a}})) -> forall M, P M.
  
    Proof. exact mset_ind_type. Qed.

    Lemma union_comm M N : M + N =mul= N + M.

    Proof. solve_meq. Qed.

    Lemma intersection_comm M N : M # N =mul= N # M.

    Proof. try_solve_meq. Qed.

    Lemma union_assoc M N P : M + (N + P) =mul= (M + N) + P.

    Proof. solve_meq. Qed.

    Lemma member_singleton x y : x in {{y}} -> x =A= y.

    Proof.
      mset_unfold; intros.
      case (eqA_dec x y); [trivial | intro x_neq_y].
      assert (x/{{y}} = 0); [auto with multisets | idtac].
      rewrite H0 in H; lia.
    Qed.

    Lemma singleton_member_eqA a b : a in {{b}} -> a =A= b.

    Proof.
      intro h. destruct (eqA_dec a b); trivial.
      absurd (mult a {{b}} > 0); trivial.
      rewrite singleton_mult_notin; trivial.
      lia.
    Qed.

    Lemma singleton_mult_union_empty a a' M : 
        {{a}} =mul= {{a'}} + M -> M =mul= empty.

    Proof.
      intros.
      destruct M using mset_ind; auto with multisets.
      assert ({{a}} =mul= {{a'}} + {{a0}} + M).
      rewrite H; solve_meq.
      clear H IHM.
      destruct (eqA_dec a a').
      destruct (eqA_dec a a0).
      absurd (a/{{a}} = a/({{a'}} + {{a0}} + M)).
      rewrite !union_mult, !singleton_mult_in; auto with sets.
      lia.
      apply meq_multeq; trivial.
      absurd ((a0/({{a'}} + {{a0}} + M))%msets > 0).
      rewrite <- (meq_multeq H0 a0).
      rewrite singleton_mult_notin; auto with sets arith.
      rewrite !union_mult, singleton_mult_in with a0 a0; auto with sets arith.
      absurd ((a'/({{a'}} + {{a0}} + M))%msets > 0).
      rewrite <- (meq_multeq H0 a').
      rewrite singleton_mult_notin; auto with sets arith.
      rewrite !union_mult, singleton_mult_in with a' a'; auto with sets arith.
    Qed.

    Lemma member_pair x y z : x in {{y,z}} -> x =A= y \/ x =A= z.

    Proof.
      intro H.
      case (eqA_dec x y); [auto | intro x_neq_y].
      case (eqA_dec x z); [auto | intro x_neq_z].
      assert (x/{{y, z}} = 0).
      mset_unfold.
      rewrite union_mult.
      rewrite !singleton_mult_notin; trivial.
      unfold member in H.
      rewrite H0 in H; lia.
    Qed.

    Lemma union_perm M N P : M + N + P =mul= M + P + N.

    Proof. solve_meq. Qed.

    Lemma union_empty M : M + empty =mul= M.

    Proof. solve_meq. Qed.

    Lemma notempty_member M : M <>mul empty -> exists N a, M =mul= {{a}} + N.

    Proof.
      intros H.
      destruct M using mset_ind.
      absurd (empty =mul= empty); auto with multisets.
      ex M a. apply union_comm.
    Qed.

    Lemma not_empty M x : x in M -> M =mul= empty -> False.

    Proof.
      unfold member; intros mult_x_M M_is_empty.
      absurd (x/M = 0).
      lia.
      assert (x/empty = 0); [auto with multisets | idtac].
      assert (x/M = x/empty); [apply meq_multeq; trivial | idtac].
      lia.
    Qed.
 
    Lemma member_union_l a M N : a in M -> a in (M + N).

    Proof. unfold member; intro H. rewrite union_mult. lia. Qed.

    Lemma member_union_r a M N : a in N -> a in (M + N).

    Proof. unfold member; intro H. rewrite union_mult. lia. Qed.

    Lemma mult_insert : forall M a, (a/(M + {{a}}))%msets > 0.

    Proof.
      intros M a.
      replace (a/(M + {{a}})) with ((a/M)%msets + (a/{{a}})%msets)%nat.
      replace (a/{{a}}) with 1.
      lia.
      sym; auto with multisets sets.
      auto with multisets.
    Qed.

    Lemma singleton_member a : a in {{a}}.

    Proof.
      unfold member. assert (a/{{a}} = 1); [idtac | lia].
      apply singleton_mult_in; auto with sets.
    Qed.

    Lemma member_insert a M : a in (insert a M).
  
    Proof. apply member_union_l. apply singleton_member. Qed.

    Lemma member_member_union a M N : a in M -> a in (M+N).

    Proof.
      unfold member; intros.
      replace (a/(M+N)) with ((a/M)%msets + (a/N)%msets)%nat.
      lia.
      auto with multisets.
    Qed.

    Lemma member_diff_member a M N : a in (M-N) -> a in M.

    Proof. unfold member. rewrite (diff_mult M N). lia. Qed.

    Lemma diff_member_ly_rn a M N : a in M -> ~a in N -> a in (M - N).
    
    Proof. unfold member; intros H H0. rewrite diff_mult. lia. Qed.

    Lemma diff_remove_both a M N :
      a in M -> a in N -> M - N =mul= (remove a M) - (remove a N).
    
    Proof.
      unfold member; intros H H0.
      mset_unfold.
      apply multeq_meq; intro x.
      rewrite !diff_mult.
      destruct (eqA_dec x a).
      rewrite !singleton_mult_in; trivial.
      rewrite (mult_eqA_compat M e), (mult_eqA_compat N e).
      lia.
      rewrite !singleton_mult_notin; trivial.
      lia.
    Qed.

    Lemma member_union a M N : a in (M+N) -> a in M \/ a in N.

    Proof. unfold member. rewrite (union_mult M N). lia. Qed.

    Lemma member_meq_union a M N M' N' :
      M + N =mul= M' + N' -> (a in M \/ a in N) -> ~a in N' -> a in M'.

    Proof.
      mset_unfold; intros.
      assert (((a/M)%msets + (a/N)%msets)%nat
              = ((a/M')%msets + (a/N')%msets)%nat).
      rewrite <- !union_mult.
      apply meq_multeq; trivial.
      lia.
    Qed.

    Lemma meq_union_meq M N P : M + P =mul= N + P -> M =mul= N.

    Proof.
      intros; try_solve_meq.
      assert (((x/M)%msets + (x/P)%msets)%nat
              = ((x/N)%msets + (x/P)%msets)%nat).
      rewrite <- !union_mult.
      apply meq_multeq; trivial.
      lia.
    Qed.

    Lemma meq_meq_union M N P : M =mul= N -> M + P =mul= N + P.

    Proof. solve_meq. Qed.

    Lemma meq_ins_ins_eq a a' M M' :
      M + {{a}} =mul= M' + {{a'}} -> a =A= a' -> M =mul= M'.

    Proof.
      intros.
      cut (M + {{a}} =mul= M' + {{a'}}).
      rewrite H0; intro; apply meq_union_meq with {{a'}}; trivial.
      trivial.
    Qed.

    Lemma meq_ins_ins a a' M M' :
      M + {{a}} =mul= M' + {{a'}} -> M =mul= M' + {{a'}} - {{a}}.

    Proof.
      intros.
      try_solve_meq.
      assert ((x/M)%msets + (x/{{a}})%msets
              = (x/M')%msets + (x/{{a'}})%msets)%nat.
      rewrite <- !union_mult.
      apply meq_multeq; trivial.
      lia.
    Qed.

    Lemma member_ins_ins_meq a a' M M' :
      M + {{a}} =mul= M' + {{a'}} -> ~a =A= a' -> a in M'.

    Proof.
      intros.
      assert (((a/M)%msets + 1)%nat = ((a/M')%msets + 0)%nat).
      rewrite <- (singleton_mult_in ((Seq_refl A eqA eqA_Equivalence) a)),
        <- (singleton_mult_notin H0), <- !union_mult.
      apply meq_multeq; trivial.
      mset_unfold; lia.
    Qed.

    Lemma meq_ins_rem a M : a in M -> M =mul= M - {{a}} + {{a}}.

    Proof.
      mset_unfold; intros.
      apply multeq_meq; intro.
      rewrite union_mult.
      rewrite diff_mult.
      case (eqA_dec x a); intro x_a.
      (* x =A= a *)
      rewrite singleton_mult_in; trivial.
      assert (x/M = a/M).
      apply mult_eqA_compat; trivial.
      lia.
      (* ~ x =A= a *)
      rewrite !singleton_mult_notin.
      lia.
      trivial.
    Qed.

    Lemma meq_remove_insert a M : remove a (M + {{a}}) =mul= M.
  
    Proof. solve_meq. Qed.

    Lemma meq_remove a M N : insert a M =mul= N -> M =mul= remove a N.
  
    Proof. intros. rewrite <- H. solve_meq. Qed.

    Lemma insert_meq M N a : insert a M =mul= insert a N -> M =mul= N.
    
    Proof.
      intros; apply multeq_meq; intro.
      set (w := (meq_multeq H) x).
      unfold insert in w.
      rewrite !union_mult in w.
      lia.
    Qed.

    Lemma insert_remove_eq a a' M : a =A= a' -> M =mul= remove a (insert a' M).
    
    Proof.
      intros.
      apply multeq_meq.
      intro x; mset_unfold.
      rewrite diff_mult.
      rewrite union_mult.
      destruct (eqA_dec x a).
      rewrite !singleton_mult_in; eauto with sets.
      lia.
      rewrite !singleton_mult_notin; eauto with sets.
      lia.
    Qed.

    Lemma meq_insert_remove a M : a in M -> insert a (remove a M) =mul= M.
    
    Proof.
      intros.
      apply multeq_meq; intro x.
      unfold insert, remove.
      rewrite union_mult.
      rewrite diff_mult.
      destruct (eqA_dec x a).
      rewrite singleton_mult_in; trivial.
      rewrite (mult_eqA_compat M e).
      unfold member in H.
      lia.
      rewrite singleton_mult_notin; trivial.
      lia.
    Qed.

    Lemma insert_remove_noteq a a' M :
      ~a =A= a' -> remove a (insert a' M) =mul= insert a' (remove a M).
    
    Proof.
      intros.
      apply multeq_meq.
      intro x; mset_unfold.
      repeat progress (try rewrite union_mult; try rewrite diff_mult).
      destruct (eqA_dec x a).
      rewrite !(singleton_mult_in e), (@singleton_mult_notin x a').
      lia.
      rewrite e; auto with sets.
      rewrite (@singleton_mult_notin x a); trivial.
      destruct (eqA_dec x a').
      solve_meq.
      solve_meq.
    Qed.

    Lemma meq_cons a M N :
      M + {{a}} =mul= N -> exists N', N =mul= N' + {{a}} /\ M =mul= N'.
      
    Proof.
      intros.
      exists (remove a N); split.
      assert (aN: a in N).
      rewrite <- H.
      rewrite (union_comm M {{a}}).
      fold (insert a M); apply member_insert.
      set (N' := N) in |- * at 1.
      rewrite (meq_ins_rem aN); unfold N'; clear N'.
      rewrite (meq_remove_insert a (N - {{a}})).
      apply meq_ins_rem; trivial.    
      rewrite <- H.
      solve_meq.
    Qed.
  
    Lemma meq_diff_meq M N P : M =mul= N -> M - P =mul= N - P.
  
    Proof. solve_meq. Qed.

    Section Decidability.

      Lemma member_dec a M : {a in M}+{~a in M}.
  
      Proof.
        intros; case (Compare_dec.zerop (mult a M)); intro.
        right; mset_unfold; lia.
        left; auto.
      Qed.

      Lemma empty_dec : forall M, {M =mul= empty}+{M <>mul empty}.
  
      Proof.
        apply mset_ind_type with 
          (P := fun M => {M =mul= empty}+{M <>mul empty}).
        left; solve_meq.
        intros M a cmp; right; intro emp.
        absurd (a/(M + {{a}}) = a/empty); auto with multisets.
        rewrite empty_mult; rewrite union_mult.
        set (w := singleton_member a); unfold member in w.
        lia.
      Qed.

      Lemma empty_decomp_dec : forall M,
          {Ma: (Multiset * A) | M =mul= fst Ma + {{snd Ma}}} + {M =mul= empty}.
  
      Proof.
        induction M using mset_ind_type.
        right; auto with multisets.
        left; exists (M, a); auto with multisets.
      Qed.

    End Decidability.

    Lemma insert_diff a M N :
      insert a M - N =mul= empty -> a in N /\ M - remove a N =mul= empty.

    Proof.
      intros.
      assert (a in N).
      destruct (member_dec a N); trivial.
      exfalso.
      apply not_empty with empty a; auto with multisets.
      fold (member a empty).
      rewrite <- H.
      apply diff_member_ly_rn; eauto with multisets.
      apply member_insert.
      split; trivial.
      rewrite <- H.
      rewrite (diff_remove_both (member_insert a M) H0).
      solve_meq.
    Qed.

    Lemma diff_MM_empty M : M - M =mul= empty.

    Proof. solve_meq. Qed.

    Lemma ins_meq_union M N P a :
      M + {{a}} =mul= N + P -> a in N -> M =mul= N - {{a}} + P.

    Proof.
      mset_unfold; try_solve_meq.
      assert (((x/M)%msets + (x/{{a}})%msets)%nat
              = ((x/N)%msets + (x/P)%msets)%nat).
      rewrite <- !union_mult.
      apply meq_multeq; trivial.
      case (eqA_dec x a); intro x_a.
      (* x =A= a *)
      assert (x/N = a/N).
      apply mult_eqA_compat; trivial.
      rewrite singleton_mult_in.
      assert (((x/M)%msets + 1)%nat = ((x/N)%msets + (x/P)%msets)%nat).
      rewrite <- (singleton_mult_in x_a); trivial.
      lia.
      trivial.
      (* ~ x =A= a *)
      rewrite (singleton_mult_notin x_a).
      assert (((x/M)%msets + 0)%nat = ((x/N)%msets + (x/P)%msets)%nat).
      rewrite <- (singleton_mult_notin x_a); trivial.
      lia.
    Qed.

    Lemma mem_memrem M a b : ~ a =A= b -> a in M -> a in (M - {{b}}).

    Proof.
      compute; intros.
      rewrite diff_mult.
      rewrite singleton_mult_notin.
      lia.
      trivial.
    Qed.

    Lemma member_notempty M x : x in M -> M <>mul empty.

    Proof.
      unfold not; intros.
      absurd (mult x M = 0).
      unfold member in H; lia.
      rewrite (meq_multeq H0); auto with multisets.
    Qed.

    Lemma singleton_notempty x : {{x}} <>mul empty.

    Proof. apply member_notempty with x. apply singleton_member. Qed.

    Lemma union_isempty M N : M + N =mul= empty -> M =mul= empty.

    Proof.
      intros; try_solve_meq.
      assert (((x/M)%msets + (x/N)%msets)%nat = x/empty).
      rewrite <- (meq_multeq H); auto with multisets.
      rewrite empty_mult in H0.
      lia.
    Qed.

    Lemma union_notempty M N : M <>mul empty -> M + N <>mul empty.

    Proof.
      compute in *; intros; apply H. apply union_isempty with N; trivial.
    Qed.

    Lemma remove_union a L R :
      a in L -> remove a (L + R) =mul= (remove a L) + R.
  
    Proof.
      intros.
      apply multeq_meq; intros.
      unfold remove.
      repeat (rewrite diff_mult || rewrite union_mult).
      destruct (eqA_dec x a).
      rewrite singleton_mult_in; trivial.
      rewrite (mult_eqA_compat L e).
      unfold member in H; lia.
      rewrite singleton_mult_notin; trivial.
      lia.
    Qed.

    Lemma meq_remove_elem_right a M L R :
      M + {{a}} =mul= L + R -> a in R -> M =mul= L + (remove a R).

    Proof.
      intros. rewrite (union_comm L (remove a R)), <- (remove_union L H0),
        (union_comm R L), <- H. solve_meq.
    Qed.

  End MultisetLemmas.

  #[global] Hint Immediate member_singleton
       member_member_union
       member_diff_member
       member_union
       member_meq_union
       union_comm
       intersection_comm
       union_assoc : multisets.

  #[global] Hint Resolve union_empty
       not_empty
       singleton_member
       meq_union_meq
       meq_meq_union
       meq_ins_ins_eq
       meq_ins_ins
       member_ins_ins_meq
       meq_ins_rem
       meq_diff_meq
       diff_MM_empty
       ins_meq_union
       mem_memrem
       member_union_r
       member_union_l
       member_notempty
       singleton_notempty
       union_isempty
       union_notempty : multisets.

  Section MultisetLemmas2.

    Lemma double_split L R U D :
      L + R =mul= U + D -> R =mul= (R # D) + (U - L).

    Proof.
      intros; try_solve_meq.
      assert (((x/L)%msets + (x/R)%msets)%nat
              = ((x/U)%msets + (x/D)%msets)%nat).
      rewrite <- (union_mult L R).
      rewrite <- (union_mult U D).
      auto with multisets.
      case (Compare_dec.le_lt_dec (x/L)%msets (x/U)%msets); intro l_u.
      (* u >= l *)
      assert ((x/R)%msets >= (x/D)%msets); [lia | idtac].
      rewrite (Nat.min_r (x/R)%msets (x/D)%msets); lia.
      (* l > u *)
      assert ((x/R)%msets < (x/D)%msets); [lia | idtac].
      rewrite (proj2 (Nat.sub_0_le _ _)).
      rewrite (Nat.min_l (x/R)%msets (x/D)%msets); lia.
      lia.
    Qed.

    Variables (P Q : A -> Prop) (PQ_dec : forall a, {P a}+{Q a}).

    Definition comp_eqA P := forall a b, a =A= b -> P a -> P b.

    Variables (P_comp : comp_eqA P) (Q_comp : comp_eqA Q).

    Lemma partition : forall M, exists Mp, exists2 Mq, M =mul= Mp + Mq
      & (forall p, p in Mp -> P p) /\ (forall q, q in Mq -> Q q).

    Proof.
      induction M using mset_ind.
      (* induction base *)
      exists empty; exists empty.
      solve_meq.
      split; intros.
      absurd (p in empty); eauto with multisets.
      absurd (q in empty); eauto with multisets.
      (* induction step *)
      decompose record IHM.
      case (PQ_dec a); intro wa.
      (* a goes to left part *)
      exists (x + {{a}}); exists x0.
      rewrite (union_perm x {{a}} x0); auto with multisets.
      split; intros.
      case (member_union H1); intro wp.
      apply H; trivial.
      assert (pa : a =A= p); [ auto with multisets sets
                             | apply (P_comp pa); trivial].
      apply H2; trivial.
      (* a goes to right part *)
      exists x; exists (x0 + {{a}}).
      rewrite (union_assoc x x0 {{a}}); auto with multisets.
      split; intros.
      apply H; trivial.
      case (member_union H1); intro wp.
      apply H2; trivial.
      assert (pa : a =A= q); [ auto with multisets sets
                             | apply (Q_comp pa); trivial].
    Qed.

  End MultisetLemmas2.

  Section List2Multiset.

    Lemma member_list_multiset : forall l,
      forall x, In x l -> member x (list2multiset l).

    Proof.
      induction l.
      (* base step *)
      intros x x_In_nil; absurd (In x nil); auto.
      (* induction step *)
      simpl; intros x x_In_al; case x_In_al.
      intro ax; rewrite ax; apply member_insert.
      intro x_In_l; mset_unfold.
      rewrite union_mult.
      assert ((x/(list2multiset l))%msets > 0).
      apply (IHl x); trivial.
      lia.
    Qed.

    Lemma member_multiset_list : forall l,
        forall x, member x (list2multiset l) -> exists2 y, In y l & x =A= y.

    Proof.
      induction l.
      (* base step *)
      simpl; intros x x_in_empty.
      absurd (empty <>mul empty); eauto with multisets.
      (* induction step *)
      unfold insert; simpl; intros x x_in_al.
      case (member_union x_in_al).
      intro x_a; exists a; auto with multisets.
      intro x_l; destruct (IHl x x_l).
      exists x0; auto with sets.
    Qed.

    Lemma list2multiset_app : forall M1 M2,
        list2multiset (M1 ++ M2) =mul= list2multiset M1 + list2multiset M2.

    Proof.
      induction M1; intros.
      (* induction base *)
      simpl.
      eauto with multisets.
      (* induction step *)
      simpl.
      unfold insert.
      rewrite (IHM1 M2).
      solve_meq.
    Qed.

    Lemma list2multiset_mult : forall l a,
        a / (list2multiset l) = multiplicity (list_contents eqA_dec l) a.

    Proof.
      induction l; intros.
      auto with multisets.
      simpl; unfold insert.
      rewrite union_mult.
      destruct (eqA_dec a a0).
      rewrite singleton_mult_in; auto with sets.
      rewrite singleton_mult_notin; auto with sets.
    Qed.

    Lemma meq_permutation l l' :
        list2multiset l =mul= list2multiset l' -> permutation eqA_dec l l'.
    
    Proof.
      intros; intro a. rewrite <- !list2multiset_mult.
      apply meq_multeq; trivial.
    Qed.

    Lemma permutation_meq l l' :
      permutation eqA_dec l l' -> list2multiset l =mul= list2multiset l'.
    
    Proof.
      intros. apply multeq_meq. intro x. rewrite !list2multiset_mult. apply H.
    Qed.

    Lemma list2multiset_eq_length l l' :
      list2multiset l =mul= list2multiset l' -> length l = length l'.
    
    Proof.
      intros.
      apply permutation_length with eqA eqA_dec.
      exact eqA_Equivalence.
      apply meq_permutation; trivial.
    Qed.

    Lemma list2multiset_cons_length l l' : forall a,
      list2multiset l + {{a}} =mul= list2multiset l' ->
      length l' = S (length l).
    
    Proof.
      destruct l'.
      simpl; intros.
      exfalso.
      apply not_empty with (list2multiset l + {{a}}) a; trivial.
      apply member_union_r; auto with multisets.    
      intros.
      change (S (length l)) with (length (a0 :: l)).
      apply permutation_length with eqA eqA_dec.
      exact eqA_Equivalence.
      apply meq_permutation.
      rewrite <- H.
      simpl; solve_meq.
    Qed.

    Lemma list2multiset_remove_in a : forall m,
        remove a (list2multiset m)
        =mul= list2multiset (removeElem eqA eqA_dec a m).
    
    Proof.
      induction m; simpl; intros.
      solve_meq.
      destruct (eqA_dec a a0); simpl.
      rewrite <- (insert_remove_eq (list2multiset m) e); auto with multisets.
      rewrite (insert_remove_noteq (list2multiset m) n).
      rewrite IHm; auto with multisets.
    Qed.

    Lemma diff_empty : forall l m,
        list2multiset l - list2multiset m =mul= empty ->
        (length l - length m = 0)%nat.
    
    Proof.
      induction l.
      auto.
      intros.
      simpl in H.
      destruct (insert_diff H).
      assert (length m > 0).        
      destruct (member_multiset_list m H0).
      destruct m.
      inversion H2.
      simpl; auto with arith.
      assert ((length l - pred (length m) = 0)%nat). 
      set (w := IHl (removeElem eqA eqA_dec a m)).
      rewrite removeElem_length_in in w.
      apply w.
      rewrite <- H1.
      rewrite (list2multiset_remove_in a m); auto with multisets.
      destruct (member_multiset_list m H0).
      exists x; split; trivial.
      destruct (length m); simpl in *; lia.
    Qed.

    Lemma list2multiset_union_length : forall l m n,
        list2multiset l =mul= list2multiset m + list2multiset n ->
        length l = (length m + length n)%nat.
    
    Proof.
      induction l; simpl; intros.
      destruct m.
      destruct n; trivial.
      exfalso; apply not_empty with (list2multiset (a::n)) a.
      simpl; unfold insert; auto with multisets.
      rewrite H; solve_meq.
      exfalso; apply not_empty with
                      (list2multiset (a::m) + list2multiset n) a.
      simpl; unfold insert; auto with multisets.
      rewrite H; solve_meq.    
      destruct (@member_union a (list2multiset m) (list2multiset n)).
      rewrite <- H; auto with multisets.
      unfold insert; apply member_union_l; auto with multisets.
      rewrite (IHl (removeElem eqA eqA_dec a m) n).
      rewrite (removeElem_length_in).
      destruct m; simpl; trivial.
      exfalso; apply not_empty with (list2multiset nil) a; trivial.
      simpl; auto with multisets.
      destruct (member_multiset_list m H0).
      exists x; split; trivial.
      rewrite <- (list2multiset_remove_in a m).
      rewrite <- (remove_union (list2multiset n) H0).
      apply insert_meq with a.
      assert (a in (list2multiset m + list2multiset n)).
      apply member_union_l; trivial.
      rewrite (meq_insert_remove H1); trivial.
      rewrite (IHl m (removeElem eqA eqA_dec a n)).
      rewrite (removeElem_length_in).
      destruct n; simpl; trivial.
      exfalso; apply not_empty with (list2multiset nil) a; trivial.
      simpl; auto with multisets.
      destruct (member_multiset_list n H0).
      exists x; split; trivial.
      rewrite <- (list2multiset_remove_in a n).
      rewrite (union_comm (list2multiset m) (remove a (list2multiset n))).
      rewrite <- (remove_union (list2multiset m) H0).
      apply insert_meq with a.
      assert (a in (list2multiset m + list2multiset n)).
      apply member_union_r; trivial.
      rewrite (union_comm (list2multiset n) (list2multiset m)).
      rewrite (meq_insert_remove H1); trivial.
    Qed.

    Lemma list2multiset_diff_length : forall l m n,
        list2multiset l =mul= list2multiset m - list2multiset n ->
        length l >= length m - length n.

    Proof.
      induction l.
      simpl; intros.
      rewrite (diff_empty m n); auto with multisets arith.
      intros; simpl.
      assert (length l >= length m - (length (a :: n))).
      apply IHl.
      simpl in H.
      rewrite (meq_remove H).
      simpl; solve_meq.
      simpl in H0; lia. 
    Qed.

    Lemma list2multiset_insert_nth a l p :
      list2multiset (insert_nth l p a) =mul= insert a (list2multiset l).
    
    Proof.
      intros.
      change (insert a (list2multiset l)) with (list2multiset (a :: l)).
      apply permutation_meq.
      apply insert_nth_permut.
    Qed.

  End List2Multiset.

  Section Multiset2List. (* William Delobel *)

    Definition mult_to_list : forall M, {l : list A | M =mul= list2multiset l}.

    Proof.
      induction M as [ | M a IHM] using mset_ind_type.
      (* base case *)
      exists (nil (A := A)).
      simpl; auto with multisets.
      (* induction step *)
      elim IHM; clear IHM; intros l IHM.
      exists (a::l).
      simpl; unfold insert; rewrite <- IHM; apply union_comm.
    Defined.
  
    Definition multiset2list M :=
      match mult_to_list M with @exist _ _ l _ => l end.
  
    Lemma multiset2list_empty : multiset2list empty = nil.

    Proof.
      unfold multiset2list.
      elim (mult_to_list empty).
      intros x Hx; destruct x as [ | a x]; trivial.
      gen (meq_sym Hx); clear Hx; intro Hx.
      gen (union_isempty Hx); clear Hx; intro Hx.
      elim (singleton_notempty Hx).
    Qed.
  
    Lemma double_convertion : forall M, list2multiset (multiset2list M) =mul= M.

    Proof.
      induction M as [ | M a IHM] using mset_ind.
      (* base case *)
      rewrite multiset2list_empty; simpl; auto with multisets.
      (* induction step *)
      unfold multiset2list; elim (mult_to_list (M + {{a}})).
      intros l Hl.
      rewrite Hl; auto with multisets.
    Qed.

  End Multiset2List.

  Section Multiset2List_Results.

    Lemma multiset2list_meq_non_empty : forall M,
      M <>mul empty -> multiset2list M <> nil.
    
    Proof.
      destruct M using mset_ind.
      auto with multisets.
      intros _.
      unfold multiset2list; elim (mult_to_list (M + {{a}})).
      destruct x; auto with datatypes.
      simpl; intro abs.
      absurd (M + {{a}} =mul= empty); trivial.
      apply member_notempty with a; trivial.
      apply member_union_r; auto with multisets.
    Qed.

    Lemma multiset2list_meq_empty : forall M,
        M =mul= empty -> multiset2list M = nil.
    
    Proof.
      destruct M using mset_ind.
      unfold multiset2list.
      elim (mult_to_list empty).
      destruct x; trivial.
      simpl; intro abs.
      absurd (insert a (list2multiset x) =mul= empty); auto with multisets.
      apply member_notempty with a; unfold insert; auto with multisets.
      intro abs.
      absurd (M + {{a}} =mul= empty); trivial.
      apply member_notempty with a; trivial.
      apply member_union_r; auto with multisets.
    Qed.

    Lemma in_multiset_in_multiset2list : forall M x,
        x in M -> exists y, x =A= y /\ In y (multiset2list M).
    
    Proof.
      destruct M using mset_ind.
      intros x abs.
      absurd (empty =mul= empty); auto with multisets.
      apply member_notempty with x; trivial.
      unfold multiset2list.
      elim (mult_to_list (M + {{a}})).
      intros l Ml x xin.
      assert (x in (list2multiset l)).
      rewrite <- Ml; trivial.
      destruct (member_multiset_list l H).
      exists x0; auto.
    Qed.

    Lemma in_multiset2list_in_multiset : forall M x,
        In x (multiset2list M) -> x in M.
    
    Proof.
      destruct M using mset_ind.
      rewrite multiset2list_empty.
      inversion 1.
      unfold multiset2list.
      destruct (mult_to_list (M + {{a}})) as [l Mal]; intros x xl.
      rewrite Mal.
      apply member_list_multiset; trivial.
    Qed.

    Lemma multiset2list_insert a M :
    exists a' p, a =A= a' /\
                 permutation eqA_dec (multiset2list M)
                             (drop_nth (multiset2list (insert a M)) p)
                 /\ nth_error (multiset2list (insert a M)) p = Some a'.
      
    Proof.
      unfold multiset2list; intros.
      destruct (mult_to_list M).
      destruct (mult_to_list (insert a M)).
      destruct (@member_multiset_list x0 a) as [a' a'x0 a'a].
      rewrite <- m0; apply member_insert.
      destruct (list_In_nth x0 a' a'x0) as [p x0p].
      exists a'; exists p; split; trivial; split; trivial.
      apply permutation_drop with a a'; trivial.
      exact eqA_Equivalence.
      apply meq_permutation.
      simpl.
      rewrite <- m; trivial.
    Qed.

    Lemma multiset2list_cons_length M a :
        length (multiset2list (M + {{a}})) = S (length (multiset2list M)).
    
    Proof.
      intros; unfold multiset2list.
      destruct (mult_to_list (M + {{a}})).
      destruct (mult_to_list M); simpl.
      apply list2multiset_cons_length with a.
      rewrite <- m0; trivial.
    Qed.

    Lemma multiset2list_union_length M N :
      length (multiset2list (M + N))
      = (length (multiset2list M) + length (multiset2list N))%nat.
    
    Proof.
      intros; unfold multiset2list.
      destruct (mult_to_list (M + N));
        destruct (mult_to_list M);
	destruct (mult_to_list N); simpl.    
      apply list2multiset_union_length.
      rewrite <- m; rewrite <- m0; rewrite <- m1; auto with multisets.
    Qed.

    Lemma multiset2list_diff_length M N :
      length (multiset2list (M - N))
      >= length (multiset2list M) - length (multiset2list N).
    
    Proof.
      intros; unfold multiset2list.
      destruct (mult_to_list (M - N));
        destruct (mult_to_list M);
	destruct (mult_to_list N); simpl.    
      apply list2multiset_diff_length.
      rewrite <- m; rewrite <- m0; rewrite <- m1; auto with multisets.
    Qed.

    Lemma multiset2list_meq_length M M' :
      M =mul= M' -> length (multiset2list M) = length (multiset2list M').
  
    Proof.
      intros; unfold multiset2list.
      destruct (mult_to_list M); destruct (mult_to_list M'); simpl.
      apply list2multiset_eq_length.
      rewrite <- m; rewrite <- m0; trivial.
    Qed.

    Lemma cons_eq_cons_cons_absurd a a' a'' M :
      {{a}} =mul= {{a'}} + {{a''}} + M -> False.
    
    Proof.
      intro.
      absurd ({{a}} =mul= insert a' (insert a'' M)); trivial.
      assert (M + {{a'}} + {{a''}} =mul= {{a}}).
      rewrite H; solve_meq.
      destruct (meq_cons H0) as [m' [am'a1 xa0m']].
      absurd (m' =mul= empty).
      intro mempty.
      apply not_empty with m' a'; trivial.
      unfold member; rewrite <- (meq_multeq xa0m' a').
      fold (member a' (M + {{a'}})).
      apply member_union_r; auto with multisets.
      apply (@singleton_mult_union_empty a a'' m').
      rewrite am'a1; auto with multisets.
      rewrite H; solve_meq.
    Qed.

    Lemma multiset2list_singleton a :
      exists a', a =A= a' /\ multiset2list {{a}} = a' :: nil.
    
    Proof.
      unfold multiset2list.
      destruct (mult_to_list {{a}}).
      destruct x; simpl in m.
      exfalso; apply not_empty with {{a}} a; trivial.
      unfold member; rewrite singleton_mult_in; auto with sets.
      destruct x; simpl in m.
      unfold insert in m.
      destruct (eqA_dec a a0).
      exists a0; split; trivial.
      exfalso.
      absurd (a/{{a}} = a/{{a0}}).
      rewrite singleton_mult_in with a a; auto with sets.
      rewrite singleton_mult_notin with a a0; auto with sets.
      apply meq_multeq.
      rewrite m; auto with multisets.
      exfalso.
      apply cons_eq_cons_cons_absurd with a a0 a1 (list2multiset x).
      rewrite m; solve_meq.
    Qed.

  End Multiset2List_Results.

  Section MultisetCardinality.
  
    Definition card_def (M : Multiset) : { n | length (multiset2list M) = n}.
  
    Proof.
      induction M as [ | M a IHM] using mset_ind_type.
      exists 0.
      rewrite multiset2list_empty; trivial.
      destruct IHM.
      exists (S x).
      rewrite multiset2list_cons_length; try_solve.
    Defined.

    Definition card (M : Multiset) := proj1_sig (card_def M).

    Lemma empty_card : card empty = 0.
  
    Proof.
      intros.
      unfold card.
      destruct (card_def empty); simpl.
      rewrite <- e.
      rewrite multiset2list_empty; trivial.
    Qed.

    Instance card_morph : Proper (meq ==> eq) card.
  
    Proof.
      intros m m0; unfold card.
      destruct (card_def m).
      destruct (card_def m0); simpl.
      rewrite <- e; rewrite <- e0.
      apply multiset2list_meq_length; trivial.
    Qed.

    Lemma multiset2list_card M : length (multiset2list M) = card M.
    
    Proof. intros. unfold card; destruct (card_def M); trivial. Qed.

    Lemma card_non_empty M : M <>mul empty -> card M > 0.
    
    Proof.
      intros.
      unfold card; destruct (card_def M); simpl.
      assert (w := multiset2list_meq_non_empty H).
      destruct (multiset2list M); try_solve.
      rewrite <- e; auto with arith.
    Qed.

    Lemma singleton_card x : card {{x}} = 1.
  
    Proof.
      unfold card.
      destruct (card_def {{x}}); simpl.
      rewrite <- e.
      destruct (multiset2list_singleton x) as [x' [_ xx']].
      rewrite xx'; trivial.
    Qed.

    Lemma pair_card x y : card {{x, y}} = 2.
  
    Proof.
      unfold card, pair, insert.
      destruct (card_def ({{x}} + {{y}})); simpl.
      rewrite <- e.
      rewrite multiset2list_cons_length.
      destruct (multiset2list_singleton x) as [x' [_ xx']].
      rewrite xx'; trivial.
    Qed.

    Lemma union_card M N : card (M + N) = (card M + card N)%nat.
  
    Proof.
      unfold card.
      destruct (card_def (M + N)); destruct (card_def M);
      destruct (card_def N); simpl.
      rewrite <- e; rewrite <- e0; rewrite <- e1.
      apply multiset2list_union_length.
    Qed.

    Lemma diff_card M N : card (M - N) >= card M - card N.

    Proof.
      unfold card.
      destruct (card_def (M - N)); destruct (card_def M);
      destruct (card_def N); simpl.
      rewrite <- e; rewrite <- e0; rewrite <- e1.
      apply multiset2list_diff_length.
    Qed.

  End MultisetCardinality.

  Section Pair.

    Lemma pair_eq a b c d :
      {{a, b}} =mul= {{c, d}} -> (a =A= c /\ b =A= d) \/ (a =A= d /\ b =A= c).
    
    Proof.
      intros.
      destruct (eqA_dec a c).
      destruct (eqA_dec b d).
      left; split; trivial.
      destruct (eqA_dec a d).
      absurd (mult b {{a, b}} = mult b {{c, d}}).
      unfold pair, insert.
      rewrite !union_mult.
      rewrite (@singleton_mult_in b b); auto with sets.
      rewrite (@singleton_mult_notin b a); eauto with sets.
      rewrite (@singleton_mult_notin b c); eauto with sets.
      rewrite (@singleton_mult_notin b d); [|eauto with sets].
      lia.
      setoid_replace c with d; eauto with sets.
      apply meq_multeq; trivial.
      absurd (mult d {{a, b}} = mult d {{c, d}}).
      unfold pair, insert.
      rewrite !union_mult.
      rewrite (@singleton_mult_notin d a); auto with sets.
      rewrite (@singleton_mult_notin d b); auto with sets.
      rewrite (@singleton_mult_in d d); auto with sets.
      lia.
      apply meq_multeq; trivial.
      destruct (eqA_dec a d).
      destruct (eqA_dec b c).
      right; split; trivial.
      absurd (mult c {{a, b}} = mult c {{c, d}}).
      unfold pair, insert.
      rewrite !union_mult.
      rewrite (@singleton_mult_notin c a); auto with sets.
      rewrite (@singleton_mult_notin c b); auto with sets.
      rewrite (@singleton_mult_in c c); auto with sets.

      apply meq_multeq; trivial.
      absurd (mult a {{a, b}} = mult a {{c, d}}).
      unfold pair, insert.
      rewrite !union_mult.
      rewrite (@singleton_mult_notin a c); auto with sets.
      rewrite (@singleton_mult_notin a d); auto with sets.
      rewrite (@singleton_mult_in a a); auto with sets.

      apply meq_multeq; trivial.
    Qed.

    Lemma pair_decomp a b X Y : {{a, b}} =mul= X + Y ->
      (X =mul= {{a, b}} /\ Y =mul= empty) \/
      (X =mul= empty /\ Y =mul= {{a, b}}) \/
      (X =mul= {{a}} /\ Y =mul= {{b}}) \/
      (X =mul= {{b}} /\ Y =mul= {{a}}).
    
    Proof.
      intros.
      destruct (empty_decomp_dec X) as [[[X1 c] X1c] | Xempty].
      simpl in X1c.
      destruct (empty_decomp_dec X1) as [[[X2 d] X2d] | X1empty].
      simpl in X2d.
      destruct (empty_decomp_dec X2) as [[[X3 e] X3e] | X2empty].
      simpl in X3e.
      absurd (card {{a, b}} = card (X + Y)).
      repeat (rewrite union_card; try rewrite (card_morph X1c); 
              try rewrite (card_morph X2d); try rewrite (card_morph X3e)).
      rewrite pair_card, !singleton_card; lia.
      apply (card_morph H).
      assert (Y =mul= empty).
      destruct (empty_decomp_dec Y) as [[[Y1 e] Y1e] | Yempty]; trivial.
      simpl in Y1e.
      absurd (card {{a, b}} = card (X + Y)).
      repeat (rewrite union_card; try rewrite (card_morph X1c); 
              try rewrite (card_morph X2d); try rewrite (card_morph Y1e)).
      rewrite pair_card, !singleton_card; lia.
      apply (card_morph H).
      left; split; trivial.
      rewrite H, X1c, X2d, X2empty, H0; solve_meq.    
      destruct (empty_decomp_dec Y) as [[[Y1 d] Y1d] | Yempty]; trivial.
      simpl in Y1d.
      destruct (empty_decomp_dec Y1) as [[[Y2 e] Y2e] | Y1empty]; trivial.
      simpl in Y2e.
      absurd (card {{a, b}} = card (X + Y)).
      repeat (rewrite union_card; try rewrite (card_morph X1c); 
              try rewrite (card_morph Y1d); try rewrite (card_morph Y2e)).
      rewrite pair_card, !singleton_card; lia.
      apply (card_morph H).
      destruct (@pair_eq a b c d) as [[ac bd] | [ad bc]].
      rewrite H, X1c, Y1d, X1empty, Y1empty; solve_meq.
      right; right; left; split.
      rewrite X1c, X1empty, ac; solve_meq.
      rewrite Y1d, Y1empty, bd; solve_meq.
      right; right; right; split.
      rewrite X1c, X1empty, bc; solve_meq.
      rewrite Y1d, Y1empty, ad; solve_meq.
      absurd (card {{a, b}} = card (X + Y)).
      repeat (rewrite union_card; try rewrite (card_morph X1c); 
              try rewrite (card_morph X1empty);
              try rewrite (card_morph Yempty)).
      rewrite pair_card, !singleton_card; lia.
      apply (card_morph H).
      destruct (empty_decomp_dec Y) as [[[Y1 c] Y1c] | Yempty]; trivial.
      simpl in Y1c.
      destruct (empty_decomp_dec Y1) as [[[Y2 d] Y2d] | Y1empty]; trivial.
      simpl in Y2d.
      destruct (empty_decomp_dec Y2) as [[[Y3 e] Y3e] | Y2empty]; trivial.
      simpl in Y3e.
      absurd (card {{a, b}} = card (X + Y)).
      repeat (rewrite union_card; try rewrite (card_morph Y1c); 
              try rewrite (card_morph Y2d); try rewrite (card_morph Y3e)).
      rewrite pair_card, !singleton_card; lia.
      apply (card_morph H).
      right; left; split; trivial.
      rewrite H, Y1c, Y2d, Y2empty, Xempty; solve_meq.
      absurd (card {{a, b}} = card (X + Y)).
      repeat (rewrite union_card; try rewrite (card_morph Xempty); 
              try rewrite (card_morph Y1c); try rewrite (card_morph Y1empty)).
      rewrite pair_card, !singleton_card; lia.
      apply (card_morph H).
      absurd (card {{a, b}} = card (X + Y)).
      repeat (rewrite union_card; try rewrite (card_morph Xempty); 
              try rewrite (card_morph Yempty)).
      rewrite pair_card; rewrite empty_card; lia.
      apply (card_morph H).    
    Qed.

  End Pair.

  #[global] Hint Immediate double_split : multisets.

(*COQ: At the moment I extended module Eqset to include the requirement of
decidable equality. Hence to instantiate multisets to Eqset module decidability
of multiset equality needs to be proven; or Eqset needs to be split to Eqset
and Eqset_dec, with the latter one introducing the requirement for decidable
equality. I tried to do just that but with the present pre-version of Coq 8.2
was getting error: "Anomaly: Not_found", so I abandoned this. At the moment
MultisetEqset is not used anywhere anyway.

Module MultisetEqset <: Eqset.

  Definition A := Multiset.
  Definition eqA := meq.
  Definition eqA_Equivalence := MultisetSetoidTheory.

End MultisetEqset.
*)

End Multiset.
