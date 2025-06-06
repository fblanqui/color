From Stdlib Require Import ZArith ZArithRing Ring_polynom Bool List FunInd Lia.
From CoLoR Require Import closure.

Function  all_coef_pos (p:Pol Z) : bool :=
  match p with 
    | Pc c => match Z.compare 0 c with 
                | Gt => false 
                | _ => true 
              end
    | Pinj _ p => all_coef_pos p
    | PX p _ q => andb (all_coef_pos p) (all_coef_pos q)
  end.


Function all_mem_pos (l:list Z) : Prop :=
  match l with
    | nil => True
    | c::l => (0<=c)%Z /\ all_mem_pos l
  end.
Open Scope Z_scope.

Import InitialRing.
Import BinList.
Functional Scheme jump_ind := Induction for jump Sort Prop.
Open Scope Z_scope.
Lemma all_mem_pos_def : forall l, (forall c, In c l -> 0<= c) <-> all_mem_pos l.
Proof.
intro l;split;intro H.
induction l. simpl. trivial.
simpl.
split.
apply H;simpl;auto.
apply IHl;intro;simpl in H;auto.
functional induction (all_mem_pos l).
simpl;tauto.
destruct H;simpl.
intros x H';simpl in H';destruct H'.
subst.
assumption.
auto.
Qed.


Lemma tail_in : forall A (l:list A) x, In x (tail l) -> In x l.
Proof.
  induction l.

  simpl;tauto.
  simpl.
  auto.
Qed.
Lemma jump_in : forall A n l (x:A), In x (jump n l) -> @In A x l.
Proof.
intros a n l;functional induction (jump n l).
intros;apply tail_in;eauto.
eauto.
intros;apply tail_in;auto.
Qed.

Lemma pos_expr_if_all_pos_aux : 
  forall (p:Pol Z), all_coef_pos p = true -> forall l, all_mem_pos l  -> 
    0<=Pphi  0 Zplus Zmult  (IDphi (R:=Z))  l p.
Proof.
  intros p;functional induction (all_coef_pos p).

  intro;discriminate.

  intros _. 
  simpl.
  destruct c;simpl in y;try discriminate;simpl;auto with zarith.
  unfold IDphi;auto with zarith.

  simpl.
  intros H l H0.
  apply IHb.
  exact H.
  rewrite <- all_mem_pos_def in H0|-*.
  intros c H1.
  apply H0.
  apply jump_in with _x;exact H1.

  simpl.
  intros H l H0.

  assert (0<=hd 0 l).
  clear - H0.
  induction l.
  simpl;lia.
  simpl.

  rewrite <- all_mem_pos_def in H0;simpl in H0;eauto.
  assert (0<= pow_pos Zmult (hd 0 l) _x).
  set (u:=hd 0 l) in *;clearbody u.
  clear - H1.
  induction _x.
  simpl;  auto with zarith.
  simpl;  auto with zarith.
  simpl;  auto with zarith.
assert (0 <=
   Pphi 0 Zplus Zmult (IDphi (R:=Z)) l p0).
apply IHb.
symmetry in H.
destruct (@andb_true_eq _ _ H);auto.
assumption.
assert (0<=Pphi 0 Zplus Zmult (IDphi (R:=Z)) (tail l) q).
apply IHb0.
symmetry in H;destruct (@andb_true_eq _ _ H);auto.
rewrite <- all_mem_pos_def in H0|-*.
  intros c H4;  apply H0;apply tail_in;exact H4.
auto with zarith.
Qed.
(*
Lemma pos_expr_if_all_pos_aux' : 
  forall (p:Pol Z), all_coef_pos p = true -> forall l, all_mem_pos l  -> 
    0<= @Pphi_dev _  0 1 Zplus Zmult Zminus Z.opp _ 0 1 Z.opp Z.eqb  (IDphi (R:=Z)) get_signZ  l p.
Proof.
  intros p H l H0.
  rewrite (@Ring_polynom.Pphi_dev_ok
    Z 0 1 Zplus Zmult Zminus Z.opp (@eq Z) InitialRing.Zsth InitialRing.Zeqe
    (@Rth_ARth _ _ _ _ _ _ _ _ InitialRing.Zsth InitialRing.Zeqe InitialRing.Zth)
    _ _ _ _ _ _ _ _ (IDphi (R:=Z))
    (@IDmorph _ _ _ _ _ _ _ _  InitialRing.Zsth Z.eqb InitialRing.Zeqb_ok) 
  ).
  apply pos_expr_if_all_pos_aux;assumption.
  constructor.
  destruct c;simpl;try (intros;discriminate).
  intros c H1;injection H1;intro;subst. unfold IDphi; reflexivity.
Qed.
*)

Lemma Zeq_bool_eq : forall x y : Z, (x =? y) = true -> x = y.
Proof. intros x y xy. apply Z.eqb_eq. exact xy. Qed.

Lemma pos_expr_if_all_pos_aux' : 
  forall (p:Pol Z), all_coef_pos p = true -> forall l, all_mem_pos l  -> 
    0<= 
    @Pphi_pow _  0 1 Zplus Zmult Zminus Z.opp _ 0 1 Z.eqb  
    (IDphi (R:=Z)) _ Z_of_N Zpower  get_signZ  l p.
Proof.
  intros p H l H0.
  replace ( @Pphi_pow _  0 1 Zplus Zmult Zminus Z.opp _ 0 1 Z.eqb  (IDphi (R:=Z)) _ Z_of_N Zpower get_signZ l p)
    with (Pphi 0 Zplus Zmult (@IDphi Z) l p).
  apply pos_expr_if_all_pos_aux;assumption.
  symmetry;eapply Pphi_pow_ok with (1:=InitialRing.Zsth) (C:= Z).
  exact  InitialRing.Zeqe.
  exact (@Rth_ARth _ _ _ _ _ _ _ _ InitialRing.Zsth InitialRing.Zeqe InitialRing.Zth).
  eexact  (@IDmorph Z Z0 1 Zplus Zmult Zminus Z.opp _  InitialRing.Zsth Z.eqb Zeq_bool_eq).
  exact Zpower_theory.
  apply get_signZ_th.
Qed.


Lemma pos_expr_if_all_pos' : 
  forall pe, 
    all_coef_pos 
    (norm_subst 0 1 Zplus Zmult Zminus Z.opp Z.eqb Z.div_eucl ring_subst_niter nil pe) = true -> 
    forall l, all_mem_pos l  -> 
    0<= (PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z)) Z_of_N Zpower l pe) .
Proof.
  intros p H l H0.
  rewrite Zr_ring_lemma2 with 
    (n:=ring_subst_niter) (lH:=@nil (PExpr Z * PExpr Z)) 
    (l:=l) 
    (lmp:=@nil (Z*Mon * Pol Z)) 
    (pe:=p) 
    (npe:=
      norm_subst 0 1 Zplus Zmult Zminus Z.opp Z.eqb Z.div_eucl ring_subst_niter nil
        p).
  apply pos_expr_if_all_pos_aux';assumption.
  vm_compute;exact I.
  vm_compute;reflexivity.
  reflexivity.
Qed.


Lemma pos_expr_if_all_pos : 
  forall pe1 pe2, 
    all_coef_pos (
      norm_subst 0 1 Zplus Zmult Zminus Z.opp Z.eqb Z.div_eucl ring_subst_niter
        nil (PEsub pe2  pe1)
    ) = true -> 
    forall l, all_mem_pos l  -> 
      PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z)) Z_of_N Zpower l pe1 <=  
    PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z)) Z_of_N Zpower l pe2 .
Proof.
  intros pe1 pe2 H l H0.
  assert (0<= PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z)) Z_of_N Zpower l (PEsub pe2 pe1)).
  apply pos_expr_if_all_pos'.
  assumption.
  assumption.
  simpl in H1;auto with zarith.
Qed.


Lemma jump_nil : forall p, jump p (@nil Z) = nil .
Proof.
  induction p;simpl.

  do 2 rewrite IHp;reflexivity.

  do 2 rewrite IHp;reflexivity.

  reflexivity.
Qed.

Lemma Pphi_nil : forall p, 
  Pphi 0 Zplus Zmult (IDphi (R:=Z)) nil p = 
  match p with 
    | Pc c => c 
    | Pinj _ p => Pphi 0 Zplus Zmult (IDphi (R:=Z)) nil p
    | PX _ _ p => Pphi 0 Zplus Zmult (IDphi (R:=Z)) nil p
  end.
Proof.
destruct p.

simpl;unfold IDphi;reflexivity.

simpl.
rewrite jump_nil;reflexivity.
simpl.

replace (pow_pos Zmult 0 p2) with 0.
ring.
clear; induction p2; simpl.
1, 3: reflexivity.
rewrite <- IHp2;reflexivity.
Qed.


Function all_mem_bounded (l:list (Z*Z)) : Prop :=
  match l with
    | nil => True
    | (b,z)::l => (b<=z)%Z /\ all_mem_bounded l
  end.



Lemma tail_length : forall A (l1 l2:list A), length l1 = length l2 -> 
  length (tail l1) = length (tail l2).
Proof.
  induction l1 as [|x l1];destruct l2 as [|y l2];intros Hlength;simpl in Hlength;
    try discriminate Hlength;simpl;auto.
Qed.


Lemma jump_length : forall A n (l1 l2:list A), length l1 = length l2 -> 
  length (jump n l1) = length (jump n l2).
Proof.
  intros A n l1;functional induction (jump n l1);  simpl;  intros l2 Hlength.

  apply IHl0;  apply IHl;  apply tail_length; apply Hlength.
  apply IHl0;  apply IHl;   apply Hlength.
  apply tail_length; apply Hlength.
Qed.

Lemma all_mem_pos_tail : forall (l:list Z), all_mem_pos l -> 
  all_mem_pos (tail l).
Proof. 
  intros l; functional induction all_mem_pos l. 
  vm_compute;trivial.
  inversion 1;auto.
Qed.

Lemma all_mem_pos_jump : forall n (l:list Z), all_mem_pos l -> 
  all_mem_pos (jump n l).
Proof.
  intros n l;functional induction (jump n l);simpl;intros Hmem.
  apply IHl1;apply IHl0;apply all_mem_pos_tail; apply Hmem.
  apply IHl1;apply IHl0;apply Hmem.
  apply all_mem_pos_tail; apply Hmem.
Qed.

Functional Scheme combine_ind := Induction for combine Sort Prop.


Lemma combine_tail : forall A (l1 l2: list A), 
  combine (tail l1) (tail l2) =  tail (combine l1 l2).
Proof.
  intros A l1 l2;functional induction (combine l1 l2).
  vm_compute;reflexivity.
  simpl;destruct tl; reflexivity.
  simpl;reflexivity.
Qed.

Lemma combine_jump : forall A n (l1 l2: list A), 
  combine (jump n l1) (jump n l2) =  jump n (combine l1 l2).
Proof.
  intros A n l1;functional induction (jump n l1);simpl;intros l2.
  rewrite IHl0;rewrite IHl;rewrite combine_tail;reflexivity.
  rewrite IHl0;rewrite IHl;reflexivity.
  rewrite combine_tail;reflexivity.
Qed.


Lemma all_mem_bounded_tail : forall (l:list (Z*Z)), all_mem_bounded l -> 
  all_mem_bounded (tail l).
Proof.
  intros l;functional induction (all_mem_bounded l);simpl.
  trivial.
  inversion 1;auto.
Qed.


Lemma all_mem_bounded_jump : forall n (l:list (Z*Z)), all_mem_bounded l -> 
  all_mem_bounded (jump n l).
Proof.
  intros n l;functional induction (jump n l);simpl;intros H.
  apply IHl1;apply IHl0;apply all_mem_bounded_tail;apply H.
  apply IHl1;apply IHl0;apply H.
  apply all_mem_bounded_tail;apply H.
Qed.


Lemma all_mem_pos_all_mem_bounded : 
  forall l1 l2, length l1 = length l2 -> all_mem_pos l1 -> 
    all_mem_bounded (combine l1 l2) -> all_mem_pos l2.
Proof.
  intros l1 l2;functional induction (combine l1 l2).
  destruct l';intros Hlength;try discriminate;tauto.
  intros abs;discriminate.
  intros Hlength;injection Hlength;clear Hlength;intro Hlength;simpl in *; inversion 1;
    inversion 1;auto with zarith.
Qed.

Lemma Zmult_compat : forall n m, 0<=n -> 0<n*m -> 0<n /\ 0<m.
Proof.
  intros.
  case (Z_lt_le_dec 0 n).
  intros H'.
  replace 0 with (0*n) in H0 by ring;
  replace (n*m) with (m*n) in H0 by ring;
  generalize (Zmult_gt_0_lt_reg_r _ _ _ (Z.lt_gt _ _ H') H0);auto.
  intro;  assert (n=0) by lia.
  subst;simpl in H0.
  lia.
Qed.

Functional Scheme pow_pos_ind := Induction for pow_pos Sort Prop.

Lemma pow_pos_pos : forall z p, 0<=z -> 0<= pow_pos Zmult z p .
Proof.
intros z p;functional induction  (pow_pos Zmult z p);
auto with zarith.
Qed.

Lemma pow_pos_strict_pos : forall z p, 0<z -> 0< pow_pos Zmult z p .
Proof.
intros z p; functional induction  (pow_pos Zmult z p). 3: easy.

intros.
apply Zmult_lt_0_compat;auto.
apply Zmult_lt_0_compat;auto.

intros.
apply Zmult_lt_0_compat;auto.
Qed.

Lemma pow_pos_monotonic : 
  forall p z1 z2, 0<=z1<=z2 -> pow_pos Zmult z1 p <= pow_pos Zmult z2 p.
Proof.
  intros p z1 z2 z1_le_z2.
  functional induction (pow_pos Zmult z1 p);simpl in *.
  destruct z1_le_z2 as [le_z1 z1_le_z2].

  apply Zmult_le_compat;try assumption.
  apply Zmult_le_compat;try assumption.
  apply pow_pos_pos;auto with zarith.
  apply pow_pos_pos;auto with zarith.
  apply Zmult_le_0_compat;apply pow_pos_pos;auto with zarith.

  apply Zmult_le_compat;try assumption.
  apply pow_pos_pos;auto with zarith.
  apply pow_pos_pos;auto with zarith.

  
  auto with zarith.
Qed.






Lemma strict_pos_expr_if_all_pos_aux : 
  forall (p:Pol Z), all_coef_pos p = true -> forall lb, all_mem_pos lb  -> 
    forall lz, length lb = length lz -> all_mem_bounded (combine lb lz) ->
    0 < Pphi  0 Zplus Zmult  (IDphi (R:=Z)) lb p ->
    0< Pphi 0 Zplus Zmult  (IDphi (R:=Z))  lz p.
Proof.

  induction p.

  
  intros H lb H0 lz H1 H2 H3;tauto.

  simpl. intros Hp0 lb lb_pos lz Hlength lb_lz H.
  apply IHp with (jump p lb);try assumption.
  apply all_mem_pos_jump;exact lb_pos.
  apply jump_length;exact Hlength.
  rewrite combine_jump;apply all_mem_bounded_jump;exact lb_lz.


  simpl. intros Hp1_p3 lb lb_pos lz Hlength lb_lz H.
  assert(h1:0<=pow_pos Zmult (hd 0 lb) p2).
  destruct lb.
  simpl; clear;  induction p2; simpl; auto with zarith.
  simpl. simpl in lb_pos. destruct lb_pos.
  clear - H0.
  induction p2; simpl; auto with zarith.
  assert (h2:0<=Pphi 0 Zplus Zmult (IDphi (R:=Z)) lb p1).
  apply  pos_expr_if_all_pos_aux.
  symmetry in Hp1_p3;destruct (@andb_true_eq _ _ Hp1_p3);auto.
  exact lb_pos.
  assert (h3:0<=Pphi 0 Zplus Zmult (IDphi (R:=Z)) lb p1 * pow_pos Zmult (hd 0 lb) p2).
  auto with zarith.
  assert(h4:(0<Pphi 0 Zplus Zmult (IDphi (R:=Z)) (tail lb) p3)\/0<Pphi 0 Zplus Zmult (IDphi (R:=Z)) lb p1 * pow_pos Zmult (hd 0 lb) p2).
  case(Zle_lt_or_eq _ _ h3).
  auto.
  intro Heq;rewrite <- Heq in H;simpl in H;auto.
  assert(h5:0<=pow_pos Zmult (hd 0 lz) p2).
  destruct lz.
  simpl; clear;  induction p2; simpl; auto with zarith.
  simpl. 
  destruct lb;try discriminate. 
  simpl in lb_pos. destruct lb_pos.
  simpl in lb_lz;destruct lb_lz.
  assert (0<= z) by auto with zarith.
  clear - H4.
  induction p2; simpl; auto with zarith.
  assert (h6:0<=Pphi 0 Zplus Zmult (IDphi (R:=Z)) lz p1).
  apply  pos_expr_if_all_pos_aux.
  symmetry in Hp1_p3;destruct (@andb_true_eq _ _ Hp1_p3);auto.
  apply  all_mem_pos_all_mem_bounded with lb. exact Hlength. exact lb_pos.
  exact lb_lz.
  assert (h7:0<=Pphi 0 Zplus Zmult (IDphi (R:=Z)) lz p1 * pow_pos Zmult (hd 0 lz) p2).
  auto with zarith.
  case h4;clear h4;intro h4.

  assert (h8:0< Pphi 0 Zplus Zmult (IDphi (R:=Z)) (tail lz) p3).
  apply IHp2 with (tail lb).
  symmetry in Hp1_p3;destruct (@andb_true_eq _ _ Hp1_p3);auto.
  apply all_mem_pos_tail;exact lb_pos.
  apply tail_length;exact Hlength.
  rewrite combine_tail;apply all_mem_bounded_tail;exact lb_lz.
  exact h4.
  auto with zarith.


  destruct (Zmult_compat _ _ h2 h4) as [h8 h9];clear h4.
  assert (h10:0 < Pphi 0 Zplus Zmult (IDphi (R:=Z)) lz p1).
  apply IHp1 with lb.
  symmetry in Hp1_p3;destruct (@andb_true_eq _ _ Hp1_p3);auto.
  exact lb_pos.
  exact Hlength.
  exact lb_lz.
  exact h8.

  assert (h11: 0 < pow_pos Zmult (hd 0 lz) p2).
  destruct lz.
  clear -  h9 Hlength lb_lz.
  destruct lb;try discriminate.
  simpl in h9|-*.
  clear - h9;
    apply False_ind.
  replace  (pow_pos Zmult 0 p2) with 0 in *.
  lia.
  clear.
  induction p2;simpl.
  1, 3: reflexivity.
  rewrite <- IHp2;ring.
  simpl.
  clear -  h9 Hlength lb_pos lb_lz.
  destruct lb;try discriminate.
  simpl in h9,lb_lz,lb_pos|-*.



  destruct lb_lz as [h _].
  destruct lb_pos as [h1 _].
  clear - h h1 h9.
  apply Z.lt_le_trans with (pow_pos Zmult z0 p2).
  assumption.
  apply pow_pos_monotonic;auto with zarith.
  assert (0 <
   Pphi 0 Zplus Zmult (IDphi (R:=Z)) lz p1 * pow_pos Zmult (hd 0 lz) p2).
  apply Zmult_lt_0_compat;assumption.
  assert ( 0<=Pphi 0 Zplus Zmult (IDphi (R:=Z)) (tail lz) p3).
  apply pos_expr_if_all_pos_aux.
  symmetry in Hp1_p3;destruct (@andb_true_eq _ _ Hp1_p3);auto.
  apply all_mem_pos_tail. apply all_mem_pos_all_mem_bounded with lb; assumption.
  lia.
Defined.


Lemma strict_pos_expr_if_all_pos_aux' : 
  forall (p:Pol Z), all_coef_pos p = true -> forall lb, all_mem_pos lb  -> 
    forall lz, length lb = length lz -> all_mem_bounded (combine lb lz) -> 
    0<  @Pphi_pow _  0 1 Zplus Zmult Zminus Z.opp _ 0 1 Z.eqb  (IDphi (R:=Z)) _ Z_of_N Zpower  (get_signZ)  lb p ->
    0<  @Pphi_pow _  0 1 Zplus Zmult Zminus Z.opp _ 0 1 Z.eqb  (IDphi (R:=Z)) _ Z_of_N Zpower  (get_signZ)  lz p.
Proof.
  intros p H lb H0 lz H1 H2.
 replace ( @Pphi_pow _  0 1 Zplus Zmult Zminus Z.opp _ 0 1 Z.eqb  (IDphi (R:=Z)) _ Z_of_N Zpower  (get_signZ)  lb p)
    with (Pphi 0 Zplus Zmult (@IDphi Z) lb p).
 replace (Pphi_pow 0 1 Zplus Zmult Zminus Z.opp 0 1 Z.eqb 
     (IDphi (R:=Z)) Z_of_N Zpower (get_signZ) lz p)
    with (Pphi 0 Zplus Zmult (@IDphi Z) lz p).
 intro.
 apply strict_pos_expr_if_all_pos_aux with lb;assumption.
 symmetry;eapply Pphi_pow_ok with (1:=InitialRing.Zsth) (C:= Z).
  exact  InitialRing.Zeqe.
  exact (@Rth_ARth _ _ _ _ _ _ _ _ InitialRing.Zsth InitialRing.Zeqe InitialRing.Zth).
  eexact  (@IDmorph Z Z0 1 Zplus Zmult Zminus Z.opp _  InitialRing.Zsth Z.eqb Zeq_bool_eq).
  exact Zpower_theory.
  apply get_signZ_th.
 symmetry;eapply Pphi_pow_ok with (1:=InitialRing.Zsth) (C:= Z).
  exact  InitialRing.Zeqe.
  exact (@Rth_ARth _ _ _ _ _ _ _ _ InitialRing.Zsth InitialRing.Zeqe InitialRing.Zth).
  eexact  (@IDmorph Z Z0 1 Zplus Zmult Zminus Z.opp _  InitialRing.Zsth Z.eqb Zeq_bool_eq).
  exact Zpower_theory.
  apply get_signZ_th.
Qed.

Lemma strict_pos_expr_if_all_pos' : 
  forall pe, all_coef_pos (norm_subst 0 1 Zplus Zmult Zminus Z.opp Z.eqb Z.div_eucl ring_subst_niter nil pe) = true -> 
    forall lb, all_mem_pos lb  -> 
      forall lz, length lb = length lz -> all_mem_bounded (combine lb lz) ->
      0 < PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z)) Z_of_N Zpower lb pe -> 
      0< ( PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z)) Z_of_N Zpower lz pe) .
Proof.
  intros pe H lb lb_pos lz Hlength Hlb_lz.


  rewrite Zr_ring_lemma2 with (n:=ring_subst_niter) (lH:=@nil (PExpr Z * PExpr Z))  
    (lmp:=@nil (Z*Mon * Pol Z)) (pe:=pe) (npe:=norm_subst 0 1 Zplus Zmult Zminus Z.opp Z.eqb Z.div_eucl ring_subst_niter nil
      pe).
  rewrite Zr_ring_lemma2 with (n:=ring_subst_niter) (lH:=@nil (PExpr Z * PExpr Z))  
    (lmp:=@nil (Z*Mon * Pol Z)) (pe:=pe) (npe:=norm_subst 0 1 Zplus Zmult Zminus Z.opp Z.eqb Z.div_eucl ring_subst_niter nil
      pe).
  apply strict_pos_expr_if_all_pos_aux';assumption.
  vm_compute;exact I.
  vm_compute;reflexivity.
  reflexivity.
  vm_compute;exact I.
  vm_compute;reflexivity.
  reflexivity.
Qed.

Lemma strict_pos_expr_if_all_pos :   forall pe1 pe2, 
  all_coef_pos (norm_subst 0 1 Zplus Zmult Zminus Z.opp Z.eqb Z.div_eucl ring_subst_niter nil  (PEsub pe2 pe1)) = true -> 
  forall lb, all_mem_pos lb -> 
    forall lz, length lb = length lz -> all_mem_bounded (combine lb lz) ->
      PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z))  Z_of_N Zpower lb pe1 < 
      PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z))  Z_of_N Zpower lb pe2 -> 
      PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z))  Z_of_N Zpower lz pe1 < 
      ( PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z))  Z_of_N Zpower lz pe2) .
Proof.
  intros pe1 pe2 H lb H0 lz H1 H2 H3.


  assert (0<  PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z))  Z_of_N Zpower lz pe2  -
    PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z))  Z_of_N Zpower lz pe1).
  replace (PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z))  Z_of_N Zpower lz pe2  -
    PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z))  Z_of_N Zpower lz pe1) with 
  (PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z))  Z_of_N Zpower lz (PEsub pe2  pe1)) by (vm_compute;reflexivity).
  apply strict_pos_expr_if_all_pos' with lb.
  assumption.
  assumption. 
  assumption.
  assumption.
  simpl. auto with zarith.
  auto with zarith.
Qed.

Function all_le (l1 l2:list Z) {struct l1}: Prop := 
  match l1 with 
    | nil => 
      match l2 with 
        | nil => True 
        | _ => False
      end
    | x::l1 => 
      match l2 with 
        | nil => False 
        | y::l2 => 
          x <= y /\ all_le l1 l2
      end
  end
.

Lemma all_le_def : forall l1 l2, all_le l1 l2 <-> (length l1 = length l2 /\ forall x y, In (x,y) (combine l1 l2) -> x <= y).
Proof.
intros l1 l2;functional induction (all_le l1 l2).

simpl;tauto.

simpl.
destruct l2.
split;try tauto.
split;try tauto.
simpl;inversion 1;discriminate.

simpl.
split;try tauto.
simpl;inversion 1;discriminate.


simpl.
destruct IHP as [lhs rhs].
split.
intros [H1 H2]. 
destruct (lhs H2) as [Heq Hforall];split.
f_equal.
exact Heq.
intros x' y' [h|h].
injection h;clear h;intros;subst;exact H1.
auto.



clear lhs.
intros [H1 H2].
split;auto.
Qed.

Lemma jump_combine : 
  forall A n (l1 l2:list A), jump n (combine l1 l2) = combine (jump n l1) (jump n l2).
Proof.

  induction n;  simpl.
  
  intros l1 l2.
  do 2 rewrite <- IHn.
  do 2 f_equal.
  destruct l1;destruct l2;simpl;try reflexivity.
  destruct l1;simpl;  reflexivity.

  intros l1 l2.
  do 2 rewrite <- IHn.
  do 2 f_equal.

  intros l1 l2.
  destruct l1;destruct l2;simpl;try reflexivity.
  destruct l1;simpl;  reflexivity.
Qed.


Lemma pos_pol_incr : 
  forall (p:Pol Z), all_coef_pos p = true -> 
    forall l1 l2, all_le l1 l2  -> all_mem_pos l1 -> 
     0<=Pphi  0 Zplus Zmult  (IDphi (R:=Z))  l1 p <= Pphi  0 Zplus Zmult  (IDphi (R:=Z))  l2 p.
Proof.
  intros p;functional induction (all_coef_pos p).
(**)
  intro;discriminate.
(**)
  intros _. 
  simpl.
  destruct c;simpl in y;try discriminate;simpl;split;unfold IDphi;auto with zarith.
(**)
  simpl.
  intros H l1 l2 H0 H1.
  apply IHb.
  exact H.
  rewrite  all_le_def in H0|-*.
  destruct H0 as [Hlength Hforall].
  split.
  apply jump_length;exact Hlength.
  intros x y H0;apply Hforall;apply jump_in with _x. 
  rewrite jump_combine;assumption.
  rewrite <- all_mem_pos_def in H1|-*.
  intros c H2;apply H1;apply jump_in with _x;assumption.
(**)
  simpl.
  intros H l1 l2 H0 H1.
  assert (0<=pow_pos Zmult (hd 0 l1) _x <= pow_pos Zmult (hd 0 l2) _x).
  destruct l1;destruct l2;simpl in H0;try tauto;simpl;auto with zarith.
  clear;induction _x;simpl;auto with zarith.

  destruct H0.
  simpl in H1;destruct H1 as [ H1 _ ].
  clear - H0 H1. 
  assert (0<=z0);auto with zarith.
  generalize dependent z0;generalize dependent z.
  induction _x;simpl;intros.
  assert (0<=pow_pos Zmult z _x) by (clear -H1;induction _x;simpl;auto with zarith).
  assert (z*pow_pos Zmult z _x <= z0 * pow_pos Zmult z0 _x).
    destruct (IH_x _ H1 _ H0 H);apply Z.le_trans with (z0*pow_pos Zmult z _x);
      auto with zarith.
    split.
    auto with zarith.
    destruct (IH_x _ H1 _ H0 H).
    do 2 rewrite Zmult_assoc.
    apply Z.le_trans with (z*pow_pos Zmult z _x * pow_pos Zmult z0 _x);auto with zarith.

    destruct (IH_x _ H1 _ H0 H).     
    split;auto with zarith.
  assert (0<= pow_pos Zmult z0 _x).
  apply Z.le_trans with (pow_pos Zmult z _x);auto with zarith.
  apply Z.le_trans with (pow_pos Zmult z _x*pow_pos Zmult z0 _x);auto with zarith.
  auto with zarith.

assert (0 <= Pphi 0 Zplus Zmult (IDphi (R:=Z)) l1 p0 <= Pphi 0 Zplus Zmult (IDphi (R:=Z)) l2 p0).
apply IHb.
symmetry in H.
destruct (@andb_true_eq _ _ H);auto.
assumption.
assumption.
assert (0<=Pphi 0 Zplus Zmult (IDphi (R:=Z)) (tail l1) q <= Pphi 0 Zplus Zmult (IDphi (R:=Z)) (tail l2) q).
apply IHb0.
symmetry in H;destruct (@andb_true_eq _ _ H);auto.
destruct l1;destruct l2;simpl in H0;simpl;auto;try tauto.
rewrite <- all_mem_pos_def in H1|-*.
  intros c H4;  apply H1;apply tail_in;exact H4.
destruct H2;destruct H3;destruct H4;split;auto with zarith.
assert (0<=Pphi 0 Zplus Zmult (IDphi (R:=Z)) l2 p0) by 
  (apply Z.le_trans with (Pphi 0 Zplus Zmult (IDphi (R:=Z)) l1 p0);auto with zarith).
assert (0<=Pphi 0 Zplus Zmult (IDphi (R:=Z)) (tail l2) q) by 
  (apply Z.le_trans with (Pphi 0 Zplus Zmult (IDphi (R:=Z)) (tail l1) q);auto with zarith).
assert (0 <= pow_pos Zmult (hd 0 l2) _x) by 
  (apply Z.le_trans with (pow_pos Zmult (hd 0 l1) _x);auto with zarith).
assert (Pphi 0 Zplus Zmult (IDphi (R:=Z)) l1 p0 * pow_pos Zmult (hd 0 l1) _x <= 
  Pphi 0 Zplus Zmult (IDphi (R:=Z)) l2 p0 * pow_pos Zmult (hd 0 l2) _x) 
by (apply Z.le_trans with (Pphi 0 Zplus Zmult (IDphi (R:=Z)) l2 p0 * pow_pos Zmult (hd 0 l1) _x);auto with zarith).
auto with zarith.
Qed.

Lemma pos_pol_incr' : 
  forall (p:Pol Z), all_coef_pos p = true -> 
    forall l1 l2, all_le l1 l2  -> all_mem_pos l1 -> 
     0<=@Pphi_pow _  0 1 Zplus Zmult Zminus Z.opp _ 0 1  Z.eqb  (IDphi (R:=Z)) _ Z_of_N Zpower  (get_signZ) l1 p <= 
     @Pphi_pow _  0 1 Zplus Zmult Zminus Z.opp _ 0 1  Z.eqb  (IDphi (R:=Z)) _ Z_of_N Zpower  (get_signZ) l2 p.
Proof.
  intros p H l1 l2 H0 H1.
 replace (@Pphi_pow _  0 1 Zplus Zmult Zminus Z.opp _ 0 1 Z.eqb  (IDphi (R:=Z)) _ Z_of_N Zpower  (get_signZ)  l1 p)
    with (Pphi 0 Zplus Zmult (@IDphi Z) l1 p).
 replace (Pphi_pow 0 1 Zplus Zmult Zminus Z.opp 0 1 Z.eqb 
     (IDphi (R:=Z)) Z_of_N Zpower (get_signZ) l2 p)
    with (Pphi 0 Zplus Zmult (@IDphi Z) l2 p).
 apply pos_pol_incr;assumption.
 symmetry;eapply Pphi_pow_ok with (1:=InitialRing.Zsth) (C:= Z).
  exact  InitialRing.Zeqe.
  exact (@Rth_ARth _ _ _ _ _ _ _ _ InitialRing.Zsth InitialRing.Zeqe InitialRing.Zth).
  eexact  (@IDmorph Z Z0 1 Zplus Zmult Zminus Z.opp _  InitialRing.Zsth Z.eqb Zeq_bool_eq).
  exact Zpower_theory.
  apply get_signZ_th.  
 symmetry;eapply Pphi_pow_ok with (1:=InitialRing.Zsth) (C:= Z).
  exact  InitialRing.Zeqe.
  exact (@Rth_ARth _ _ _ _ _ _ _ _ InitialRing.Zsth InitialRing.Zeqe InitialRing.Zth).
  eexact  (@IDmorph Z Z0 1 Zplus Zmult Zminus Z.opp _  InitialRing.Zsth Z.eqb Zeq_bool_eq).
  exact Zpower_theory.
  apply get_signZ_th.
Qed.

Lemma pos_expr_incr_aux :   
  forall pe, 
  all_coef_pos (norm_subst 0 1 Zplus Zmult Zminus Z.opp Z.eqb Z.div_eucl ring_subst_niter nil  pe) = true -> 
  forall l1 l2, all_le l1 l2 -> all_mem_pos l1 -> 
    0 <=  PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z))  Z_of_N Zpower l1 pe 
    <= ( PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z))  Z_of_N Zpower l2 pe) .
Proof.
  intros pe H l1 l2 H0 H1.
  
  rewrite Zr_ring_lemma2 with (n:=ring_subst_niter) (lH:=@nil (PExpr Z * PExpr Z))  
    (lmp:=@nil (Z * Mon * Pol Z)) (pe:=pe) (npe:=norm_subst 0 1 Zplus Zmult Zminus Z.opp Z.eqb Z.div_eucl ring_subst_niter nil
      pe).
  rewrite Zr_ring_lemma2 with (n:=ring_subst_niter) (lH:=@nil (PExpr Z * PExpr Z))  
    (lmp:=@nil (Z* Mon * Pol Z)) (pe:=pe) (npe:=norm_subst 0 1 Zplus Zmult Zminus Z.opp Z.eqb Z.div_eucl ring_subst_niter nil
      pe).
  apply pos_pol_incr';assumption.
  vm_compute;exact I.
  vm_compute;reflexivity.
  reflexivity.
  vm_compute;exact I.
  vm_compute;reflexivity.
  reflexivity.
Qed.

Lemma pos_expr_incr :   
  forall pe, 
  all_coef_pos (norm_subst 0 1 Zplus Zmult Zminus Z.opp Z.eqb Z.div_eucl ring_subst_niter nil  pe) = true -> 
  forall l1 l2, all_le l1 l2 -> all_mem_pos l1 -> 
    PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z))  Z_of_N Zpower l1 pe 
    <= ( PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z))  Z_of_N Zpower l2 pe) .
Proof.
  intros pe H l1 l2 H0 H1.
  destruct (pos_expr_incr_aux pe H l1 l2 H0 H1) as [_ h];exact h.
Qed.

Ltac find_bounds_fv fv := 
  match goal with 
    | H: ?b <= fv |- _ => 
      match isZcst b with 
        | false => fail 1
        | true => 
          match b with
            | 0 => fail 2
            | _ => constr:(b)
          end
      end
    | _ => constr:(0)
  end
  .


Ltac map tac l := 
  match l with 
    | nil => constr:(@nil Z)
    | ?x::?l => 
      let l' := map tac l in 
        let x' := tac x in 
          constr:(x'::l')
  end.

(* Import Ring_polynom. *)
Ltac ring_ineq := 
  match goal with 
    | |- ?p <= ?q => 
      let mkFV := FV Zcst Zpow_tac Zplus Zmult Zminus Z.opp Zpower in 
        let mkPol := mkPolexpr Z Zcst Zpow_tac Zplus Zmult Zminus Z.opp Zpower in
          let fv := mkFV p (@List.nil Z) in
          let fv := mkFV q fv in
            let pe := mkPol p fv in
            let qe := mkPol q fv in
              let p' := constr:(Ring_polynom.PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z)) Z_of_N Zpower fv pe) in  
                let q' := constr:(Ring_polynom.PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z)) Z_of_N Zpower fv qe) in 
                  let H:= fresh "H" in 
                  (assert (H':p' <= q');[
                    apply pos_expr_if_all_pos;
                      [vm_compute;reflexivity|
                        simpl;repeat split;assumption]
                    | vm_compute in H';exact H'
                  ])
    | |- ?p < ?q => 
      let mkFV := FV Zcst Zpow_tac Zplus Zmult Zminus Z.opp Zpower in 
        let mkPol := mkPolexpr Z Zcst Zpow_tac Zplus Zmult Zminus Z.opp Zpower in
          let fv := mkFV p (@List.nil Z) in
          let fv := mkFV q fv in
            let pe := mkPol p fv in
            let qe := mkPol q fv in
              let p' := 
                constr:(
                  Ring_polynom.PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z)) Z_of_N Zpower fv pe
                ) 
                in  
                let q' := 
                  constr:(
                    Ring_polynom.PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z)) Z_of_N Zpower fv qe
                  ) 
                  in 
                  let H:= fresh "H" in 
                  (assert (H':p' < q');[
                    let lb := map find_bounds_fv fv in 
                      apply strict_pos_expr_if_all_pos with lb;[
                        vm_compute;reflexivity|
                          simpl;repeat split; auto with zarith|
                            vm_compute;reflexivity|
                              simpl;repeat split;assumption|
                                vm_compute;reflexivity]
                        | vm_compute in H';exact H'
                  ]
                  )
  end.

Ltac modify_FV H l :=
  match l with
    | nil => constr:(@nil Z)
    | ?x::?l =>
        match type of H with
          | ?p <= x  =>
            match p with
              | 0 => fail 1
              | _ =>
                constr:(p::l)
            end
      end
    | ?y::?l => 
      let fv' := modify_FV H l in
        constr:(y::fv')
  end.

Ltac set_as_var_if_needed p := 
  let set_as_var :=       
    let x := fresh "x" in
      assert (0<=p) by ring_ineq
        in
        
        match p with 
          | context [Zplus _ _] => set_as_var
          | context [Zmult _ _] => set_as_var
          | context [Zminus _ _] => set_as_var
          | context [Z.opp _] => set_as_var
          | _ => idtac 
        end
.



Ltac ring_ineq_same_pol H :=
  try exact H;
  match type of H with 
    | ?p <= ?q => 
      (set_as_var_if_needed p;
      set_as_var_if_needed q)
  end;

  match goal with
    | |- ?p <= ?q =>
      let mkFV := FV Zcst Zpow_tac Zplus Zmult Zminus Z.opp Zpower in
        let mkPol := mkPolexpr Z Zcst Zpow_tac Zplus Zmult Zminus Z.opp Zpower in
          let fv2 := mkFV q  (@List.nil Z) in
            let fv1 := modify_FV H fv2 in
            let qe := mkPol q fv2 in
              let p' := constr:(Ring_polynom.PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z)) Z_of_N Zpower fv1 qe) in
                let q' := constr:(Ring_polynom.PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z)) Z_of_N Zpower fv2 qe) in
                  let H':= fresh "H" in
                  (assert (H':p' <= q');[
                    apply pos_expr_incr;
                      [vm_compute;reflexivity|
                        cbv beta iota zeta delta [all_le all_mem_pos];
                          repeat split;auto with zarith|
                            cbv beta iota zeta delta [all_le all_mem_pos];
                          repeat split;auto with zarith
                      ]
                    | vm_compute in H'|-*;exact H'
                  ])
  end
  .

Ltac get_fun p e := 
  let e' := eval pattern p in e in 
    match e' with 
      | ?f _ => constr:(f)
    end
.




Ltac check_goal continue_tac  Hacc order H trans_right trans_left p q lhs rhs := 
  match isZcst p with 
    | true => fail 1
    | false => 
      match rhs with 
        | context [q] => 
          let f := get_fun q rhs in 
            apply (trans_right) with (f p);
              [
                match Hacc with 
                  | tt => clear H
                  | ?Hacc => generalize (conj H Hacc);clear Hacc H;intro Hacc
                end;continue_tac tt
                |
                let H' := fresh in 
                  let e := constr:(forall a b, 0 <= a -> order a b -> order (f a) (f b)) in
                  assert (H':e);
                    [
                      let h := fresh "h" in 
                        (cbv beta;do 3 intro;intro h;ring_ineq_same_pol h)
                      |
                        cbv beta in H'; refine (H' _ _ _ H);ring_ineq
                    ]
              ]
        | _ => 
          match lhs with 
            context [p] => 
            let f := get_fun p lhs in 
              apply (trans_left) with (f q);
                [
                  let H' := fresh "H" in
                    assert (H':forall a b, 0 <= a -> order a b -> order (f a) (f b));
                      [
                        let h := fresh "h" in
                          (cbv beta;do 3 intro;intro h;ring_ineq_same_pol h)
                        |
                          cbv beta in H'; refine (H' _ _ _ H);ring_ineq
                      ]
                  |              
                    match Hacc with 
                      | tt => clear H
                      | ?Hacc => generalize (conj H Hacc);clear Hacc H;intro Hacc
                    end;continue_tac tt
                ]
          end 
          
      end
  end.        
          

Ltac soft_prove_ineq continue_tac Hacc := 
  match goal with 
    | H:?p <= ?q |- ?lhs <= ?rhs => 
        check_goal continue_tac Hacc Z.le H Z.le_trans Z.le_trans p q lhs rhs 
    | H:?p <= ?q |- ?lhs < ?rhs => 
        check_goal continue_tac Hacc Z.le H Z.lt_le_trans Z.le_lt_trans p q lhs rhs 
    | H:?p < ?q |- ?lhs < ?rhs => 
      check_goal continue_tac Hacc Z.lt H Z.le_lt_trans Z.lt_le_trans p q lhs rhs
    | _ => ring_ineq
  end.
From Stdlib Require Zwf.
From CoLoR Require terminaison.
Ltac prove_ineq := soft_prove_ineq ltac:(fun _ => prove_ineq) tt.

Ltac isVar t := 
  match goal with 
    | v:Z |- _ => 
      match t with 
        v => constr:(true)
      end
    | _ => constr:(false)
  end.


(*
      let mkFV := FV Zcst Zpow_tac Zplus Zmult Zminus Z.opp Zpower in
        let mkPol := mkPolexpr Z Zcst Zpow_tac Zplus Zmult Zminus Z.opp Zpower in
          let fv2 := mkFV q  (@List.nil Z) in
            let fv1 := modify_FV H fv2 in
            let qe := mkPol q fv2 in
              let p' := constr:(Ring_polynom.PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z)) Z_of_N Zpower fv1 qe) in
                let q' := constr:(Ring_polynom.PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z)) Z_of_N Zpower fv2 qe) in

Goal 
  forall pe1 pe2 fv, 
  PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z))  Z_of_N Zpower fv pe1 - 
  PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z))  Z_of_N Zpower nil pe2
    <= ( PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z))  Z_of_N Zpower fv pe2) - 
      PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z))  Z_of_N Zpower nil pe2
 ->   PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z))  Z_of_N Zpower fv pe1 
    <= ( PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z))  Z_of_N Zpower fv pe2) .
Proof.
  intros pe1 pe2 fv H.
  lia.
Qed.
*)

Ltac translate_vars := 
  match goal with 
    | H: ?p <= ?v |- _ => 
      match isZcst p with 
        | true => 
          match p with 
            | 0 => fail 2
            | _ => 
              match isVar v with 
                | true =>
                  let v' := fresh "v" in 
                    set (v':= v - p) in *;
                      assert (v = v' + p) by (unfold v';ring);
                        assert (0<=v') by auto with zarith;
                          clearbody v';
                            subst v ; try clear H                            
                | false => 
                  let mkFV := FV Zcst Zpow_tac Zplus Zmult Zminus Z.opp Zpower in
                    let mkPol := mkPolexpr Z Zcst Zpow_tac Zplus Zmult Zminus Z.opp Zpower in
                      let fv := mkFV v  (@List.nil Z) in
                        match fv with 
                          | _::nil => 
                            let ve := mkPol v fv in
                              
                              match eval vm_compute in (Ring_polynom.PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z)) Z_of_N Zpower nil ve) with
                                | 0%Z => fail 5
                                | _ => 
                                  let h := fresh "h" in 
                                    assert (h:p - Ring_polynom.PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z)) Z_of_N Zpower nil ve <=
                                      Ring_polynom.PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z)) Z_of_N Zpower fv ve - Ring_polynom.PEeval 0 1 Zplus Zmult Zminus Z.opp (IDphi (R:=Z)) Z_of_N Zpower nil ve);
                                    [     lazy beta delta  [Ring_polynom.PEeval IDphi BinList.nth hd] iota zeta; lia|
                                      lazy beta delta  [Ring_polynom.PEeval IDphi BinList.nth hd] iota zeta in h;
                                        ring_simplify in h;clear H]
                            end
                          | _ => fail 4

                        end

              end
          end
      end
  end.

From Stdlib Require Import Lia.

From CoLoR Require interp.
Ltac full_prove_ineq 
  term_constructor
  find_replacement 
  osl_star 
  mm
  mm_star_monotonic 
  order 
  order_op 
  simplify_star_reduction_R 
  rew
  gen_pos_hyp
  pre_concl_tac
  IHx
  apply_subst :=
  try (simplify_star_reduction_R tt );
    first [
      solve [apply IHx;clear IHx;
        match goal with 
          |- order _ (mm (term_constructor ?f ?l)) => 
            let l' := find_replacement l in 
              apply (order_op).(interp.le_lt_compat_right) 
          with (mm (term_constructor f l') ) ;[|
            apply mm_star_monotonic;
              repeat apply osl_star;
                (assumption || constructor 1)
          ]
        end;
        clear;
          simpl apply_subst;
          rew tt;
          repeat (gen_pos_hyp tt);
            pre_concl_tac tt;
            (lia) || 
              (repeat translate_vars;( ring_ineq|| prove_ineq ))]|
      let IHx' := fresh "IHx" in
        match goal with 
          | |- Acc ?R ?t => 
            assert (IHx':forall y, order (mm y) (mm t) -> Acc R y)
        end;
        [let y := fresh "y" in 
          let x := fresh "x" in
            let H := fresh "H" in 
              intros y H;
                apply IHx;clear IHx; 
                  match goal with 
                    |- order _ (mm (term_constructor ?f ?l)) => 
                      let l' := find_replacement l in 
                        apply (order_op).(interp.le_lt_compat_right) 
                    with (mm (term_constructor f l') ) ;[|
                      apply mm_star_monotonic;
                        repeat apply osl_star;
                          (assumption || constructor 1)
                    ]
                  end;
                  match type of H with 
                    | order _ ?u => 
                      apply (order_op).(interp.le_lt_compat_right)
                    with u;[assumption|]
                  end;
                  clear;
simpl apply_subst;
                    rew tt;
                    repeat (gen_pos_hyp tt);
                      pre_concl_tac tt;
                        ((lia) || ((repeat translate_vars);
                          prove_ineq))
          | clear IHx;rename IHx' into IHx;
            repeat match goal with | H: terminaison.star _ _ _ _ |- _ => clear H end
        ]
        
    ].

