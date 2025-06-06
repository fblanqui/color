From Stdlib Require Import Setoid Morphisms.

Set Implicit Arguments.

Opaque iff.

Ltac morph eq :=
  compute; intros; rewrite !eq;
  repeat match goal with H: _ <-> _ |- _ => rewrite H;clear H end;
  reflexivity.
 
Inductive or2 ( A1  A2 :Prop) : Prop :=
| or2_1 : A1 -> or2  A1  A2  
| or2_2 : A2 -> or2  A1  A2   
.

Lemma or2_equiv: forall  A1  A2 , or2  A1  A2  <-> A1  \/ A2 .
Proof. intros.
split.

intros H.
destruct H.
left. assumption.
right.  assumption.
intros H.
destruct H. constructor 1. exact H.
constructor 2. exact H.

Qed.

 
Inductive or3 ( A1  A2  A3 :Prop) : Prop :=
| or3_1 : A1 -> or3  A1  A2  A3 
| or3_2 : A2 -> or3  A1  A2  A3 
| or3_3 : A3 -> or3  A1  A2  A3 
.

Lemma or3_equiv: forall  A1  A2  A3 , or3  A1  A2  A3  <-> A1  \/ A2  \/ A3 .
Proof. intros.
split.

intros H.
destruct H.
left. assumption.
right. left. assumption.
right. right. assumption.
intros H.
destruct H. constructor 1. exact H.
destruct H. constructor 2. exact H.
constructor 3. exact H.

Qed.


Global Instance or3_morph : Proper (iff ==> iff ==> iff ==> iff) or3.

Proof. morph or3_equiv. Qed.

Inductive or4 ( A1  A2  A3  A4 :Prop) : Prop :=
| or4_1 : A1 -> or4  A1  A2  A3  A4 
| or4_2 : A2 -> or4  A1  A2  A3  A4 
| or4_3 : A3 -> or4  A1  A2  A3  A4 
| or4_4 : A4 -> or4  A1  A2  A3  A4 
.

Lemma or4_equiv: forall  A1  A2  A3  A4 , or4  A1  A2  A3  A4  <-> A1  \/ A2  \/ A3  \/ A4 .
Proof. intros.
split.

intros H.
rewrite <- or3_equiv.
destruct H.
constructor 1. exact H.
constructor 2. exact H.
constructor 3. left. exact H.
constructor 3. right. exact H.
intros H.
destruct H.
constructor 1. exact H.
rewrite <- or3_equiv in H.
destruct H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.

Qed.


Global Instance or4_morph : Proper (iff ==> iff ==> iff ==> iff ==> iff) or4.

Proof. morph or4_equiv. Qed.

Inductive or5 ( A1  A2  A3  A4  A5 :Prop) : Prop :=
| or5_1 : A1 -> or5  A1  A2  A3  A4  A5 
| or5_2 : A2 -> or5  A1  A2  A3  A4  A5 
| or5_3 : A3 -> or5  A1  A2  A3  A4  A5 
| or5_4 : A4 -> or5  A1  A2  A3  A4  A5 
| or5_5 : A5 -> or5  A1  A2  A3  A4  A5 
.

Lemma or5_equiv: forall  A1  A2  A3  A4  A5 , or5  A1  A2  A3  A4  A5  <-> A1  \/ A2  \/ A3  \/ A4  \/ A5 .
Proof. intros.
split.

intros H.
rewrite <- or4_equiv.
destruct H.
constructor 1. exact H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. left. exact H.
constructor 4. right. exact H.
intros H.
destruct H.
constructor 1. exact H.
rewrite <- or4_equiv in H.
destruct H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.

Qed.

Global Instance or5_morph : Proper (iff ==> iff ==> iff ==> iff ==> iff ==> iff) or5.

Proof. morph or5_equiv. Qed.

Inductive or6 ( A1  A2  A3  A4  A5  A6 :Prop) : Prop :=
| or6_1 : A1 -> or6  A1  A2  A3  A4  A5  A6 
| or6_2 : A2 -> or6  A1  A2  A3  A4  A5  A6 
| or6_3 : A3 -> or6  A1  A2  A3  A4  A5  A6 
| or6_4 : A4 -> or6  A1  A2  A3  A4  A5  A6 
| or6_5 : A5 -> or6  A1  A2  A3  A4  A5  A6 
| or6_6 : A6 -> or6  A1  A2  A3  A4  A5  A6 
.

Lemma or6_equiv: forall  A1  A2  A3  A4  A5  A6 , or6  A1  A2  A3  A4  A5  A6  <-> A1  \/ A2  \/ A3  \/ A4  \/ A5  \/ A6 .
Proof. intros.
split.

intros H.
rewrite <- or5_equiv.
destruct H.
constructor 1. exact H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. left. exact H.
constructor 5. right. exact H.
intros H.
destruct H.
constructor 1. exact H.
rewrite <- or5_equiv in H.
destruct H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.

Qed.

Global Instance or6_morph : Proper (iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff) or6.

Proof. morph or6_equiv. Qed.

Inductive or7 ( A1  A2  A3  A4  A5  A6  A7 :Prop) : Prop :=
| or7_1 : A1 -> or7  A1  A2  A3  A4  A5  A6  A7 
| or7_2 : A2 -> or7  A1  A2  A3  A4  A5  A6  A7 
| or7_3 : A3 -> or7  A1  A2  A3  A4  A5  A6  A7 
| or7_4 : A4 -> or7  A1  A2  A3  A4  A5  A6  A7 
| or7_5 : A5 -> or7  A1  A2  A3  A4  A5  A6  A7 
| or7_6 : A6 -> or7  A1  A2  A3  A4  A5  A6  A7 
| or7_7 : A7 -> or7  A1  A2  A3  A4  A5  A6  A7 
.

Lemma or7_equiv: forall  A1  A2  A3  A4  A5  A6  A7 , or7  A1  A2  A3  A4  A5  A6  A7  <-> A1  \/ A2  \/ A3  \/ A4  \/ A5  \/ A6  \/ A7 .
Proof. intros.
split.

intros H.
rewrite <- or6_equiv.
destruct H.
constructor 1. exact H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. left. exact H.
constructor 6. right. exact H.
intros H.
destruct H.
constructor 1. exact H.
rewrite <- or6_equiv in H.
destruct H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.

Qed.

Global Instance or7_morph : Proper (iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff) or7.

Proof. morph or7_equiv. Qed.

Inductive or8 ( A1  A2  A3  A4  A5  A6  A7  A8 :Prop) : Prop :=
| or8_1 : A1 -> or8  A1  A2  A3  A4  A5  A6  A7  A8 
| or8_2 : A2 -> or8  A1  A2  A3  A4  A5  A6  A7  A8 
| or8_3 : A3 -> or8  A1  A2  A3  A4  A5  A6  A7  A8 
| or8_4 : A4 -> or8  A1  A2  A3  A4  A5  A6  A7  A8 
| or8_5 : A5 -> or8  A1  A2  A3  A4  A5  A6  A7  A8 
| or8_6 : A6 -> or8  A1  A2  A3  A4  A5  A6  A7  A8 
| or8_7 : A7 -> or8  A1  A2  A3  A4  A5  A6  A7  A8 
| or8_8 : A8 -> or8  A1  A2  A3  A4  A5  A6  A7  A8 
.

Lemma or8_equiv: forall  A1  A2  A3  A4  A5  A6  A7  A8 , or8  A1  A2  A3  A4  A5  A6  A7  A8  <-> A1  \/ A2  \/ A3  \/ A4  \/ A5  \/ A6  \/ A7  \/ A8 .
Proof. intros.
split.

intros H.
rewrite <- or7_equiv.
destruct H.
constructor 1. exact H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. left. exact H.
constructor 7. right. exact H.
intros H.
destruct H.
constructor 1. exact H.
rewrite <- or7_equiv in H.
destruct H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.

Qed.

Global Instance or8_morph : Proper (iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff) or8.

Proof. morph or8_equiv. Qed.

Inductive or9 ( A1  A2  A3  A4  A5  A6  A7  A8  A9 :Prop) : Prop :=
| or9_1 : A1 -> or9  A1  A2  A3  A4  A5  A6  A7  A8  A9 
| or9_2 : A2 -> or9  A1  A2  A3  A4  A5  A6  A7  A8  A9 
| or9_3 : A3 -> or9  A1  A2  A3  A4  A5  A6  A7  A8  A9 
| or9_4 : A4 -> or9  A1  A2  A3  A4  A5  A6  A7  A8  A9 
| or9_5 : A5 -> or9  A1  A2  A3  A4  A5  A6  A7  A8  A9 
| or9_6 : A6 -> or9  A1  A2  A3  A4  A5  A6  A7  A8  A9 
| or9_7 : A7 -> or9  A1  A2  A3  A4  A5  A6  A7  A8  A9 
| or9_8 : A8 -> or9  A1  A2  A3  A4  A5  A6  A7  A8  A9 
| or9_9 : A9 -> or9  A1  A2  A3  A4  A5  A6  A7  A8  A9 
.

Lemma or9_equiv: forall  A1  A2  A3  A4  A5  A6  A7  A8  A9 , or9  A1  A2  A3  A4  A5  A6  A7  A8  A9  <-> A1  \/ A2  \/ A3  \/ A4  \/ A5  \/ A6  \/ A7  \/ A8  \/ A9 .
Proof. intros.
split.

intros H.
rewrite <- or8_equiv.
destruct H.
constructor 1. exact H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. left. exact H.
constructor 8. right. exact H.
intros H.
destruct H.
constructor 1. exact H.
rewrite <- or8_equiv in H.
destruct H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.

Qed.

Global Instance or9_morph : Proper (iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff) or9.

Proof. morph or9_equiv. Qed.

Inductive or10 ( A1  A2  A3  A4  A5  A6  A7  A8  A9  A10 :Prop) : Prop :=
| or10_1 : A1 -> or10  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10 
| or10_2 : A2 -> or10  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10 
| or10_3 : A3 -> or10  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10 
| or10_4 : A4 -> or10  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10 
| or10_5 : A5 -> or10  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10 
| or10_6 : A6 -> or10  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10 
| or10_7 : A7 -> or10  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10 
| or10_8 : A8 -> or10  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10 
| or10_9 : A9 -> or10  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10 
| or10_10 : A10 -> or10  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10 
.

Lemma or10_equiv: forall  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10 , or10  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  <-> A1  \/ A2  \/ A3  \/ A4  \/ A5  \/ A6  \/ A7  \/ A8  \/ A9  \/ A10 .
Proof. intros.
split.

intros H.
rewrite <- or9_equiv.
destruct H.
constructor 1. exact H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. left. exact H.
constructor 9. right. exact H.
intros H.
destruct H.
constructor 1. exact H.
rewrite <- or9_equiv in H.
destruct H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.
constructor 10. exact H.

Qed.

Global Instance or10_morph : Proper (iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff) or10.

Proof. morph or10_equiv. Qed.

Inductive or11 ( A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11 :Prop) : Prop :=
| or11_1 : A1 -> or11  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11 
| or11_2 : A2 -> or11  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11 
| or11_3 : A3 -> or11  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11 
| or11_4 : A4 -> or11  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11 
| or11_5 : A5 -> or11  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11 
| or11_6 : A6 -> or11  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11 
| or11_7 : A7 -> or11  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11 
| or11_8 : A8 -> or11  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11 
| or11_9 : A9 -> or11  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11 
| or11_10 : A10 -> or11  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11 
| or11_11 : A11 -> or11  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11 
.

Lemma or11_equiv: forall  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11 , or11  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  <-> A1  \/ A2  \/ A3  \/ A4  \/ A5  \/ A6  \/ A7  \/ A8  \/ A9  \/ A10  \/ A11 .
Proof. intros.
split.

intros H.
rewrite <- or10_equiv.
destruct H.
constructor 1. exact H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.
constructor 10. left. exact H.
constructor 10. right. exact H.
intros H.
destruct H.
constructor 1. exact H.
rewrite <- or10_equiv in H.
destruct H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.
constructor 10. exact H.
constructor 11. exact H.

Qed.

Global Instance or11_morph : Proper (iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff) or11.

Proof. morph or11_equiv. Qed.

Inductive or12 ( A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12 :Prop) : Prop :=
| or12_1 : A1 -> or12  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12 
| or12_2 : A2 -> or12  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12 
| or12_3 : A3 -> or12  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12 
| or12_4 : A4 -> or12  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12 
| or12_5 : A5 -> or12  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12 
| or12_6 : A6 -> or12  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12 
| or12_7 : A7 -> or12  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12 
| or12_8 : A8 -> or12  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12 
| or12_9 : A9 -> or12  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12 
| or12_10 : A10 -> or12  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12 
| or12_11 : A11 -> or12  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12 
| or12_12 : A12 -> or12  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12 
.

Lemma or12_equiv: forall  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12 , or12  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  <-> A1  \/ A2  \/ A3  \/ A4  \/ A5  \/ A6  \/ A7  \/ A8  \/ A9  \/ A10  \/ A11  \/ A12 .
Proof. intros.
split.

intros H.
rewrite <- or11_equiv.
destruct H.
constructor 1. exact H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.
constructor 10. exact H.
constructor 11. left. exact H.
constructor 11. right. exact H.
intros H.
destruct H.
constructor 1. exact H.
rewrite <- or11_equiv in H.
destruct H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.
constructor 10. exact H.
constructor 11. exact H.
constructor 12. exact H.

Qed.

Global Instance or12_morph : Proper (iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff) or12.

Proof. morph or12_equiv. Qed.

Inductive or13 ( A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13 :Prop) : Prop :=
| or13_1 : A1 -> or13  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13 
| or13_2 : A2 -> or13  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13 
| or13_3 : A3 -> or13  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13 
| or13_4 : A4 -> or13  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13 
| or13_5 : A5 -> or13  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13 
| or13_6 : A6 -> or13  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13 
| or13_7 : A7 -> or13  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13 
| or13_8 : A8 -> or13  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13 
| or13_9 : A9 -> or13  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13 
| or13_10 : A10 -> or13  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13 
| or13_11 : A11 -> or13  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13 
| or13_12 : A12 -> or13  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13 
| or13_13 : A13 -> or13  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13 
.

Lemma or13_equiv: forall  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13 , or13  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  <-> A1  \/ A2  \/ A3  \/ A4  \/ A5  \/ A6  \/ A7  \/ A8  \/ A9  \/ A10  \/ A11  \/ A12  \/ A13 .
Proof. intros.
split.

intros H.
rewrite <- or12_equiv.
destruct H.
constructor 1. exact H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.
constructor 10. exact H.
constructor 11. exact H.
constructor 12. left. exact H.
constructor 12. right. exact H.
intros H.
destruct H.
constructor 1. exact H.
rewrite <- or12_equiv in H.
destruct H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.
constructor 10. exact H.
constructor 11. exact H.
constructor 12. exact H.
constructor 13. exact H.

Qed.

Global Instance or13_morph : Proper (iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff) or13.

Proof. morph or13_equiv. Qed.

Inductive or14 ( A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14 :Prop) : Prop :=
| or14_1 : A1 -> or14  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14 
| or14_2 : A2 -> or14  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14 
| or14_3 : A3 -> or14  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14 
| or14_4 : A4 -> or14  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14 
| or14_5 : A5 -> or14  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14 
| or14_6 : A6 -> or14  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14 
| or14_7 : A7 -> or14  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14 
| or14_8 : A8 -> or14  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14 
| or14_9 : A9 -> or14  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14 
| or14_10 : A10 -> or14  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14 
| or14_11 : A11 -> or14  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14 
| or14_12 : A12 -> or14  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14 
| or14_13 : A13 -> or14  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14 
| or14_14 : A14 -> or14  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14 
.

Lemma or14_equiv: forall  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14 , or14  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  <-> A1  \/ A2  \/ A3  \/ A4  \/ A5  \/ A6  \/ A7  \/ A8  \/ A9  \/ A10  \/ A11  \/ A12  \/ A13  \/ A14 .
Proof. intros.
split.

intros H.
rewrite <- or13_equiv.
destruct H.
constructor 1. exact H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.
constructor 10. exact H.
constructor 11. exact H.
constructor 12. exact H.
constructor 13. left. exact H.
constructor 13. right. exact H.
intros H.
destruct H.
constructor 1. exact H.
rewrite <- or13_equiv in H.
destruct H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.
constructor 10. exact H.
constructor 11. exact H.
constructor 12. exact H.
constructor 13. exact H.
constructor 14. exact H.

Qed.

Global Instance or14_morph : Proper (iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff) or14.

Proof. morph or14_equiv. Qed.

Inductive or15 ( A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15 :Prop) : Prop :=
| or15_1 : A1 -> or15  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15 
| or15_2 : A2 -> or15  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15 
| or15_3 : A3 -> or15  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15 
| or15_4 : A4 -> or15  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15 
| or15_5 : A5 -> or15  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15 
| or15_6 : A6 -> or15  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15 
| or15_7 : A7 -> or15  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15 
| or15_8 : A8 -> or15  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15 
| or15_9 : A9 -> or15  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15 
| or15_10 : A10 -> or15  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15 
| or15_11 : A11 -> or15  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15 
| or15_12 : A12 -> or15  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15 
| or15_13 : A13 -> or15  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15 
| or15_14 : A14 -> or15  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15 
| or15_15 : A15 -> or15  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15 
.

Lemma or15_equiv: forall  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15 , or15  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  <-> A1  \/ A2  \/ A3  \/ A4  \/ A5  \/ A6  \/ A7  \/ A8  \/ A9  \/ A10  \/ A11  \/ A12  \/ A13  \/ A14  \/ A15 .
Proof. intros.
split.

intros H.
rewrite <- or14_equiv.
destruct H.
constructor 1. exact H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.
constructor 10. exact H.
constructor 11. exact H.
constructor 12. exact H.
constructor 13. exact H.
constructor 14. left. exact H.
constructor 14. right. exact H.
intros H.
destruct H.
constructor 1. exact H.
rewrite <- or14_equiv in H.
destruct H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.
constructor 10. exact H.
constructor 11. exact H.
constructor 12. exact H.
constructor 13. exact H.
constructor 14. exact H.
constructor 15. exact H.

Qed.

Global Instance or15_morph : Proper (iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff) or15.

Proof. morph or15_equiv. Qed.

Inductive or16 ( A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16 :Prop) : Prop :=
| or16_1 : A1 -> or16  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16 
| or16_2 : A2 -> or16  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16 
| or16_3 : A3 -> or16  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16 
| or16_4 : A4 -> or16  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16 
| or16_5 : A5 -> or16  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16 
| or16_6 : A6 -> or16  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16 
| or16_7 : A7 -> or16  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16 
| or16_8 : A8 -> or16  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16 
| or16_9 : A9 -> or16  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16 
| or16_10 : A10 -> or16  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16 
| or16_11 : A11 -> or16  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16 
| or16_12 : A12 -> or16  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16 
| or16_13 : A13 -> or16  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16 
| or16_14 : A14 -> or16  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16 
| or16_15 : A15 -> or16  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16 
| or16_16 : A16 -> or16  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16 
.

Lemma or16_equiv: forall  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16 , or16  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  <-> A1  \/ A2  \/ A3  \/ A4  \/ A5  \/ A6  \/ A7  \/ A8  \/ A9  \/ A10  \/ A11  \/ A12  \/ A13  \/ A14  \/ A15  \/ A16 .
Proof. intros.
split.

intros H.
rewrite <- or15_equiv.
destruct H.
constructor 1. exact H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.
constructor 10. exact H.
constructor 11. exact H.
constructor 12. exact H.
constructor 13. exact H.
constructor 14. exact H.
constructor 15. left. exact H.
constructor 15. right. exact H.
intros H.
destruct H.
constructor 1. exact H.
rewrite <- or15_equiv in H.
destruct H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.
constructor 10. exact H.
constructor 11. exact H.
constructor 12. exact H.
constructor 13. exact H.
constructor 14. exact H.
constructor 15. exact H.
constructor 16. exact H.

Qed.

Global Instance or16_morph : Proper (iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff) or16.

Proof. morph or16_equiv. Qed.

Inductive or17 ( A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17 :Prop) : Prop :=
| or17_1 : A1 -> or17  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17 
| or17_2 : A2 -> or17  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17 
| or17_3 : A3 -> or17  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17 
| or17_4 : A4 -> or17  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17 
| or17_5 : A5 -> or17  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17 
| or17_6 : A6 -> or17  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17 
| or17_7 : A7 -> or17  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17 
| or17_8 : A8 -> or17  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17 
| or17_9 : A9 -> or17  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17 
| or17_10 : A10 -> or17  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17 
| or17_11 : A11 -> or17  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17 
| or17_12 : A12 -> or17  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17 
| or17_13 : A13 -> or17  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17 
| or17_14 : A14 -> or17  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17 
| or17_15 : A15 -> or17  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17 
| or17_16 : A16 -> or17  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17 
| or17_17 : A17 -> or17  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17 
.

Lemma or17_equiv: forall  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17 , or17  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  <-> A1  \/ A2  \/ A3  \/ A4  \/ A5  \/ A6  \/ A7  \/ A8  \/ A9  \/ A10  \/ A11  \/ A12  \/ A13  \/ A14  \/ A15  \/ A16  \/ A17 .
Proof. intros.
split.

intros H.
rewrite <- or16_equiv.
destruct H.
constructor 1. exact H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.
constructor 10. exact H.
constructor 11. exact H.
constructor 12. exact H.
constructor 13. exact H.
constructor 14. exact H.
constructor 15. exact H.
constructor 16. left. exact H.
constructor 16. right. exact H.
intros H.
destruct H.
constructor 1. exact H.
rewrite <- or16_equiv in H.
destruct H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.
constructor 10. exact H.
constructor 11. exact H.
constructor 12. exact H.
constructor 13. exact H.
constructor 14. exact H.
constructor 15. exact H.
constructor 16. exact H.
constructor 17. exact H.

Qed.

Global Instance or17_morph : Proper (iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff) or17.

Proof. morph or17_equiv. Qed.

Inductive or18 ( A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18 :Prop) : Prop :=
| or18_1 : A1 -> or18  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18 
| or18_2 : A2 -> or18  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18 
| or18_3 : A3 -> or18  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18 
| or18_4 : A4 -> or18  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18 
| or18_5 : A5 -> or18  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18 
| or18_6 : A6 -> or18  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18 
| or18_7 : A7 -> or18  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18 
| or18_8 : A8 -> or18  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18 
| or18_9 : A9 -> or18  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18 
| or18_10 : A10 -> or18  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18 
| or18_11 : A11 -> or18  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18 
| or18_12 : A12 -> or18  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18 
| or18_13 : A13 -> or18  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18 
| or18_14 : A14 -> or18  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18 
| or18_15 : A15 -> or18  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18 
| or18_16 : A16 -> or18  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18 
| or18_17 : A17 -> or18  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18 
| or18_18 : A18 -> or18  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18 
.

Lemma or18_equiv: forall  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18 , or18  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  <-> A1  \/ A2  \/ A3  \/ A4  \/ A5  \/ A6  \/ A7  \/ A8  \/ A9  \/ A10  \/ A11  \/ A12  \/ A13  \/ A14  \/ A15  \/ A16  \/ A17  \/ A18 .
Proof. intros.
split.

intros H.
rewrite <- or17_equiv.
destruct H.
constructor 1. exact H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.
constructor 10. exact H.
constructor 11. exact H.
constructor 12. exact H.
constructor 13. exact H.
constructor 14. exact H.
constructor 15. exact H.
constructor 16. exact H.
constructor 17. left. exact H.
constructor 17. right. exact H.
intros H.
destruct H.
constructor 1. exact H.
rewrite <- or17_equiv in H.
destruct H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.
constructor 10. exact H.
constructor 11. exact H.
constructor 12. exact H.
constructor 13. exact H.
constructor 14. exact H.
constructor 15. exact H.
constructor 16. exact H.
constructor 17. exact H.
constructor 18. exact H.

Qed.

Global Instance or18_morph : Proper (iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff) or18.

Proof. morph or18_equiv. Qed.

Inductive or19 ( A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19 :Prop) : Prop :=
| or19_1 : A1 -> or19  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19 
| or19_2 : A2 -> or19  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19 
| or19_3 : A3 -> or19  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19 
| or19_4 : A4 -> or19  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19 
| or19_5 : A5 -> or19  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19 
| or19_6 : A6 -> or19  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19 
| or19_7 : A7 -> or19  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19 
| or19_8 : A8 -> or19  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19 
| or19_9 : A9 -> or19  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19 
| or19_10 : A10 -> or19  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19 
| or19_11 : A11 -> or19  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19 
| or19_12 : A12 -> or19  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19 
| or19_13 : A13 -> or19  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19 
| or19_14 : A14 -> or19  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19 
| or19_15 : A15 -> or19  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19 
| or19_16 : A16 -> or19  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19 
| or19_17 : A17 -> or19  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19 
| or19_18 : A18 -> or19  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19 
| or19_19 : A19 -> or19  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19 
.

Lemma or19_equiv: forall  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19 , or19  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  <-> A1  \/ A2  \/ A3  \/ A4  \/ A5  \/ A6  \/ A7  \/ A8  \/ A9  \/ A10  \/ A11  \/ A12  \/ A13  \/ A14  \/ A15  \/ A16  \/ A17  \/ A18  \/ A19 .
Proof. intros.
split.

intros H.
rewrite <- or18_equiv.
destruct H.
constructor 1. exact H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.
constructor 10. exact H.
constructor 11. exact H.
constructor 12. exact H.
constructor 13. exact H.
constructor 14. exact H.
constructor 15. exact H.
constructor 16. exact H.
constructor 17. exact H.
constructor 18. left. exact H.
constructor 18. right. exact H.
intros H.
destruct H.
constructor 1. exact H.
rewrite <- or18_equiv in H.
destruct H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.
constructor 10. exact H.
constructor 11. exact H.
constructor 12. exact H.
constructor 13. exact H.
constructor 14. exact H.
constructor 15. exact H.
constructor 16. exact H.
constructor 17. exact H.
constructor 18. exact H.
constructor 19. exact H.

Qed.

Global Instance or19_morph : Proper (iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff) or19.

Proof. morph or19_equiv. Qed.

Inductive or20 ( A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20 :Prop) : Prop :=
| or20_1 : A1 -> or20  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20 
| or20_2 : A2 -> or20  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20 
| or20_3 : A3 -> or20  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20 
| or20_4 : A4 -> or20  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20 
| or20_5 : A5 -> or20  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20 
| or20_6 : A6 -> or20  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20 
| or20_7 : A7 -> or20  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20 
| or20_8 : A8 -> or20  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20 
| or20_9 : A9 -> or20  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20 
| or20_10 : A10 -> or20  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20 
| or20_11 : A11 -> or20  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20 
| or20_12 : A12 -> or20  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20 
| or20_13 : A13 -> or20  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20 
| or20_14 : A14 -> or20  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20 
| or20_15 : A15 -> or20  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20 
| or20_16 : A16 -> or20  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20 
| or20_17 : A17 -> or20  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20 
| or20_18 : A18 -> or20  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20 
| or20_19 : A19 -> or20  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20 
| or20_20 : A20 -> or20  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20 
.

Lemma or20_equiv: forall  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20 , or20  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  <-> A1  \/ A2  \/ A3  \/ A4  \/ A5  \/ A6  \/ A7  \/ A8  \/ A9  \/ A10  \/ A11  \/ A12  \/ A13  \/ A14  \/ A15  \/ A16  \/ A17  \/ A18  \/ A19  \/ A20 .
Proof. intros.
split.

intros H.
rewrite <- or19_equiv.
destruct H.
constructor 1. exact H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.
constructor 10. exact H.
constructor 11. exact H.
constructor 12. exact H.
constructor 13. exact H.
constructor 14. exact H.
constructor 15. exact H.
constructor 16. exact H.
constructor 17. exact H.
constructor 18. exact H.
constructor 19. left. exact H.
constructor 19. right. exact H.
intros H.
destruct H.
constructor 1. exact H.
rewrite <- or19_equiv in H.
destruct H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.
constructor 10. exact H.
constructor 11. exact H.
constructor 12. exact H.
constructor 13. exact H.
constructor 14. exact H.
constructor 15. exact H.
constructor 16. exact H.
constructor 17. exact H.
constructor 18. exact H.
constructor 19. exact H.
constructor 20. exact H.

Qed.

Global Instance or20_morph : Proper (iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff) or20.

Proof. morph or20_equiv. Qed.

Inductive or21 ( A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21 :Prop) : Prop :=
| or21_1 : A1 -> or21  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21 
| or21_2 : A2 -> or21  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21 
| or21_3 : A3 -> or21  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21 
| or21_4 : A4 -> or21  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21 
| or21_5 : A5 -> or21  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21 
| or21_6 : A6 -> or21  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21 
| or21_7 : A7 -> or21  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21 
| or21_8 : A8 -> or21  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21 
| or21_9 : A9 -> or21  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21 
| or21_10 : A10 -> or21  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21 
| or21_11 : A11 -> or21  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21 
| or21_12 : A12 -> or21  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21 
| or21_13 : A13 -> or21  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21 
| or21_14 : A14 -> or21  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21 
| or21_15 : A15 -> or21  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21 
| or21_16 : A16 -> or21  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21 
| or21_17 : A17 -> or21  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21 
| or21_18 : A18 -> or21  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21 
| or21_19 : A19 -> or21  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21 
| or21_20 : A20 -> or21  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21 
| or21_21 : A21 -> or21  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21 
.

Lemma or21_equiv: forall  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21 , or21  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  <-> A1  \/ A2  \/ A3  \/ A4  \/ A5  \/ A6  \/ A7  \/ A8  \/ A9  \/ A10  \/ A11  \/ A12  \/ A13  \/ A14  \/ A15  \/ A16  \/ A17  \/ A18  \/ A19  \/ A20  \/ A21 .
Proof. intros.
split.

intros H.
rewrite <- or20_equiv.
destruct H.
constructor 1. exact H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.
constructor 10. exact H.
constructor 11. exact H.
constructor 12. exact H.
constructor 13. exact H.
constructor 14. exact H.
constructor 15. exact H.
constructor 16. exact H.
constructor 17. exact H.
constructor 18. exact H.
constructor 19. exact H.
constructor 20. left. exact H.
constructor 20. right. exact H.
intros H.
destruct H.
constructor 1. exact H.
rewrite <- or20_equiv in H.
destruct H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.
constructor 10. exact H.
constructor 11. exact H.
constructor 12. exact H.
constructor 13. exact H.
constructor 14. exact H.
constructor 15. exact H.
constructor 16. exact H.
constructor 17. exact H.
constructor 18. exact H.
constructor 19. exact H.
constructor 20. exact H.
constructor 21. exact H.

Qed.

Global Instance or21_morph : Proper (iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff) or21.

Proof. morph or21_equiv. Qed.

Inductive or22 ( A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22 :Prop) : Prop :=
| or22_1 : A1 -> or22  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22 
| or22_2 : A2 -> or22  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22 
| or22_3 : A3 -> or22  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22 
| or22_4 : A4 -> or22  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22 
| or22_5 : A5 -> or22  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22 
| or22_6 : A6 -> or22  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22 
| or22_7 : A7 -> or22  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22 
| or22_8 : A8 -> or22  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22 
| or22_9 : A9 -> or22  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22 
| or22_10 : A10 -> or22  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22 
| or22_11 : A11 -> or22  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22 
| or22_12 : A12 -> or22  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22 
| or22_13 : A13 -> or22  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22 
| or22_14 : A14 -> or22  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22 
| or22_15 : A15 -> or22  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22 
| or22_16 : A16 -> or22  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22 
| or22_17 : A17 -> or22  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22 
| or22_18 : A18 -> or22  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22 
| or22_19 : A19 -> or22  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22 
| or22_20 : A20 -> or22  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22 
| or22_21 : A21 -> or22  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22 
| or22_22 : A22 -> or22  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22 
.

Lemma or22_equiv: forall  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22 , or22  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  <-> A1  \/ A2  \/ A3  \/ A4  \/ A5  \/ A6  \/ A7  \/ A8  \/ A9  \/ A10  \/ A11  \/ A12  \/ A13  \/ A14  \/ A15  \/ A16  \/ A17  \/ A18  \/ A19  \/ A20  \/ A21  \/ A22 .
Proof. intros.
split.

intros H.
rewrite <- or21_equiv.
destruct H.
constructor 1. exact H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.
constructor 10. exact H.
constructor 11. exact H.
constructor 12. exact H.
constructor 13. exact H.
constructor 14. exact H.
constructor 15. exact H.
constructor 16. exact H.
constructor 17. exact H.
constructor 18. exact H.
constructor 19. exact H.
constructor 20. exact H.
constructor 21. left. exact H.
constructor 21. right. exact H.
intros H.
destruct H.
constructor 1. exact H.
rewrite <- or21_equiv in H.
destruct H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.
constructor 10. exact H.
constructor 11. exact H.
constructor 12. exact H.
constructor 13. exact H.
constructor 14. exact H.
constructor 15. exact H.
constructor 16. exact H.
constructor 17. exact H.
constructor 18. exact H.
constructor 19. exact H.
constructor 20. exact H.
constructor 21. exact H.
constructor 22. exact H.

Qed.

Global Instance or22_morph : Proper (iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff) or22.

Proof. morph or22_equiv. Qed.

Inductive or23 ( A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23 :Prop) : Prop :=
| or23_1 : A1 -> or23  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23 
| or23_2 : A2 -> or23  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23 
| or23_3 : A3 -> or23  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23 
| or23_4 : A4 -> or23  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23 
| or23_5 : A5 -> or23  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23 
| or23_6 : A6 -> or23  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23 
| or23_7 : A7 -> or23  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23 
| or23_8 : A8 -> or23  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23 
| or23_9 : A9 -> or23  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23 
| or23_10 : A10 -> or23  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23 
| or23_11 : A11 -> or23  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23 
| or23_12 : A12 -> or23  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23 
| or23_13 : A13 -> or23  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23 
| or23_14 : A14 -> or23  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23 
| or23_15 : A15 -> or23  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23 
| or23_16 : A16 -> or23  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23 
| or23_17 : A17 -> or23  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23 
| or23_18 : A18 -> or23  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23 
| or23_19 : A19 -> or23  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23 
| or23_20 : A20 -> or23  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23 
| or23_21 : A21 -> or23  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23 
| or23_22 : A22 -> or23  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23 
| or23_23 : A23 -> or23  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23 
.

Lemma or23_equiv: forall  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23 , or23  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  <-> A1  \/ A2  \/ A3  \/ A4  \/ A5  \/ A6  \/ A7  \/ A8  \/ A9  \/ A10  \/ A11  \/ A12  \/ A13  \/ A14  \/ A15  \/ A16  \/ A17  \/ A18  \/ A19  \/ A20  \/ A21  \/ A22  \/ A23 .
Proof. intros.
split.

intros H.
rewrite <- or22_equiv.
destruct H.
constructor 1. exact H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.
constructor 10. exact H.
constructor 11. exact H.
constructor 12. exact H.
constructor 13. exact H.
constructor 14. exact H.
constructor 15. exact H.
constructor 16. exact H.
constructor 17. exact H.
constructor 18. exact H.
constructor 19. exact H.
constructor 20. exact H.
constructor 21. exact H.
constructor 22. left. exact H.
constructor 22. right. exact H.
intros H.
destruct H.
constructor 1. exact H.
rewrite <- or22_equiv in H.
destruct H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.
constructor 10. exact H.
constructor 11. exact H.
constructor 12. exact H.
constructor 13. exact H.
constructor 14. exact H.
constructor 15. exact H.
constructor 16. exact H.
constructor 17. exact H.
constructor 18. exact H.
constructor 19. exact H.
constructor 20. exact H.
constructor 21. exact H.
constructor 22. exact H.
constructor 23. exact H.

Qed.

Global Instance or23_morph : Proper (iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff) or23.

Proof. morph or23_equiv. Qed.

Inductive or24 ( A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24 :Prop) : Prop :=
| or24_1 : A1 -> or24  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24 
| or24_2 : A2 -> or24  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24 
| or24_3 : A3 -> or24  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24 
| or24_4 : A4 -> or24  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24 
| or24_5 : A5 -> or24  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24 
| or24_6 : A6 -> or24  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24 
| or24_7 : A7 -> or24  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24 
| or24_8 : A8 -> or24  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24 
| or24_9 : A9 -> or24  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24 
| or24_10 : A10 -> or24  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24 
| or24_11 : A11 -> or24  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24 
| or24_12 : A12 -> or24  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24 
| or24_13 : A13 -> or24  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24 
| or24_14 : A14 -> or24  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24 
| or24_15 : A15 -> or24  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24 
| or24_16 : A16 -> or24  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24 
| or24_17 : A17 -> or24  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24 
| or24_18 : A18 -> or24  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24 
| or24_19 : A19 -> or24  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24 
| or24_20 : A20 -> or24  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24 
| or24_21 : A21 -> or24  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24 
| or24_22 : A22 -> or24  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24 
| or24_23 : A23 -> or24  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24 
| or24_24 : A24 -> or24  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24 
.

Lemma or24_equiv: forall  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24 , or24  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24  <-> A1  \/ A2  \/ A3  \/ A4  \/ A5  \/ A6  \/ A7  \/ A8  \/ A9  \/ A10  \/ A11  \/ A12  \/ A13  \/ A14  \/ A15  \/ A16  \/ A17  \/ A18  \/ A19  \/ A20  \/ A21  \/ A22  \/ A23  \/ A24 .
Proof. intros.
split.

intros H.
rewrite <- or23_equiv.
destruct H.
constructor 1. exact H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.
constructor 10. exact H.
constructor 11. exact H.
constructor 12. exact H.
constructor 13. exact H.
constructor 14. exact H.
constructor 15. exact H.
constructor 16. exact H.
constructor 17. exact H.
constructor 18. exact H.
constructor 19. exact H.
constructor 20. exact H.
constructor 21. exact H.
constructor 22. exact H.
constructor 23. left. exact H.
constructor 23. right. exact H.
intros H.
destruct H.
constructor 1. exact H.
rewrite <- or23_equiv in H.
destruct H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.
constructor 10. exact H.
constructor 11. exact H.
constructor 12. exact H.
constructor 13. exact H.
constructor 14. exact H.
constructor 15. exact H.
constructor 16. exact H.
constructor 17. exact H.
constructor 18. exact H.
constructor 19. exact H.
constructor 20. exact H.
constructor 21. exact H.
constructor 22. exact H.
constructor 23. exact H.
constructor 24. exact H.

Qed.

Global Instance or24_morph : Proper (iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff) or24.

Proof. morph or24_equiv. Qed.

Inductive or25 ( A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24  A25 :Prop) : Prop :=
| or25_1 : A1 -> or25  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24  A25 
| or25_2 : A2 -> or25  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24  A25 
| or25_3 : A3 -> or25  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24  A25 
| or25_4 : A4 -> or25  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24  A25 
| or25_5 : A5 -> or25  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24  A25 
| or25_6 : A6 -> or25  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24  A25 
| or25_7 : A7 -> or25  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24  A25 
| or25_8 : A8 -> or25  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24  A25 
| or25_9 : A9 -> or25  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24  A25 
| or25_10 : A10 -> or25  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24  A25 
| or25_11 : A11 -> or25  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24  A25 
| or25_12 : A12 -> or25  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24  A25 
| or25_13 : A13 -> or25  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24  A25 
| or25_14 : A14 -> or25  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24  A25 
| or25_15 : A15 -> or25  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24  A25 
| or25_16 : A16 -> or25  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24  A25 
| or25_17 : A17 -> or25  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24  A25 
| or25_18 : A18 -> or25  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24  A25 
| or25_19 : A19 -> or25  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24  A25 
| or25_20 : A20 -> or25  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24  A25 
| or25_21 : A21 -> or25  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24  A25 
| or25_22 : A22 -> or25  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24  A25 
| or25_23 : A23 -> or25  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24  A25 
| or25_24 : A24 -> or25  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24  A25 
| or25_25 : A25 -> or25  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24  A25 
.

Lemma or25_equiv: forall  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24  A25 , or25  A1  A2  A3  A4  A5  A6  A7  A8  A9  A10  A11  A12  A13  A14  A15  A16  A17  A18  A19  A20  A21  A22  A23  A24  A25  <-> A1  \/ A2  \/ A3  \/ A4  \/ A5  \/ A6  \/ A7  \/ A8  \/ A9  \/ A10  \/ A11  \/ A12  \/ A13  \/ A14  \/ A15  \/ A16  \/ A17  \/ A18  \/ A19  \/ A20  \/ A21  \/ A22  \/ A23  \/ A24  \/ A25 .
Proof. intros.
split.

intros H.
rewrite <- or24_equiv.
destruct H.
constructor 1. exact H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.
constructor 10. exact H.
constructor 11. exact H.
constructor 12. exact H.
constructor 13. exact H.
constructor 14. exact H.
constructor 15. exact H.
constructor 16. exact H.
constructor 17. exact H.
constructor 18. exact H.
constructor 19. exact H.
constructor 20. exact H.
constructor 21. exact H.
constructor 22. exact H.
constructor 23. exact H.
constructor 24. left. exact H.
constructor 24. right. exact H.
intros H.
destruct H.
constructor 1. exact H.
rewrite <- or24_equiv in H.
destruct H.
constructor 2. exact H.
constructor 3. exact H.
constructor 4. exact H.
constructor 5. exact H.
constructor 6. exact H.
constructor 7. exact H.
constructor 8. exact H.
constructor 9. exact H.
constructor 10. exact H.
constructor 11. exact H.
constructor 12. exact H.
constructor 13. exact H.
constructor 14. exact H.
constructor 15. exact H.
constructor 16. exact H.
constructor 17. exact H.
constructor 18. exact H.
constructor 19. exact H.
constructor 20. exact H.
constructor 21. exact H.
constructor 22. exact H.
constructor 23. exact H.
constructor 24. exact H.
constructor 25. exact H.

Qed.

Global Instance or25_morph : Proper (iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff ==> iff) or25.

Proof. morph or25_equiv. Qed.
