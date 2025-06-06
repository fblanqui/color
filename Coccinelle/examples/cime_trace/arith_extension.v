From Stdlib Require Import Arith.

Fixpoint le_bool (n m : nat ) : bool := 
  match n,m with 
    | 0,_ => true
    | _,0 => false 
    | S n, S m => le_bool n m
  end.

Lemma le_bool_ok_true : 
  forall n m, le_bool n m = true -> le n m.
Proof.
  induction n.

  intros m _;induction m.
  constructor.
  constructor;exact IHm.

  intros [|m].
  intros abs;discriminate abs.
  simpl;intros h.
  apply le_n_S.
  apply IHn. exact h.
Qed.
