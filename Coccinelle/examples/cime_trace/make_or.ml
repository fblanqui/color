open Format
  
let rec pr_ais fmt i = 
  if i>0 
  then
    fprintf fmt "%a A%d " pr_ais (i-1) i
      
  
let rec pr_or_ais fmt i = 
  if i>1 
  then
    fprintf fmt "%a \\/ A%d " pr_or_ais (i-1) i
  else fprintf fmt "A1 "
      

let pr_ori_constr fmt i j = 
  fprintf fmt "| or%d_%d : A%d -> or%d %a\n" 
    i j j i pr_ais i

let pr_ori_ind fmt i = 
  fprintf fmt 
    "@[Inductive or%d (%a:Prop) : Prop :=@."
    i pr_ais i;
  for j=1 to i do
    pr_ori_constr fmt i j;
  done;
  fprintf fmt ".@]@.@."


(* let pr_ori_lemma1 fmt i j =  *)
(*   for k = 1 to j -1 do  *)
(*     fprintf fmt "right. " *)
(*   done;  *)
(*   if (i<>j) then fprintf fmt "left. " *)

let pr_ori_lemma1 fmt i = 
  if i > 3 
  then 
    begin
      fprintf fmt "rewrite <- or%d_equiv.@." (i-1);
      fprintf fmt "destruct H.@.";
      for j=1 to (i-2) do
	fprintf fmt "constructor %d. exact H.@." j
      done;
      fprintf fmt "constructor %d. left. exact H.@." (i-1);
      fprintf fmt "constructor %d. right. exact H.@." (i-1);
    end
  else 
    begin
      fprintf fmt "destruct H.@.";
      fprintf fmt "left. assumption.@.";
      fprintf fmt "right. left. assumption.@.";
      fprintf fmt "right. right. assumption.@."
    end

let pr_ori_lemma2 fmt i =
  if i = 3 
  then
    begin
      for j = 1 to (i-1)  do 
	fprintf fmt "destruct H. constructor %d. exact H.@." j
      done;
      fprintf fmt "constructor %d. exact H.@." i
    end
  else 
    begin
      fprintf fmt "destruct H.@.";
      fprintf fmt "constructor 1. exact H.@.";
      fprintf fmt "rewrite <- or%d_equiv in H.@." (i-1);
      fprintf fmt "destruct H.@.";
      for j = 2 to i do 
	fprintf fmt "constructor %d. exact H.@." j;
      done;
      
    end
    
let pr_ori_lemma fmt i = 
  fprintf fmt "Lemma or%d_equiv: forall %a, or%d %a <-> %a.@." 
    i pr_ais i i pr_ais i pr_or_ais i;
  fprintf fmt "@[Proof. ";
  fprintf fmt "intros.@.split.@.@.";
  fprintf fmt "intros H.@.";
(*   fprintf fmt "repeat (first[left;assumption|right]);assumption.@.@."; *)
(*   for j = 1 to i do  pr_ori_lemma1 fmt i j; fprintf fmt "assumption.@."; done; *)
  pr_ori_lemma1 fmt i;
  fprintf fmt "intros H.@.";
(*   fprintf fmt "repeat (destruct H;[constructor assumption|idtac]);constructor assumption.@]@.Qed.@.@.@." *)
  pr_ori_lemma2 fmt i;
  fprintf fmt "@]@.Qed.@.@.@."
    

let pr_ori_morph fmt i =
  fprintf fmt "Add Morphism or%d : or%d_morph.@." i i;
  fprintf fmt "Proof.@.";
  fprintf fmt "intros.@.";
  fprintf fmt "do 2 rewrite or%d_equiv.@." i;
  fprintf fmt "repeat match goal with@.";
  fprintf fmt "H: _ <-> _ |- _ => rewrite H;clear H@.";
  fprintf fmt "end.@.";
  fprintf fmt "reflexivity.@.";
  fprintf fmt "Qed.@."
  
let pr_ori fmt i = 
  pr_ori_ind fmt i;
  pr_ori_lemma fmt i;
  pr_ori_morph fmt i
  



let _ = 
  let f  = open_out "or_ext_generated.v" in
  let fmt = formatter_of_out_channel f in
  fprintf fmt "Require Import Setoid.@.";
  fprintf fmt "Set Implicit Arguments.@.@.@.";
  for i = 3 to 100 do pr_ori fmt i; done;
  close_out f
