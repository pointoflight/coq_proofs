(*
p/q != sqrt(2)
(p*p)/(q*q) != 2
p*p != 2*q*q
 *)
Require Import Arith.Even.
Require Import Omega.
 
Check Nat.even.
 
Lemma two_times_x_is_even : forall x : nat,
    Nat.even (2*x) = true.
Proof.
  simpl.
  induction x.
  - simpl.
    reflexivity.
  - rewrite Nat.add_0_r.
    rewrite Nat.add_0_r in IHx.
    replace (S x + S x) with (S (S (x+x))).
    + simpl.
      apply IHx.
    + simpl.
      rewrite (Nat.add_comm x (S x)).
      simpl.
      reflexivity.
Qed.
 
Lemma even_exists : forall x : nat,
    Nat.even x = true -> exists k, 2*k = x.
Proof.
  intros.
  apply Nat.even_spec in H.
  unfold Nat.Even in H.
  destruct H.
  exists x0.
  symmetry.
  apply H.
Qed.
 
Lemma next_even_is_odd : forall x : nat,
    Nat.even x = negb (Nat.even (S x)).
Proof.
  intros.
  induction x.
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHx.
    rewrite -> Bool.negb_involutive.
    reflexivity.
Qed.  
 
Lemma cancel_negb : forall a b : bool,
    negb a = negb b -> a = b.
Proof.
  intros.
  destruct a.
  - destruct b.
    + reflexivity.
    + simpl in H.
      symmetry.
      apply H.
  - destruct b.
    + simpl in H.
      symmetry.
      apply H.
    + reflexivity.
Qed.
 
Lemma even_is_xor : forall x y : nat,
    Nat.even (x+y) = negb (xorb (Nat.even x) (Nat.even y)).
Proof.
  intros.
  induction x.
  - simpl.
    case (Nat.even y); reflexivity.
  - rewrite next_even_is_odd in IHx.
    rewrite (next_even_is_odd x) in IHx.
    apply cancel_negb in IHx.
    rewrite Nat.add_succ_l.
    rewrite -> IHx.
    clear IHx.
    rewrite Bool.negb_xorb_l.
    reflexivity.
Qed.
 
   
 
Lemma square_even_is_even : forall x : nat,
    Nat.even (x*x) = Nat.even x.
Proof.
  intros.
 
  induction x.
  - simpl.
    reflexivity.
    (* (x + 1) * (x + 1) = x * x + 2 * x + 1 *)
  - replace (S x * S x) with ((1 + x) * (1 + x)).
    2 : {
      simpl.
      reflexivity.
    }
    rewrite Nat.mul_add_distr_r.
    rewrite Nat.mul_add_distr_l.
    rewrite Nat.mul_add_distr_l.
    rewrite Nat.add_assoc.
    repeat rewrite Nat.mul_1_l.
    rewrite Nat.mul_1_r.
    repeat rewrite <- Nat.add_assoc.
    repeat rewrite even_is_xor.
    repeat rewrite <- IHx.
    replace (Nat.even 1) with false.
    2 : { trivial. }
    rewrite -> Bool.xorb_false_l.
    rewrite -> Bool.xorb_nilpotent.
    replace (negb false) with true.
    2 : { trivial. }
    rewrite -> Bool.xorb_true_r.
    rewrite -> Bool.negb_involutive.
    rewrite -> IHx.
    clear IHx.
    induction x.
    + simpl.
      reflexivity.
    + rewrite <- IHx.
      rewrite -> Bool.negb_involutive.
      simpl.
      reflexivity.
Qed.
 
Lemma cancel_2 : forall x y : nat,
    2 * x = 2 * y -> x = y.
Proof.
  intros.
  omega.
Qed.    
 
 
Theorem sqrt2_infinite_descent : forall p q : nat,
    q <> 0 -> p * p = 2 * q * q -> exists pp qq : nat,
        pp * pp = 2 * qq * qq /\ qq < q.
Proof.                                              
  intros p q qnz eq.
  assert (eq' := eq).
 
  assert (Nat.even (p * p) = true).
  {
    rewrite -> eq.
    rewrite <- Nat.mul_assoc.
    apply two_times_x_is_even.
  }
  assert (Nat.even p = true).
  {
    rewrite square_even_is_even in H.
    apply H.                            
  }
  apply even_exists in H0.
  destruct H0 as [p' Hp'].
  repeat rewrite <- Hp' in eq.
  repeat rewrite <- Nat.mul_assoc in eq.
  apply cancel_2 in eq.
  rewrite Nat.mul_comm in eq.
  clear H.
 
  assert (Nat.even (q * q) = true).
  {
    rewrite <- eq.
    rewrite <- Nat.mul_assoc.
    apply two_times_x_is_even.
  }
  assert (Nat.even q = true).
  {
    rewrite square_even_is_even in H.
    apply H.
  }
  apply even_exists in H0.
  destruct H0 as [q' Hq'].
  rewrite <- Hq' in eq.
  repeat rewrite <- Nat.mul_assoc in eq.
  apply cancel_2 in eq.
  symmetry in eq.
  rewrite Nat.mul_comm in eq.
  clear H.
  symmetry in eq.
 
  exists p'.
  exists q'.
  split.
  apply eq.
 
  omega.
Qed.
 
Check sqrt2_infinite_descent.
 
Definition lt_nat (q q' : nat*nat) := snd q < snd q'.
 
Theorem lt_wf : well_founded lt_nat.
Proof.
  apply (well_founded_lt_compat (nat*nat) snd).
  intros.
  unfold lt_nat in H.
  apply H.
Qed.
 
Check well_founded.
Check well_founded_ind.
 
Theorem infinite_descent' : forall f : nat*nat -> Prop,
    (forall A : nat*nat, (f A -> exists B : nat*nat, (f B) /\ (snd B) < (snd A))) ->
                         forall C : nat * nat, ~(f C).
Proof.
  intros f H.
  apply (well_founded_ind lt_wf (fun x => ~(f x))).
  simpl.
  intros.
  specialize (H x).
  unfold not.
  intros HA.
  apply H in HA.
  destruct HA as [B HA].
  specialize (H0 B).
  unfold lt_nat in H0.
  destruct HA.
  apply H0 in H2.
  apply H2.
  apply H1.
Qed.
 
(*
Theorem infinite_descent' : forall f : nat*nat -> Prop,
    (forall A : nat*nat, (f A -> exists B : nat*nat, (f B) /\ (snd B) < (snd A))) ->
                         forall C : nat * nat, ~(f C).
Proof.
*)
 
Theorem infinite_descent : forall f : nat -> nat -> Prop,
    (forall p q : nat, ((f p q) -> exists pp qq : nat, (f pp qq) /\ qq < q)) ->
    forall r s : nat, ~(f r s).
Proof.
  intros f H.
  intros r s.
  pose (rs := (r,s)).
  replace r with (fst rs); try reflexivity.
  replace s with (snd rs); try reflexivity.
  apply (well_founded_ind lt_wf (fun x => ~(f (fst x) (snd x)))).
  intros.
  specialize (H (fst x) (snd x)).
  intros HA.
  apply H in HA.
  destruct HA as [pp HA].
  destruct HA as [qq HA].
  destruct HA.
  pose (ppqq := (pp, qq)).
  specialize (H0 ppqq).
  unfold lt_nat in H0.
  replace qq with (snd ppqq) in H2; try reflexivity.
  apply H0 in H2.
  apply H2.
  simpl.
  apply H1.
Qed.
 
 
Theorem sqrt2_is_irrational : forall p q : nat,
    q <> 0 -> p*p <> 2*q*q.
Proof.
  intros p q qnz.
  unfold not.
  intros eq.
  specialize (infinite_descent (fun (p q: nat) => p*p = 2*q*q)).
  intros id.
  specialize (id p q).
  simpl in id.
  simpl in eq.
  apply id in eq.
  apply eq.
  apply (sqrt2_infinite_descent p q).
  apply qnz.
  simpl.
  apply eq.
Qed.