Require Import Omega.
Require Import Nat.
Require Export Arith_base.
Require Import Arith.Even.
Require Import BinPos BinInt BinNat Pnat Nnat.
Require Import PeanoNat.
Require Import ZArith_base.
Require Import ZArithRing.
Require Import Zcomplements.
Require Import Zdiv.
Require Import Wf_nat.

Lemma even_exists : forall x : nat,
Nat.even x = true -> exists k, 2*k = x.
Proof.
intros.
apply Nat.even_spec in H.
unfold Nat.Even in H.
destruct H.
exists x0.
auto.
Qed.

Lemma even_minus_even_is_even : forall x a : nat,
    Nat.even(x + 2*a) = true -> Nat.even(x) = true.
Proof.
intros.
apply Nat.even_spec in H.
unfold Nat.Even in H.
apply Nat.even_spec.
unfold Nat.Even.
destruct H.
apply f_equal with (f := fun t => t- 2*a) in H.
replace (x + 2*a - 2*a) with (x) in H.
replace (2*x0 - 2*a) with (2*(x0-a)) in H.
exists (x0-a).
assumption.
omega.
omega.
Qed.



Theorem two_times_x_even : forall x : nat, Nat.even(2 * x) = true.
Proof.
  simpl.
  induction x.
  auto.
  rewrite Nat.add_0_r.
  rewrite Nat.add_0_r in IHx.
  replace (S x + S x) with (S (S (x + x))).
  simpl.
  apply IHx.
  simpl.
  auto.
Qed.


Axiom trivial : forall x : nat, 2*(x-1) +1 = 2*x - 1.




  Lemma even_plus_one_is_odd : forall x : nat, Nat.even(x+1) = true -> Nat.odd(x) = true.
Proof.
intros.
apply Nat.even_spec in H.
apply Nat.odd_spec.
unfold Nat.Odd.
unfold Nat.Even in H.
destruct H.
apply f_equal with (f := fun t => t-1) in H.
replace (x +1-1) with (x) in H.
replace (2*x0 -1) with (2*(x0-1) + 1) in H.
exists (x0-1).
assumption.
apply trivial.
omega.
Qed.

  
  Theorem easy : forall p q : Prop, (p->q) -> (~q->~p).
Proof.
intros.
intro.
apply H0.
apply H.
assumption.
Qed.

Lemma not_even_not_odd : forall n, even n -> odd n -> False.
Proof.
induction n.
intros even_0 odd_0.
inversion odd_0.
intros even_Sn odd_Sn.
inversion even_Sn.
inversion  odd_Sn.
auto with arith.
Qed.

Axiom not_even_implies_odd: forall x : nat, Nat.even(x) <> true -> Nat.odd(x) = true.
Theorem square_even_is_even : forall x : nat, Nat.even(x * x) = true <->  Nat.even(x) = true.
Proof.
intros.
induction x.
simpl.  
split.
auto.
auto.
split.
intros.
replace (S x  * S x) with ((x*x + 1) + 2*x) in H.
assert (forall p q : nat, Nat.even(p+2*q) = true -> Nat.even(p) = true).
apply even_minus_even_is_even.
assert (Nat.even(x*x+1) = true).
destruct (H0 (x*x+1) (x)).
assumption.
auto.
assert (Nat.odd(x*x) = true).
apply even_plus_one_is_odd.
assumption.
destruct IHx.
assert (Nat.odd x = true).
assert (~Nat.even(x*x) = true -> ~Nat.even(x) = true).     
apply easy.
assumption.
assert (Nat.even(x*x) <> true).
unfold not.
intros.
assert (forall n : nat, (Nat.Even(n) -> Nat.Odd(n) -> False)).
intros.
apply even_equiv in H7.
apply odd_equiv in H8.
cut (odd n).
cut (even n).
apply not_even_not_odd.
assumption.
assumption.
destruct (H7 (x*x)).
cut (Nat.even(x*x) = true).
apply Nat.even_spec.
assumption.
cut (Nat.odd(x*x) = true).
apply Nat.odd_spec.
assumption.
assert (Nat.even x <> true).
apply H5.
assumption.
cut (Nat.even x <> true).
apply not_even_implies_odd.
assumption.
replace (S x) with (x+1).
cut (Nat.odd(1)= true).
cut (Nat.odd(x) = true).
rewrite Nat.even_spec.
repeat rewrite Nat.odd_spec.
rewrite <-  even_equiv.
repeat rewrite <- odd_equiv.
apply odd_even_plus. 
assumption.
auto.
omega.
simpl.
replace (S x) with (x+1).
rewrite Nat.mul_add_distr_l.
repeat omega.
omega.
intros.
rewrite Nat.even_spec in H.
rewrite Nat.even_spec.
unfold Nat.Even in H.
unfold Nat.Even.
destruct H.
replace (S x) with (2*x0).
exists (2*x0*x0).
rewrite <- Nat.mul_assoc.
apply f_equal.
rewrite Nat.mul_assoc.
replace (x0*2) with (2*x0).
auto.
omega.
Qed.


Theorem root_2_irr : forall p q : nat,p * p <> 2 * q * q.
  Proof.
  intros.
  unfold not.
  intros eq.
  assert (Nat.even(p*p) = true).
  rewrite eq.
  replace (2*q*q) with (2*(q*q)).
  apply two_times_x_even.
  symmetry.
  apply mult_assoc_reverse.
  assert (Nat.even(p)= true).
  apply square_even_is_even.
  assumption.


  (* The proof is incomplete, still need a way to define relatively prime numbers (that's readily available from coq) and a few lemmas need to be proved which are listed as axioms *)
