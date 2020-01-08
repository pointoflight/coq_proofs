Require Import Omega.
Require Import Nat.

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
replace (S x  * S x) with ((x*x + 1) + 2*x) in 
exists (x0-a).
auto.
replace (2*(x0-a)) with (2*x0 - 2*a).
apply f_equal with (f := fun t => t-2*a) in H.
replace (x+ 2*a - 2*a) with (x) in H.

replace (S x * S x) with ((1+x) * (1+x)).
rewrite Nat.mul_add_distr_r.
rewrite Nat.mul_add_distr_l.
rewrite Nat.mul_add_distr_l.
rewrite Nat.add_assoc.
repeat rewrite Nat.mul_1_l.
rewrite Nat.mul_1_r.









Theorem root_2_irr : forall p q : nat, p * p <> 2 * q * q.
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
  