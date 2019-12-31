Inductive N : Set :=
| zero : N
| succ : N -> N.

Fixpoint plus (m n : N) :=
match m with
| zero => n
| succ m' => succ (plus m' n)
end.

Lemma plus_n_zero: forall n, n = plus n zero
Proof.
induction n.
auto.
simpl.
f_equal.
assumption.
Qed.

Lemma plus_succ: forall m n, succ (plus n m) = plus n (succ m).
Proof.
intros.
induction n.
auto.
simpl.
f_equal.
assumption.
Qed.

Theorem plus_comm: forall m n, plus m n = plus n m.
Proof.
intros.
induction m.
simpl.
apply plus_n_zero.
simpl.
rewrite IHm.
apply plus_succ.
Qed.

Inductive tree : Set :=
| empty : tree
| node : tree -> tree -> tree.

Fixpoint size t := 
match t with
| empty => zero
| node t1 t2 => succ (plus (size t1) (size t2))
end.

Fixpoint swap t :=
match t with 
| empty => empty
| node t1 t2 => node (swap t2) (swap t1)
end.

Theorem swap_size: forall t, size t = size (swap t).
Proof.
intro.
induction t.
auto.
simpl.
f_equal.
rewrite plus_comm.
f_equal; assumption
Qed. 




















