From Stdlib Require Arith.

Inductive light : Type :=
  | Red
  | Green
  | Blue
  | Blink (a b : light).

Fixpoint count (l : light) : nat :=
  match l with
  | Red => 1
  | Green => 1
  | Blue => 1
  | Blink a b => count a + count b
  end.

Theorem count_positive : forall l, count l > 0.
Proof.
  induction l as [| | | l1 IHl1 l2 IHl2].
  - auto with arith.
  - auto with arith.
  - auto with arith.
  - auto with arith.
    simpl;
    auto with arith.
Qed.
