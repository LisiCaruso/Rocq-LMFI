Inductive alpha := M | I | U.

Definition word := list alpha.

Inductive lang : word -> Prop :=
| axiom : lang [M;I]
| rule1 x : lang (x ++ [I]) -> lang (x ++ [I;U])
| rule2 x : lang ([M] ++ x) -> lang ([M] ++ x ++ x)
| rule3 x y : lang (x ++ [I;I;I] ++ y) -> lang (x ++ [U] ++ y)
| rule4 x y : lang (x ++ [U;U] ++ y) -> lang (x ++ y).
