Require Import Arith.

Module Type EQ.
  Parameter t : Type.
  Axiom eq_dec : forall x y : t, {x = y} + {x <> y}.
End EQ.
