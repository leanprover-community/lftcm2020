import linear_algebra.finite_dimensional
import ring_theory.algebraic

/-
The following exercise will not be completely straight-forward.
We will prove a result that is not yet in mathlib:
“Finite field extensions are algebraic.”

Hints for proving this result:
 * Look up the definition of `finite_dimensional`.
 * Search the library for useful lemmas about `is_algebraic` and `is_integral`.
-/

namespace algebra
variables {K L : Type*} [field K] [field L] [algebra K L] [finite_dimensional K L]

lemma is_algebraic_of_finite_dimensional : is_algebraic K L :=
begin
  -- sorry
  intro x,
  rw is_algebraic_iff_is_integral,
  apply is_integral_of_noetherian',
  assumption,
  -- sorry
end

end algebra
