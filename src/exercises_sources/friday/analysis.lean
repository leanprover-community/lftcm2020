import analysis.analytic.composition
import analysis.normed_space.real_inner_product
import topology.metric_space.pi_Lp
import analysis.calculus.iterated_deriv

namespace lftcm

open real

/-!
# Derivatives

Lean can automatically compute some simple derivatives using `simp` tactic.
-/

example : deriv (λ x : ℝ, x^5) 6 = 5 * 6^4 := sorry

example (x₀ : ℝ) (h₀ : x₀ ≠ 0) : deriv (λ x:ℝ, 1 / x) x₀ = -1 / x₀^2 := sorry

example : deriv sin pi = -1 := sorry

-- Sometimes you need `ring` and/or `field_simp` after `simp`
example (x₀ : ℝ) (h : x₀ ≠ 0) :
  deriv (λ x : ℝ, exp(x^2) / x^5) x₀ = (2 * x₀^2 - 5) * exp (x₀^2) / x₀^6 :=
begin
  have : x₀^5 ≠ 0, { sorry },
  simp [this],
  sorry
end

example (a b x₀ : ℝ) (h : x₀ ≠ 1) :
  deriv (λ x, (a * x + b) / (x - 1)) x₀ = -(a + b) / (x₀ - 1)^2 :=
begin
  sorry
end

-- Currently `simp` is unable to solve the next example
-- A PR that will make this example provable `by simp` would be very welcome!
example : iterated_deriv 7 (λ x, sin (tan x) - tan (sin x)) 0 = -168 := sorry

end lftcm


