import analysis.analytic.composition
import analysis.inner_product_space.basic
import analysis.normed_space.pi_Lp
import analysis.calculus.iterated_deriv
import analysis.calculus.mean_value
import analysis.calculus.implicit
import measure_theory.integral.bochner
import measure_theory.measure.lebesgue
import linear_algebra.matrix.trace


namespace lftcm

noncomputable theory

open real
open_locale topological_space filter classical real

/-!
# Derivatives

Lean can automatically compute some simple derivatives using `simp` tactic.
-/

example : deriv (λ x : ℝ, x^5) 6 = 5 * 6^4 := sorry

example (x₀ : ℝ) (h₀ : x₀ ≠ 0) : deriv (λ x:ℝ, 1 / x) x₀ = -1 / x₀^2 := sorry

example : deriv sin π = -1 := sorry

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

-- Currently `simp` is unable to solve the next example.
-- A PR that will make this example provable `by simp` would be very welcome!
example : iterated_deriv 7 (λ x, sin (tan x) - tan (sin x)) 0 = -168 := sorry

variables (m n : Type) [fintype m] [fintype n]

-- Generalizations of the next two instances should go to `analysis/normed_space/basic`
instance : normed_add_comm_group (matrix m n ℝ) := pi.normed_add_comm_group
instance : normed_space ℝ (matrix m n ℝ) := pi.normed_space

/-- Trace of a matrix as a continuous linear map. -/
def matrix.trace_clm : matrix n n ℝ →L[ℝ] ℝ :=
(matrix.trace_linear_map n ℝ ℝ).mk_continuous (fintype.card n)
begin
  sorry
end

-- Another hard exercise that would make a very good PR
example :
  has_fderiv_at (λ m : matrix n n ℝ, m.det) (matrix.trace_clm n) 1 :=
begin
  sorry
end

end lftcm


#check deriv

#check has_fderiv_at


example (y : ℝ) : has_deriv_at (λ x : ℝ, 2 * x + 5) 2 y :=
begin
  have := ((has_deriv_at_id y).const_mul 2).add_const 5,
  rwa [mul_one] at this,
end

example (y : ℝ) : deriv (λ x : ℝ, 2 * x + 5) y = 2 := by simp

#check exists_has_deriv_at_eq_slope

#check exists_deriv_eq_slope


open set topological_space

namespace measure_theory

variables {α E : Type*} [measurable_space α] [normed_add_comm_group E] [normed_space ℝ E]
  [measurable_space E] [borel_space E] [complete_space E] [second_countable_topology E]
  {μ : measure α} {f : α → E}

#check integral

#check ∫ x : ℝ, x ^ 2

#check ∫ x in Icc (0:ℝ) 1, x^2

#check ∫ x, f x ∂μ

#check integral_add

#check integral_add_measure

#check integral_union

lemma integral_sdiff (f : α → E) (hfm : measurable f) {s t : set α}
  (hs : measurable_set s) (ht : measurable_set t) (hst : s ⊆ t)
  (hfi : integrable f $ μ.restrict t) :
  ∫ x in t \ s, f x ∂μ = ∫ x in t, f x ∂μ - ∫ x in s, f x ∂μ :=
begin
  -- hint: apply `integral_union` to `s` and `t \ s`
  sorry
end

lemma integral_Icc_sub_Icc_of_le [linear_order α] [topological_space α] [order_topology α]
  [borel_space α] {x y z : α} (hxy : x ≤ y) (hyz : y ≤ z)
  {f : α → ℝ} (hfm : measurable f) (hfi : integrable f (μ.restrict $ Icc x z)) :
  ∫ a in Icc x z, f a ∂μ - ∫ a in Icc x y, f a ∂μ = ∫ a in Ioc y z, f a ∂μ :=
begin
  rw [sub_eq_iff_eq_add', ← integral_union, Icc_union_Ioc_eq_Icc];
  sorry
end

#check set_integral_const

end measure_theory

open measure_theory

theorem FTC {f : ℝ → ℝ} {x y : ℝ} (hy : continuous_at f y) (h : x < y)
  (hfm : measurable f)
  (hfi : integrable f (volume.restrict $ Icc x y)) :
  has_deriv_at (λ z, ∫ a in Icc x z, f a) (f y) y :=
begin
  have A : has_deriv_within_at (λ z, ∫ a in Icc x z, f a) (f y) (Ici y) y,
  { rw [has_deriv_within_at_iff_tendsto, metric.tendsto_nhds_within_nhds],
    intros ε ε0,
    rw [metric.continuous_at_iff] at hy,
    rcases hy ε ε0 with ⟨δ, δ0, hδ⟩,
    use [δ, δ0],
    intros z hyz hzδ,
    rw [integral_Icc_sub_Icc_of_le, dist_zero_right, real.norm_eq_abs, abs_mul, abs_of_nonneg, abs_of_nonneg],
    all_goals {sorry } },
  have B : has_deriv_within_at (λ z, ∫ a in Icc x z, f a) (f y) (Iic y) y,
  { sorry },
  have := B.union A,
  simpa using this
end
