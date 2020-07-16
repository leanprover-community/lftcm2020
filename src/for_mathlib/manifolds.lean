import geometry.manifold.times_cont_mdiff
import geometry.manifold.real_instances

open set

instance : has_zero (Icc (0 : ℝ) 1) := ⟨⟨(0 : ℝ), ⟨le_refl _, zero_le_one⟩⟩⟩
instance : has_one (Icc (0 : ℝ) 1) := ⟨⟨(1 : ℝ), ⟨zero_le_one, le_refl _⟩⟩⟩

namespace metric

lemma is_closed_sphere {α : Type*} [metric_space α] {x : α} {r : ℝ} :
  is_closed (sphere x r) :=
is_closed_eq (continuous_id.dist continuous_const) continuous_const

end metric

section fderiv_id

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E]

lemma fderiv_id' {x : E} : fderiv 𝕜 (λ (x : E), x) x = continuous_linear_map.id 𝕜 E :=
fderiv_id

end fderiv_id

lemma pi_Lp.norm_coord_le_norm
  {ι : Type*} [fintype ι] {p : ℝ} {hp : 1 ≤ p} {α : ι → Type*} [∀i, normed_group (α i)]
  (x : pi_Lp p hp α) (i : ι) : ∥x i∥ ≤ ∥x∥ :=
calc
  ∥x i∥ ≤ (∥x i∥ ^ p) ^ (1/p) :
  begin
    have : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp),
    rw [← real.rpow_mul (norm_nonneg _), mul_one_div_cancel this, real.rpow_one],
  end
  ... ≤ _ :
  begin
    have A : ∀ j, 0 ≤ ∥x j∥ ^ p := λ j, real.rpow_nonneg_of_nonneg (norm_nonneg _) _,
    simp only [pi_Lp.norm_eq, one_mul, linear_map.coe_mk],
    apply real.rpow_le_rpow (A i),
    { exact finset.single_le_sum (λ j hj, A j) (finset.mem_univ _) },
    { exact div_nonneg zero_le_one (lt_of_lt_of_le zero_lt_one hp) }
  end

lemma pi_Lp.times_cont_diff_coord
  {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {ι : Type*} [fintype ι]
  {p : ℝ} {hp : 1 ≤ p} {α : ι → Type*} {n : with_top ℕ} (i : ι)
  [∀i, normed_group (α i)] [∀i, normed_space 𝕜 (α i)] :
  times_cont_diff 𝕜 n (λ x : pi_Lp p hp α, x i) :=
let F : pi_Lp p hp α →ₗ[𝕜] α i :=
{ to_fun := λ x, x i, map_add' := λ x y, rfl, map_smul' := λ x c, rfl } in
(F.mk_continuous 1 (λ x, by simpa using pi_Lp.norm_coord_le_norm x i)).times_cont_diff
