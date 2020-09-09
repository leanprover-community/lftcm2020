/- Missing bits that should be added to mathlib after the workshop and after cleaning them up -/

import geometry.manifold.times_cont_mdiff
import geometry.manifold.real_instances

open set

open_locale big_operators

section pi_Lp_smooth

variables
  {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {ι : Type*} [fintype ι]
  {p : ℝ} {hp : 1 ≤ p} {α : ι → Type*} {n : with_top ℕ} (i : ι)
  [∀i, normed_group (α i)] [∀i, normed_space 𝕜 (α i)]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] {f : E → pi_Lp p hp α} {s : set E} {x : E}

lemma pi_Lp.norm_coord_le_norm (x : pi_Lp p hp α) (i : ι) : ∥x i∥ ≤ ∥x∥ :=
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
    { exact div_nonneg zero_le_one (le_trans zero_le_one hp) }
  end

lemma pi_Lp.times_cont_diff_coord :
  times_cont_diff 𝕜 n (λ x : pi_Lp p hp α, x i) :=
let F : pi_Lp p hp α →ₗ[𝕜] α i :=
{ to_fun := λ x, x i, map_add' := λ x y, rfl, map_smul' := λ x c, rfl } in
(F.mk_continuous 1 (λ x, by simpa using pi_Lp.norm_coord_le_norm x i)).times_cont_diff

lemma pi_Lp.times_cont_diff_within_at_iff_coord :
  times_cont_diff_within_at 𝕜 n f s x ↔ ∀ i, times_cont_diff_within_at 𝕜 n (λ x, (f x) i) s x:=
begin
  classical,
  split,
  { assume h i,
   exact (pi_Lp.times_cont_diff_coord i).comp_times_cont_diff_within_at h, },
  { assume h,
    let F : Π (i : ι), α i →ₗ[𝕜] pi_Lp p hp α := λ i,
    { to_fun := λ y, function.update 0 i y,
      map_add' := begin
        assume y y',
        ext j,
        by_cases h : j = i,
        { rw h, simp },
        { simp [h], }
      end,
      map_smul' := begin
        assume c x,
        ext j,
        by_cases h : j = i,
        { rw h, simp },
        { simp [h], }
      end },
    let G : Π (i : ι), α i →L[𝕜] pi_Lp p hp α := λ i,
    begin
      have p_ne_0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp),
      refine (F i).mk_continuous 1 (λ x, _),
      have : (λ j, ∥function.update 0 i x j∥ ^ p) = (λ j, if j = i then ∥x∥ ^ p else 0),
      { ext j,
        by_cases h : j = i,
        { rw h, simp },
        { simp [h, p_ne_0] } },
      simp only [pi_Lp.norm_eq, this, one_mul, finset.mem_univ, if_true, linear_map.coe_mk, finset.sum_ite_eq'],
      rw [← real.rpow_mul (norm_nonneg _), mul_one_div_cancel p_ne_0, real.rpow_one]
    end,
    have : times_cont_diff_within_at 𝕜 n (λ x, (∑ (i : ι), G i ((f x) i))) s x,
    { apply times_cont_diff_within_at.sum (λ i hi, _),
      exact (G i).times_cont_diff.comp_times_cont_diff_within_at (h i) },
    convert this,
    ext x j,
    simp,
    change f x j = (∑ (i : ι), function.update 0 i (f x i)) j,
    rw finset.sum_apply,
    have : ∀ i, function.update 0 i (f x i) j = (if j = i then f x j else 0),
    { assume i,
      by_cases h : j = i,
      { rw h, simp },
      { simp [h] } },
    simp [this] }
end

lemma pi_Lp.times_cont_diff_at_iff_coord :
  times_cont_diff_at 𝕜 n f x ↔ ∀ i, times_cont_diff_at 𝕜 n (λ x, (f x) i) x :=
by simp [← times_cont_diff_within_at_univ, pi_Lp.times_cont_diff_within_at_iff_coord]

lemma pi_Lp.times_cont_diff_on_iff_coord :
  times_cont_diff_on 𝕜 n f s ↔ ∀ i, times_cont_diff_on 𝕜 n (λ x, (f x) i) s :=
by { simp_rw [times_cont_diff_on, pi_Lp.times_cont_diff_within_at_iff_coord], tauto }

lemma pi_Lp.times_cont_diff_iff_coord :
  times_cont_diff 𝕜 n f ↔ ∀ i, times_cont_diff 𝕜 n (λ x, (f x) i) :=
by simp [← times_cont_diff_on_univ, pi_Lp.times_cont_diff_on_iff_coord]

end pi_Lp_smooth
