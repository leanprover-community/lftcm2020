/- Missing bits that should be added to mathlib after the workshop and after cleaning them up -/

import geometry.manifold.cont_mdiff
import geometry.manifold.instances.real

open set

open_locale big_operators ennreal

section pi_Lp_smooth

variables
  {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {ι : Type*} [fintype ι]
  {p : ℝ≥0∞} [hp : fact (1 ≤ p)] {α : ι → Type*} {n : with_top ℕ} (i : ι)
  [∀i, normed_add_comm_group (α i)] [∀i, normed_space 𝕜 (α i)]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E] {f : E → pi_Lp p α} {s : set E} {x : E}

include hp

lemma pi_Lp.norm_coord_le_norm (x : pi_Lp p α) (i : ι) : ‖x i‖ ≤ ‖x‖ :=
begin
  unfreezingI { rcases p.trichotomy with (rfl | rfl | h) },
  { exact false.elim (lt_irrefl _ (zero_lt_one.trans_le hp.out)) },
  { rw pi_Lp.norm_eq_csupr,
    exact le_cSup (finite_range _).bdd_above (mem_range_self _) },
  { calc
    ‖x i‖ ≤ (‖x i‖ ^ p.to_real) ^ (1/p.to_real) :
      by rw [← real.rpow_mul (norm_nonneg _), mul_one_div_cancel h.ne', real.rpow_one]
    ... ≤ _ :
    begin
      have A : ∀ j, 0 ≤ ‖x j‖ ^ p.to_real := λ j, real.rpow_nonneg_of_nonneg (norm_nonneg _) _,
      simp only [pi_Lp.norm_eq_sum h, one_mul, linear_map.coe_mk],
      apply real.rpow_le_rpow (A i),
      { exact finset.single_le_sum (λ j hj, A j) (finset.mem_univ _) },
      { exact div_nonneg zero_le_one h.le, }
    end }
end

lemma pi_Lp.cont_diff_coord :
  cont_diff 𝕜 n (λ x : pi_Lp p α, x i) :=
let F : pi_Lp p α →ₗ[𝕜] α i :=
{ to_fun := λ x, x i, map_add' := λ x y, rfl, map_smul' := λ x c, rfl } in
(F.mk_continuous 1 (λ x, by simpa using pi_Lp.norm_coord_le_norm x i)).cont_diff

lemma pi_Lp.cont_diff_within_at_iff_coord :
  cont_diff_within_at 𝕜 n f s x ↔ ∀ i, cont_diff_within_at 𝕜 n (λ x, (f x) i) s x:=
begin
  classical,
  split,
  { assume h i,
    have : cont_diff 𝕜 n (λ (x : pi_Lp p α), x i) := pi_Lp.cont_diff_coord i,
    exact this.comp_cont_diff_within_at h },
  { assume h,
    let F : Π (i : ι), α i →ₗ[𝕜] pi_Lp p α := λ i,
    { to_fun := λ y, function.update 0 i y,
      map_add' :=
      begin
        assume y y',
        ext j,
        by_cases h : j = i,
        { rw h, simp },
        { simp [h], }
      end,
      map_smul' :=
      begin
        assume c x,
        ext j,
        by_cases h : j = i,
        { rw h, simp },
        { simp [h], }
      end },
    let G : Π (i : ι), α i →L[𝕜] pi_Lp p α := λ i,
    begin
      refine (F i).mk_continuous 1 (λ x, _),
      unfreezingI { rcases p.trichotomy with (rfl | rfl | h) },
      { exact false.elim (lt_irrefl _ (zero_lt_one.trans_le hp.out)) },
      { haveI : nonempty ι := ⟨i⟩,
        simp only [pi_Lp.norm_eq_csupr, linear_map.coe_mk, one_mul],
        refine cSup_le (range_nonempty _) _,
        simp only [mem_range, forall_exists_index, forall_apply_eq_imp_iff'],
        assume j,
        by_cases hji : j = i,
        { rw hji, simp only [function.update_same] },
        { simp only [hji, function.update_noteq, ne.def, not_false_iff, pi.zero_apply, norm_zero, norm_nonneg] } },
      { have : (λ j, ‖function.update 0 i x j‖ ^ p.to_real) = (λ j, if j = i then ‖x‖ ^ p.to_real else 0),
        { ext j,
          by_cases hji : j = i,
          { rw hji, simp },
          { simp [hji, h.ne'], } },
        simp only [pi_Lp.norm_eq_sum h, this, one_mul, finset.mem_univ, if_true, linear_map.coe_mk, finset.sum_ite_eq'],
        rw [← real.rpow_mul (norm_nonneg _), mul_one_div_cancel h.ne', real.rpow_one], }
    end,
    have : cont_diff_within_at 𝕜 n (λ x, (∑ (i : ι), G i ((f x) i))) s x,
    { apply cont_diff_within_at.sum (λ i hi, _),
      exact (G i).cont_diff.comp_cont_diff_within_at (h i) },
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

lemma pi_Lp.cont_diff_at_iff_coord :
  cont_diff_at 𝕜 n f x ↔ ∀ i, cont_diff_at 𝕜 n (λ x, (f x) i) x :=
by simp [← cont_diff_within_at_univ, pi_Lp.cont_diff_within_at_iff_coord]

lemma pi_Lp.cont_diff_on_iff_coord :
  cont_diff_on 𝕜 n f s ↔ ∀ i, cont_diff_on 𝕜 n (λ x, (f x) i) s :=
by { simp_rw [cont_diff_on, pi_Lp.cont_diff_within_at_iff_coord], tauto }

lemma pi_Lp.cont_diff_iff_coord :
  cont_diff 𝕜 n f ↔ ∀ i, cont_diff 𝕜 n (λ x, (f x) i) :=
by simp [← cont_diff_on_univ, pi_Lp.cont_diff_on_iff_coord]

end pi_Lp_smooth
