import linear_algebra.finite_dimensional
import ring_theory.algebraic
import data.zmod.basic
import tactic


section exercise1
/-
We will warm up with a well-known result:
“Subgroups of abelian groups are normal.”

Hints for proving this result:
  * Notice that `normal` is a structure,
    which you can see by going to the definition.
    The `constructor` tactic will help you to get started.
-/

namespace add_subgroup
variables {A : Type*} [add_comm_group A]

lemma normal_of_add_comm_group (H : add_subgroup A) : normal H :=
begin
  -- sorry
  constructor,
  intros x hx y,
  simpa,
  -- sorry
end

end add_subgroup

end exercise1

section exercise2
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

end exercise2

section exercise3
/-
The next exercise asks to show that a monic polynomial `f ∈ ℤ[X]` is irreducible
if it is irreducible modulo a prime `p`.
This fact is also not in mathlib.

Hint: prove the helper lemma that is stated first.

Follow-up question:
Can you generalise `irreducible_of_irreducible_mod_prime`?
-/

namespace polynomial
variables {R S : Type*} [semiring R] [integral_domain S] (φ : R →+* S)

lemma is_unit_of_is_unit_leading_coeff_of_is_unit_map
  (f : polynomial R) (hf : is_unit (leading_coeff f)) (H : is_unit (map φ f)) :
  is_unit f :=
begin
  -- sorry
  have key := degree_eq_zero_of_is_unit H,
  have hφ_lcf : φ (leading_coeff f) ≠ 0,
  { apply is_unit.ne_zero,
    apply is_unit.map',
    assumption },
  rw degree_map_eq_of_leading_coeff_ne_zero _ hφ_lcf at key,
  rw eq_C_of_degree_eq_zero key,
  apply is_unit.map',
  rw [eq_C_of_degree_eq_zero key, leading_coeff_C] at hf,
  exact hf,
  -- sorry
end

lemma irreducible_of_irreducible_mod_prime (f : polynomial ℤ) (p : ℕ) [fact p.prime]
  (h_mon : monic f) (h_irr : irreducible (map (int.cast_ring_hom (zmod p)) f)) :
  irreducible f :=
begin
  -- sorry
  split,
  { intro hf,
    apply h_irr.1,
    apply is_unit.map',
    exact hf },
  { intros g h Hf,
    have aux : is_unit (leading_coeff g * leading_coeff h),
    { rw [← leading_coeff_mul, ← Hf, h_mon.leading_coeff], exact is_unit_one },
    have lc_g_unit : is_unit (leading_coeff g),
    { apply is_unit_of_mul_is_unit_left aux },
    have lc_h_unit : is_unit (leading_coeff h),
    { apply is_unit_of_mul_is_unit_right aux },
    rw Hf at h_irr,
    simp at h_irr,
    have key_fact := h_irr.2 _ _ rfl,
    cases key_fact with Hg Hh,
    { left,
      apply is_unit_of_is_unit_leading_coeff_of_is_unit_map _ g lc_g_unit Hg },
    { right,
      apply is_unit_of_is_unit_leading_coeff_of_is_unit_map _ h lc_h_unit Hh } }
  -- sorry
end

end polynomial

end exercise3

example : true :=
begin
  exact x
end
