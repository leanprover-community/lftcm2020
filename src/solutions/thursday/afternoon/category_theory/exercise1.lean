import algebra.category.CommRing
import category_theory.yoneda

open category_theory
open opposite
open polynomial

noncomputable theory

/-!
# Exercise 1

We show that the forgetful functor `CommRing ⥤ Type` is (co?)representable.

There are a sequence of hints available in
`hints/thursday/afternoon/category_theory/hintX.lean`, for `X = 1,2,3,4`.
-/
section exercise1

-- Because we'll be working with `polynomial ℤ`, which is in `Type 0`,
-- we just restrict to that universe for this exercise.
notation `CommRing` := CommRing.{0}

/-!
Before getting to the actual exercise,
I'm going to prove three facts about ring homomorphisms, which you may find useful.
You can just skip over them for now!
-/
lemma helper₀ (R S : CommRing) (f : R ⟶ S) (i : ℤ) :
  f (algebra_map ℤ R i) = algebra_map ℤ S i :=
by simp

lemma helper₁ (R S : CommRing) (p : polynomial ℤ) (f : R ⟶ S) (r : R) :
  eval₂ (algebra_map ℤ S) (f r) p = f (eval₂ (algebra_map ℤ R) r p) :=
begin
  dsimp [eval₂, finsupp.sum],
  simp only [f.map_sum, f.map_mul, f.map_pow, helper₀],
end

lemma helper₂ (R : CommRing) (p : polynomial ℤ) (f : polynomial ℤ →+* R) :
  eval₂ (algebra_map ℤ R) (f X) p = f p :=
begin
  dsimp [eval₂, finsupp.sum],
  simp_rw [←helper₀ (CommRing.of (polynomial ℤ)) R f],
  simp_rw [←f.map_pow, ←f.map_mul, ←f.map_sum],
  congr,
  conv_rhs { rw [←polynomial.sum_C_mul_X_eq p], },
  simp [finsupp.sum],
end

/-!
One bonus hint before we start, showing you how to obtain the
ring homomorphism from `ℤ` into any commutative ring.
-/
example (R : CommRing) : ℤ →+* R :=
by library_search

/-!
The actual exercise!
-/
def CommRing_forget_representable : Σ (R : CommRing), (forget CommRing) ≅ coyoneda.obj (op R) :=
-- sorry
⟨CommRing.of (polynomial ℤ),
 { hom :=
   { app := λ R r, polynomial.eval₂_ring_hom (algebra_map ℤ R) r,
     naturality' := λ R S f, by { ext r p, simp only [coe_eval₂_ring_hom, coe_comp], apply helper₁, }, },
   inv :=
   { app := λ R f, by { dsimp at f, exact f X, }, },
   inv_hom_id' := by { ext R f p, apply helper₂, }, }⟩
-- sorry

end exercise1
