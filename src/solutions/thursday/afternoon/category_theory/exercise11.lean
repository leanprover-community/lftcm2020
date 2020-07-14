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
I'm going to prove two facts about ring homomorphisms, which you may find useful.
You can just skip over them for now!
-/
@[simp]
lemma eval₂_algebra_map {S : Type*} [comm_ring S] (p : polynomial ℤ) (s : S) :
  eval₂ (algebra_map ℤ S) s p = aeval ℤ S s p :=
rfl

-- lemma helper₁ (R S : CommRing) (p : polynomial ℤ) (f : R ⟶ S) (r : R) :
--   eval₂ (algebra_map ℤ S) (f r) p = f (eval₂ (algebra_map ℤ R) r p) :=
-- begin
--   simp,
--   sorry
-- end

-- lemma helper₂ (R : CommRing) (p : polynomial ℤ) (f : polynomial ℤ →+* R) :
--   eval₂ (algebra_map ℤ R) (f X) p = f p :=
-- begin
--   simp,
--   sorry
-- end

-- lemma helper₁ {R S : Type*} [ring R] [ring S] (p : polynomial ℤ) (f : R →+* S) (r : R) :
--   eval₂ (algebra_map ℤ S) (f r) p = f (eval₂ (algebra_map ℤ R) r p) :=
-- begin
--   dsimp [eval₂, finsupp.sum],
--   simp only [f.map_sum, f.map_mul, f.map_pow, ring_hom.eq_int_cast, ring_hom.map_int_cast],
-- end

-- lemma helper₂ {R : Type*} [ring R] (p : polynomial ℤ) (f : polynomial ℤ →+* R) :
--   eval₂ (algebra_map ℤ R) (f X) p = f p :=
-- begin
--   conv_rhs { rw [←polynomial.sum_C_mul_X_eq p], },
--   dsimp [eval₂, finsupp.sum],
--   simp only [f.map_sum, f.map_mul, f.map_pow, ring_hom.eq_int_cast, ring_hom.map_int_cast],
-- end

lemma helper₁ {R A B : Type*} [comm_ring R] [ring A] [ring B] [algebra R A] [algebra R B]
  (p : polynomial R) (f : A →ₐ[R] B) (a : A) :
  eval₂ (algebra_map R B) (f a) p = f (eval₂ (algebra_map R A) a p) :=
begin
  dsimp [eval₂, finsupp.sum],
  simp only [f.map_sum, f.map_mul, f.map_pow, ring_hom.eq_int_cast, ring_hom.map_int_cast, alg_hom.commutes],
end

@[simp] lemma polynomial.C_eq_algebra_map {R : Type*} [comm_ring R] (r : R) :
  C r = algebra_map R (polynomial R) r :=
rfl

lemma helper₂ {R A : Type*} [comm_ring R] [ring A] [algebra R A] (p : polynomial R) (f : polynomial R →ₐ[R] A) :
  eval₂ (algebra_map R A) (f X) p = f p :=
begin
  conv_rhs { rw [←polynomial.sum_C_mul_X_eq p], },
  dsimp [eval₂, finsupp.sum],
  simp only [f.map_sum, f.map_mul, f.map_pow, ring_hom.eq_int_cast, ring_hom.map_int_cast],
  simp [polynomial.C_eq_algebra_map],
end


lemma helper₁' {R S : Type*} [ring R] [ring S] (p : polynomial ℤ) (f : R →+* S) (r : R) :
  eval₂ (algebra_map ℤ S) (f r) p = f (eval₂ (algebra_map ℤ R) r p) :=
helper₁ p f r

lemma helper₂' {R : Type*} [ring R] (p : polynomial ℤ) (f : polynomial ℤ →+* R) :
  eval₂ (algebra_map ℤ R) (f X) p = f p :=
begin
  conv_rhs { rw [←polynomial.sum_C_mul_X_eq p], },
  dsimp [eval₂, finsupp.sum],
  simp only [f.map_sum, f.map_mul, f.map_pow, ring_hom.eq_int_cast, ring_hom.map_int_cast],
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

-- ⟨CommRing.of (polynomial ℤ),
--  { hom :=
--    { app := λ R r, (polynomial.aeval ℤ R r).to_ring_hom,
--      naturality' := λ R S f, by { ext r p, sorry }, },
--    inv :=
--    { app := λ R f, by { dsimp at f, exact f X, }, },
--    inv_hom_id' := by { ext R f p, apply helper₂, }, }⟩


end exercise1
