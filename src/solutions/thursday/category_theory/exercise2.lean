import algebra.category.Ring.basic
import data.polynomial.lifts

/-!
Let's show that taking polynomials over a ring is functor `Ring ⥤ Ring`.
-/

noncomputable theory -- the default implementation of polynomials is noncomputable

/-!
Hints:
* use `polynomial.map_ring_hom`
-/

def Ring.polynomial : Ring ⥤ Ring :=
-- sorry
{ obj := λ R, Ring.of (polynomial R),
  map := λ R S f, polynomial.map_ring_hom f,
  map_id' := by { intros, ext; simp, },
  map_comp' := by { intros, ext; simp, }, }
-- sorry

def CommRing.polynomial : CommRing ⥤ CommRing :=
-- sorry
{ obj := λ R, CommRing.of (polynomial R),
  map := λ R S f, polynomial.map_ring_hom f,
  map_id' := by { intros, ext; simp, },
  map_comp' := by { intros, ext; simp, }, }
-- sorry

open category_theory

def commutes :
  (forget₂ CommRing Ring) ⋙ Ring.polynomial ≅ CommRing.polynomial ⋙ (forget₂ CommRing Ring) :=
-- Hint: You can do this in two lines, ≤ 33 columns!
-- sorry
{ hom := { app := λ R, 𝟙 _, },
  inv := { app := λ R, 𝟙 _, }, }.
-- sorry


/-!
There are some further hints in
`hints/category_theory/exercise2/`
-/
