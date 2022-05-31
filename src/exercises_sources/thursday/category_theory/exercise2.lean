import algebra.category.Ring.basic
import data.polynomial

/-!
Let's show that taking polynomials over a ring is functor `Ring ⥤ Ring`.
-/

noncomputable theory -- the default implementation of polynomials is noncomputable

-- Just ignore this for now: it's a hack that prevents an annoying problem,
-- and a cleaner fix is on its way to mathlib.
local attribute [irreducible] polynomial.eval₂

/-!
Hints:
* use `polynomial.map_ring_hom`
-/

def Ring.polynomial : Ring ⥤ Ring :=
sorry

def CommRing.polynomial : CommRing ⥤ CommRing :=
sorry

open category_theory

def commutes :
  (forget₂ CommRing Ring) ⋙ Ring.polynomial ≅ CommRing.polynomial ⋙ (forget₂ CommRing Ring) :=
-- Hint: You can do this in two lines, ≤ 33 columns!
sorry


/-!
There are some further hints in
`hints/category_theory/exercise2/`
-/

/-!
Bonus problem:

Why did we set `local attribute [irreducible] polynomial.eval₂`?
What goes wrong without it? Why?
-/


