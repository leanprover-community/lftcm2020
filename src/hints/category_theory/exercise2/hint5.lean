import algebra.category.Ring.basic
import data.polynomial.lifts

noncomputable theory -- the default implementation of polynomials is noncomputable

local attribute [irreducible] polynomial.eval₂

def Ring.polynomial : Ring ⥤ Ring :=
{ obj := λ R, Ring.of (polynomial R),
  map := λ R S f, polynomial.map_ring_hom f }

def CommRing.polynomial : CommRing ⥤ CommRing :=
-- Let's just copy and paste the construction above, replace `Ring.of` with `CommRing.of`!
sorry
