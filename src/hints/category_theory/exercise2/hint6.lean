import algebra.category.Ring.basic
import data.polynomial.lifts

noncomputable theory -- the default implementation of polynomials is noncomputable

local attribute [irreducible] polynomial.eval₂

def Ring.polynomial : Ring ⥤ Ring :=
{ obj := λ R, Ring.of (polynomial R),
  map := λ R S f, polynomial.map_ring_hom f }

def CommRing.polynomial : CommRing ⥤ CommRing :=
{ obj := λ R, CommRing.of (polynomial R),
  map := λ R S f, polynomial.map_ring_hom f }

open category_theory

def commutes :
  (forget₂ CommRing Ring) ⋙ Ring.polynomial ≅ CommRing.polynomial ⋙ (forget₂ CommRing Ring) :=
-- We're trying to construct an isomorphism between functors here,
-- so let's just set up a stub for the structure:
{ hom :=
  { app := sorry,
    naturality' := sorry, },
  inv :=
  { app := sorry,
    naturality' := sorry },
  hom_inv_id' := sorry,
  inv_hom_id' := sorry, }.
