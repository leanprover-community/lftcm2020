import algebra.category.Ring.basic
import data.polynomial

noncomputable theory -- the default implementation of polynomials is noncomputable

local attribute [irreducible] polynomial.eval₂

-- In the previous hint, we constructed a "tactic mode" construction of the `map` field:
def Ring.polynomial : Ring ⥤ Ring :=
{ obj := λ R, Ring.of (polynomial R),
  map :=
  begin
    intros R S f,
    apply polynomial.map_ring_hom,
    apply f,
  end, }

-- In this file, I'll walk you through the process of condensing this into a term-mode proof.

-- Our first step is to notice that the `begin ... end` block beings with `intros ...`,
-- which we can turn into `λ ...,` outside the `begin .. end` block:

def Ring.polynomial_2 : Ring ⥤ Ring :=
{ obj := λ R, Ring.of (polynomial R),
  map := λ R S f,
  begin
    apply polynomial.map_ring_hom,
    apply f,
  end, }

-- If you hover over `polynomial.map_ring_hom`, you'll see it has just one arguments, so we can
-- convert the proof to

def Ring.polynomial_3 : Ring ⥤ Ring :=
{ obj := λ R, Ring.of (polynomial R),
  map := λ R S f, polynomial.map_ring_hom f }

-- 🎉
