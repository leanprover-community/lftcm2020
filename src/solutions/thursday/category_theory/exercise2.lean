import algebra.category.CommRing.basic
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
@[simps]
def Ring.polynomial : Ring ⥤ Ring :=
-- sorry
{ obj := λ R, Ring.of (polynomial R),
  map := λ R S f, polynomial.map_ring_hom f,
  map_id' := by { intros, ext; simp, },
  map_comp' := by { intros, ext; simp, }, }
-- sorry

@[simps]
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

/-!
Bonus problem:

Why did we set `local attribute [irreducible] polynomial.eval₂`?
What goes wrong without it? Why?
-/
-- omit

local attribute [semireducible] polynomial.eval₂

/- def Ring.polynomial' : Ring ⥤ Ring :=
{ obj := λ R, Ring.of (polynomial R),
  map := λ R S f, ring_hom.of (polynomial.map f),
  map_comp' := λ R S T f g, begin refl end, }.  -/

  -- fails, but takes >5s seconds to do so!

/-!
What's going on?

For some reason trying to solve the goal in `map_comp'` using `refl` takes a huge amount of time.
This causes the automation which is responsible for
automatically proving functoriality of functors to time out, and fail.

How can `refl` take so long? Isn't it just checking if two things are the same?
The problem is that when we work in type theory, in principle no definition is "opaque",
and Lean sometimes has to unfold definitions in order to compare if two things are actually the same.

Usually it's pretty conservative about this, and manages to avoid unfolding too deeply
before coming up with an answer, but in bad cases it can get really bad.

Somehow this is happening here!

The solution we have available is to mark definitions as `[irreducible]`,
which (almost, but not quite completely) prevents Lean from unfolding when checking
definitional equality. Of course, this has a consequence --- Lean will sometimes
fail to prove things by `refl` now!

The solution to this is to provide a thorough API for our important definitions,
so that after some point in the development one never needs to unfold the actual definition again,
but one can work through theorems proved about the definition
(e.g. characterisations and universal properties).

An important example of this is that we have marked `real` as `[irreducible]` in Lean ---
after you've got things working, no one should ever have to know whether the "actual definition"
is in terms of Cauchy sequences or Dedekind cuts.

Unfortunately at this point we don't use `[irreducible]` often enough in Lean, and improving this
aspect of mathlib is an ongoin project.
-/
-- omit
