import category_theory.limits.shapes.zero
import category_theory.full_subcategory
import algebra.homology.chain_complex
import data.int.basic

/-!
Let's give a quirky definition of a cochain complex in a category `C` with zero morphisms,
as a functor `F` from `(ℤ, ≤)` to `C`, so that `∀ i, F.map (by tidy : i ≤ i+2) = 0`.

Let's think of this as a full subcategory of all functors `(ℤ, ≤) ⥤ C`,
and realise that natural transformations are exactly chain maps.

Finally let's construct an equivalence of categories with the usual definition of chain cocomplex!
-/

open category_theory
open category_theory.limits

-- Anytime we have a `[preorder α]`, we automatically get a `[category.{v} α]` instance,
-- in which the morphisms `X ⟶ Y` are defined to be `ulift (plift X ≤ Y)`.
-- (We need those annoying `ulift` and `plift` because `X ≤ Y` is a `Prop`,
-- and the morphisms spaces of a category need to be in `Type v` for some `v`.)

namespace exercise3

variables (C : Type) [category.{0} C] [has_zero_morphisms C]

@[derive category]
def complex : Type :=
{ F : ℤ ⥤ C // ∀ i : ℤ, F.map (by tidy : i ⟶ i+2) = 0 }

def functor : complex C ⥤ cochain_complex C :=
{ obj := λ P,
  { X := P.1.obj,
    d := λ i, P.1.map (by tidy : i ⟶ i+1),
    d_squared' := sorry, },
  map := λ P Q α,
  { f := λ i, α.app i,
    comm' := sorry, } }

def long_map (P : cochain_complex C) (i j : ℤ) : P.X i ⟶ P.X j :=
if h₀ : j = i then
  eq_to_hom (by rw h₀)
else if h₁ : j = i+1 then
  P.d i ≫ eq_to_hom (by {simp [h₁]})
else 0

def inverse : cochain_complex C ⥤ complex C :=
{ obj := λ P,
  { val :=
    { obj := λ i, P.X i,
      map := λ i j p, long_map C P i j,
      map_id' := sorry,
      map_comp' := sorry },
    property := sorry, },
  map := λ P Q f,
  { app := λ i, f.f i,
    naturality' := sorry, },
  map_id' := sorry,
  map_comp' := sorry, }

def exercise3 : complex C ≌ cochain_complex C :=
sorry

end exercise3
