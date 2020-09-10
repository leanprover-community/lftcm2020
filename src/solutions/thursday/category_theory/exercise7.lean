import category_theory.monoidal.category
import algebra.category.CommRing.basic

/-!
Let's define the category of monoid objects in a monoidal category.
-/

open category_theory

variables (C : Type*) [category C] [monoidal_category C]

structure Mon_ :=
(X : C)
(ι : 𝟙_ C ⟶ X)
(μ : X ⊗ X ⟶ X)
-- There are three missing axioms here!
-- Use `λ_ X`, `ρ_ X` and `α_ X Y Z` for unitors and associators.
-- omit
(μ_ι : (λ_ X).inv ≫ (ι ⊗ 𝟙 X) ≫ μ = 𝟙 X)
(ι_μ : (ρ_ X).inv ≫ (𝟙 X ⊗ ι) ≫ μ = 𝟙 X)
(μ_assoc : (α_ X X X).hom ≫ (𝟙 X ⊗ μ) ≫ μ = (μ ⊗ 𝟙 X) ≫ μ)
-- omit

namespace Mon_

variables {C}

@[ext]
structure hom (M N : Mon_ C) :=
(hom : M.X ⟶ N.X)
-- What are the axioms?
-- omit
(ι_hom' : M.ι ≫ hom = N.ι . obviously)
(μ_hom' : M.μ ≫ hom = (hom ⊗ hom) ≫ N.μ . obviously)
-- omit

-- omit
restate_axiom hom.ι_hom'
restate_axiom hom.μ_hom'
attribute [simp, reassoc] hom.ι_hom hom.μ_hom

@[simps]
def id (M : Mon_ C) : hom M M :=
{ hom := 𝟙 M.X, }

@[simps]
def comp {M N O : Mon_ C} (f : hom M N) (g : hom N O) : hom M O :=
{ hom := f.hom ≫ g.hom, }
-- omit

instance : category (Mon_ C) :=
-- sorry
{ hom := λ M N, hom M N,
  id := id,
  comp := λ M N O f g, comp f g, }
-- sorry

end Mon_

/-!
(Note: since LFTCM2020, the goal of this exercise has been PR'd to mathlib,
under `category_theory.monoidal.internal`, along with several of the projects listed below.)
Bonus projects (all but the first will be non-trivial with today's mathlib):
* ✓ Construct the category of module objects for a fixed monoid object.
* ✓ Check that `Mon_ Type ≌ Mon`.
* Check that `Mon_ Mon ≌ CommMon`, via the Eckmann-Hilton argument.
  (You'll have to hook up the cartesian monoidal structure on `Mon` first.)
* Check that `Mon_ AddCommGroup ≌ Ring`.
  (You'll have to hook up the monoidal structure on `AddCommGroup`.
  Currently we have the monoidal structure on `Module R`; perhaps one could specialize to `R = ℤ`
  and transport the monoidal structure across an equivalence? This sounds like some work!)
* ✓ Check that `Mon_ (Module R) ≌ Algebra R`.
* Show that if `C` is braided (you'll have to define that first!)
   then `Mon_ C` is naturally monoidal.
* Can you transport this monoidal structure to `Ring` or `Algebra R`?
  How does it compare to the "native" one?
-/
