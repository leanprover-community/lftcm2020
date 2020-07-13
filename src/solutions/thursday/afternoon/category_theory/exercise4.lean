import category_theory.monoidal.category

/-!
Let's construct the category of monoid objects in a monoidal category.
-/

universes v u

open category_theory

variables (C : Type u) [category.{v} C] [monoidal_category C]

structure Mon_in :=
(X : C)
(ι : 𝟙_ C ⟶ X)
(μ : X ⊗ X ⟶ X)
-- There are three missing axioms here!

namespace Mon_in

variables {C}

def hom (A B : Mon_in C) : Type v := sorry

instance : category (Mon_in C) := sorry

end Mon_in

/-!
Bonus projects:

1. Construct the category of module objects for a fixed monoid object.
2. Check that `Mon_in Type ≌ Mon`.
3. Check that `Mon_in AddCommGroup ≌ Ring`.
4. Check that `Mon_in (Module R) ≌ Algebra R`.
5. Show that if `C` is braided (you'll have to define that first!)
   then `Mon_in C` is naturally monoidal.
6. Can you transport this monoidal structure to `Ring` or `Algebra R`?
   How does it compare to the "native" one?
-/
