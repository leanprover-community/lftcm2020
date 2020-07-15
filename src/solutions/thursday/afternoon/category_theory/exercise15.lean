import category_theory.limits.shapes.biproducts

/-!
Let's show that every preadditive category embeds into a preadditive category with biproducts,
and identify a good universal property.

This is a more advanced exercise, for which I've indicated a suggested structure,
but not written a full solution. I hope this structure will work out!
-/

universes v u

variables (C : Type u)

structure family :=
(ι : Type v)
[fintype : fintype ι]
[decidable_eq : decidable_eq ι]
(val : ι → C)

variables {C}

def dmatrix {X Y : family C} (Z : X.ι → Y.ι → Type*) := Π (i : X.ι) (j : Y.ι), Z i j

open category_theory

variables [category.{v} C] [preadditive C]

namespace family

def hom (X Y : family C) := dmatrix (λ i j, X.val i ⟶ Y.val j)

instance : category.{v (max u (v+1))} (family.{v} C) :=
{ hom := hom,
  id := sorry,
  comp := sorry,
  id_comp' := sorry,
  comp_id' := sorry,
  assoc' := sorry, }

variables (C)

def embedding : C ⥤ family.{v} C :=
sorry

lemma embedding.faithful : faithful (embedding C) :=
sorry

instance : preadditive (family.{v} C) :=
sorry

open category_theory.limits

instance : has_finite_biproducts (family.{v} C) :=
sorry

variables {C}

def factor {D : Type u} [category.{v} D] [preadditive D] [has_finite_biproducts D]
  (F : C ⥤ D) : family.{v} C ⥤ D :=
sorry

def factor_factorisation {D : Type u} [category.{v} D] [preadditive D] [has_finite_biproducts D]
  (F : C ⥤ D) : F ≅ embedding C ⋙ factor F :=
sorry

end family
