import category_theory.limits.shapes.kernels

open category_theory

namespace category_theory.limits

universes v u

variables {C : Type u} [category.{v} C] [has_zero_morphisms C]

@[simps]
def cokernel_comp_is_iso {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  [has_cokernel (f ≫ g)] [has_cokernel f] [is_iso g] :
  cokernel (f ≫ g) ≅ cokernel f :=
{ hom := cokernel.desc _ (inv g ≫ cokernel.π f) (by simp),
  inv := cokernel.desc _ (g ≫ cokernel.π (f ≫ g)) (by { rw [←category.assoc, cokernel.condition], }), }

end category_theory.limits
