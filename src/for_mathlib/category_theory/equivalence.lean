import category_theory.equivalence

open category_theory

universes v₁ v₂ u₁ u₂

namespace category_theory.equivalence

variables {C : Type u₁} [category.{v₁} C]
variables {D : Type u₂} [category.{v₂} D]
variables (e : C ≌ D)

@[simp] lemma functor_map_inj_iff {X Y : C} (f g : X ⟶ Y) : e.functor.map f = e.functor.map g ↔ f = g :=
begin
  split,
  { intro w, apply e.functor.map_injective, exact w, },
  { rintro ⟨rfl⟩, refl, }
end

@[simp] lemma inverse_map_inj_iff {X Y : D} (f g : X ⟶ Y) : e.inverse.map f = e.inverse.map g ↔ f = g :=
begin
  split,
  { intro w, apply e.inverse.map_injective, exact w, },
  { rintro ⟨rfl⟩, refl, }
end

@[simp] lemma cancel_unit_right_assoc {W X X' Y : C}
  (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X') (g' : X' ⟶ Y)  :
  f ≫ g ≫ e.unit.app Y = f' ≫ g' ≫ e.unit.app Y ↔ f ≫ g = f' ≫ g' :=
by simp only [←category.assoc, cancel_mono]

@[simp] lemma cancel_counit_inv_right_assoc {W X X' Y : D}
  (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X') (g' : X' ⟶ Y)  :
  f ≫ g ≫ e.counit_inv.app Y = f' ≫ g' ≫ e.counit_inv.app Y ↔ f ≫ g = f' ≫ g' :=
by simp only [←category.assoc, cancel_mono]

@[simp] lemma cancel_unit_right_assoc' {W X X' Y Y' Z : C}
  (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (f' : W ⟶ X') (g' : X' ⟶ Y') (h' : Y' ⟶ Z) :
  f ≫ g ≫ h ≫ e.unit.app Z = f' ≫ g' ≫ h' ≫ e.unit.app Z ↔ f ≫ g ≫ h = f' ≫ g' ≫ h' :=
by simp only [←category.assoc, cancel_mono]

@[simp] lemma cancel_counit_inv_right_assoc' {W X X' Y Y' Z : D}
  (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (f' : W ⟶ X') (g' : X' ⟶ Y') (h' : Y' ⟶ Z) :
  f ≫ g ≫ h ≫ e.counit_inv.app Z = f' ≫ g' ≫ h' ≫ e.counit_inv.app Z ↔ f ≫ g ≫ h = f' ≫ g' ≫ h' :=
by simp only [←category.assoc, cancel_mono]

end category_theory.equivalence
