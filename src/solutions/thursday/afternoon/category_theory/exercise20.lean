import for_mathlib.category_theory -- This imports some simp lemmas that I realised belong in mathlib while writing this exercise.

universes v₁ v₂ u₁ u₂

open category_theory

variables {C : Type u₁} [category.{v₁} C]
variables {D : Type u₂} [category.{v₂} D]

lemma equiv_reflects_mono {X Y : C} (f : X ⟶ Y) (e : C ≌ D)
  (hef : mono (e.functor.map f)) : mono f :=
begin
  tidy,
  apply e.functor.map_injective,
  apply (cancel_mono (e.functor.map f)).1,
  apply e.inverse.map_injective,
  simp,
  assumption
end

lemma equiv_preserves_mono {X Y : C} (f : X ⟶ Y) [mono f] (e : C ≌ D) :
  mono (e.functor.map f) :=
begin
  tidy,
  replace w := congr_arg (λ k : Z ⟶ e.functor.obj Y, e.inverse.map k) w,
  simp at w,
  simp only [←category.assoc, cancel_mono] at w,
  simp at w,
  exact w,
end
