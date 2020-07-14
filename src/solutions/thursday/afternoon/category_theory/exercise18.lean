import category_theory.limits.shapes.pullbacks

/-!
Thanks to Markus Himmel for suggesting this question.
-/

open category_theory
open category_theory.limits

/-!
Let C be a category, X and Y be objects and f : X ⟶ Y be a morphism. Show that f is an epimorphism
if and only if the diagram

X --f--→ Y
|        |
f        𝟙
|        |
↓        ↓
Y --𝟙--→ Y

is a pushout.
-/

universes v u

variables {C : Type u} [category.{v} C]

def pushout_of_epi {X Y : C} (f : X ⟶ Y) [epi f] :
  is_colimit (pushout_cocone.mk (𝟙 Y) (𝟙 Y) rfl : pushout_cocone f f) :=
-- Hint: you can start a proof with `fapply pushout_cocone.is_colimit.mk`
-- to save a little bit of work over just building a `is_colimit` structure directly.
begin
  fapply pushout_cocone.is_colimit.mk,
  { intro s,
    apply s.ι.app walking_span.left, },
  { tidy, },
  { tidy,
    apply (cancel_epi f).1,
    have fst := s.ι.naturality walking_span.hom.fst,
    simp at fst,
    rw fst,
    have snd := s.ι.naturality walking_span.hom.snd,
    simp at snd,
    rw snd, },
  { tidy, specialize w walking_span.left, tidy, }
end

theorem epi_of_pushout {X Y : C} (f : X ⟶ Y)
  (is_colim : is_colimit (pushout_cocone.mk (𝟙 Y) (𝟙 Y) rfl : pushout_cocone f f)) : epi f :=
{ left_cancellation := λ Z g h hf,
  begin
    let a := pushout_cocone.mk _ _ hf,
    have hg : is_colim.desc a = g, {
      have := is_colim.fac a walking_span.left,
      simp at this,
      dsimp at this,
      simp at this,
      exact this,
    },
    have hh : is_colim.desc a = h, {
      have := is_colim.fac a walking_span.right,
      simp at this,
      dsimp at this,
      simp at this,
      exact this,
    },
    rw [←hg, ←hh],
  end }
