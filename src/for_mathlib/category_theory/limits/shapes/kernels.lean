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


namespace kernel_fork

variables {X Y : C} {f : X ⟶ Y}

/-- This is a slightly more convenient method to verify that a kernel fork is a limit cone. It
    only asks for a proof of facts that carry any mathematical content -/
def is_limit_aux (t : kernel_fork f)
  (lift : Π (s : kernel_fork f), s.X ⟶ t.X)
  (fac : ∀ (s : kernel_fork f), lift s ≫ t.ι = s.ι)
  (uniq : ∀ (s : kernel_fork f) (m : s.X ⟶ t.X) (w : m ≫ t.ι = s.ι), m = lift s) :
  is_limit t :=
{ lift := lift,
  fac' := λ s j,
  begin
    cases j,
    { exact fac s, },
    { simp, },
  end,
  uniq' := λ s m w, uniq s m (w limits.walking_parallel_pair.zero), }

/--
This is a more convenient formulation to show that a `pullback_cone` constructed using
`pullback_cone.mk` is a limit cone.
-/
def is_limit.mk {W : C} (g : W ⟶ X) (eq : g ≫ f = 0)
  (lift : Π {W' : C} (g' : W' ⟶ X) (eq' : g' ≫ f = 0), W' ⟶ W)
  (fac : ∀ {W' : C} (g' : W' ⟶ X) (eq' : g' ≫ f = 0), lift g' eq' ≫ g = g')
  (uniq : ∀ {W' : C} (g' : W' ⟶ X) (eq' : g' ≫ f = 0) (m : W' ⟶ W) (w : m ≫ g = g'), m = lift g' eq') :
  is_limit (kernel_fork.of_ι g eq) :=
is_limit_aux _ (λ s, lift s.ι s.condition) (λ s, fac s.ι s.condition) (λ s, uniq s.ι s.condition)

end kernel_fork

end category_theory.limits
