import algebra.category.Ring.basic
import data.polynomial.lifts

noncomputable theory -- the default implementation of polynomials is noncomputable

local attribute [irreducible] polynomial.eval₂

def Ring.polynomial : Ring ⥤ Ring :=
{ obj := λ R, Ring.of (polynomial R),
  map :=
  begin
    -- The goal is `Π {X Y : Ring}, (X ⟶ Y) → (Ring.of (polynomial ↥X) ⟶ Ring.of (polynomial ↥Y))`
    -- so we need to:
    intros R S f,
    -- The goal is now to provide a morphism in `Ring`
    -- from `Ring.of (polynomial R)` to `Ring.of (polynomial S)`.
    -- By definition this is a `ring_hom (polynomial R) (polynomial S)`,
    -- which can also be written `polynomial R →+* polynomial S`.

    -- The hint suggested looked at `polynomial.map`.
    -- If you type `#print polynomial.map` above, you'll see that it just provides a "bare function"
    -- `polynomial R → polynomial S`, rather than an actual `ring_hom`.
    -- Looking further in the same file, you can find its morphism version, called
    -- `polynomial.map_ring_hom`.

    apply polynomial.map_ring_hom,

    -- Now it's "downhill": we just tell Lean what we want to use:
    apply f,

    -- With the goals completed, you should now try to "golf" this proof to a term mode proof.
    -- The next hint file walks you through doing this.
  end, }

def CommRing.polynomial : CommRing ⥤ CommRing :=
sorry

open category_theory

def commutes :
  (forget₂ CommRing Ring) ⋙ Ring.polynomial ≅ CommRing.polynomial ⋙ (forget₂ CommRing Ring) :=
sorry
