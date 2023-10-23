import algebra.category.Ring.basic
import category_theory.yoneda
import data.polynomial.algebra_map

noncomputable theory

open category_theory
open opposite

/-!
Let's give the forward map first, not worrying about naturality.
-/
def CommRing_forget_representable : Σ (R : CommRing), (forget CommRing) ≅ coyoneda.obj (op R) :=
⟨CommRing.of (polynomial ℤ),
 { hom :=
   { app := λ R r,
     begin
       dsimp,
       -- The goal is `CommRing.of (polynomial ℤ) ⟶ R`,
       -- and we have available `r : (forget CommRing).obj R`.
       -- The only plausible function is:
       -- "evaluation the polynomial at `r`, after mapping coefficients into `R`."
       exact polynomial.eval₂_ring_hom (algebra_map ℤ R) r
     end,
     naturality' := sorry, },
   inv := sorry,
   hom_inv_id' := sorry,
   inv_hom_id' := sorry, }⟩
