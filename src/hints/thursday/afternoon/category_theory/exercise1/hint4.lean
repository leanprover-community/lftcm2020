import algebra.category.CommRing
import category_theory.yoneda

noncomputable theory

open category_theory
open opposite
open polynomial

/-!
We can "follow our nose" on the two remaining proof obligations,
and in both cases we arrive at a result that is "just about polynomials",
so we call `extract_goal` and go prove them as lemmas.
-/
def CommRing_forget_representable : Σ (R : CommRing), (forget CommRing) ≅ coyoneda.obj (op R) :=
⟨CommRing.of (polynomial ℤ),
 { hom :=
   { app := λ R r, polynomial.eval₂_ring_hom (algebra_map ℤ R) r,
     naturality' := λ R S f, begin ext r p, dsimp at *, simp, extract_goal, sorry, end, },
   inv :=
   { app := λ R f, begin dsimp at f, exact f X, end, },
   inv_hom_id' := begin ext R f p, dsimp at *, extract_goal, sorry, end, }⟩
