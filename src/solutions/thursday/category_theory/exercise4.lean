import algebra.category.Ring.basic
import category_theory.yoneda
import data.polynomial.algebra_map

open category_theory
open opposite
open polynomial

noncomputable theory

/-!
We show that the forgetful functor `CommRing ⥤ Type` is (co)representable.

There are a sequence of hints available in
`hints/category_theory/hintX.lean`, for `X = 1,2,3,4`.
-/

-- Because we'll be working with `polynomial ℤ`, which is in `Type 0`,
-- we just restrict to that universe for this exercise.
notation `CommRing` := CommRing.{0}

/-!
One bonus hint before we start, showing you how to obtain the
ring homomorphism from `ℤ` into any commutative ring.
-/
example (R : CommRing) : ℤ →+* R :=
by library_search

/-!
Also useful may be the functions
-/
#print polynomial.eval₂
#print polynomial.eval₂_ring_hom

/-!
The actual exercise!
-/
def CommRing_forget_representable : Σ (R : CommRing), (forget CommRing) ≅ coyoneda.obj (op R) :=
-- sorry
⟨CommRing.of (polynomial ℤ),
 { hom :=
   { app := λ R r, polynomial.eval₂_ring_hom (algebra_map ℤ R) r, },
   inv :=
   { app := λ R f, by { dsimp at f, exact f X, }, }, }⟩
-- sorry

/-!
There are some further hints in
`hints/category_theory/exercise4/`
-/

/-
If you get an error message
```
synthesized type class instance is not definitionally equal to expression inferred by typing rules
```
while solving this exercise, see hint4.lean.
-/
