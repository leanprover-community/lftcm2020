import category_theory.isomorphism
import category_theory.yoneda

open category_theory
open opposite

variables {C : Type*} [category C]

/-! Hint 1:
`yoneda` is set up so that `(yoneda.obj X).obj (op Y) = (Y ⟶ X)`
(we need to write `op Y` to explicitly move `Y` to the opposite category).
-/

/-! Hint 2:
If you have a natural isomorphism `α : F ≅ G`, you can access
* the forward natural transformation as `α.hom`
* the backwards natural transformation as `α.inv`
* the component at `X`, as an isomorphism `F.obj X ≅ G.obj X` as `α.app X`.
-/

def iso_of_hom_iso (X Y : C) (h : yoneda.obj X ≅ yoneda.obj Y) : X ≅ Y :=
{ hom := (h.hom.app (op X)) (𝟙 X),
  inv := (h.inv.app (op Y)) (𝟙 Y) }

/-!
There are some further hints in
`src/hints/thursday/afternoon/category_theory/exercise1/`
-/
