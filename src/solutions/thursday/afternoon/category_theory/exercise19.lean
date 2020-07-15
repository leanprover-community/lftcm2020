import category_theory.isomorphism
import category_theory.yoneda


open category_theory
open opposite

universes v u

variables {C : Type u} [category.{v} C]

/- Hint 1:
`yoneda` is set up so that `(yoneda.obj X).obj (op Y) = (Y ⟶ X)`
(we need to write `op Y` to explicitly move `Y` to the opposite category).
-/

/- Hint 2:
If you have a natural isomorphism `α : F ≅ G`, you can access
* the forward natural transformation as `α.hom`
* the backwards natural transformation as `α.inv`
* the component at `X`, as an isomorphism `F.obj X ≅ G.obj X` as `α.app X`.
-/

/- Hint 3:
You might find the lemma `nat_iso.hom_inv_id_app` useful.
-/

def iso_of_hom_iso (X Y : C) (h : yoneda.obj X ≅ yoneda.obj Y) : X ≅ Y :=
{ hom := (h.app (op X)).hom (𝟙 X),
  inv := (h.symm.app (op Y)).hom (𝟙 Y),
  hom_inv_id' :=
  begin
    simp,
    have := nat_iso.hom_inv_id_app h (op X),
    have := congr_fun this _,
    exact this,
  end,
  inv_hom_id' :=
  begin
    simp,
    have := nat_iso.inv_hom_id_app h (op Y),
    have := congr_fun this _,
    exact this,
  end, }
