import category_theory.isomorphism
import category_theory.yoneda

open category_theory
open opposite

variables {C : Type*} [category C]

def iso_of_hom_iso_attempt_1 (X Y : C) (h : yoneda.obj X ≅ yoneda.obj Y) : X ≅ Y :=
-- We're trying to construct an isomorphism, so our first task is to write a stub for the structure:
{ }

/-
This says:

```
invalid structure value { ... }, field 'hom' was not provided
invalid structure value { ... }, field 'inv' was not provided
```

so let's try again:
-/

def iso_of_hom_iso_attempt_2 (X Y : C) (h : yoneda.obj X ≅ yoneda.obj Y) : X ≅ Y :=
{ hom := sorry,
  inv := sorry, }

/-
This says:
  ```
  `chain` tactic made no progress
  state:
  C : Type u_1,
  _inst_1 : category C,
  X Y : C,
  h : yoneda.obj X ≅ yoneda.obj Y
  ⊢ sorry ≫ sorry = 𝟙 X

  `chain` tactic made no progress
  state:
  C : Type u_1,
  _inst_1 : category C,
  X Y : C,
  h : yoneda.obj X ≅ yoneda.obj Y
  ⊢ sorry ≫ sorry = 𝟙 Y
  ```

What's going on? An isomorphism in fact has two more fields, called `hom_inv_id'` and `inv_hom_id'`.
These are both marked using an `auto_param`, and so a tactic called `obviously` is trying to solve
them for us, but can't because they don't yet make sense.

Let's add in those fields:
-/

def iso_of_hom_iso_attempt_3 (X Y : C) (h : yoneda.obj X ≅ yoneda.obj Y) : X ≅ Y :=
{ hom := sorry,
  inv := sorry,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry, }

/-
Finally it's time to think about the maths, but lets do that in the next hint file.
-/
