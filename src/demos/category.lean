import category_theory.category
import category_theory.functor
import category_theory.functor_category
import algebra.category.CommRing
import algebra.category.Group.images
import algebra.homology.homology
import category_theory.limits.shapes.finite_limits
import data.int.parity
import data.zmod.basic

open category_theory

/-!
## Categories

Categories are implemented in mathlib as a typeclass, parametrised by the type of objects.

Thus to talk about an arbitrary category, we can write
-/
variables (C : Type) [category C]

/-!
There is special notation for the morphisms in a category: if `X Y : C`, we write
* `X ⟶ Y` for the type of morphisms from `X` to `Y`.
  (To enter the special arrow `⟶`, type `\hom`, or hover over the symbol to see the hint.)
* `𝟙 X` is a the identity morphisms on `X` (i.e., a term of type `X ⟶ X`).
* If `f : X ⟶ Y` and `g : Y ⟶ Z`, then we write `f ≫ g` for the composition, a morphism `X ⟶ Z`.
-/

example {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
  (f ≫ (𝟙 X ≫ g)) ≫ h = f ≫ g ≫ h :=
begin
  rw category.id_comp,
  rw category.assoc,
  -- alternatively, just `simp` will do
end

/-!
## Functors

To introduce functors, we'll need a second category around.
-/
variables (D : Type) [category D]

/-!
We write a functor as `F : C ⥤ D`.
(Unlike categories, which are partially unbundled, a functor is "fully bundled",
containing the function on objects as field. This parallels the design for algebraic structures.)
-/

example (F : C ⥤ D) (X : C) : F.map (𝟙 X) = 𝟙 (F.obj X) :=
F.map_id X

example (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : F.map (f ≫ g) = F.map f ≫ F.map g :=
F.map_comp f g

/-!
The identity functor is written as `𝟭 C`, and functor composition is written `⋙`.
-/
example (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) : (𝟭 C ⋙ F).map (f ≫ 𝟙 Y) = F.map f :=
begin
  rw functor.comp_map,
  rw functor.map_comp,
  rw category_theory.functor.map_id, -- yuck! we really should fix this
  rw functor.id_map,
  rw functor.map_comp,
  rw category_theory.functor.map_id,
  rw category.comp_id,
  -- or just replace the entire proof with `by simp`
end

/-!
## Natural transformations

The collection of functors from `C` to `D` has been given the structure of a category:
to talk about the natural transformations, you just write `F ⟶ G` using the usual "morphism" arrow.

If `α : F ⟶ G`, then `α.app X` is the component at `X`, i.e. a morphism `F.obj X ⟶ G.obj X`.
-/
example {F G : C ⥤ D} {α : F ⟶ G} {X Y : C} (f : X ⟶ Y) :
  F.map f ≫ α.app Y = α.app X ≫ G.map f :=
α.naturality f   -- or just `by simp`


/-!
## A note on universes

Before we go on, we should mention a slight complication: out in the world we meet
both small and large categories. In set-theoretic foundations, this distinction is about
whether the objects form a set or merely a class.

In the type-theoretic foundations used in Lean, this distinction is about whether
the objects and morphisms live in the same universe, or if the objects live one universe higher up.

Rather than making separate definitions for the two cases, we simply allow the objects and morphisms
to live in two unrelated universes. To talk about a general category we thus write
-/
universes u v

variables (E : Type u) [category.{v} E]

/-!
This says that the objects live in universe `u`, while the morphisms live in universe `v`.
In fact, the definition `category` is paramaterised by two universe levels, and
when we write `category.{v} E` Lean actually understands this as `category.{v u} E`,
automatically filling in the second argument from the universe level of `E`.

There are abbreviations available for the two standard cases:
* if `E : Type (u+1)`, then `large_category E` means `category.{u (u+1)} E`
* if `E : Type u`, then `small_category E` means `category.{u u} E`.

However you'll rarely use these except when setting up particular examples.
All the "concrete" categories, like `Group`, `Ring`, and `Top`, described below,
are instances of `large_category`.
Typically the indexing diagrams for limits and colimits are instances of `small_category`.

If you're talking about an arbitrary category, and you don't mind whether it is small or large,
you should just allow two independent universe variables, as above.
-/


/-!
## Concrete categories

We've set up a number of concrete categories in mathlib,
although at this point they are not widely used.
-/

example (R S : CommRing) (f : R ⟶ S) (x y : R) : f (x * y) = f x * f y := by simp

/-!
Note here we have a particularly succinct way of introducing a commutative ring:
we just write `R : CommRing`, rather than `(R : Type) [comm_ring R]`.
Rather than writing `f : R →+* S` for a `ring_hom`, we can just use the morphism arrow,
and Lean works out the appropriate notion automatically.

There's a coercion from `CommRing` to `Type`,
so we can still talk about elements by writing `x : R`,
and morphisms automatically behave properly as functions (e.g. in `f (x * y)`).
-/


/-!
## Limits and colimits

We talk about limits using the following notions:
* For `F : J ⥤ C`, `c : cone F` consists of
  * `c.X : C` an object in `C`, and
  * `c.π`, a natural transformation with components `c.π.app j : c.X ⟶ F.obj j`.
* For `c : cone F`, `is_limit c` expresses that `c` is a limit cone.
* `has_limit F`, a typeclass specifying a particular choice of limit cone for a functor `F`.
* `has_limits_of_shape J C`, a typeclass specifying a choice of limit for any functor `F : J ⥤ C`.
* `has_limits C`, a typeclass specifying a choice of limit for any functor into `C`.

(There are also all the dual notions, `cocone`, `is_colimit`, `has_colimit`, etc.)

There are also typeclasses for various "special shapes", in particular
* `has_equalizers`
* `has_pullbacks`
* `has_binary_products` / `has_finite_products` / `has_products`
* `has_terminal`

A related typeclass `has_zero_morphisms C` specifies a choice of zero morphism in each hom space,
satisfying the usual axioms (equivalent to `C` being enriched in pointed sets), and using that
we can also express some other special shapes, including
* `has_kernels`
* `has_binary_biproducts` / `has_finite_biproducts`
* `has_zero_object`

For most of the concrete categories, these instances are all available when appropriate.
-/

/-!
### Examples of using (co)limits in `Top`
-/


/-!
## Applications

We're only just getting to the point in mathlib where we're ready to do the sorts of mathematics
that rely on category theory as a basic language. There's lots more to come ---
big chunks of algebraic geometry, quantum topology, homological algebra, etc.

One important way in which we'll use the category theory library is to achieve polymorphism.
We don't want to separately prove theorems about sheaves of sets, sheaves of rings, etc.
Instead we'd like to talk about sheaves in an arbitrary category,
possibly with some additional typeclasses providing extra structure
(`has_products`, `concrete_category`, `monoidal_category`, etc),
and prove our theorems there.
-/

/-!
### Homological algebra

We've recently set up the very basics of homoological algebra using the category theory library.
There's still a way to go --- good projects for the near future include
* injective covers and resolutions
* `Ext` and `Tor`
* bicomplexes, the salamander, snake, five, and nine lemmas

Here's something you can do already:
-/

open category_theory.limits
local notation `Ab` := AddCommGroup.{0}

local attribute [instance] has_equalizers_of_has_finite_limits
local attribute [instance] has_coequalizers_of_has_finite_colimits

noncomputable theory -- `has_images Ab` is noncomputable
instance : has_image_maps Ab := sorry


open cochain_complex homological_complex

def Z := AddCommGroup.of ℤ

def mul_by (k : ℤ) : Z ⟶ Z :=
{ to_fun := λ x, (k * x : ℤ),
  map_zero' := by simp,
  map_add' := by simp [mul_add], }

/--
We define the complex `... --0--> ℤ --2--> ℤ --0--> ℤ --4--> ℤ --0--> ...`
-/
def P : cochain_complex Ab :=
{ X := λ i, Z,
  d := λ i, if i.even then mul_by i else 0,
  d_squared' :=
  begin
    ext i, dsimp,
    by_cases h : i.even;
    simp [h] with parity_simps,
  end }

#check (graded_cohomology Ab).obj P

def P_2 : P.cohomology_group 2 ≅ 0 :=
begin
  dunfold cohomology_group, -- `cohomomology_group` is an abbreviation, so we need to use `dunfold` rather than `dsimp`
  dsimp [homology_group, homological_complex.image_to_kernel_map],
  change cokernel (image_to_kernel_map 0 (mul_by 2) _) ≅ 0,
  calc _ ≅ cokernel (0 : image (0 : Z ⟶ Z) ⟶ kernel (mul_by 2)) : _
     ... ≅ kernel (mul_by 2) : _
     ... ≅ 0 : _,
  all_goals { sorry, },
end

def P_3 : P.cohomology_group 3 ≅ AddCommGroup.of (zmod 2) :=
begin
  dunfold cohomology_group,
  dsimp [homology_group, homological_complex.image_to_kernel_map],
  change cokernel (image_to_kernel_map (mul_by 2) 0 _) ≅ AddCommGroup.of (zmod 2),
  calc _ ≅ cokernel (image.ι (mul_by 2) ≫ inv (kernel.ι (0 : Z ⟶ Z))) : _
     ... ≅ cokernel (image.ι (mul_by 2)) : _
     ... ≅ cokernel (mul_by 2) : _
     ... ≅ AddCommGroup.of (zmod 2) : _,
  all_goals { sorry, },
end




/-!
## Odds and ends

There's a bunch in mathlib's `category_theory/` folder that hasn't been mentioned at all here,
including:

* Adjunctions
* Monads
* Abelian categories
* Monoidal categories

-/
