import category_theory.category.basic
import category_theory.functor

import algebra.category.Group.images
import algebra.category.Group.colimits
import algebra.category.Group.abelian
import algebra.category.Module.monoidal
import algebra.category.Ring.basic

import category_theory.abelian.basic
import category_theory.limits.shapes.finite_limits

import topology.instances.real
import topology.category.Top
import topology.category.UniformSpace


/-!
This is a demo of the category theory library in mathlib,
as part of "Lean for the Curious Mathematician 2020".

You can get this file by:
* installing Lean if necessary: https://leanprover-community.github.io/get_started.html#regular-install
* `leanproject get mathlib`
* `code mathlib`
* open the file `docs/tutorial/lftcm2020/src/demos/category_theory.lean`

If you've already got a copy of `mathlib`, you should update it now, using
```
  cd /path/to/mathlib/
  git pull
  leanproject get-cache
```

There are also exercises associated with this demo, in
`exercise_sources/thursday/category_theory/`
with hints at
`hints/category_theory/`
and (partial) solutions at
`solutions/thursday/category_theory/`
Any of Exercises 1-7 should be approachable after the demo.
The later exercises are quite hard, and will take you longer than the afternoon problem session!
-/

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
To build a functor `F : C ⥤ D` we need to specify four fields
* `obj : C → D`
* `map : ∀ {X Y : C} (f : X ⟶ Y), obj X ⟶ obj Y`
* `map_id'` and `map_comp'`, expressing the functor laws.
-/

example {X : C} : C ⥤ Type* :=
{ obj := λ Y, X ⟶ Y,
  map := λ Y Y' f g, g ≫ f,
  map_id' := λ X, begin funext, simp, end,
  map_comp' := λ X Y Z f g, begin funext, simp, end }

/-!
However Lean will automatically attempt to fill in the `map_id'` and `map_comp'` fields itself,
because these fields are marked with `auto_param`. This lets us specify a tactic to use to
try to synthesize the field.

(In fact, the whole category theory library started off as an experiment to see how far we could
push this automation.)
-/

example {X : C} : C ⥤ Type* :=
{ obj := λ Y, X ⟶ Y,
  map := λ Y Y' f g, g ≫ f, }

/-!
Lean automatically checked functoriality here!
This was pretty easy: we just need to use `category.comp_id` and `category.assoc`.
The more powerful we make the `simp` lemmas, the more boring goals can be discharged automatically.

Most of the `auto_param`s appearing in mathlib so far are in the `category_theory` library,
where they are nearly all filled using the tactic `tidy`, which repeatedly attempts to use
one of a list of "conservative" tactics.

You can see what `tidy` is doing using `tidy?`:
-/

example {X : C} : C ⥤ Type* :=
{ obj := λ Y, X ⟶ Y,
  map := λ Y Y' f g, g ≫ f,
  map_id' := by tidy?,
  map_comp' := by tidy? }

/-!
Sebastien's talk on differential geometry tomorrow will give another example of `auto_param` being used.

You can also watch me doing a speed-run https://youtu.be/oz3z2NSNY8c of Floris's "pointed map" exercises
from yesterday, taking advantage of `auto_param`.
-/




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
Again, to construct a natural transformation `F ⟶ G` we need to provide two fields
* `app : Π X : C, F.obj X ⟶ G.obj X` and
* `naturality'`, which often is provided by automation.
-/


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

We've set up a number of concrete categories in mathlib.
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

noncomputable theory
open category_theory.limits

def R : Top := Top.of ℝ
def I : Top := Top.of (set.Icc 0 1 : set ℝ)
def pt : Top := Top.of unit

-- Let's construct the mapping cylinder.
def to_pt (X : Top) : X ⟶ pt :=
{ to_fun := λ _, unit.star, continuous_to_fun := continuous_const }

def I₀ : pt ⟶ I :=
{ to_fun := λ _, ⟨(0 : ℝ), by norm_num [set.left_mem_Icc]⟩,
  continuous_to_fun := continuous_const }

def I₁ : pt ⟶ I :=
{ to_fun := λ _, ⟨(1 : ℝ), by norm_num [set.right_mem_Icc]⟩,
  continuous_to_fun := continuous_const }

-- We now construct a cylinder as a categorical limit.
-- `limits.prod` is a shorthand for constructing a limit over the two point diagram:
def cylinder (X : Top) : Top := prod X I

-- To define a map to the cylinder, we give a map to each factor.
-- `prod.lift` is a helper method, providing a wrapper around `limit.lift` for binary products.
def cylinder₀ (X : Top) : X ⟶ cylinder X := prod.lift (𝟙 X) (to_pt X ≫ I₀)
def cylinder₁ (X : Top) : X ⟶ cylinder X := prod.lift (𝟙 X) (to_pt X ≫ I₁)

/--
The mapping cylinder is the pushout of the diagram
```
    X
   ↙ ↘
  Y   (X x I)
```
(`pushout` is implemented just as a wrapper around `colimit`)
-/
def mapping_cylinder {X Y : Top} (f : X ⟶ Y) : Top := pushout f (cylinder₁ X)


/-!
It's perhaps worth admitting here that constructing objects using categorical (co)limits
typically gives quite ghastly "definitional" properties --- if you want to use these objects,
you're going to have to work through their universal properties.

This is not necessarily a bad thing, but takes some getting used to.
-/

/-!
## Applications

We're only just getting to the point in mathlib where we're ready to do the sorts of mathematics
that rely on category theory as a basic language. There's lots more to come ---
big chunks of algebraic geometry, homological algebra, quantum topology, etc.

One important way in which we'll use the category theory library is to achieve polymorphism.
We don't want to separately prove theorems about sheaves of sets, sheaves of rings, etc.
Instead we'd like to talk about sheaves in an arbitrary category,
possibly with some additional typeclasses providing extra structure
(`has_products`, `concrete_category`, `monoidal_category`, etc),
and prove our theorems there.
-/

/-!
## Odds and ends

There's a bunch in mathlib's `category_theory/` folder that hasn't been mentioned at all here,
including:

* Adjunctions
* Equivalences
* Monads
* Abelian categories
* Monoidal categories
* ...

Built on top of the category theory library we have things like
* (Co)homology of chain complexes in `algebra.homology.homology`.
* The (pre)sheaf of continuous functions in `topology.sheaves.sheaf_of_functions`.
* The Giry monad in `measure_theory.category.Meas`.
-/

#print category_theory.adjunction.right_adjoint_preserves_limits

#print category_theory.abelian

-- When this tutorial was written we didn't have a single instance of `abelian` in the library.
example : abelian AddCommGroup.{0} := by apply_instance
example (R : Ring) : abelian (Module R) := by apply_instance

example (R : CommRing.{u}) : monoidal_category (Module.{u} R) := by apply_instance

example : reflective (forget₂ CpltSepUniformSpace UniformSpace) := by apply_instance
