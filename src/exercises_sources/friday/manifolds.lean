import ...for_mathlib.manifolds
import geometry.manifold.cont_mdiff_mfderiv

noncomputable theory

open_locale manifold classical big_operators
open set

universe u


/-!
## Reminder on updating the exercises

These instructions are now available at:
https://leanprover-community.github.io/lftcm2020/exercises.html

To get a new copy of the exercises,
run the following commands in your terminal:

```
leanproject get lftcm2020
cp -r lftcm2020/src/exercises_sources/ lftcm2020/src/my_exercises
code lftcm2020
```

To update your exercise files, run the following commands:

```
cd /path/to/lftcm2020
git pull
leanproject get-mathlib-cache
```

Don’t forget to copy the updated files to `src/my_exercises`.

-/

/-!
## An overview of manifolds in Lean, discussing design decisions

Warning: there are sorries in this section, they are not supposed to be filled! The exercises sections
start later, and there you will have plenty of sorries to fill.

What is a manifold?

1) allow field other than `ℝ` or `ℂ`?
2) allow infinite dimension?
3) allow boundary?
4) allow model space depending on the point of the manifold?

Bourbaki: 2, 4 (and just definitions and statements, no proofs!)
Lean: 1, 2, 3

Perelman geometrization theorem : any compact connected irreducible 3-manifold can
be cut along tori into finitely many pieces, each of which has a _geometric structure_ of
finite volume, i.e., it is locally like a model space, with changes of coordinates given
locally by the action of a Lie group

Typical dynamics theorem : let `M` be a compact manifold, and `f : M → M` a map with property
such and such. Then ...

Or : Consider a hyperbolic surface of genus `g`, and a random geodesic of length `T`. How many
times does it typically self-intersect?


Manifold in Lean:

* charted space structure, i.e., set of local homeos to a model space. This is data, fixed
  once and for all (and a typeclass)
* compatibility condition, i.e., the change of coordinates should belong to some subgroup
  of the group of local homeos of the model space. This is Prop (and a typeclass). The same
  manifold can be at the same time an analytic manifold, a smooth manifold and a topological
  manifold (with the same fixed atlas).
* A charted space is a smooth manifold (with corners) if it is compatible with the smooth
  groupoid on the model space. To cover uniformly both situations with and without boundary,
  the smooth groupoid is with respect to a map `I : H → E` (think of `H` as the half-space and
  `E` the full space), which is the identity in the boundaryless situation, the inclusion in
  the half-space situation. This map `I` is called a _model with corners_. The most standard ones
  (identity in `ℝ^n` and inclusion of half-space in `ℝ^n`) have dedicated notations:
  `𝓡 n` and `𝓡∂ n`.
-/

#check charted_space (euclidean_half_space 1) (Icc (0 : ℝ) 1)
#check has_groupoid (Icc (0 : ℝ) 1) (cont_diff_groupoid ∞ (𝓡∂ 1))
#check smooth_manifold_with_corners (𝓡∂ 1) (Icc (0 : ℝ) 1)

-- atlases are not maximal in general

#check (cont_diff_groupoid ∞ (𝓡∂ 1)).maximal_atlas (Icc (0 : ℝ) 1)

-- let's try to put a smooth manifold structure on the sphere
-- (we don't have submanifolds yet, but it's coming in the near future)

@[derive topological_space]
definition sphere (n : ℕ) : Type := metric.sphere (0 : euclidean_space ℝ (fin (n+1))) 1

instance (n : ℕ) : has_coe (sphere n) (euclidean_space ℝ (fin (n+1))) := ⟨subtype.val⟩

instance (n : ℕ) : charted_space (euclidean_space ℝ (fin n)) (sphere n) :=
{ atlas            := begin sorry end,
  chart_at         := begin sorry end,
  mem_chart_source := begin sorry end,
  chart_mem_atlas  := begin sorry end }

instance (n : ℕ) : smooth_manifold_with_corners (𝓡 n) (sphere n) :=
{ compatible := begin
    assume e e' he he',
    sorry
  end }

-- smooth functions

def inc (n : ℕ) : sphere n → euclidean_space ℝ (fin (n+1)) :=
λ p : sphere n, (p : euclidean_space ℝ (fin (n+1)))

lemma inc_smooth (n : ℕ) : cont_mdiff (𝓡 n) (𝓡 (n+1)) ∞ (inc n) :=
begin
  rw cont_mdiff_iff,
  split,
  { exact continuous_subtype_coe, },
  { assume x y,
    sorry }
end

lemma inc_continuous (n : ℕ) : continuous (inc n) :=
(inc_smooth n).continuous

lemma inc_mdifferentiable (n : ℕ) : mdifferentiable (𝓡 n) (𝓡 (n+1)) (inc n) :=
(inc_smooth n).mdifferentiable le_top

-- tangent space and tangent bundles

example (n : ℕ) (p : sphere n) (v : tangent_space (𝓡 n) p) :
  tangent_bundle (𝓡 n) (sphere n) :=
⟨p, v⟩

-- tangent map, derivatives

example (n : ℕ) : cont_mdiff ((𝓡 n).prod (𝓡 n)) ((𝓡 (n+1)).prod (𝓡 (n+1))) ∞
  (tangent_map (𝓡 n) (𝓡 (n+1)) (inc n)) :=
(inc_smooth n).cont_mdiff_tangent_map le_top

example (n : ℕ) (f : sphere n → sphere (n^2)) (p : sphere n) (v : tangent_space (𝓡 n) p) :
  mfderiv (𝓡 n) (𝓡 (n^2)) f p v = (tangent_map (𝓡 n) (𝓡 (n^2)) f ⟨p, v⟩).2 :=
rfl

/- Can you express the sphere eversion theorem, i.e., the fact that there is a smooth isotopy
of immersions between the canonical embedding of the sphere `S^2` and `ℝ^3`, and the antipodal
embedding?

Note that we haven't defined immersions in mathlib, but you can jut require that the fiber
derivative is injective everywhere, which is easy to express if you know that the derivative
of a function `f` from a manifold of dimension `2` to a manifold of dimension `3` at a point `x` is
`mfderiv (𝓡 2) (𝓡 3) f x`.

Don't forget to require the global smoothness of the map! You may need to know that the interval
`[0,1]`, called `Icc (0 : ℝ) 1` in Lean, already has a manifold (with boundary!) structure,
where the corresponding model with corners is called `𝓡∂ 1`.
-/
theorem sphere_eversion :
  ∃ f : (Icc (0 : ℝ) 1) × sphere 2 → euclidean_space ℝ (fin 3),
  cont_mdiff ((𝓡∂ 1).prod (𝓡 2)) (𝓡 3) ∞ f
  ∧ ∀ (t : (Icc (0 : ℝ) 1)), ∀ (p : sphere 2),
    function.injective (mfderiv (𝓡 2) (𝓡 3) (f ∘ λ y, (t, y)) p)
  ∧ ∀ (p : sphere 2), f (0, p) = p
  ∧ ∀ (p : sphere 2), f (1, p) = - p :=
sorry

/- Dicussing three (controversial?) design decisions

#### Local homeos

What is a local homeo `f` between an open subset of `E` and an open subset of `F`?
1) a map defined on a subtype: `f x` only makes sense for `x : f.source`
2) a map defined on the whole space `E`, but taking values in `option F = F ∪ {junk}`, with
  `f x = junk` when `x ∉ f.source`
3) a map defined on the whole space `E`, taking values in `F`, and we don't care about its values
  outside of `f.source`.

Just like division by zero! But worse:

* issue with 1): you keep intersecting chart domains. But the subtype `u ∩ v` is not the same as
  the subtype `v ∩ u`, so you keep adding casts everywhere
* issue with 2): if you want to say that a chart is smooth, then you define to define smooth functions
  between `option E` and `option F` when `E` and `F` are vector spaces. All notions need to be
  redefined with `option`.
* issue with 3): it works perfectly well, but it makes mathematicians unhappy/uneasy (and it is *not*
  equivalent to 1) or 2) when one of the spaces is empty)

I picked 3)

#### Tangent vectors

What is a tangent vector (for a manifold `M` modelled on a vector space `E`)?
1) An equivalence class of germs of curves
2) A derivation
3) Physicist point of view: I don't know what a tangent vector is, but I know in charts.
  Mathematician's interpretation: equivalence class of `(e, v)` where `e` is a chart at `x`, `v` a vector
  in the vector space, and `(e, v) ∼ (e', v')` if `D(e' ∘ e ⁻¹) v = v'`
4) ...

Issues:
1) Pictures are pretty, but this doesn't bring anything compared to 3) when you go down to details.
   And what about boundaries, where you can only have a half-curve
2) Need partitions of unity to show that this is local and coincides with the usual point of view.
   Doesn't work well in finite smoothness, nor in complex manifolds
3) Fine, works in all situations, but requires a lot of work to define the equivalence classes,
   the topology, check that the topology is compatible with the vector space structure, and so on.
   In a vector space, the tangent space is not defeq to the vector space itself
4) Pick one favorite chart at `x`, say `e_x`, and *define* the tangent space at `x` to be `E`,
   but "seen" in the chart `e_x` (this will show up in the definition of the derivative : the
   derivative of `f : M → M'` at `x` is defined to be the derivative of the map
   `e_{f x} ∘ f ∘ e_x⁻¹`). Works perfectly fine, but makes mathematicians unhappy/uneasy.
   (Axiom of choice? In fact we put the choice of `e_x` in the *definition* of charted spaces,
   so not further choice)

I picked 4)

#### Smooth functions in manifolds with boundary

Usual definition of smooth functions in a half space: extend to a smooth function a little bit
beyond the boundary, so one only really needs to speak of smooth functions in open subsets of
vector spaces.

When you define the derivative, you will need to check that it does not depend on the choice
of the extension. Even worse when you want to define the tangent bundle: choose an open extension
of your manifold with boundary, and then check that the restriction of the tangent bundle does
not depend on the choice of the extension. Very easy when handwaving, nightmare to formalize.
(What is the extension of the manifold with boundary? Another type?)

Instead, if you define derivatives in (non-open) domains, you can talk of smooth functions in
domains, and do everything without extending. Need to know this early enough: when starting to
define derivatives, you should already think of manifolds with boundaries! That's what we did
in mathlib.

Difficulty: if a domain `s` is too small (think `s = ℝ ⊆ ℝ^2`), the values of `f` on `s` do not
prescribe uniquely a derivative, so `fderiv_within_at ℝ f s x` may behave badly: the derivative of
a sum might be different from sum of derivatives, as there is an arbitrary choice to be made.
This does not happen with the half-space, as it is large enough: derivatives within domains only
work well if the tangent directions span the whole space. Predicate `unique_diff_on` for sets
in vector spaces. You won't find this in books!
-/


/-! ## Exercises -/

/-! ### Local homeomorphisms

Local homeomorphisms are globally defined maps with a globally defined "inverse", but the only
relevant set is the *source*, which should be mapped homeomorphically to the *target*.
-/

-- set up a simple helper simp lemma to simplify our life later.
@[simp] lemma neg_mem_Ioo_minus_one_one (x : ℝ) : -x ∈ Ioo (-1 : ℝ) 1 ↔ x ∈ Ioo (-1 : ℝ) 1 :=
begin
  sorry
end

/- Define a local homeomorphism from `ℝ` to `ℝ` which is just `x ↦ -x`, but on `(-1, 1)`. In
Lean, the interval `(-1, 1)` is denoted by `Ioo (-1 : ℝ) 1` (where `o` stands for _open_). -/

def my_first_local_homeo : local_homeomorph ℝ ℝ :=
{ to_fun := λ x, -x,
  inv_fun := λ x, -x,
  source := Ioo (-1) 1,
  target := sorry,
  map_source' :=
  begin
    sorry
  end,
  map_target' :=
  begin
    sorry
  end,
  left_inv' :=
  begin
    sorry
  end,
  right_inv' :=
  begin
    sorry
  end,
  open_source := sorry,
  open_target := sorry,
  continuous_to_fun := sorry,
  continuous_inv_fun := sorry }

/- Two simple lemmas that will prove useful below. You can leave them sorried if you like. -/

lemma ne_3_of_mem_Ioo {x : ℝ} (h : x ∈ Ioo (-1 : ℝ) 1) : x ≠ 3 :=
begin
  sorry
end

lemma neg_ne_3_of_mem_Ioo {x : ℝ} (h : x ∈ Ioo (-1 : ℝ) 1) : -x ≠ 3 :=
begin
sorry
end

/- Now, define a second local homeomorphism which is almost like the previous one.  You may find the
following lemma useful for `continuous_to_fun`: -/
#check continuous_on.congr

def my_second_local_homeo : local_homeomorph ℝ ℝ :=
{ to_fun := λ x, if x = 3 then 0 else - x,
  inv_fun := λ x, -x,
  source := Ioo (-1) 1,
  target := sorry,
  map_source' := sorry,
  map_target' := sorry,
  left_inv' := sorry,
  right_inv' := sorry,
  open_source := sorry,
  open_target := sorry,
  continuous_to_fun :=
  begin
    sorry
  end,
  continuous_inv_fun := sorry }

/- Although the two above local homeos are the same for all practical purposes as they coincide
where relevant, they are not *equal*: -/

lemma my_first_local_homeo_ne_my_second_local_homeo :
  my_first_local_homeo ≠ my_second_local_homeo :=
begin
  sorry
end

/- The right equivalence relation for local homeos is not equality, but `eq_on_source`.
Indeed, the two local homeos we have defined above coincide from this point of view. -/

#check local_homeomorph.eq_on_source

lemma eq_on_source_my_first_local_homeo_my_second_local_homeo :
  local_homeomorph.eq_on_source my_first_local_homeo my_second_local_homeo :=
begin
  sorry
end


/-! ### An example of a charted space structure on `ℝ`

A charted space is a topological space together with a set of local homeomorphisms to a model space,
whose sources cover the whole space. For instance, `ℝ` is already endowed with a charted space
structure with model space `ℝ`, where the unique chart is the identity:
-/

#check charted_space_self ℝ

/- For educational purposes only, we will put another charted space structure on `ℝ` using the
local homeomorphisms we have constructed above. To avoid using too much structure of `ℝ` (and to
avoid confusing Lean), we will work with a copy of `ℝ`, on which we will only register the
topology. -/

@[derive topological_space]
def myℝ : Type := ℝ

instance : charted_space ℝ myℝ :=
{ atlas := { local_homeomorph.refl ℝ, my_first_local_homeo },
  chart_at := λ x, if x ∈ Ioo (-1 : ℝ) 1 then my_first_local_homeo else local_homeomorph.refl ℝ,
  mem_chart_source :=
  begin
  sorry
  end,
  chart_mem_atlas :=
  begin
    sorry
  end }

/- Now come more interesting bits. We have endowed `myℝ` with a charted space structure, with charts
taking values in `ℝ`. We want to say that this is a smooth structure, i.e., the changes of
coordinates are smooth. In Lean, this is written with `has_groupoid`. A groupoid is a set
of local homeomorphisms of the model space (for example, local homeos that are smooth on their
domain). A charted space admits the groupoid as a structure groupoid if all the changes of
coordinates belong to the groupoid.

There is a difficulty that the definitions are set up to be able to also speak of smooth manifolds
with boundary or with corners, so the name of the smooth groupoid on `ℝ` has the slightly strange
name `cont_diff_groupoid ∞ (model_with_corners_self ℝ ℝ)`. To avoid typing again and again
`model_with_corners_self ℝ ℝ`, let us introduce a shortcut
-/

abbreviation 𝓡1 := model_with_corners_self ℝ ℝ

/- In the library, there are such shortcuts for manifolds modelled on `ℝ^n`, denoted with `𝓡 n`,
but for `n = 1` this does not coincide with the above one, as `ℝ^1` (a.k.a. `fin 1 → ℝ`) is not
the same as `ℝ`! Still, since they are of the same nature, the notation we have just introduced
is very close, compare `𝓡1` with `𝓡 1` (and try not to get confused): -/

instance smooth_myℝ : has_groupoid myℝ (cont_diff_groupoid ∞ 𝓡1) :=
begin
  -- in theory, we should prove that all compositions of charts are diffeos, i.e., they are smooth
  -- and their inverse are smooth. For symmetry reasons, it suffices to check one direction
  apply has_groupoid_of_pregroupoid,
  -- take two charts `e` and `e'`
  assume e e' he he',
  -- if next line is a little bit slow for your taste, you can replace `simp` with `squeeze_simp`
  -- and then follow the advice
  simp [atlas] at he he',
  dsimp,
  -- to continue, some hints:
  -- (1) don't hesitate to use the fact that the restriction of a smooth function to a
  -- subset is still smooth there (`cont_diff.cont_diff_on`)
  -- (2) hopefully, there is a theorem saying that the negation function is smooth.
  -- you can either try to guess its name, or hope that `suggest` will help you there.
  sorry
end

/- The statement of the previous instance is not very readable. There is a shortcut notation: -/

instance : smooth_manifold_with_corners 𝓡1 myℝ := { .. smooth_myℝ }

/- We will now study a very simple map from `myℝ` to `ℝ`, the identity. -/

def my_map : myℝ → ℝ := λ x, x

/- The map `my_map` is a map going from the type `myℝ` to the type `ℝ`. From the point of view of
the kernel of Lean, it is just the identity, but from the point of view of structures on `myℝ`
and `ℝ` it might not be trivial, as we have registered different instances on these two types. -/

/- The continuity should be trivial, as the topologies on `myℝ` and `ℝ` are definitionally the
same. So `continuous_id` might help. -/

lemma continuous_my_map : continuous my_map :=
sorry

/- Smoothness should not be obvious, though, as the manifold structures are not the same: the atlas
on `myℝ` has two elements, while the atlas on `ℝ` has one single element.
Note that `myℝ` is not a vector space, nor a normed space, so one can not ask whether `my_map`
is smooth in the usual sense (as a map between vector spaces): -/

-- lemma cont_diff_my_map : cont_diff ℝ ∞ my_map := sorry

/- does not make sense (try uncommenting it!) However, we can ask whether `my_map` is a smooth
map between manifolds, i.e., whether it is smooth when read in the charts. When we mention the
smoothness of a map, we should always specify explicitly the model with corners we are using,
because there might be several around (think of a complex manifold that you may want to consider
as a real manifold, to talk about functions which are real-smooth but not holomorphic) -/

lemma cont_mdiff_my_map : cont_mdiff 𝓡1 𝓡1 ∞ my_map :=
begin
  -- put things in a nicer form. The simpset `mfld_simps` registers many simplification rules for
  -- manifolds. `simp` is used heavily in manifold files to bring everything into manageable form.
  rw cont_mdiff_iff,
  simp only [continuous_my_map] with mfld_simps,
  -- simp has erased the chart in the target, as it knows that the only chart in the manifold `ℝ`
  -- is the identity.
  assume x y,
  sorry
end

/- Now, let's go to tangent bundles. We have a smooth manifold, so its tangent bundle should also
be a smooth manifold. -/

-- the type `tangent_bundle 𝓡1 myℝ` makes sense
#check tangent_bundle 𝓡1 myℝ

/- The tangent space above a point of `myℝ` is just a one-dimensional vector space
(identified with `ℝ`).
So, one can prescribe an element of the tangent bundle as a pair (more on this below) -/
example : tangent_bundle 𝓡1 myℝ := ⟨(4 : ℝ), 0⟩

/- Type-class inference can construct the smooth manifold structure on the tangent bundle. -/
example : smooth_manifold_with_corners (𝓡1.prod 𝓡1) (tangent_bundle 𝓡1 myℝ) :=
sorry

/-
NB: the model space for the tangent bundle to a product manifold or a tangent space is not
`ℝ × ℝ`, but a copy called `model_prod ℝ ℝ`. Otherwise, `ℝ × ℝ` would have two charted space
structures with model `ℝ × ℝ`, the identity one and the product one, which are not definitionally
equal. And this would be bad.
-/
example : charted_space (model_prod ℝ ℝ) (tangent_bundle 𝓡1 myℝ) :=
sorry

/-
The charts of any smooth vector bundle are characterized by `fiber_bundle.charted_space_chart_at`
-/
#check @fiber_bundle.charted_space_chart_at

/- A smooth map between manifolds induces a map between their tangent bundles. In `mathlib` this is
called the `tangent_map` (you might instead know it as the "differential" or "pushforward" of the
map).  Let us check that the `tangent_map` of `my_map` is smooth. -/
lemma cont_mdiff_tangent_map_my_map :
  cont_mdiff (𝓡1.prod 𝓡1) (𝓡1.prod 𝓡1) ∞ (tangent_map 𝓡1 𝓡1 my_map) :=
begin
  -- hopefully, there is a theorem providing the general result, i.e. the tangent map to a smooth
  -- map is smooth.
  -- you can either try to guess its name, or hope that `suggest` will help you there.
  sorry
end

/- (Harder question) Can you show that this tangent bundle is homeomorphic to `ℝ × ℝ`? You could
try to build the homeomorphism by hand, using `tangent_map 𝓡1 𝓡1 my_map` in one direction and a
similar map in the other direction, but it is probably more efficient to use one of the charts of
the tangent bundle.

Remember, the model space for `tangent_bundle 𝓡1 myℝ` is `model_prod ℝ ℝ`, not `ℝ × ℝ`. But the
topologies on `model_prod ℝ ℝ` and `ℝ × ℝ` are the same, so it is by definition good enough to
construct a homeomorphism with `model_prod ℝ ℝ`.
 -/

def my_homeo : tangent_bundle 𝓡1 myℝ ≃ₜ (ℝ × ℝ) :=
begin
  sorry
end

/- Up to now, we have never used the definition of the tangent bundle, and this corresponds to
the usual mathematical practice: one doesn't care if the tangent space is defined using germs of
curves, or spaces of derivations, or whatever equivalent definition. Instead, one relies all the
time on functoriality (i.e., a smooth map has a well defined derivative, and they compose well,
together with the fact that the tangent bundle to a vector space is the product).

If you want to know more about the internals of the tangent bundle in mathlib, you can browse
through the next section, but it is maybe wiser to skip it on first reading, as it is not needed
to use the library
-/

section you_should_probably_skip_this

/- If `M` is a manifold modelled on a vector space `E`, then the underlying type for the tangent
bundle is effectively `Σ (x : M), tangent_space x M` (i.e., the disjoint union of the tangent spaces,
indexed by `x` -- this is a basic object in dependent type theory). And `tangent_space x M`
is just (a copy of) `E` by definition. -/

lemma tangent_bundle_myℝ_is_prod : tangent_bundle 𝓡1 myℝ = bundle.total_space ℝ (λ x : myℝ, ℝ) :=
sorry

/- This means that you can specify a point in the tangent bundle as a pair `⟨x, v⟩`.
However, in general, a tangent bundle is not trivial: the topology on `tangent_bundle 𝓡1 myℝ` is *not*
the product topology. Instead, the tangent space at a point `x` is identified with `ℝ` through some
preferred chart at `x`, called `chart_at ℝ x`, but the way they are glued together depends on the
manifold and the charts.

In vector spaces, the tangent space is canonically the product space, with the same topology, as
there is only one chart so there is no strange gluing at play. The fact that the canonical map
from the sigma type to the product type (called `equiv.sigma_equiv_prod`) is a homeomorphism is
given in the library by `tangent_bundle_model_space_homeomorph` (note that this is a definition,
constructing the homeomorphism, instead of a proposition asserting that `equiv.sigma_equiv_prod`
is a homeomorphism, because we use bundled homeomorphisms in mathlib).

Let us register the identification explicitly, as a homeomorphism. You can use the relevant fields
of `tangent_bundle_model_space_homeomorph` to fill the nontrivial fields here.
-/

def tangent_bundle_vector_space_triv (E : Type u) [normed_add_comm_group E] [normed_space ℝ E] :
  tangent_bundle (model_with_corners_self ℝ E) E ≃ₜ E × E :=
{ to_fun := λ p, (p.1, p.2),
  inv_fun := λ p, ⟨p.1, p.2⟩,
  left_inv := sorry,
  right_inv := sorry,
  continuous_to_fun := begin
    sorry
  end,
  continuous_inv_fun :=
  begin
    sorry
  end }

/- Even though the tangent bundle to `myℝ` is trivial abstractly, with this construction the
tangent bundle is *not* the product space with the product topology, as we have used various charts
so the gluing is not trivial. The following exercise unfolds the definition to see what is going on.
It is not a reasonable exercise, in the sense that one should never ever do this when working
with a manifold! -/

lemma crazy_formula_after_identifications (x : ℝ) (v : ℝ) :
  let p : tangent_bundle 𝓡1 myℝ := ⟨(3 : ℝ), 0⟩ in
  chart_at (model_prod ℝ ℝ) p ⟨x, v⟩ = if x ∈ Ioo (-1 : ℝ) 1 then (x, -v) else (x, v) :=
begin
  -- this exercise is not easy (and shouldn't be: you are not supposed to use the library like this!)
  -- if you really want to do this, you should unfold as much as you can using simp and dsimp, until you
  -- are left with a statement speaking of derivatives of real functions, without any manifold code left.
  sorry
end

end you_should_probably_skip_this

/-!
### The language of manifolds

In this paragraph, we will try to write down interesting statements of theorems, without proving them. The
goal here is that Lean should not complain on the statement, but the proof should be sorried.
-/

/- Here is a first example, already filled up, to show you how diffeomorphisms are currently named
(we will probably introduce an abbreviation, but this hasn't been done yet).
Don't try to fill the sorried proof! -/

/-- Two zero-dimensional connected manifolds are diffeomorphic. -/
theorem diffeomorph_of_zero_dim_connected
  (M M' : Type*) [topological_space M] [topological_space M']
  [charted_space (euclidean_space ℝ (fin 0)) M] [charted_space (euclidean_space ℝ (fin 0)) M']
  [connected_space M] [connected_space M'] :
  nonempty (structomorph (cont_diff_groupoid ∞ (𝓡 0)) M M') :=
sorry

/- Do you think that this statement is correct? (note that we have not assumed that our manifolds
are smooth, nor that they are separated, but this is maybe automatic in zero dimension).

Now, write down a version of this theorem in dimension 1, replacing the first sorry with meaningful content
(and adding what is needed before the colon).
Don't try to fill the sorried proof! -/

/-- Two one-dimensional smooth compact connected manifolds are diffeomorphic. -/
theorem diffeomorph_of_one_dim_compact_connected
  
  :
  sorry
:= sorry

/- You will definitely need to require smoothness and separation in this case, as it is wrong otherwise.
Note that Lean won't complain if you don't put these assumptions, as the theorem would still make
sense, but it would just turn out to be wrong.

The previous statement is not really satisfactory: we would instead like to express that any such
manifold is diffeomorphic to the circle. The trouble is that we don't have the circle as a smooth
manifold yet. Since we have cheated and introduced it (with sorries) at the beginning of the tutorial,
let's cheat again and use it to reformulate the previous statement.
-/

-- the next result is not trivial, leave it sorried (but you can work on it if you don't like
-- manifolds and prefer topology -- then please PR it to mathlib!).
instance connected_sphere (n : ℕ) : connected_space (sphere (n+1)) := sorry

/- The next two instances are easier to prove, you can prove them or leave them sorried
as you like. For the second one, you may need to use facts of the library such as -/
#check is_compact_iff_compact_space
#check metric.is_compact_iff_is_closed_bounded

instance (n : ℕ) : t2_space (sphere n) :=
begin
  sorry
end

instance (n : ℕ) : compact_space (sphere n) :=
begin
  sorry
end

/- Now, you can prove that any one-dimensional compact connected manifold is diffeomorphic to
the circle. Here, you should fill the `sorry` (but luckily you may use
`diffeomorph_of_one_dim_compact_connected`). -/
theorem diffeomorph_circle_of_one_dim_compact_connected
  (M : Type*) [topological_space M] [charted_space (euclidean_space ℝ (fin 1)) M]
  [connected_space M] [compact_space M] [t2_space M] [smooth_manifold_with_corners (𝓡 1) M] :
  nonempty (structomorph (cont_diff_groupoid ∞ (𝓡 1)) M (sphere 1)) :=
sorry


/- What about trying to say that there are uncountably many different smooth structures on `ℝ⁴`?
(see https://en.wikipedia.org/wiki/Exotic_R4). The library is not really designed with this in mind,
as in general we only work with one differentiable structure on a space, but it is perfectly
capable of expressing this fact if one uses the `@` version of some definitions.

Don't try to fill the sorried proof!
-/

theorem exotic_ℝ4 :
  sorry
  :=
sorry

/-!
### Smooth functions on `[0, 1]`

In this paragraph, you will prove several (math-trivial but Lean-nontrivial) statements on the smooth
structure of `[0,1]`. These facts should be Lean-trivial, but they are not (yet) since there is essentially
nothing in this direction for now in the library.

The goal is as much to be able to write the statements as to prove them. Most of the necessary vocabulary
has been introduced above, so don't hesitate to browse the file if you are stuck. Additionally, you will
need the notion of a smooth function on a subset: it is `cont_diff_on` for functions between vector
spaces and `cont_mdiff_on` for functions between manifolds.

Try to formulate the next math statements in Lean, and prove them (but see below for hints):

Lemma cont_mdiff_g : the inclusion `g` of `[0, 1]` in `ℝ` is smooth.

Lemma msmooth_of_smooth : Consider a function `f : ℝ → [0, 1]`, which is smooth in the usual sense as a function
from `ℝ` to `ℝ` on a set `s`. Then it is manifold-smooth on `s`.

Definition : construct a function `f` from `ℝ` to `[0,1]` which is the identity on `[0, 1]`.

Theorem : the tangent bundle to `[0, 1]` is homeomorphic to `[0, 1] × ℝ`

Hint for the last theorem: don't try to unfold the definition of the tangent bundle, it will only get you
into trouble. Instead, use the derivatives of the maps `f` and `g`, and rely on functoriality
to check that they are inverse to each other. (This advice is slightly misleading as these derivatives
do not go between the right spaces, so you will need to massage them a little bit).

A global advice: don't hesitate to use and abuse `simp`, it is the main workhorse in this
area of mathlib.
-/

/- After doing the exercise myself, I realized it was (way!) too hard. So I will give at least the statements
of the lemmas, to guide you a little bit more. To let you try the original version if you want,
I have left a big blank space to avoid spoilers. -/


























































def g : Icc (0 : ℝ) 1 → ℝ := subtype.val

-- smoothness results for `euclidean_space` are expressed for general `L^p` spaces
-- (as `euclidean_space` has the `L^2` norm), in:
#check pi_Lp.cont_diff_coord
#check pi_Lp.cont_diff_on_iff_coord

lemma cont_mdiff_g : cont_mdiff (𝓡∂ 1) 𝓡1 ∞ g :=
begin
  sorry
end

lemma msmooth_of_smooth {f : ℝ → Icc (0 : ℝ) 1} {s : set ℝ} (h : cont_diff_on ℝ ∞ (λ x, (f x : ℝ)) s) :
  cont_mdiff_on 𝓡1 (𝓡∂ 1) ∞ f s :=
begin
  sorry
end

/- A function from `ℝ` to `[0,1]` which is the identity on `[0,1]`. -/
def f : ℝ → Icc (0 : ℝ) 1 :=
λ x, ⟨max (min x 1) 0, by simp [le_refl, zero_le_one]⟩

lemma cont_mdiff_on_f : cont_mdiff_on 𝓡1 (𝓡∂ 1) ∞ f (Icc 0 1) :=
begin
  sorry
end

lemma fog : f ∘ g = id :=
begin
  sorry
end

lemma gof : ∀ x ∈ Icc (0 : ℝ) 1, g (f x) = x :=
begin
  sorry
end

def G : tangent_bundle (𝓡∂ 1) (Icc (0 : ℝ) 1) → (Icc (0 : ℝ) 1) × ℝ :=
λ p, (p.1, ((tangent_bundle_vector_space_triv ℝ) (tangent_map (𝓡∂ 1) 𝓡1 g p)).2)

lemma continuous_G : continuous G :=
begin
  sorry
end

def F : (Icc (0 : ℝ) 1) × ℝ → tangent_bundle (𝓡∂ 1) (Icc (0 : ℝ) 1) :=
λ p, tangent_map_within 𝓡1 (𝓡∂ 1) f (Icc 0 1)
  ((tangent_bundle_vector_space_triv ℝ).symm (p.1, p.2))

lemma continuous_F : continuous F :=
begin
  sorry
end

lemma FoG : F ∘ G = id :=
begin
  sorry
end

lemma GoF : G ∘ F = id :=
begin
  sorry
end

def my_tangent_homeo : tangent_bundle (𝓡∂ 1) (Icc (0 : ℝ) 1) ≃ₜ (Icc (0 : ℝ) 1) × ℝ :=
sorry


/-!
### Further things to do

1) can you prove `diffeomorph_of_zero_dim_connected` or `connected_sphere`?

2) Try to express and then prove the local inverse theorem in real manifolds: if a map between
real manifolds (without boundary, modelled on a complete vector space) is smooth, then it is
a local homeomorphism around each point. We already have versions of this statement in mathlib
for functions between vector spaces, but this is very much a work in progress.

3) What about trying to prove `diffeomorph_of_one_dim_compact_connected`? (I am not sure mathlib
is ready for this, as the proofs I am thinking of are currently a little bit too high-powered.
If you manage to do it, you should absolutely PR it!)

4) Why not contribute to the proof of `sphere_eversion`? You can have a look at
https://leanprover-community.github.io/sphere-eversion/ to learn more about this project
by Patrick Massot.
-/

