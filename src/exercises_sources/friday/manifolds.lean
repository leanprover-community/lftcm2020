import geometry.manifold.times_cont_mdiff
import geometry.manifold.real_instances

noncomputable theory

open_locale manifold classical big_operators
open set


/-! ### Local homeomorphisms

Local homeomorphisms are globally defined maps with a globally defined "inverse", but the only
relevant set is the *source*, which should be mapped homeomorphically to the *target*.
-/



/- Define a local homeomorphism from `ℝ` to `ℝ` which is just `x ↦ -x`, but on `(-1, 1)`. In
Lean, the interval `(-1, 1)` is denoted by `Ioo (-1 : ℝ) 1` (where `o` stands for _open_). -/

@[simp] lemma neg_mem_Ioo_minus_one_one (x : ℝ) : -x ∈ Ioo (-1 : ℝ) 1 ↔ x ∈ Ioo (-1 : ℝ) 1 :=
begin
  sorry
end

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
Indeed, the two local homeos we have defined above coincide from the point of view. -/

#check @local_homeomorph.eq_on_source

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
coordinates are smooth. In Lean, this is written with `has_structure_groupoid`. A groupoid is a set
of local homeomorphisms of the model space (for example, local homeos that are smooth on their
domain). A charted space admits the groupoid as a structure groupoid if all the changes of
coordinates belong to the groupoid.

There is a difficulty that the definitions are set up to be able to also speak of smooth manifolds
with boundary or with corners, so the name of the smooth groupoid on `ℝ` has the slightly strange
name `times_cont_diff_groupoid ∞ (model_with_corners_self ℝ ℝ)`. To avoid typing again and again
`model_with_corners_self ℝ ℝ`, let us introduce a shortcut
-/

abbreviation I := model_with_corners_self ℝ ℝ

/- In the library, there are such shortcuts for manifolds modelled on `ℝ^n`, denoted with `𝓡 n`,
but for `n = 1` this does not coincide with the above one, as `ℝ^1` (a.k.a. `fin 1 → ℝ`) is not
the same as `ℝ`! -/

instance : has_groupoid myℝ (times_cont_diff_groupoid ∞ I) :=
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
  -- subset is still smooth there (`times_cont_diff.times_cont_diff_on`)
  -- (2) hopefully, there is a theorem saying that the negation function is smooth.
  -- you can either try to guess its name, or hope that `suggest` will help you there.
  sorry
end

/- The statement of the previous instance is not very readable. There is a shortcut notation: -/

instance : smooth_manifold_with_corners I myℝ := {}

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

-- lemma times_cont_diff_my_map : times_cont_diff ℝ ∞ my_map := sorry

/- does not make sense (try uncommenting it!) However, we can ask whether `my_map` is a smooth
map between manifolds, i.e., whether it is smooth when read in the charts. When we mention the
smoothness of a map, we should always specify explicitly the model with corners we are using,
because there might be several around (think of a complex manifold that you may want to consider
as a real manifold, to talk about functions which are real-smooth but not holomorphic) -/

lemma times_cont_mdiff_my_map : times_cont_mdiff I I ∞ my_map :=
begin
  -- put things in a nicer form. The simpset `mfld_simps` registers many simplification rules for
  -- manifolds. `simp` is used heavily in manifold files to bring everything into manageable form.
  rw times_cont_mdiff_iff,
  simp only [continuous_my_map] with mfld_simps,
  -- simp has erased the chart in the target, as it knows that the only chart in the manifold `ℝ`
  -- is the identity.
  assume x y,
  sorry
end

/- Now, let's go to tangent bundles. We have a smooth manifold, so its tangent bundle should also
be a smooth manifold. -/

-- the type `tangent_bundle I myℝ` makes sense
#check tangent_bundle I myℝ

/- In `mathlib`, vector bundles have preferred trivializations at each point, just as manifolds have
preferred charts.  So a point in a vector bundle can be specified just by an ordered pair. (Of
course, this specification will not vary smoothly outside a fixed chart!) -/
example : tangent_bundle I myℝ := ((4 : ℝ), 5)

/- Construct the smooth manifold structure on the tangent bundle. Hint: the answer is a one-liner,
and this instance is not really needed. -/
instance tangent_bundle_myℝ : smooth_manifold_with_corners (I.prod I) (tangent_bundle I myℝ) :=
sorry

/-
NB: the model space for the tangent bundle to a product manifold or a tangent space is not
`ℝ × ℝ`, but a copy called `model_prod ℝ ℝ`. Otherwise, `ℝ × ℝ` would have two charted space
structures with model `ℝ × ℝ`, the identity one and the product one, which are not definitionally
equal. And this would be bad.
-/
#check tangent_bundle.charted_space I myℝ

/- A smooth map between manifolds induces a map between their tangent bundles. In `mathlib` this is
called the `tangent_map` (you might instead know it as the "differential" or "pushforward" of the
map).  Let us check that the `tangent_map` of `my_map` is smooth. -/
lemma times_cont_mdiff_tangent_map_my_map :
  times_cont_mdiff (I.prod I) (I.prod I) ∞ (tangent_map I I my_map) :=
begin
  -- hopefully, there is a theorem providing the general result, i.e. the tangent map to a smooth
  -- map is smooth.
  -- you can either try to guess its name, or hope that `suggest` will help you there.
  sorry
end

/- (Harder question) Can you show that this tangent bundle is homeomorphic to `ℝ × ℝ`? You could
try to build the homeomorphism by hand, using `tangent_map I I my_map` in one direction and a
similar map in the other direction, but it is probably more efficient to use one of the charts of
the tangent bundle.

Remember, the model space for `tangent_bundle I myℝ` is `model_prod ℝ ℝ`, not `ℝ × ℝ`. But the
topologies on `model_prod ℝ ℝ` and `ℝ × ℝ` are the same, so it is by definition good enough to
construct a homeomorphism with `model_prod ℝ ℝ`.
 -/

def my_homeo : tangent_bundle I myℝ ≃ₜ (ℝ × ℝ) :=
begin
  sorry
end

/-!
### The language of manifolds

In this paragraph, we will try to write down interesting statements of theorems, without proving them. The
goal here is that Lean should not complain on the statement, but the proof should be sorried.
-/

/- Here is a first example, to show you how diffeomorphisms are currently named
(we will probably introduce an abbreviation, but this hasn't been done yet): -/

/-- Two zero-dimensional connected manifolds are diffeomorphic. -/
theorem diffeomorph_of_zero_dim_connected
  (M M' : Type*) [topological_space M] [topological_space M']
  [charted_space (euclidean_space (fin 0)) M] [charted_space (euclidean_space (fin 0)) M']
  [connected_space M] [connected_space M'] :
  nonempty (structomorph (times_cont_diff_groupoid ∞ (𝓡 0)) M M') :=
sorry

/- Do you think that this statement is correct? (note that we have not assumed that our manifolds
are smooth, nor that they are separated, but this is maybe automatic in zero dimension).

Now, write down a version of this theorem in dimension 1, replacing the first sorry with meaningful content
(and adding what is needed before the colon): -/

/-- Two one-dimensional smooth compact connected manifolds are diffeomorphic. -/
theorem diffeomorph_of_one_dim_compact_connected

  :
  sorry
:=  sorry

/- You will definitely need to require smoothness and separation in this case, as it is wrong otherwise.
Note that Lean won't complain if you don't put these assumptions, as the theorem would still make
sense, but it would just turn out to be wrong.

The previous statement is not really satisfactory: we would instead like to express that any such
manifold is diffeomorphic to the circle. The trouble is that we don't have the circle as a smooth
manifold yet. Let's cheat and introduce it nevertheless.
-/

@[derive topological_space]
definition sphere (n : ℕ) : Type := {x : euclidean_space (fin (n+1)) // ∥x∥ = (1 : ℝ)}

instance (n : ℕ) : charted_space (euclidean_space (fin n)) (sphere n) := sorry
instance (n : ℕ) : smooth_manifold_with_corners (𝓡 n) (sphere n) := sorry
instance (n : ℕ) : connected_space (sphere (n+1)) := sorry

/- The next two instances are easier to prove, you can prove them or leave them sorried
as you like. For the second one, you may need to use facts of the library such as -/
#check compact_iff_compact_space
#check metric.compact_iff_closed_bounded

instance (n : ℕ) : t2_space (sphere n) :=
begin
  sorry
end

instance (n : ℕ) : compact_space (sphere n) :=
begin
  sorry
end

/- Now, you can prove that any one-dimensional compact connected manifold is diffeomorphic to
the circle -/
theorem diffeomorph_circle_of_one_dim_compact_connected
  (M : Type*) [topological_space M] [charted_space (euclidean_space (fin 1)) M]
  [connected_space M] [compact_space M] [t2_space M] :
  nonempty (structomorph (times_cont_diff_groupoid ∞ (𝓡 1)) M (sphere 1)) :=
sorry




/-!
### Further things to do

1) can you prove `diffeomorph_of_zero_dim_connected`?

2) Try to express and then prove the local inverse theorem in real manifolds: if a map between
real manifolds (without boundary, modelled on a complete vector space) is smooth, then it is
a local homeomorphism around each point. We already have versions of this statement in mathlib
for functions between vector spaces, but this is very much a work in progress.

3) What about trying to prove `diffeomorph_of_one_dim_compact_connected`? (I am not sure mathlib
is ready for this, as the proofs I am thinking of are currently a little bit too high-powered.
If you manage to do it, you should absolutely PR it!)


-/
