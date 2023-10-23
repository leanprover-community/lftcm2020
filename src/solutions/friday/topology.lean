import topology.metric_space.basic

open_locale classical filter topology

namespace lftcm
open filter set

/-!
# Filters

## Definition of filters
-/

def principal {α : Type*} (s : set α) : filter α :=
{ sets := {t | s ⊆ t},
  univ_sets := begin
    -- sorry
    tauto,
    -- sorry
  end,
  sets_of_superset := begin
    -- sorry
    intros U V hU hUV,
    tauto,
    -- sorry
  end,
  inter_sets := begin
    -- sorry
    rintros U V hU hV,
    intros x xs,
    split ; tauto,
    -- sorry
  end}

def at_top : filter ℕ :=
{ sets := {s | ∃ a, ∀ b, a ≤ b → b ∈ s},
  univ_sets := begin
    -- sorry
    use 42,
    finish,
    -- sorry
  end,
  sets_of_superset := begin
    -- sorry
    rintros U V ⟨N, hN⟩ hUV,
    use N,
    tauto,
    -- sorry
  end,
  inter_sets := begin
    -- sorry
    rintros U V ⟨N, hN⟩ ⟨N', hN'⟩,
    use max N N',
    intros b hb,
    rw max_le_iff at hb,
    split ; tauto,
    -- sorry
  end}

-- The next exercise is slightly more tricky, you should probably keep it for later

def nhds (x : ℝ) : filter ℝ :=
{ sets := {s | ∃ ε > 0, Ioo (x - ε) (x + ε) ⊆ s},
  univ_sets := begin
    -- sorry
    use 42⁻¹,
    split,
    norm_num,
    tauto,
    -- sorry
  end,
  sets_of_superset := begin
    -- sorry
    rintros U V ⟨ε, hε⟩ hUV,
    use ε,
    tauto,
    -- sorry
  end,
  inter_sets := begin
    -- sorry
    rintros U V ⟨ε, hε, hU⟩ ⟨ε', hε', hV⟩,
    use [min ε ε', lt_min hε hε'],
    intros b hb,
    rw mem_Ioo at hb,
    split,
    { apply hU,
      split ; linarith [min_le_left ε ε'] },
    { apply hV,
      split ; linarith [min_le_right ε ε'] },
    -- sorry
  end}

/-
The filter axiom are also available as standalone lemmas where the filter argument is implicit
Compare
-/
#check @filter.sets_of_superset
#check @mem_of_superset

-- And analogously:
#check @inter_mem


/-!
## Definition of "tends to"
-/

-- We'll practive using tendsto by reproving the composition lemma `tendsto.comp` from mathlib
-- Let's first use the concrete definition recorded by `tendsto_def`
#check @tendsto_def
#check @preimage_comp

example {α β γ : Type*} {A : filter α} {B : filter β} {C : filter γ} {f : α → β} {g : β → γ}
  (hf : tendsto f A B) (hg : tendsto g B C) : tendsto (g ∘ f) A C :=
begin
  -- sorry
  rw tendsto_def at *,
  intros U U_in,
  rw preimage_comp,
  apply hf,
  apply hg,
  assumption,
  -- sorry
end

-- Now let's get functorial (same statement as above, different proof packaging).
example {α β γ : Type*} {A : filter α} {B : filter β} {C : filter γ} {f : α → β} {g : β → γ}
  (hf : tendsto f A B) (hg : tendsto g B C) : tendsto (g ∘ f) A C :=
begin
  calc
  map (g ∘ f) A = map g (map f A) : /- inline sorry -/ map_map/- inline sorry -/
            ... ≤ map g B         : /- inline sorry -/map_mono hf/- inline sorry -/
            ... ≤ C               : /- inline sorry -/hg/- inline sorry -/,
end

/-
Let's now focus on the pull-back operation `filter.comap` which takes `f : X → Y`
and a filter `G` on `Y` and returns a filter on `X`.
-/

#check @mem_comap -- this is by definition, the proof is `iff.rfl`

-- It also help to record a special case of one implication:
#check @preimage_mem_comap

-- The following exercise, which reproves `comap_ne_bot_iff` can start using
#check @forall_mem_nonempty_iff_ne_bot

example {α β : Type*} {f : filter β} {m : α → β} :
  (comap m f).ne_bot ↔ ∀ t ∈ f, ∃ a, m a ∈ t :=
begin
  -- sorry
  rw ← forall_mem_nonempty_iff_ne_bot,
  split ; intro h,
  { intros t t_in,
    exact h (m ⁻¹' t) ⟨t, t_in, subset.refl _⟩, },
  { rintros s ⟨u, u_in, hu⟩,
    cases h u u_in with x hx,
    exact ⟨x, hu hx⟩ },
  -- sorry
end

/-!
## Properties holding eventually
-/

/--
The next exercise only needs the definition of filters and the fact that
  `∀ᶠ x in f, p x` is a notation for `{x | p x} ∈ f`.
It is called `eventually_and` in mathlib, and won't be needed below.

For instance, applied to `α = ℕ` and the `at_top` filter above, it says
that, given two predicates `p` and `q` on natural numbers,
p n and q n for n large enough if and only if p n holds for n large enough
and q n holds for n large enough.
-/

example {α : Type*} {p q : α → Prop} {f : filter α} :
  (∀ᶠ x in f, p x ∧ q x) ↔ (∀ᶠ x in f, p x) ∧ (∀ᶠ x in f, q x) :=
begin
  -- sorry
  split,
  { intro h,
    split,
    { apply mem_of_superset h,
      intros x x_in,
      exact x_in.1 },
    { apply mem_of_superset h,
      intros x x_in,
      exact x_in.2 } },
  { intros h,
    exact f.inter_sets h.1 h.2, },
  -- sorry
end

/-!
## Topological spaces
-/

section

-- This is how we can talk about two topological spaces X and Y
variables {X Y : Type*} [topological_space X] [topological_space Y]

/-
Given a topological space `X` and some `A : set X`, we have the usual zoo of predicates
`is_open A`, `is_closed A`, `is_connected A`, `is_compact A` (and some more)

There are also additional type classes referring to properties of `X` itself,
like `compact_space X` or `connected_space X`
-/


/-- We can talk about continuous functions from `X` to `Y` -/
example (f : X → Y) : continuous f ↔ ∀ V, is_open V → is_open (f ⁻¹' V) := continuous_def

/- Each point `x` of a topological space has a neighborhood filter `𝓝 x`
   made of sets containing an open set containing `x`.
   It is always a proper filter, as recorded by `nhds_ne_bot`
   Asking for continuity is the same as asking for continuity at each point
   the right-hand side below is known as `continuous_at f x` -/
example (f : X → Y) : continuous f ↔ ∀ x, tendsto f (𝓝 x) (𝓝 (f x)) := continuous_iff_continuous_at

/- The topological structure also brings operations on sets.
   To each `A : set X`, we can associate `closure A`, `interior A` and `frontier A`.

   We'll focus on `closure A`. It is defined as the intersection of closed sets containing `A`
   but we can characterize it in terms of neighborhoods. The most concrete version is

   `mem_closure_iff_nhds : a ∈ closure A ↔ ∀ B ∈ 𝓝 a, (B ∩ A).nonempty`

   We'll pratice by reproving the slightly more abstract `mem_closure_iff_comap_ne_bot`.
   First let's review sets and subtypes. Fix a type `X` and recall
   that `A : set X` is not a type a priori, but Lean coerces automatically when needed to the
   type `↥A` whose terms are build of a term `x : X` and a proof of `x ∈ A`.
   In the other direction, inhabitants of `↥A` can be coerced to `X` automatically.
   This inclusion coercion map is called `coe : A → X` and `coe a` is also denoted by `↑a`.

   Now assume `X` is a topological space, and let's understand the closure of A in terms
   of `coe` and the neighborhood filter.

   In the next exercise, you can use `simp_rw` instead of `rw` to rewrite inside a quantifier
-/

#check inter_nonempty_iff_exists_right

example {A : set X} {x : X} :
  x ∈ closure A ↔ (comap (coe : A → X) (𝓝 x)).ne_bot :=
begin
  -- sorry
  simp_rw [mem_closure_iff_nhds, comap_ne_bot_iff, inter_nonempty_iff_exists_right],
  simp only [set_coe.exists, subtype.coe_mk],
  -- sorry
end

/-
In elementary contexts, the main property of `closure A` is that a converging sequence
`u : ℕ → X` such that `∀ n, u n ∈ A` has its limit in `closure A`.
Note we don't need all the full sequence to be in
`A`, it's enough to ask it for `n` large enough, ie. `∀ᶠ n in at_top, u n ∈ A`.
Also there is no reason to use sequences only, we can use any map and any source filter.
We hence have the important
`mem_closure_of_tendsto` : ∀ {f : β → X} {F : filter β} {a : X}
  {A : set X}, F ≠ ⊥ → tendsto f F (𝓝 a) → (∀ᶠ x in F, f x ∈ A) → a ∈ closure A

If `A` is known to be closed then we can replace `closure A` by `A`, this is
`is_closed.mem_of_tendsto`.
-/

/-
We need one last piece of filter technology: bases. By definition, each neighborhood of a point
`x` contains an *open* neighborhood of `x`.
Hence we can often restrict our attention to such neighborhoods.
The general definition recording such a situation is:

`has_basis` (l : filter α) (p : ι → Prop) (s : ι → set α) : Prop :=
(mem_iff' : ∀ t, t ∈ l ↔ ∃ i (hi : p i), s i ⊆ t)

You can now inspect three examples of how bases allow to restrict attention to certain elements
of a filter.
-/

#check @has_basis.mem_iff
#check @has_basis.tendsto_left_iff
#check @has_basis.tendsto_right_iff

-- We'll use the following bases:

#check @nhds_basis_opens'
#check @closed_nhds_basis

/--
Our main goal is now to prove the basic theorem which allows extension by continuity.
From Bourbaki's general topology book, I.8.5, Theorem 1 (taking only the non-trivial implication):

Let `X` be a topological space, `A` a dense subset of `X`, `f : A → Y`  a mapping of `A` into a
regular space `Y`. If, for each `x` in `X`, `f(y)` tends to a limit in `Y` when `y` tends to `x`
while remaining in `A` then there exists a continuous extension `φ` of `f` to `X`.

The regularity assumption on `Y` ensures that each point of `Y` has a basis of *closed*
neighborhoods, this is `closed_nhds_basis`.
It also ensures that `Y` is Hausdorff so limits in `Y` are unique, this is `tendsto_nhds_unique`.

mathlib contains a refinement of the above lemma, `dense_inducing.continuous_at_extend`,
but we'll stick to Bourbaki's version here.

Remember that, given `A : set X`, `↥A` is the subtype associated to `A`, and Lean will automatically
insert that funny up arrow when needed. And the (inclusion) coercion map is `coe : A → X`.
The assumption "tends to `x` while remaining in `A`" corresponds to the pull-back filter
`comap coe (𝓝 x)`.

Let's prove first an auxilliary lemma, extracted to simplify the context
(in particular we don't need Y to be a topological space here).
-/
lemma aux {X Y A : Type*} [topological_space X] {c : A → X} {f : A → Y} {x : X} {F : filter Y}
  (h : tendsto f (comap c (𝓝 x)) F) {V' : set Y} (V'_in : V' ∈ F) :
  ∃ V ∈ 𝓝 x, is_open V ∧ c ⁻¹' V ⊆ f ⁻¹' V' :=
begin
  -- sorry
  simpa [and_assoc] using ((nhds_basis_opens' x).comap c).tendsto_left_iff.mp h V' V'_in
  -- sorry
end

/--
Let's now turn to the main proof of the extension by continuity theorem.

When Lean needs a topology on `↥A` it will use the induced topology, thanks to the instance
`subtype.topological_space`.
This all happens automatically. The only relevant lemma is
`nhds_induced coe : ∀ a : ↥A, 𝓝 a = comap coe (𝓝 ↑a)`
(this is actually a general lemma about induced topologies).

The proof outline is:

The main assumption and the axiom of choice give a function `φ` such that
`∀ x, tendsto f (comap coe $ 𝓝 x) (𝓝 (φ x))`
(because `Y` is Hausdorff, `φ` is entirely determined, but we won't need that until we try to
prove that `φ` indeed extends `f`).

Let's first prove `φ` is continuous. Fix any `x : X`.
Since `Y` is regular, it suffices to check that for every *closed* neighborhood
`V'` of `φ x`, `φ ⁻¹' V' ∈ 𝓝 x`.

The limit assumption gives (through the auxilliary lemma above)
some `V ∈ 𝓝 x` such `is_open V ∧ coe ⁻¹' V ⊆ f ⁻¹' V'`.

Since `V ∈ 𝓝 x`, it suffices to prove `V ⊆ φ ⁻¹' V'`, ie  `∀ y ∈ V, φ y ∈ V'`.
Let's fix `y` in `V`. Because `V` is *open*, it is a neighborhood of `y`.

In particular `coe ⁻¹' V ∈ comap coe (𝓝 y)` and a fortiori `f ⁻¹' V' ∈ comap coe (𝓝 y)`.
In addition `comap coe $ 𝓝 y ≠ ⊥` because `A` is dense.

Because we know `tendsto f (comap coe $ 𝓝 y) (𝓝 (φ y))` this implies
`φ y ∈ closure V'` and, since `V'` is closed, we have proved `φ y ∈ V'`.

It remains to prove that `φ` extends `f`. This is were continuity of `f` enters the discussion,
together with the fact that `Y` is Hausdorff.
-/
example [t3_space Y] {A : set X} (hA : ∀ x, x ∈ closure A)
  {f : A → Y} (f_cont : continuous f)
  (hf : ∀ x : X, ∃ c : Y, tendsto f (comap coe $ 𝓝 x) $ 𝓝 c) :
  ∃ φ : X → Y, continuous φ ∧ ∀ a : A, φ a = f a :=
begin
  -- sorry
  choose φ hφ using hf,
  use φ,
  split,
  { rw continuous_iff_continuous_at,
    intros x,
    suffices : ∀ V' ∈ 𝓝 (φ x), is_closed V' → φ ⁻¹' V' ∈ 𝓝 x,
      by simpa [continuous_at, (closed_nhds_basis _).tendsto_right_iff],
    intros V' V'_in V'_closed,
    obtain ⟨V, V_in, V_op, hV⟩ : ∃ V ∈ 𝓝 x, is_open V ∧ coe ⁻¹' V ⊆ f ⁻¹' V',
    { exact aux (hφ x) V'_in },
    suffices : ∀ y ∈ V, φ y ∈ V',
      from mem_of_superset V_in this,
    intros y y_in,
    have hVx : V ∈ 𝓝 y := is_open.mem_nhds V_op y_in,
    haveI : (comap (coe : A → X) (𝓝 y)).ne_bot := by simpa [mem_closure_iff_comap_ne_bot] using hA y,
    apply is_closed.mem_of_tendsto V'_closed (hφ y),
    exact mem_of_superset (preimage_mem_comap hVx) hV },
  { intros a,
    have lim : tendsto f (𝓝 a) (𝓝 $ φ a),
      by simpa [nhds_induced] using hφ a,
    exact tendsto_nhds_unique lim f_cont.continuous_at },
  -- sorry
end

end

/-!
## Metric spaces
-/

/--
We now leave general topology and turn to metric spaces. The distance function is denoted by `dist`.
A slight difficulty here is that, as in Bourbaki, many results you may expect
to see stated for metric spaces are stated for uniform spaces, a more general notion that also
includes topological groups. In this tutorial we will avoid uniform spaces for simplicity.

We will prove that continuous functions from a compact metric space to a
metric space are uniformly continuous. mathlib has a much more general
version (about functions between uniform spaces...).

The lemma `metric.uniform_continuous_iff` allows to translate the general definition
of uniform continuity to the ε-δ definition that works for metric spaces only.
So let's fix `ε > 0` and start looking for `δ`.

We will deduce Heine-Cantor from the fact that a real value continuous function
on a nonempty compact set reaches its infimum. There are several ways to state that,
but here we recommend `is_compact.exists_forall_le`.

Let `φ : X × X → ℝ := λ p, dist (f p.1) (f p.2)` and let `K := { p : X × X | ε ≤ φ p }`.
Observe `φ` is continuous by assumption on `f` and using `continuous_dist`.
And `K` is closed using `is_closed_le` hence compact since `X` is compact.

Then we discuss two possibilities using `eq_empty_or_nonempty`.
If `K` is empty then we are clearly done (we can set `δ = 1` for instance).
So let's assume `K` is not empty, and choose `(x₀, x₁)` attaining the infimum
of `φ` on `K`. We can then set `δ = dist x₀ x₁` and check everything works.
-/
example {X : Type*} [metric_space X] [compact_space X] {Y : Type*} [metric_space Y]
  {f : X → Y} (hf : continuous f) : uniform_continuous f :=
begin
  -- sorry
  rw metric.uniform_continuous_iff,
  intros ε ε_pos,
  let φ : X × X → ℝ := λ p, dist (f p.1) (f p.2),
  have φ_cont : continuous φ := continuous_dist.comp (hf.prod_map hf),
  let K := { p : X × X | ε ≤ φ p },
  have K_closed : is_closed K := is_closed_le continuous_const φ_cont,
  have K_cpct : is_compact K := K_closed.is_compact,
  cases eq_empty_or_nonempty K with hK hK,
  { use [1, by norm_num],
    intros x y hxy,
    have : (x, y) ∉ K, by simp [hK],
    simpa [K] },
  { rcases K_cpct.exists_forall_le hK continuous_dist.continuous_on with ⟨⟨x₀, x₁⟩, xx_in, H⟩,
    use dist x₀ x₁,
    split,
    { change _ < _,
      rw dist_pos,
      intro h,
      have : ε ≤ 0, by simpa [*] using xx_in,
      linarith },
    { intros x x',
      contrapose!,
      intros hxx',
      linarith [H (x, x') hxx'] } },
  -- sorry
end

end lftcm
