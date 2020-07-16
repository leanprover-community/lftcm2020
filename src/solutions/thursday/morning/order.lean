/-
# Orders

Groups, rings, fields, modules etc are in the "algebra hierarchy".

Metric and topological spaces are in the "topology hierarchy".

The other important heirarchy is the "order hierarchy".

It starts with partially ordered sets, and then goes on to lattices.

Because I like algebra, let's demonstrate the order heirarchy by
making an algebraic type, namely the type of subgroups of a group G,
and then working up the order heirarchy with it. Subgroups of a group
are ordered by inclusion, and this is where we shall start. We will
then define infs and sups, and bot and top, and go on from there.

-/
import tactic

-- The type of subgroups of a group G is called `subgroup G` in Lean.
-- It already has a lattice structure, so let's make it all again
-- from scratch.

/-- The type of subgroups of a group `G`. -/
structure subgp (G : Type) [group G] :=
-- A subgroup of G is a sub*set* of G, called `carrier`
(carrier : set G)
-- and then one axiom per piece of structure for a group (i.e. *, 1, ⁻¹)
(mul_mem' {a b : G} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier)
(one_mem' : (1 : G) ∈ carrier)
(inv_mem' {a : G} : a ∈ carrier → a⁻¹ ∈ carrier)

-- The reason we use `mul_mem'` and not `mul_mem` will become clearer
-- in a minute.

namespace subgp

-- We'll be dealing with sets, so let's open the `set` namespace

open set

-- Let G be a group, let H,J,K be subgroups of G, and let a,b,c be elements of G.
variables {G : Type} [group G] (H J K : subgp G) (a b c : G)

/-
Important point: we want to hide this "carrier" as much as possible. As
mathematicians we want to be able to say "a ∈ H", and not "a ∈ H.carrier".
This is standard abuse of notation in mathematics: is a group a set G,
or is it an ordered quadruple (G,*,1,⁻¹)? We don't want to worry about
this distinction. So let's define notation a ∈ H.
-/

-- want to be able to say `a ∈ H` if `H : subgroup G`
instance : has_mem G (subgp G) := ⟨λ g H, g ∈ H.carrier⟩

-- Now we can restate our axioms without using this `carrier` nonsense.

theorem mul_mem {x y : G} : x ∈ H → y ∈ H → x * y ∈ H := mul_mem' H
theorem one_mem : (1 : G) ∈ H := one_mem' H
theorem inv_mem {x : G} : x ∈ H → x⁻¹ ∈ H := inv_mem' H

-- If the `carrier` notation leaks out, we can put it back with this lemma
lemma mem_coe {g : G} : g ∈ H.carrier ↔ g ∈ H :=
begin
  -- Both sides are definitionally equal: the definition of `g ∈ H` is `g ∈ H.carrier`.
  refl, -- note that ↔ is a reflexive binary relation! So the `refl` tactic works
end

-- We also want an extensionality lemma using this `x ∈ H` notation:
-- we want to prove that two subgroups `H` and `J` are equal if (and only if)
-- they have the same elements. Let's start by proving that
-- two subgroups are equal if the underlying subsets are equal

lemma carrier_injective (H J : subgp G) (h : H.carrier = J.carrier) : H = J :=
begin
  -- take H and J apart
  cases H, cases J,
  -- and note that they are the same set, and then a bunch of proofs
  -- which are equal by definition, so it's obvious
  simp * at *
end

-- Now let's prove that two subgroups are equal iff they have the same elements.
-- This is the most useful "extensionality lemma" so we tag it `@[ext]`.
@[ext] theorem ext {H J : subgp G} (h : ∀ (x : G), x ∈ H ↔ x ∈ J) : H = J :=
begin
  -- it suffices to prove the subsets are equal
  apply carrier_injective,
  -- Now let's use extensionality for subsets
  ext x,
  exact h x,
end

-- We also want the `iff` version of this.
theorem ext_iff {H J : subgp G} : H = J ↔ ∀ (x : G), x ∈ H ↔ x ∈ J :=
begin
  split,
  { -- one way is just a rewrite!
    intro h,
    rw h,
    simp,
  },
  { -- the other way we just did
    exact subgp.ext
  }
end

/-

## Partial orders

-/

-- These are familiar to most mathematicians. We will put a partial order
-- structure on `subgroup G`. In other words, we will create a term of
-- type `partial_order (subgroup G)`.

-- Let's define `H₁ ≤ H₂` to mean `H₁ ⊆ H₂`, using the `has_le` notation typeclass
instance : has_le (subgp G) := ⟨λ S T, S.carrier ⊆ T.carrier⟩

-- If "carrier"s leak out, we can put them back with this
lemma le_def (H J : subgp G) : H.carrier ≤ J.carrier ↔ H ≤ J :=
iff.rfl -- this is a term mode proof; iff.rfl is the name of the proof that ↔ is reflexive

-- "tidy" is a one-size-fits-all tactic which solves certain kinds of "follow your nose" goals.
instance : partial_order (subgp G) :=
{ le := (≤),
  le_refl := by tidy,
  le_trans := by tidy,
  le_antisymm := by tidy }

-- Another proof:
example : partial_order (subgp G) := partial_order.lift subgp.carrier carrier_injective

/-

This is the beginning. We now have `≤` and `<` defined on subgroups (`H < J` is
defined to mean `H ≤ J ∧ ¬ (J ≤ H)` -- this is part of the notation which comes
with partial orders).

Let's now prove that `subgp G` is a `semilattice_inf_top`. We will have to
get our hands dirty with `carrier`s because we're doing set-theoretic things.
First let's define `top` -- the biggest subgroup. The underlying carrier
is `univ : set G`, i.e. the subset `G` of `G`. You can prove the
axioms hold! The useful piece of interface for `univ` you'll need
is `mem_univ g : g ∈ univ`.

-/

def top : subgp G :=
{ carrier := set.univ,
  mul_mem' := begin
    intros,
    apply mem_univ,
  end,
  one_mem' := begin
    apply mem_univ,
  end,
  inv_mem' := begin
    intros,
    apply mem_univ
  end }

-- Add the `⊤` (type with `\top`) notation for this subgroup:
instance : has_top (subgp G) := ⟨top⟩

/-
  We'll now prove the theorem that the intersection of
  two subgroups is a subgroup. This is a *definition* in Lean,
  indeed it is a construction which given two subgroups `H` and `K` of `G`
  produces a third subgroup `H ⊓ K`. This is all part of the lattice
  notation.


  The part of the interface for `∩` you'll need is that `a ∈ B ∩ C` is
  definitionally equal to `a ∈ B ∧ a ∈ C`, so you can use `split`
  if you have a goal `⊢ a ∈ B ∩ C`, and you can use `cases h` if you
  have a hypothesis `h : a ∈ B ∩ C`. Don't forget `mul_mem' H`, `one_mem' H`
  and `inv_mem' H`, the "carrier" versions of the axioms.
-/

/-- "Theorem" : intersection of two subgps is a subgp -/
def inf (H K : subgp G) : subgp G :=
{ carrier := H.carrier ∩ K.carrier,
  mul_mem' := begin
    rintros a b ⟨haH, haK⟩ ⟨hbH, hbK⟩,
    split,
    { apply H.mul_mem' haH hbH },
    { apply K.mul_mem' haK hbK }
  end,
  one_mem' := begin
    split,
    { apply one_mem' },
    { apply one_mem' }
  end,
  inv_mem' := begin
    rintros a ⟨haH, haK⟩,
    exact ⟨H.inv_mem haH, K.inv_mem haK⟩
  end }

--  Get the `⊓` symbol with `\glb`.
-- Add the `⊓` (type with `\glb`) notation for the intersection (inf) of two subgroups:
instance : has_inf (subgp G) := ⟨inf⟩

-- We now check the four axioms for a semilattice_inf_top.

lemma le_top (H : subgp G) : H ≤ ⊤ :=
begin
  intros x hx,
  apply mem_univ,
end

lemma inf_le_left (H K : subgp G) : H ⊓ K ≤ H :=
begin
  -- by definition this says `H.carrier ∩ K.carrier ⊆ H.carrier`
  change H.carrier ∩ K.carrier ⊆ H.carrier,
  -- now try `library_search`, to find that this is called `inter_subset_left
  apply inter_subset_left
end

lemma inf_le_right (H K : subgp G) : H ⊓ K ≤ K :=
inter_subset_right _ _

lemma le_inf (H J K : subgp G) (h1 : H ≤ J) (h2 : H ≤ K) : H ≤ J ⊓ K :=
begin
  exact subset_inter h1 h2,
end

instance : semilattice_inf_top (subgp G) :=
{ top := top,
  le_top := le_top,
  inf := inf,
  inf_le_left := inf_le_left,
  inf_le_right := inf_le_right,
  le_inf := le_inf,
  .. subgp.partial_order } -- don't forget to inlude the partial order

/- The logic behind `semilattice_inf_top` is that it is the simplest class
which is closed under all finite "meet"s. The meet of 0 subgroups
is `top`, the meet of one subgroup is the subgroup, the meet of two
subgroups is their inf, and for three or more you proceed by induction.

But we can do better than finite intersetions -- we can take
arbitrary intersections! Let's define the `Inf` of an arbitrary
set of subgroups of `G`.

The interface for sets you'll need to know here is that if `S` is a
set of subsets of `G`, then `⋂₀ S` is notation for their intersection, and
to work with it you'll need to know
`set.mem_sInter : g ∈ ⋂₀ S ↔ ∀ (H : set G), H ∈ S → g ∈ H`.
-/

def Inf (S : set (subgp G)) : subgp G :=
{ carrier := Inf (subgp.carrier '' S),
  mul_mem' :=  begin
    intros x y hx hy,
    rw mem_sInter at hx hy ⊢,
    rintro t ⟨H, hH, rfl⟩,
    apply H.mul_mem',
    apply hx, use H, tauto,
    apply hy, use H, tauto,
  end,
  one_mem' := begin
    rw mem_sInter,
    rintro t ⟨H, hH, rfl⟩,
    apply subgp.one_mem',
  end,
  inv_mem' := begin
    intros x hx,
    rw mem_sInter at hx ⊢,
    rintro t ⟨H, Hh, rfl⟩,
    apply H.inv_mem',
    apply hx,
    use [H, Hh],
  end }

-- We now equip `subgp G` with an Inf. I think the notation is `⨅`, or `\Inf`.
instance : has_Inf (subgp G) := ⟨Inf⟩

/- # Complete lattices

A complete lattice has arbitrary Infs and arbitrary Sups. Our next goal
is to make `subgp G` into a complete lattice. But before we do that
I need to tell you about

# Galois connections

A Galois conection is a pair of adjoint functors between two
partially ordered sets, considered as categories whose hom sets Hom(H,J) have
size 1 if H ≤ J and size 0 otherwise. In other words, a Galois
connection between two partial orders α and β is a pair of functions
`l : α → β` and `u : β → α` such that `∀ (a : α) (b : β), l a ≤ b ↔ a ≤ u b`.
There is an example coming from Galois theory (between subfields and subgroups),
and an example coming from classical algebraic geometry (between affine
varieties and ideals); note that in both cases you have to use the opposite
partial order on one side to make everything covariant.

The examples we want to keep in mind here are:
1) α = subsets of G, β = subgroups of G, l = "subgroup generated by", u = `carrier`
2)

# Galois insertions

A particularly cool kind of Galois connection is a Galois insertion, which
is a Galois connection such that `l ∘ u = id`.



-/

#check galois_connection

-- goal -- make subgps of a group into a complete lattice
/-
complete_lattice_of_Inf :
  Π (α : Type u_1) [H1 : partial_order α] [H2 : has_Inf α],
    (∀ (s : set α), is_glb s (Inf s)) → complete_lattice α
-/

instance : complete_lattice (subgp G) := complete_lattice_of_Inf _ begin
  intro S,
    apply @is_glb.of_image _ _ _ _ subgp.carrier,
  intros, refl,
  apply is_glb_Inf,
end

-- adjoint functor to carrier functor is the span functor
-- from subsets to subgps
def span (S : set G) : subgp G := Inf {H : subgp G | S ⊆ H.carrier}

lemma monotone_carrier : monotone (subgp.carrier : subgp G → set G) :=
λ H J, id

lemma monotone_span : monotone (span : set G → subgp G) :=
λ S T h, Inf_le_Inf $ λ H hH x hx, hH $ h hx

lemma subset_span (S : set G) : S ≤ (span S).carrier :=
begin
  rintro x hx _ ⟨H, hH, rfl⟩,
  exact hH hx,
end

lemma span_subgp (H : subgp G) : span H.carrier = H :=
begin
  ext,
  split,
  { intro hx,
    unfold span at hx,
    replace hx := mem_sInter.1 hx,
    apply hx,
    use H,
    simp,
    tauto! },
  { intro h,
    apply subset_span,
    exact h},
end

-- the functors are adjoint
def gi_subgp : galois_insertion span (@subgp.carrier G _) :=
galois_insertion.monotone_intro monotone_carrier monotone_span subset_span span_subgp

instance foo : complete_lattice (set G) := by apply_instance

instance bar : complete_lattice (subgp G) := galois_insertion.lift_complete_lattice gi_subgp

end subgp
