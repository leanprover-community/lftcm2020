/-
This is a sorry-free file covering the material on Wednesday afternoon
at LFTCM2020. It's how to build some algebraic structures in Lean
-/

/-
As a mathematician I essentially always start my Lean files with the following two lines:
-/
import tactic

/- That gives me access to all Lean's tactics
(see https://leanprover-community.github.io/mathlib_docs/tactics.html)
-/

open_locale classical

/- That makes Lean not complain if you use the law of the excluded middle
or the axiom of choice!

The idea of this file is to show how to build in Lean what the computer scientists call
"an algebraic heirarchy", and what mathematicians call "groups, rings, fields, modules etc"

Let's start with the theory of groups. Unfortunately Lean has groups already,
so we will have to do everything in a namespace
-/

namespace lftcm

/- ... which means that now when we define `group`, it will actually be called `lftcm.group`.

## Notation typeclasses

To make a term of type `has_mul G`, you need to give a map G^2 → G (or
more precisely, a map `has_mul.mul : G → G → G`. Lean's notation `g * h`
is notation for `has_mul.mul g h`. Furthermore, `has_mul` is a class.

In short, this means that if you write `[has_mul G]` then `G` will
magically have a multiplication called `*` (satisfying no axioms).

Similarly `[has_one G]` gives you `has_one.one : G` with notation `1 : G`,
and `[has_inv G]` gives you `has_inv.inv : G → G` with notation `g⁻¹ : G`

## Definition of a group

If `G` is a type, equipped with `* : G^2 → G`, `1 : G` and `⁻¹ : G → G`
then it's a group if it satisfies the group axioms.

-/

/-- `group G` is the type of group structures on a type `G`. -/
class group (G : Type) extends has_mul G, has_one G, has_inv G :=
(mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c))
(one_mul : ∀ (a : G), 1 * a = a)
(mul_left_inv : ∀ (a : G), a⁻¹ * a = 1)

/-

Advantages of this approach: axioms look lovely.

Disadvantage: what if I want the group law to be `+`??

Lean's solution: develop a `to_additive` attribute which translates all theorems about
`group`s (with group law `*`) to `add_group`s (with group law `+`).

-/

namespace group

-- let G be a group

variables {G : Type} [group G]

/-
Lemmas about groups are proved in this namespace. We already have some!
Indeed we just defined

`group.mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c)`
`group.one_mul : ∀ (a : G), 1 * a = a`
`group.mul_left_inv : ∀ (a : G), a⁻¹ * a = 1`

Because we are in the `group` namespace, we don't need to write `group.`
everywhere.

Let's put some more theorems into the `group` namespace.

We definitely need `mul_one` and `mul_right_inv`, and it's a fun exercise to
get them. Here is a route:

`mul_left_cancel : ∀ (a b c : G), a * b = a * c → b = c`
`mul_eq_of_eq_inv_mul {a x y : G} : x = a⁻¹ * y → a * x = y`
`mul_one (a : G) : a * 1 = a`
`mul_right_inv (a : G) : a * a⁻¹ = 1`
-/

lemma mul_left_cancel (a b c : G) (Habac : a * b = a * c) : b = c :=
 calc b = 1 * b         : by rw one_mul
    ... = (a⁻¹ * a) * b : by rw mul_left_inv
    ... = a⁻¹ * (a * b) : by rw mul_assoc
    ... = a⁻¹ * (a * c) : by rw Habac
    ... = (a⁻¹ * a) * c : by rw mul_assoc
    ... = 1 * c         : by rw mul_left_inv
    ... = c             : by rw one_mul

-- faster method
lemma mul_left_cancel' (a b c : G) (Habac : a * b = a * c) : b = c :=
begin
  rw [←one_mul b, ←mul_left_inv a, mul_assoc, Habac, ←mul_assoc, mul_left_inv, one_mul],
end

lemma mul_eq_of_eq_inv_mul {a x y : G} (h : x = a⁻¹ * y) : a * x = y :=
begin
  apply mul_left_cancel a⁻¹,
  -- ⊢ a⁻¹ * (a * x) = a⁻¹ * y
  rw ←mul_assoc,
  -- ⊢ a⁻¹ * a * x = a⁻¹ * y (remember this means (a⁻¹ * a) * x = ...)
  rw mul_left_inv,
  -- ⊢ 1 * x = a⁻¹ * y
  rw one_mul,
  -- ⊢ x = a⁻¹ * y
  exact h
end

-- The same proof
lemma mul_eq_of_eq_inv_mul' {a x y : G} (h : x = a⁻¹ * y) : a * x = y :=
mul_left_cancel a⁻¹ _ _ $ by rwa [←mul_assoc, mul_left_inv, one_mul]

/-

So now we can finally prove `mul_one` and `mul_right_inv`.

But before we start, let's learn a little bit about the simplifier.

## The `simp` tactic -- Lean's simplifier

We have the theorems (axioms) `one_mul g : 1 * g = g` and
`mul_left_inv g : g⁻¹ * g = 1`. Both of these theorems are of
the form `A = B`, with `A` more complicated than `B`. This means
that they are *perfect* theorems for the simplifier. Let's teach
those theorems to the simplifier, by adding a `@[simp]` tag to them.

-/

attribute [simp] one_mul mul_left_inv

/-

Now let's prove `mul_one` using the simplifier. This also a perfect
`simp` lemma, so let's also add the `simp` attribute to it.

-/

@[simp] theorem mul_one (a : G) : a * 1 = a :=
begin
  apply mul_eq_of_eq_inv_mul,
  -- ⊢ 1 = a⁻¹ * a
  simp,
end

/-
The simplifier solved `1 = a⁻¹ * a` because it knew `mul_left_inv`.
Feel free to comment out the `attribute [simp] one_mul mul_left_inv` line
above, and observe that the proof breaks.

-/

-- term mode proof
theorem mul_one' (a : G) : a * 1 = a :=
mul_eq_of_eq_inv_mul $ by simp

-- see if you can get the simplifier to do this one too
@[simp] theorem mul_right_inv (a : G) : a * a⁻¹ = 1 :=
begin
  apply mul_eq_of_eq_inv_mul,
  -- ⊢ a⁻¹ = a⁻¹ * 1
  simp
end

-- Now here's a question. Can we train the simplifier to solve the following problem:

--example (a b c d : G) :
--  ((a * b)⁻¹ * a * 1⁻¹⁻¹⁻¹ * b⁻¹ * b * b * 1 * 1⁻¹)⁻¹ = (c⁻¹⁻¹ * d * d⁻¹ * 1⁻¹⁻¹ * c⁻¹⁻¹⁻¹)⁻¹⁻¹ :=
--by simp

-- Remove the --'s and see that it fails. Let's see if we can get it to work.

-- We start with two very natural `simp` lemmas.

@[simp] lemma one_inv : (1 : G)⁻¹ = 1 :=
begin
  apply mul_left_cancel (1 : G),
  simp,
end

@[simp] lemma inv_inv (a : G) : a⁻¹⁻¹ = a :=
begin
  apply mul_left_cancel a⁻¹,
  simp,
end

-- Here is a riskier looking `[simp]` lemma.

attribute [simp] mul_assoc

-- The simplifier will now push all brackets to the right, which means
-- that it's worth proving the following two lemmas and tagging
-- them `[simp]`, so that we can still cancel a with a⁻¹ in these situations.

@[simp] lemma inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b :=
begin
  rw ←mul_assoc,
  simp,
end

@[simp] lemma mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b :=
begin
  rw ←mul_assoc,
  simp
end

-- Finally, let's make a `simp` lemma which enables us to
-- reduce all inverses to inverses of variables
@[simp] lemma mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  apply mul_left_cancel (a * b),
  rw mul_right_inv,
  simp,
end

/-

If you solved them all -- congratulations!
You have just turned Lean's simplifier into a normalising confluent
rewriting system for groups, following Knuth-Bendix.

https://en.wikipedia.org/wiki/Confluence_(abstract_rewriting)#Motivating_examples

In other words, the simplifier will now put any element of a free group
into a canonical normal form, and can hence solve the word problem
for free groups.

-/
example (a b c d : G) :
  ((a * b)⁻¹ * a * 1⁻¹⁻¹⁻¹ * b⁻¹ * b * b * 1 * 1⁻¹)⁻¹ = (c⁻¹⁻¹ * d * d⁻¹ * 1⁻¹⁻¹ * c⁻¹⁻¹⁻¹)⁻¹⁻¹ :=
by simp

end group



end lftcm
