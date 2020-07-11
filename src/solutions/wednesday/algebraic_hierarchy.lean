/-
This is a sorry-free file covering the material on Wednesday afternoon
at LFTCM2020. It's how to build some algebraic structures in Lean
-/

-- As a mathematician I essentially always start my Lean files with the following two lines:

import tactic -- this gives me all Lean's tactics (see https://leanprover-community.github.io/mathlib_docs/tactics.html)

open_locale classical -- otherwise Lean will complain if you use the law of the excluded middle or the axiom of choice!

-- The idea of this file is to show how to build in Lean what the computer scientists call
-- "an algebraic heirarchy", and what mathematicians call "groups, rings, fields, modules etc"

-- Let's start with the theory of groups.
-- Unfortunately Lean has groups already:

#check group

-- so we will have to do everything in a namespace

namespace lftcm

-- ... which means that now when we define `group`, it will actually be called `lftcm.group`.

-- If `G` is a type, equipped with `* : G^2 → G`, `1 : G` and `⁻¹ : G → G`
-- then it's a group if it satisfies the group axioms.

/-- `group G` is the type of group structures on a type `G`. -/
class group (G : Type) extends has_mul G, has_one G, has_inv G :=
(mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c))
(one_mul : ∀ (a : G), 1 * a = a)
(mul_left_inv : ∀ (a : G), a⁻¹ * a = 1)

-- The "extends has_mul G" trick looks like a very neat way of setting stuff up,
-- until you realise that you're going to have to set up the theory of
-- additive groups with `has_add G`, `has_zero G` and `has_neg G` separately :-(
-- Fortunately, there is a way of doing it all automatically :-)
-- We'll get to this later, when we see rings (which will extend additive groups)

namespace group

-- let G be a group

variables {G : Type} [group G]

/-
Lemmas about groups are proved in this namespace. We already have
`group.mul_assoc` and `group.one_mul` and `group.mul_left_inv`. We definitely
need `mul_one` and `mul_right_inv`, and it's a fun exercise to get them. Here
is a route:

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
  -- ⊢ a⁻¹ * a * x = a⁻¹ * y
  rw mul_left_inv,
  -- ⊢ 1 * x = a⁻¹ * y
  rw one_mul,
  -- ⊢ x = a⁻¹ * y
  exact h
end

-- The same proof
lemma mul_eq_of_eq_inv_mul' {a x y : G} (h : x = a⁻¹ * y) : a * x = y :=
mul_left_cancel a⁻¹ _ _ $ by rwa [←mul_assoc, mul_left_inv, one_mul]

end group

/-
`eq_mul_inv_of_mul_eq {a b c : G} (h : a * c = b) : a = b * c⁻¹`
`mul_left_eq_self {a b : G} : a * b = b ↔ a = 1`
`eq_inv_of_mul_eq_one {a b : G} (h : a * b = 1) : a = b⁻¹`
`inv_inv (a : G) : a ⁻¹ ⁻¹ = a`
`inv_eq_of_mul_eq_one {a b : G} (h : a * b = 1) : a⁻¹ = b`
-/
end lftcm
