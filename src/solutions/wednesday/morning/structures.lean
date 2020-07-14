import data.rat.basic
import algebra.group.prod
import tactic.basic
/-!

Lecture 1:
* Use one structure as a running example, probably `equiv` or `embedding`.
* Declaring a structure
  * name, arguments, type, fields
* Using a structure
  * Using projections (without and with the `open` command)
  * projection notation
  * `.1`, `.2`

Lecture 2:
* The `extends` keyword
* Declaring objects of a structure
  * Using the structure notation `{ field1 := _ }` and the `..` notation (and hole commands)
  * Using the anonymous constructor
  * maybe: using the constructor `foo.mk`

Lecture 3: Classes
  * Difference between structures and classes
  * How to use classes
  * When to use classes

Lecture 4: "advanced" topics
  * Proving equalities between objects of a structure
    * ext
  * Subtypes and prod (& existential & sigma types)
  * maybe: declaring coercions
  * ...
-/

noncomputable theory

section bijections

open function

variables {A B : Type*}

/- potential examples / exercises / solutions to exercises -/

structure bijection (A B : Type*) :=
  (to_fun : A → B)
  (injective : injective to_fun)
  (surjective : surjective to_fun)

/- after lecture 2, though it's mostly an exercise in searching the library
  (or proving something nontrivial) -/
instance : has_coe_to_fun (bijection A B) :=
⟨_, λ f, f.to_fun⟩

/- There is a lemma in the library that almost states this. Try using `suggest`. -/
def equiv_of_bijection (f : bijection A B) : A ≃ B :=
/- inline sorry -/ equiv.of_bijective f ⟨f.injective, f.surjective⟩ /- inline sorry -/

def bijection_of_equiv (f : A ≃ B) : bijection A B :=
-- sorry
{ to_fun := f,
  injective := f.injective,
  surjective := f.surjective }
-- sorry

/- after lecture 4 -/
@[ext] def bijection.ext {f g : bijection A B} (hfg : ∀ x, f x = g x) : f = g :=
/- inline sorry -/ by { cases f, cases g, congr, ext, exact hfg x } /- inline sorry -/

@[simp] lemma coe_mk {f : A → B} {h1f : injective f} {h2f : surjective f} {x : A} :
  { bijection . to_fun := f, injective := h1f, surjective := h2f } x = f x := rfl

def bijection_equiv_equiv : bijection A B ≃ (A ≃ B) :=
-- sorry
{ to_fun := equiv_of_bijection,
  inv_fun := bijection_of_equiv,
  left_inv := by { intro f, ext, simp [bijection_of_equiv, equiv_of_bijection] },
  right_inv := by { intro f, ext, simp [bijection_of_equiv, equiv_of_bijection] } }
-- sorry

end bijections

/- Below is a possible definition of a group in Lean. It's not the definition we use use in mathlib,
  which will explained in detail in the next session. -/

structure Group :=
  (G : Type*)
  (op : G → G → G)
  (infix * := op) -- temporary notation `*` for `op`, just inside this structure declaration
  (op_assoc' : ∀ (x y z : G), (x * y) * z = x * (y * z))
  (id : G)
  (notation 1 := id) -- temporary notation `1` for `id`, just inside this structure declaration
  (id_op' : ∀ (x : G), 1 * x = x)
  (inv : G → G)
  (postfix ⁻¹ := inv) -- temporary notation `⁻¹` for `inv`, just inside this structure declaration
  (op_left_inv' : ∀ (x : G), x⁻¹ * x = 1)

namespace Group

variables {G : Group} /- Let `G` be a group -/

/- The following line declares that if `G : Group`, then we can also view `G` as a type. -/
instance : has_coe_to_sort Group := ⟨_, Group.G⟩
/- The following lines declare the notation `*`, `⁻¹` and `1` for the fields of `Group`. -/
instance : has_mul G := ⟨G.op⟩
instance : has_inv G := ⟨G.inv⟩
instance : has_one G := ⟨G.id⟩

/- the axioms for groups are satisfied -/
lemma op_assoc (x y z : G) : (x * y) * z = x * (y * z) := G.op_assoc' x y z

lemma id_op (x : G) : 1 * x = x := G.id_op' x

lemma op_left_inv (x : G) : x⁻¹ * x = 1 := G.op_left_inv' x

/- Use the axioms `op_assoc`, `id_op` and `op_left_inv` to prove the following lemma.
  The fields `op_assoc'`, `id_op'` and `op_left_inv'` should not be used directly, nor can you use
  any lemmas from the library about `mul`. -/
lemma eq_id_of_op_eq_self {G : Group} {x : G} : x * x = x → x = 1 :=
begin
  -- sorry
  intro hx, rw [←id_op x, ← op_left_inv x, op_assoc, hx]
  -- sorry
end

/- Apply the previous lemma to show that `⁻¹` is also a right-sided inverse. -/
lemma op_right_inv {G : Group} (x : G) : x * x⁻¹ = 1 :=
begin
  -- sorry
  apply eq_id_of_op_eq_self,
  rw [op_assoc x x⁻¹ (x * x⁻¹), ← op_assoc x⁻¹ x x⁻¹, op_left_inv, id_op]
  -- sorry
end

/- we can prove that `1` is also a right identity. -/
lemma op_id {G : Group} (x : G) : x * 1 = x :=
begin
  -- sorry
  rw [← op_left_inv x, ← op_assoc, op_right_inv, id_op]
  -- sorry
end

/- show that the rationals under addition form a group. The underlying type will be `ℚ`.
  Use `library_search` for the proofs. -/
def rat_Group : Group :=
-- sorry
{ G := ℚ,
  op := (+),
  op_assoc' := add_assoc,
  id := 0,
  id_op' := zero_add,
  inv := λ x, -x,
  op_left_inv' := neg_add_self }
-- sorry

/-
  However, it is inconvenient to use this group instance directly.
  One reason is that to use these group operations we now have to write
`(x y : rat_Group)` instead of `(x y : ℚ)`.
  That's why in Lean we do something else,
explained in the next lecture.
-/

/- show that the cartesian product of two groups is a group. The underlying type will be `G × H`. -/
-- sorry
def prod_Group (G H : Group) : Group :=
{ G := G × H,
  op := λ x y, (x.1 * y.1, x.2 * y.2),
  op_assoc' := by { intros, ext; simp; rw [op_assoc] },
  id := (1, 1),
  id_op' := by { intros, ext; simp; rw [id_op] },
  inv := λ x, (x.1⁻¹, x.2⁻¹),
  op_left_inv' := by { intros, ext; simp; rw [op_left_inv] } }
-- sorry

end Group



/-- We can use classes to implement a "safe" square root on natural numbers. -/

@[class] def is_square (n : ℕ) : Prop := ∃k : ℕ, k^2 = n

namespace is_square

def sqrt (n : ℕ) [hn : is_square n] := classical.some hn

prefix `√`:(max+1) := sqrt
@[simp] lemma sqrt_square (n : ℕ) [hn : is_square n] : (√n) ^ 2 = n :=
classical.some_spec hn

@[simp] lemma sqrt_eq_iff (n k : ℕ) [hn : is_square n] : √n = k ↔ n = k^2 :=
-- sorry
⟨λ h, by simp [← h], λ hk, pow_left_inj (nat.zero_le _) (nat.zero_le k) two_pos (by simp [hk])⟩
-- sorry

instance square_square (n : ℕ) : is_square (n^2) :=
/- inline sorry -/ ⟨n, rfl⟩ /- inline sorry -/

instance square_mul_self (n : ℕ) : is_square (n*n) :=
/- inline sorry -/ ⟨n, by simp [nat.pow_two]⟩ /- inline sorry -/

instance square_mul (n m : ℕ) [is_square n] [is_square m] : is_square (n*m) :=
/- inline sorry -/ ⟨√n * √m, by simp [nat.mul_pow]⟩ /- inline sorry -/

lemma sqrt_mul (n m : ℕ) [is_square n] [is_square m] : √(n * m) = √n * √m :=
/- inline sorry -/ by simp [nat.mul_pow] /- inline sorry -/

/- hint: use `nat.le_mul_self` -/
lemma sqrt_le (n : ℕ) [is_square n] : √n ≤ n :=
/- inline sorry -/ by { conv_rhs { rw [← sqrt_square n, nat.pow_two] }, apply nat.le_mul_self } /- inline sorry -/

end is_square






structure pointed_type :=
(type : Type*)
(point : type)

namespace pointed_type
variables {A B : pointed_type}

/- The following line declares that if `A : pointed_type`, then we can also view `A` as a type. -/
instance : has_coe_to_sort pointed_type := ⟨_, pointed_type.type⟩

/- Show that the product of two pointed types is a pointed type. The underyling type will be `A × B`. -/
@[simps point]
def prod (A B : pointed_type) : pointed_type :=
-- sorry
{ type := A × B,
  point := (A.point, B.point) }
-- sorry

end pointed_type

structure pointed_map (A B : pointed_type) :=
(to_fun : A → B)
(to_fun_point : to_fun A.point = B.point)

namespace pointed_map

infix ` →. `:25 := pointed_map

variables {A B C D : pointed_type}
variables {h : C →. D} {g : B →. C} {f f₁ f₂ : A →. B}

instance : has_coe_to_fun (A →. B) := ⟨λ _, A → B, pointed_map.to_fun⟩

@[simp] lemma coe_mk {f : A → B} {hf : f A.point = B.point} {x : A} :
  { pointed_map . to_fun := f, to_fun_point := hf } x = f x := rfl
@[simp] lemma coe_point : f A.point = B.point := f.to_fun_point

@[ext] protected lemma ext (hf₁₂ : ∀ x, f₁ x = f₂ x) : f₁ = f₂ :=
begin
  -- sorry
  cases f₁ with f₁ hf₁, cases f₂ with f₂ hf₂, congr, ext x, exact hf₁₂ x
  -- sorry
end

def comp (g : B →. C) (f : A →. B) : A →. C :=
-- sorry
{ to_fun := g ∘ f,
  to_fun_point := by simp }
-- sorry

def id : A →. A :=
-- sorry
{ to_fun := id,
  to_fun_point := by simp }
-- sorry

lemma comp_assoc : h.comp (g.comp f) = (h.comp g).comp f :=
-- sorry
by { ext x, refl }
-- sorry

lemma id_comp : f.comp id = f :=
-- sorry
by { ext x, refl }
-- sorry

lemma comp_id : id.comp f = f :=
-- sorry
by { ext x, refl }
-- sorry

def fst : A.prod B →. A :=
-- sorry
{ to_fun := prod.fst,
  to_fun_point := rfl }
-- sorry

def snd : A.prod B →. B :=
-- sorry
{ to_fun := prod.snd,
  to_fun_point := rfl }
-- sorry

def pair (f : C →. A) (g : C →. B) : C →. A.prod B :=
-- sorry
{ to_fun := λ c, (f c, g c),
  to_fun_point := by simp }
-- sorry

lemma fst_pair (f : C →. A) (g : C →. B) : fst.comp (f.pair g) = f :=
-- sorry
by { ext, simp [pair, fst, comp] }
-- sorry

lemma snd_pair (f : C →. A) (g : C →. B) : snd.comp (f.pair g) = g :=
-- sorry
by { ext, simp [pair, snd, comp] }
-- sorry

lemma pair_unique (f : C →. A) (g : C →. B) (u : C →. A.prod B) (h1u : fst.comp u = f)
  (h2u : snd.comp u = g) : u = f.pair g :=
begin
  -- sorry
  ext,
  { have : fst (u x) = f x, { rw [←h1u], simp [comp] }, simpa using this },
  { have : snd (u x) = g x, { rw [←h2u], simp [comp] }, simpa using this }
  -- sorry
end


end pointed_map

/- As an advanced exercise, you can show that the category of pointed type has coproducts.
  For this we need quotients, the basic interface is given with the declarations
  `quot r`: the quotient of the equivalence relation generated by relation `r` on `A`
  `quot.mk r : A → quot r`,
  `quot.sound`
  `quot.lift` (see below)
  -/

#print quot
#print quot.mk
#print quot.sound
#print quot.lift

open sum

/- We want to define the coproduct of pointed types `A` and `B` as the coproduct `A ⊕ B` of the
  underlying type, identifying the two basepoints.

  First define a relation that *only* relates `inl A.point ~ inr B.point`.
-/
def coprod_rel (A B : pointed_type) : (A ⊕ B) → (A ⊕ B) → Prop :=
-- sorry
λ x y, x = inl A.point ∧ y = inr B.point
-- sorry

namespace pointed_type

@[simps point]
def coprod (A B : pointed_type) : pointed_type :=
-- sorry
{ type := quot (coprod_rel A B),
  point := quot.mk _ (inl A.point) }
-- sorry
end pointed_type

namespace pointed_map

variables {A B C D : pointed_type}

def inl : A →. A.coprod B :=
-- sorry
{ to_fun := quot.mk _ ∘ sum.inl,
  to_fun_point := rfl }
-- sorry

def inr : B →. A.coprod B :=
-- sorry
{ to_fun := quot.mk _ ∘ sum.inr,
  to_fun_point := by { refine (quot.sound _).symm, exact ⟨rfl, rfl⟩ } }
-- sorry

def elim (f : A →. C) (g : B →. C) : A.coprod B →. C :=
-- sorry
{ to_fun := quot.lift (sum.elim f g) (by { rintro _ _ ⟨rfl, rfl⟩, simp }),
  to_fun_point := by simp }
-- sorry

lemma elim_comp_inl (f : A →. C) (g : B →. C) : (f.elim g).comp inl = f :=
-- sorry
by { ext, simp [elim, inl, comp] }
-- sorry

lemma elim_comp_inr (f : A →. C) (g : B →. C) : (f.elim g).comp inr = g :=
-- sorry
by { ext, simp [elim, inr, comp] }
-- sorry

lemma elim_unique (f : A →. C) (g : B →. C) (u : A.coprod B →. C) (h1u : u.comp inl = f)
  (h2u : u.comp inr = g) : u = f.elim g :=
begin
  -- sorry
  ext (x|y),
  { have : u (inl x) = f x, { rw [←h1u], simp [comp] }, simpa [elim, inl] using this },
  { have : u (inr y) = g y, { rw [←h2u], simp [comp] }, simpa [elim, inl] using this }
  -- sorry
end

end pointed_map
