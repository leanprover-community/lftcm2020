import data.rat.basic
import algebra.group.prod
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

open function

variables {α β : Type*}

#print embedding
#print equiv

/- potential examples / exercises / solutions to exercises -/

structure bijection (α β : Type*) extends embedding α β :=
  (surjective : surjective to_fun)

instance : has_coe_to_fun (bijection α β) :=
⟨_, λ f, f.to_fun⟩

/- after lecture 2, though it's mostly an exercise in searching the library (or proving something nontrivial) -/

def equiv_of_bijection (f : bijection α β) : α ≃ β :=
equiv.of_bijective f ⟨f.inj', f.surjective⟩

def bijection_of_equiv (f : α ≃ β) : bijection α β :=
{ to_fun := f,
  inj' := f.injective,
  surjective := f.surjective }

/- after lecture 4 -/
def bijection_equiv_equiv : bijection α β ≃ (α ≃ β) :=
sorry


structure Group :=
  (G : Type*)
  (op : G → G → G)
  (infix * := op) -- temporary notation for `op`, just inside this structure declaration
  (op_assoc' : ∀ (x y z : G), (x * y) * z = x * (y * z))
  (id : G)
  (notation 1 := id) -- temporary notation for `1`, just inside this structure declaration
  (id_op' : ∀ (x : G), 1 * x = x)
  (inv : G → G)
  (postfix ⁻¹ := inv) -- temporary notation for `inv`, just inside this structure declaration
  (op_left_inv' : ∀ (x : G), x⁻¹ * x = 1)


/- exercise after lesson 2 -/
namespace Group

variables {G : Group}

/- declaring that if `G : Group`, then we can view `G` as a type. -/
instance : has_coe_to_sort Group := ⟨_, Group.G⟩
/- declaring notation `*`, `⁻¹` and `1` for `G : Group`. -/
instance : has_mul G := ⟨G.op⟩
instance : has_inv G := ⟨G.inv⟩
instance : has_one G := ⟨G.id⟩

/- the axioms for groups are satisfied -/
lemma op_assoc (x y z : G) : (x * y) * z = x * (y * z) := G.op_assoc' x y z

lemma id_op (x : G) : 1 * x = x := G.id_op' x

lemma op_left_inv (x : G) : x⁻¹ * x = 1 := G.op_left_inv' x

/- Use these axioms to prove this useful lemma. -/
lemma eq_id_of_op_eq_self {G : Group} {x : G} : x * x = x → x = 1 :=
by { intro hx, rw [←id_op x, ← op_left_inv x, op_assoc, hx] }

/- Apply the previous lemma to show that `⁻¹` is also a right-sided inverse. -/
lemma op_right_inv {G : Group} (x : G) : x * x⁻¹ = 1 :=
by { apply eq_id_of_op_eq_self,
     rw [op_assoc x x⁻¹ (x * x⁻¹), ← op_assoc x⁻¹ x x⁻¹, op_left_inv, id_op] }

/- we can prove that `1` is also a right identity. -/
lemma op_id {G : Group} (x : G) : x * 1 = x :=
by { rw [← op_left_inv x, ← op_assoc, op_right_inv, id_op] }

/- after lecture 2 -/
/- show that the rationals under addition form a group. The underlying type will be `ℚ`. -/
def rat_Group : Group :=
{ G := ℚ,
  op := (+),
  op_assoc' := add_assoc,
  id := 0,
  id_op' := zero_add,
  inv := λ x, -x,
  op_left_inv' := neg_add_self }

/- However, one disadvantage is that to use these group operations we now have to write
`(x y : rat_Group)` instead of `(x y : ℚ)`. That's why in Lean we do something else,
explained in the next lecture. -/

/- after lecture 4 -/
/- show that the cartesian product of two groups is a group. The underlying type will be `G × H`. -/
def prod_Group2 (G H : Group) : Group :=
{ G := G × H,
  op := λ x y, (x.1 * y.1, x.2 * y.2),
  op_assoc' := by { intros, ext; simp; rw [op_assoc] },
  id := (1, 1),
  id_op' := by { intros, ext; simp; rw [id_op] },
  inv := λ x, (x.1⁻¹, x.2⁻¹),
  op_left_inv' := by { intros, ext; simp; rw [op_left_inv] } }

-- solution 2: use operations from the library (cannot use `mul_assoc` etc. from the library, since we have not declared the appropriate instances)
def prod_Group (G H : Group) : Group :=
{ G := G × H,
  op := (*),
  op_assoc' := by { intros, ext; simp; rw [op_assoc] },
  id := 1,
  id_op' := by { intros, ext; simp; rw [id_op] },
  inv := λ x, x⁻¹,
  op_left_inv' := by { intros, ext; simp; rw [op_left_inv] } }


end Group
