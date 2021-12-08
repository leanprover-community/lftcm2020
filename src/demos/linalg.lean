import algebra.module
import analysis.inner_product_space.basic
import data.matrix.notation
import data.matrix.dmatrix
import linear_algebra.basic
import linear_algebra.bilinear_form
import linear_algebra.quadratic_form.basic
import linear_algebra.finsupp
import tactic
import linear_algebra.matrix.nonsingular_inverse

/-
According to Wikipedia, everyone's favourite reliable source of knowledge,
linear algebra studies linear equations and linear maps, representing them
in vector spaces and through matrices.

Vector spaces are special cases of modules where scalars live any semiring,
not necessarily a field.
-/

#print module
-- class module (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M]
-- extends distrib_mul_action R M := ...

/-
In other words: let `R` be a semiring and `M` have `0` and a commutative operator `+`,
then a module structure over `R` on `M` has a scalar multiplication `•` (`has_scalar.smul`),
which satisfies the following identities:
-/
#check add_smul -- ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x
#check smul_add -- ∀ (r : R) (x y : M), r • (x + y) = r • x + r • y
#check mul_smul -- ∀ (r s : R) (x : M), (r * s) • x = r • (s • x)
#check one_smul -- ∀ (x : M), 1 • x = x
#check zero_smul -- ∀ (x : M), 0 • x = 0
#check smul_zero -- ∀ (r : R), r • 0 = 0
/-
These equations define modules (and vector spaces).
-/

/-
The last two identities follow automatically from the previous if `M` has a negation operator,
turning it into an additive group, so the function `module.of_core` does the proofs for you:
-/
#check module.of_core

section module

/-
Typical examples of modules (and vector spaces):
-/
-- import algebra.pi_instances
variables {n : Type} [fintype n]
example : module ℕ (n → ℕ) := infer_instance -- Or as mathematicians commonly know it: `ℕ^n`.
example : module ℤ (n → ℤ) := infer_instance
example : module ℚ (n → ℚ) := infer_instance


/- If you want a specifically `k`-dimensional module, use `fin k` as the `fintype`. -/
example {k : ℕ} : module ℤ (fin k → ℤ) := infer_instance

variables {R M N : Type} [ring R] [add_comm_group M] [add_comm_group N] [module R M] [module R N]
example : module R R := infer_instance
example : module ℤ R := infer_instance
example : module R (M × N) := infer_instance
example : module R (M × N) := infer_instance

example {R' : Type} [comm_ring R'] (f : R →+* R') : module R R' := ring_hom.to_module f

/- To explicitly construct elements of `fin k → R`, use the following notation: -/
-- import data.matrix.notation
example : fin 4 → ℤ := ![1, 2, -4, 3]

end module

section linear_map

variables {R M : Type} [comm_ring R] [add_comm_group M] [module R M]

/-
Maps between modules that respect `+` and `•` are called `linear_map`,
and an `R`-linear map from `M` to `N` has notation `M →ₗ[R] N`:
-/
#print linear_map

/- They are bundled, meaning we define them by giving the map and the proofs simultaneously: -/
def twice : M →ₗ[R] M :=
{ to_fun := λ x, (2 : R) • x,
  map_add' := λ x y, smul_add 2 x y,
  map_smul' := λ s x, smul_comm 2 s x }

/- Linear maps can be applied as if they were functions: -/
#check twice (![37, 42] : fin 2 → ℚ)

/- Some basic operations on linear maps: -/
-- import linear_algebra.basic
#check linear_map.comp -- composition
#check linear_map.has_zero -- 0
#check linear_map.has_add -- (+)
#check linear_map.has_scalar -- (•)

/-
A linear equivalence is an invertible linear map.
These are the correct notion of "isomorphism of modules".
-/
#print linear_equiv
/- The identity function is defined twice: once as linear map and once as linear equivalence. -/
#check linear_map.id
#check linear_equiv.refl

end linear_map

section submodule

variables {R M : Type} [comm_ring R] [add_comm_group M] [module R M]

/-
The submodules of a module `M` are subsets of `M` (i.e. elements of `set M`)
that are closed under the module operations `0`, `+` and `•`.
`subspace` is defined to be a special case of `submodule`.
-/
#print submodule
#print subspace

/-
Note that the `ideal`s of a ring `R` are defined to be exactly the `R`-submodules of `R`.
This should save us a lot of re-definition work.
-/
#print ideal

/-
You can directly define a submodule by giving its carrier subset and proving that
the carrier is closed under each operation:
-/
def zero_submodule : submodule R M :=
{ carrier := {0},
  zero_mem' := by simp,
  add_mem' := by { intros x y hx hy, simp at hx hy, simp [hx, hy] },
  smul_mem' := by { intros r x hx, simp at hx, simp [hx] } }

/- There are many library functions for defining submodules: -/
variables (S T : submodule R M)
#check (twice.range : submodule R M) -- the image of `twice` in `M`
#check (twice.ker : submodule R M) -- the kernel of `twice` in `M`
#check submodule.span ℤ {(2 : ℤ)} -- also known as 2ℤ
#check S.map twice -- also known as {twice x | x ∈ S}
#check S.comap twice -- also known as {x | twice x ∈ S}

/- For submodule inclusion, we write `≤`: -/
#check S ≤ T
#check S < T
/- The zero submodule is written `⊥` and the whole module as a submodule is written `⊤`: -/
example {x : M} : x ∈ (⊥ : submodule R M) ↔ x = 0 := submodule.mem_bot R
example {x : M} : x ∈ (⊤ : submodule R M) := submodule.mem_top
/- Intersection and sum of submodules are usually written with the lattice operators `⊓` and `⊔`: -/
#check submodule.mem_inf -- x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T
#check submodule.mem_sup -- x ∈ S ⊔ T ↔ ∃ (y ∈ S) (z ∈ T), x = y + z

/- The embedding of a submodule in the ambient space, is called `subtype`: -/
#check submodule.subtype

/- Finally, we can take the quotient modulo a submodule.
Note the nonstandard ⧸, typed with \quot .
 -/

#check ℤ ⧸ submodule.span ℤ {(2 : ℤ)}

end submodule

section forms

variables {n R : Type} [comm_ring R] [fintype n]

/- In addition to linear maps, there are bilinear forms, quadratic forms and sesquilinear forms. -/
-- import linear_algebra.bilinear_form
-- import linear_algebra.quadratic_form
#check bilin_form

/- Defining a bilinear form works similarly to defining a linear map: -/
def dot_product : bilin_form R (n → R) :=
{ bilin := λ x y, matrix.dot_product x y,
  bilin_add_left := matrix.add_dot_product,
  bilin_smul_left := matrix.smul_dot_product,
  bilin_add_right := matrix.dot_product_add,
  bilin_smul_right := matrix.dot_product_smul }

/- Some other constructions on forms: -/
#check bilin_form.to_quadratic_form
#check quadratic_form.associated
#check quadratic_form.has_scalar
#check quadratic_form.proj

end forms

section matrix

variables {m n R : Type} [fintype m] [fintype n] [comm_ring R]

/-
Matrices in mathlib are basically no more than a rectangular block of entries.
Under the hood, they are specified by a function taking a row and column,
and returning the entry at that index.
They are useful when you want to compute an invariant such as the determinant,
as these are typically noncomputable for linear maps.

A type of matrices `matrix m n α` requires that the types `m` and `n` of the indices
are `fintype`s, and there is no restriction on the type `α` of the entries.
-/
#print matrix

/-
Like vectors in `n → R`, matrices are typically indexed over `fin k`.
To define a matrix, you map the indexes to the entry:
-/
def example_matrix : matrix (fin 2) (fin 3) ℤ := λ i j, i + j
#eval example_matrix 1 2

/- Like vectors, we can use `![...]` notation to define matrices: -/
def other_example_matrix : matrix (fin 3) (fin 2) ℤ :=
![![0, 1],
  ![1, 2],
  ![2, 3]]

/- We have the 0 matrix and the sum of two matrices: -/
example (i j) : (0 : matrix m n R) i j = 0 := dmatrix.zero_apply i j
example (A B : matrix m n R) (i j) : (A + B) i j = A i j + B i j := dmatrix.add_apply A B i j

/-
Matrices have multiplication and transpose operators `matrix.mul` and `matrix.transpose`.
The following line allows `⬝` and `ᵀ` to stand for these two respectively:
-/
open_locale matrix

#check example_matrix ⬝ other_example_matrix
#check example_matrixᵀ

/- On square matrices, we have a semiring structure with `(*) = (⬝)` and `1` as the identity matrix. -/
#check matrix.semiring

/-
When working with matrices, a "vector" is always of the form `n → R`
where `n` is a `fintype`. The operations between matrices and vectors are defined.
-/
#check matrix.col -- turn a vector into a column matrix
#check matrix.row -- turn a vector into a row matrix
#check matrix.vec_mul_vec -- column vector times row vector

/-
You have to explicitly specify whether vectors are multiplied on the left or on the right:
-/
#check example_matrix.mul_vec -- (fin 3 → ℤ) → (fin 2 → ℤ), right multiplication
#check example_matrix.vec_mul -- (fin 2 → ℤ) → (fin 3 → ℤ), left multiplication

/- You can convert a matrix to a linear map, which acts by right multiplication of vectors. -/
variables {M N : Type} [add_comm_group M] [add_comm_group N] [module R M] [module R N]
#check matrix.to_lin' -- matrix m n R → ((n → R) →ₗ[R] (m → R))

/-
Going between linear maps and matrices is an isomorphism,
as long as you have chosen a basis for each module.
-/
variables [decidable_eq m] [decidable_eq n]
variables (v : basis m R M) (w : basis n R N)
#check linear_map.to_matrix v w -- (M →ₗ[R] N) ≈ₗ[R] matrix n m R

/-
Invertible (i.e. nonsingular) matrices have an inverse operation denoted by `⁻¹`.
-/
#check matrix.inv_def

end matrix

section odds_and_ends

/- Other useful parts of the library: -/
-- import analysis.inner_product_space.basic
#print normed_space -- module with a norm
#print inner_product_space -- normed space with an inner product in ℝ or ℂ

#print finite_dimensional.finrank -- the rank (or dimension) of a space, as a natural number (infinity -> 0)
#print module.rank -- the rank (or dimension) of a module (or vector space), as a cardinal

end odds_and_ends
