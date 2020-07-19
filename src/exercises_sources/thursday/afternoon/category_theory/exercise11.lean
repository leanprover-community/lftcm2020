import algebra.category.Group.limits
import algebra.category.Group.colimits
import algebra.category.Group.preadditive
import category_theory.abelian.basic

/-!
Let's prove that the category of abelian groups is abelian!
This is currently missing in mathlib.

The only things remaining are
"every mono is the kernel of its cokernel" and "every epi is the cokernel of its kernel"
and these should be easy consequences of statements in the non-categorical group theory library.
-/

open category_theory
open category_theory.limits

instance : abelian AddCommGroup :=
{ normal_mono := λ X Y f f_mono,
  -- If you're actually going to attempt this, write `by extract_goal` here
  -- and prove this as a preliminary lemma.
  { Z := cokernel f,
    g := cokernel.π f,
    w := by tidy,
    is_limit :=
    begin
      fapply kernel_fork.is_limit.of_ι,
      -- now look in group_theory/quotient_group.lean!
      sorry,
      sorry,
      sorry,
    end, },
  normal_epi := sorry, }
