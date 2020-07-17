import for_mathlib.category_theory -- This imports some simp lemmas that I realised belong in mathlib while writing this exercise.

open category_theory

variables {C : Type*} [category C]
variables {D : Type*} [category D]

lemma equiv_reflects_mono {X Y : C} (f : X ⟶ Y) (e : C ≌ D)
  (hef : mono (e.functor.map f)) : mono f :=
-- Hint: when `e : C ≌ D`, `e.functor.map_injective` says
--   `∀ f g, e.functor.map f = e.functor.map g → f = g`
-- Hint: use `cancel_mono`.
{ right_cancellation :=
  begin
    intros,
    apply e.functor.map_injective,
    rw ← cancel_mono (e.functor.map f),
    apply e.inverse.map_injective,
    simpa,
  end }

lemma equiv_preserves_mono {X Y : C} (f : X ⟶ Y) [mono f] (e : C ≌ D) :
  mono (e.functor.map f) :=
-- Hint: if `w : f = g`, to obtain `F.map f = F.map G`,
--   you can use `have w' := congr_arg (λ k, F.map k) w`.
{ right_cancellation :=
  begin
    intros,
    have := congr_arg (λ k, e.inverse.map k) w,
    simp at this,
    rw [← category.assoc, ← category.assoc, cancel_mono f] at this,
    replace := congr_arg (λ k, e.functor.map k) this,
    simpa,
  end }

/-!
There are some further hints in
`src/hints/thursday/afternoon/category_theory/exercise3/`
-/


lemma bar (a b : ℕ) (h : a.succ = b.succ) : a = b :=
  @eq.dcases_on _ (nat.succ a)
    (λ (t_1 : nat) (h_1 : (nat.succ a) = t_1),
       (nat.succ b) = t_1 → h == h_1 → a = b)
    (nat.succ b)
    h
    (λ (H_1 : (nat.succ b) = (nat.succ a)),
       @nat.no_confusion.{0}
         (h == (eq.refl (nat.succ a)) → a = b)
         (nat.succ b)
         (nat.succ a)
         H_1
         (λ (n_eq : b = a),
            @eq.rec.{0 1} nat a
              (λ (b : nat),
                 ∀ (h : (nat.succ a) = (nat.succ b)),
                   h == (eq.refl (nat.succ a)) →
                   a = b)
              (λ (h : (nat.succ a) = (nat.succ a))
               (H_2 : h == (eq.refl (nat.succ a))), eq.refl a)
              b
              (n_eq.symm)
              h))
    (eq.refl (nat.succ b))
    (heq.refl h)


lemma foo (a b : ℕ) (h : a.succ = b.succ) : a = b :=
begin
  cases h, refl
end

#print eq.dcases_on

set_option pp.all true

#print foo
