import category_theory.limits.shapes.biproducts

/-!
Let's show that every preadditive category embeds into a preadditive category with biproducts,
and identify a good universal property.

This is a more advanced exercise, for which I've indicated a suggested structure,
but not written a full solution. I hope this structure will work out!
-/

noncomputable theory

universes v u

variables (C : Type u)

structure additive_envelope :=
(ι : Type)
[fintype : fintype ι]
[decidable_eq : decidable_eq ι]
(val : ι → C)

attribute [instance] additive_envelope.fintype additive_envelope.decidable_eq

variables {C}

def dmatrix {X Y : additive_envelope C} (Z : X.ι → Y.ι → Type*) := Π (i : X.ι) (j : Y.ι), Z i j
-- You may need to develop some API for `dmatrix`, parallel to that in `data.matrix.basic`.
-- One thing you'll certainly need is an "extensionality" lemma,
-- showing that you can prove two `dmatrix`s are equal by checking componentwise.

open category_theory

variables [category C] [preadditive C]

namespace family

def hom (X Y : additive_envelope C) := dmatrix (λ i j, X.val i ⟶ Y.val j)

open_locale big_operators

instance : category (additive_envelope C) :=
{ hom := hom,
  id := λ X i j, if h : i = j then eq_to_hom (by subst h) else 0,
  comp := λ X Y Z f g i k, ∑ (j : Y.ι), f i j ≫ g j k,
  id_comp' := sorry,
  comp_id' := sorry,
  assoc' := sorry, }

variables (C)

@[simps]
def embedding : C ⥤ additive_envelope C :=
{ obj := λ X, ⟨unit, λ _, X⟩,
  map := λ X Y f _ _, f,
  map_id' := sorry,
  map_comp' := sorry, }

lemma embedding.faithful : faithful (embedding C) :=
sorry

instance : preadditive (additive_envelope C) :=
sorry -- probably best to go back and make `dmatrix` an `add_comm_group` first.

open category_theory.limits

instance : has_finite_biproducts (additive_envelope C) :=
{ has_biproducts_of_shape := λ J _,
  by { classical, exactI -- this makes the `fintype` instance on `J` available as well as decidable equality
  { has_biproduct := λ F, has_biproduct.mk
    { bicone :=
      { X :=
        { ι := Σ (j : J), (F j).ι,
          val := λ p, (F p.1).val p.2 },
        ι := sorry,
        π := sorry,
        ι_π := sorry, },
      is_bilimit := sorry }}} }

variables {C}

def factor {D : Type u} [category.{v} D] [preadditive D] [has_finite_biproducts D]
  (F : C ⥤ D) : additive_envelope C ⥤ D :=
{ obj := λ X, ⨁ (λ i, F.obj (X.val i)),
  map := sorry,
  map_id' := sorry,
  map_comp' := sorry, }

def factor_factorisation {D : Type u} [category D] [preadditive D] [has_finite_biproducts D]
  (F : C ⥤ D) : F ≅ embedding C ⋙ factor F :=
sorry

end family

