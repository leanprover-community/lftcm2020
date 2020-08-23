import algebra.category.Group.basic

open category_theory

universes u

namespace AddCommGroup

@[simp]
lemma zero_morphism_apply {G H : AddCommGroup} (g : G) : (0 : G ⟶ H) g = 0 := rfl

/-- The bundled group corresponding to `⊥ : add_subgroup G` is isomorphic to `0`. -/
@[simps]
def of_add_subgroup_bot {G : Type*} [add_comm_group G] : AddCommGroup.of (⊥ : add_subgroup G) ≅ 0 :=
{ hom := 0, inv := 0, }

end AddCommGroup

namespace CommGroup

@[simp, to_additive]
lemma coe_of {G : Type*} [comm_group G] : (CommGroup.of G : Type*) = G := rfl

/-- The bundled group corresponding to `⊤ : subgroup G` is isomorphic to `G`. -/
@[to_additive "The bundled group corresponding to `⊤ : add_subgroup G` is isomorphic to `G`."]
def of_subgroup_top {G : Type*} [comm_group G] :
  CommGroup.of (⊤ : subgroup G) ≅ CommGroup.of G :=
{ hom := subgroup.subtype ⊤,
  inv := { to_fun := λ g, ⟨g, by trivial⟩, map_one' := by tidy, map_mul' := by tidy, }, }

/-- An inclusion of subgroups gives a morphism of bundled groups. -/
@[to_additive]
def of_subgroup_le {G : Type*} [comm_group G] {H K : subgroup G} (w : H ≤ K) :
  CommGroup.of H ⟶ CommGroup.of K :=
{ to_fun := λ h, ⟨h.1, subgroup.le_def.mp w h.2⟩,
  map_one' := by tidy,
  map_mul' := by tidy, }

@[simp, to_additive] lemma of_subgroup_le_apply_val
  {G : Type*} [comm_group G] {H K : subgroup G} (w : H ≤ K) (h : H) :
  (of_subgroup_le w h : K).1 = h.1 := rfl

/-- An equality of subgroups gives an isomorphism of bundled groups. -/
@[simps, to_additive]
def of_subgroup_eq {G : Type*} [comm_group G] {H K : subgroup G} (w : H = K) :
  CommGroup.of H ≅ CommGroup.of K :=
{ hom := of_subgroup_le (le_of_eq w),
  inv := of_subgroup_le (le_of_eq w.symm), }

attribute [simps] AddCommGroup.of_add_subgroup_eq

end CommGroup
