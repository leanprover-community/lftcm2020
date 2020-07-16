import algebra.category.Group.limits
import algebra.category.Group.images
import category_theory.limits.shapes.kernels
import group_theory.quotient_group
import category_theory.over

open category_theory
open category_theory.limits

universes u

section
variables {C : Type (u+1)} [large_category C] [concrete_category C]

local attribute [instance] concrete_category.has_coe_to_sort
local attribute [instance] concrete_category.has_coe_to_fun

variables [has_zero_morphisms C]

variables {X Y : C} (f : X ⟶ Y)

@[simp]
lemma kernel_condition_apply [has_kernel f] (x : kernel f) : f (kernel.ι f x) = (0 : kernel f ⟶ Y) x :=
begin
  have h := congr_arg (λ k : kernel f ⟶ Y, (k : kernel f → Y) x) (kernel.condition f),
  dsimp at h,
  rw coe_comp at h,
  exact h
end

@[simp]
lemma cokernel_condition_apply [has_cokernel f] (x : X) : cokernel.π f (f x) = (0 : X ⟶ cokernel f) x :=
begin
  have h := congr_arg (λ k : X ⟶ cokernel f, (k : X → cokernel f) x) (cokernel.condition f),
  dsimp at h,
  rw coe_comp at h,
  exact h
end

end

namespace AddCommGroup

@[simp]
lemma coe_of {G : Type*} [add_comm_group G] : (AddCommGroup.of G : Type*) = G := rfl

def of_add_subgroup_bot {G : Type*} [add_comm_group G] : AddCommGroup.of (⊥ : add_subgroup G) ≅ 0 :=
by tidy.

def of_add_subgroup_le {G : Type*} [add_comm_group G] {H K : add_subgroup G} (w : H ≤ K) :
  AddCommGroup.of H ⟶ AddCommGroup.of K :=
{ to_fun := λ h, ⟨h.1, add_subgroup.le_def.mp w h.2⟩,
  map_zero' := by tidy,
  map_add' := by tidy, }

@[simp] lemma of_add_subgroup_le_apply_val
  {G : Type*} [add_comm_group G] {H K : add_subgroup G} (w : H ≤ K) (h : H) :
  (of_add_subgroup_le w h : K).1 = h.1 := rfl

@[simps]
def of_add_subgroup_eq {G : Type*} [add_comm_group G] {H K : add_subgroup G} (w : H = K) :
  AddCommGroup.of H ≅ AddCommGroup.of K :=
{ hom := of_add_subgroup_le (le_of_eq w),
  inv := of_add_subgroup_le (le_of_eq w.symm), }


-- What is the right generality to prove this?
@[simp]
lemma zero_morphism_apply {G H : AddCommGroup} (g : G) : (0 : G ⟶ H) g = 0 := rfl

def kernel_iso_ker {G H : AddCommGroup} (f : G ⟶ H) :
  kernel f ≅ AddCommGroup.of f.ker :=
{ hom :=
  { to_fun := λ g, ⟨kernel.ι f g,
    begin
      -- FIXME where is this `has_coe_t_aux.coe` coming from? how do we get rid of it?
      change (kernel.ι f) g ∈ f.ker,
      simp [add_monoid_hom.mem_ker],
    end⟩,
    map_zero' := rfl,
    map_add' := λ g g', rfl, },
  inv := kernel.lift f (add_subgroup.subtype f.ker) (by tidy), }.

@[simp]
lemma kernel_iso_ker_hom_comp_subtype {G H : AddCommGroup} (f : G ⟶ H) :
  (kernel_iso_ker f).hom ≫ add_subgroup.subtype f.ker = kernel.ι f := rfl

@[simp]
lemma kernel_iso_ker_inv_comp_ι {G H : AddCommGroup} (f : G ⟶ H) :
  (kernel_iso_ker f).inv ≫ kernel.ι f = add_subgroup.subtype f.ker := rfl

@[simps]
def kernel_iso_ker_over {G H : AddCommGroup} (f : G ⟶ H) :
  over.mk (kernel.ι f) ≅ @over.mk _ _ G (AddCommGroup.of f.ker) (add_subgroup.subtype f.ker) :=
-- TODO this would be cleaner if we made a `over.iso_mk`.
{ hom := over.hom_mk (kernel_iso_ker f).hom (by simp),
  inv := over.hom_mk (kernel_iso_ker f).inv (by simp), }.

-- TODO why is this not always an instance?
local attribute [instance] normal_add_subgroup_of_add_comm_group

open quotient_add_group

def cokernel_iso_quotient {G H : AddCommGroup} (f : G ⟶ H) :
  cokernel f ≅ AddCommGroup.of (quotient (set.range f)) :=
{ hom := cokernel.desc f (add_monoid_hom.of mk) begin ext, apply quotient.sound, fsplit, exact -x, simp, end,
  inv := add_monoid_hom.of (quotient_add_group.lift (set.range f) (cokernel.π f) (by tidy)), }

def image_iso_range {G H : AddCommGroup} (f : G ⟶ H) :
  image f ≅ AddCommGroup.of (set.range f) :=
iso.refl _

end AddCommGroup
