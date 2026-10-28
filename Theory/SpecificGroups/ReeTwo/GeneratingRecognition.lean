module

public import Theory.SpecificGroups.ReeTwo.Recognition

/-!
# Whole Ree local recognition from generating roots

The ten core roots, the root-one actor and the Weyl actor satisfy the
verified core and complement relations. Evaluation gives a homomorphism
from the semidirect-product model. The surviving last root makes it
injective, and generation makes it surjective, without an order hypothesis.

Source: Shinoda (1975), (2.3) and (3.2), pp.81–83, with the corrected
root relation documented in `Centralizer`.
-/

public noncomputable section
namespace ReeTwo.Centralizer
open Subgroup

/-- Concrete root relations and generation, with a nontrivial central root. -/
structure Generators (H : Type*) [Group H] where
  root : CoreRoot → H
  rootOne : H
  weyl : H
  core : CoreRelations root
  root_one : RootOneRelations rootOne root
  weyl_root : ∀ i, weyl * root i * weyl⁻¹ = root (weylRoot i)
  five : ((rootOne⁻¹) ^ 2 * weyl) ^ 5 = 1
  four : (rootOne⁻¹) ^ 4 = 1
  action : rootOne⁻¹ * ((rootOne⁻¹) ^ 2 * weyl) * (rootOne⁻¹)⁻¹ =
    ((rootOne⁻¹) ^ 2 * weyl) ^ 2
  last_ne_one : root 9 ≠ 1
  generates : closure (Set.range root ∪ {rootOne, weyl}) = ⊤

namespace Generators
variable {H : Type*} [Group H] (d : Generators H)

/-- Evaluation on the specified roots and actors. -/
def hom : Centralizer →* H :=
  lift d.core d.root_one d.weyl_root d.five d.four d.action

@[simp] theorem hom_root (i : CoreRoot) : d.hom (Centralizer.root i) = d.root i :=
  lift_root d.core d.root_one d.weyl_root d.five d.four d.action i

@[simp] theorem hom_rootOne : d.hom Centralizer.rootOne = d.rootOne :=
  lift_rootOne d.core d.root_one d.weyl_root d.five d.four d.action

@[simp] theorem hom_weyl : d.hom Centralizer.weyl = d.weyl :=
  lift_weyl d.core d.root_one d.weyl_root d.five d.four d.action

/-- A nontrivial last root detects every possible kernel. -/
theorem hom_injective : Function.Injective d.hom :=
  lift_injective d.core d.root_one d.weyl_root d.five d.four d.action d.last_ne_one

/-- Every target element is in the image because the specified roots generate. -/
theorem hom_surjective : Function.Surjective d.hom := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← d.generates]
  apply (closure_le _).mpr
  rintro x (⟨i, rfl⟩ | hx)
  · exact ⟨Centralizer.root i, d.hom_root i⟩
  · rcases hx with rfl | rfl
    · exact ⟨Centralizer.rootOne, d.hom_rootOne⟩
    · exact ⟨Centralizer.weyl, d.hom_weyl⟩

/-- The relation-defined map identifies the whole group. -/
def equiv : Centralizer ≃* H := MulEquiv.ofBijective d.hom
  ⟨d.hom_injective, d.hom_surjective⟩

@[simp] theorem equiv_root (i : CoreRoot) : d.equiv (Centralizer.root i) = d.root i :=
  d.hom_root i

end Generators
end ReeTwo.Centralizer
