module
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupTheory.Commutator.CentralExtensionPairing
public import Theory.GroupAction.AutomorphismFixedSubgroup

/-!
# Central quotient actors fix the derived group

An automorphism inducing the identity modulo the center changes each element
by a central factor. Commutators therefore remain unchanged, and the whole
derived group is fixed pointwise. This is the central-extension calculation
used for the original torus action in Aschbacher–Smith 2.4.24(2).
-/

public section
open Subgroup
open scoped commutatorElement
namespace MulAut
variable {G : Type*} [Group G]
theorem fixes_commutator_of_quotientCenter_eq_one (a : MulAut G)
    (ha : quotientAut (center G) a=1) : commutator G≤a.fixedSubgroup := by
  have hq (x:G) : QuotientGroup.mk' (center G) (a x)=QuotientGroup.mk' (center G) x := by
    rw [←quotientAut_apply_mk,ha]
    rfl
  change ⁅(⊤:Subgroup G),⊤⁆≤_
  apply commutator_le.mpr
  intro x _ y _
  rw [MulAut.mem_fixedSubgroup]
  rw [map_commutatorElement]
  exact CentralExtension.commutator_eq_of_image_eq (QuotientGroup.mk' (center G))
    (by rw [QuotientGroup.ker_mk']) (hq x) (hq y)
end MulAut
