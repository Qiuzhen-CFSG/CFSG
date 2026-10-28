module
public import Theory.SpecificGroups.SymmetricFourResidualCore
public import Theory.SpecificGroups.SymmetricFour.ResidualFactorization
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Normal four-groups and residuals in a symmetric-four carrier

A normal elementary four in S₄ has the order of its two-core, hence is that
core and is self-centralizing. The two-residual is the actual alternating
subgroup A₄. These facts transport through any multiplicative equivalence.
Source application: Aschbacher--Smith 2.5.12(2), printed pp.557--558.
-/

public section
namespace Theory.GroupTheory
open Subgroup
open Theory.SpecificGroups.SymmetricSix.DuadCalculation
variable {G : Type*} [Group G]

theorem normal_four_eq_twoCore_of_equiv
    (e : G ≃* Equiv.Perm (Fin 4)) (F : Subgroup G) [F.Normal] [IsKleinFour F] :
    F = pCore 2 G := by
  let : Finite G := Finite.of_injective e e.injective
  have hF : F ≤ pCore 2 G := le_sSup ⟨inferInstance,
    IsPGroup.of_card (p := 2) (n := 2) IsKleinFour.card_four⟩
  apply eq_of_le_of_card_ge hF
  have hc : Nat.card (pCore 2 G) = 4 := by
    rw [← core_card, core_eq, ← pCore_map_iso 2 e,
      card_map_of_injective e.injective]
  rw [hc, IsKleinFour.card_four]

theorem normal_four_selfCentralizing_of_equiv
    (e : G ≃* Equiv.Perm (Fin 4)) (F : Subgroup G) [F.Normal] [IsKleinFour F] :
    centralizer (F : Set G) = F := by
  have hmap : F.map e.toMonoidHom = core := by
    rw [normal_four_eq_twoCore_of_equiv e F, pCore_map_iso, ← core_eq]
  apply le_antisymm
  · intro x hx
    have he : e x ∈ centralizer (core : Set (Equiv.Perm (Fin 4))) := by
      rw [← hmap]
      rintro _ ⟨y,hy,rfl⟩
      simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg e (hx y hy)
    rw [centralizer_core, ← hmap] at he
    simpa only [e.symm_apply_apply] using mem_map_equiv.mp he
  · let : IsMulCommutative F := IsKleinFour.isMulCommutative
    exact le_centralizer_iff_isMulCommutative.mpr inferInstance

theorem twoResidual_equiv_alternatingFour_of_equiv
    (e : G ≃* Equiv.Perm (Fin 4)) :
    Nonempty (pResidual 2 G ≃* alternatingGroup (Fin 4)) := by
  refine ⟨(e.subgroupMap (pResidual 2 G)).trans (MulEquiv.subgroupCongr ?_)⟩
  change (pResidual 2 G).map e.toMonoidHom = _
  rw [map_pResidual, Theory.SpecificGroups.SymmetricFourResidual.residual_eq]

end Theory.GroupTheory
