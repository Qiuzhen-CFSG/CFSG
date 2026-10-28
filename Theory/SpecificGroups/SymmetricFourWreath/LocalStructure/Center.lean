module
public import Theory.SpecificGroups.SymmetricFourWreath.Core.Placement
public import Theory.SpecificGroups.SymmetricFourWreath.LocalStructure.Coordinates

/-!
# The central involution of the marked Sylow

Commutation with the rotation and reflection in the first factor and the
swap already forces a wreath element to be identity or the diagonal central
involution. Transport through the literal Sylow embedding identifies the
center with the existing marked cyclic subgroup ⟨z⟩.

Source: Aschbacher–Smith 13.9.2 setup and (6), printed p.969 (PDF p.986).
-/

public section
namespace SymmetricFourWreath
open Subgroup
private instance : DecidableEq P := (RegularWreathProduct.equivProd D8 C2).injective.decidableEq
private instance : Fintype P := Fintype.ofEquiv _ (RegularWreathProduct.equivProd D8 C2).symm

private theorem center_tests : ∀x:P,
    x*pair (DihedralGroup.r 1,1)=pair (DihedralGroup.r 1,1)*x →
    x*pair (DihedralGroup.sr 0,1)=pair (DihedralGroup.sr 0,1)*x →
    x*RegularWreathProduct.inl turn=RegularWreathProduct.inl turn*x →
    x=1 ∨ x=centralInP := by
  decide +kernel

theorem center_P : center P=centralLine := by
  ext x
  rw [mem_centralLine]
  constructor
  · intro hx
    exact center_tests x (mem_center_iff.mp hx _).symm
      (mem_center_iff.mp hx _).symm (mem_center_iff.mp hx _).symm
  · rintro (rfl|rfl)
    · exact one_mem _
    · exact mem_center_iff.mpr centralInP_central

theorem z_order : orderOf z=2 := by
  rw [←sylowEmbedding_centralInP,orderOf_injective sylowEmbedding sylowEmbedding_injective,centralInP_order]

theorem center_standardSylow :
    (center (standardSylow:Subgroup W)).map (standardSylow:Subgroup W).subtype=zpowers z := by
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    obtain ⟨b,hb⟩ := a.property
    have hc : b∈center P := by
      apply mem_center_iff.mpr
      intro c
      apply sylowEmbedding_injective
      have h := congrArg Subtype.val (mem_center_iff.mp ha ⟨sylowEmbedding c,⟨c,rfl⟩⟩)
      change sylowEmbedding c * (a:W)=(a:W)*sylowEmbedding c at h
      simpa only [map_mul,hb] using h
    rw [center_P] at hc
    change (a:W)∈zpowers z
    rw [←hb,←sylowEmbedding_centralInP,←MonoidHom.map_zpowers]
    exact mem_map_of_mem sylowEmbedding hc
  · intro hx
    have hzle : zpowers z ≤ (center (standardSylow:Subgroup W)).map (standardSylow:Subgroup W).subtype := by
      apply zpowers_le.mpr
      refine ⟨⟨z,z_mem_standardSylow⟩,?_,rfl⟩
      apply mem_center_iff.mpr
      intro a
      obtain ⟨b,hb⟩ := a.property
      apply Subtype.ext
      change (a:W)*z=z*(a:W)
      rw [←hb,←sylowEmbedding_centralInP,←map_mul,←map_mul,centralInP_central]
    exact hzle hx
end SymmetricFourWreath
