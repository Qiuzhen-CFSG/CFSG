module

public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.CharacteristicControl
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.BlockTransport
public import CFSG.Quasithin.ChapterC.Section01.RankOne.LocalC129.A7Control

/-!
# A moved χ₀ block from the original C.5 hypotheses

The characteristic normalizers of R lie in the unique maximal subgroup
over T_H. Apply the genuine earlier C.1.28 outside-block implication in
RK, then the proved C.1.29 alternating-seven exclusion. Faithful inclusion
into H preserves the original block, its module type and J(R)-movement.

The universal earlier C.1.28 implication is owned by the C.1 source
assembly. No block or action certificate is included in this input.
Source: Aschbacher–Smith C.5.3, printed pp.154–155, with C.1.28–29.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
universe u

/-- The literal earlier C.1.28 source theorem, retained for its source owner. -/
def C128Outside (𝒦 : GroupClass.{u}) : Prop :=
  ∀ {A : Type u} [Group A] [Finite A], IsSQTK 𝒦 A →
    generalizedFitting A = pCore 2 A → ∀ (S : Sylow 2 A) (N : Subgroup A),
    (S : Subgroup A).characteristicNormalizerClosure ≤ N → N ≠ ⊤ →
    ∃ L : Subgroup A, ¬L ≤ N ∧ IsChiBlockIn L ∧
      L = ⁅L,elementaryAbelianMaxJ (S : Subgroup A)⁆

variable {G : Type u} [Group G] [Finite G] {𝒦 : GroupClass.{u}}
variable {H M K R T : Subgroup G}

/-- A literal χ₀ block of H outside its unique maximal subgroup, moved
by the original J(R). All source placement assumptions are discharged. -/
theorem OriginalHypotheses.exists_moved_chiZero
    (d : OriginalHypotheses H M K R T) (outside : C128Outside 𝒦)
    (hG : IsSQTK 𝒦 G) (N : Subgroup H)
    (hN : (d.sylow : Subgroup H) ≤ N ∧ IsCoatom N) :
    ∃ L : Subgroup H, IsChiZeroBlockIn L ∧ ¬ L ≤ N ∧
      L = ⁅L,elementaryAbelianMaxJ (R.subgroupOf H)⁆ := by
  let J := R ⊔ K
  let B := (N.map H.subtype).subgroupOf J
  have hc := d.residual_characteristic_control N hN
  have hb := d.residual_maximal_restriction_ne_top N hN
  have hJ := hG.subgroup J
  have hfJ := d.residual_join_fitting
  obtain ⟨L,hout,hL,hm⟩ := outside hJ hfJ d.residual_sylow B hc hb
  have hz : IsChiZeroBlockIn L := by
    rcases LocalC129.chi_zero_or_alternating_seven_in hJ.stronglyQuasithin hL with hz | ha
    · exact hz
    · exact False.elim (hout ((LocalC129.alternating_seven_le_control_of_c128_outside
        outside hJ hfJ d.residual_sylow hL.1 ha.2).trans hc))
  let f : J →* H := inclusion (sup_le d.R_le_H d.K_le_H)
  have hfi : Function.Injective f := inclusion_injective _
  have hfr : f.range.IsSubnormal := by
    rw [inclusion_range]
    exact d.residual_join_normal.isSubnormal
  have hP : (d.residual_sylow : Subgroup J).map f = R.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_map,map_subgroupOf_eq_of_le d.R_le_H]
    exact d.residual_sylow_image
  refine ⟨L.map f,chiZero_map f hfi hfr hz,?_,?_⟩
  · intro hLN
    apply hout
    intro l hl
    exact mem_map_of_mem H.subtype (hLN (mem_map_of_mem f hl))
  · have he := congrArg (Subgroup.map f) hm
    rw [map_commutator,←elementaryAbelianMaxJ_map_injective f hfi,hP] at he
    exact he

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
end
