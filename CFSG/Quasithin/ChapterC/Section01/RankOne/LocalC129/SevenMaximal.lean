module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.LocalC129.SevenGeometry
public import CFSG.Quasithin.ChapterC.Section01.RankOne.LocalC129.SixQuotient
public import Theory.SpecificGroups.Alternating.SevenComponent.PointSix

/-!
# The actual maximal six-point obstruction

Combining the constructed seven-letter action with the exact point-preimage
quotient gives a maximal subgroup containing the original Sylow two-group.
Its intrinsic quotient is A₆ or S₆, so it contains no actual χ-block, while
C(G,T) is not contained in it. This is the precise C.1.28 consumer needed
for the ordinary A₇ exclusion in C.1.29, printed p.134.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.LocalC129
variable {G : Type*} [Group G] [Finite G]

/-- The actual A₇ source extension has a maximal Sylow overgroup with no
χ-blocks, while its characteristic-normalizer control is not contained there. -/
theorem alternating_seven_six_point_obstruction
    (hs : IsStronglyQuasithin G) (T : Sylow 2 G)
    {K : Subgroup G} (hK : IsBlock K) (ha : IsAlternatingBlock K 7)
    (hgen : K ⊔ (T : Subgroup G) = ⊤) :
    ∃ H : Subgroup G, (T : Subgroup G) ≤ H ∧ IsCoatom H ∧
      (∀ L : Subgroup H, ¬ IsChiBlockIn L) ∧
      ¬(T : Subgroup G).characteristicNormalizerClosure ≤ H := by
  obtain ⟨f, hk, hA, hT, hout⟩ := alternating_seven_control_geometry hs T hK ha hgen
  let H := (MulAction.stabilizer (Equiv.Perm (Fin 7)) (6 : Fin 7)).comap f
  have hker : IsPGroup 2 f.ker := hk.symm ▸ pCore_isPGroup
  refine ⟨H, hT, alternatingGroup.SevenComponent.point_preimage_isCoatom f hA _, ?_, hout⟩
  rcases alternatingGroup.SevenComponent.point_preimage_six_coreQuotient f hker hA (6 : Fin 7)
    with he | he
  · obtain ⟨e⟩ := he
    exact no_chiBlock_of_six_core_quotient (hs.subgroup H) e
  · obtain ⟨e⟩ := he
    exact no_chiBlock_of_symmetric_six_core_quotient (hs.subgroup H) e
end CFSG.Quasithin.ChapterC.LocalC129
