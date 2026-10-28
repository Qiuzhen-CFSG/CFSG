module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.Marking.Basic
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.Flag.Borel.PlaneLevi
public import Theory.GroupTheory.SylowNormalizerSupplement
/-!
# The plane-parabolic Borel and normality of the common Sylow

The residual projection carries the common Sylow to the upper root in SL₂.
Its normalizer is upper triangular, exactly the condition that the actual
Levi matrix preserve the marked line. The normal-supplement argument extends
this equality to the full plane parabolic. Its image in the common carrier
then proves normality of the overlap Sylow.

Source: Aschbacher--Smith, F.1.3 and F.1.12(7), printed pp.260 and 263--264.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
open Matrix Theory.SpecificGroups.UnitaryFive
variable (M : Model 4)

/-- The intrinsic residual normalizer is the literal overlap intersection. -/
theorem rightSylowNormalizer_eq_overlap :
    M.rightSylowNormalizer = (M.overlap.subgroupOf M.rightParabolic).subgroupOf M.rightLocal := by
  change Subgroup.normalizer ((SpecialLinearGroup.upperUnipotent M.F).comap
    M.rightLocalProjection : Set M.rightLocal) = _
  rw [← Subgroup.comap_normalizer_eq_of_surjective _ M.rightLocalProjection_surjective]
  ext g
  change M.rightLocalProjection g ∈ SpecialLinearGroup.rankOneBorel M.F ↔ _
  rw [SpecialLinearGroup.mem_rankOneBorel_iff]
  obtain ⟨p, rfl⟩ := M.rightLocalEquiv.surjective g
  rw [M.rightLocalProjection_equiv]
  change p.right.val 1 0 = 0 ↔ (M.rightLocalEquiv p).val ∈
    M.overlap.subgroupOf M.rightParabolic
  rw [M.rightLocalEquiv_val]
  have hu : PlaneCore.Parameters.toParabolic M.matrix p.left ∈
      M.overlap.subgroupOf M.rightParabolic :=
    M.flagRight_le_overlap (Subgroup.mem_sup_left ⟨p.left, rfl⟩)
  rw [(M.overlap.subgroupOf M.rightParabolic).mul_mem_cancel_left hu]
  change p.right.val 1 0 = 0 ↔
    (M.rightSLLevi p.right).val ∈ M.leftParabolic ∧
      (M.rightSLLevi p.right).val ∈ M.rightParabolic
  rw [and_iff_left (M.rightSLLevi p.right).property]
  exact (Flag.planeSL_mem_line_iff M.form M.rightLeviTrace
    M.rightLeviTrace_spec M.matrix p.right).symm

/-- The source B₂ is the intersection in the common projective carrier. -/
theorem rightSylowNormalizerImage_eq :
    M.rightSylowNormalizerImage = M.rightLocalImage ⊓ M.overlap := by
  rw [rightSylowNormalizerImage, M.rightSylowNormalizer_eq_overlap, ← Subgroup.map_map,
    Subgroup.subgroupOf_map_subtype]
  rw [Subgroup.map_inf _ _ _ Subtype.val_injective,
    Subgroup.map_subgroupOf_eq_of_le (show M.overlap ≤ M.rightParabolic from inf_le_right)]
  exact inf_comm _ _

/-- The full plane-parabolic normalizer is its flag stabilizer. -/
theorem rightParabolicSylow_normalizer :
    Subgroup.normalizer (M.rightParabolicSylow : Set M.rightParabolic) =
      M.overlap.subgroupOf M.rightParabolic := by
  have hSR : (M.rightParabolicSylow : Subgroup M.rightParabolic) ≤ M.rightLocal := by
    change (M.rightLocalSylow : Subgroup M.rightLocal).map M.rightLocal.subtype ≤ _
    exact (Subgroup.map_le_range _ _).trans_eq (Subgroup.range_subtype _)
  have hSB : (M.rightParabolicSylow : Subgroup M.rightParabolic) ≤
      M.overlap.subgroupOf M.rightParabolic := by
    change (M.rightLocalSylow : Subgroup M.rightLocal).map M.rightLocal.subtype ≤ _
    rw [M.rightLocalSylow_map]
    exact M.flagRight_le_overlap
  apply M.rightParabolicSylow.normalizer_eq_of_normal_supplement M.rightLocal
    (M.overlap.subgroupOf M.rightParabolic) hSR hSB M.rightLocal_sup_overlap
  have he : M.rightParabolicSylow.subtype hSR = M.rightLocalSylow := by
    apply Sylow.ext
    change ((M.rightLocalSylow : Subgroup M.rightLocal).map M.rightLocal.subtype).comap
      M.rightLocal.subtype = _
    exact Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _
  rw [he]
  exact M.rightSylowNormalizer_eq_overlap

/-- The common Sylow is normal in the full overlap. -/
theorem overlapSylow_normal : (M.overlapSylow : Subgroup M.overlap).Normal := by
  have hle : M.overlap ≤ Subgroup.normalizer (M.flagTwoSubgroup : Set M.Carrier) := by
    intro g hg
    have hg' : (⟨g, hg.2⟩ : M.rightParabolic) ∈
        Subgroup.normalizer (M.rightParabolicSylow : Set M.rightParabolic) := by
      rw [M.rightParabolicSylow_normalizer]
      exact hg
    rw [← M.rightParabolicSylow_map]
    exact Subgroup.le_normalizer_map M.rightParabolic.subtype ⟨⟨g,hg.2⟩,hg',rfl⟩
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer M.flagTwoSubgroup_le_overlap).mpr hle
end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
