module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.MiddleSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded.SmallGeometry

/-!
# Original small-quotient exclusion: MiddleSource

The source proof is specialized to the same G,T structural and escape inputs.
All subgroup restrictions, quotient maps and the actual rank-three system
are retained. The universal public API in the original module is unchanged.
Source: Aschbacher–Smith 14.7.11,49, printed pp.1045–1046,1064,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Quasithin.I5
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.Components

/-- Apply the middle-quotient proof to the actual local second parabolic.
The extra source premise is the original point-core movement, not supplied
normality, generation, a quotient or a rank-two residue. -/
theorem small_local_middle_quotient
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hmovement : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hm : Nonempty (HStar I ≃* Matrix.PSL3Two.PSL) ∨
      Nonempty (HStar I ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (HStar I ≃* Equiv.Perm (Fin 6))) :
    ∃ H₂ Y : Subgroup G, H₂ = I ⊓ F.Gi 2 ∧
      RankTwoParabolics I ((T : Subgroup G).subgroupOf I)
        ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I) (H₂.subgroupOf I) ∧
      Nonempty (HStar H₂ ≃* Equiv.Perm (Fin 3)) ∧
      Y = (pResidual 2 H₂).map H₂.subtype ∧ IsPPerfect 2 Y ∧
      (T : Subgroup G) ≤ normalizer (Y : Set G) ∧ Y ⊔ (T : Subgroup G) = H₂ ∧
      (F.Li L 1 ⊔ (T : Subgroup G)) ⊔ Y = I ∧
      ¬ Y ≤ normalizer (L : Set G) ∧ ⁅F.Vi 2,Y⁆ = ⊥ ∧
      (H₂ ⊔ F.P L) ⊓ I = H₂ ∧
      (H₂ ⊔ F.P L) ⊓ (L ⊔ (T : Subgroup G)) = F.P L ∧
      (H₂ ⊔ F.P L) ⊓ I ⊓ (L ⊔ (T : Subgroup G)) = (T : Subgroup G) ∧
      Nonempty (HStar (H₂ ⊔ F.P L) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      RankTwoParabolics (H₂ ⊔ F.P L : Subgroup G) ((T : Subgroup G).subgroupOf (H₂ ⊔ F.P L))
        (H₂.subgroupOf (H₂ ⊔ F.P L)) ((F.P L).subgroupOf (H₂ ⊔ F.P L)) := by
  obtain ⟨H₂,Y,h₂I,hT₂,hR,he,hY,hYp,hYn,hYT,hgen,hout,hc,h₂eq,hJI,hJLT,hchamber⟩ :=
    small_local_middle_intersections h hab structural previous faithful I hI hm
  have h₂plane : H₂ ≤ F.Gi 2 := h₂eq.le.trans inf_le_right
  obtain ⟨hquot,hline⟩ := middle_quotient_and_parabolics_at h structural
    hmovement H₂ (h₂I.trans hI.2.1) hT₂ h₂plane he.some
  exact ⟨H₂,Y,h₂eq,hR,he,hY,hYp,hYn,hYT,hgen,hout,hc,hJI,hJLT,hchamber,hquot,hline⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded
