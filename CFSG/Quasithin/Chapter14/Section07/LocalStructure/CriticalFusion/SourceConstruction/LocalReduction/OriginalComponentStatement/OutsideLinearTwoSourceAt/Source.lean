module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideLinearTwoSourceAt.Model
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NonnormalBinarySourceAt.PlaneContradiction

/-!
# Actual original outside binary components have field four and large sections

The original-source normality theorem supplies component normality internally.
The binary model and alternating-five wrappers therefore use only the original
component and local hypotheses, with structural and predecessor inputs at the
same group and Sylow. Their actions are on the literal original section.
Source: Aschbacher–Smith 14.7.32 and 14.7.42–46, printed pp.1058–1063.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideLinearTwoSourceAt
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The packaged actual binary linear-two row has field four and an original
section of rank at least eight when the point lies outside the component. -/
theorem local_binary_model_field_four_rank_ge_eight_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (hout : ¬ F.Li L 1 ≤ C.map I.subtype)
    (n : ℕ) (hn : 1 < n) (hm : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 (2^n)) :
    n = 2 ∧ ∃ hU : IsElementaryAbelian 2 (F.UH I),
      let := hU
      ∃ _a : LocalQuotientAction I (F.UH I) (F.Vi 1),
        8 ≤ Module.finrank (ZMod 2) (Additive ((F.UH I) ⧸ (F.Vi 1).subgroupOf (F.UH I))) := by
  have hC' : ((C.map I.subtype).subgroupOf I).IsCComponent := by
    simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hC
  have hnC := local_cComponent_normal_at d h hab structural previous faithful earlier
    I (C.map I.subtype) hI (map_subtype_le _) hC'
  let : C.Normal := by
    simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hnC
  exact local_normal_binary_model_field_four_rank_ge_eight_at d h hab structural previous
    faithful earlier I hI C hC hout n hn hm

/-- The actual outside alternating-five component supplies the original
rank-eight section required by the mixed-amalgam size comparison. -/
theorem local_alternating_five_rank_ge_eight_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (hout : ¬ F.Li L 1 ≤ C.map I.subtype)
    (e : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5)) :
    ∃ hU : IsElementaryAbelian 2 (F.UH I),
      let := hU
      ∃ _a : LocalQuotientAction I (F.UH I) (F.Vi 1),
        8 ≤ Module.finrank (ZMod 2) (Additive ((F.UH I) ⧸ (F.Vi 1).subgroupOf (F.UH I))) := by
  have hC' : ((C.map I.subtype).subgroupOf I).IsCComponent := by
    simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hC
  have hnC := local_cComponent_normal_at d h hab structural previous faithful earlier
    I (C.map I.subtype) hI (map_subtype_le _) hC'
  let : C.Normal := by
    simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hnC
  exact local_normal_alternating_five_rank_ge_eight_at d h hab structural previous
    faithful earlier I hI C hC hout e

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideLinearTwoSourceAt
