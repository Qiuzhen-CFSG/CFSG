module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.BinaryThreeContainment.Module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.BinaryThreeContainment.NormalityAt

/-!
# Binary linear-three containment at the same original G,T

The exchanged-component parabolic argument proves normality of the actual
binary linear-three component using only the original same-group earlier
hypotheses. Its literal reduced local then satisfies the proved module
exclusion. Transport preserves the intrinsic component quotient and its
ambient image, so the original point residual lies in the original component.
No universal structural premise or later 14.7.47 conclusion is used.

Source: Aschbacher–Smith, 14.7.32 and 14.7.47, printed pp.1056 and
1062–1063, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The binary L₃(2) containment case of 14.7.47, with the original
same-group earlier hypotheses and no additional normality assumption. -/
theorem local_binaryThree_component_contains_point_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* Matrix.PSL3Two.PSL) :
    F.Li L 1 ≤ C.map I.subtype := by
  let K := C.map I.subtype
  have hKI : K ≤ I := map_subtype_le C
  have hK : (K.subgroupOf I).IsCComponent := by
    simpa only [K,subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hC
  let eK : Chapter13.Section08.Source.starImage I K ≃* Matrix.PSL3Two.PSL := by
    change ((K.comap I.subtype).map (QuotientGroup.mk' (pCore 2 I))) ≃* _
    rw [show K = C.map I.subtype from rfl,comap_map_eq_self_of_injective I.subtype_injective]
    exact (cComponentTwoCoreQuotientEquiv hC).symm.trans e
  obtain ⟨hn,hJ⟩ := BinaryThreeContainment.local_linearThree_normal_and_mem_Hz_at
    d h hab structural previous faithful earlier I K hI hKI hK eK
  let J := K ⊔ (F.Li L 1 ⊔ (T : Subgroup G))
  let CJ := K.subgroupOf J
  have hKJ : K ≤ J := le_sup_left
  have hJI : J ≤ I := sup_le hKI
    (sup_le (F.Li_one_le_of_mem_Hz hI) (F.sylow_le_of_mem_Hz hI))
  have hCJ : CJ.IsCComponent := hK.subgroupOf_of_le hKJ hJI
  let : CJ.Normal := (normal_subgroupOf_iff_le_normalizer hKJ).mpr
    (hJI.trans ((normal_subgroupOf_iff_le_normalizer hKI).mp hn))
  have hambient : CJ.map J.subtype = C.map I.subtype := map_subgroupOf_eq_of_le hKJ
  let eC : C ≃* CJ := (equivMapOfInjective C I.subtype I.subtype_injective).trans
    (subgroupOfEquivOfLe hKJ).symm
  let eQ := QuotientGroup.congr _ _ eC (pCore_map_iso 2 eC)
  have hgen : J = CJ.map J.subtype ⊔ F.Li L 1 ⊔ (T : Subgroup G) := by
    rw [hambient,sup_assoc]
  have hh := BinaryThreeContainment.reduced_containment_at d h hab structural previous
    faithful earlier J hJ CJ hCJ hgen (eQ.symm.trans e)
  rwa [hambient] at hh

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
