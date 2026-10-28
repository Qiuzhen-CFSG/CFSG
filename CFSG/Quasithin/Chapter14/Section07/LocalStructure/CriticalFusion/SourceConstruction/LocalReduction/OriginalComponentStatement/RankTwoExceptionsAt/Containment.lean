module
public import Theory.SpecificGroups.CubicComponentContainment
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Source.SolvableConclusion
public import Theory.GroupTheory.CComponent.CenterlessRankNormal

/-!
# Actual G₂ and symplectic-four components at the original G,T

The component quotient is centerless and has cubic rank at least two.
Distinct conjugate components would exceed the ambient cubic rank bound,
so the original component is normal. The native cubic outer-action theorem
then absorbs the original two-perfect point residual into that component.

All structural inputs concern the same original group and Sylow subgroup.
No general normal-component theorem, later 14.7.47 input, or supplied
normality or point containment is required.
Source: Aschbacher–Smith 14.7.41, printed p.1061, using A.3.18,
pp.51–53, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}


private theorem local_normal_of_rank_two_model_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    {X : Type*} [Group X] [Finite X] (e : (C ⧸ pCore 2 C) ≃* X)
    (hz : center X = ⊥) (hr : 2 ≤ primeRank 3 X) : C.Normal := by
  let := WholeResidualAssembly.GuardedSource.local_component_twoCore_isQuasisimple
    h hab structural previous faithful I hI C hC
  have hzC : center (C ⧸ pCore 2 C) = ⊥ := by
    apply bot_unique
    intro z hz'
    have hh := (centerCongr e ⟨z,hz'⟩).property
    change e z ∈ center X at hh
    rw [hz,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  have hrC : 2 ≤ primeRank 3 (C ⧸ pCore 2 C) := by rwa [←primeRank_congr 3 e] at hr
  have hrI : primeRank 3 I ≤ 2 := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 I) pCore_isPGroup]
    exact (local_star_sqtk h I hI).stronglyQuasithin 3 (by decide) (by decide)
  exact hC.normal_of_centerless_core_threeRank hzC hrC hrI

/-- Cubic rank forces normality of every actual nonbinary G₂ component. -/
theorem local_gTwo_component_normal_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    {E : Type*} [Field E] [Finite E] [CharP E 2] (hE : 2 < Nat.card E)
    (e : (C ⧸ pCore 2 C) ≃* Atlas.G2.Model E) : C.Normal :=
  local_normal_of_rank_two_model_at h hab structural previous faithful I hI C hC e
    (Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot hE) Atlas.G2.CubicFieldActors.cubic_rank

/-- Cubic rank forces normality of every actual symplectic-four component. -/
theorem local_symplecticFour_component_normal_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (e : (C ⧸ pCore 2 C) ≃* Matrix.symplecticGroup (Fin 2) E) : C.Normal :=
  local_normal_of_rank_two_model_at h hab structural previous faithful I hI C hC e
    Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot
    Theory.SpecificGroups.SymplecticFour.OddFieldActors.cubic_rank

/-- The original point residual lies in each actual large-field G₂ component. -/
theorem local_gTwo_component_contains_point_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    {E : Type*} [Field E] [Finite E] [CharP E 2] (hE : 2 < Nat.card E)
    (e : (C ⧸ pCore 2 C) ≃* Atlas.G2.Model E) : F.Li L 1 ≤ C.map I.subtype := by
  let : C.Normal := local_gTwo_component_normal_at h hab structural previous faithful I hI C hC hE e
  have hrI : primeRank 3 I ≤ 2 := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 I) pCore_isPGroup]
    exact (local_star_sqtk h I hI).stronglyQuasithin 3 (by decide) (by decide)
  let A := (F.Li L 1).subgroupOf I
  have hAI := F.Li_one_le_of_mem_Hz hI
  let ea := subgroupOfEquivOfLe hAI
  have hp : IsPPerfect 2 A :=
    (show IsPPerfect 2 (F.Li L 1) from isPPerfect_embedded_pResidual 2 _).of_surjective
      ea.symm.toMonoidHom ea.symm.surjective
  have hc : Nat.card (A ⧸ pCore 2 A) = 3 := by
    rw [Nat.card_congr (QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)).toEquiv]
    exact pointResidual_core_quotient_card_at h structural
  have hh := map_mono (f := I.subtype)
    (Theory.SpecificGroups.CubicComponentContainment.gTwo_twoPerfect_cubic_le
      A C hC hp hc hrI hE e)
  rwa [map_subgroupOf_eq_of_le hAI] at hh

/-- The original point residual lies in each actual large-field Sp₄ component. -/
theorem local_symplecticFour_component_contains_point_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    {E : Type*} [Field E] [Finite E] [CharP E 2] (hE : 2 < Nat.card E)
    (e : (C ⧸ pCore 2 C) ≃* Matrix.symplecticGroup (Fin 2) E) :
    F.Li L 1 ≤ C.map I.subtype := by
  let : C.Normal := local_symplecticFour_component_normal_at h hab structural previous faithful I hI C hC e
  have hrI : primeRank 3 I ≤ 2 := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 I) pCore_isPGroup]
    exact (local_star_sqtk h I hI).stronglyQuasithin 3 (by decide) (by decide)
  let A := (F.Li L 1).subgroupOf I
  have hAI := F.Li_one_le_of_mem_Hz hI
  let ea := subgroupOfEquivOfLe hAI
  have hp : IsPPerfect 2 A :=
    (show IsPPerfect 2 (F.Li L 1) from isPPerfect_embedded_pResidual 2 _).of_surjective
      ea.symm.toMonoidHom ea.symm.surjective
  have hc : Nat.card (A ⧸ pCore 2 A) = 3 := by
    rw [Nat.card_congr (QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)).toEquiv]
    exact pointResidual_core_quotient_card_at h structural
  have hh := map_mono (f := I.subtype)
    (Theory.SpecificGroups.CubicComponentContainment.symplecticFour_twoPerfect_cubic_le
      A C hC hp hc hrI hE e)
  rwa [map_subgroupOf_eq_of_le hAI] at hh

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
