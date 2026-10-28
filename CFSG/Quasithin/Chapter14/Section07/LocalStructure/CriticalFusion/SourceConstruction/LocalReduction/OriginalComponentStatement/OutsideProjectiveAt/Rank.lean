module
public import Theory.GroupTheory.CubicCoreCentralizerRank
public import Theory.SpecificGroups.PSL3.SplitThreeRank
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideProjectiveAt.LinearActions
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideProjectiveAt.UnitaryActions
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ProjectiveNormalityAt
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank
public import Theory.GroupTheory.CubicCoreCentralizerRank
public import Theory.SpecificGroups.PSL3.SplitThreeRank

/-!
# Projective-three rank forces the original point into the component

A cubic outside the normal component centralizes its intrinsic quotient.
The local three-rank bound therefore leaves at most one three-direction in
that component. Explicit projective nines exclude the outside branch for
even-degree linear-three and odd-degree unitary-three groups. All structural
hypotheses concern the original group and Sylow.

Source: Aschbacher–Smith 14.7.41–42, printed pp.1061–1062.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideProjectiveAt
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original outside component has three-rank at most one in the large linear-three row. -/
theorem linear_component_threeRank_le_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) (hout : ¬ F.Li L 1 ≤ C.map I.subtype)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    {n : ℕ} (hE : Nat.card E = 2^n) (hn : 3 ≤ n)
    (e : (C ⧸ pCore 2 C) ≃* PSL(3,E)) : primeRank 3 C ≤ 1 := by
  let : C.Normal := local_projective_linearThree_normal_at d h hab structural previous
    faithful earlier I hI C hC (by omega : 0 < n) hE e
  obtain ⟨_,hfix,_⟩ := linear_component_normalizes_point_at
    d h hab structural previous faithful earlier I hI C hout hE hn e
  let A := (F.Li L 1).subgroupOf I
  have hAI := F.Li_one_le_of_mem_Hz hI
  let ea := subgroupOfEquivOfLe hAI
  have hc : Nat.card (A ⧸ pCore 2 A) = 3 := by
    rw [Nat.card_congr (QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)).toEquiv]
    exact pointResidual_core_quotient_card_at h structural
  have hz : center (C ⧸ pCore 2 C) = ⊥ := by
    let : Group.IsPerfect SL(3,E) := Atlas.sl_perfect 3 (by decide)
    have hze : center PSL(3,E) = ⊥ :=
      Group.IsPerfect.center_quotient_center_eq_bot SL(3,E)
    apply bot_unique
    intro z hz
    have hh := (centerCongr e ⟨z,hz⟩).property
    change e z ∈ center PSL(3,E) at hh
    rw [hze,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  have hrI : primeRank 3 I ≤ 2 := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 I) pCore_isPGroup]
    exact (local_star_sqtk h I hI).stronglyQuasithin 3 (by decide) (by decide)
  have hr := threeRank_le_one_of_cubic_core_centralizes A C hc hz hrI hfix
  rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 C) pCore_isPGroup] at hr
  exact hr


/-- The original outside component has three-rank at most one in the binary unitary-three row. -/
theorem unitary_component_threeRank_le_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) (hout : ¬ F.Li L 1 ≤ C.map I.subtype)
    {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (C ⧸ pCore 2 C) ≃* ProjectiveSpecialUnitaryMatrixGroup J) : primeRank 3 C ≤ 1 := by
  let : C.Normal := local_projective_unitaryThree_normal_at d h hab structural previous
    faithful earlier I hI C hC J (by omega : 0 < n) hE hconj e
  obtain ⟨_,hfix,_⟩ := unitary_component_normalizes_point_at
    d h hab structural previous faithful earlier I hI C hout J hn hE hconj e
  let A := (F.Li L 1).subgroupOf I
  have hAI := F.Li_one_le_of_mem_Hz hI
  let ea := subgroupOfEquivOfLe hAI
  have hc : Nat.card (A ⧸ pCore 2 A) = 3 := by
    rw [Nat.card_congr (QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)).toEquiv]
    exact pointResidual_core_quotient_card_at h structural
  have hz : center (C ⧸ pCore 2 C) = ⊥ := by
    have hze := HermitianForm.EvenProjectiveComparison.center_eq_bot J
      (by omega : 0 < n) hE hconj
    apply bot_unique
    intro z hz
    have hh := (centerCongr e ⟨z,hz⟩).property
    change e z ∈ center (ProjectiveSpecialUnitaryMatrixGroup J) at hh
    rw [hze,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  have hrI : primeRank 3 I ≤ 2 := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 I) pCore_isPGroup]
    exact (local_star_sqtk h I hI).stronglyQuasithin 3 (by decide) (by decide)
  have hr := threeRank_le_one_of_cubic_core_centralizes A C hc hz hrI hfix
  rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 C) pCore_isPGroup] at hr
  exact hr


/-- In an even-degree binary linear-three quotient the original point
residual is contained in the component. -/
theorem local_large_even_linearThree_contains_point_at
    (d : Counterexample T L) (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    {E : Type*} [Field E] [Finite E] [CharP E 2] {n : ℕ} (hE : Nat.card E = 2^n)
    (hn : 4 ≤ n) (heven : Even n) (e : (C ⧸ pCore 2 C) ≃* PSL(3,E)) : F.Li L 1 ≤ C.map I.subtype := by
  by_contra hout
  have hr := linear_component_threeRank_le_at d h hab structural previous faithful earlier
    I hI C hC hout hE (by omega) e
  have hh := Matrix.PSL3.SplitThreeRank.even_binary_rank hE heven
  rw [←primeRank_congr 3 e, primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 C) pCore_isPGroup] at hh
  omega

/-- In an odd-degree unitary-three quotient the original point residual is
contained in the component. -/
theorem local_odd_unitaryThree_contains_point_at
    (d : Counterexample T L) (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n)) (hodd : Odd n)
    (e : (C ⧸ pCore 2 C) ≃* ProjectiveSpecialUnitaryMatrixGroup J) : F.Li L 1 ≤ C.map I.subtype := by
  by_contra hout
  have hr := unitary_component_threeRank_le_at d h hab structural previous faithful earlier
    I hI C hC hout J hn hE hconj e
  have hh := Theory.SpecificGroups.SignedThreeCubicRank.unitary_projective J (by omega) hE hconj hodd
  rw [←primeRank_congr 3 e, primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 C) pCore_isPGroup] at hh
  omega

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideProjectiveAt
