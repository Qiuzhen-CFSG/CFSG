module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedProjectiveAt.LinearField
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedProjectiveAt.UnitaryField
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedProjectiveAt.ProjectiveExceptions
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideProjectiveAt.Rank

/-!
# Contained projective-three exclusions at the same G,T

The original Borel bounds give field four or eight, excluded by the actual
quadratic action. The outside cubic-rank bounds supply the parity containment
applications. Source: Aschbacher--Smith 14.7.41,43--44, pp.1061--1062.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedProjectiveAt
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
open Chapter13.Section08.Components Swapped Swapped.LinearTwo
open Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
  (coreAction coreAction_mk coreAction_eq_one_iff)
open AlternatingSevenSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
/-- The contained projective linear-three branch of 14.7.41 is impossible:
the original Borel forces field four, excluded on the actual module. -/
theorem local_linearThree_contained_impossible_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (hin : F.Li L 1 ≤ C.map I.subtype)
    {E : Type} [Field E] [Finite E] [CharP E 2]
    {n : ℕ} (hE : Nat.card E = 2^n) (hn : 1 < n)
    (e : (C ⧸ pCore 2 C) ≃* PSL(3,E)) : False := by
  have hn2 := local_linearThree_contained_field_four_at d h hab structural previous faithful
    earlier I hI C hC hin hE hn e
  exact (local_projective_exceptional_components_impossible_at d h hab structural previous
    faithful earlier I hI C hC).1 ⟨E,inferInstance,inferInstance,by simpa [hn2] using hE,⟨e⟩⟩

/-- Every even-degree nonbinary projective linear-three component is excluded,
without an assumed containment of the original point residual. -/
theorem local_even_linearThree_component_impossible_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    {E : Type} [Field E] [Finite E] [CharP E 2]
    {n : ℕ} (hE : Nat.card E = 2^n) (hn : 1 < n) (heven : Even n)
    (e : (C ⧸ pCore 2 C) ≃* PSL(3,E)) : False := by
  by_cases hn2 : n = 2
  · exact (local_projective_exceptional_components_impossible_at d h hab structural previous
      faithful earlier I hI C hC).1
      ⟨E,inferInstance,inferInstance,by simpa [hn2] using hE,⟨e⟩⟩
  · have hn4 : 4 ≤ n := by obtain ⟨k,hk⟩ := heven; omega
    have hin := OutsideProjectiveAt.local_large_even_linearThree_contains_point_at
      d h hab structural previous faithful earlier I hI C hC hE hn4 heven e
    exact local_linearThree_contained_impossible_at d h hab structural previous faithful
      earlier I hI C hC hin hE hn e

/-- The contained projective unitary-three branch of 14.7.41 is impossible:
the original Borel forces field eight, excluded on the actual module. -/
theorem local_unitaryThree_contained_impossible_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (hin : F.Li L 1 ≤ C.map I.subtype)
    {E : Type} [Field E] [Finite E]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (C ⧸ pCore 2 C) ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :
    False := by
  have hn3 := local_unitaryThree_contained_field_eight_at d h hab structural previous faithful
    earlier I hI C hC hin J hn hE hconj e
  exact (local_projective_exceptional_components_impossible_at d h hab structural previous
    faithful earlier I hI C hC).2 ⟨E,inferInstance,inferInstance,J,
      by simpa [hn3] using hE,by simpa [hn3] using hconj,⟨e⟩⟩

/-- Every odd-degree nonbinary projective unitary-three component is excluded,
with original point containment supplied by the three-rank argument. -/
theorem local_odd_unitaryThree_component_impossible_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    {E : Type} [Field E] [Finite E]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n)) (hodd : Odd n)
    (e : (C ⧸ pCore 2 C) ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :
    False := by
  have hin := OutsideProjectiveAt.local_odd_unitaryThree_contains_point_at d h hab structural previous
    faithful earlier I hI C hC J hn hE hconj hodd e
  exact local_unitaryThree_contained_impossible_at d h hab structural previous faithful
    earlier I hI C hC hin J hn hE hconj e

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedProjectiveAt
