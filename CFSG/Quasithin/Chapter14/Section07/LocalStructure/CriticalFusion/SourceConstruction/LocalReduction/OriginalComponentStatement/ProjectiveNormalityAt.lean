module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.BinaryThreeContainment.NonnormalAt
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.LinearTwoSeparation
public import Theory.SpecificGroups.SU3.BinaryOrderFour
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.OrderFour

/-!
# Original projective component normality at the same G,T

An actual nonnormal component has a binary PSL₂ intrinsic two-core
quotient. Such a group has elementary abelian Sylow two-subgroups and no
element of order four. The actual PSL₃ Sylow calculation and an explicit
PSU₃ root element therefore prove normality of either projective-three
component at the original G,T. No universal structural record or later
14.7.47 conclusion is used.

Source: Aschbacher–Smith 14.7.30–32, printed pp.1055–1056, and the
defining-characteristic Sylow matrix models, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Normality of the actual binary PSL₃ component, with structural inputs
only at the original Sylow. -/
theorem local_projective_linearThree_normal_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    {E : Type*} [Field E] [Finite E] {n : ℕ} (hn : 0 < n)
    (hE : Nat.card E = 2 ^ n) (e : (C ⧸ pCore 2 C) ≃* PSL(3,E)) : C.Normal := by
  by_contra hnC
  obtain ⟨m,hm,D,_,_,hD,⟨f⟩⟩ := local_nonnormal_component_binary_at
    d h hab structural previous faithful earlier I hI C hC hnC
  let : Fintype D := Fintype.ofFinite D
  let : CharP D 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hD)
  exact Matrix.PSL3.LinearThree.not_equiv_linear_two hn hE ⟨e.symm.trans f⟩

/-- Normality of the actual binary PSU₃ component, preserving the specified
Hermitian form and its intrinsic quotient equivalence. -/
theorem local_projective_unitaryThree_normal_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {n : ℕ} (hn : 0 < n) (hE : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
    (e : (C ⧸ pCore 2 C) ≃* ProjectiveSpecialUnitaryMatrixGroup J) : C.Normal := by
  by_contra hnC
  obtain ⟨m,hm,D,_,_,hD,⟨f⟩⟩ := local_nonnormal_component_binary_at
    d h hab structural previous faithful earlier I hI C hC hnC
  let : Fintype D := Fintype.ofFinite D
  let : CharP D 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hD)
  obtain ⟨g,hg⟩ := HermitianForm.BinaryOrderFour.exists_order_four J hn hE hconj
  exact not_equiv_psl_of_order_four g hg ⟨f.symm.trans e⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
