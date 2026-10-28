module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationEqualityExtensionTransferGeometry
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityComplete

/-!
# Equality recognition on the whole reduced subgroup

Apply the complete equality branch to the literal wholeReduced and
commutatorLayer of the Chapter12 reduction. The source hypotheses and
earlier LocalAnalysis are preserved; no extra fusion, quotient, core or
recognition premise remains. The final identification owner supplies the
earlier local analysis and assembles the strict branch separately.

Source: Aschbacher–Smith, 6.2.13 and 12.2.2(3d), printed pp.686–688,795.
-/

open Subgroup Theory.GroupTheory
public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G} {n : ℕ} {z : G}

/-- The whole-reduced equality configuration has no remaining fusion or recognition premise. -/
theorem reduced_m22_of_local_analysis_of_equality
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓ commutatorLayer T L =
      ZS (T : Subgroup G) L (wholeReduced T L)) :
    Nonempty (G ≃* Sporadic.Mathieu.M22) :=
  m22_of_local_analysis_of_intersection_eq A h611 hnatural hz horder hTH hbranch

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
