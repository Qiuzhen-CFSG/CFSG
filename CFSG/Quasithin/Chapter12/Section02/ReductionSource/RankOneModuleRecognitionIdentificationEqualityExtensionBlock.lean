module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationEqualityExtensionCentralizerBound
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionBlock

/-!
# The equality block on the whole reduced subgroup

The source layer is O₂(L), and the complete block contract is constructed
with the original whole reduced subgroup and the same marked quotient.
This discharges the block premise of the equality extension assembly;
the centralizer extension and elementary-four transfer remain with the
source 6.2.13 equality owner.

Source: Aschbacher–Smith, 6.2.13 and 12.2.2(3d), pp.687–688,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G} {n : ℕ} {z : G}

/-- The literal Chapter 12 setup supplies the entire block contract. -/
theorem reduced_equality_extension_block
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (hbranch : sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓
      commutatorLayer T L = ZS (T : Subgroup G) L (wholeReduced T L)) :
    EqualityExtensionBlock (T : Subgroup G) L (normalizer (L : Set G))
      (wholeReduced T L) z := by
  exact A.equality_extension_block h611 hnatural hz horder hTH hbranch

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
