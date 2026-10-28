module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationEqualityExtensionCentralizerBound
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionQuotient

/-!
# The equality centralizer quotient for Chapter 12

The literal canonical kernel P C_H(K) has quotient S₃×C₂, constructed
from the marked local S₅ quotient and the actual normal S₃ image.
Both centralizer-order alternatives remain, and the source assembly
still owns the cubic centralizer and elementary-four transfer.
Source: Aschbacher–Smith, 6.2.13 and 12.2.2(3d), pp.687–688,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G} {n : ℕ} {z : G}

/-- The extension quotient uses the original whole reduced subgroup. -/
theorem reduced_equality_extension_quotient
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (hbranch : sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓
      commutatorLayer T L = ZS (T : Subgroup G) L (wholeReduced T L)) :
    Nonempty (((centralizer ({z} : Set G)) ⧸
      (equalityCore L (wholeReduced T L) z ⊔ centralizer
        (equalityLayerClosure L (wholeReduced T L) z :
          Set (centralizer ({z} : Set G))))) ≃*
      (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2))) := by
  exact A.equality_extension_quotient h611 hnatural hz horder hTH hbranch

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
