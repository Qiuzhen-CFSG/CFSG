module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication.Intrinsic
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication.PlusComparison

/-!
# The intrinsic-to-plus central quotient comparison

The rank-two A.3.6 deduction supplies intrinsic quasisimplicity, and the
earlier R₂ condition kills O₂(K) in the actual plus action. The resulting
surjection compares central quotients and commutes with representatives
from K. No abstract replacement for the plus quotient is used.

The comparison with the image in KLᵥ/O₃′(KLᵥ) uses
the C-component placement constructed in Localization. This module supplies the
other half of that comparison, with all of its hypotheses discharged
except the named universal A.3.6 and earlier R₂ source inputs.
Source: Aschbacher–Smith, combined manuscript, pp.929–931 and A.3.18,
pp.51–53.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication
open ComponentSelection Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
    (hG : IsSimpleQTKE κ G)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D], IsSQTK κ D → pCore 2 D = ⊥ →
      ∀ B : Subgroup D, B.IsCComponent → A36Conclusion B)
    (K L T : Subgroup G) (z v : G) (hv : orderOf v = 2) (hK : K ∈ Yz L T z v)
    (hr : primeRank 3 K = 2)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)

/-- The local source inputs produce the central quotient comparison. -/
noncomputable def intrinsicPlusCentralQuotientEquiv :
    ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃*
      (plusImage K L T z v hL hz K ⧸ center (plusImage K L T z v hL hz K)) := by
  let := (source_intrinsic_quasisimple hG hA36 K L T z v hv hK hr).1
  let : Nontrivial (plusImage K L T z v hL hz K) :=
    (nontrivial_iff_ne_bot _).mpr (plusImage_ne_bot_of_mem_Yz K L T z v hL hz hK)
  exact IsQuasisimple.centralQuotientEquiv
    (intrinsicTwoCoreToPlus K L T z v hL hz hK hR)
    (intrinsicTwoCoreToPlus_surjective K L T z v hL hz hK hR)

/-- Compatibility with K → K* → K+ on every element of the original K. -/
theorem intrinsicPlusCentralQuotientEquiv_mk (k : K) :
    intrinsicPlusCentralQuotientEquiv hG hA36 K L T z v hv hK hr hL hz hR
      (QuotientGroup.mk' (center (K ⧸ pCore 2 K)) (QuotientGroup.mk' (pCore 2 K) k)) =
      QuotientGroup.mk' (center (plusImage K L T z v hL hz K))
        (toPlusImage K L T z v hK.1.1 hL hz k) := rfl

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication
