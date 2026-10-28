module
public import CFSG.Quasithin.Chapter4.Section03.A5.SourceSetup
public import CFSG.Quasithin.ChapterA.Section04.Intersection
/-!
# The reciprocal source configuration in the index-two branch

If the original outside maximal two-local H has its quotient generalized
Fitting preimage inside M, A.4.4 identifies O₂(H) with O₂(H∩M), controls
its relative characteristic normalizers in M, and forces the reciprocal
preimage of M to escape H. These are the original preparations for reversing
H and M in the proof of 4.2.5; they do not assume a model classification or
that the first preimage escapes. The A₅ application retains M=N_G(L).

Source: Aschbacher–Smith 4.2.5–9, printed pp.609–610, using A.4.4, p.58.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.A5
open ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]

/-- Both original cores and the reciprocal preimage escape from A.4.4. -/
theorem reciprocal_core_data {H M : Subgroup G}
    (hH : IsMaximalTwoLocal H) (hM : IsMaximalTwoLocal M) (hne : H ≠ M)
    (hpre : twoGeneralizedFittingPreimage H ≤ M) :
    H.pCoreIn 2 = (H ⊓ M).pCoreIn 2 ∧
      characteristicNormalizerIn M (H.pCoreIn 2) ≤ H ⊓ M ∧
      ¬ twoGeneralizedFittingPreimage M ≤ H := by
  have hXL : twoGeneralizedFittingPreimage H ≤ H ⊓ M :=
    le_inf (map_subtype_le _) hpre
  have hX : IntersectionAlternative
      (twoCoreQuotientImage H (twoGeneralizedFittingPreimage H)) := by
    rw [twoCoreQuotientImage_fittingPreimage]
    refine Or.inr ⟨le_rfl, ?_, ?_⟩
    · exact (inferInstance : ((generalizedFitting (H ⧸ pCore 2 H)).subgroupOf
        (generalizedFitting (H ⧸ pCore 2 H))).Normal).isSubnormal
    · apply (closure_le _).mpr
      intro x hx
      exact hx.1.1
  have hc := lemma_A_4_4_1 H M _ (twoCore_le_fittingPreimage H) hXL hX
  refine ⟨hc, ?_, ?_⟩
  · rw [hc]
    exact lemma_A_4_4_2 H M _ (twoCore_le_fittingPreimage H) hXL hX hH
  · intro hm
    exact hne (lemma_A_4_4_3 H M _ (twoCore_le_fittingPreimage H) hXL hX hH hM hm)
end CFSG.Quasithin.Chapter4.Section03.A5

namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
open ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

/-- The literal A₅ source uses the genuine maximal local N(L). -/
theorem source_reciprocal_core_data {H : Subgroup G}
    (hH : IsMaximalTwoLocal H) (hout : ¬ H ≤ normalizer (L : Set G))
    (hpre : twoGeneralizedFittingPreimage H ≤ normalizer (L : Set G)) :
    H.pCoreIn 2 = (H ⊓ normalizer (L : Set G)).pCoreIn 2 ∧
      characteristicNormalizerIn (normalizer (L : Set G)) (H.pCoreIn 2) ≤
        H ⊓ normalizer (L : Set G) ∧
      ¬ twoGeneralizedFittingPreimage (normalizer (L : Set G)) ≤ H :=
  Chapter4.Section03.A5.reciprocal_core_data hH d.normalizer_maximal_twoLocal
    (fun he => hout he.le) hpre
end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
