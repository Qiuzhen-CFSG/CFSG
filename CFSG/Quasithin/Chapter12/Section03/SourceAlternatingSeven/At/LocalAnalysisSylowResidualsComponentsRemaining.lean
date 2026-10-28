module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowResidualsComponentsRemaining
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisSylowResidualsComponentsExclusions

/-!
# LocalAnalysisSylowResidualsComponentsRemaining at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisSylowResidualsComponentsRemaining`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

public noncomputable section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode

open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

variable {E : S.NaturalCoordinates}

namespace SylowNormalizer.Points

variable (P : Points E)

theorem coset_components_or_C27_binaryLinear_remainder_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (M : P.Models)
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6)) :
    P.CosetComponents ∨ ∃ c ∈ P.fixed, ∃ K : Subgroup G,
      let H := centralizer ({c * (P.six : G)} : Set G)
      let R := (L ⊔ (T : Subgroup G)).pCoreIn 2
      let N := H ⊓ normalizer (L : Set G)
      P.sixGroup < K ∧
      Input KnownSimple.IsKnownSimple H R N K ∧
      H ≤ normalizer (K : Set G) ∧
      (P.sixGroup.subgroupOf (normalizer (L : Set G) ⊓ K)).IsCComponent ∧
      (Alternatives KnownSimple.IsKnownSimple H K R N →
        ∃ n, (n = 4 ∨ n = 5) ∧ IsBinaryPositiveRankParabolic
          ((starM K R N).subgroupOf (starImage K R K)) n) := by
  rcases P.coset_components_or_C27_enlargement_at structural M e6 with h | ⟨c,hc,K,hBK,h,hK,hB⟩
  · exact Or.inl h
  · exact Or.inr ⟨c,hc,K,hBK,h,hK,hB,
      P.coset_C27_alternatives_reduce_to_binaryLinear e6 hc hBK.le h hK⟩

theorem six_residuals_or_C27_binaryLinear_remainder_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (M : P.Models)
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6)) :
    (∀ c ∈ P.fixed, pointThreeResidual (c * (P.six : G)) = P.sixGroup) ∨
      ∃ c ∈ P.fixed, ∃ K : Subgroup G,
        let H := centralizer ({c * (P.six : G)} : Set G)
        let R := (L ⊔ (T : Subgroup G)).pCoreIn 2
        let N := H ⊓ normalizer (L : Set G)
        P.sixGroup < K ∧
        Input KnownSimple.IsKnownSimple H R N K ∧
        H ≤ normalizer (K : Set G) ∧
        (P.sixGroup.subgroupOf (normalizer (L : Set G) ⊓ K)).IsCComponent ∧
        (Alternatives KnownSimple.IsKnownSimple H K R N →
          ∃ n, (n = 4 ∨ n = 5) ∧ IsBinaryPositiveRankParabolic
            ((starM K R N).subgroupOf (starImage K R K)) n) := by
  rcases P.coset_components_or_C27_binaryLinear_remainder_at structural M e6 with h | h
  · exact Or.inl (fun _ hc => P.six_residual_of_coset_components h e6 hc)
  · exact Or.inr h

end SylowNormalizer.Points

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

