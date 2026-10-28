module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowResidualsComponentsExclusions
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisSylowResidualsComponents

/-!
# LocalAnalysisSylowResidualsComponentsExclusions at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisSylowResidualsComponentsExclusions`, with structural
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

theorem coset_components_or_C27_enlargement_without_three_rows_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (M : P.Models)
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6)) :
    P.CosetComponents ∨ ∃ c ∈ P.fixed, ∃ K : Subgroup G,
      P.sixGroup < K ∧
      Input KnownSimple.IsKnownSimple
        (centralizer ({c * (P.six : G)} : Set G))
        ((L ⊔ (T : Subgroup G)).pCoreIn 2)
        (centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)) K ∧
      centralizer ({c * (P.six : G)} : Set G) ≤ normalizer (K : Set G) ∧
      (P.sixGroup.subgroupOf (normalizer (L : Set G) ⊓ K)).IsCComponent ∧
      (¬ ((ChapterC.IsExceptionalAhat6Block K ∧
          (((centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)) ⊓ K).subgroupOf K).index = 15) ∨
        (ChapterC.IsExceptionalA7Block K ∧
          (((centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)) ⊓ K).subgroupOf K).index = 35))) ∧
      ¬ ∃ n, 5 ≤ n ∧ n ≤ 8 ∧
        TranspositionAction K ((L ⊔ (T : Subgroup G)).pCoreIn 2) n ∧
        starM K ((L ⊔ (T : Subgroup G)).pCoreIn 2)
            (centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)) =
          starImage K ((L ⊔ (T : Subgroup G)).pCoreIn 2) K ⊓
            centralizer (starImage K ((L ⊔ (T : Subgroup G)).pCoreIn 2)
              ((L ⊔ (T : Subgroup G)).pCoreIn 2) : Set _) := by
  rcases P.coset_components_or_C27_enlargement_at structural M e6 with hc | ⟨c,hc,K,hBK,h,hK,hB⟩
  · exact Or.inl hc
  · refine Or.inr ⟨c,hc,K,hBK,h,hK,hB,P.coset_no_exceptional_enlargement e6 hc hBK.le,?_⟩
    rintro ⟨n,hn,hn',ha,hm⟩
    exact P.coset_no_transposition_enlargement e6 hc hBK.le h hK hn hn' ha hm

theorem six_residuals_or_C27_enlargement_without_three_rows_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (M : P.Models)
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6)) :
    (∀ c ∈ P.fixed, pointThreeResidual (c * (P.six : G)) = P.sixGroup) ∨ ∃ c ∈ P.fixed, ∃ K : Subgroup G,
      P.sixGroup < K ∧
      Input KnownSimple.IsKnownSimple
        (centralizer ({c * (P.six : G)} : Set G))
        ((L ⊔ (T : Subgroup G)).pCoreIn 2)
        (centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)) K ∧
      centralizer ({c * (P.six : G)} : Set G) ≤ normalizer (K : Set G) ∧
      (P.sixGroup.subgroupOf (normalizer (L : Set G) ⊓ K)).IsCComponent ∧
      (¬ ((ChapterC.IsExceptionalAhat6Block K ∧
          (((centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)) ⊓ K).subgroupOf K).index = 15) ∨
        (ChapterC.IsExceptionalA7Block K ∧
          (((centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)) ⊓ K).subgroupOf K).index = 35))) ∧
      ¬ ∃ n, 5 ≤ n ∧ n ≤ 8 ∧
        TranspositionAction K ((L ⊔ (T : Subgroup G)).pCoreIn 2) n ∧
        starM K ((L ⊔ (T : Subgroup G)).pCoreIn 2)
            (centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)) =
          starImage K ((L ⊔ (T : Subgroup G)).pCoreIn 2) K ⊓
            centralizer (starImage K ((L ⊔ (T : Subgroup G)).pCoreIn 2)
              ((L ⊔ (T : Subgroup G)).pCoreIn 2) : Set _) := by
  rcases P.coset_components_or_C27_enlargement_without_three_rows_at structural M e6 with h | h
  · exact Or.inl (fun _ hc => P.six_residual_of_coset_components h e6 hc)
  · exact Or.inr h

end SylowNormalizer.Points

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

