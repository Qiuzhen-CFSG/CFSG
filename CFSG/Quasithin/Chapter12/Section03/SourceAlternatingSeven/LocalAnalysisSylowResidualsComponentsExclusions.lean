module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowResidualsComponents
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.TranspositionExclusion
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.ExceptionalSixExclusion

/-!
# Three excluded C.2.7 rows in every fixed-coset centralizer

The original Sylow subgroup normalizes both the containing component and
the common radical O₂(LT). The literal A₆ point residual lies in the
intersection with N(L). These facts apply the lower transposition and
exceptional-index exclusions uniformly over c in the fixed subgroup.

The component-or-enlargement alternative now rules out C.2.7(3)(b)--(d),
and its component branch feeds `six_residual_of_coset_components` with
the original centralizer and quotient maps. The other alternatives and
the source extraction remain obligations of this task; this module does
not construct `CosetComponents` from the setup.

Source: Aschbacher--Smith 3.3.22, p.597, and C.2.7, pp.145--147.
Final ambient-residual assembly: qt-d-1235-a7-sylow-ambient-residuals.
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

theorem coset_no_transposition_enlargement
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6))
    {c : G} (hc : c ∈ P.fixed) {K : Subgroup G} (hBK : P.sixGroup ≤ K)
    (h : Input KnownSimple.IsKnownSimple
      (centralizer ({c * (P.six : G)} : Set G))
      ((L ⊔ (T : Subgroup G)).pCoreIn 2)
      (centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)) K)
    (hK : centralizer ({c * (P.six : G)} : Set G) ≤ normalizer (K : Set G))
    {n : ℕ} (hn : 5 ≤ n) (hn' : n ≤ 8)
    (ha : TranspositionAction K ((L ⊔ (T : Subgroup G)).pCoreIn 2) n)
    (hm : starM K ((L ⊔ (T : Subgroup G)).pCoreIn 2)
        (centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)) =
      starImage K ((L ⊔ (T : Subgroup G)).pCoreIn 2) K ⊓
        centralizer (starImage K ((L ⊔ (T : Subgroup G)).pCoreIn 2)
          ((L ⊔ (T : Subgroup G)).pCoreIn 2) : Set _)) : False := by
  have hTR : (T : Subgroup G) ≤
      normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
    le_sup_right.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  exact ChapterC.C27Source.no_transposition_alternative_of_six h T
    ((P.coset_sylow_le hc).trans hK) hTR
    (le_inf (le_inf (P.sixGroup_le_coset_centralizer hc)
      ((pointResidual_le L (P.six : G)).trans (inf_le_left.trans L.le_normalizer))) hBK)
    e6 hn hn' ha hm

/-- The two exceptional C.2.7 rows are excluded on the literal coset intersection. -/
theorem coset_no_exceptional_enlargement
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6))
    {c : G} (hc : c ∈ P.fixed) {K : Subgroup G} (hBK : P.sixGroup ≤ K) :
    ¬ ((ChapterC.IsExceptionalAhat6Block K ∧
        (((centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)) ⊓ K).subgroupOf K).index = 15) ∨
      (ChapterC.IsExceptionalA7Block K ∧
        (((centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)) ⊓ K).subgroupOf K).index = 35)) := by
  have hB : P.sixGroup ≤
      (centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)) ⊓ K :=
    le_inf (le_inf (P.sixGroup_le_coset_centralizer hc)
      ((pointResidual_le L (P.six : G)).trans (inf_le_left.trans L.le_normalizer))) hBK
  rintro (⟨hm,hi⟩ | ⟨hm,hi⟩)
  · exact ChapterC.C27Source.no_ahatSix_alternative_of_six hB e6 hm hi
  · exact ChapterC.C27Source.no_exceptionalSeven_alternative_of_six hB e6 hm hi

/-- An actual enlargement still has to satisfy C.2.7, but its complete
transposition and exceptional rows are excluded by the inherited Sylow
and A6 quotient. -/
theorem coset_components_or_C27_enlargement_without_three_rows
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (M : P.Models)
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
  rcases P.coset_components_or_C27_enlargement structural M e6 with hc | ⟨c,hc,K,hBK,h,hK,hB⟩
  · exact Or.inl hc
  · refine Or.inr ⟨c,hc,K,hBK,h,hK,hB,P.coset_no_exceptional_enlargement e6 hc hBK.le,?_⟩
    rintro ⟨n,hn,hn',ha,hm⟩
    exact P.coset_no_transposition_enlargement e6 hc hBK.le h hK hn hn' ha hm

/-- The literal A.3.18 consumer retains only enlargements outside the three
excluded rows. This is still a reduction, not the full component theorem. -/
theorem six_residuals_or_C27_enlargement_without_three_rows
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (M : P.Models)
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
  rcases P.coset_components_or_C27_enlargement_without_three_rows structural M e6 with h | h
  · exact Or.inl (fun _ hc => P.six_residual_of_coset_components h e6 hc)
  · exact Or.inr h

end SylowNormalizer.Points
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
