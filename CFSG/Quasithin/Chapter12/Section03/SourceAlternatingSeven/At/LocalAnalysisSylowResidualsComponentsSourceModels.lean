module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowResidualsComponentsSourceModels
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisSylowResidualsComponentsBinaryLinear

/-!
# LocalAnalysisSylowResidualsComponentsSourceModels at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisSylowResidualsComponentsSourceModels`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

public noncomputable section

open Subgroup Theory.GroupTheory

open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode

open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface

open ChapterC.C27Source

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

variable {E : S.NaturalCoordinates}

namespace SylowNormalizer.Points

variable (P : Points E)

theorem coset_no_source_enlargement_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6))
    {c : G} (hc : c ∈ P.fixed) {K : Subgroup G} (hBK : P.sixGroup ≤ K)
    (h : Input KnownSimple.IsKnownSimple
      (centralizer ({c * (P.six : G)} : Set G))
      ((L ⊔ (T : Subgroup G)).pCoreIn 2)
      (centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)) K)
    (hK : centralizer ({c * (P.six : G)} : Set G) ≤ normalizer (K : Set G)) : False := by
  let R := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let N := centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)
  have hB : P.sixGroup ≤ N ⊓ K := le_inf
    (le_inf (P.sixGroup_le_coset_centralizer hc)
      ((pointResidual_le L (P.six : G)).trans (inf_le_left.trans L.le_normalizer))) hBK
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) := (P.coset_sylow_le hc).trans hK
  have hTN : (T : Subgroup G) ≤ N := le_inf (P.coset_sylow_le hc)
    (S.hypothesis.source_sylow_normalizes_at structural)
  have hLR : L ⊔ (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) := le_sup_right.trans hLR
  have hBR : P.sixGroup ≤ normalizer (R : Set G) :=
    (pointResidual_le L (P.six : G)).trans (inf_le_left.trans (le_sup_left.trans hLR))
  have hF {F : ChapterB.QuasisimpleSource.BinaryField} (large : 1 < F.degree) :
      2 < Nat.card F.Carrier := by
    rw [F.card_eq]
    exact lt_of_lt_of_le (by decide : 2 < 2^2)
      (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega))
  cases star_model_from_source h with
  | linearTwo F e => exact no_linearTwo_star_of_six h hB e6 e
  | linearThree F e => exact no_linearThree_star_of_six h hB e6 T hTK hTN F e
  | symplectic F large e => exact no_symplectic_star_of_six h hB e6 T hTK hTN (hF large) e
  | g2 F large e => exact no_g2_star_of_six h hB e6 T hTK hTN (hF large) e
  | g2DerivedTwo e => exact no_binaryG2_star_of_six h hB e6 e
  | alternating n hn e =>
    rcases hn with hn | hn | hn | hn
    · exact no_small_alternating_star_of_six h hB e6 (Or.inl hn) e
    · exact no_small_alternating_star_of_six h hB e6 (Or.inr hn) e
    · exact no_large_alternating_star_of_six h hB e6 hBR T hTK hTR (Or.inl hn) e
    · exact no_large_alternating_star_of_six h hB e6 hBR T hTK hTR (Or.inr hn) e
  | linearFiveTwo e => exact P.coset_no_linearFive_star_at structural e6 hc hBK h hK e
  | tripleSix _ e => exact no_tripleSix_star_of_six h hB e6 e

theorem cosetComponents_of_source_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (M : P.Models)
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6)) :
    P.CosetComponents := by
  rcases P.coset_components_or_C27_enlargement_at structural M e6 with hc | ⟨c,hc,K,hBK,h,hK,_⟩
  · exact hc
  · exact (P.coset_no_source_enlargement_at structural e6 hc hBK.le h hK).elim

theorem six_residuals_of_source_components_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (M : P.Models)
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6)) :
    ∀ c ∈ P.fixed, pointThreeResidual (c * (P.six : G)) = P.sixGroup :=
  fun _ hc => P.six_residual_of_coset_components (P.cosetComponents_of_source_at structural M e6) e6 hc

end SylowNormalizer.Points

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

