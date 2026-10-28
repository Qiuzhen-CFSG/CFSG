module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowResidualsComponentsRemaining
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.BinaryLinearSixExclusion

/-!
# All fixed-coset C.2.7 enlargement alternatives are excluded

The last binary-linear row uses the actual normal six-point residual in
M ∩ K. Its image cannot be normal in the endpoint parabolic's A₈ Levi
quotient. Together with the earlier seven exclusions, this rules out all
eight C.2.7 alternatives uniformly over c in the fixed subgroup.

The SL₅(2) star model is also excluded directly from the original Sylow
intersection: the proved Sylow-overgroup theorem supplies its flag. The
component branch feeds the literal `six_residual_of_coset_components`
consumer. Derivation of the remaining source alternatives is still needed
before constructing `CosetComponents`; no universal C.2.7 source premise
is used here. Final ambient-residual assembly remains with
qt-d-1235-a7-sylow-ambient-residuals.

Source: Aschbacher–Smith C.2.7, printed pp.145–147, and 3.3.22, p.597.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}
variable {E : S.NaturalCoordinates}
namespace SylowNormalizer.Points
variable (P : Points E)

/-- The inherited Sylow subgroup constructs the flag and excludes the
SL₅(2) star model before the full C.2.7 alternative extraction. -/
theorem coset_no_linearFive_star
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6))
    {c : G} (hc : c ∈ P.fixed) {K : Subgroup G} (hBK : P.sixGroup ≤ K)
    (h : Input KnownSimple.IsKnownSimple
      (centralizer ({c * (P.six : G)} : Set G))
      ((L ⊔ (T : Subgroup G)).pCoreIn 2)
      (centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)) K)
    (hK : centralizer ({c * (P.six : G)} : Set G) ≤ normalizer (K : Set G))
    (e5 : starImage K ((L ⊔ (T : Subgroup G)).pCoreIn 2) K ≃* SL(5,ZMod 2)) : False := by
  apply ChapterC.C27Source.no_linearFive_star_of_normal_six h _ _ e6 T
    ((P.coset_sylow_le hc).trans hK)
    (le_inf (P.coset_sylow_le hc) (S.hypothesis.source_sylow_normalizes structural)) e5
  · exact le_inf (le_inf (P.sixGroup_le_coset_centralizer hc)
      ((pointResidual_le L (P.six : G)).trans (inf_le_left.trans L.le_normalizer))) hBK
  · exact inf_le_left.trans (P.coset_local_normalizes hc)

/-- The binary-linear row is impossible on the literal fixed coset. The
six-point residual is normal in the local intersection, and its image
cannot be normal in the endpoint A₈ Levi quotient. -/
theorem coset_no_binaryLinear_enlargement
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6))
    {c : G} (hc : c ∈ P.fixed) {K : Subgroup G} (hBK : P.sixGroup ≤ K)
    (h : Input KnownSimple.IsKnownSimple
      (centralizer ({c * (P.six : G)} : Set G))
      ((L ⊔ (T : Subgroup G)).pCoreIn 2)
      (centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)) K)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hp : IsBinaryPositiveRankParabolic
      ((starM K ((L ⊔ (T : Subgroup G)).pCoreIn 2)
        (centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G))).subgroupOf
          (starImage K ((L ⊔ (T : Subgroup G)).pCoreIn 2) K)) n) : False := by
  apply ChapterC.C27Source.no_binaryLinear_parabolic_of_normal_six h _ _ e6 hn hp
  · exact le_inf (le_inf (P.sixGroup_le_coset_centralizer hc)
      ((pointResidual_le L (P.six : G)).trans (inf_le_left.trans L.le_normalizer))) hBK
  · exact inf_le_left.trans (P.coset_local_normalizes hc)

/-- All eight source alternatives contradict a containing component of the
fixed-coset centralizer. This is the exclusion step, with source extraction
still a separate mathematical obligation. -/
theorem coset_no_C27_alternatives
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6))
    {c : G} (hc : c ∈ P.fixed) {K : Subgroup G} (hBK : P.sixGroup ≤ K)
    (h : Input KnownSimple.IsKnownSimple
      (centralizer ({c * (P.six : G)} : Set G))
      ((L ⊔ (T : Subgroup G)).pCoreIn 2)
      (centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)) K)
    (hK : centralizer ({c * (P.six : G)} : Set G) ≤ normalizer (K : Set G)) :
    ¬ Alternatives KnownSimple.IsKnownSimple
      (centralizer ({c * (P.six : G)} : Set G)) K
      ((L ⊔ (T : Subgroup G)).pCoreIn 2)
      (centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)) := by
  intro ha
  obtain ⟨n,hn,hp⟩ := P.coset_C27_alternatives_reduce_to_binaryLinear e6 hc hBK h hK ha
  exact P.coset_no_binaryLinear_enlargement e6 hc hBK h hn hp

/-- Every possible proper enlargement now violates the C.2.7 alternatives.
The input retains R = O₂(LT), the normal container and the actual local
component; deriving those alternatives remains necessary for completion. -/
theorem coset_components_or_C27_source_failure
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (M : P.Models)
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6)) :
    P.CosetComponents ∨ ∃ c ∈ P.fixed, ∃ K : Subgroup G,
      let H := centralizer ({c * (P.six : G)} : Set G)
      let R := (L ⊔ (T : Subgroup G)).pCoreIn 2
      let N := H ⊓ normalizer (L : Set G)
      P.sixGroup < K ∧ Input KnownSimple.IsKnownSimple H R N K ∧
      H ≤ normalizer (K : Set G) ∧
      (P.sixGroup.subgroupOf (normalizer (L : Set G) ⊓ K)).IsCComponent ∧
      (¬ Alternatives KnownSimple.IsKnownSimple H K R N) ∧
      ¬ Nonempty (starImage K R K ≃* SL(5,ZMod 2)) := by
  rcases P.coset_components_or_C27_enlargement structural M e6 with h | ⟨c,hc,K,hBK,h,hK,hB⟩
  · exact Or.inl h
  · exact Or.inr ⟨c,hc,K,hBK,h,hK,hB,P.coset_no_C27_alternatives e6 hc hBK.le h hK,
      fun ⟨e5⟩ => P.coset_no_linearFive_star structural e6 hc hBK.le h hK e5⟩

/-- Apply the completed exclusion reduction to the exact ambient residual
consumer. The second branch records precisely the remaining source step. -/
theorem six_residuals_or_C27_source_failure
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (M : P.Models)
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6)) :
    (∀ c ∈ P.fixed, pointThreeResidual (c * (P.six : G)) = P.sixGroup) ∨
      ∃ c ∈ P.fixed, ∃ K : Subgroup G,
        let H := centralizer ({c * (P.six : G)} : Set G)
        let R := (L ⊔ (T : Subgroup G)).pCoreIn 2
        let N := H ⊓ normalizer (L : Set G)
        P.sixGroup < K ∧ Input KnownSimple.IsKnownSimple H R N K ∧
        H ≤ normalizer (K : Set G) ∧
        (P.sixGroup.subgroupOf (normalizer (L : Set G) ⊓ K)).IsCComponent ∧
        (¬ Alternatives KnownSimple.IsKnownSimple H K R N) ∧
        ¬ Nonempty (starImage K R K ≃* SL(5,ZMod 2)) := by
  rcases P.coset_components_or_C27_source_failure structural M e6 with h | h
  · exact Or.inl (fun _ hc => P.six_residual_of_coset_components h e6 hc)
  · exact Or.inr h

end SylowNormalizer.Points
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
