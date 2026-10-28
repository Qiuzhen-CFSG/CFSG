module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowResidualsComponentsExclusions
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.ParabolicSixExclusion

/-!
# Reducing fixed-coset C.2.7 enlargement to the binary-linear row

The six-point residual lies in the literal intersection of the containing
component with the local normalizer. Its A₆ quotient excludes the χ,
transposition, exceptional, rank-two parabolic, binary G₂, and linear-three
rows. The rank-two and linear-three cases use the perfect image in the
actual star intersection; the degree-eight transposition case retains the
original Sylow subgroup and the common radical O₂(LT).

The resulting reduction feeds `six_residual_of_coset_components`. The
source extraction and binary-linear parabolic exclusion remain open:
no universal C.2.7 source premise or full `CosetComponents` constructor
is asserted here. Final ambient-residual assembly belongs to
qt-d-1235-a7-sylow-ambient-residuals.

Source: Aschbacher–Smith C.2.7, printed pp.145–147, and 3.3.22, p.597.
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

/-- On the original coset centralizer, all seven non-binary-linear C.2.7
alternatives contradict the actual A₆ residual. The C.2.7 alternative is
an explicit premise here; this does not assert its source extraction. -/
theorem coset_C27_alternatives_reduce_to_binaryLinear
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6))
    {c : G} (hc : c ∈ P.fixed) {K : Subgroup G} (hBK : P.sixGroup ≤ K)
    (h : Input KnownSimple.IsKnownSimple
      (centralizer ({c * (P.six : G)} : Set G))
      ((L ⊔ (T : Subgroup G)).pCoreIn 2)
      (centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)) K)
    (hK : centralizer ({c * (P.six : G)} : Set G) ≤ normalizer (K : Set G))
    (ha : Alternatives KnownSimple.IsKnownSimple
      (centralizer ({c * (P.six : G)} : Set G)) K
      ((L ⊔ (T : Subgroup G)).pCoreIn 2)
      (centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G))) :
    ∃ n, (n = 4 ∨ n = 5) ∧ IsBinaryPositiveRankParabolic
      ((starM K ((L ⊔ (T : Subgroup G)).pCoreIn 2)
        (centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G))).subgroupOf
          (starImage K ((L ⊔ (T : Subgroup G)).pCoreIn 2) K)) n := by
  have hB : P.sixGroup ≤
      (centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)) ⊓ K :=
    le_inf (le_inf (P.sixGroup_le_coset_centralizer hc)
      ((pointResidual_le L (P.six : G)).trans (inf_le_left.trans L.le_normalizer))) hBK
  cases ha with
  | chi _ _ ha =>
    exact (ChapterC.C27Source.no_chi_alternative_of_six h hB e6 ha).elim
  | alternating n hn hn' _ _ ha hm =>
    exact (P.coset_no_transposition_enlargement e6 hc hBK h hK hn hn' ha hm).elim
  | ahatSix _ hm hi _ =>
    exact (ChapterC.C27Source.no_ahatSix_alternative_of_six hB e6 hm hi).elim
  | exceptionalSeven _ hm hi =>
    exact (ChapterC.C27Source.no_exceptionalSeven_alternative_of_six hB e6 hm hi).elim
  | rankTwo _ ha =>
    rcases ha with ⟨_,hp⟩ | ⟨_,hp⟩
    · exact (ChapterC.C27Source.no_six_parabolic_of_six h hB e6 hp).elim
    · exact (ChapterC.C27Source.no_sp4_parabolic_of_six h hB e6 hp).elim
  | binaryG2 _ hm _ =>
    exact (ChapterC.C27Source.no_binaryG2_containing_six hBK e6 hm).elim
  | linearThree n F hn hF hp _ =>
    exact (ChapterC.C27Source.no_linearThree_parabolic_of_six h hB e6 F hn hF hp).elim
  | binaryLinear n hn hp => exact ⟨n,hn,hp⟩

/-- A proper containing component retains the literal C.2.7 input and the
proved reduction of its alternatives to the binary-linear parabolic row.
The source extraction and exclusion of that last row remain to be proved. -/
theorem coset_components_or_C27_binaryLinear_remainder
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (M : P.Models)
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
  rcases P.coset_components_or_C27_enlargement structural M e6 with h | ⟨c,hc,K,hBK,h,hK,hB⟩
  · exact Or.inl h
  · exact Or.inr ⟨c,hc,K,hBK,h,hK,hB,
      P.coset_C27_alternatives_reduce_to_binaryLinear e6 hc hBK.le h hK⟩

/-- The exact prime-to-three residual consumer, after excluding C.2.7(a)–(g).
The remaining branch records a conditional reduction, not an extraction
of the source alternatives. -/
theorem six_residuals_or_C27_binaryLinear_remainder
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (M : P.Models)
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
  rcases P.coset_components_or_C27_binaryLinear_remainder structural M e6 with h | h
  · exact Or.inl (fun _ hc => P.six_residual_of_coset_components h e6 hc)
  · exact Or.inr h

end SylowNormalizer.Points
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
