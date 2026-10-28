module
public import CFSG.Quasithin.Chapter10.SourceA5ComponentNormalizer.StarRankReduction

/-!
# The low-cubic-rank part of the literal C.2.7 catalogue

The actual core-to-star map is an isomorphism when the containing component
has three-rank at most one. The concrete cubic ranks exclude all star rows
except binary SL₂ and SL₃; the alternating-five row is identified with SL₂(4).
No factor of five is required, so this applies to the binary-three branch
of the half-Sylow argument. The subsequent BinaryThree consumer excludes
both surviving rows using the original smaller quotient and full Sylow.

Source: Aschbacher--Smith C.2.7 and its use in 10.2.6,
printed pp.145--147 and 748--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter1.RadicalExclusions.ModelReduction FullSieve SourceInterface
open ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine ChapterC.C27Source
private def alternatingFiveLinearEquiv :
    alternatingGroup (Fin 5) ≃* SL(2,BinaryField.four.Carrier) :=
  (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K := BinaryField.four.Carrier) (by
      change Nat.card (GaloisField 2 2) = 4
      rw [GaloisField.card 2 2 (by decide)]
      decide)).some.symm.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm

private theorem low_cubic_star_model {A : Type*} [Group A] [Finite A]
    (h : StarModels.Model A) (hr : primeRank 3 A ≤ 1)
    (hz : center A = ⊥) :
    ∃ F : BinaryField, Nonempty (A ≃* SL(2,F.Carrier)) ∨ Nonempty (A ≃* SL(3,F.Carrier)) := by
  cases h with
  | linearTwo F e => exact ⟨F,Or.inl ⟨e⟩⟩
  | linearThree F e =>
    exact ⟨F,Or.inr ⟨e⟩⟩
  | symplectic F _ e =>
    have hl := (Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic (F := F.Carrier)).trans
      (Theory.GroupTheory.primeRank_le_of_injective 3 (commutator (Matrix.symplecticGroup (Fin 2) F.Carrier)).subtype Subtype.val_injective)
    rw [←primeRank_equiv 3 e] at hl
    omega
  | g2 F _ e =>
    have hl := (Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2 (F := F.Carrier)).trans
      (Theory.GroupTheory.primeRank_le_of_injective 3 (commutator (Atlas.G2.Model F.Carrier)).subtype Subtype.val_injective)
    rw [←primeRank_equiv 3 e] at hl
    omega
  | g2DerivedTwo e =>
    have hl := Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2 (F := ZMod 2)
    rw [←primeRank_equiv 3 e] at hl
    omega
  | alternating n hn e =>
    have hnlt : n < 6 := by
      by_contra! hh
      have hl := alternatingGroup.TwoThreeCycles.two_le_primeRank hh
      rw [←primeRank_equiv 3 e] at hl
      omega
    have hn5 : n = 5 := by rcases hn with hn | hn | hn | hn <;> omega
    subst n
    exact ⟨BinaryField.four,Or.inl ⟨e.trans alternatingFiveLinearEquiv⟩⟩
  | linearFiveTwo e =>
    have hl := Theory.SpecificGroups.Classical.BinaryLinearThreeRank.two_le_primeRank (by decide : 4 ≤ 5)
    rw [←primeRank_equiv 3 e] at hl
    omega
  | tripleSix e _ =>
    have hc : Nat.card (center A) = 3 := by
      rw [Nat.card_congr e.toEquiv]
      exact Nat.card_zmod 3
    rw [hz, card_bot] at hc
    omega


/-- Low cubic rank leaves only binary linear degree two or three in C.2.7. -/
theorem source_low_cubic_coreQuotient_linear
    {G : Type*} [Group G] [Finite G] {H K R M : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple H R M K) (hr : primeRank 3 K ≤ 1) :
    ∃ F : BinaryField,
      Nonempty ((K ⧸ pCore 2 K) ≃* SL(2,F.Carrier)) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* SL(3,F.Carrier)) := by
  let e := source_rank_one_coreToStar_equiv h hr
  have hrQ : primeRank 3 (K ⧸ pCore 2 K) ≤ 1 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 K) pCore_isPGroup).trans hr
  have hrS : primeRank 3 (starImage K R K) ≤ 1 := (primeRank_equiv 3 e) ▸ hrQ
  have hc : Nat.card (center (starImage K R K)) = 1 := by
    rw [←Nat.card_congr (centerCongr e).toEquiv,
      source_rank_one_coreQuotient_center h hr,card_bot]
  obtain ⟨F,hF⟩ := low_cubic_star_model (star_model_from_source h) hrS
    ((eq_bot_iff_card _).mpr hc)
  refine ⟨F,?_⟩
  rcases hF with hF | hF
  · obtain ⟨d⟩ := hF
    exact Or.inl ⟨e.trans d⟩
  · obtain ⟨d⟩ := hF
    exact Or.inr ⟨e.trans d⟩
end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
