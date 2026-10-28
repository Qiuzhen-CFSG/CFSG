module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearOddControl
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSymplecticHall

/-!
# Faithfulness of the original nonbinary linear-three Hall action

The actual odd-normalizer theorem excludes the elementary odd kernel
constructed by the original H-star Hall argument. Thus every prescribed
odd Hall acts faithfully on the literal L/O₂(L) section, and the original
generation parameter is bounded by that quotient action's Cartan parameter.
No Hall faithfulness, placement, or normalizer hypothesis is supplied by
the caller. The numerical Cartan and whole-orbit fixed-space bounds remain
separate source duties.
Source: Aschbacher--Smith 4.4.13--14 and 7.3.4, pp.623--625,699.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource ChapterE
open ChapterE.Section06.FixedPointBounds ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Chapter7.NormalizedSource.MathieuGeneration
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem no_hall_kernel_actor
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (A : Subgroup G)
    (hA : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAC : A ≤ centralizer (D.sourceOrbit : Set G)) :
    normalizer (A : Set G) ≤ normalizer (L : Set G) := by
  let : Fact p.Prime := ⟨hp⟩
  let := hAe
  have hodd : Odd (Nat.card A) := by
    obtain ⟨n,he⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [he]
    exact ho.pow
  exact D.sourceOrbit_linear_oddNormalizer_le h hd F hn hmodel A hA hAC hodd

/-- Every original odd Hall has trivial literal section-action kernel. -/
theorem sourceOrbit_linear_hall_faithful
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < generationParameter H)
    (B : Subgroup H) (hBN : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H))) :
    B.map H.subtype ⊓ Chapter4.sectionCentralizer L = ⊥ := by
  by_contra hk
  obtain ⟨p,A,hp,ho,hA,hAe,_,_,hAC,_,hout⟩ :=
    D.sourceOrbit_whole_nonfaithful_hall_escaping_actor h hmany hnon hH hlarge
      B hBN hHall hk
  exact hout (D.no_hall_kernel_actor h hd F hn hmodel hp ho A hA hAe hAC)

/-- The original H-star generation parameter is bounded by the actual quotient action. -/
theorem sourceOrbit_linear_generation_le_quotient_nPrime
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < generationParameter H) :
    generationParameter H ≤ nPrime (normalizerPCoreQuotientAction L).range := by
  apply (D.sourceOrbit_whole_generation_or_odd_escape h hmany hnon hH hlarge).resolve_right
  rintro ⟨p,A,hp,ho,hA,hAe,_,_,hAC,_,hout⟩
  exact hout (D.no_hall_kernel_actor h hd F hn hmodel hp ho A hA hAe hAC)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
