module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Components.CenterPrime
public import Theory.GroupTheory.PerfectCenterPrimeRank
public import Theory.GroupTheory.PerfectCentralCoverPrimeRank
public import Theory.Quasithin.CubicIntersectionLocalTwoRank

/-!
# Ordinary and local ranks of the centered source components

A nontrivial component center is cubic by the actual covering list. Central
transfer forces ordinary three-rank at least two, while the distinct-component
normalizer bounds give the opposite inequality. Perfect central-cover transfer
also gives exact rank two in the central quotient.

For two such components, their intersection has order at most three. If one
had local three-rank at least two, their commuting product would contain an
actual two-local of rank at least three. Thus both centered components have
local three-rank at most one. The remaining model sieve identifies which
actual components can have this local rank.

Source: Aschbacher–Smith A.2.12(I)–(II), printed pp.36–37.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {G S : Type u} [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

theorem CounterexampleToTheoremA.component_center_card_three
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hsemi : IsSemisimple G) (hn : ¬ IsQuasisimple G)
    (hcovers : SQTKStructure.OrdinarySource.RemainingOddCoverInputs.{u})
    {C : Subgroup G} (hC : IsComponent G C) (hz : center C ≠ ⊥) :
    Nat.card (center C) = 3 := by
  rcases h.component_center_card_and_coverModel ih hsemi hn hcovers hC with he | he
  · exact (hz (card_eq_one.mp he)).elim
  · exact he.1

theorem CounterexampleToTheoremA.component_threeRanks_eq_two
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hsemi : IsSemisimple G) (hn : ¬ IsQuasisimple G)
    (hcovers : SQTKStructure.OrdinarySource.RemainingOddCoverInputs.{u})
    {C : Subgroup G} (hC : IsComponent G C) (hz : center C ≠ ⊥) :
    primeRank 3 C = 2 ∧ primeRank 3 (C ⧸ center C) = 2 := by
  let := hC.2
  have hc := h.component_center_card_three ih hsemi hn hcovers hC hz
  have hp : IsPGroup 3 (center C) := IsPGroup.of_card (n := 1) (by simpa using hc)
  have hlo := two_le_primeRank_of_nontrivial_prime_center (by decide) hp hz
  have hmod := component_centralQuotient_models_of_semisimple_not_quasisimple
    ih h.1 h.2.1 hsemi hn hC
  have hhi := hmod.1 3 Nat.prime_three (by decide)
  have hqlo := PerfectCentralCovering.two_le_primeRank_central_quotient (by decide) hlo
  have hqhi := hmod.2.1 3 Nat.prime_three (by decide)
  exact ⟨by omega, by omega⟩

theorem CounterexampleToTheoremA.component_local_threeRank_le_one_of_other_centered
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hsemi : IsSemisimple G) (hn : ¬ IsQuasisimple G)
    (hcovers : SQTKStructure.OrdinarySource.RemainingOddCoverInputs.{u})
    {C D : Subgroup G} (hC : IsComponent G C) (hD : IsComponent G D) (hne : C ≠ D)
    (hzC : center C ≠ ⊥) (hzD : center D ≠ ⊥) :
    twoLocalPrimeRank 3 C ≤ 1 := by
  have hc : C ≤ centralizer (D : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (hC.commutator_eq_bot_of_ne hD hne)
  have hint : C ⊓ D ≤ (center C).map C.subtype := by
    rintro x ⟨hxC, hxD⟩
    refine ⟨⟨x, hxC⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (hc y.property x hxD).symm
  have hcard : Nat.card (C ⊓ D : Subgroup G) ≤ 3 := by
    have hh := card_le_of_le hint
    rwa [card_map_of_injective C.subtype_injective,
      h.component_center_card_three ih hsemi hn hcovers hC hzC] at hh
  have hDlo : 2 ≤ primeRank 3 D :=
    (h.component_threeRanks_eq_two ih hsemi hn hcovers hD hzD).1.ge
  by_contra hh
  exact Theory.Quasithin.CubicIntersection.not_quasithin_of_local_two_ordinary_two
    C D hc hcard (by omega) hDlo h.1

end CFSG.Quasithin.ChapterA.Section02
