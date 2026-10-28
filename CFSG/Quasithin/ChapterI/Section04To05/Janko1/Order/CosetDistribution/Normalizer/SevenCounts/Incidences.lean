module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Normalizer.SevenCounts.Geometry
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Normalizer.SevenCounts.Incidences.CentralizedSingletons
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.Incidences.LocalInverters

/-!
# The four involution incidences in the seven-centralizer normalizer

For `A = C_G(S)` and `H = N_G(A)`, count the literal pairs of outside
involutions and elements of orders two, three and six in H. The supplied
geometry identifies the inversion sets with cyclic subgroups. Ambient
six-inverter counts and the prime data then give the three inversion
equations. The centralization count uses the proved singleton criterion
and the unique three-subgroup centralized by each centralized singleton.

These are precisely the four incidence inputs of
`bender_seven_counts_of_incidences`. The structure and geometry remain
explicit inputs whose producers belong to the source-theorem assembly.

Source: H. Bender, *Finite groups with large subgroups*, Illinois J. Math.
18 (1974), proof of (4.3), printed p.226, before the later Sylow-normalizer
coset distribution.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData

/-- All four literal seven-normalizer incidence equations, conditional only
on the supplied local structure and geometry and the source hypotheses. -/
public theorem bender_seven_incidences
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : Janko1CentralizerData G) {d : ℕ} (localData : BenderPrimeData G d)
    (S : Subgroup G) (_hSN : S ≤ normalizer (h.sylow : Set G)) (hS : Nat.card S = 7)
    (_heven : Even (Nat.card (normalizer (S : Set G))))
    (_hcontrary : centralizer (S : Set G) ≠ S)
    (structureData : BenderSevenStructure h S) (geometry : BenderSevenGeometry S) :
    Nat.card (BenderInvolutionsInFibers
      (normalizer (centralizer (S : Set G) : Set G)) 6) =
        6 * Nat.card (centralizer (S : Set G)) ∧
    Nat.card (BenderInvolutionsInFibers
      (normalizer (centralizer (S : Set G) : Set G)) 2) +
        Nat.card (BenderInvolutionsInFibers
          (normalizer (centralizer (S : Set G) : Set G)) 6) =
        30 * Nat.card (centralizer (S : Set G)) ∧
    Nat.card (BenderInvolutionsInFibers
      (normalizer (centralizer (S : Set G) : Set G)) 3) +
        Nat.card (BenderInvolutionsInFibers
          (normalizer (centralizer (S : Set G) : Set G)) 6) =
        6 * d * Nat.card (centralizer (S : Set G)) ∧
    Nat.card (BenderCentralizedSingletons
      (normalizer (centralizer (S : Set G) : Set G))) =
        2 * (d - 1) * Nat.card (centralizer (S : Set G)) := by
  exact ⟨bender_seven_six_incidence_of_local_count h localData hS structureData geometry
      (bender_six_inverter_card h),
    bender_seven_two_incidence h localData hS structureData geometry,
    bender_seven_three_incidence h localData hS structureData geometry,
    bender_seven_centralized_singleton_incidence h localData hS structureData geometry⟩

end CFSG.Quasithin.Janko1CentralizerData
