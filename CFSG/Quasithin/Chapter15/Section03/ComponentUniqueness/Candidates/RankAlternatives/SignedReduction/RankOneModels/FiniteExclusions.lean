module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.ComponentStructure.Models
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.ThreeRank
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.RankOne.FiniteModels.Basic
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore
public import Theory.Quasithin.Rank

/-!
# Alternating and sporadic exclusions at three-rank one

Two disjoint three-cycles exclude the simple alternating models. Their triple
covers have odd central subgroups, contradicting the trivial odd core.
For sporadic covers, rank decreases under the two-core quotient, so the actual
rank witnesses in every allowed carrier rule them out, including HS.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 1.1.5(3)(c,d,f),
printed pp.501–503, and the rank-one paragraph of 15.3.37 on p.1135.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.RankOneModels
open ComponentStructure ClassificationModels
open DiagonalOuter.FieldExclusion.RankOne.FiniteModels
variable {K : Type*} [Group K] [Finite K]

/-- The complete sporadic list in 1.1.5(3)(f) has three-rank at least two. -/
theorem sporadic_rank (name : SporadicName) (hne : name ≠ .j3) [Finite name.Carrier] :
    2 ≤ primeRank 3 name.Carrier := by
  cases name with
  | m11 => exact m11_rank_ge_two
  | m12 => exact m12_rank_ge_two
  | m22 => exact m22_rank_ge_two
  | m23 => exact m23_rank_ge_two
  | m24 => exact m24_rank_ge_two
  | j2 => exact j2_rank_ge_two
  | j3 => exact (hne rfl).elim
  | j4 => exact j4_rank_ge_two
  | hs => exact Sporadic.LeechRelated.HS.ThreeRank.two_le_primeRank
  | he => exact held_rank_ge_two
  | ru => exact ru_rank_ge_two

/-- A quotient by the actual two-core retains the rank obstruction. -/
theorem not_sporadic_quotient (hr : primeRank 3 K = 1)
    (name : SporadicName) (hne : name ≠ .j3)
    (hmodel : Nonempty ((K ⧸ pCore 2 K) ≃* name.Carrier)) : False := by
  obtain ⟨e⟩ := hmodel
  let : Finite name.Carrier := Finite.of_injective e.symm e.symm.injective
  have h := sporadic_rank name hne
  rw [← primeRank_equiv 3 e] at h
  have hu := primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 K) pCore_isPGroup
  omega

/-- Trivial odd core forbids the genuine central three-cover. -/
theorem no_three_center [IsQuasisimple K] (ho : pPrimeCore 2 K = ⊥)
    (hZ : Nonempty (center K ≃* Multiplicative (ZMod 3))) : False := by
  obtain ⟨e⟩ := hZ
  have hp : IsPGroup 2 (center K) := by
    rw [IsQuasisimple.center_eq_pCore ho]
    exact pCore_isPGroup
  have hc : Nat.card (center K) = 3 := by
    simpa using Nat.card_congr e.toEquiv
  rcases hp.card_eq_or_dvd with h | h <;> norm_num [hc] at h

/-- Both alternating-action constructors, including their triple covers,
are impossible at rank one with trivial odd core. -/
theorem not_alternating_action [IsQuasisimple K] (ho : pPrimeCore 2 K = ⊥)
    (hr : primeRank 3 K = 1) {n : ℕ} (hn : 6 ≤ n)
    (alpha : MulAut K) (sigma : Equiv.Perm (Fin n))
    (hmodel : AlternatingAction alpha n sigma) : False := by
  rcases hmodel with ⟨e, _⟩ | ⟨_, hZ, _⟩
  · have h := alternatingGroup.TwoThreeCycles.two_le_primeRank hn
    rw [← primeRank_equiv 3 e, hr] at h
    omega
  · exact no_three_center ho hZ

end CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.RankOneModels
