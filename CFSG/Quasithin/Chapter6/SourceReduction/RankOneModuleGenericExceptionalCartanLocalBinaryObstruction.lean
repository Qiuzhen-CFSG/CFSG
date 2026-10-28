module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericCartan
public import Theory.SpecificGroups.Triality.BinaryParabolicObstruction
public import Theory.GroupTheory.PResidual.PerfectImage

/-!
# Obstruction to the intrinsic parabolic step in local Cartan escape

The first rank-two paragraph of 5.1.13 uses permutation of D with T and
normalization of P by T to infer normalization of P by D. On the genuine
binary triality carrier, a cubic in the other Levi disproves this inference,
even when an odd Hall subgroup of N(T) centralizes the cubic. The arms
parabolic is perfect, so the same example moves its literal O² residual.

This does not refute 5.1.13 under its full ambient hypotheses. In particular,
the constructed cubic and Borel Hall subgroup are not asserted to come from
an original Input and CartanPair. The existing original binary reduction
forces n = 2; its remaining exclusion must use additional ambient information.
Nor may the Borel in this model be identified with an ambient overlap before
accounting for the latter's two-core kernel.

Source: Aschbacher--Smith 5.1.12--13, printed pp.635--636,
refs/quasithin.pdf. The calculation blocks only the unqualified intermediate
implication, leaving SourceLocalCartanEscape and all its interfaces unchanged.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryParabolicObstruction
open Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.ConcreteBruhat
local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "M" => BinaryCarrier 1 Nat.zero_lt_one

/-- The intrinsic inference cannot be used to exclude the binary row.
The full positive Sylow, its literal normalizer and the literal residual
are used throughout; no original ambient Input is constructed. -/
theorem not_residual_normalization_of_permutability :
    ¬ (∀ (D B : Subgroup M), Nat.card D = 3 → IsCyclic D →
      B ≤ normalizer (unipotentSylow P rfl : Set M) →
      IsHallSubgroup OddHall.oddPrimes
        (B.subgroupOf (normalizer (unipotentSylow P rfl : Set M))) →
      B ≤ centralizer (D : Set M) →
      (D : Set M) * (unipotentSylow P rfl : Set M) =
        (unipotentSylow P rfl : Set M) * D →
      (unipotentSylow P rfl : Subgroup M) ≤
        normalizer (parabolic P .arms : Set M) →
      D ≤ normalizer (residual (parabolic P .arms) : Set M)) := by
  intro h
  obtain ⟨D,hD,hcyc,_,hperm,hcent,hHall,hU,hnot⟩ :=
    Triality.Standard.BinaryParabolicObstruction.compatible_cubic_not_normalizes_arms
  have hN : normalizer (unipotentSylow P rfl : Set M) = borel P :=
    normalizer_unipotent_eq_borel P rfl
  have hBN : torus P ≤ normalizer (unipotentSylow P rfl : Set M) :=
    hN.symm ▸ torus_le_borel P
  have hBH : IsHallSubgroup OddHall.oddPrimes
      ((torus P).subgroupOf (normalizer (unipotentSylow P rfl : Set M))) := by
    rwa [hN]
  let : Group.IsPerfect (parabolic P .arms) :=
    parabolic_arms_isPerfect_at_two P rfl rfl
  have hR : residual (parabolic P .arms) = parabolic P .arms := by
    rw [residual, pResidual_eq_top_of_isPerfect 2,
      ← MonoidHom.range_eq_map, range_subtype]
  have hn := h D (torus P) hD hcyc hBN hBH hcent hperm hU
  rw [hR] at hn
  exact hnot hn

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryParabolicObstruction
