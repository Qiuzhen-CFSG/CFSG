module
public import Theory.SpecificGroups.Alternating.FourPairThompson.Definitions
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.PrimeRankDihedral
public import Theory.GroupTheory.PrimeRankSylow
public import Theory.SpecificGroups.SymmetricFourSylow
public import Stellmacher.ElementaryAbelianMaxJ
import Mathlib.Tactic

/-!
# Elementary subgroups of the four-point factors

The dihedral Sylow theorem bounds elementary subgroups of S₄ by four.
The literal Klein four base therefore has order sixteen and is elementary.
These facts supply the Thompson argument in Aschbacher–Smith 14.1.10.
-/
@[expose] public section
namespace AlternatingFourPair.Thompson
open Subgroup Theory.GroupTheory
 theorem symmetricFour_twoRank_le : primeRank 2 D ≤ 2 := by
  let P : Sylow 2 D := Classical.choice inferInstance
  obtain ⟨e⟩ := Equiv.Perm.sylow_two_equiv_dihedral_four P
  rw [P.primeRank_eq, primeRank_equiv 2 e]
  exact dihedral_rank_le_two 2

 theorem symmetricFour_elementary_card_le (E : Subgroup D)
    (hE : IsElementaryAbelian 2 E) : Nat.card E ≤ 4 :=
  (primeRank_le_iff_elementary_card_le D).mp symmetricFour_twoRank_le E hE

 theorem core_elementary : IsElementaryAbelian 2 (pCore 2 D) := by
  rw [← Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq]
  infer_instance
 theorem core_card : Nat.card (pCore 2 D) = 4 := by
  rw [← Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq]
  exact Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_card

 theorem kleinBase_card : Nat.card kleinBase = 16 := by
  change Nat.card (coordinateSubgroup (pCore 2 D)) = 16
  rw [Nat.card_congr (coordinateEquiv _).toEquiv, Nat.card_fun, core_card]
  norm_num [Nat.card_eq_fintype_card]

instance kleinBase_elementary : IsElementaryAbelian 2 kleinBase := by
  change IsElementaryAbelian 2 (coordinateSubgroup (pCore 2 D))
  refine { is_comm.comm := ?_, exponent_dvd_p := ?_ }
  · intro a b
    let : IsElementaryAbelian 2 (pCore 2 D) := core_elementary
    apply (coordinateEquiv (pCore 2 D)).injective
    exact ((coordinateEquiv _).map_mul a b).trans
      ((IsMulCommutative.is_comm.comm _ _).trans ((coordinateEquiv _).map_mul b a).symm)
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro a
    apply (coordinateEquiv (pCore 2 D)).injective
    rw [map_pow, map_one]
    funext i
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp core_elementary.exponent_dvd_p _

 theorem core_mem_iff (x : D) : x ∈ pCore 2 D ↔ x.sign = 1 ∧ x ^ 2 = 1 := by
  rw [← Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq]
  exact Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_mem_iff x

 theorem kleinBase_le_alternatingBase : kleinBase ≤ alternatingBase := by
  intro w hw
  exact ⟨hw.1, fun i => (core_mem_iff _).mp (hw.2 i) |>.1⟩
end AlternatingFourPair.Thompson
