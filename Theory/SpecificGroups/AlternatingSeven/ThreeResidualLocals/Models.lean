module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Tactic

/-!
# Concrete seven-point action models for A4

These three generated permutation subgroups provide shared coordinates for the
natural four-point action, that action together with its three-point quotient,
and the action rotating three pairs. All generators are proved even. The paired
model centralizes the literal permutation (0 1)(2 3)(4 5), whose centralizer has
order 48. Recognition, completeness of the action catalogue, and residual
calculations are separate mathematical assertions, not part of these definitions.

Source: the A7 partition calculation in Aschbacher–Smith 15.3.43, printed p.1140.
-/

@[expose] public section

open Subgroup Equiv
namespace AlternatingSeven.ThreeResidualLocals

abbrev Perm7 := Equiv.Perm (Fin 7)

/-- The common involution `(0 1)(2 3)` in the three action models. -/
def fourFlip : Perm7 := swap 0 1 * swap 2 3

/-- The cubic generator on the natural four-point orbit. -/
def naturalThree : Perm7 := swap 0 1 * swap 1 2

/-- The cubic generator for the four-point action plus the nontrivial three-point quotient. -/
def diagonalThree : Perm7 := naturalThree * (swap 4 5 * swap 5 6)

/-- The cubic generator rotating three pairs. -/
def pairedThree : Perm7 := (swap 0 2 * swap 2 4) * (swap 1 3 * swap 3 5)

/-- The model fixing three points. -/
def naturalFour : Subgroup Perm7 := closure ({naturalThree, fourFlip} : Set Perm7)

/-- The model with four-point and three-point orbits. -/
def diagonalFour : Subgroup Perm7 := closure ({diagonalThree, fourFlip} : Set Perm7)

/-- The model acting on six points and fixing the seventh. -/
def pairedFour : Subgroup Perm7 := closure ({pairedThree, fourFlip} : Set Perm7)

/-- The actual permutation interchanging the points of each of the three pairs. -/
def pairing : Perm7 := swap 0 1 * swap 2 3 * swap 4 5

theorem model_generators_even :
    fourFlip ∈ alternatingGroup (Fin 7) ∧
    naturalThree ∈ alternatingGroup (Fin 7) ∧
    diagonalThree ∈ alternatingGroup (Fin 7) ∧
    pairedThree ∈ alternatingGroup (Fin 7) := by
  norm_num [Perm.mem_alternatingGroup, fourFlip, naturalThree, diagonalThree,
    pairedThree, map_mul, Perm.sign_swap]
  decide

theorem models_le_alternating :
    naturalFour ≤ alternatingGroup (Fin 7) ∧
    diagonalFour ≤ alternatingGroup (Fin 7) ∧
    pairedFour ≤ alternatingGroup (Fin 7) := by
  obtain ⟨hb, hn, hd, hp⟩ := model_generators_even
  constructor
  · exact (closure_le _).mpr (by simpa only [Set.pair_subset_iff, SetLike.mem_coe] using And.intro hn hb)
  constructor
  · exact (closure_le _).mpr (by simpa only [Set.pair_subset_iff, SetLike.mem_coe] using And.intro hd hb)
  · exact (closure_le _).mpr (by simpa only [Set.pair_subset_iff, SetLike.mem_coe] using And.intro hp hb)

theorem pairing_cycleType : pairing.cycleType = {2, 2, 2} := by decide

theorem pairing_sq : pairing ^ 2 = 1 := by decide

theorem pairedFour_le_centralizer_pairing :
    pairedFour ≤ centralizer ({pairing} : Set Perm7) := by
  apply (closure_le _).mpr
  rw [Set.pair_subset_iff, SetLike.mem_coe]
  constructor <;> apply mem_centralizer_singleton_iff.mpr <;> decide

theorem centralizer_pairing_card :
    Nat.card (centralizer ({pairing} : Set Perm7)) = 48 := by
  rw [Equiv.Perm.nat_card_centralizer, pairing_cycleType]
  norm_num

end AlternatingSeven.ThreeResidualLocals
