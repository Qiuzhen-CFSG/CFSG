module
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.FourBlockPoint
/-!
# Nontrivial Sylow action at the even four-block stabilizer

A Sylow two-subgroup of the even four-block stabilizer cannot lie in its
intrinsic two-core. The core is the product of the two block Klein groups,
whereas the simultaneous transposition in the two blocks is an involution
outside that product. If a Sylow lay in the core, its maximality applied
to the normal-core join with this involution would give a contradiction.

This supplies the point-stabilizer obstruction in Aschbacher--Smith
12.6.31, printed pp.836--837, used by the original marked torus argument.
-/

public section
open Subgroup
namespace BinaryPermutation.TerminalOrthogonal.FourBlockResidual
open Theory.SpecificGroups.SymmetricEight
open scoped commutatorElement

/-- The even four-block stabilizer has no Sylow two-subgroup in its two-core. -/
theorem sylow_not_le_core (S : Sylow 2 P) : ¬ (S : Subgroup P) ≤ pCore 2 P := by
  intro hS
  let a : S8 := Equiv.swap 0 1 * Equiv.swap 4 5
  have ha : a ∈ P := by
    constructor
    · change Equiv.Perm.sign a = 1
      decide +kernel
    · change ∀ i j : Fin 8, (a i).val / 4 = (a j).val / 4 ↔ i.val / 4 = j.val / 4
      decide +kernel
  let b : P := ⟨a,ha⟩
  have hb : b^2=1 := by
    apply Subtype.ext
    change a^2=1
    decide +kernel
  have hp : IsPGroup 2 (zpowers b) := IsPGroup.of_card_dvd_pow (n := 1) (by
    simpa only [Nat.card_zpowers,pow_one] using orderOf_dvd_of_pow_eq_one hb)
  have hs := S.is_maximal' (hp.to_sup_of_normal_right pCore_isPGroup)
    (hS.trans le_sup_right)
  have hbcore : b ∈ pCore 2 P := hS (hs.le (mem_sup_left (mem_zpowers b)))
  have hambient := mem_map_of_mem P.subtype hbcore
  change a ∈ P.pCoreIn 2 at hambient
  rw [FourBlockPoint.intermediate_core P R_le_P inf_le_right] at hambient
  have hn : ¬ ∃ i j : Fin 4, a = FourBlockCoreAction.kleinPerm i j := by decide +kernel
  exact hn hambient
end BinaryPermutation.TerminalOrthogonal.FourBlockResidual
