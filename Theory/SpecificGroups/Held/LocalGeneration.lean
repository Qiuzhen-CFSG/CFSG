module

public import Mathlib.GroupTheory.Index
public import Mathlib.Order.Atoms

/-!
# An order criterion for the Held local pair

The maximal subgroup of shape `2^(1+6).L₃(2)` has order 21504;
its extension in `He:2` has order 43008. Neither order is divisible by
nine. Thus either maximal subgroup, together with any subgroup whose
order is divisible by nine, generates the ambient group.

This is only the generation step: construction, maximality, orders and
local quotient identifications of the subgroups remain separate inputs.
The argument is Lagrange's theorem followed by maximality.

Source for the intended local subgroups: ATLAS of Finite Group
Representations, https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/He/ .
-/

@[expose] public section
namespace Held

variable {G : Type*} [Group G]

/-- The orders of the two possible extensions of the Held local maximal
subgroup exclude containment of a subgroup with order divisible by nine. -/
theorem local_pair_sup_eq_top (P B : Subgroup G) (hP : IsCoatom P)
    (hcard : Nat.card P = 21504 ∨ Nat.card P = 43008)
    (hB : 9 ∣ Nat.card B) : P ⊔ B = ⊤ := by
  have hnot : ¬ B ≤ P := by
    intro hBP
    have hdiv : 9 ∣ Nat.card P := hB.trans (Subgroup.card_dvd_of_le hBP)
    rcases hcard with hcard | hcard
    · rw [hcard] at hdiv
      exact (by decide : ¬ 9 ∣ 21504) hdiv
    · rw [hcard] at hdiv
      exact (by decide : ¬ 9 ∣ 43008) hdiv
  apply hP.lt_iff.mp
  exact lt_of_le_of_ne le_sup_left (fun heq => hnot (heq ▸ le_sup_right))

end Held
