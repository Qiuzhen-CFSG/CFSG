module

public import Theory.GroupTheory.InvolutionCentralizerControl
public import Mathlib.GroupTheory.Commutator.Basic
meta import Lean.Elab.Tactic.Omega

/-!
# A normalized image of order at most two

A subgroup with at most two image elements has trivial automorphism group.
Thus every normalizing subgroup centralizes its image, and the original
commutator lies in the kernel of the same homomorphism.

Source application: Aschbacher–Smith 14.7.4(4), where this observation and
the three-subgroups lemma force the full point-radical image.
-/

public section
namespace Subgroup

/-- A normalizing subgroup centralizes an image of order at most two. -/
theorem commutator_le_ker_of_normalized_image_card_le_two {J X : Type*} [Group J] [Group X] [Finite X]
    (q : J →* X) (A B : Subgroup J) (hn : A ≤ normalizer (B : Set J))
    (hc : Nat.card (B.map q) ≤ 2) : ⁅A,B⁆ ≤ q.ker := by
  have hz : ⁅A.map q,B.map q⁆ = ⊥ := by
    have hp := Nat.card_pos (α := B.map q)
    have hc' : Nat.card (B.map q) = 1 ∨ Nat.card (B.map q) = 2 := by omega
    rcases hc' with hc' | hc'
    · rw [card_eq_one.mp hc', commutator_bot_right]
    · apply commutator_eq_bot_iff_le_centralizer.mpr
      exact ((map_mono hn).trans (le_normalizer_map q)).trans
        (normalizer_le_centralizer_of_card_two _ hc')
  rw [← map_commutator, Subgroup.map_eq_bot_iff] at hz
  exact hz

end Subgroup
