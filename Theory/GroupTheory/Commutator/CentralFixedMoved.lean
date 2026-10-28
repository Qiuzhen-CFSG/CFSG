module
public import Mathlib.GroupTheory.Commutator.Basic
/-!
# Fixed derived subgroup and centrality of the moved subgroup

If L fixes P', then a subgroup A of P centralizes [P,L] exactly when [A,L]
centralizes P. Both implications are rotations of the three-subgroups lemma.
No finiteness, splitting, or coprime action is needed.

Source application: MS93 (3.10), printed p.880, identifying the fixed-space
kernel in the moving central quotient used by (5.12), printed p.927.
-/
public section
open scoped commutatorElement
namespace Subgroup
theorem commutator_centralizes_iff_centralizes_moved
    {G : Type*} [Group G] (P L A : Subgroup G) (hAP : A≤P)
    (hfixed : ⁅P,P⁆≤centralizer (L:Set G)) :
    ⁅A,L⁆≤centralizer (P:Set G) ↔ A≤centralizer ((⁅P,L⁆:Subgroup G):Set G) := by
  have hPA : ⁅⁅P,A⁆,L⁆=⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    ((commutator_mono le_rfl hAP).trans hfixed)
  constructor
  · intro ha
    apply le_centralizer_iff.mp
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply commutator_commutator_eq_bot_of_rotate
    · rw [commutator_comm L A]
      exact commutator_eq_bot_iff_le_centralizer.mpr ha
    · simpa only [commutator_comm A P] using hPA
  · intro ha
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply commutator_commutator_eq_bot_of_rotate
    · rw [commutator_comm L P]
      exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mpr ha)
    · exact hPA
end Subgroup
