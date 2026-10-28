module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# A fixed subgroup in an irreducible commutator layer

Suppose N lies in a centerless group H, with [N,H] contained in an
irreducible H-subgroup Z. If an actor D normalizes N and [D,H] centralizes
N, the three-subgroup lemma makes C_Z(D) H-invariant. A nonzero fixed
subgroup therefore forces D to fix Z, then to centralize N.

This is the commutator argument used in DGS, *Groups and Graphs* (1985),
9.8, printed p.146, before the torus displacement escapes the middle core.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

/-- An actor commuting with the ambient group on a central layer fixes
that layer if it fixes a nonzero part of its irreducible displacement. -/
theorem centralizes_layer_of_fixed_irreducible
    (H N Z D : Subgroup G) (hNH : N ≤ H) (hZN : Z ≤ N)
    (hDN : D ≤ normalizer (N : Set G))
    (hHZ : H ≤ normalizer (Z : Set G)) (hNZ : ⁅N,H⁆ ≤ Z)
    (hDH : ⁅D,H⁆ ≤ centralizer (N : Set G))
    (hcenter : center H = ⊥)
    (hirr : ∀ A : Subgroup G, A ≤ Z → H ≤ normalizer (A : Set G) → A = ⊥ ∨ A = Z)
    (hfixed : Z ⊓ centralizer (D : Set G) ≠ ⊥) : N ≤ centralizer (D : Set G) := by
  let C := Z ⊓ centralizer (D : Set G)
  have hCD : ⁅C,D⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
  have hHC : H ≤ normalizer (C : Set G) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    apply le_inf
    · exact (commutator_mono le_rfl inf_le_left).trans
        (le_normalizer_iff_commutator_le_right.mp hHZ)
    · apply commutator_eq_bot_iff_le_centralizer.mp
      apply commutator_commutator_eq_bot_of_rotate
      · rw [hCD,commutator_bot_left]
      · exact commutator_eq_bot_iff_le_centralizer.mpr
          (hDH.trans (centralizer_le (inf_le_left.trans hZN)))
  have hC : C = Z := (hirr C inf_le_left hHC).resolve_left hfixed
  have hZD : Z ≤ centralizer (D : Set G) := hC ▸ (show C ≤ centralizer (D : Set G) from inf_le_right)
  have hNDH : ⁅N,D⁆ ≤ centralizer (H : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply commutator_commutator_eq_bot_of_rotate
    · exact commutator_eq_bot_iff_le_centralizer.mpr hDH
    · rw [commutator_comm H N]
      exact commutator_eq_bot_iff_le_centralizer.mpr (hNZ.trans hZD)
  have hNDN : ⁅N,D⁆ ≤ N := le_normalizer_iff_commutator_le_left.mp hDN
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply bot_unique
  intro x hx
  have hm : (⟨x,hNH (hNDN hx)⟩ : H) ∈ center H := by
    apply mem_center_iff.mpr
    intro h
    apply Subtype.ext
    exact hNDH hx h h.property
  exact mem_bot.mpr (congrArg (fun a : H => (a : G)) (mem_bot.mp (hcenter ▸ hm)))
end Subgroup
