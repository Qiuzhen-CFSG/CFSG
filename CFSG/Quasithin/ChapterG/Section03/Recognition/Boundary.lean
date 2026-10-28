module

public import CFSG.Quasithin.ChapterG.Section03.Recognition.Configurations
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Boundaries of full-action configurations

Different canonical blocks fix each other's centers. If every root outside a
configuration also fixes its points, its stability under the inside roots makes
it stable under the entire generated group. Thus a proper configuration inside
one block has a pair of moving centers across its boundary.

Source: Aschbacher--Smith, G.3.1, printed p.337.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section03
open BinaryLinear BinaryTransvectionGroups
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- A root centered in another block fixes the present block pointwise. -/
theorem Hypotheses.root_fixes_other_block {G : Subgroup (GL V)} [Finite G]
    {Δ : Set V} (h : Hypotheses G Δ) (i : OrbitBlock G Δ)
    {y : V} (hy : y ∈ Δ) (hyi : y ∉ i.val) {a : GL V} (ha : a ∈ rootGroup G y) :
    ∀ x ∈ i.val, a x = x := by
  intro x hx
  by_contra hax
  apply hyi
  rw [orbitBlock_eq_orbit i hx]
  exact MulAction.mem_orbit_symm.mp (h.same_orbit_of_moved hy (block_subset h i hx) ha hax)

/-- A proper full-action configuration has a moving root across its boundary. -/
theorem LinearConfiguration.exists_moving_boundary {G : Subgroup (GL V)} [Finite G]
    {Δ Γ : Set V} (h : Hypotheses G Δ) (i : OrbitBlock G Δ)
    (c : LinearConfiguration G Δ Γ) (hΓ : Γ ⊆ i.val) (hne : Γ ≠ i.val) :
    ∃ x ∈ Γ, ∃ y ∈ i.val, y ∉ Γ ∧ ∃ a ∈ rootGroup G y, a x ≠ x := by
  have hΓne : Γ.Nonempty := by
    by_contra hn
    have he := Set.not_nonempty_iff_eq_empty.mp hn
    have hd := c.dimension_ge_two
    rw [he, Submodule.span_empty, finrank_bot] at hd
    omega
  obtain ⟨x, hx⟩ := hΓne
  by_contra hn
  push Not at hn
  have hroot (y : V) (hy : y ∈ Δ) (a : GL V) (ha : a ∈ rootGroup G y) :
      ∀ z ∈ Γ, a z ∈ Γ := by
    intro z hz
    by_cases hyΓ : y ∈ Γ
    · exact c.stable a (rootGroup_le_generated G hyΓ ha) z hz
    by_cases hyi : y ∈ i.val
    · rw [hn z hz y hyi hyΓ a ha]
      exact hz
    · rw [h.root_fixes_other_block i hy hyi ha z (hΓ hz)]
      exact hz
  have hgen (a : GL V) (ha : a ∈ generated G Δ) : ∀ z ∈ Γ, a z ∈ Γ := by
    refine Subgroup.iSup_induction _ (C := fun a : GL V => ∀ z ∈ Γ, a z ∈ Γ) ha ?_ (by intro z hz; exact hz) ?_
    · intro y b hb
      refine Subgroup.iSup_induction _ (C := fun a : GL V => ∀ z ∈ Γ, a z ∈ Γ) hb ?_ (by intro z hz; exact hz) ?_
      · intro hy t ht
        exact hroot y hy t ht
      · intro t u ht hu z hz
        exact ht (u z) (hu z hz)
    · intro t u ht hu z hz
      exact ht (u z) (hu z hz)
  apply hne
  apply Set.Subset.antisymm hΓ
  intro y hy
  rw [orbitBlock_eq_orbit i (hΓ hx)] at hy
  obtain ⟨a, rfl⟩ := MulAction.mem_orbit_iff.mp hy
  exact hgen a.val a.property x hx

end CFSG.Quasithin.ChapterG.Section03
