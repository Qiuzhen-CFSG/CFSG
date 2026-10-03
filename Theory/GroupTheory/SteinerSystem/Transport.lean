module

public import Theory.GroupTheory.SteinerSystem.Completion
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Relabeling finite Steiner systems

Permuting the points preserves block sizes and unique completion, so it
transports a Steiner system to another with the same parameters. The block
family is transported using the pointwise action on finite sets.
-/

namespace Theory.GroupTheory.SteinerSystem

open scoped Pointwise

variable {α : Type*} [Fintype α] [DecidableEq α] {t k : ℕ}

/-- Relabel the points of a Steiner system by a permutation. -/
@[expose]
public def relabel (D : SteinerSystem α t k) (e : Equiv.Perm α) :
    SteinerSystem α t k where
  blocks := e • D.blocks
  block_card := by
    intro B hB
    obtain ⟨C, hC, rfl⟩ := Finset.mem_smul_finset.mp hB
    simpa only [Finset.card_smul_finset] using D.block_card C hC
  steiner := by
    intro S hS
    obtain ⟨B, ⟨hB, hSB⟩, huniq⟩ :=
      D.existsUnique_block (e⁻¹ • S) (by simpa only [Finset.card_smul_finset] using hS)
    apply Finset.card_eq_one.mpr
    refine ⟨e • B, ?_⟩
    ext C
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hCmem, hSC⟩
      obtain ⟨C, hCbase, rfl⟩ := Finset.mem_smul_finset.mp hCmem
      have hpre : e⁻¹ • S ⊆ C := by
        simpa only [inv_smul_smul] using
          (Finset.smul_finset_subset_smul_finset (a := e⁻¹) hSC)
      rw [huniq C ⟨hCbase, hpre⟩]
    · rintro rfl
      refine ⟨Finset.smul_mem_smul_finset hB, ?_⟩
      simpa only [smul_inv_smul] using
        (Finset.smul_finset_subset_smul_finset (a := e) hSB)

/-- Relabeling acts on the block family by the pointwise finite-set action. -/
@[simp]
public theorem relabel_blocks (D : SteinerSystem α t k) (e : Equiv.Perm α) :
    (D.relabel e).blocks = e • D.blocks := rfl

end Theory.GroupTheory.SteinerSystem
