module
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.ProjectiveComparison.GraphData

/-!
# Kernel-checked graph witnesses for the central quotient

The two generators preserve the 45-neighbor rows, whose block labels are
strictly increasing. The parent map decreases rank away from roots 0 and 1.
These are precisely the inputs to the structural block-kernel proof, and are
checked without group-order or group-identification assumptions.
Source and reproducible table construction: `GraphData` and its replay script.
-/

public section
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.BlockAction.Graph

set_option Elab.async false

private theorem a_checked : ∀ p i,
    a (neighbor p i) = neighbor (a p) (nextA p i) := by decide +kernel

private theorem b_checked : ∀ p i,
    b (neighbor p i) = neighbor (b p) (nextB p i) := by decide +kernel

theorem neighbor_a (p : Point) (i : Fin 45) :
    ∃ j, a (neighbor p i) = neighbor (a p) j := ⟨nextA p i, a_checked p i⟩

theorem neighbor_b (p : Point) (i : Fin 45) :
    ∃ j, b (neighbor p i) = neighbor (b p) j := ⟨nextB p i, b_checked p i⟩

private theorem blocks_strict : ∀ p : Point, ∀ i : Fin 44,
    blockOf (neighbor p i.castSucc) < blockOf (neighbor p i.succ) := by decide +kernel

theorem neighbor_blocks_injective (p : Point) :
    Function.Injective (fun i => blockOf (neighbor p i)) :=
  (Fin.strictMono_iff_lt_succ.mpr (blocks_strict p)).injective

theorem parent_rank_lt (p : Point) (hp : p ≠ 0) (hp' : p ≠ 1) :
    rank (parent p) < rank p := by
  have h : ∀ p : Point, p ≠ 0 → p ≠ 1 → rank (parent p) < rank p := by decide +kernel
  exact h p hp hp'

theorem parent_neighbor (p : Point) (hp : p ≠ 0) (hp' : p ≠ 1) :
    ∃ i, neighbor (parent p) i = p := by
  have h : ∀ p : Point, p ≠ 0 → p ≠ 1 → neighbor (parent p) (edge p) = p := by
    decide +kernel
  exact ⟨edge p, h p hp hp'⟩

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.BlockAction.Graph
