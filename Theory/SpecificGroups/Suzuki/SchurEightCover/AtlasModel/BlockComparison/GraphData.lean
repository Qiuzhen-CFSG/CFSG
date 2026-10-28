module
public import Theory.SpecificGroups.Suzuki.SchurEightCover.AtlasModel.BlockComparison.GraphTables
public import Theory.SpecificGroups.Suzuki.SchurEightCover.AtlasModel.BlockComparison.Partition
public import Mathlib.Order.Fin.Basic

/-!
# Checked graph certificates for exhaustion of the block kernel

The finite checks establish invariance of an eight-neighbor graph under both
original generators. The eight neighbors have distinct block labels. A parent
map with strictly decreasing natural rank connects each nonzero point to zero.
Finally, a point in block zero adjacent to block one must be one of the four
central translates of zero. These are all the numerical inputs to the kernel
proof; they imply no unverified group-order assertion.

All evaluations use Lean's kernel. The tables and their reproducible discovery
are documented in `GraphTables` and `source/graph_data.py`.
-/

namespace BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.BlockComparison.Graph
open Data

private theorem of_checkEdges {P : Point → Fin 8 → Prop} [∀ p i, Decidable (P p i)]
    (h : checkPoints (fun p => (List.finRange 8).all fun j => decide (P p j)) = true) :
    ∀ p j, P p j := by
  have hp : ∀ p, (List.finRange 8).all (fun j => decide (P p j)) = true := by
    apply of_checkPoints
    simpa only [Bool.decide_eq_true] using h
  intro p j
  exact of_decide_eq_true (List.all_eq_true.mp (hp p) j (by simp))

private theorem a_checked : ∀ p i,
    aFun (neighbor p i) = neighbor (aFun p) (nextA p i) := by
  apply of_checkEdges
  decide +kernel

private theorem b_checked : ∀ p i,
    bFun (neighbor p i) = neighbor (bFun p) (nextB p i) := by
  apply of_checkEdges
  decide +kernel

public theorem neighbor_a (p : Point) (i : Fin 8) :
    ∃ j, aFun (neighbor p i) = neighbor (aFun p) j :=
  ⟨nextA p i, a_checked p i⟩

public theorem neighbor_b (p : Point) (i : Fin 8) :
    ∃ j, bFun (neighbor p i) = neighbor (bFun p) j :=
  ⟨nextB p i, b_checked p i⟩

private theorem blocks_strict (p : Point) : ∀ i : Fin 7,
    blockOf (neighbor p i.castSucc) < blockOf (neighbor p i.succ) := by
  apply of_checkPoints _ p
  decide +kernel

public theorem neighbor_blocks_injective (p : Point) :
    Function.Injective (fun i => blockOf (neighbor p i)) :=
  (Fin.strictMono_iff_lt_succ.mpr (blocks_strict p)).injective

public theorem parent_rank_lt (p : Point) (hp : p ≠ 0) :
    rank (parent p) < rank p := by
  have h : ∀ p : Point, p ≠ 0 → rank (parent p) < rank p := by
    apply of_checkPoints
    decide +kernel
  exact h p hp

public theorem parent_neighbor (p : Point) (hp : p ≠ 0) :
    ∃ i, neighbor (parent p) i = p := by
  have h : ∀ p : Point, p ≠ 0 → neighbor (parent p) (edge p) = p := by
    apply of_checkPoints
    decide +kernel
  exact ⟨edge p, h p hp⟩

public theorem base_candidates (p : Point) (hp : blockOf p = blockOf 0)
    (i : Fin 8) (hi : blockOf (neighbor p i) = blockOf (neighbor 0 0)) :
    p = 0 ∨ p = zFun 0 ∨ p = wFun 0 ∨ p = zFun (wFun 0) := by
  have h : ∀ p : Point, blockOf p = blockOf 0 → ∀ i : Fin 8,
      blockOf (neighbor p i) = blockOf (neighbor 0 0) →
      p = 0 ∨ p = zFun 0 ∨ p = wFun 0 ∨ p = zFun (wFun 0) := by
    apply of_checkPoints
    decide +kernel
  exact h p hp i hi

end BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.BlockComparison.Graph
