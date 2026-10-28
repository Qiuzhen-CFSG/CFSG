module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceLineGeometry
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.Graph

/-!
# The literal linear source collinearity graph

The three-point line action identifies adjacency in the actual coset geometry
with the orbit of a base-line edge. This proves edge transitivity and identifies
the relative edge fixer as the kernel of the symmetric-three action. The graph,
faithfulness and vertex action use the shared literal-coset construction.

Source: Aschbacher, *Sporadic Groups* (1994), 41.1–41.4, pp.219–222.
The uniqueness-system generation and local-comparison obligations are separate.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear.SourceGeometry
open GraphUniquenessSystem GraphUniquenessSystem.Cosets
open UniquenessMathieu.OctadSource (Point Line PointLineIncident graph)
variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)

variable [Finite G] (hlinear : F.LinearFusion)

include hlinear in
/-- Every actual nontrivial base-line edge has the full source collinearity orbit. -/
theorem graph_eq_orbit (t : G) (ht : t ∈ sourcePlaneNormalizer F)
    (htR : t ∉ rowNormalizer F) : graph F = Cosets.graph (rowNormalizer F) t htR := by
  ext a b
  exact (adj_iff_collinear (rowNormalizer F) t (sourcePlaneNormalizer F) htR ht
    (line_transitive F hlinear t ht htR) a b).symm

/-- Edge transitivity is proved from the literal three-point line action. -/
theorem graph_edge_transitive (a b : Point F) (h : (graph F).Adj a b) :
    ∃ g : G,
      (g • vertex (rowNormalizer F) 1 = a ∧
        g • vertex (rowNormalizer F) (lineSwap F hlinear : G) = b) ∨
      (g • vertex (rowNormalizer F) 1 = b ∧
        g • vertex (rowNormalizer F) (lineSwap F hlinear : G) = a) := by
  rw [graph_eq_orbit F hlinear _ (lineSwap F hlinear).property (lineSwap_not_row F hlinear)] at h
  exact Cosets.edge_transitive _ _ _ a b h

/-- The three source line points form their literal collinearity triangle. -/
theorem linePoint_adj {i j : Fin 3} (hij : i ≠ j) :
    (graph F).Adj (linePoint F hlinear i) (linePoint F hlinear j) := by
  refine ⟨fun he => hij (linePoint_injective F hlinear he), vertex (sourcePlaneNormalizer F) 1, ?_, ?_⟩
  · obtain ⟨a, ha, hx⟩ := (incident_base_line_iff F hlinear (linePoint F hlinear i)).mpr ⟨i, rfl⟩
    exact ⟨a, hx, ha⟩
  · obtain ⟨a, ha, hx⟩ := (incident_base_line_iff F hlinear (linePoint F hlinear j)).mpr ⟨j, rfl⟩
    exact ⟨a, hx, ha⟩

/-- The distinguished edge has both endpoints on the marked source line. -/
theorem graph_adj_base :
    (graph F).Adj (vertex (rowNormalizer F) 1)
      (vertex (rowNormalizer F) (lineSwap F hlinear : G)) := by
  rw [← linePoint_zero F hlinear, ← linePoint_one F hlinear]
  exact linePoint_adj F hlinear (by decide)

private theorem perm_three_fix_pair : ∀ p : Equiv.Perm (Fin 3),
    p 0 = 0 → p 1 = 1 → p = 1 := by decide

/-- Within the actual line stabilizer, fixing two of its points is equivalent
to fixing its full three-point residue. No ambient line-uniqueness premise is hidden. -/
theorem line_edgeFixer_iff (n : sourcePlaneNormalizer F) :
    (n : G) ∈ edgeFixer G (vertex (rowNormalizer F) 1)
      (vertex (rowNormalizer F) (lineSwap F hlinear : G)) ↔ lineAction F hlinear n = 1 := by
  change ((n : G) • vertex (rowNormalizer F) 1 = vertex (rowNormalizer F) 1 ∧
    (n : G) • vertex (rowNormalizer F) (lineSwap F hlinear : G) =
      vertex (rowNormalizer F) (lineSwap F hlinear : G)) ↔ _
  rw [← linePoint_zero F hlinear, ← linePoint_one F hlinear, linePoint_smul, linePoint_smul]
  rw [(linePoint_injective F hlinear).eq_iff, (linePoint_injective F hlinear).eq_iff]
  constructor
  · rintro ⟨h0, h1⟩; exact perm_three_fix_pair _ h0 h1
  · intro h; simp [h]

/-- The relative edge fixer is the kernel of the actual line action. -/
theorem line_edgeFixer_eq :
    (edgeFixer G (vertex (rowNormalizer F) 1)
      (vertex (rowNormalizer F) (lineSwap F hlinear : G))).subgroupOf (sourcePlaneNormalizer F) =
      (lineAction F hlinear).ker := by
  ext n
  exact line_edgeFixer_iff F hlinear n

end Theory.GroupTheory.TransvectionFive.UniquenessLinear.SourceGeometry
