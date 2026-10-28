module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.LineAction
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.Flags

/-!
# The actual Mathieu source collinearity graph

The vertices are literal cosets G/N_G(U₁), and adjacency means distinct
points sharing a coset of N_G(A₁). The three-point line action proves that
this is the orbit graph of any marked edge on the base line. The ambient
action preserves adjacency and is vertex- and edge-transitive. Ambient
simplicity and the earlier point-core fusion premise give faithfulness.
The exact marked point and relative line edge stabilizers are retained.

These results supply the graph and action part of the source uniqueness
system. They do not assert global generation, the remaining plane-residue
clauses, or the source-to-native local comparison.

Source: Aschbacher, *Sporadic Groups* (1994), 41.1–41.4, pp.219–222.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer GraphUniquenessSystem
open GraphUniquenessSystem.Cosets
variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)

/-- The source graph uses common actual line cosets as its incidence test. -/
@[expose] def graph : SimpleGraph (Point F) where
  Adj := Collinear (rowNormalizer F) (planeNormalizer F)
  symm := ⟨by rintro a b ⟨hab, l, ha, hb⟩; exact ⟨hab.symm, l, hb, ha⟩⟩
  loopless := ⟨by rintro a ⟨ha, _⟩; exact ha rfl⟩

@[simp] theorem graph_adj_iff (a b : Point F) :
    (graph F).Adj a b ↔ a ≠ b ∧ ∃ l : Line F,
      PointLineIncident F a l ∧ PointLineIncident F b l := Iff.rfl

/-- Incidence with an actual line is preserved by ambient left translation. -/
theorem pointLineIncident_smul (g : G) {a : Point F} {l : Line F}
    (h : PointLineIncident F a l) : PointLineIncident F (g • a) (g • l) := by
  obtain ⟨k, rfl, rfl⟩ := h
  exact ⟨g * k, rfl, rfl⟩

theorem graph_preserves (g : G) {a b : Point F} (h : (graph F).Adj a b) :
    (graph F).Adj (g • a) (g • b) := by
  obtain ⟨hab, l, ha, hb⟩ := h
  exact ⟨fun he => hab ((MulAction.injective g) he), g • l,
    pointLineIncident_smul F g ha, pointLineIncident_smul F g hb⟩

/-- The chosen base point retains its full ambient row normalizer. -/
theorem graph_vertex_stabilizer :
    MulAction.stabilizer G (vertex (rowNormalizer F) 1) = rowNormalizer F :=
  stabilizer_base _

theorem graph_vertex_transitive (a : Point F) :
    ∃ g : G, g • vertex (rowNormalizer F) 1 = a := transitive _ a

/-- Faithfulness is inherited from the proper point stabilizer in the original
simple group, without assuming simplicity of a locally generated subgroup. -/
theorem graph_faithful (hG : IsSimpleGroup G) (hcore : PointCoreFusion z)
    (g : G) (hg : ∀ a : Point F, g • a = a) : g = 1 :=
  source_point_action_faithful F hG hcore g hg

variable [Finite G] (D : LocalData F)

include D in
/-- Every actual nontrivial base-line edge has the full source collinearity orbit. -/
theorem graph_eq_orbit (t : G) (ht : t ∈ planeNormalizer F)
    (htR : t ∉ rowNormalizer F) : graph F = Cosets.graph (rowNormalizer F) t htR := by
  ext a b
  exact (adj_iff_collinear (rowNormalizer F) t (planeNormalizer F) htR ht
    (line_transitive F D t ht htR) a b).symm

/-- Edge transitivity is proved from the literal three-point line action. -/
theorem graph_edge_transitive (a b : Point F) (h : (graph F).Adj a b) :
    ∃ g : G,
      (g • vertex (rowNormalizer F) 1 = a ∧
        g • vertex (rowNormalizer F) (lineSwap F D : G) = b) ∨
      (g • vertex (rowNormalizer F) 1 = b ∧
        g • vertex (rowNormalizer F) (lineSwap F D : G) = a) := by
  rw [graph_eq_orbit F D _ (lineSwap F D).property (lineSwap_not_row F D)] at h
  exact Cosets.edge_transitive _ _ _ a b h

/-- The three source line points form their literal collinearity triangle. -/
theorem linePoint_adj {i j : Fin 3} (hij : i ≠ j) :
    (graph F).Adj (linePoint F D i) (linePoint F D j) := by
  refine ⟨fun he => hij (linePoint_injective F D he), vertex (planeNormalizer F) 1, ?_, ?_⟩
  · obtain ⟨a, ha, hx⟩ := (incident_base_line_iff F D (linePoint F D i)).mpr ⟨i, rfl⟩
    exact ⟨a, hx, ha⟩
  · obtain ⟨a, ha, hx⟩ := (incident_base_line_iff F D (linePoint F D j)).mpr ⟨j, rfl⟩
    exact ⟨a, hx, ha⟩

/-- The distinguished edge has both endpoints on the marked source line. -/
theorem graph_adj_base :
    (graph F).Adj (vertex (rowNormalizer F) 1)
      (vertex (rowNormalizer F) (lineSwap F D : G)) := by
  rw [← linePoint_zero F D, ← linePoint_one F D]
  exact linePoint_adj F D (by decide)

private theorem perm_three_fix_pair : ∀ p : Equiv.Perm (Fin 3),
    p 0 = 0 → p 1 = 1 → p = 1 := by decide

/-- Within the actual line stabilizer, fixing two of its points is equivalent
to fixing its full three-point residue. No ambient line-uniqueness premise is hidden. -/
theorem line_edgeFixer_iff (n : planeNormalizer F) :
    (n : G) ∈ edgeFixer G (vertex (rowNormalizer F) 1)
      (vertex (rowNormalizer F) (lineSwap F D : G)) ↔ lineAction F D n = 1 := by
  change ((n : G) • vertex (rowNormalizer F) 1 = vertex (rowNormalizer F) 1 ∧
    (n : G) • vertex (rowNormalizer F) (lineSwap F D : G) =
      vertex (rowNormalizer F) (lineSwap F D : G)) ↔ _
  rw [← linePoint_zero F D, ← linePoint_one F D, linePoint_smul, linePoint_smul]
  rw [(linePoint_injective F D).eq_iff, (linePoint_injective F D).eq_iff]
  constructor
  · rintro ⟨h0, h1⟩; exact perm_three_fix_pair _ h0 h1
  · intro h; simp [h]

/-- The relative edge fixer is the kernel of the actual line action. -/
theorem line_edgeFixer_eq :
    (edgeFixer G (vertex (rowNormalizer F) 1)
      (vertex (rowNormalizer F) (lineSwap F D : G))).subgroupOf (planeNormalizer F) =
      (lineAction F D).ker := by
  ext n
  exact line_edgeFixer_iff F D n

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
