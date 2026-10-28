module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceNormalCore
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceNormalCore

/-!
# The full source edge fixer and uniqueness of lines

The row intersects the actual pointwise edge fixer in its marked eight-group:
that subgroup has index two in the row, while a marked row shear moves the
second endpoint. Normalizing this intersection forces the whole edge fixer
into the line normalizer, where it is the kernel of the three-point action.
Every edge therefore determines a unique literal source line. The same
intersection calculation identifies the normalizer of the edge fixer inside
the row normalizer with the point-line flag stabilizer.

These are the line-uniqueness and vertex-normalizer assertions used in
Aschbacher, *Sporadic Groups* (1994), 41.4, p.222. The argument uses the
21/21 linear fusion counts and actual cosets; it assumes neither ambient
simplicity nor global generation. The implementation import reuses the
checked marked row shear without exposing its matrix encoding.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear.SourceGeometry
open GraphUniquenessSystem GraphUniquenessSystem.Cosets
variable {G : Type*} [Group G] [Finite G] {z : G}
  (F : MarkedCentralizer z) (hlinear : F.LinearFusion)

/-- The row kernel on the chosen edge is precisely the original marked eight-group. -/
theorem row_edgeFixer_intersection :
    F.row ⊓ edgeFixer G (vertex (rowNormalizer F) 1)
      (vertex (rowNormalizer F) (lineSwap F hlinear : G)) = F.row ⊓ F.plane := by
  let B := edgeFixer G (vertex (rowNormalizer F) 1)
    (vertex (rowNormalizer F) (lineSwap F hlinear : G))
  have hplane : F.plane ≤ rowNormalizer F :=
    (F.pullback_le _).trans (point_centralizer_le_row_normalizer F)
  have hDB : F.row ⊓ F.plane ≤ B := by
    intro a ha
    change a ∈ edgeFixer G (vertex (rowNormalizer F) 1)
      (vertex (rowNormalizer F) (lineSwap F hlinear : G))
    rw [Cosets.edgeFixer_eq]
    refine ⟨F.row.le_normalizer ha.1, ?_⟩
    apply hplane
    exact (mem_normalizer_iff.mp ((sourcePlaneNormalizer F).inv_mem (lineSwap F hlinear).property) a).mp ha.2
  have hnot : (rowShear F : G) ∉ B := by
    intro h
    have h1 := (line_edgeFixer_iff F hlinear (rowShear F)).mp h
    rw [rowShear_action] at h1
    exact (by decide : Equiv.swap (1 : Fin 3) 2 ≠ 1) h1
  let D := (F.row ⊓ F.plane).subgroupOf F.row
  let E := B.subgroupOf F.row
  have hDE : D ≤ E := fun _ ha => hDB ha
  have hDcard : Nat.card D = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show F.row ⊓ F.plane ≤ F.row from inf_le_left)).toEquiv).trans
      (UniquenessMathieu.SourceNormalizer.row_plane_card F)
  have hi : D.index = 2 := by
    have hc := D.card_mul_index
    rw [hDcard, row_card F] at hc
    omega
  have hm := relIndex_mul_index hDE
  rw [hi] at hm
  have hp : (D.relIndex E * E.index).Prime := hm ▸ (by decide : Nat.Prime 2)
  have hED : E ≤ D := by
    rcases Nat.prime_mul_iff.mp hp with ⟨_, hE⟩ | ⟨_, hrel⟩
    · have hEtop : E = ⊤ := index_eq_one.mp hE
      have hn : (⟨rowShear F, rowShearPoint_mem F⟩ : F.row) ∈ E := by rw [hEtop]; trivial
      exact False.elim (hnot hn)
    · exact relIndex_eq_one.mp hrel
  apply le_antisymm
  · intro a ha
    exact hED (x := ⟨a, ha.1⟩) ha.2
  · exact le_inf inf_le_left hDB

/-- Fixing the two source endpoints forces preservation of their marked line.
This is proved for the full ambient edge fixer, not just its line intersection. -/
theorem edgeFixer_le_line :
    edgeFixer G (vertex (rowNormalizer F) 1)
      (vertex (rowNormalizer F) (lineSwap F hlinear : G)) ≤ sourcePlaneNormalizer F := by
  let B := edgeFixer G (vertex (rowNormalizer F) 1)
    (vertex (rowNormalizer F) (lineSwap F hlinear : G))
  intro b hb
  have hbR : b ∈ rowNormalizer F := by
    have h := hb.1
    change b ∈ MulAction.stabilizer G (vertex (rowNormalizer F) 1) at h
    simpa only [stabilizer_base] using h
  have hn : b ∈ normalizer ((F.row ⊓ B : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hbR, B.le_normalizer hb⟩
  change b ∈ normalizer ((F.row ⊓ edgeFixer G (vertex (rowNormalizer F) 1)
    (vertex (rowNormalizer F) (lineSwap F hlinear : G)) : Subgroup G) : Set G) at hn
  rw [row_edgeFixer_intersection F hlinear, source_row_plane_normalizer F] at hn
  exact hn.2

/-- The full source edge fixer is the kernel of the literal symmetric-three
action, embedded by the original line-normalizer inclusion. -/
theorem edgeFixer_eq_line_kernel :
    edgeFixer G (vertex (rowNormalizer F) 1)
      (vertex (rowNormalizer F) (lineSwap F hlinear : G)) =
        ((lineAction F hlinear).ker).map (sourcePlaneNormalizer F).subtype := by
  apply le_antisymm
  · intro b hb
    exact ⟨⟨b, edgeFixer_le_line F hlinear hb⟩,
      (line_edgeFixer_iff F hlinear _).mp hb, rfl⟩
  · rintro b ⟨a, ha, rfl⟩
    exact (line_edgeFixer_iff F hlinear a).mpr ha

/-- The same literal identification for the edge reversal chosen inside G₃. -/
theorem plane_edgeFixer_eq_line_kernel :
    edgeFixer G (vertex (rowNormalizer F) 1)
      (vertex (rowNormalizer F) (planeSwap F hlinear : G)) =
        ((lineAction F hlinear).ker).map (sourcePlaneNormalizer F).subtype := by
  rw [planeSwap_vertex, edgeFixer_eq_line_kernel]

open UniquenessMathieu.OctadSource (Point Line PointLineIncident pointLineIncident_smul)

/-- The distinguished edge is incident with exactly its original source line. -/
theorem base_line_unique (l : Line F)
    (hxl : PointLineIncident F (vertex (rowNormalizer F) 1) l)
    (hyl : PointLineIncident F (vertex (rowNormalizer F) (lineSwap F hlinear : G)) l) :
    l = vertex (sourcePlaneNormalizer F) 1 := by
  obtain ⟨a, hax, hal⟩ := hxl
  obtain ⟨b, hby, hbl⟩ := hyl
  have haM : a ∈ rowNormalizer F := (vertex_eq_base _ _).mp hax
  have huP : a⁻¹ * b ∈ sourcePlaneNormalizer F :=
    (vertex_eq_iff _ _ _).mp (hal.trans hbl.symm)
  have huM : a⁻¹ * b ∉ rowNormalizer F := by
    intro h
    exact (graph_adj_base F hlinear).ne
      (hax.symm.trans (((vertex_eq_iff _ _ _).mpr h).trans hby))
  obtain ⟨p, hpP, hpx, hpt⟩ := line_transitive F hlinear (lineSwap F hlinear : G)
    (lineSwap F hlinear).property (lineSwap_not_row F hlinear) (a⁻¹ * b) huP huM
  have hapB : a * p ∈ edgeFixer G (vertex (rowNormalizer F) 1)
      (vertex (rowNormalizer F) (lineSwap F hlinear : G)) := by
    constructor
    · change vertex (rowNormalizer F) ((a * p) * 1) = vertex (rowNormalizer F) 1
      rw [mul_one]
      exact (vertex_eq_base _ _).mpr ((rowNormalizer F).mul_mem haM ((vertex_eq_base _ _).mp hpx))
    · change vertex (rowNormalizer F) ((a * p) * (lineSwap F hlinear : G)) = _
      have hh := congrArg (fun q : Point F => a • q) hpt
      simpa only [smul_vertex, mul_assoc, mul_inv_cancel_left, hby] using hh
  have haP : a ∈ sourcePlaneNormalizer F := by
    have h := (sourcePlaneNormalizer F).mul_mem (edgeFixer_le_line F hlinear hapB)
      ((sourcePlaneNormalizer F).inv_mem hpP)
    simpa only [mul_inv_cancel_right] using h
  exact hal.symm.trans ((vertex_eq_base _ _).mpr haP)

include hlinear in
/-- Any two distinct source points are on at most one literal source line. -/
theorem line_unique {a b : Point F} (hab : a ≠ b) {l m : Line F}
    (hal : PointLineIncident F a l) (hbl : PointLineIncident F b l)
    (ham : PointLineIncident F a m) (hbm : PointLineIncident F b m) : l = m := by
  have hgraph : (UniquenessMathieu.OctadSource.graph F).Adj a b := ⟨hab, l, hal, hbl⟩
  obtain ⟨g, h | h⟩ := graph_edge_transitive F hlinear a b hgraph
  · have hl := base_line_unique F hlinear (g⁻¹ • l)
      (by simpa only [← h.1, inv_smul_smul] using pointLineIncident_smul F g⁻¹ hal)
      (by simpa only [← h.2, inv_smul_smul] using pointLineIncident_smul F g⁻¹ hbl)
    have hm := base_line_unique F hlinear (g⁻¹ • m)
      (by simpa only [← h.1, inv_smul_smul] using pointLineIncident_smul F g⁻¹ ham)
      (by simpa only [← h.2, inv_smul_smul] using pointLineIncident_smul F g⁻¹ hbm)
    exact MulAction.injective g⁻¹ (hl.trans hm.symm)
  · have hl := base_line_unique F hlinear (g⁻¹ • l)
      (by simpa only [← h.1, inv_smul_smul] using pointLineIncident_smul F g⁻¹ hbl)
      (by simpa only [← h.2, inv_smul_smul] using pointLineIncident_smul F g⁻¹ hal)
    have hm := base_line_unique F hlinear (g⁻¹ • m)
      (by simpa only [← h.1, inv_smul_smul] using pointLineIncident_smul F g⁻¹ hbm)
      (by simpa only [← h.2, inv_smul_smul] using pointLineIncident_smul F g⁻¹ ham)
    exact MulAction.injective g⁻¹ (hl.trans hm.symm)

/-- The original line normalizer normalizes the full pointwise edge fixer. -/
theorem line_normalizes_edgeFixer :
    sourcePlaneNormalizer F ≤ normalizer ((edgeFixer G (vertex (rowNormalizer F) 1)
      (vertex (rowNormalizer F) (lineSwap F hlinear : G))) : Set G) := by
  apply le_normalizer_iff.mpr
  intro n hn b hb
  have hbP := edgeFixer_le_line F hlinear hb
  let n' : sourcePlaneNormalizer F := ⟨n, hn⟩
  let b' : sourcePlaneNormalizer F := ⟨b, hbP⟩
  change ((n' * b' * n'⁻¹ : sourcePlaneNormalizer F) : G) ∈ _
  apply (line_edgeFixer_iff F hlinear _).mpr
  rw [map_mul, map_mul, map_inv, (line_edgeFixer_iff F hlinear b').mp hb, mul_one, mul_inv_cancel]

/-- The vertex-side normalizer clause of 41.4 (V4): the edge fixer's
normalizer inside G₁ is exactly the point-line flag stabilizer. -/
theorem row_edgeFixer_normalizer :
    normalizer ((edgeFixer G (vertex (rowNormalizer F) 1)
      (vertex (rowNormalizer F) (lineSwap F hlinear : G))) : Set G) ⊓ rowNormalizer F =
      sourcePlaneNormalizer F ⊓ rowNormalizer F := by
  apply le_antisymm
  · intro n hn
    have hi := inf_normalizer_le_normalizer_inf (H := F.row)
      (K := edgeFixer G (vertex (rowNormalizer F) 1)
        (vertex (rowNormalizer F) (lineSwap F hlinear : G))) ⟨hn.2, hn.1⟩
    rw [row_edgeFixer_intersection F hlinear, source_row_plane_normalizer F] at hi
    exact ⟨hi.2, hn.2⟩
  · exact fun n hn => ⟨line_normalizes_edgeFixer F hlinear hn.1, hn.2⟩

end Theory.GroupTheory.TransvectionFive.UniquenessLinear.SourceGeometry
