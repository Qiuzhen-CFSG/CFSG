module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.LinePlane
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceTensorProduct

/-!
# Unique source lines and their ambient edge fixers

The row group centralizes its first tensor direction, so it acts trivially
on the three-dimensional tensor factor. Its kernel on the three line points
is therefore exactly U₁∩A₁. The full edge fixer normalizes this intersection,
whose normalizer is G₁∩G₂. Thus it preserves the actual line. Ordered edge
transitivity on a specified line now proves uniqueness of that line for any
two distinct incident source points.

This discharges the line-uniqueness and ambient-edge containment used in
Aschbacher, *Sporadic Groups* (1994), 38.8 and 41.4, printed pp.208, 222.
Only the genuine earlier normalizer data are used; global generation and
source-to-native local comparison remain separate obligations.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer PlaneTensor PlaneCensus
open GraphUniquenessSystem GraphUniquenessSystem.Cosets
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z) (D : LocalData F)

/-- The row group normalizes the first rectangle through the literal intersection. -/
theorem row_le_line_normalizer : F.row ≤ planeNormalizer F := by
  intro a ha
  have hc : a ∈ Subgroup.centralizer ((F.row ⊓ F.plane : Subgroup G) : Set G) := by
    rw [source_row_plane_centralizer]
    exact mem_sup_left ha
  have hn := centralizer_le_normalizer _ hc
  rw [source_row_plane_normalizer] at hn
  exact hn.2

private theorem first_tensor_injective : Function.Injective (tensorCode 0) := by decide

/-- Row elements act trivially on the three-dimensional tensor factor. -/
theorem row_line_linear_factor (a : F.row) :
    (planeQuotientEquiv F D.orientation.1
      (QuotientGroup.mk (inclusion (row_le_line_normalizer F) a))).1 = 1 := by
  let n := inclusion (row_le_line_normalizer F) a
  have h0 : lineAction F D n 0 = 0 :=
    (lineAction_fix_iff F D n).mpr (F.row.le_normalizer a.property)
  apply LinearEquiv.ext
  intro v
  apply first_tensor_injective
  apply element_injective F
  have hc : (a : G) ∈ Subgroup.centralizer (F.row : Set G) :=
    (row_centralizer_eq F).symm ▸ a.property
  have hh := mem_centralizer_iff.mp hc (element F (tensorCode 0 v))
    ((tensor_element_mem_row_iff F 0 v).mpr (Or.inl rfl))
  have he := lineAction_tensor F D n 0 v
  rw [h0] at he
  exact he.trans (by change (a : G) * _ * (a : G)⁻¹ = _; rw [← hh, mul_inv_cancel_right]; rfl)

/-- On the original row, the kernel of the three-point action is exactly U₁∩A₁. -/
theorem row_line_kernel_iff (a : F.row) :
    lineAction F D (inclusion (row_le_line_normalizer F) a) = 1 ↔ (a : G) ∈ F.plane := by
  let n := inclusion (row_le_line_normalizer F) a
  have he : planeQuotientEquiv F D.orientation.1 (QuotientGroup.mk n) = 1 ↔
      lineAction F D n = 1 := by
    constructor
    · intro h; exact congrArg Prod.snd h
    · intro h; exact Prod.ext (row_line_linear_factor F D a) h
  rw [← he, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  rfl

/-- The row stabilizer of the second marked point is the actual eight-group U₁∩A₁. -/
theorem row_inf_edgeFixer :
    F.row ⊓ edgeFixer G (vertex (rowNormalizer F) 1)
      (vertex (rowNormalizer F) (lineSwap F D : G)) = F.row ⊓ F.plane := by
  ext a
  constructor
  · rintro ⟨ha, he⟩
    exact ⟨ha, (row_line_kernel_iff F D ⟨a, ha⟩).mp
      ((line_edgeFixer_iff F D (inclusion (row_le_line_normalizer F) ⟨a, ha⟩)).mp he)⟩
  · rintro ⟨ha, hp⟩
    exact ⟨ha, (line_edgeFixer_iff F D (inclusion (row_le_line_normalizer F) ⟨a, ha⟩)).mpr
      ((row_line_kernel_iff F D ⟨a, ha⟩).mpr hp)⟩

/-- The full ambient edge fixer preserves its actual line. -/
theorem edgeFixer_le_line :
    edgeFixer G (vertex (rowNormalizer F) 1)
      (vertex (rowNormalizer F) (lineSwap F D : G)) ≤ planeNormalizer F := by
  intro a ha
  have har : a ∈ rowNormalizer F := by
    have hh := ha.1
    change a ∈ MulAction.stabilizer G (vertex (rowNormalizer F) 1) at hh
    rwa [stabilizer_base] at hh
  have hn := inf_normalizer_le_normalizer_inf
    (show a ∈ normalizer (F.row : Set G) ⊓ normalizer
      (edgeFixer G (vertex (rowNormalizer F) 1)
        (vertex (rowNormalizer F) (lineSwap F D : G)) : Set G) from
        ⟨har, le_normalizer ha⟩)
  rw [row_inf_edgeFixer F D, source_row_plane_normalizer] at hn
  exact hn.2

/-- Ordered edges on a specified line have a common marked-edge representative. -/
theorem line_edge_representative {a b : Point F} {l : Line F} (hab : a ≠ b)
    (ha : PointLineIncident F a l) (hb : PointLineIncident F b l) :
    ∃ g : G, g • vertex (rowNormalizer F) 1 = a ∧
      g • vertex (rowNormalizer F) (lineSwap F D : G) = b ∧
      g • vertex (planeNormalizer F) 1 = l := by
  obtain ⟨g, rfl, hg⟩ := ha
  obtain ⟨k, rfl, hk⟩ := hb
  have huL : g⁻¹ * k ∈ planeNormalizer F :=
    (vertex_eq_iff _ _ _).mp (hg.trans hk.symm)
  have huR : g⁻¹ * k ∉ rowNormalizer F :=
    fun h => hab ((vertex_eq_iff _ _ _).mpr h)
  obtain ⟨p, hp, hpR, he⟩ := line_transitive F D _ (lineSwap F D).property
    (lineSwap_not_row F D) _ huL huR
  refine ⟨g * p, ?_, ?_, ?_⟩
  · simpa only [smul_vertex, mul_one] using congrArg (fun a => g • a) hpR
  · simpa only [smul_vertex, mul_assoc, mul_inv_cancel_left] using
      congrArg (fun a => g • a) he
  · rw [smul_vertex, mul_one]
    apply Eq.trans ?_ hg
    symm
    exact (vertex_eq_iff _ _ _).mpr (by simpa using hp)

include D in
/-- Two distinct source points determine at most one actual line coset. -/
theorem line_unique {a b : Point F} {l k : Line F} (hab : a ≠ b)
    (hal : PointLineIncident F a l) (hbl : PointLineIncident F b l)
    (hak : PointLineIncident F a k) (hbk : PointLineIncident F b k) : l = k := by
  obtain ⟨g, hga, hgb, hgl⟩ := line_edge_representative F D hab hal hbl
  obtain ⟨h, hha, hhb, hhk⟩ := line_edge_representative F D hab hak hbk
  have he : g⁻¹ * h ∈ edgeFixer G (vertex (rowNormalizer F) 1)
      (vertex (rowNormalizer F) (lineSwap F D : G)) := by
    constructor
    · change (g⁻¹ * h) • _ = _
      rw [mul_smul, hha, ← hga, inv_smul_smul]
    · change (g⁻¹ * h) • _ = _
      rw [mul_smul, hhb, ← hgb, inv_smul_smul]
  have hl := (vertex_eq_iff (planeNormalizer F) g h).mpr (edgeFixer_le_line F D he)
  simp only [smul_vertex, mul_one] at hgl hhk
  exact hgl.symm.trans (hl.trans hhk)

include D in
/-- Source collinearity retains its unique incident line, with no extra geometry premise. -/
theorem graph_adj_unique_line {a b : Point F} (h : (graph F).Adj a b) :
    ∃! l : Line F, PointLineIncident F a l ∧ PointLineIncident F b l := by
  obtain ⟨hab, l, ha, hb⟩ := h
  exact ⟨l, ⟨ha, hb⟩, fun k hk => line_unique F D hab hk.1 hk.2 ha hb⟩

/-- The ambient edge fixer is exactly the embedded kernel of the literal three-point action. -/
theorem edgeFixer_eq_line_kernel :
    edgeFixer G (vertex (rowNormalizer F) 1)
      (vertex (rowNormalizer F) (lineSwap F D : G)) =
        (lineAction F D).ker.map (planeNormalizer F).subtype := by
  apply le_antisymm
  · intro g hg
    exact ⟨⟨g, edgeFixer_le_line F D hg⟩,
      (line_edgeFixer_iff F D _).mp hg, rfl⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact (line_edgeFixer_iff F D g).mpr hg

/-- The unordered edge stabilizer also lies in the actual line stabilizer. -/
theorem edgeStabilizer_le_line :
    edgeStabilizer G (vertex (rowNormalizer F) 1)
      (vertex (rowNormalizer F) (lineSwap F D : G)) ≤ planeNormalizer F := by
  intro g hg
  rcases hg with hg | hg
  · exact edgeFixer_le_line F D hg
  · have hs := Cosets.swap (rowNormalizer F) (lineSwap F D : G) (lineSwap_square_mem F D)
    have he : g * (lineSwap F D : G) ∈ edgeFixer G (vertex (rowNormalizer F) 1)
        (vertex (rowNormalizer F) (lineSwap F D : G)) := by
      constructor
      · change (g * _) • _ = _
        rw [mul_smul, hs.1, hg.2]
      · change (g * _) • _ = _
        rw [mul_smul, hs.2, hg.1]
    exact (planeNormalizer F).mul_mem_cancel_right (lineSwap F D).property |>.mp
      (edgeFixer_le_line F D he)

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
