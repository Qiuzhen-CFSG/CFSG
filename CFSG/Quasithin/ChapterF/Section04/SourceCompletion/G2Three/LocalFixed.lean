module

public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.G2Three.Canonical
public import Theory.Combinatorics.SimpleGraph.FixedNeighbors
public import Theory.GroupAction.DihedralPolygon.FixedHexagon

/-!
# The canonical Weyl rotation fixes the base flag

The four-element neighborhoods at the two base vertices each have exactly
two torus-fixed neighbors. This follows from the actual endpoint maps and
the native torus elements moving a third neighbor. Short geodesic
uniqueness propagates the fixed-point condition. The thin fixed-graph
argument then puts the sixth canonical rotation power in the whole Borel
whenever the completion has hexagon diameter.

Source context: Aschbacher–Smith F.4.16–17 and F.4.26, printed pp.282–283
and 288. The supplied diameter is proved from the original involutions in
`Hexagon.lean`; no apartment or ambient equivalence is an input.
-/

@[expose] public section

open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.G2.Explicit Atlas.SplitOctonion
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.G2Three.Completion
variable {G : Type*} [Group G] (c : Completion G)
local notation "x" => RankTwo.base c.family false
local notation "l" => RankTwo.base c.family true
local notation "A" => c.torus (-1) 1

theorem fixes_base_iff (g : G) (i : Bool) :
    g • RankTwo.base c.family i=RankTwo.base c.family i ↔ g∈c.family i := by
  change g∈stabilizer c.family (RankTwo.base c.family i) ↔ _
  simp only [stabilizer,RankTwo.base,stabilizer_base]

theorem S_fixes : c.S • x=x := (c.fixes_base_iff _ false).mpr ⟨nativeS,rfl⟩
theorem R_fixes : c.R • l=l := (c.fixes_base_iff _ true).mpr ⟨nativeR,rfl⟩
theorem S_moves : c.S • l≠l := by
  intro h
  exact c.S_out (c.overlap ▸
    show c.S∈c.left.range⊓c.right.range from ⟨⟨nativeS,rfl⟩,(c.fixes_base_iff _ true).mp h⟩)
theorem R_moves : c.R • x≠x := by
  intro h
  exact c.R_out (c.overlap ▸
    show c.R∈c.left.range⊓c.right.range from ⟨(c.fixes_base_iff _ false).mp h,⟨nativeR,rfl⟩⟩)

theorem left_conjugate_fixed_iff (u a : parabolic₁ (F := ZMod 3)) :
    c.left a • (c.left u • l)=c.left u • l ↔ (u⁻¹*a*u).val∈borel := by
  have he : c.left a • (c.left u • l)=c.left u • l ↔
      c.left (u⁻¹*a*u) • l=l := by
    constructor
    · intro h
      simpa only [map_mul,map_inv,SemigroupAction.mul_smul,inv_smul_smul] using congrArg ((c.left u)⁻¹ • ·) h
    · intro h
      simpa only [map_mul,map_inv,SemigroupAction.mul_smul,smul_inv_smul] using congrArg (c.left u • ·) h
  rw [he,c.fixes_base_iff]
  constructor
  · intro h
    apply (c.left_mem_middle_iff _).mp
    exact c.overlap ▸ show c.left (u⁻¹*a*u)∈c.left.range⊓c.right.range from ⟨⟨_,rfl⟩,h⟩
  · intro h
    exact c.middle_le_right ((c.left_mem_middle_iff _).mpr h)

theorem right_conjugate_fixed_iff (u a : parabolic₂ (F := ZMod 3)) :
    c.right a • (c.right u • x)=c.right u • x ↔ (u⁻¹*a*u).val∈borel := by
  have he : c.right a • (c.right u • x)=c.right u • x ↔
      c.right (u⁻¹*a*u) • x=x := by
    constructor
    · intro h
      simpa only [map_mul,map_inv,SemigroupAction.mul_smul,inv_smul_smul] using congrArg ((c.right u)⁻¹ • ·) h
    · intro h
      simpa only [map_mul,map_inv,SemigroupAction.mul_smul,smul_inv_smul] using congrArg (c.right u • ·) h
  rw [he,c.fixes_base_iff]
  constructor
  · intro h
    apply (c.right_mem_middle_iff _).mp
    exact c.overlap ▸ show c.right (u⁻¹*a*u)∈c.left.range⊓c.right.range from ⟨h,⟨_,rfl⟩⟩
  · intro h
    exact c.middle_le_left ((c.right_mem_middle_iff _).mpr h)

private theorem base_adj : c.graph.Adj x l :=
  ⟨Bool.false_ne_true,incident_base c.family false true⟩

theorem fixed_neighbors_left (v : c.Vertex) (hv : c.graph.Adj x v) (hQ : c.TorusFixed v) :
    v=l ∨ v=c.S • l := by
  have hAx := (c.torus_fixed_base false).1
  have hAy := (c.torus_fixed_base true).1
  have hAz := ((c.torus_fixed_S l).mpr (c.torus_fixed_base true)).1
  let u := TernaryTorus.shortMover
  have hu : c.left u • x=x := (c.fixes_base_iff _ false).mpr ⟨u,rfl⟩
  have hm : A • (c.left u • l)≠c.left u • l := by
    intro h
    have hh := (c.left_conjugate_fixed_iff u
      ⟨TernaryTorus.a,borel_le_parabolic₁ (mem_sup_right ⟨(-1,1),rfl⟩)⟩).mp h
    exact TernaryTorus.shortMover_not_fixed hh
  apply SimpleGraph.fixed_neighbors_of_four (translationGraphIso c.family A)
    (c.card_neighbors x) hAx (base_adj c)
    (by simpa only [c.S_fixes] using c.graphAction.map_adj c.S (base_adj c))
    (by simpa only [hu] using c.graphAction.map_adj (c.left u) (base_adj c))
    hAy hAz (Ne.symm c.S_moves) hm hv hQ.1

theorem fixed_neighbors_right (v : c.Vertex) (hv : c.graph.Adj l v) (hQ : c.TorusFixed v) :
    v=x ∨ v=c.R • x := by
  have hAx := (c.torus_fixed_base true).1
  have hAy := (c.torus_fixed_base false).1
  have hAz := ((c.torus_fixed_R x).mpr (c.torus_fixed_base false)).1
  let u := TernaryTorus.longMover
  have hu : c.right u • l=l := (c.fixes_base_iff _ true).mpr ⟨u,rfl⟩
  have hm : A • (c.right u • x)≠c.right u • x := by
    intro h
    have he := c.right_torus (-1) 1
    have hh := (c.right_conjugate_fixed_iff u
      ⟨TernaryTorus.a,borel_le_parabolic₂ (mem_sup_right ⟨(-1,1),rfl⟩)⟩).mp
      (by change c.right ⟨Atlas.G2.torus (-1) 1,_⟩ • _=_; rw [c.right_torus]; exact h)
    exact TernaryTorus.longMover_not_fixed hh
  apply SimpleGraph.fixed_neighbors_of_four (translationGraphIso c.family A)
    (c.card_neighbors l) hAx (base_adj c).symm
    (by simpa only [c.R_fixes] using c.graphAction.map_adj c.R (base_adj c).symm)
    (by simpa only [hu] using c.graphAction.map_adj (c.right u) (base_adj c).symm)
    hAy hAz (Ne.symm c.R_moves) hm hv hQ.1

/-- The original hexagon diameter forces the canonical Weyl rotation to fix the base flag. -/
theorem rotation_six_mem_middle (hdiam : ∀v w,c.graph.dist v w≤6) :
    (c.R*c.S)^6∈c.middle.range := by
  have hh := GroupAction.DihedralPolygon.fixed_edge_sequence_closes c.bipartiteAction
    c.S c.R x l c.S_sq c.R_sq c.S_fixes c.R_fixes (base_adj c)
    c.S_moves c.R_moves c.connected hdiam c.cycle_length_ge_twelve
    c.TorusFixed (c.torus_fixed_base false) (c.torus_fixed_base true)
    c.torus_fixed_S c.torus_fixed_R c.fixed_neighbors_left c.fixed_neighbors_right
    (by
      intro v w p hp hl hv hw u hu
      exact ⟨SimpleGraph.short_geodesic_fixed c.cycle_length_ge_twelve c.graphAction
        p hp hl _ hv.1 hw.1 u hu,
        SimpleGraph.short_geodesic_fixed c.cycle_length_ge_twelve c.graphAction
        p hp hl _ hv.2 hw.2 u hu⟩)
  exact c.overlap ▸ show (c.R*c.S)^6∈c.left.range⊓c.right.range from
    ⟨(c.fixes_base_iff _ false).mp hh.1,(c.fixes_base_iff _ true).mp hh.2⟩
end CFSG.Quasithin.ChapterF.SourceCompletion.G2Three.Completion
