module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.HexadControl
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.PointEdge
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.PlaneOrbits

/-!
# Normalizer control for the original point-plane edge subgroup

The same native hexad chart carries the literal plane part of the edge
fixer to the stabilizer of two neighboring hexads. Its only fixed plane
points are the endpoints. An element of I normalizing that subgroup fixes
the first endpoint, so it must fix the second as well. Thus I_y is
self-normalizing in I, the condition used to retain the edge during the
Section 8 overlap correction.

Source: Aschbacher--Segev, Invent. Math. 105 (1991), (8.2), p.606.
All points use the original left cosets and the supplied line and marker.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry LocalGeometry.LocalSubgroups SourceCycleBase GraphUniquenessSystem
open Sporadic.Mathieu
open scoped Pointwise
namespace EdgeControl

variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
variable (a : SourceIncidence.LocalData h)
private def planeVertex (x : centralizer z) :
    {x : Point a.P // OnPlane a.P x (Cosets.vertex (centralizer z) 1)} :=
  ⟨Cosets.vertex a.P.M x,⟨x,rfl,(Cosets.vertex_eq_base _ _).mpr x.property⟩⟩

private theorem planeVertex_fixed (n x : centralizer z) :
    (n : G) • Cosets.vertex a.P.M (x : G)=Cosets.vertex a.P.M (x : G) ↔
      a.designProjection n • (a.planePoints (planeVertex a x)).val =
        (a.planePoints (planeVertex a x)).val := by
  rw [a.planePoints_apply (planeVertex a x) x rfl]
  rw [Cosets.smul_vertex,eq_comm,Cosets.vertex_eq_iff]
  change ((x⁻¹*(n*x) : centralizer z) : G) ∈ a.P.M ↔ _
  rw [a.point_plane_overlap,map_mul,map_mul,map_inv]
  simp only [mul_smul,inv_smul_eq_iff]

/-- The actual plane part of the edge fixer has exactly the two endpoints
as fixed points in its plane. This is the normalizer-control step in (8.2). -/
theorem edgePlane_fixed (t v : centralizer z)
    (ht : (t : G) ∈ a.L.G₂) (hnt : (t : G) ∉ a.P.M)
    (hfix : ∀ b : centralizer z, (b : G) ∈ lineEdgeGroup a t →
      (b : G) • Cosets.vertex a.P.M (v : G)=Cosets.vertex a.P.M (v : G)) :
    Cosets.vertex a.P.M (v : G)=Cosets.vertex a.P.M 1 ∨
      Cosets.vertex a.P.M (v : G)=Cosets.vertex a.P.M (t : G) := by
  have hadj : Adj a.L (planeVertex a 1).val (planeVertex a t).val := by
    refine ⟨?_,Cosets.vertex a.L.G₂ 1,⟨1,rfl,rfl⟩,⟨t,rfl,(Cosets.vertex_eq_base _ _).mpr ht⟩⟩
    exact fun he => hnt ((Cosets.vertex_eq_base _ _).mp he.symm)
  have he := neighbor_fixed (a.planePoints (planeVertex a 1))
    (a.planePoints (planeVertex a t)) (a.planePoints (planeVertex a v))
    ((a.plane_adj_two _ _).mp hadj) (by
      intro g hgA hgB
      obtain ⟨n,hn⟩ := a.designProjection_surjective (M22ValueBound.Concrete.inclusion g)
      have hnA := (planeVertex_fixed a n 1).mpr (by rw [hn]; exact hgA)
      have hnB := (planeVertex_fixed a n t).mpr (by rw [hn]; exact hgB)
      have hnmem : (n : G) ∈ lineEdgeGroup a t := by
        refine ⟨?_,?_⟩
        · exact (Cosets.vertex_eq_base _ _).mp (by simpa only [Cosets.smul_vertex,mul_one,coe_one] using hnA)
        · rw [←Cosets.stabilizer_vertex]
          exact hnB
      have hv := (planeVertex_fixed a n v).mp (hfix n hnmem)
      rw [hn] at hv
      exact hv)
  rcases he with he | he
  · exact Or.inl (congrArg Subtype.val (a.planePoints.injective he))
  · exact Or.inr (congrArg Subtype.val (a.planePoints.injective he))

/-- Inside I=H∩M the actual local edge fixer is self-normalizing. This
retains the original left-coset edge and does not assert automorphism rigidity. -/
theorem edgePlane_normalizer (t : centralizer z)
    (ht : (t : G) ∈ a.L.G₂) (hnt : (t : G) ∉ a.P.M) :
    (a.P.M.subgroupOf (centralizer z)) ⊓
      normalizer ((lineEdgeGroup a t).subgroupOf (centralizer z) : Set (centralizer z)) =
        (lineEdgeGroup a t).subgroupOf (centralizer z) := by
  apply le_antisymm
  · intro n hn
    have hnfix : (n : G) • Cosets.vertex a.P.M 1=Cosets.vertex a.P.M 1 := by
      rw [Cosets.smul_vertex,mul_one]
      exact (Cosets.vertex_eq_base _ _).mpr hn.1
    have hfixed (b : centralizer z) (hb : (b : G) ∈ lineEdgeGroup a t) :
        (b : G) • Cosets.vertex a.P.M ((n*t : centralizer z) : G)=
          Cosets.vertex a.P.M ((n*t : centralizer z) : G) := by
      have hi := (mem_normalizer_iff.mp (inv_mem hn.2) b).mp
        (show b ∈ (lineEdgeGroup a t).subgroupOf (centralizer z) from hb)
      have hi' : ((n⁻¹*b*n : centralizer z) : G) ∈ lineEdgeGroup a t := by
        change ((n⁻¹*b*(n⁻¹)⁻¹ : centralizer z) : G) ∈ lineEdgeGroup a t at hi
        simpa only [inv_inv] using hi
      have hh : ((n⁻¹*b*n : centralizer z) : G) • Cosets.vertex a.P.M (t : G)=
          Cosets.vertex a.P.M (t : G) := by
        have hb' := hi'.2
        rw [←Cosets.stabilizer_vertex] at hb'
        exact hb'
      have he := congrArg ((n : G) • ·) hh
      simpa only [coe_mul,coe_inv,mul_smul,smul_inv_smul,←Cosets.smul_vertex] using he
    rcases edgePlane_fixed a t (n*t) ht hnt hfixed with he | he
    · have hh : (n : G) • Cosets.vertex a.P.M (t : G)=
          (n : G) • Cosets.vertex a.P.M 1 := by
        rw [hnfix,Cosets.smul_vertex]
        exact he
      exact (hnt ((Cosets.vertex_eq_base _ _).mp ((MulAction.injective (n : G)) hh))).elim
    · refine ⟨hn.1,?_⟩
      rw [←Cosets.stabilizer_vertex]
      exact he
  · intro b hb
    exact ⟨hb.1,le_normalizer hb⟩

end EdgeControl
end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
