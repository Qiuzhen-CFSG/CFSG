module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.EdgeRigidity
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.NativePlaneEdge
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.AlignPlaneGroup

/-!
# Aligning the source plane map with the full native setwise edge

The tensor quotient gives the source edge fixer order 10752. Its plane
intersection has index seven and thus order 1536. A point-flag comparison
transports this literal intersection to the common fixer of the native first
octad and the image of the source plane reversal. The native six-column
criterion forces those octads to be adjacent. Conjugating the plane map
inside the point stabilizer aligns the second endpoint, while preserving the
common four and the full action kernel. Equality of the original point
cosets then proves preservation of the entire setwise edge, including its
reversing elements.

The final application uses the same oriented marking and local data from
`SourceData.ofFusion` inside the normalizer span. This discharges the plane
edge-alignment step of Aschbacher, *Sporadic Groups* (1994), 41.4, p.222.
Agreement of the two local maps on the full overlap and the source 41.2
ambient generation remain separate obligations.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer
open GraphUniquenessSystem GraphUniquenessSystem.Cosets
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24ChapterHStabilizers
open PairOvergroups
variable {G : Type*} [Group G] [Finite G] {z : G}
  (F : MarkedCentralizer z) (D : LocalData F)

/-- The full source edge fixer has order 2^6 · 168. -/
theorem edgeGroup_card : Nat.card (edgeGroup F D) = 10752 := by
  have hc := (F.plane.subgroupOf (edgeGroup F D)).card_mul_index
  have hA : Nat.card (F.plane.subgroupOf (edgeGroup F D)) = 64 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (rectangle_le_edgeGroup F D)).toEquiv,
      source_plane_card]
  have hq : (F.plane.subgroupOf (edgeGroup F D)).index = 168 := by
    change Nat.card (edgeGroup F D ⧸ F.plane.subgroupOf (edgeGroup F D)) = _
    rw [Nat.card_congr (edgeQuotientEquiv F D).toEquiv]
    exact BinaryLinear.FourParabolicAction.card_GL_three (by simp)
  rw [hA,hq] at hc
  exact hc.symm

/-- The literal plane–edge fixer has order 1536. This determines the
six-neighbor orbit in the actual fifteen-point plane action. -/
theorem plane_edgeGroup_card :
    Nat.card ((edgeGroup F D).subgroupOf (threeSpaceNormalizer F)) = 1536 := by
  have hc := ((threeSpaceNormalizer F).subgroupOf (edgeGroup F D)).card_mul_index
  change Nat.card ((threeSpaceNormalizer F).subgroupOf (edgeGroup F D)) *
    (threeSpaceNormalizer F).relIndex (edgeGroup F D) = _ at hc
  rw [edge_plane_index F D,edgeGroup_card F D] at hc
  have h1 := card_map_of_injective
    (K := (threeSpaceNormalizer F).subgroupOf (edgeGroup F D))
    (edgeGroup F D).subtype_injective
  have h2 := card_map_of_injective
    (K := (edgeGroup F D).subgroupOf (threeSpaceNormalizer F))
    (threeSpaceNormalizer F).subtype_injective
  rw [subgroupOf_map_subtype] at h1 h2
  rw [inf_comm] at h1
  omega



omit D [Finite G] in
/-- A point-flag comparison identifies equality of the actual ambient point
cosets with equality of the corresponding native octads. -/
theorem plane_equiv_coset_eq_iff
    (e : threeSpaceNormalizer F ≃* sextetStabilizer standardSextet)
    (hf : ∀ n : threeSpaceNormalizer F, (n : G) ∈ rowNormalizer F ↔
      (e n : M24) ∈ octadStabilizer OctadGraph.first)
    (a b : threeSpaceNormalizer F) :
    vertex (rowNormalizer F) (a : G) = vertex (rowNormalizer F) (b : G) ↔
      (e a : M24) • OctadGraph.first = (e b : M24) • OctadGraph.first := by
  rw [vertex_eq_iff]
  change ((a⁻¹ * b : threeSpaceNormalizer F) : G) ∈ rowNormalizer F ↔ _
  rw [hf, ← stabilizer_octad]
  change (e (a⁻¹ * b) : M24) • OctadGraph.first = OctadGraph.first ↔ _
  rw [map_mul,map_inv,Subgroup.coe_mul,Subgroup.coe_inv,mul_smul,inv_smul_eq_iff,eq_comm]

/-- The original source edge is transported to the first octad and the image
of its chosen plane reversal, without assuming that image is adjacent. -/
theorem plane_equiv_edgeFixer
    (e : threeSpaceNormalizer F ≃* sextetStabilizer standardSextet)
    (hf : ∀ n : threeSpaceNormalizer F, (n : G) ∈ rowNormalizer F ↔
      (e n : M24) ∈ octadStabilizer OctadGraph.first) :
    ((edgeGroup F D).subgroupOf (threeSpaceNormalizer F)).map e.toMonoidHom =
      (octadStabilizer OctadGraph.first ⊓
        octadStabilizer ((e ⟨planeSwap F D,planeSwap_mem F D⟩ : M24) • OctadGraph.first)).subgroupOf
          (sextetStabilizer standardSextet) := by
  let t : threeSpaceNormalizer F := ⟨planeSwap F D,planeSwap_mem F D⟩
  have hmem (n : threeSpaceNormalizer F) : (n : G) ∈ edgeGroup F D ↔
      (e n : M24) ∈ octadStabilizer OctadGraph.first ∧
      (e n : M24) ∈ octadStabilizer ((e t : M24) • OctadGraph.first) := by
    change (n : G) ∈ MulAction.stabilizer G (vertex (rowNormalizer F) 1) ∧
      (n : G) ∈ MulAction.stabilizer G (vertex (rowNormalizer F) (lineSwap F D : G)) ↔ _
    rw [stabilizer_base,← planeSwap_vertex F D]
    refine and_congr (hf n) ?_
    rw [MulAction.mem_stabilizer_iff,← stabilizer_octad,MulAction.mem_stabilizer_iff,
      smul_vertex]
    have h := plane_equiv_coset_eq_iff F e hf (n*t) t
    simpa only [map_mul,Subgroup.coe_mul,mul_smul] using h
  ext m
  constructor
  · rintro ⟨n,hn,rfl⟩
    exact (hmem n).mp hn
  · intro hm
    refine ⟨e.symm m,(hmem (e.symm m)).mpr ?_,e.apply_symm_apply m⟩
    simpa only [e.apply_symm_apply] using (show
      (m : M24) ∈ octadStabilizer OctadGraph.first ∧
      (m : M24) ∈ octadStabilizer ((e t : M24) • OctadGraph.first) from hm)

/-- The image of the chosen source reversal gives an actual adjacent octad,
so it can be aligned inside the native point stabilizer. -/
theorem plane_equiv_exists_edge_correction
    (e : threeSpaceNormalizer F ≃* sextetStabilizer standardSextet)
    (hf : ∀ n : threeSpaceNormalizer F, (n : G) ∈ rowNormalizer F ↔
      (e n : M24) ∈ octadStabilizer OctadGraph.first) :
    ∃ k : sextetStabilizer standardSextet,
      (k : M24) • OctadGraph.first = OctadGraph.first ∧
      (k : M24) • ((e ⟨planeSwap F D,planeSwap_mem F D⟩ : M24) • OctadGraph.first) =
        OctadGraph.second := by
  apply OctadGraph.NativePlaneEdge.exists_edge_correction
  rw [← plane_equiv_edgeFixer F D e hf,card_map_of_injective e.injective]
  exact plane_edgeGroup_card F D



/-- Once the two actual endpoints are aligned, the same map preserves the
full local setwise edge, including its reversing coset. -/
theorem plane_equiv_edgeStabilizer
    (e : threeSpaceNormalizer F ≃* sextetStabilizer standardSextet)
    (hf : ∀ n : threeSpaceNormalizer F, (n : G) ∈ rowNormalizer F ↔
      (e n : M24) ∈ octadStabilizer OctadGraph.first)
    (ht : (e ⟨planeSwap F D,planeSwap_mem F D⟩ : M24) • OctadGraph.first = OctadGraph.second)
    (n : threeSpaceNormalizer F) :
    (n : G) ∈ edgeStabilizer G (vertex (rowNormalizer F) 1)
      (vertex (rowNormalizer F) (lineSwap F D : G)) ↔
        (e n : M24) ∈ OctadGraph.system.edgeSetGroup := by
  let t : threeSpaceNormalizer F := ⟨planeSwap F D,planeSwap_mem F D⟩
  have h1 := plane_equiv_coset_eq_iff F e hf n 1
  have h2 := plane_equiv_coset_eq_iff F e hf (n*t) t
  have h3 := plane_equiv_coset_eq_iff F e hf n t
  have h4 := plane_equiv_coset_eq_iff F e hf (n*t) 1
  change (e t : M24) • OctadGraph.first = OctadGraph.second at ht
  simp only [map_one,map_mul,Subgroup.coe_one,Subgroup.coe_mul,mul_smul,one_smul,ht] at h1 h2 h3 h4
  change (((n : G) • vertex (rowNormalizer F) 1 = vertex (rowNormalizer F) 1 ∧
      (n : G) • vertex (rowNormalizer F) (lineSwap F D : G) = vertex (rowNormalizer F) (lineSwap F D : G)) ∨
    ((n : G) • vertex (rowNormalizer F) 1 = vertex (rowNormalizer F) (lineSwap F D : G) ∧
      (n : G) • vertex (rowNormalizer F) (lineSwap F D : G) = vertex (rowNormalizer F) 1)) ↔ _
  rw [← planeSwap_vertex F D]
  simp only [smul_vertex,mul_one]
  exact or_congr (and_congr h1 h2) (and_congr h3 h4)

/-- The actual plane map preserves the common four, the plane-action kernel,
the point flag and the entire setwise edge. The adjustment takes place
inside the actual native point–plane group. -/
theorem exists_native_plane_marked_edge_flag_equiv :
    ∃ e : threeSpaceNormalizer F ≃* sextetStabilizer standardSextet,
      ((F.row ⊓ F.threeSpace).subgroupOf (threeSpaceNormalizer F)).map
        ((sextetStabilizer standardSextet).subtype.comp e.toMonoidHom) = CommonPlane.common ∧
      (planePointAction F).ker.map e.toMonoidHom = SextetCore.columnHom.ker ∧
      (∀ n : threeSpaceNormalizer F, (n : G) ∈ rowNormalizer F ↔
        (e n : M24) ∈ octadStabilizer OctadGraph.first) ∧
      (e ⟨planeSwap F D,planeSwap_mem F D⟩ : M24) • OctadGraph.first = OctadGraph.second ∧
      (∀ n : threeSpaceNormalizer F,
        (n : G) ∈ edgeStabilizer G (vertex (rowNormalizer F) 1)
          (vertex (rowNormalizer F) (lineSwap F D : G)) ↔
            (e n : M24) ∈ OctadGraph.system.edgeSetGroup) := by
  obtain ⟨e,hc,hker⟩ := exists_native_plane_common_equiv F D
  have hf (n : threeSpaceNormalizer F) : (n : G) ∈ rowNormalizer F ↔
      (e n : M24) ∈ octadStabilizer OctadGraph.first := by
    rw [OctadGraph.NativePlane.first_eq_standardOctad]
    exact native_plane_equiv_point_flag F D e hc n
  obtain ⟨k,hkx,hky⟩ := plane_equiv_exists_edge_correction F D e hf
  let e' := e.trans (MulAut.conj k)
  have hcommon : ((F.row ⊓ F.threeSpace).subgroupOf (threeSpaceNormalizer F)).map
      ((sextetStabilizer standardSextet).subtype.comp e'.toMonoidHom) = CommonPlane.common := by
    have hm : ((sextetStabilizer standardSextet).subtype.comp e'.toMonoidHom) =
        (MulAut.conj (k : M24)).toMonoidHom.comp
          ((sextetStabilizer standardSextet).subtype.comp e.toMonoidHom) := by
      ext n
      rfl
    rw [hm,← map_map,hc]
    apply mem_normalizer_iff_map_conj_eq.mp
    apply (native_normalizes_common_iff k).mpr
    rw [← OctadGraph.NativePlane.first_eq_standardOctad,← stabilizer_octad]
    exact hkx
  have hkernel : (planePointAction F).ker.map e'.toMonoidHom = SextetCore.columnHom.ker := by
    change (planePointAction F).ker.map ((MulAut.conj k).toMonoidHom.comp e.toMonoidHom) = _
    rw [← map_map,hker]
    exact mem_normalizer_iff_map_conj_eq.mp
      (show k ∈ normalizer (SextetCore.columnHom.ker : Set (sextetStabilizer standardSextet)) by
        rw [normalizer_eq_top]
        trivial)
  have hflag (n : threeSpaceNormalizer F) : (n : G) ∈ rowNormalizer F ↔
      (e' n : M24) ∈ octadStabilizer OctadGraph.first := by
    rw [OctadGraph.NativePlane.first_eq_standardOctad]
    exact native_plane_equiv_point_flag F D e' hcommon n
  have hsecond : (e' ⟨planeSwap F D,planeSwap_mem F D⟩ : M24) • OctadGraph.first = OctadGraph.second := by
    have hki : (k : M24)⁻¹ • OctadGraph.first = OctadGraph.first := by
      rw [inv_smul_eq_iff,hkx]
    change ((k : M24) * (e ⟨planeSwap F D,planeSwap_mem F D⟩ : M24) * (k : M24)⁻¹) •
      OctadGraph.first = _
    rw [mul_smul,mul_smul,hki]
    exact hky
  exact ⟨e',hcommon,hkernel,hflag,hsecond,plane_equiv_edgeStabilizer F D e' hflag hsecond⟩

/-- The complete plane-side comparison on the literal source and native
uniqueness systems. Agreement with the vertex map is still separate. -/
theorem exists_native_local_edge_flag_equiv
    (hgen : threeSpaceNormalizer F ⊔ rowNormalizer F = ⊤) :
    ∃ e : (system_of_generation F D hgen).H ≃* OctadGraph.system.H,
      (∀ n : (system_of_generation F D hgen).H,
        (n : G) ∈ (system_of_generation F D hgen).vertexGroup ↔
          (e n : M24) ∈ OctadGraph.system.vertexGroup) ∧
      (∀ n : (system_of_generation F D hgen).H,
        (n : G) ∈ (system_of_generation F D hgen).edgeSetGroup ↔
          (e n : M24) ∈ OctadGraph.system.edgeSetGroup) ∧
      (planePointAction F).ker.map e.toMonoidHom = SextetCore.columnHom.ker := by
  obtain ⟨e,_,hk,hf,_,he⟩ := exists_native_plane_marked_edge_flag_equiv F D
  refine ⟨e,?_,he,hk⟩
  intro n
  change (n : G) ∈ MulAction.stabilizer G (vertex (rowNormalizer F) 1) ↔ _
  rw [stabilizer_base,OctadGraph.system_vertex]
  exact hf n

/-- Original-fusion consumer: the same oriented normalizer-span system now
has its plane map preserving both the point flag and the full setwise edge. -/
theorem oriented_normalizerSpan_local_edge_flag_equiv (hfusion : F.MathieuFusion) :
    let E := SourceData.ofFusion F hfusion
    let U := normalizerSpan_system E.oriented.marking E.localData
    ∃ e : U.H ≃* OctadGraph.system.H,
      (∀ n : U.H, (n : normalizerSpan E.oriented.marking) ∈ U.vertexGroup ↔
        (e n : M24) ∈ OctadGraph.system.vertexGroup) ∧
      (∀ n : U.H, (n : normalizerSpan E.oriented.marking) ∈ U.edgeSetGroup ↔
        (e n : M24) ∈ OctadGraph.system.edgeSetGroup) ∧
      (planePointAction (normalizerSpanMarking E.oriented.marking)).ker.map e.toMonoidHom =
        SextetCore.columnHom.ker := by
  let E := SourceData.ofFusion F hfusion
  exact exists_native_local_edge_flag_equiv (normalizerSpanMarking E.oriented.marking)
    (normalizerSpanLocalData E.oriented.marking E.localData)
    (normalizerSpan_pair_generate E.oriented.marking E.localData)

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
