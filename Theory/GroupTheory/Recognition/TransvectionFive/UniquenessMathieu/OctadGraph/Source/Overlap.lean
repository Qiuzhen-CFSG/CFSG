module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.AlignPlaneEdge
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.AlignEdge

/-!
# Correcting the full overlap of the two Mathieu local maps

The row kernel meets the plane–edge fixer in the same common eight as the
full edge fixer. Its ambient normalizer recovers the point–line flag, so
an element of the vertex group normalizing the local edge fixer also
normalizes the full edge fixer. Both constructed local maps preserve the
pointwise local edge, so their restrictions to the full point–plane group
differ by an automorphism preserving this subgroup.

If every automorphism of that point–plane group is inner, conjugation by
the corresponding source element corrects the vertex map on the entire
overlap. The normalizer implication ensures its edge clause survives. This
constructs an actual `GraphUniquenessSystem.Similarity`, and the existing
rigidity and native cycle-base consumer recognize the oriented normalizer
span as M₂₄.

This is the compatibility argument of Aschbacher, *Sporadic Groups* (1994),
41.4, p.222, with source 41.3's inner-automorphism assertion still explicit.
It is a conditional comparison, not a proof of 41.3 or of the original
ambient-generation claim in 41.2. Both remain with the source assembly.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer
open GraphUniquenessSystem GraphUniquenessSystem.Cosets
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open PairOvergroups
variable {G : Type*} [Group G] [Finite G] {z : G}
  (F : MarkedCentralizer z) (D : LocalData F)

/-- Intersecting the local edge fixer with the row kernel recovers the
same literal common eight as the full edge fixer. -/
theorem row_inf_plane_edge :
    F.row ⊓ (threeSpaceNormalizer F ⊓ edgeGroup F D) = F.row ⊓ F.plane := by
  apply le_antisymm
  · intro a ha
    have hh : a ∈ F.row ⊓ edgeGroup F D := ⟨ha.1,ha.2.2⟩
    rw [row_inf_edgeFixer F D] at hh
    exact hh
  · intro a ha
    have hh : a ∈ F.row ⊓ edgeGroup F D := by rwa [row_inf_edgeFixer F D]
    exact ⟨ha.1,rectangle_le_plane_normalizer F D ha.2,hh.2⟩

/-- The normalizer implication used in source Hypothesis V(4): an element of the point stabilizer normalizing
the local edge fixer normalizes the full ambient edge fixer. The common
eight recovers the actual point–line flag. -/
theorem normalizes_local_edge_implies_full (g : rowNormalizer F)
    (hg : (g : G) ∈ normalizer ((threeSpaceNormalizer F ⊓ edgeGroup F D : Subgroup G) : Set G)) :
    (g : G) ∈ normalizer (edgeGroup F D : Set G) := by
  have hi := inf_normalizer_le_normalizer_inf ⟨g.property,hg⟩
  rw [row_inf_plane_edge F D,source_row_plane_normalizer] at hi
  have hh : (g : G) ∈ rowNormalizer F ⊓ planeNormalizer F := hi
  rw [← edgeGroup_normalizer_in_row F D] at hh
  exact hh.2

private def restrictInf {A B : Type*} [Group A] [Group B]
    {H K : Subgroup A} {H' K' : Subgroup B} (e : H ≃* H')
    (he : ∀ h : H, (h : A) ∈ K ↔ (e h : B) ∈ K') :
    ↥(H ⊓ K) ≃* ↥(H' ⊓ K') where
  toFun a := ⟨e ⟨a,a.property.1⟩,(e _).property,(he _).mp a.property.2⟩
  invFun a := ⟨e.symm ⟨a,a.property.1⟩,(e.symm _).property,
    (he _).mpr (by simpa only [e.apply_symm_apply] using (show (a : B) ∈ K' from a.property.2))⟩
  left_inv a := by
    apply Subtype.ext
    exact congrArg (fun b : H => (b : A)) (e.symm_apply_apply ⟨a,a.property.1⟩)
  right_inv a := by
    apply Subtype.ext
    exact congrArg (fun b : H' => (b : B)) (e.apply_symm_apply ⟨a,a.property.1⟩)
  map_mul' a b := by
    apply Subtype.ext
    exact congrArg (fun b : H' => (b : B)) (e.map_mul ⟨a,a.property.1⟩ ⟨b,b.property.1⟩)

private theorem edge_iff_vertex_setwise {A X : Type*} [Group A] [MulAction A X]
    (x y : X) (hxy : x ≠ y) (a : A) :
    a ∈ edgeFixer A x y ↔ a ∈ MulAction.stabilizer A x ∧ a ∈ edgeStabilizer A x y := by
  constructor
  · intro ha
    exact ⟨ha.1,Or.inl ha⟩
  · rintro ⟨ha,hb|hb⟩
    · exact hb
    · exact False.elim (hxy ((show a • x = x from ha).symm.trans hb.1))

/-- The plane-side comparison also preserves the pointwise local edge,
by combining its point flag and setwise-edge clauses. -/
theorem plane_equiv_pointwise_edge
    (e : threeSpaceNormalizer F ≃* sextetStabilizer standardSextet)
    (hf : ∀ n : threeSpaceNormalizer F, (n : G) ∈ rowNormalizer F ↔
      (e n : M24) ∈ octadStabilizer OctadGraph.first)
    (he : ∀ n : threeSpaceNormalizer F,
      (n : G) ∈ edgeStabilizer G (vertex (rowNormalizer F) 1)
        (vertex (rowNormalizer F) (lineSwap F D : G)) ↔
          (e n : M24) ∈ OctadGraph.system.edgeSetGroup) (n : threeSpaceNormalizer F) :
    (n : G) ∈ edgeGroup F D ↔ (e n : M24) ∈ OctadGraph.system.edgeGroup := by
  rw [edgeGroup,edge_iff_vertex_setwise _ _ (graph_adj_base F D).ne,stabilizer_base]
  change _ ↔ (e n : M24) ∈ edgeFixer M24 OctadGraph.first OctadGraph.second
  rw [edge_iff_vertex_setwise _ _ OctadGraph.first_adj_second.ne,stabilizer_octad]
  exact and_congr (hf n) (he n)



private theorem exists_compatible_vertex_equiv
    {G' : Type*} [Group G'] (P' H' E' : Subgroup G')
    (v : rowNormalizer F ≃* P')
    (hvH : ∀ a : rowNormalizer F, (a : G) ∈ threeSpaceNormalizer F ↔
      (v a : G') ∈ H')
    (hvE : ∀ a : rowNormalizer F, (a : G) ∈ edgeGroup F D ↔
      (v a : G') ∈ E')
    (e : threeSpaceNormalizer F ≃* H')
    (heV : ∀ n : threeSpaceNormalizer F, (n : G) ∈ rowNormalizer F ↔
      (e n : G') ∈ P')
    (heE : ∀ n : threeSpaceNormalizer F,
      (n : G) ∈ edgeGroup F D ↔ (e n : G') ∈ E')
    (hinner : Function.Surjective
      (MulAut.conj : ↥(rowNormalizer F ⊓ threeSpaceNormalizer F) →*
        MulAut ↥(rowNormalizer F ⊓ threeSpaceNormalizer F))) :
    ∃ v' : rowNormalizer F ≃* P',
      (∀ a : rowNormalizer F, (a : G) ∈ edgeGroup F D ↔
        (v' a : G') ∈ E') ∧
      (∀ a : ↥(rowNormalizer F ⊓ threeSpaceNormalizer F),
        (v' ⟨a,a.property.1⟩ : G') = (e ⟨a,a.property.2⟩ : G')) := by
  let I := rowNormalizer F ⊓ threeSpaceNormalizer F
  let vr := restrictInf v hvH
  let er : I ≃* ↥(P' ⊓ H') :=
    (MulEquiv.subgroupCongr (inf_comm _ _)).trans
      ((restrictInf e heV).trans (MulEquiv.subgroupCongr (inf_comm _ _)))
  obtain ⟨c,hc⟩ := hinner (vr.trans er.symm)
  have hrel (a : I) :
      (v ⟨a,a.property.1⟩ : G') =
        (e ⟨(c*a*c⁻¹ : I),(c*a*c⁻¹ : I).property.2⟩ : G') := by
    have hh := congrArg (fun f : MulAut I => er (f a)) hc
    change er (MulAut.conj c a) = er (er.symm (vr a)) at hh
    rw [er.apply_symm_apply] at hh
    exact (congrArg Subtype.val hh).symm
  have hd (a : I) : (a : G) ∈ edgeGroup F D ↔
      ((c*a*c⁻¹ : I) : G) ∈ edgeGroup F D := by
    rw [hvE ⟨a,a.property.1⟩,
      heE ⟨(c*a*c⁻¹ : I),(c*a*c⁻¹ : I).property.2⟩,
      hrel a]
  have hER : edgeGroup F D ≤ rowNormalizer F := by
    intro a ha
    have hh := ha.1
    rwa [stabilizer_base] at hh
  have hnc : (c : G) ∈ normalizer ((threeSpaceNormalizer F ⊓ edgeGroup F D : Subgroup G) : Set G) := by
    apply mem_normalizer_iff.mpr
    intro a
    constructor
    · intro ha
      let b : I := ⟨a,hER ha.2,ha.1⟩
      exact ⟨(mem_normalizer_iff.mp ((threeSpaceNormalizer F).le_normalizer c.property.2) a).mp ha.1,
        (hd b).mp ha.2⟩
    · intro ha
      have hH : a ∈ threeSpaceNormalizer F :=
        (mem_normalizer_iff.mp ((threeSpaceNormalizer F).le_normalizer c.property.2) a).mpr ha.1
      have hR : a ∈ rowNormalizer F :=
        (mem_normalizer_iff.mp ((rowNormalizer F).le_normalizer c.property.1) a).mpr (hER ha.2)
      exact ⟨hH,(hd ⟨a,hR,hH⟩).mpr ha.2⟩
  have hnE := normalizes_local_edge_implies_full F D ⟨c,c.property.1⟩ hnc
  let cr : rowNormalizer F := ⟨c,c.property.1⟩
  let v' := (MulAut.conj cr⁻¹).trans v
  have hv'E (a : rowNormalizer F) : (a : G) ∈ edgeGroup F D ↔
      (v' a : G') ∈ E' := by
    exact (mem_normalizer_iff.mp ((normalizer (edgeGroup F D : Set G)).inv_mem hnE)
      (a : G)).trans (hvE (MulAut.conj cr⁻¹ a))
  have hagree (a : I) : (v' ⟨a,a.property.1⟩ : G') = (e ⟨a,a.property.2⟩ : G') := by
    have hh := hrel (c⁻¹*a*c)
    have heq : c*(c⁻¹*a*c)*c⁻¹ = a := by group
    change (v (cr⁻¹ * ⟨a,a.property.1⟩ * (cr⁻¹)⁻¹) : G') = _
    rw [inv_inv]
    have harg : cr⁻¹ * ⟨a,a.property.1⟩ * cr =
        (⟨(c⁻¹*a*c : I),(c⁻¹*a*c : I).property.1⟩ : rowNormalizer F) := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul,Subgroup.coe_inv,cr]
    rw [harg]
    simpa only [heq] using hh
  exact ⟨v',hv'E,hagree⟩

/-- The full compatibility step: the source assertion that every automorphism
of the point–plane intersection is inner corrects the vertex map. The
normalizer clause above ensures that the correction preserves the full edge.
This retains source 41.3 explicitly; it does not assert its proof. -/
theorem native_similarity_of_inner_point_plane
    (hgen : threeSpaceNormalizer F ⊔ rowNormalizer F = ⊤)
    (hinner : Function.Surjective
      (MulAut.conj : ↥(rowNormalizer F ⊓ threeSpaceNormalizer F) →*
        MulAut ↥(rowNormalizer F ⊓ threeSpaceNormalizer F))) :
    Nonempty (Similarity (system_of_generation F D hgen) OctadGraph.system) := by
  obtain ⟨v,hvH,_,hvE⟩ := exists_native_row_edge_flag_equiv F D
  obtain ⟨e,_,_,heV,_,heE⟩ := exists_native_plane_marked_edge_flag_equiv F D
  obtain ⟨v',hv'E,hagree⟩ := exists_compatible_vertex_equiv F D
    (octadStabilizer OctadGraph.first) (sextetStabilizer standardSextet)
    OctadGraph.system.edgeGroup v hvH hvE e heV
    (plane_equiv_pointwise_edge F D e heV heE) hinner
  let sourceVertex : (system_of_generation F D hgen).vertexGroup ≃* rowNormalizer F :=
    MulEquiv.subgroupCongr (stabilizer_base _)
  let nativeVertex : OctadGraph.system.vertexGroup ≃* octadStabilizer OctadGraph.first :=
    MulEquiv.subgroupCongr OctadGraph.system_vertex
  refine ⟨{
    vertexIso := sourceVertex.trans (v'.trans nativeVertex.symm)
    localIso := e
    agree := ?_
    local_vertex := ?_
    edge := ?_
    local_edge := heE }⟩
  · intro a haH haV
    exact hagree ⟨a,(sourceVertex ⟨a,haV⟩).property,haH⟩
  · intro n
    change (n : G) ∈ MulAction.stabilizer G (vertex (rowNormalizer F) 1) ↔ _
    rw [stabilizer_base,OctadGraph.system_vertex]
    exact heV n
  · intro a
    exact hv'E (sourceVertex a)

/-- Recognition of the correctly oriented normalizer span now requires only
the remaining source 41.3 inner-automorphism assertion for its full overlap.
The original ambient-generation obligation is not discharged by this result. -/
theorem oriented_normalizerSpan_equiv_of_inner_point_plane (hfusion : F.MathieuFusion)
    (hinner : let E := SourceData.ofFusion F hfusion
      let F' := normalizerSpanMarking E.oriented.marking
      Function.Surjective (MulAut.conj : ↥(rowNormalizer F' ⊓ threeSpaceNormalizer F') →*
        MulAut ↥(rowNormalizer F' ⊓ threeSpaceNormalizer F'))) :
    let E := SourceData.ofFusion F hfusion
    Nonempty (normalizerSpan E.oriented.marking ≃* M24) := by
  let E := SourceData.ofFusion F hfusion
  obtain ⟨s⟩ := native_similarity_of_inner_point_plane (normalizerSpanMarking E.oriented.marking)
    (normalizerSpanLocalData E.oriented.marking E.localData)
    (normalizerSpan_pair_generate E.oriented.marking E.localData) hinner
  obtain ⟨e,_,_⟩ := normalizerSpan_existsUnique_mulEquiv_of_similarity
    E.oriented.marking E.localData s
  exact ⟨e⟩

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
