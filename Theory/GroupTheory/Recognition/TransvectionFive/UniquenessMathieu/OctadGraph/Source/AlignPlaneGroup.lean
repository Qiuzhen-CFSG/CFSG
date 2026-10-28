module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.PlaneCommonFour
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.NativePlane

/-!
# Aligning the actual native plane map with the point flag

The source common four has already been identified with the native double-zero
subgroup of a column pair. Transitivity on pairs supplies a conjugator inside
the actual native sextet stabilizer carrying it to the marked common four.
Normality preserves the plane-action kernel under this correction.

Inside the sextet stabilizer, the normalizer of the marked common four is
exactly the marked octad stabilizer: its column action must fix that pair.
The source point–plane group normalizes its common four, so its image lies
in the native point–plane flag. Both literal intersections have order 9216,
which proves equality. The resulting map is supplied on the actual systems
and the original correctly oriented normalizer span.

This proves the plane-side point-flag alignment in Aschbacher, *Sporadic
Groups* (1994), 41.4, p.222. Alignment of the local setwise edge and agreement
with the vertex map on the entire overlap remain necessary for similarity;
the source 41.2 ambient-generation argument is also still separate.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer
open Atlas.Codes Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Representation.Hexacode
open BinaryPermutation.SixPairsQuadratic (Pair pairPerm pairHom)
open M24ChapterHStabilizers

private theorem pair_transport (s : Pair) :
    ∃ g : sextetStabilizer standardSextet,
      pairPerm (SextetCore.columnHom g) s = CommonPlane.basePair := by
  have ht : ∀ s : Pair, ∃ i j : Fin 6,
      pairPerm (Equiv.swap 0 i * Equiv.swap 4 j) CommonPlane.basePair = s := by decide +kernel
  obtain ⟨i,j,hh⟩ := ht s
  obtain ⟨g,hg⟩ := SextetCore.columnHom_surjective (Equiv.swap 0 i * Equiv.swap 4 j)
  refine ⟨g⁻¹,?_⟩
  have h : pairHom (SextetCore.columnHom g) CommonPlane.basePair = s := by
    change pairPerm _ _ = _
    rw [hg]
    exact hh
  change pairHom (SextetCore.columnHom g⁻¹) s = _
  rw [map_inv,map_inv,← h]
  exact Equiv.symm_apply_apply _ _

/-- The native normalizer of its common four is exactly its point–plane flag,
relative to the actual sextet stabilizer. -/
theorem native_normalizes_common_iff (g : sextetStabilizer standardSextet) :
    (g : M24) ∈ normalizer (CommonPlane.common : Set M24) ↔
      (g : M24) ∈ octadStabilizer standardOctad := by
  rw [mem_normalizer_iff_map_conj_eq]
  change CommonPlane.common.map (MulAut.conj (g : M24)).toMonoidHom = CommonPlane.common ↔ _
  rw [CommonPlane.common_eq_planeGroup,CommonPlane.planeGroup_map,
    CommonPlane.planeGroup_injective.eq_iff]
  rw [OctadGraph.NativePlane.sextet_mem_octad_iff,MulAction.mem_stabilizer_iff]
  apply Iff.trans (Subtype.ext_iff)
  simp only [pairPerm,Finset.smul_finset_def,Finset.map_eq_image]
  rfl

variable {G : Type*} [Group G] [Finite G] {z : G}
  (F : MarkedCentralizer z) (D : LocalData F)

include D in
/-- Align the source common four with the marked native common four using
an element of the actual sextet stabilizer. -/
theorem exists_native_plane_common_equiv :
    ∃ e : threeSpaceNormalizer F ≃* sextetStabilizer standardSextet,
      ((F.row ⊓ F.threeSpace).subgroupOf (threeSpaceNormalizer F)).map
        ((sextetStabilizer standardSextet).subtype.comp e.toMonoidHom) = CommonPlane.common ∧
      (planePointAction F).ker.map e.toMonoidHom = SextetCore.columnHom.ker := by
  obtain ⟨e,s,_,hk,hs⟩ := exists_native_plane_equiv_common_four F D
  obtain ⟨g,hg⟩ := pair_transport s
  let e' := e.trans (MulAut.conj g)
  refine ⟨e',?_,?_⟩
  · have hm : ((sextetStabilizer standardSextet).subtype.comp e'.toMonoidHom) =
        (MulAut.conj (g : M24)).toMonoidHom.comp
          ((sextetStabilizer standardSextet).subtype.comp e.toMonoidHom) := by
      ext n
      rfl
    rw [hm,← map_map,hs,CommonPlane.planeGroup_map,hg,← CommonPlane.common_eq_planeGroup]
  · change (planePointAction F).ker.map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _
    rw [← map_map,hk]
    exact mem_normalizer_iff_map_conj_eq.mp
      (show g ∈ normalizer (SextetCore.columnHom.ker : Set (sextetStabilizer standardSextet)) by
        rw [normalizer_eq_top]
        trivial)

include D in
omit [Finite G] in
/-- Every plane map preserving the actual common four carries the full
point–plane flag onto its native flag. -/
theorem native_plane_equiv_point_flag
    (e : threeSpaceNormalizer F ≃* sextetStabilizer standardSextet)
    (he : ((F.row ⊓ F.threeSpace).subgroupOf (threeSpaceNormalizer F)).map
        ((sextetStabilizer standardSextet).subtype.comp e.toMonoidHom) = CommonPlane.common) :
    ∀ n : threeSpaceNormalizer F, (n : G) ∈ rowNormalizer F ↔
      (e n : M24) ∈ octadStabilizer standardOctad := by
  let A := (F.row ⊓ F.threeSpace).subgroupOf (threeSpaceNormalizer F)
  let J := (rowNormalizer F).subgroupOf (threeSpaceNormalizer F)
  let J' := (octadStabilizer standardOctad).subgroupOf (sextetStabilizer standardSextet)
  have hle : J.map e.toMonoidHom ≤ J' := by
    rintro _ ⟨n,hn,rfl⟩
    apply (native_normalizes_common_iff (e n)).mp
    have hnA : n ∈ normalizer (A : Set (threeSpaceNormalizer F)) := by
      apply mem_normalizer_iff.mpr
      intro a
      change ((a : G) ∈ F.row ∧ (a : G) ∈ F.threeSpace) ↔
        (n : G) * (a : G) * (n : G)⁻¹ ∈ F.row ∧
          (n : G) * (a : G) * (n : G)⁻¹ ∈ F.threeSpace
      have hnR : (n : G) ∈ rowNormalizer F := hn
      exact and_congr (mem_normalizer_iff.mp hnR (a : G))
        (mem_normalizer_iff.mp n.property (a : G))
    have hh := mem_normalizer_iff_map_conj_eq.mp hnA
    change A.map (MulAut.conj n).toMonoidHom = A at hh
    apply mem_normalizer_iff_map_conj_eq.mpr
    change CommonPlane.common.map (MulAut.conj (e n : M24)).toMonoidHom = _
    rw [← he, map_map]
    have hc : (MulAut.conj (e n : M24)).toMonoidHom.comp
        ((sextetStabilizer standardSextet).subtype.comp e.toMonoidHom) =
      ((sextetStabilizer standardSextet).subtype.comp e.toMonoidHom).comp
        (MulAut.conj n).toMonoidHom := by
      apply MonoidHom.ext
      intro a
      change (e n : M24) * (e a : M24) * (e n : M24)⁻¹ = (e (n * a * n⁻¹) : M24)
      simp only [map_mul,map_inv,Subgroup.coe_mul,Subgroup.coe_inv]
    rw [hc,← map_map]
    exact congrArg (fun B => B.map ((sextetStabilizer standardSextet).subtype.comp e.toMonoidHom)) hh
  have hcard : Nat.card J = Nat.card J' := by
    have h := card_map_of_injective (K := J) (threeSpaceNormalizer F).subtype_injective
    have h' := card_map_of_injective (K := J') (sextetStabilizer standardSextet).subtype_injective
    rw [subgroupOf_map_subtype,point_plane_card F D] at h
    rw [subgroupOf_map_subtype,OctadGraph.NativePlane.point_plane_card] at h'
    exact h.symm.trans h'
  have hmap : J.map e.toMonoidHom = J' := eq_of_le_of_card_ge hle (by
    rw [card_map_of_injective e.injective,hcard])
  intro n
  change n ∈ J ↔ e n ∈ J'
  rw [← hmap,mem_map_equiv,MulEquiv.symm_apply_apply]

include D in
/-- The actual plane map now preserves its full point–plane flag and plane-action kernel. -/
theorem exists_native_plane_point_flag_equiv :
    ∃ e : threeSpaceNormalizer F ≃* sextetStabilizer standardSextet,
      (∀ n : threeSpaceNormalizer F, (n : G) ∈ rowNormalizer F ↔
        (e n : M24) ∈ octadStabilizer standardOctad) ∧
      (planePointAction F).ker.map e.toMonoidHom = SextetCore.columnHom.ker := by
  obtain ⟨e,hc,hk⟩ := exists_native_plane_common_equiv F D
  exact ⟨e,native_plane_equiv_point_flag F D e hc,hk⟩

/-- The plane-group map preserves the point flag on the literal source/native
uniqueness systems, in addition to the full plane-action kernel. -/
theorem exists_native_local_point_flag_equiv
    (hgen : threeSpaceNormalizer F ⊔ rowNormalizer F = ⊤) :
    ∃ e : (system_of_generation F D hgen).H ≃* OctadGraph.system.H,
      (∀ n : (system_of_generation F D hgen).H,
        (n : G) ∈ (system_of_generation F D hgen).vertexGroup ↔
          (e n : M24) ∈ OctadGraph.system.vertexGroup) ∧
      (planePointAction F).ker.map e.toMonoidHom = SextetCore.columnHom.ker := by
  obtain ⟨e,hf,hk⟩ := exists_native_plane_point_flag_equiv F D
  refine ⟨e,?_,hk⟩
  intro n
  change (n : G) ∈ MulAction.stabilizer G
    (GraphUniquenessSystem.Cosets.vertex (rowNormalizer F) 1) ↔ _
  rw [GraphUniquenessSystem.Cosets.stabilizer_base,OctadGraph.system_vertex,
    OctadGraph.NativePlane.first_eq_standardOctad]
  exact hf n

/-- The original fusion data supplies a plane map preserving the exact common
point flag in the same oriented normalizer-span system. -/
theorem oriented_normalizerSpan_local_point_flag_equiv (hfusion : F.MathieuFusion) :
    let E := SourceData.ofFusion F hfusion
    let U := normalizerSpan_system E.oriented.marking E.localData
    ∃ e : U.H ≃* OctadGraph.system.H,
      (∀ n : U.H, (n : normalizerSpan E.oriented.marking) ∈ U.vertexGroup ↔
        (e n : M24) ∈ OctadGraph.system.vertexGroup) ∧
      (planePointAction (normalizerSpanMarking E.oriented.marking)).ker.map e.toMonoidHom =
        SextetCore.columnHom.ker := by
  let E := SourceData.ofFusion F hfusion
  exact exists_native_local_point_flag_equiv (normalizerSpanMarking E.oriented.marking)
    (normalizerSpanLocalData E.oriented.marking E.localData)
    (normalizerSpan_pair_generate E.oriented.marking E.localData)

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
