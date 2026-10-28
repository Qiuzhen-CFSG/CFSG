module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.NativeVertex
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.NativePlane

/-!
# Aligning the source and native point–plane flags

Choose a linear change of four-space coordinates carrying the original
source row two-space onto the native common four. Surjectivity of the
native octad action lifts this change to an element of the octad stabilizer.
Conjugating the already constructed row isomorphism by that element gives
an actual isomorphism preserving the point–plane intersection. The same map
retains its kernel coordinates and its literal quotient action.

The final consumer applies this to the complete source system inside the
normalizer-generated subgroup. This supplies the point–plane alignment in
Aschbacher, *Sporadic Groups* (1994), 41.4, p.222. Simultaneous alignment of
the line and edge and agreement with a local-plane isomorphism remain
requirements for the similarity; no such similarity is assumed here.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24ChapterHStabilizers.OctadAction

private theorem parabolic_conjugation (U W : Submodule (ZMod 2) Space)
    (d : Space ≃ₗ[ZMod 2] Space) (hd : U.map d.toLinearMap = W)
    (f : Space ≃ₗ[ZMod 2] Space) :
    f ∈ BinaryLinear.parabolic U ↔ d * f * d⁻¹ ∈ BinaryLinear.parabolic W := by
  subst W
  constructor
  · intro h v
    simpa only [Submodule.mem_map_equiv, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
      LinearEquiv.symm_apply_apply] using h (d.symm v)
  · intro h v
    have hh := h (d v)
    simpa only [Submodule.mem_map_equiv, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
      LinearEquiv.symm_apply_apply] using hh

variable {G : Type*} [Group G] [Finite G] {z : G}
  (F : MarkedCentralizer z) (D : LocalData F)
include D

/-- Alignment of the literal point–plane stabilizers, retaining the linear
coordinate change and the quotient action of the same row isomorphism. -/
theorem exists_native_row_plane_equiv :
    ∃ (d : Space ≃ₗ[ZMod 2] Space)
      (e : rowNormalizer F ≃* Stabilizer standardOctad),
      (rowSubspace F F.threeSpace).map d.toLinearMap = OctadGraph.NativePlane.commonSubspace ∧
      (∀ a : F.row, e (inclusion F.row.le_normalizer a) =
        ((coreCoordinates standardOctad).symm
          (Multiplicative.ofAdd (d (rowCoordinates F a).toAdd)) : Stabilizer standardOctad)) ∧
      (∀ n, linearAction standardOctad (e n) = d * rowAction F D n * d⁻¹) ∧
      (∀ n : rowNormalizer F, (n : G) ∈ threeSpaceNormalizer F ↔
        (e n : M24) ∈ sextetStabilizer standardSextet) := by
  obtain ⟨d, hd⟩ := BinaryLinear.FourParabolicAction.exists_linearEquiv_map_eq
    (rowSubspace F F.threeSpace) OctadGraph.NativePlane.commonSubspace
    ((row_threeSpace_finrank F).trans OctadGraph.NativePlane.commonSubspace_finrank.symm)
  obtain ⟨k, hk⟩ := linearAction_surjective standardOctad d
  obtain ⟨e, hker, he⟩ := exists_native_row_equiv_action F D standardOctad
  let e' := e.trans (MulAut.conj k)
  have hact (n : rowNormalizer F) :
      linearAction standardOctad (e' n) = d * rowAction F D n * d⁻¹ := by
    change linearAction standardOctad (k * e n * k⁻¹) = _
    rw [map_mul, map_mul, map_inv, hk, he]
  have hker' (a : F.row) : e' (inclusion F.row.le_normalizer a) =
      ((coreCoordinates standardOctad).symm
        (Multiplicative.ofAdd (d (rowCoordinates F a).toAdd)) : Stabilizer standardOctad) := by
    let b := (coreCoordinates standardOctad).symm (rowCoordinates F a)
    have hb : coreConjugate standardOctad k b =
        (coreCoordinates standardOctad).symm
          (Multiplicative.ofAdd (d (rowCoordinates F a).toAdd)) := by
      apply (coreCoordinates standardOctad).injective
      apply Multiplicative.toAdd.injective
      rw [coreCoordinates_conjugation, naturalAction_quotientEquiv, hk,
        MulEquiv.apply_symm_apply]
      rw [MulEquiv.apply_symm_apply]
      rfl
    change k * e (inclusion F.row.le_normalizer a) * k⁻¹ = _
    rw [hker]
    exact (coreConjugate_coe standardOctad k b).symm.trans (congrArg Subtype.val hb)
  refine ⟨d, e', hd, hker', hact, ?_⟩
  intro n
  change n ∈ (threeSpaceNormalizer F).subgroupOf (rowNormalizer F) ↔
    e' n ∈ (sextetStabilizer standardSextet).subgroupOf (Stabilizer standardOctad)
  rw [← plane_parabolic_comap F D, ← OctadGraph.NativePlane.plane_parabolic_comap]
  change rowAction F D n ∈ BinaryLinear.parabolic (rowSubspace F F.threeSpace) ↔
    linearAction standardOctad (e' n) ∈ BinaryLinear.parabolic OctadGraph.NativePlane.commonSubspace
  rw [hact]
  exact parabolic_conjugation _ _ d hd _

/-- The same alignment on the marked native octad used by the graph system. -/
theorem exists_native_row_plane_equiv_first :
    ∃ e : rowNormalizer F ≃* Stabilizer OctadGraph.first,
      ∀ n : rowNormalizer F, (n : G) ∈ threeSpaceNormalizer F ↔
        (e n : M24) ∈ sextetStabilizer standardSextet := by
  rw [OctadGraph.NativePlane.first_eq_standardOctad]
  obtain ⟨_, e, _, _, _, he⟩ := exists_native_row_plane_equiv F D
  exact ⟨e, he⟩

/-- Actual consumer on the two literal uniqueness systems: the vertex map
carries their common point–plane subgroup onto the native one. -/
theorem exists_native_vertex_plane_equiv
    (hgen : threeSpaceNormalizer F ⊔ rowNormalizer F = ⊤) :
    ∃ e : (system_of_generation F D hgen).vertexGroup ≃* OctadGraph.system.vertexGroup,
      ∀ a : (system_of_generation F D hgen).vertexGroup,
        (a : G) ∈ (system_of_generation F D hgen).H ↔
          (e a : M24) ∈ OctadGraph.system.H := by
  obtain ⟨e, he⟩ := exists_native_row_plane_equiv_first F D
  let v : (system_of_generation F D hgen).vertexGroup ≃* rowNormalizer F :=
    MulEquiv.subgroupCongr (GraphUniquenessSystem.Cosets.stabilizer_base _)
  let w : OctadGraph.system.vertexGroup ≃* Stabilizer OctadGraph.first :=
    MulEquiv.subgroupCongr OctadGraph.system_vertex
  refine ⟨v.trans (e.trans w.symm), ?_⟩
  intro a
  exact he (v a)

/-- The generation premise is discharged inside the original normalizer span. -/
theorem normalizerSpan_vertex_plane_equiv :
    ∃ e : (normalizerSpan_system F D).vertexGroup ≃* OctadGraph.system.vertexGroup,
      ∀ a : (normalizerSpan_system F D).vertexGroup,
        (a : normalizerSpan F) ∈ (normalizerSpan_system F D).H ↔
          (e a : M24) ∈ OctadGraph.system.H :=
  exists_native_vertex_plane_equiv (normalizerSpanMarking F)
    (normalizerSpanLocalData F D) (normalizerSpan_pair_generate F D)

omit D in
/-- Original-fusion application using exactly the orientation and local data
produced by the completed source normalizer construction. -/
theorem oriented_normalizerSpan_vertex_plane_equiv (hfusion : F.MathieuFusion) :
    let E := SourceData.ofFusion F hfusion
    ∃ e : (normalizerSpan_system E.oriented.marking E.localData).vertexGroup ≃*
        OctadGraph.system.vertexGroup,
      ∀ a : (normalizerSpan_system E.oriented.marking E.localData).vertexGroup,
        (a : normalizerSpan E.oriented.marking) ∈
          (normalizerSpan_system E.oriented.marking E.localData).H ↔
        (e a : M24) ∈ OctadGraph.system.H := by
  let E := SourceData.ofFusion F hfusion
  exact normalizerSpan_vertex_plane_equiv E.oriented.marking E.localData

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
