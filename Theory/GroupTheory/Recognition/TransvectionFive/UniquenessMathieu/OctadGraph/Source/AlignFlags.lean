module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.NativeLine
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.NativeVertex
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Flags

/-!
# Simultaneous source/native row-flag alignment

The source row intersections form a nested two-space and hyperplane. The
literal native intersections now give a nested pair of the same dimensions.
Flag transitivity chooses one binary linear coordinate change carrying both
subspaces to their targets. Lift that change to the native octad stabilizer
and conjugate the kernel-marked row isomorphism by the lift.

The same isomorphism preserves both actual point–line and point–plane
subgroups, and retains its conjugated quotient action and kernel coordinates.
The final consumer uses the original fusion producer's same 21/45-oriented
marking and its complete local data inside the normalizer span.

Source: Aschbacher, *Sporadic Groups* (1994), 41.4, p.222. Edge preservation
is proved in `AlignEdge`; the compatible plane-group map and ambient
41.2 generation argument are still required for the full comparison.
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

/-- Simultaneous alignment of the literal point–line and point–plane
stabilizers, retaining the same kernel coordinates and quotient action. -/
theorem exists_native_row_flag_equiv :
    ∃ (d : Space ≃ₗ[ZMod 2] Space)
      (e : rowNormalizer F ≃* Stabilizer standardOctad),
      (rowSubspace F F.threeSpace).map d.toLinearMap = OctadGraph.NativePlane.commonSubspace ∧
      (rowSubspace F F.plane).map d.toLinearMap = OctadGraph.NativeLine.commonSubspace ∧
      (∀ a : F.row, e (inclusion F.row.le_normalizer a) =
        ((coreCoordinates standardOctad).symm
          (Multiplicative.ofAdd (d (rowCoordinates F a).toAdd)) : Stabilizer standardOctad)) ∧
      (∀ n, linearAction standardOctad (e n) = d * rowAction F D n * d⁻¹) ∧
      (∀ n : rowNormalizer F, (n : G) ∈ threeSpaceNormalizer F ↔
        (e n : M24) ∈ sextetStabilizer standardSextet) ∧
      (∀ n : rowNormalizer F, (n : G) ∈ planeNormalizer F ↔
        (e n : M24) ∈ PairOvergroups.trioStabilizer PairOvergroups.standardTrio) := by
  obtain ⟨d, hd, hl⟩ := BinaryLinear.FourParabolicAction.exists_linearEquiv_map_flag
    (rowSubspace F F.threeSpace) (rowSubspace F F.plane)
    OctadGraph.NativePlane.commonSubspace OctadGraph.NativeLine.commonSubspace
    (row_subspaces_nested F) OctadGraph.NativeLine.plane_common_le_common
    ((row_threeSpace_finrank F).trans OctadGraph.NativePlane.commonSubspace_finrank.symm)
    ((row_plane_finrank F).trans OctadGraph.NativeLine.commonSubspace_finrank.symm)
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
  refine ⟨d, e', hd, hl, hker', hact, ?_, ?_⟩
  · intro n
    change n ∈ (threeSpaceNormalizer F).subgroupOf (rowNormalizer F) ↔
      e' n ∈ (sextetStabilizer standardSextet).subgroupOf (Stabilizer standardOctad)
    rw [← plane_parabolic_comap F D, ← OctadGraph.NativePlane.plane_parabolic_comap]
    change rowAction F D n ∈ BinaryLinear.parabolic (rowSubspace F F.threeSpace) ↔
      linearAction standardOctad (e' n) ∈ BinaryLinear.parabolic OctadGraph.NativePlane.commonSubspace
    rw [hact]
    exact parabolic_conjugation _ _ d hd _
  · intro n
    change n ∈ (planeNormalizer F).subgroupOf (rowNormalizer F) ↔
      e' n ∈ (PairOvergroups.trioStabilizer PairOvergroups.standardTrio).subgroupOf
        (Stabilizer standardOctad)
    rw [← line_parabolic_comap F D, ← OctadGraph.NativeLine.line_parabolic_comap]
    change rowAction F D n ∈ BinaryLinear.parabolic (rowSubspace F F.plane) ↔
      linearAction standardOctad (e' n) ∈ BinaryLinear.parabolic OctadGraph.NativeLine.commonSubspace
    rw [hact]
    exact parabolic_conjugation _ _ d hl _

/-- Both actual native flags are preserved by one vertex-group map. -/
theorem exists_native_vertex_flag_equiv
    (hgen : threeSpaceNormalizer F ⊔ rowNormalizer F = ⊤) :
    ∃ e : (system_of_generation F D hgen).vertexGroup ≃* OctadGraph.system.vertexGroup,
      (∀ a : (system_of_generation F D hgen).vertexGroup,
        (a : G) ∈ threeSpaceNormalizer F ↔
          (e a : M24) ∈ sextetStabilizer standardSextet) ∧
      (∀ a : (system_of_generation F D hgen).vertexGroup,
        (a : G) ∈ planeNormalizer F ↔
          (e a : M24) ∈ PairOvergroups.trioStabilizer PairOvergroups.standardTrio) := by
  obtain ⟨_, e, _, _, _, _, hH, hL⟩ := exists_native_row_flag_equiv F D
  let v : (system_of_generation F D hgen).vertexGroup ≃* rowNormalizer F :=
    MulEquiv.subgroupCongr (GraphUniquenessSystem.Cosets.stabilizer_base _)
  let w : OctadGraph.system.vertexGroup ≃* Stabilizer standardOctad :=
    MulEquiv.subgroupCongr (OctadGraph.system_vertex.trans
      (congrArg octadStabilizer OctadGraph.NativePlane.first_eq_standardOctad))
  exact ⟨v.trans (e.trans w.symm), fun a => hH (v a), fun a => hL (v a)⟩

omit D in
/-- Original fusion supplies simultaneous native point–line and point–plane
alignment in the same oriented normalizer span. -/
theorem oriented_normalizerSpan_vertex_flag_equiv (hfusion : F.MathieuFusion) :
    let E := SourceData.ofFusion F hfusion
    ∃ e : (normalizerSpan_system E.oriented.marking E.localData).vertexGroup ≃*
        OctadGraph.system.vertexGroup,
      (∀ a : (normalizerSpan_system E.oriented.marking E.localData).vertexGroup,
        (a : normalizerSpan E.oriented.marking) ∈
          threeSpaceNormalizer (normalizerSpanMarking E.oriented.marking) ↔
        (e a : M24) ∈ sextetStabilizer standardSextet) ∧
      (∀ a : (normalizerSpan_system E.oriented.marking E.localData).vertexGroup,
        (a : normalizerSpan E.oriented.marking) ∈
          planeNormalizer (normalizerSpanMarking E.oriented.marking) ↔
        (e a : M24) ∈ PairOvergroups.trioStabilizer PairOvergroups.standardTrio) := by
  let E := SourceData.ofFusion F hfusion
  exact exists_native_vertex_flag_equiv (normalizerSpanMarking E.oriented.marking)
    (normalizerSpanLocalData E.oriented.marking E.localData)
    (normalizerSpan_pair_generate E.oriented.marking E.localData)

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
