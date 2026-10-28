module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.AlignFlags
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.NativeEdge
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.EdgePerfect

/-!
# The simultaneous native row comparison preserves the whole edge

The source edge fixer is the derived subgroup of the point–line group.
A row isomorphism carrying that group onto the native point–line group
therefore carries its commutators into the native edge fixer. On both
sides the remaining action fixes one of three letters. The unique
nonidentity permutation fixing that letter, together with an actual
native lift, proves the reverse inclusion without assuming edge
compatibility or using abstract isomorphism types alone.

The same map retains its kernel coordinates, quotient action and both
marked flags. The final consumer supplies the vertex component, including
the exact edge restriction, on the oriented normalizer-span system from
the original fusion hypothesis. A compatible plane-group isomorphism and
the ambient generation argument are still required for full similarity
and recognition.

Source: Aschbacher, *Sporadic Groups* (1994), 41.4, p.222, especially the
derived-group characterization of the pointwise line fixer.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open PairOvergroups
variable {G : Type*} [Group G] [Finite G] {z : G}
  (F : MarkedCentralizer z) (D : LocalData F)

/-- A row isomorphism preserving the actual point–line subgroup necessarily
preserves the full native edge fixer. -/
theorem row_equiv_native_edge
    (e : rowNormalizer F ≃* octadStabilizer OctadGraph.first)
    (hP : ∀ n : rowNormalizer F, (n : G) ∈ planeNormalizer F ↔
      (e n : M24) ∈ trioStabilizer standardTrio) :
    ∀ n : rowNormalizer F, (n : G) ∈ edgeGroup F D ↔
      (e n : M24) ∈ OctadGraph.system.edgeGroup := by
  let P := (planeNormalizer F).subgroupOf (rowNormalizer F)
  let P' := (trioStabilizer standardTrio).subgroupOf (octadStabilizer OctadGraph.first)
  have hPm : P.map e.toMonoidHom = P' := by
    ext n
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact (hP a).mp ha
    · intro hn
      refine ⟨e.symm n,(hP (e.symm n)).mpr ?_,e.apply_symm_apply n⟩
      rw [e.apply_symm_apply]
      exact hn
  have hle : ∀ a : rowNormalizer F, (a : G) ∈ edgeGroup F D →
      (e a : M24) ∈ OctadGraph.system.edgeGroup := by
    intro a ha
    have hc : e a ∈ ⁅P',P'⁆ := by
      rw [← hPm, ← map_commutator, pointLine_relative_commutator F D]
      exact mem_map_of_mem e.toMonoidHom ha
    have hh := mem_map_of_mem (octadStabilizer OctadGraph.first).subtype hc
    rw [map_commutator, subgroupOf_map_subtype, inf_comm] at hh
    exact OctadGraph.NativeLine.pointLine_commutator_le hh
  obtain ⟨b',hbT,hbE⟩ := OctadGraph.NativeLine.exists_pointLine_not_edge
  let b := e.symm b'
  have hbP : (b : G) ∈ planeNormalizer F := (hP b).mpr (by
    simpa only [b,e.apply_symm_apply] using hbT)
  have hbN : (e b : M24) ∉ OctadGraph.system.edgeGroup := by
    simpa only [b,e.apply_symm_apply] using hbE
  have hb : (b : G) ∉ edgeGroup F D := fun h => hbN (hle b h)
  intro a
  refine ⟨hle a, ?_⟩
  intro ha
  have haP : (a : G) ∈ planeNormalizer F :=
    (hP a).mpr (OctadGraph.NativeLine.edge_le_trio ha)
  by_contra haE
  let al : planeNormalizer F := ⟨a,haP⟩
  let bl : planeNormalizer F := ⟨b,hbP⟩
  have hqa : lineAction F D al ≠ 1 := fun h => haE ((line_edgeFixer_iff F D al).mpr h)
  have hqb : lineAction F D bl ≠ 1 := fun h => hb ((line_edgeFixer_iff F D bl).mpr h)
  have hq : lineAction F D al = lineAction F D bl :=
    (by decide : ∀ p q : Equiv.Perm (Fin 3), p 0 = 0 → q 0 = 0 →
      p ≠ 1 → q ≠ 1 → p = q) _ _
      ((lineAction_fix_iff F D al).mpr a.property)
      ((lineAction_fix_iff F D bl).mpr b.property) hqa hqb
  have hab : ((a * b⁻¹ : rowNormalizer F) : G) ∈ edgeGroup F D := by
    apply (line_edgeFixer_iff F D (al * bl⁻¹)).mpr
    rw [map_mul,map_inv,hq,mul_inv_cancel]
  have hh := OctadGraph.system.edgeGroup.mul_mem
    (OctadGraph.system.edgeGroup.inv_mem (hle (a*b⁻¹) hab)) ha
  apply hbN
  simpa only [map_mul,map_inv,Subgroup.coe_mul,Subgroup.coe_inv,
    mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel,mul_one] using hh

/-- The edge restriction holds for the same row map that carries the two
marked subspaces and intertwines both kernel and quotient actions. -/
theorem exists_native_row_marked_edge_flag_equiv :
    ∃ (d : M24ChapterHStabilizers.OctadAction.Space ≃ₗ[ZMod 2]
        M24ChapterHStabilizers.OctadAction.Space)
      (e : rowNormalizer F ≃* octadStabilizer standardOctad),
      (rowSubspace F F.threeSpace).map d.toLinearMap = OctadGraph.NativePlane.commonSubspace ∧
      (rowSubspace F F.plane).map d.toLinearMap = OctadGraph.NativeLine.commonSubspace ∧
      (∀ a : F.row, e (inclusion F.row.le_normalizer a) =
        ((M24ChapterHStabilizers.OctadAction.coreCoordinates standardOctad).symm
          (Multiplicative.ofAdd (d (rowCoordinates F a).toAdd)) : octadStabilizer standardOctad)) ∧
      (∀ n, M24ChapterHStabilizers.OctadAction.linearAction standardOctad (e n) =
        d * rowAction F D n * d⁻¹) ∧
      (∀ n : rowNormalizer F, (n : G) ∈ threeSpaceNormalizer F ↔
        (e n : M24) ∈ sextetStabilizer standardSextet) ∧
      (∀ n : rowNormalizer F, (n : G) ∈ planeNormalizer F ↔
        (e n : M24) ∈ trioStabilizer standardTrio) ∧
      (∀ n : rowNormalizer F, (n : G) ∈ edgeGroup F D ↔
        (e n : M24) ∈ OctadGraph.system.edgeGroup) := by
  obtain ⟨d,e,hd,hl,hker,hact,hH,hL⟩ := exists_native_row_flag_equiv F D
  let w : octadStabilizer standardOctad ≃* octadStabilizer OctadGraph.first :=
    MulEquiv.subgroupCongr (congrArg octadStabilizer
      OctadGraph.NativePlane.first_eq_standardOctad.symm)
  exact ⟨d,e,hd,hl,hker,hact,hH,hL,row_equiv_native_edge F D (e.trans w) hL⟩

/-- One source/native row map preserves both flags and the full edge group;
its kernel coordinates and quotient action are unchanged from the flag map. -/
theorem exists_native_row_edge_flag_equiv :
    ∃ e : rowNormalizer F ≃* octadStabilizer OctadGraph.first,
      (∀ n : rowNormalizer F, (n : G) ∈ threeSpaceNormalizer F ↔
        (e n : M24) ∈ sextetStabilizer standardSextet) ∧
      (∀ n : rowNormalizer F, (n : G) ∈ planeNormalizer F ↔
        (e n : M24) ∈ trioStabilizer standardTrio) ∧
      (∀ n : rowNormalizer F, (n : G) ∈ edgeGroup F D ↔
        (e n : M24) ∈ OctadGraph.system.edgeGroup) := by
  obtain ⟨_,e,_,_,_,_,hH,hL,hE⟩ := exists_native_row_marked_edge_flag_equiv F D
  let w : octadStabilizer standardOctad ≃* octadStabilizer OctadGraph.first :=
    MulEquiv.subgroupCongr (congrArg octadStabilizer
      OctadGraph.NativePlane.first_eq_standardOctad.symm)
  let e' := e.trans w
  have hL' : ∀ n : rowNormalizer F, (n : G) ∈ planeNormalizer F ↔
      (e' n : M24) ∈ trioStabilizer standardTrio := hL
  exact ⟨e',hH,hL',hE⟩

/-- The vertex component of a similarity, now preserving its actual edge and
point–plane subgroup on the literal uniqueness systems. -/
theorem exists_native_vertex_edge_flag_equiv
    (hgen : threeSpaceNormalizer F ⊔ rowNormalizer F = ⊤) :
    ∃ e : (system_of_generation F D hgen).vertexGroup ≃* OctadGraph.system.vertexGroup,
      (∀ a : (system_of_generation F D hgen).vertexGroup,
        (a : G) ∈ (system_of_generation F D hgen).H ↔
          (e a : M24) ∈ OctadGraph.system.H) ∧
      (∀ a : (system_of_generation F D hgen).vertexGroup,
        (a : G) ∈ planeNormalizer F ↔
          (e a : M24) ∈ trioStabilizer standardTrio) ∧
      (∀ a : (system_of_generation F D hgen).vertexGroup,
        (a : G) ∈ (system_of_generation F D hgen).edgeGroup ↔
          (e a : M24) ∈ OctadGraph.system.edgeGroup) := by
  obtain ⟨e,hH,hL,hE⟩ := exists_native_row_edge_flag_equiv F D
  let v : (system_of_generation F D hgen).vertexGroup ≃* rowNormalizer F :=
    MulEquiv.subgroupCongr (GraphUniquenessSystem.Cosets.stabilizer_base _)
  let w : OctadGraph.system.vertexGroup ≃* octadStabilizer OctadGraph.first :=
    MulEquiv.subgroupCongr OctadGraph.system_vertex
  exact ⟨v.trans (e.trans w.symm), fun a => hH (v a), fun a => hL (v a),
    fun a => hE (v a)⟩

/-- The original fusion hypothesis supplies the complete vertex-side comparison
in the same oriented source span, without any additional local premise. -/
theorem oriented_normalizerSpan_vertex_edge_flag_equiv (hfusion : F.MathieuFusion) :
    let E := SourceData.ofFusion F hfusion
    let U := normalizerSpan_system E.oriented.marking E.localData
    ∃ e : U.vertexGroup ≃* OctadGraph.system.vertexGroup,
      (∀ a : U.vertexGroup,
        (a : normalizerSpan E.oriented.marking) ∈ U.H ↔
          (e a : M24) ∈ OctadGraph.system.H) ∧
      (∀ a : U.vertexGroup,
        (a : normalizerSpan E.oriented.marking) ∈
          planeNormalizer (normalizerSpanMarking E.oriented.marking) ↔
          (e a : M24) ∈ trioStabilizer standardTrio) ∧
      (∀ a : U.vertexGroup,
        (a : normalizerSpan E.oriented.marking) ∈ U.edgeGroup ↔
          (e a : M24) ∈ OctadGraph.system.edgeGroup) := by
  let E := SourceData.ofFusion F hfusion
  exact exists_native_vertex_edge_flag_equiv (normalizerSpanMarking E.oriented.marking)
    (normalizerSpanLocalData E.oriented.marking E.localData)
    (normalizerSpan_pair_generate E.oriented.marking E.localData)

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
