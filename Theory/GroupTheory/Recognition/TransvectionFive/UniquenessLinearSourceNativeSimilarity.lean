module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceNativeGeometry
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceEdgeRigidity

/-!
# Compatible native similarities and recognition inside the generated subgroup

Marked alignment supplies two maps agreeing on the entire intersection.
First conjugate within the native plane to put the image of the pointwise
edge fixer on the specified edge. The local fixer of that edge fixes just
the three nonzero vectors in its binary span. Therefore the image of a source
edge reversal selects a point with the same full edge fixer. A second plane
conjugation aligns that reversal while preserving the maps' agreement and
both subgroup tests. Decomposing the setwise edge stabilizer into its fixer
and reversing coset supplies the last similarity condition.

The existing odd-index rigidity proves the literal edge-conjugation identity.
Consequently the original source comparison requires only ambient generation.
Inside the normalizer-generated subgroup that premise is already proved, so
its comparison and its isomorphism with the native SL₅(2) are unconditional
consequences of the marked linear fusion data. No simplicity of this subgroup
is assumed, and its recognition does not assert that it is the ambient group.

Source: Aschbacher, *Sporadic Groups* (1994), 37.9, 41.3--41.5,
pp.202--204,222. The remaining ambient generation argument is 41.1, p.220.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
open scoped Matrix
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear
open GraphUniquenessSystem SourceGeometry

private theorem conjugate_fixes_iff {A X : Type*} [Group A] [MulAction A X]
    (q g : A) (v : X) : (q * g * q⁻¹) • (q • v) = q • v ↔ g • v = v := by
  simp only [mul_smul, inv_smul_smul]
  exact (MulAction.injective q).eq_iff

/-- Aligned maps preserve the native system's specified pointwise edge fixer. -/
theorem exists_native_edge_maps {G : Type*} [Group G] [Finite G] {z : G}
    (F : MarkedCentralizer z) (hlinear : F.LinearFusion) :
    ∃ (r : rowNormalizer F ≃* nativeSystem.system.vertexGroup)
      (t : sourceThreeSpaceNormalizer F ≃* nativeSystem.system.H),
      (∀ (g : G) (hr : g ∈ rowNormalizer F) (ht : g ∈ sourceThreeSpaceNormalizer F),
        (r ⟨g, hr⟩ : SL) = (t ⟨g, ht⟩ : SL)) ∧
      (∀ h : sourceThreeSpaceNormalizer F, (h : G) ∈ rowNormalizer F ↔
        (t h : SL) ∈ nativeSystem.system.vertexGroup) ∧
      (∀ a : rowNormalizer F, (a : G) ∈ SourceGeometry.edgeGroup F hlinear ↔
        (r a : SL) ∈ nativeSystem.system.edgeGroup) := by
  obtain ⟨r, t, ha, hl, he⟩ := exists_native_system_local_maps F hlinear
  obtain ⟨p, hpx, hpy⟩ := exists_plane_pair (basisPoint 0) nativeSourceNeighbor
    (basisPoint_mem_plane (by simp)) nativeSourceNeighbor_mem nativeSourceNeighbor_ne.symm
  let q : SL := (p : SL)⁻¹
  have hqx : q • basisPoint 0 = basisPoint 0 := by
    change (p : SL)⁻¹ • basisPoint 0 = basisPoint 0
    rw [inv_smul_eq_iff, hpx]
  have hqy : q • nativeSourceNeighbor = basisPoint 1 := by
    change (p : SL)⁻¹ • nativeSourceNeighbor = basisPoint 1
    rw [inv_smul_eq_iff, hpy]
  have hqH : q ∈ nativeSystem.system.H := by
    rw [nativeSystem.local_eq]
    exact planeGroup.inv_mem p.property
  have hqM : q ∈ nativeSystem.system.vertexGroup := by
    change q • nativeSystem.system.x = nativeSystem.system.x
    rw [nativeSystem.point_eq]
    exact hqx
  let r' := r.trans (MulAut.conj (⟨q, hqM⟩ : nativeSystem.system.vertexGroup))
  let t' := t.trans (MulAut.conj (⟨q, hqH⟩ : nativeSystem.system.H))
  refine ⟨r', t', ?_, ?_, ?_⟩
  · intro g hr ht
    change q * (r ⟨g, hr⟩ : SL) * q⁻¹ = q * (t ⟨g, ht⟩ : SL) * q⁻¹
    rw [ha]
  · intro h
    exact (hl h).trans ((mem_normalizer_iff.mp
      (nativeSystem.system.vertexGroup.le_normalizer hqM)) (t h : SL))
  · intro a
    rw [he]
    change ((r a : SL) • basisPoint 0 = basisPoint 0 ∧
      (r a : SL) • nativeSourceNeighbor = nativeSourceNeighbor) ↔
        (q * (r a : SL) * q⁻¹) • nativeSystem.system.x = nativeSystem.system.x ∧
        (q * (r a : SL) * q⁻¹) • nativeSystem.system.y = nativeSystem.system.y
    rw [nativeSystem.point_eq, nativeSystem.neighbor_eq, ← hqx, ← hqy,
      conjugate_fixes_iff, conjugate_fixes_iff, hqx]


private theorem native_local_pair_fixed (w : Point) (hw : w ≠ basisPoint 0)
    (hfix : ∀ a ∈ planeGroup ⊓ nativeSystem.system.edgeGroup, a • w = w) :
    w = basisPoint 1 ∨ w.val = (basisPoint 0).val + (basisPoint 1).val := by
  have hz (j : Fin 5) (hj : 2 ≤ j.val) : w.val j = 0 := by
    let n : SL := root (show (0 : Fin 5) < j by omega)
    have hnH : n ∈ planeGroup := by
      intro v
      change linearEquiv n v ∈ planeSpace ↔ v ∈ planeSpace
      rw [BinaryLinear.OuterCyclic.slEquivLinear_apply, native_planeSpace_mem_iff, native_planeSpace_mem_iff]
      change ((1 + Matrix.single 0 j 1) *ᵥ v) 3 = 0 ∧
        ((1 + Matrix.single 0 j 1) *ᵥ v) 4 = 0 ↔ _
      simp [Matrix.add_mulVec, Matrix.single_mulVec_eq]
    have hnx (i : Fin 5) (hi : i.val < 2) : n • basisPoint i = basisPoint i := by
      apply Subtype.ext
      change linearEquiv n (Pi.single i 1) = Pi.single i 1
      rw [BinaryLinear.OuterCyclic.slEquivLinear_apply]
      change (1 + Matrix.single 0 j 1) *ᵥ Pi.single i 1 = Pi.single i 1
      have hij : i ≠ j := by intro h; subst j; omega
      rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
      simp [hij]
    have hnB : n ∈ nativeSystem.system.edgeGroup := by
      change n • nativeSystem.system.x = _ ∧ n • nativeSystem.system.y = _
      rw [nativeSystem.point_eq, nativeSystem.neighbor_eq]
      exact ⟨hnx 0 (by decide), hnx 1 (by decide)⟩
    have he := congrArg (fun v : Point => v.val 0) (hfix n ⟨hnH, hnB⟩)
    change ((1 + Matrix.single 0 j 1) *ᵥ w.val) 0 = w.val 0 at he
    simpa [Matrix.add_mulVec, Matrix.single_mulVec_eq] using he
  have hc : w.val = (basisPoint 1).val ∨
      w.val = (basisPoint 0).val + (basisPoint 1).val :=
    (by decide : ∀ v : Space, v ≠ 0 → v ≠ (basisPoint 0).val →
      v 2 = 0 → v 3 = 0 → v 4 = 0 → v = (basisPoint 1).val ∨
      v = (basisPoint 0).val + (basisPoint 1).val) w.val w.property
      (fun h => hw (Subtype.ext h)) (hz 2 (by decide)) (hz 3 (by decide)) (hz 4 (by decide))
  exact hc.imp Subtype.ext id

private theorem native_edge_fixer_of_local_fixed (w : Point) (hw : w ≠ basisPoint 0)
    (hfix : ∀ a ∈ planeGroup ⊓ nativeSystem.system.edgeGroup, a • w = w) :
    nativeSystem.system.edgeGroup = edgeFixer SL (basisPoint 0) w := by
  rcases native_local_pair_fixed w hw hfix with rfl | hw
  · change edgeFixer SL nativeSystem.system.x nativeSystem.system.y = _
    rw [nativeSystem.point_eq, nativeSystem.neighbor_eq]
  · ext g
    change (g • nativeSystem.system.x = _ ∧ g • nativeSystem.system.y = _) ↔
      g • basisPoint 0 = basisPoint 0 ∧ g • w = w
    rw [nativeSystem.point_eq, nativeSystem.neighbor_eq]
    constructor
    · rintro ⟨hx, hy⟩
      refine ⟨hx, Subtype.ext ?_⟩
      change linearEquiv g w.val = w.val
      rw [hw, map_add, show linearEquiv g (basisPoint 0).val = (basisPoint 0).val from
        congrArg Subtype.val hx, show linearEquiv g (basisPoint 1).val = (basisPoint 1).val from
        congrArg Subtype.val hy]
    · rintro ⟨hx, hg⟩
      refine ⟨hx, Subtype.ext ?_⟩
      have h := congrArg Subtype.val hg
      change linearEquiv g w.val = w.val at h
      rw [hw, map_add, show linearEquiv g (basisPoint 0).val = (basisPoint 0).val from
        congrArg Subtype.val hx] at h
      exact add_left_cancel h


universe u v
variable {G : Type u} {V : Type v} [Group G] [MulAction G V]

private structure NativeMaps (U : System G V) where
  vertexIso : U.vertexGroup ≃* nativeSystem.system.vertexGroup
  localIso : U.H ≃* nativeSystem.system.H
  agree : ∀ (g : G) (hgH : g ∈ U.H) (hgx : g ∈ U.vertexGroup),
    (vertexIso ⟨g, hgx⟩ : SL) = (localIso ⟨g, hgH⟩ : SL)
  local_vertex : ∀ h : U.H, (h : G) ∈ U.vertexGroup ↔
    (localIso h : SL) ∈ nativeSystem.system.vertexGroup
  edge : ∀ a : U.vertexGroup, (a : G) ∈ U.edgeGroup ↔
    (vertexIso a : SL) ∈ nativeSystem.system.edgeGroup

private theorem NativeMaps.local_fixer {U : System G V} (s : NativeMaps U) (h : U.H) :
    (h : G) ∈ U.edgeGroup ↔ (s.localIso h : SL) ∈ nativeSystem.system.edgeGroup := by
  constructor
  · intro hh
    have he := (s.edge ⟨h, hh.1⟩).mp hh
    rwa [s.agree h h.property hh.1] at he
  · intro hh
    have hm := (s.local_vertex h).mpr hh.1
    apply (s.edge ⟨h, hm⟩).mpr
    rwa [s.agree h h.property hm]

private theorem NativeMaps.swap_image_fixed {U : System G V} (s : NativeMaps U)
    (t : U.H) (htx : (t : G) • U.x = U.y) :
    ∀ a ∈ planeGroup ⊓ nativeSystem.system.edgeGroup,
      a • ((s.localIso t : SL) • basisPoint 0) = (s.localIso t : SL) • basisPoint 0 := by
  rintro a ⟨haH, haB⟩
  have haH' : a ∈ nativeSystem.system.H := nativeSystem.local_eq.symm ▸ haH
  let b : U.H := s.localIso.symm ⟨a, haH'⟩
  have hb : s.localIso b = ⟨a, haH'⟩ := s.localIso.apply_symm_apply _
  have hbB : (b : G) ∈ U.edgeGroup := (s.local_fixer b).mpr (by rw [hb]; exact haB)
  have hc : ((t⁻¹ * b * t : U.H) : G) ∈ U.vertexGroup := by
    change ((t : G)⁻¹ * (b : G) * (t : G)) • U.x = U.x
    rw [mul_smul, mul_smul, htx, show (b : G) • U.y = U.y from hbB.2,
      inv_smul_eq_iff, htx]
  have he := (s.local_vertex (t⁻¹ * b * t)).mp hc
  change (s.localIso (t⁻¹ * b * t) : SL) • nativeSystem.system.x = _ at he
  rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, hb, nativeSystem.point_eq, mul_smul, mul_smul, inv_smul_eq_iff] at he
  exact he

private theorem pair_stabilizer_iff {A X : Type*} [Group A] [MulAction A X]
    (x y : X) (t g : A) (htx : t • x = y) (hty : t • y = x) :
    g ∈ edgeStabilizer A x y ↔ g ∈ edgeFixer A x y ∨ g * t ∈ edgeFixer A x y := by
  change ((g • x = x ∧ g • y = y) ∨ (g • x = y ∧ g • y = x)) ↔
    (g • x = x ∧ g • y = y) ∨ ((g * t) • x = x ∧ (g * t) • y = y)
  simp only [mul_smul, htx, hty]
  tauto

private def NativeMaps.similarity_of_swap {U : System G V} (s : NativeMaps U)
    (t : U.H) (htx : (t : G) • U.x = U.y) (hty : (t : G) • U.y = U.x)
    (htx' : (s.localIso t : SL) • nativeSystem.system.x = nativeSystem.system.y)
    (hty' : (s.localIso t : SL) • nativeSystem.system.y = nativeSystem.system.x) :
    Similarity U nativeSystem.system where
  vertexIso := s.vertexIso
  localIso := s.localIso
  agree := s.agree
  local_vertex := s.local_vertex
  edge := s.edge
  local_edge := by
    intro h
    rw [pair_stabilizer_iff U.x U.y (t : G) (h : G) htx hty,
      pair_stabilizer_iff nativeSystem.system.x nativeSystem.system.y (s.localIso t : SL)
        (s.localIso h : SL) htx' hty']
    have hh := s.local_fixer h
    have hht := s.local_fixer (h * t)
    simpa only [map_mul, Subgroup.coe_mul] using or_congr hh hht

private theorem NativeMaps.nonempty_similarity {U : System G V} (s : NativeMaps U) :
    Nonempty (Similarity U nativeSystem.system) := by
  obtain ⟨t, htx, hty⟩ := U.exists_swap
  let w : Point := (s.localIso t : SL) • basisPoint 0
  have hw : w ≠ basisPoint 0 := by
    intro he
    have hm : (s.localIso t : SL) ∈ nativeSystem.system.vertexGroup := by
      change (s.localIso t : SL) • nativeSystem.system.x = _
      rw [nativeSystem.point_eq]
      exact he
    have ht := (s.local_vertex t).mpr hm
    exact U.adjacent.ne (ht.symm.trans htx)
  have hwP : w.val ∈ planeSpace := by
    have hp : (s.localIso t : SL) ∈ planeGroup := nativeSystem.local_eq ▸ (s.localIso t).property
    exact (hp (basisPoint 0).val).mpr (basisPoint_mem_plane (by simp))
  have hB : nativeSystem.system.edgeGroup = edgeFixer SL (basisPoint 0) w :=
    native_edge_fixer_of_local_fixed w hw (s.swap_image_fixed t htx)
  obtain ⟨p, hpx, hpy⟩ := exists_plane_pair (basisPoint 0) w
    (basisPoint_mem_plane (by simp)) hwP hw.symm
  let q : SL := (p : SL)⁻¹
  have hqx : q • basisPoint 0 = basisPoint 0 := by
    change (p : SL)⁻¹ • basisPoint 0 = _
    rw [inv_smul_eq_iff, hpx]
  have hqy : q • w = basisPoint 1 := by
    change (p : SL)⁻¹ • w = _
    rw [inv_smul_eq_iff, hpy]
  have hqH : q ∈ nativeSystem.system.H := by
    rw [nativeSystem.local_eq]
    exact planeGroup.inv_mem p.property
  have hqM : q ∈ nativeSystem.system.vertexGroup := by
    change q • nativeSystem.system.x = _
    rw [nativeSystem.point_eq]
    exact hqx
  let r' := s.vertexIso.trans (MulAut.conj (⟨q, hqM⟩ : nativeSystem.system.vertexGroup))
  let t' := s.localIso.trans (MulAut.conj (⟨q, hqH⟩ : nativeSystem.system.H))
  let s' : NativeMaps U := {
    vertexIso := r'
    localIso := t'
    agree := by
      intro g hgH hgr
      change q * (s.vertexIso ⟨g, hgr⟩ : SL) * q⁻¹ = q * (s.localIso ⟨g, hgH⟩ : SL) * q⁻¹
      rw [s.agree]
    local_vertex := by
      intro h
      exact (s.local_vertex h).trans ((mem_normalizer_iff.mp
        (nativeSystem.system.vertexGroup.le_normalizer hqM)) (s.localIso h : SL))
    edge := by
      intro a
      rw [s.edge]
      conv_lhs => rw [hB]
      change ((s.vertexIso a : SL) • basisPoint 0 = _ ∧ (s.vertexIso a : SL) • w = _) ↔
        (q * (s.vertexIso a : SL) * q⁻¹) • nativeSystem.system.x = _ ∧
        (q * (s.vertexIso a : SL) * q⁻¹) • nativeSystem.system.y = _
      rw [nativeSystem.point_eq, nativeSystem.neighbor_eq, ← hqx, ← hqy,
        conjugate_fixes_iff, conjugate_fixes_iff, hqx] }
  have htx' : (s'.localIso t : SL) • nativeSystem.system.x = nativeSystem.system.y := by
    change (q * (s.localIso t : SL) * q⁻¹) • nativeSystem.system.x = _
    rw [nativeSystem.point_eq, nativeSystem.neighbor_eq]
    conv_lhs => rw [← hqx]
    simp only [mul_smul, inv_smul_smul]
    exact hqy
  have hty' : (s'.localIso t : SL) • nativeSystem.system.y = nativeSystem.system.x := by
    have ht2 : ((t * t : U.H) : G) ∈ U.vertexGroup := by
      change ((t : G) * (t : G)) • U.x = U.x
      rw [mul_smul, htx, hty]
    have he := (s'.local_vertex (t * t)).mp ht2
    change (s'.localIso (t * t) : SL) • nativeSystem.system.x = _ at he
    rw [map_mul, Subgroup.coe_mul, mul_smul, htx'] at he
    exact he
  exact ⟨s'.similarity_of_swap t htx hty htx' hty'⟩


/-- All local comparison clauses, including the setwise edge condition, follow
from the original linear fusion hypotheses once the source system is generated. -/
theorem nonempty_source_similarity {G : Type*} [Group G] [Finite G] {z : G}
    (F : MarkedCentralizer z) (hlinear : F.LinearFusion)
    (hgen : rowNormalizer F ⊔ sourceThreeSpaceNormalizer F = ⊤) :
    Nonempty (Similarity (system_of_global_generation F hlinear hgen) nativeSystem.system) := by
  let U := system_of_global_generation F hlinear hgen
  have hM : U.vertexGroup = rowNormalizer F := system_of_global_generation_vertexGroup F hlinear hgen
  have hH : U.H = sourceThreeSpaceNormalizer F := system_of_global_generation_local F hlinear hgen
  have hB : U.edgeGroup = SourceGeometry.edgeGroup F hlinear := by
    change edgeFixer G U.x U.y = _
    rw [system_of_global_generation_point, system_of_global_generation_neighbor, planeSwap_vertex]
  obtain ⟨r, t, ha, hl, he⟩ := exists_native_edge_maps F hlinear
  let r' := (MulEquiv.subgroupCongr hM).trans r
  let t' := (MulEquiv.subgroupCongr hH).trans t
  have s : NativeMaps U := {
    vertexIso := r'
    localIso := t'
    agree := by
      intro g hgH hgM
      exact ha g (hM ▸ hgM) (hH ▸ hgH)
    local_vertex := by
      intro h
      rw [hM]
      exact hl (MulEquiv.subgroupCongr hH h)
    edge := by
      intro a
      rw [hB]
      exact he (MulEquiv.subgroupCongr hM a) }
  exact s.nonempty_similarity

/-- The literal source comparison now requires only the ambient generation
clause of source 41.1. Its edge-conjugation identity is supplied by rigidity. -/
theorem nonempty_sourceComparison_of_generation {G : Type*} [Group G] [Finite G] {z : G}
    (F : MarkedCentralizer z) (hlinear : F.LinearFusion)
    (hgen : rowNormalizer F ⊔ sourceThreeSpaceNormalizer F = ⊤) :
    Nonempty (SourceComparison F) := by
  obtain ⟨s⟩ := nonempty_source_similarity F hlinear hgen
  exact ⟨sourceComparison_of_similarity F hlinear hgen s⟩

/-- The actual normalizer-generated subgroup has a complete source comparison;
all generation, similarity and edge-conjugation premises are discharged there. -/
theorem normalizerSpan_sourceComparison {G : Type*} [Group G] [Finite G] {z : G}
    (F : MarkedCentralizer z) (hlinear : F.LinearFusion) :
    Nonempty (SourceComparison (normalizerSpanMarking F)) :=
  nonempty_sourceComparison_of_generation (normalizerSpanMarking F)
    (normalizerSpan_linearFusion F hlinear) (normalizerSpan_row_threeSpace_generate F hlinear)

/-- Recognition of the source induction subgroup, with no simplicity assumption
on that subgroup and no claim yet that it equals the ambient group. -/
theorem normalizerSpan_nonempty_equiv {G : Type*} [Group G] [Finite G] {z : G}
    (F : MarkedCentralizer z) (hlinear : F.LinearFusion) :
    Nonempty (normalizerSpan F ≃* SL) := by
  obtain ⟨C⟩ := normalizerSpan_sourceComparison F hlinear
  exact C.nonempty_equiv

end Theory.GroupTheory.TransvectionFive.UniquenessLinear
