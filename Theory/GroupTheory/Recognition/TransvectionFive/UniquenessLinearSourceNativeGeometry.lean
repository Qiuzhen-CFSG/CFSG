module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceNativeFusion
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSystem
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceSystem
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceRow
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Intersections.Model

/-!
# The native normalizers in the literal vector action

The row normalizer is exactly the stabilizer of the first nonzero coordinate
vector. Conjugating a row root detects its first column; conversely that
column condition preserves all row roots. The fixed space of the second
rectangle is the coordinate three-space. Its normalizer is precisely that
space's stabilizer, as is also checked by the lower-left matrix block.

The source point cosets therefore identify equivariantly with the native
nonzero vectors. The actual chosen source edge becomes an edge within the
native plane, and its whole pointwise fixer is preserved. Specializing the
aligned maps gives maps into the native system's actual vertex and local
groups, with their agreement, intersection membership and edge-fixer tests.
The final application uses the normalizer-generated subgroup without
assuming it simple.

Source: Aschbacher, *Sporadic Groups* (1994), Example 38.4 and 41.4--41.5,
pp.206--207,222. Setwise-edge alignment and ambient source generation remain
separate obligations before the arbitrary source comparison is assembled.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
open scoped Matrix
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear
open GraphUniquenessSystem

private theorem vertex_firstColumn (g : SL) :
    g ∈ nativeSystem.system.vertexGroup ↔ ∀ i : Fin 5, g i 0 = if i = 0 then 1 else 0 := by
  change g • nativeSystem.system.x = nativeSystem.system.x ↔ _
  rw [nativeSystem.point_eq]
  rw [Subtype.ext_iff]
  change linearEquiv g (Pi.single 0 1) = Pi.single 0 1 ↔ _
  rw [BinaryLinear.OuterCyclic.slEquivLinear_apply]
  simp [Matrix.mulVec_single, funext_iff, Pi.single_apply]

private theorem row_normalizer_firstColumn (g : SL)
    (hg : g ∈ normalizer (Model.row : Set SL)) :
    ∀ i : Fin 5, g i 0 = if i = 0 then 1 else 0 := by
  have ht : transvection ∈ Model.row := subset_closure ⟨4, by decide, rfl⟩
  have hrow : g * transvection * g⁻¹ ∈ Model.row := (mem_normalizer_iff.mp hg _).mp ht
  have hm := modelRowCoordinates_matrix ⟨_, hrow⟩
  obtain ⟨j, hj⟩ : ∃ j : Fin 5, g⁻¹ 4 j ≠ 0 := by
    by_contra! hn
    exact (g⁻¹).det_ne_zero (Matrix.det_eq_zero_of_row_eq_zero 4 hn)
  have hz (i : Fin 5) (hi : i ≠ 0) : g i 0 = 0 := by
    have he := UniquenessMathieu.SourceNormalizer.conjugate_root_entry g
      (show (0 : Fin 5) < 4 by decide) i j
    change (g * transvection * g⁻¹) i j = _ at he
    have hh := congrFun (congrFun hm i) j
    simp only [Matrix.add_apply, Matrix.single, Matrix.of_apply, Ne.symm hi,
      false_and, if_false, add_zero, Matrix.one_apply] at hh
    have heq : g i 0 * g⁻¹ 4 j = 0 := add_left_cancel (he.symm.trans (hh.trans (add_zero _).symm))
    exact (mul_eq_zero.mp heq).resolve_right hj
  have h00 : g 0 0 = 1 := by
    apply (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1)
    intro he
    apply g.det_ne_zero
    apply Matrix.det_eq_zero_of_column_eq_zero 0
    intro i
    by_cases hi : i = 0
    · simpa only [hi] using he
    · exact hz i hi
  intro i
  by_cases hi : i = 0
  · simpa only [hi, ite_true] using h00
  · simpa only [if_neg hi] using hz i hi

/-- The actual row normalizer is the native vertex stabilizer. -/
theorem native_row_normalizer : rowNormalizer nativeMarking = nativeSystem.system.vertexGroup := by
  change normalizer (nativeMarking.pullback Model.row : Set SL) = _
  rw [nativeMarking_pullback Model.row Model.row_le_centralizer]
  apply le_antisymm
  · intro g hg
    exact (vertex_firstColumn g).mpr (row_normalizer_firstColumn g hg)
  · apply normalizes_closure_of_generators
    rintro g hg _ ⟨j, hj, rfl⟩
    exact row_product_of_firstColumns g g⁻¹ (mul_inv_cancel g)
      ((vertex_firstColumn g).mp hg)
      ((vertex_firstColumn g⁻¹).mp (nativeSystem.system.vertexGroup.inv_mem hg)) j hj

/-- Membership in the native coordinate three-space. -/
theorem native_planeSpace_mem_iff (v : Space) : v ∈ planeSpace ↔ v 3 = 0 ∧ v 4 = 0 := by
  rw [planeSpace, Pi.mem_spanSubset_iff]
  constructor
  · intro h
    exact ⟨h 3 (by decide), h 4 (by decide)⟩
  · rintro ⟨h3, h4⟩ i hi
    fin_cases i <;> simp_all

private theorem rectangle_fixed (v : Space) :
    (∀ a : Model.threeSpace, linearEquiv (a : SL) v = v) ↔ v ∈ planeSpace := by
  rw [native_planeSpace_mem_iff]
  constructor
  · intro h
    have ht (j : Fin 5) (hj : 3 ≤ j.val) : root (show (0 : Fin 5) < j by omega) ∈ Model.threeSpace :=
      subset_closure ⟨0, j, by omega, by decide, hj, rfl⟩
    have hh (j : Fin 5) (hj : 3 ≤ j.val) : v j = 0 := by
      have he := congrFun (h ⟨_, ht j hj⟩) 0
      change ((1 + Matrix.single 0 j 1) *ᵥ v) 0 = v 0 at he
      simpa [Matrix.add_mulVec, Matrix.single_mulVec_eq] using he
    exact ⟨hh 3 (by decide), hh 4 (by decide)⟩
  · rintro ⟨h3, h4⟩ a
    have he := RectangleCoordinates.mem3_iff (a : SL) |>.mp a.property
    funext i
    change ((a : SL).val *ᵥ v) i = v i
    have h0 := he i 0 (by omega)
    have h1 := he i 1 (by omega)
    have h2 := he i 2 (by omega)
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change (a : SL) i 0 * v 0 + ((a : SL) i 1 * v 1 +
      ((a : SL) i 2 * v 2 + ((a : SL) i 3 * v 3 + (a : SL) i 4 * v 4))) = v i
    rw [h0, h1, h2, h3, h4, mul_zero, mul_zero, add_zero, add_zero]
    fin_cases i <;> simp_all

private theorem normalizer_preserves_plane (g : SL)
    (hg : g ∈ normalizer (Model.threeSpace : Set SL)) {v : Space} (hv : v ∈ planeSpace) :
    linearEquiv g v ∈ planeSpace := by
  apply (rectangle_fixed _).mp
  intro a
  have ha : g⁻¹ * (a : SL) * (g⁻¹)⁻¹ ∈ Model.threeSpace :=
    (mem_normalizer_iff.mp ((normalizer _).inv_mem hg) (a : SL)).mp a.property
  have hh := congrArg (linearEquiv g) ((rectangle_fixed v).mpr hv ⟨_, ha⟩)
  change linearEquiv g (linearEquiv (g⁻¹ * (a : SL) * (g⁻¹)⁻¹) v) = _ at hh
  change (linearEquiv g * linearEquiv (g⁻¹ * (a : SL) * (g⁻¹)⁻¹)) v = _ at hh
  rw [← map_mul] at hh
  have he : g * (g⁻¹ * (a : SL) * (g⁻¹)⁻¹) = (a : SL) * g := by group
  rw [he, map_mul] at hh
  exact hh

private theorem plane_lowerLeft (g : SL) (hg : g ∈ planeGroup)
    (i j : Fin 5) (hi : 3 ≤ i.val) (hj : j.val < 3) : g i j = 0 := by
  have hv : (basisPoint j).val ∈ planeSpace := basisPoint_mem_plane (by
    fin_cases j <;> simp_all)
  have he := (hg (basisPoint j).val).mpr hv
  rw [native_planeSpace_mem_iff] at he
  have hm : (linearEquiv g (basisPoint j).val) i = 0 := by
    fin_cases i <;> simp_all
  simpa [basisPoint, BinaryLinear.OuterCyclic.slEquivLinear_apply,
    Matrix.mulVec_single] using hm

/-- The second rectangle normalizer is the native plane stabilizer. -/
theorem native_threeSpace_normalizer : sourceThreeSpaceNormalizer nativeMarking = planeGroup := by
  change normalizer (nativeMarking.pullback Model.threeSpace : Set SL) = _
  rw [nativeMarking_pullback Model.threeSpace Model.threeSpace_le_centralizer]
  apply le_antisymm
  · intro g hg v
    constructor
    · intro hv
      have h := normalizer_preserves_plane g⁻¹ ((normalizer _).inv_mem hg) hv
      change linearEquiv g⁻¹ (linearEquiv g v) ∈ planeSpace at h
      change (linearEquiv g⁻¹ * linearEquiv g) v ∈ planeSpace at h
      rw [← map_mul, inv_mul_cancel, map_one] at h
      exact h
    · exact normalizer_preserves_plane g hg
  · apply normalizes_closure_of_generators
    rintro g hg _ ⟨i, j, hij, hi, hj, rfl⟩
    apply (RectangleCoordinates.mem3_iff _).mpr
    intro a b hab
    rw [UniquenessMathieu.SourceNormalizer.conjugate_root_entry]
    by_cases ha : a.val < 3
    · have hb : b.val < 3 := by omega
      rw [plane_lowerLeft g⁻¹ (planeGroup.inv_mem hg) j b hj hb, mul_zero, add_zero]
    · rw [plane_lowerLeft g hg a i (by omega) hi, zero_mul, add_zero]

open SourceGeometry GraphUniquenessSystem.Cosets

/-- The two literal normalizers generate the native matrix group. -/
theorem native_normalizers_generate :
    rowNormalizer nativeMarking ⊔ sourceThreeSpaceNormalizer nativeMarking = ⊤ := by
  rw [native_row_normalizer, native_threeSpace_normalizer, sup_comm]
  exact nativeSystem.local_eq ▸ nativeSystem.system.generate

private theorem native_coset_eq_iff (g h : SL) :
    g • basisPoint 0 = h • basisPoint 0 ↔
      vertex (rowNormalizer nativeMarking) g = vertex (rowNormalizer nativeMarking) h := by
  rw [vertex_eq_iff, native_row_normalizer]
  change _ ↔ (g⁻¹ * h) • nativeSystem.system.x = nativeSystem.system.x
  rw [nativeSystem.point_eq, mul_smul, inv_smul_eq_iff, eq_comm]

private def nativePointMap : Vertex (rowNormalizer nativeMarking) → Point :=
  Quotient.lift (fun g : SL => g • basisPoint 0) (by
    intro g h hgh
    exact (native_coset_eq_iff g h).mpr (Quotient.sound hgh))

/-- Literal row-normalizer cosets are the nonzero native vectors. -/
def nativePointEquiv : Vertex (rowNormalizer nativeMarking) ≃ Point :=
  Equiv.ofBijective nativePointMap (by
    constructor
    · intro a b
      induction a using QuotientGroup.induction_on with
      | H a =>
        induction b using QuotientGroup.induction_on with
        | H b => exact (native_coset_eq_iff a b).mp
    · intro v
      obtain ⟨g, hg⟩ := nativeSystem.system.vertex_transitive v
      refine ⟨QuotientGroup.mk g, ?_⟩
      change g • basisPoint 0 = v
      simpa only [nativeSystem.point_eq] using hg)

/-- A source coset is sent to its representative acting on the native base point. -/
theorem nativePointEquiv_vertex (g : SL) :
    nativePointEquiv (vertex (rowNormalizer nativeMarking) g) = g • basisPoint 0 := by rfl

/-- The point identification retains the original left action. -/
theorem nativePointEquiv_smul (g : SL) (x : Vertex (rowNormalizer nativeMarking)) :
    nativePointEquiv (g • x) = g • nativePointEquiv x := by
  induction x using QuotientGroup.induction_on with
  | H h => exact mul_smul g h (basisPoint 0)

/-- The literal chosen source edge, now in the native nonzero-vector action. -/
def nativeSourceNeighbor : Point :=
  (planeSwap nativeMarking nativeMarking_linearFusion : SL) • basisPoint 0

/-- The chosen source edge has distinct native endpoints. -/
theorem nativeSourceNeighbor_ne : nativeSourceNeighbor ≠ basisPoint 0 := by
  intro he
  have hm : (planeSwap nativeMarking nativeMarking_linearFusion : SL) ∈
      nativeSystem.system.vertexGroup := by
    change (planeSwap nativeMarking nativeMarking_linearFusion : SL) • nativeSystem.system.x = _
    rw [nativeSystem.point_eq]
    exact he
  rw [← native_row_normalizer] at hm
  exact planeSwap_not_row nativeMarking nativeMarking_linearFusion hm

/-- The chosen native neighbor lies in the actual coordinate plane. -/
theorem nativeSourceNeighbor_mem : nativeSourceNeighbor.val ∈ planeSpace := by
  have hm := planeSwap_mem nativeMarking nativeMarking_linearFusion
  rw [native_threeSpace_normalizer] at hm
  exact (hm (basisPoint 0).val).mpr (basisPoint_mem_plane (by simp))

/-- The whole source edge fixer is the literal vector-pair fixer. -/
theorem native_source_edgeGroup :
    SourceGeometry.edgeGroup nativeMarking nativeMarking_linearFusion =
      edgeFixer SL (basisPoint 0) nativeSourceNeighbor := by
  change edgeFixer SL (vertex (rowNormalizer nativeMarking) 1)
    (vertex (rowNormalizer nativeMarking) (lineSwap nativeMarking nativeMarking_linearFusion : SL)) = _
  rw [← planeSwap_vertex]
  ext g
  change (g • vertex (rowNormalizer nativeMarking) 1 = vertex (rowNormalizer nativeMarking) 1 ∧
    g • vertex (rowNormalizer nativeMarking) (planeSwap nativeMarking nativeMarking_linearFusion : SL) =
      vertex (rowNormalizer nativeMarking) (planeSwap nativeMarking nativeMarking_linearFusion : SL)) ↔ _
  rw [← nativePointEquiv.injective.eq_iff, ← nativePointEquiv.injective.eq_iff]
  simp only [nativePointEquiv_smul, nativePointEquiv_vertex, one_smul]
  rfl


/-- The constructed maps land in the actual two local groups of the native
uniqueness system and preserve the full pointwise edge stabilizer. -/
theorem exists_native_system_local_maps {G : Type*} [Group G] [Finite G] {z : G}
    (F : MarkedCentralizer z) (hlinear : F.LinearFusion) :
    ∃ (r : rowNormalizer F ≃* nativeSystem.system.vertexGroup)
      (t : sourceThreeSpaceNormalizer F ≃* nativeSystem.system.H),
      (∀ (g : G) (hr : g ∈ rowNormalizer F) (ht : g ∈ sourceThreeSpaceNormalizer F),
        (r ⟨g, hr⟩ : SL) = (t ⟨g, ht⟩ : SL)) ∧
      (∀ h : sourceThreeSpaceNormalizer F, (h : G) ∈ rowNormalizer F ↔
        (t h : SL) ∈ nativeSystem.system.vertexGroup) ∧
      (∀ a : rowNormalizer F, (a : G) ∈ SourceGeometry.edgeGroup F hlinear ↔
        (r a : SL) ∈ edgeFixer SL (basisPoint 0) nativeSourceNeighbor) := by
  obtain ⟨r, t, _, _, he, ht, ha⟩ := exists_compatible_native_maps F hlinear
  have hr (a : rowNormalizer F) :
      (a : G) ∈ SourceGeometry.edgeGroup F hlinear ↔
        (r a : SL) ∈ SourceGeometry.edgeGroup nativeMarking nativeMarking_linearFusion := by
    change a ∈ (SourceGeometry.edgeGroup F hlinear).subgroupOf (rowNormalizer F) ↔
      r a ∈ (SourceGeometry.edgeGroup nativeMarking nativeMarking_linearFusion).subgroupOf _
    rw [← he]
    exact (mem_map_iff_mem r.injective).symm
  have hl (h : sourceThreeSpaceNormalizer F) :
      (h : G) ∈ rowNormalizer F ↔ (t h : SL) ∈ rowNormalizer nativeMarking := by
    change h ∈ (rowNormalizer F).subgroupOf _ ↔ t h ∈ (rowNormalizer nativeMarking).subgroupOf _
    rw [← ht]
    exact (mem_map_iff_mem t.injective).symm
  have hh : ∃ (r : rowNormalizer F ≃* rowNormalizer nativeMarking)
      (t : sourceThreeSpaceNormalizer F ≃* sourceThreeSpaceNormalizer nativeMarking),
      (∀ (g : G) (hr : g ∈ rowNormalizer F) (ht : g ∈ sourceThreeSpaceNormalizer F),
        (r ⟨g, hr⟩ : SL) = (t ⟨g, ht⟩ : SL)) ∧
      (∀ h : sourceThreeSpaceNormalizer F, (h : G) ∈ rowNormalizer F ↔
        (t h : SL) ∈ rowNormalizer nativeMarking) ∧
      (∀ a : rowNormalizer F, (a : G) ∈ SourceGeometry.edgeGroup F hlinear ↔
        (r a : SL) ∈ SourceGeometry.edgeGroup nativeMarking nativeMarking_linearFusion) :=
    ⟨r, t, ha, hl, hr⟩
  rw [native_row_normalizer, native_threeSpace_normalizer, native_source_edgeGroup] at hh
  rw [nativeSystem.local_eq]
  exact hh

/-- The literal induction subgroup has these native local comparisons without
any simplicity assumption on that subgroup. -/
theorem normalizerSpan_native_system_local_maps {G : Type*} [Group G] [Finite G] {z : G}
    (F : MarkedCentralizer z) (hlinear : F.LinearFusion) :
    ∃ (r : rowNormalizer (normalizerSpanMarking F) ≃* nativeSystem.system.vertexGroup)
      (t : sourceThreeSpaceNormalizer (normalizerSpanMarking F) ≃* nativeSystem.system.H),
      (∀ (g : normalizerSpan F) (hr : g ∈ rowNormalizer (normalizerSpanMarking F))
        (ht : g ∈ sourceThreeSpaceNormalizer (normalizerSpanMarking F)),
        (r ⟨g, hr⟩ : SL) = (t ⟨g, ht⟩ : SL)) ∧
      (∀ h : sourceThreeSpaceNormalizer (normalizerSpanMarking F),
        (h : normalizerSpan F) ∈ rowNormalizer (normalizerSpanMarking F) ↔
        (t h : SL) ∈ nativeSystem.system.vertexGroup) ∧
      (∀ a : rowNormalizer (normalizerSpanMarking F),
        (a : normalizerSpan F) ∈ SourceGeometry.edgeGroup (normalizerSpanMarking F)
          (normalizerSpan_linearFusion F hlinear) ↔
        (r a : SL) ∈ edgeFixer SL (basisPoint 0) nativeSourceNeighbor) :=
  exists_native_system_local_maps (normalizerSpanMarking F) (normalizerSpan_linearFusion F hlinear)

end Theory.GroupTheory.TransvectionFive.UniquenessLinear
