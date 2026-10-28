module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceNativeFusion
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.RowComparison
public import Theory.GroupTheory.SubgroupCenterImageBound
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceLocalIsomorphisms


/-!
# Inner automorphisms of the full Mathieu point–plane intersection

The linear and Mathieu row normalizers are the same split natural extension.
Their marked row isomorphism preserves the literal two-space normalizer, so
it restricts to an isomorphism of the full point–plane intersections.

In the linear intersection, the proved marked automorphism theorem gives
innerness for automorphisms fixing z. Its Sylow two-subgroup has center
exactly ⟨z⟩. Sylow conjugacy therefore adjusts any automorphism to fix z,
proving full innerness. Transport through the constructed intersection
isomorphism proves the same assertion for the original Mathieu subgroup.
No linear fusion assumption is imposed on the Mathieu marking.

This supplies Aschbacher, *Sporadic Groups* (1994), 41.3, printed p.222,
using the existing marked proof and the common row-parabolic structure.
Its consumer is the actual overlap correction in `Source.Similarity`.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer

private theorem inner_of_sylow_center {H : Type*} [Group H] [Finite H]
    (P : Sylow 2 H) (z : H) (hz : orderOf z = 2)
    (hc : (center P).map (P : Subgroup H).subtype = zpowers z)
    (hi : ∀ a : MulAut H, a z = z → ∃ c : H, a = MulAut.conj c) :
    Function.Surjective (MulAut.conj : H →* MulAut H) := by
  classical
  intro a
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq H (a • P) P
  let b : MulAut H := MulAut.conj g * a
  have hb : (P : Subgroup H).map b.toMonoidHom = P :=
    by
      rw [Sylow.smul_def, ← mul_smul] at hg
      exact congrArg Sylow.toSubgroup hg
  have hzmap : (zpowers z).map b.toMonoidHom = zpowers z := by
    rw [← hc, map_subgroup_center_eq _ b.injective, hb]
  have hmem : b z ∈ zpowers z := hzmap ▸ mem_map_of_mem b.toMonoidHom (mem_zpowers z)
  have hne : b z ≠ 1 := by
    intro h
    have he : z = 1 := b.injective (h.trans b.map_one.symm)
    simp [he] at hz
  have hbz : b z = z := by
    rw [mem_zpowers_iff_mem_range_orderOf, hz] at hmem
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hmem
    have hn2 := Finset.mem_range.mp hn
    interval_cases n
    · exact (hne (by simpa using he.symm)).elim
    · simpa using he.symm
  obtain ⟨c,hc⟩ := hi b hbz
  refine ⟨g⁻¹*c,?_⟩
  apply MulEquiv.ext
  intro x
  have he := congrArg (fun f : MulAut H => f x) hc
  change g * a x * g⁻¹ = c * x * c⁻¹ at he
  change (g⁻¹*c)*x*(g⁻¹*c)⁻¹ = a x
  calc
    _ = g⁻¹ * (c*x*c⁻¹) * g := by group
    _ = _ := by rw [← he]; group

/-- Full innerness of the shared point–plane parabolic in the linear model. -/
theorem linear_point_plane_inner {G : Type*} [Group G] [Finite G] {z : G}
    (F : MarkedCentralizer z) (hlinear : F.LinearFusion) :
    Function.Surjective (MulAut.conj : rowThreeIntersection F →*
      MulAut (rowThreeIntersection F)) := by
  let I := rowThreeIntersection F
  let P := (sourceSylow F).subtype (sylow_le_rowThreeIntersection F)
  let p : I := ⟨z, threeSpace_le_rowThreeIntersection F (point_mem_threeSpace F)⟩
  have hP : (P : Subgroup I).map I.subtype = (sourceSylow F : Subgroup G) :=
    map_subgroupOf_eq_of_le (sylow_le_rowThreeIntersection F)
  have hc : (center P).map (P : Subgroup I).subtype = zpowers p := by
    apply Subgroup.map_injective I.subtype_injective
    rw [map_subgroup_center_eq _ I.subtype_injective, hP, sourceSylow_center,
      MonoidHom.map_zpowers]
    rfl
  apply inner_of_sylow_center P p
    ((orderOf_injective I.subtype I.subtype_injective p).symm.trans F.point_orderOf) hc
  intro a ha
  obtain ⟨c,_,hc⟩ := intersection_point_automorphism_inner F hlinear a ha
  exact ⟨c,hc⟩


variable {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
  {z : G} {z' : G'} (F : MarkedCentralizer z) (F' : MarkedCentralizer z')

/-- The shared split row structure gives a marked comparison across fusion types. -/
theorem exists_linear_row_equiv (D : LocalData F) (h' : F'.LinearFusion) :
    ∃ e : rowNormalizer F ≃* rowNormalizer F',
      ∀ a : F.row, e (inclusion F.row.le_normalizer a) =
        inclusion F'.row.le_normalizer (rowMarkingEquiv F F' a) := by
  let q := (LocalData.rowEquiv F D).trans (linearRowQuotientEquiv F' h').symm
  obtain ⟨e,he,_⟩ := split_normalizer_equiv F.row F'.row (rowMarkingEquiv F F') q
    (rowQuotientAction F')
    (fun n a => Subtype.ext (rowQuotientAction_mk_apply F' n a)) (by
      intro n a
      obtain ⟨n', hn'⟩ := QuotientGroup.mk'_surjective
        (F'.row.subgroupOf (rowNormalizer F')) (q (QuotientGroup.mk n))
      rw [← hn']
      have hq : linearRowQuotientEquiv F' h' (QuotientGroup.mk n') =
          LocalData.rowEquiv F D (QuotientGroup.mk n) := by
        change linearRowQuotientEquiv F' h' ((QuotientGroup.mk' _) n') = _
        rw [hn']
        exact (linearRowQuotientEquiv F' h').apply_symm_apply _
      have he : rowQuotientAction F' (QuotientGroup.mk n') (rowMarkingEquiv F F' a) =
          F'.row.normalizerMonoidHom n' (rowMarkingEquiv F F' a) :=
        Subtype.ext (rowQuotientAction_mk_apply F' n' _)
      change rowMarkingEquiv F F' (F.row.normalizerMonoidHom n a) =
        rowQuotientAction F' (QuotientGroup.mk n') (rowMarkingEquiv F F' a)
      rw [he]
      apply (rowCoordinates F').injective
      apply Multiplicative.toAdd.injective
      rw [UniquenessLinear.rowMarkingEquiv_coordinates, ← LocalData.rowEquiv_action F D,
        ← linearRowQuotientEquiv_action F' h', hq, UniquenessLinear.rowMarkingEquiv_coordinates])
    (rowQuotientAction_injective F') (row_normalizer_splits F) (row_normalizer_splits F')
  exact ⟨e,he⟩

private def intersectionSubgroupEquiv {H : Type*} [Group H] (A B : Subgroup H) :
    ↥(A ⊓ B) ≃* B.subgroupOf A :=
  (subgroupOfEquivOfLe (show A ⊓ B ≤ A from inf_le_left)).symm.trans
    (MulEquiv.subgroupCongr (inf_subgroupOf_left B A))

/-- The full literal Mathieu overlap is isomorphic to the shared linear overlap. -/
theorem exists_linear_point_plane_equiv (D : LocalData F) (h' : F'.LinearFusion) :
    Nonempty (↥(rowNormalizer F ⊓ threeSpaceNormalizer F) ≃* rowThreeIntersection F') := by
  obtain ⟨e,he⟩ := exists_linear_row_equiv F F' D h'
  have hI := row_normalizer_equiv_threeSpace_intersection F F' e he
  exact ⟨(intersectionSubgroupEquiv (rowNormalizer F) (threeSpaceNormalizer F)).trans
    ((e.subgroupMap _).trans ((MulEquiv.subgroupCongr hI).trans
      (intersectionSubgroupEquiv (rowNormalizer F') (sourceThreeSpaceNormalizer F')).symm))⟩

omit F' in
/-- Source 41.3 for the actual Mathieu point–plane subgroup. -/
theorem point_plane_inner (D : LocalData F) :
    Function.Surjective (MulAut.conj : ↥(rowNormalizer F ⊓ threeSpaceNormalizer F) →*
      MulAut ↥(rowNormalizer F ⊓ threeSpaceNormalizer F)) := by
  obtain ⟨e⟩ := exists_linear_point_plane_equiv F nativeMarking D nativeMarking_linearFusion
  intro a
  obtain ⟨c,hc⟩ := linear_point_plane_inner nativeMarking nativeMarking_linearFusion
    (e.symm.trans (a.trans e))
  refine ⟨e.symm c,?_⟩
  apply MulEquiv.ext
  intro x
  apply e.injective
  have hh := congrArg (fun f : MulAut (rowThreeIntersection nativeMarking) => f (e x)) hc
  change c * e x * c⁻¹ = e (a (e.symm (e x))) at hh
  rw [e.symm_apply_apply] at hh
  change e (e.symm c * x * (e.symm c)⁻¹) = e (a x)
  simpa only [map_mul,map_inv,e.apply_symm_apply] using hh

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
