module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialKernelCoreDisplacement
public import Theory.GroupTheory.QuadraticCoreActor

/-!
# The fixed subgroup and a crossed conjugate generate a two-group

The centralizer two-core moves the fixed subgroup only inside the moved plane.
For an element centralizing that plane, the fixed subgroup and its conjugate
both centralize the plane.  The quadratic-core actor lemma therefore makes
their join a two-group.  This is a genuine crossed-pair restriction; it does
not identify the two fixed subgroups.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open Section02.ChosenGeometry.Cyclic
variable {G : Type*} [Group G] [Finite G]

set_option backward.isDefEq.respectTransparency false in
/-- A centralizer element can only produce a two-group crossed fixed pair. -/
theorem PreparedChosenModule.extraspecial_moved_fixed_pair_two
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (g : G) (hg : g ∈ centralizer
      ((⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ : Subgroup G) : Set G)) :
    IsPGroup 2 (thompsonFixed T V ⊔
      (thompsonFixed T V).map (MulAut.conj g).toMonoidHom : Subgroup G) := by
  let := h.elementary
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  let E := thompsonFixed T V
  let Eg := E.map (MulAut.conj g).toMonoidHom
  let C := centralizer (U : Set G)
  let Q := C.pCoreIn 2
  have hcore := h.extraspecial_moved_centralizer_twoCore
    hG T hempty hM hmany hJ hu hfull hex
  change C.pCoreIn 2 = Mc.pCoreIn 2 ∧ _ at hcore
  rcases hcore with ⟨_,_,_,hselfQ⟩
  have hdisp := h.extraspecial_moved_centralizer_core_displacement
    hG T hempty hM hmany hJ hu hfull hex
  change ⁅Q,E⁆ ≤ U at hdisp
  have hUE : U ≤ E := by
    exact h.extraspecial_thompson_moved_le_fixed hG T hempty hM hmany hJ hfull hex
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 Eg := IsElementaryAbelian.map
    (MulAut.conj g).toMonoidHom
  have hEcentral : E ≤ C := by
    exact (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le hUE)
  have hEgcentral : Eg ≤ C := by
    rintro _ ⟨e, he, rfl⟩
    exact C.mul_mem (C.mul_mem hg (hEcentral he)) (C.inv_mem hg)
  have hCnorm : C ≤ normalizer (Q : Set G) :=
    C.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hQnorm : E ≤ normalizer (Q : Set G) := by
    exact hEcentral.trans hCnorm
  have hEgNorm : Eg ≤ normalizer (Q : Set G) := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := hx
    exact (normalizer (Q : Set G)).mul_mem
      ((normalizer (Q : Set G)).mul_mem (hCnorm hg) (hQnorm he))
      ((normalizer (Q : Set G)).inv_mem (hCnorm hg))
  have hself : (E ⊔ Eg) ⊓ centralizer (Q : Set G) ≤ Q := by
    intro x hx
    have hxC : x ∈ C := (sup_le hEcentral hEgcentral) hx.1
    exact hselfQ ⟨hxC, hx.2⟩
  apply Subgroup.isPGroup_sup_of_centralized_displacement Q E Eg U
    (isPGroup_pCoreIn 2 C) (IsElementaryAbelian.isPGroup 2 Eg)
    hQnorm hEgNorm hself hdisp
  · exact hEcentral
  · exact hEgcentral

end CFSG.Quasithin.Chapter15.Section01
