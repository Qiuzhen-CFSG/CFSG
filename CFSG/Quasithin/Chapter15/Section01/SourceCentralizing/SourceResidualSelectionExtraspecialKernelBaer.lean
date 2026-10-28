module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialKernelPair
public import Theory.GroupTheory.BaerSuzukiLocal

/-!
# The fixed subgroup lies in the moved-plane centralizer's two-core

The crossed-pair two-group result is exactly the relative Baer--Suzuki
criterion inside `C_G(U)`.  It therefore places the original fixed subgroup
inside `O₂(C_G(U))`.  This is an intrinsic containment and does not identify
the fixed subgroup with the core or claim that the core normalizes it.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open Section02.ChosenGeometry.Cyclic
variable {G : Type*} [Group G] [Finite G]

set_option backward.isDefEq.respectTransparency false in
/-- The original fixed subgroup is contained in the relative two-core of its
moved-plane centralizer. -/
theorem PreparedChosenModule.extraspecial_moved_fixed_le_centralizer_twoCore
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    thompsonFixed T V ≤
      (centralizer ((⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ : Subgroup G) : Set G)).pCoreIn 2 := by
  let := h.elementary
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  let E := thompsonFixed T V
  let C := centralizer (U : Set G)
  have hUE : U ≤ E := by
    exact h.extraspecial_thompson_moved_le_fixed hG T hempty hM hmany hJ hfull hex
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
  have hEC : E ≤ C := by
    exact (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le hUE)
  exact le_pCoreIn_of_conjugate_sup_isPGroup C E hEC
    (IsElementaryAbelian.isPGroup 2 E) (by
      intro g hg
      exact h.extraspecial_moved_fixed_pair_two
        hG T hempty hM hmany hJ hu hfull hex g hg)

end CFSG.Quasithin.Chapter15.Section01
