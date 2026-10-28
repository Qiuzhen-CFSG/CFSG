module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialKernelIntersection
public import Theory.GroupTheory.ChainCentralizerTwoCore

/-!
# The exact-intersection branch has nontrivial upper displacement

Let U be the original moved four-group and Q=O₂(C_G(U)). If the full
module's Q-displacement lay in U, it would stabilize the normal chain
Q > U > 1 and centralize U. The characteristic-two chain lemma would
put V in Q. Therefore the alternative V ∩ Q = E has displacement
strictly beyond U, since the actual orders of V and E are 64 and 16.

This restricts the original core action without assuming its image or
claiming the remaining centralizer normalization.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- In the exact sixteen-intersection branch, the original two-core's
full-module displacement cannot be contained in the moved four-group. -/
theorem PreparedChosenModule.extraspecial_exact_intersection_core_displacement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (heq : V ⊓ (centralizer ((⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ : Subgroup G) : Set G)).pCoreIn 2 =
      thompsonFixed T V) :
    ¬ ⁅(centralizer ((⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ : Subgroup G) : Set G)).pCoreIn 2,V⁆ ≤
      ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ := by
  let := h.elementary
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  let C := centralizer (U : Set G)
  let Q := C.pCoreIn 2
  have hUV : U ≤ V := (h.extraspecial_thompson_moved_le_fixed
    hG T hempty hM hmany hJ hfull hex).trans inf_le_left
  have hVC : V ≤ C := V.le_centralizer.trans (centralizer_le hUV)
  have hUC : U ≤ C := hUV.trans hVC
  have hCQ : C ≤ normalizer (Q : Set G) := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hself : C ⊓ centralizer (Q : Set G) ≤ Q :=
    (h.extraspecial_moved_centralizer_twoCore hG T hempty hM hmany hJ hu hfull hex).2.2.2
  intro hdisp
  have hVQ : V ≤ Q := le_twoCore_of_relative_chain C Q U V
    (pCoreIn_le 2 C) hUC hVC hCQ (Subgroup.centralizer_le_normalizer _)
    (isPGroup_pCoreIn 2 C) hself hVC (by rwa [commutator_comm])
  have hVE : V = thompsonFixed T V := (inf_eq_left.mpr hVQ).symm.trans heq
  have hEcard := h.extraspecial_thompson_fixed_card hG T hempty hM hmany hJ hfull hex
  obtain ⟨_,_,_,_,_,_,hdim,_⟩ := hex
  have hVcard : Nat.card V = 64 := by
    change Nat.card (Additive V) = 64
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hdim]
    norm_num
  rw [←hVE,hVcard] at hEcard
  omega

end CFSG.Quasithin.Chapter15.Section01
