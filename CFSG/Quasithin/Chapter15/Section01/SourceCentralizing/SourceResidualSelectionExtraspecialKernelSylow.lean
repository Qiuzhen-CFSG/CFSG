module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialPartnerPlane
public import Theory.GroupTheory.SylowCentralizerOfNormalizer

/-!
# The literal kernel Sylow has the original first Thompson subgroup

The original Sylow group normalizes the moved plane U. Its centralizer
S₀ = C_T(U) is therefore a Sylow subgroup of C_G(U). Since U lies in
C_V(J₁(T)), the same S₀ contains J₁(T), and Thompson inheritance gives
J₁(S₀) = J₁(T). Thus the kernel fusion problem retains the original
Thompson omega-center. No normalization by the kernel is asserted.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The actual centralizer kernel has Sylow C_T(U), normal in T, with
exactly the original first Thompson subgroup and containing the same fixed
subgroup in its Thompson omega-center. -/
theorem PreparedChosenModule.extraspecial_kernel_sylow_thompson
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
    let C := centralizer (U : Set G)
    let S₀ := (T : Subgroup G) ⊓ C
    (∃ Q : Sylow 2 C, (Q : Subgroup C).map C.subtype = S₀) ∧
      (S₀.subgroupOf (T : Subgroup G)).Normal ∧
      ChapterB.thompsonJ S₀ 1 = ChapterB.thompsonJ (T : Subgroup G) 1 ∧
      elementaryAbelianMaxJ S₀ = elementaryAbelianMaxJ (T : Subgroup G) ∧
      thompsonFixed T V ≤ omegaOneCenterAmbient (ChapterB.thompsonJ S₀ 1) := by
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  let C := centralizer (U : Set G)
  let S₀ := (T : Subgroup G) ⊓ C
  have hTJ : (T : Subgroup G) ≤ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) :=
    ChapterB.le_normalizer_thompsonJ (T : Subgroup G) 1
  have hTU : (T : Subgroup G) ≤ normalizer (U : Set G) := by
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    have htV : V.map (MulAut.conj t).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp (h.normalized (hM.1.2 ht))
    have htJ : (ChapterB.thompsonJ (T : Subgroup G) 1).map (MulAut.conj t).toMonoidHom =
        ChapterB.thompsonJ (T : Subgroup G) 1 := mem_normalizer_iff_map_conj_eq.mp (hTJ ht)
    change (⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆).map (MulAut.conj t).toMonoidHom = _
    rw [map_commutator,htV,htJ]
  obtain ⟨Q,hQ⟩ := T.exists_centralizer_sylow_of_normalizes U hTU
  have hTC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    hTU.trans (normalizer_le_normalizer_centralizer _)
  have hTS₀ : (T : Subgroup G) ≤ normalizer (S₀ : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer hTC).trans inf_normalizer_le_normalizer_inf
  have hn : (S₀.subgroupOf (T : Subgroup G)).Normal := normal_subgroupOf_of_le_normalizer hTS₀
  have hUE := h.extraspecial_thompson_moved_le_fixed hG T hempty hM hmany hJ hfull hex
  have hJC : ChapterB.thompsonJ (T : Subgroup G) 1 ≤ C :=
    le_centralizer_iff.mp (hUE.trans inf_le_right)
  have hJS₀ : ChapterB.thompsonJ (T : Subgroup G) 1 ≤ S₀ :=
    le_inf (ChapterB.thompsonJ_le _ _) hJC
  have hr : 1 < ChapterB.twoRank (T : Subgroup G) := by
    let := h.elementary
    exact chosen_twoRank_gt_one_of_quadraticRatio_two T hM.1.2 h.le_selected
      h.normalized h.quadratic_ratio
  have he : ChapterB.thompsonJ S₀ 1 = ChapterB.thompsonJ (T : Subgroup G) 1 :=
    (ChapterB.lemma_B_2_3_3 (T : Subgroup G) S₀ hr hJS₀ inf_le_left).symm
  have hJ₀S₀ : elementaryAbelianMaxJ (T : Subgroup G) ≤ S₀ :=
    le_inf (sSup_le fun _ hA => hA.1)
      (hJ.trans (centralizer_le ((hUE.trans inf_le_left).trans h.le_local)))
  have hJ₀ : elementaryAbelianMaxJ S₀ = elementaryAbelianMaxJ (T : Subgroup G) :=
    elementaryAbelianMaxJ_eq_of_intermediate (T : Subgroup G) S₀ hJ₀S₀ inf_le_left
  refine ⟨⟨Q,hQ⟩,hn,he,hJ₀,?_⟩
  rw [he]
  exact h.thompsonFixed_le_omega T hM

end CFSG.Quasithin.Chapter15.Section01
