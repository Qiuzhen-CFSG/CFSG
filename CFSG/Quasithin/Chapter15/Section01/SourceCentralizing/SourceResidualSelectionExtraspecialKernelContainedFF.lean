module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialKernelContainedCore
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialKernelThreeStep
public import Theory.GroupTheory.ElementaryThompsonNormalizerControl
import all CFSG.Quasithin.ChapterD.Section01.UniqueFactor.SourceThompson

/-!
# The actual partner action on the full-module span is an FF action

The three-step core argument places the original V in O₂(C_G(U)). Its
centralizer span H is therefore elementary, normal under Mc, and contained
in both original local two-cores. H is strictly larger than V, since otherwise
Mc would normalize V and lie in M. Moreover J(T) moves H: Thompson Frattini
control would otherwise put Mc in M, since C_G(H)≤C_G(V)≤M and N_G(J(T))≤M.
The maximum-elementary offender criterion gives the actual FF action on H.
No chief-factor classification or normalization of the original E is inferred.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The original extraspecial source supplies a strictly larger elementary
common-core span with a genuine FF action of the same partner Mc. -/
theorem PreparedChosenModule.extraspecial_partner_full_span_ff
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
    let C := centralizer (U : Set G)
    let H := conjugateSpanBy V C
    ∃ (hn : Mc ≤ normalizer (H : Set G)) (he : IsElementaryAbelian 2 H),
      letI := he
      V < H ∧ H ≤ M.pCoreIn 2 ⊓ C.pCoreIn 2 ∧
        ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (H : Set G) ∧
        IsFFModule (imageRepresentation Mc H hn) := by
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  let C := centralizer (U : Set G)
  let H := conjugateSpanBy V C
  have hVQ := h.extraspecial_module_le_moved_centralizer_twoCore
    hG T hempty hM hmany hJ hu hfull hex
  have hs := h.extraspecial_contained_module_span
    hG T hempty hM hmany hJ hu hfull hex hVQ
  have hcore := h.extraspecial_moved_centralizer_twoCore
    hG T hempty hM hmany hJ hu hfull hex
  have hHM := (h.extraspecial_contained_span_le_selected_core
    hG T hempty hM hmany hJ hu hfull hex hVQ).1
  have htwo := h.maximal_overgroups_of_full_extraspecial
    hG T hempty hM hmany hJ hu hfull hex
  have hMc : Mc ∈ maximalTwoLocalOvergroups (T : Subgroup G) := by
    rw [htwo]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hne : Mc ≠ M := by
    intro he
    rw [htwo,he] at hmany
    simp at hmany
  have hNM : normalizer (V : Set G) ≤ M := by
    let := h.elementary
    exact hM.1.1.2 ⟨V,h.nontrivial,IsElementaryAbelian.isPGroup 2 V,rfl⟩ h.normalized
  have hCM : centralizer (H : Set G) ≤ M :=
    (centralizer_le (le_conjugateSpanBy V C)).trans
      ((Subgroup.centralizer_le_normalizer _).trans hNM)
  have hnot : ¬ Mc ≤ M := fun hh => hne (hMc.1.eq_of_le hM.1.1.1 hh)
  have hVH : V < H := lt_of_le_of_ne (le_conjugateSpanBy V C) (by
    intro he
    have hn : normalizer (H : Set G) = normalizer (V : Set G) :=
      congrArg (fun W : Subgroup G => normalizer (W : Set G)) he.symm
    exact hnot (hs.2.2.1.trans (hn.le.trans hNM)))
  have hJT : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (H : Set G) := by
    intro hj
    have hm : (((T.subtype hMc.2 : Sylow 2 Mc) : Subgroup Mc).map Mc.subtype) =
        (T : Subgroup G) := map_subgroupOf_eq_of_le hMc.2
    apply hnot
    apply le_of_thompson_normalizer_centralizer_control Mc M H (T.subtype hMc.2)
      hs.2.2.1 (inf_le_right.trans hCM)
    · simpa only [hm] using hj
    · simpa only [hm] using (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1
  let := hs.1
  refine ⟨hs.2.2.1,hs.1,hVH,le_inf hHM hs.2.1,hJT,?_⟩
  exact image_isFF_of_maxJ_not_centralizes Mc (T : Subgroup G) H hMc.2
    (hs.2.1.trans hcore.2.1) hs.2.2.1 hJT

end CFSG.Quasithin.Chapter15.Section01
