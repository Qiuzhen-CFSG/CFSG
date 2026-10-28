module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialAction
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialAmbient
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionFifteenKernel

/-!
# Original ambient alternatives in the full extraspecial row

A third maximal local has a symmetric-three action on its own local module.
Source ordering places that module inside the original Thompson fixed
subgroup. Original H-star residual centralization therefore bounds the
three-rank of every H-star residual contained in that third local by one.
The no-third alternative retains the actual maximal-overgroup pair and
its independently proved fixed-normalizer placement. Neither branch is
promoted to the unresolved global residual normalization.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

private theorem full_seed_le_fixed (T : Sylow 2 G) {M V : Subgroup G}
    (hfull : V = localModule T M) : centralInvolutions T ≤ thompsonFixed T V := by
  refine le_inf ?_ ?_
  · rw [hfull]
    exact le_conjugateSpanBy _ _
  · intro z hz j hj
    exact ((mem_omegaOneCenterAmbient_iff _ z).mp hz).2.2 j
      (ChapterB.thompsonJ_le _ _ hj)

/-- The third local's own module is inside the original fixed four-space;
no equality with that four-space is asserted. -/
theorem PreparedChosenModule.extraspecial_third_module_le_fixed
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V N : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    localModule T N ≤ thompsonFixed T V := by
  have hn := (h.extraspecial_third_intersection hG T hempty hM hmany hJ hu hfull hex
    hN hNM hNMc).2.2
  have hord := source_ordering_of_centralizing_orderingMaximal hG T hempty hM hJ N hN
  change conjugateSpanBy (centralInvolutions T) N ≤ _
  apply (closure_le _).mpr
  rintro x ⟨n,hnN,z,hz,rfl⟩
  obtain ⟨a,ha,c,hc,rfl⟩ := hord n hnN
  have hcz := mem_centralizer_iff.mp hc.2 z
    (le_conjugateSpanBy (centralInvolutions T) N hz)
  have he : (a*c)*z*(a*c)⁻¹ = a*z*a⁻¹ := by
    calc
      _ = a*(c*z)*c⁻¹*a⁻¹ := by group
      _ = a*(z*c)*c⁻¹*a⁻¹ := by rw [hcz]
      _ = _ := by group
  rw [he]
  exact le_normalizer_iff.mp hn a ⟨ha.2,ha.1⟩ z (full_seed_le_fixed T hfull hz)

/-- Every actual H-star residual inside a third maximal local has
three-rank at most one in the full extraspecial row. -/
theorem PreparedChosenModule.extraspecial_third_HStar_residual_rank
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V N H : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) (hHN : H ≤ N) :
    primeRank 3 ((pResidual 2 H).map H.subtype) ≤ 1 := by
  obtain ⟨e⟩ := h.extraspecial_third_action_symmetricThree hG T hempty hM hJ hu hfull hex
    hN hNM hNMc
  have hr := Section02.source_local_symmetricThree_centralizer_rank hG T hempty hN hu hmany hNMc e
  have hmod := h.extraspecial_third_module_le_fixed hG T hempty hM hmany hJ hu hfull hex
    hN hNM hNMc
  have hres := h.source_thompsonFixed_local_residuals hG T hempty hM hJ H hH
  have hle : (pResidual 2 H).map H.subtype ≤
      N ⊓ centralizer (localModule T N : Set G) :=
    le_inf ((map_subtype_le _).trans hHN) (hres.trans (centralizer_le hmod))
  exact (Theory.GroupTheory.primeRank_le_of_injective 3 (Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)).trans hr

end CFSG.Quasithin.Chapter15.Section01
