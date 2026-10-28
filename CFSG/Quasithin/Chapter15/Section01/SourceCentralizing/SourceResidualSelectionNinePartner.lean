module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNine

/-!
# The original centralizer partner in the full Nine row

The actual maximal Sylow image forces M intersect M_c to have that exact
image. The action kernel and T centralize the original central seed, so
ordering gives M_c = C_G(Z). This argument uses only the full prepared
module and the genuine Nine action, with no global Thompson residual input.
It does not assert that this partner normalizes the Thompson fixed subgroup.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

private theorem partner_eq_of_intersection_centralizes {T : Sylow 2 G} {M Mc : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hi : M ⊓ Mc ≤ centralizer (centralInvolutions T : Set G)) :
    Mc = centralizer (centralInvolutions T : Set G) := by
  have hC := CFSG.Quasithin.Chapter15.Section03.InitialSource.centralizer_le_partner T hu
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc :=
    (le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow T)).trans hC
  have ho := source_ordering_of_centralizing_orderingMaximal hG T hempty
    hM hJ Mc ⟨hMc.1, hTMc⟩
  apply le_antisymm ?_ hC
  intro x hx
  obtain ⟨a, ha, c, hc, rfl⟩ := ho x hx
  exact mul_mem (hi ⟨ha.2, ha.1⟩) (centralizer_le (le_conjugateSpanBy _ _) hc.2)

/-- The original full prepared action with a maximal Sylow image identifies
the actual partner and its intersection with the selected maximal local. -/
theorem PreparedChosenModule.nine_partner_centralizer_of_sylow_image_coatom {T : Sylow 2 G} {M Mc V : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hp : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hmax : IsCoatom (((T : Subgroup G).subgroupOf M).map
      (actionHom M V hp.normalized).rangeRestrict)) :
    Mc = centralizer (centralInvolutions T : Set G) ∧
      M ⊓ Mc = M ⊓ centralizer (centralInvolutions T : Set G) ∧
      M ⊓ centralizer (centralInvolutions T : Set G) =
        (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G) := by
  let f := (actionHom M V hp.normalized).rangeRestrict
  let S := ((T : Subgroup G).subgroupOf M).map f
  let I := (M ⊓ Mc).subgroupOf M
  have hC := CFSG.Quasithin.Chapter15.Section03.InitialSource.centralizer_le_partner T hu
  have hTMc : (T : Subgroup G) ≤ Mc :=
    (le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow T)).trans hC
  have hSI : S ≤ I.map f := map_mono (comap_mono (le_inf hM.1.2 hTMc))
  have hIs : I.map f = S := by
    rcases hmax.le_iff.mp hSI with htop | heq
    · have hMMc : M ≤ Mc := by
        intro x hx
        have him : f ⟨x, hx⟩ ∈ I.map f := htop ▸ mem_top _
        obtain ⟨y, hy, he⟩ := him
        have hk : y⁻¹ * (⟨x, hx⟩ : M) ∈ f.ker := by
          change f (y⁻¹ * ⟨x, hx⟩) = 1
          rw [map_mul, map_inv, he, inv_mul_cancel]
        rw [show f = (actionHom M V hp.normalized).rangeRestrict from rfl,
          MonoidHom.ker_rangeRestrict, actionHom_ker] at hk
        have hh := Mc.mul_mem hy.2 (hp.centralizer_le_partner T hu hk)
        change (y : G) * ((y : G)⁻¹ * x) ∈ Mc at hh
        simpa only [mul_inv_cancel_left] using hh
      have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
        hu ▸ Set.mem_singleton Mc
      exact (hne (le_antisymm hMMc (hM.1.1.2 hMc.1.1 hMMc))).elim
    · exact heq
  have hIle : M ⊓ Mc ≤ (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G) := by
    intro x hx
    have him : f ⟨x, hx.1⟩ ∈ S := hIs ▸ mem_map_of_mem f hx
    obtain ⟨t, ht, he⟩ := him
    have hk : t⁻¹ * (⟨x, hx.1⟩ : M) ∈ f.ker := by
      change f (t⁻¹ * ⟨x, hx.1⟩) = 1
      rw [map_mul, map_inv, he, inv_mul_cancel]
    rw [show f = (actionHom M V hp.normalized).rangeRestrict from rfl,
      MonoidHom.ker_rangeRestrict, actionHom_ker] at hk
    have hh : (t : G) * ((t : G)⁻¹ * x) ∈
        (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G) :=
      mul_mem (mem_sup_right ht)
      (mem_sup_left (show (t : G)⁻¹ * x ∈ M ⊓ centralizer (V : Set G) from
        ⟨M.mul_mem (M.inv_mem t.property) hx.1, hk⟩))
    simpa only [mul_inv_cancel_left] using hh
  have he : Mc = centralizer (centralInvolutions T : Set G) :=
    partner_eq_of_intersection_centralizes hG hempty hM hJ hu (hIle.trans (by
      apply sup_le
      · exact inf_le_right.trans (centralizer_le (by rw [hfull]; exact le_conjugateSpanBy _ _))
      · exact le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow T)))
  refine ⟨he, by rw [he],?_⟩
  have hTI : (T : Subgroup G) ≤ M ⊓ centralizer (centralInvolutions T : Set G) :=
    le_inf hM.1.2 (le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow T))
  let C := M ⊓ centralizer (centralInvolutions T : Set G)
  have hgen := congrArg (Subgroup.map C.subtype)
    (pResidual_sup_sylow_eq_top (T.subtype hTI))
  rw [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTI,
    ←MonoidHom.range_eq_map,range_subtype] at hgen
  apply le_antisymm
  · change C ≤ _
    rw [←hgen]
    exact sup_le_sup_right (le_inf ((map_subtype_le _).trans inf_le_left) hp.seed_residual) _
  · exact sup_le (inf_le_inf_left M (centralizer_le (by rw [hfull]; exact le_conjugateSpanBy _ _))) hTI

/-- The full Nine row identifies the literal centralizer partner. -/
theorem PreparedChosenModule.nine_partner_centralizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hp : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (h9 : letI := hp.elementary
      SourceCases.Nine (imageRepresentation M V hp.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V hp.normalized).rangeRestrict)) :
    Mc = centralizer (centralInvolutions T : Set G) ∧
      M ⊓ Mc = M ⊓ centralizer (centralInvolutions T : Set G) ∧
      M ⊓ centralizer (centralInvolutions T : Set G) =
        (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G) := by
  let := hp.elementary
  let P := (T.subtype hM.1.2).mapSurjective
    (actionHom M V hp.normalized).rangeRestrict_surjective
  exact hp.nine_partner_centralizer_of_sylow_image_coatom hG hempty hM hJ hu hne hfull
    (h9.sylow_isCoatom P)

end CFSG.Quasithin.Chapter15.Section01
