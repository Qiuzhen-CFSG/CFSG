module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialKernelContainedFF
public import CFSG.Quasithin.Chapter15.Section01.CaseI.SylowControl
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Extraspecial.Construction
public import Theory.GroupTheory.SpecificGroups.KleinFourAut

/-!
# The original marked Sylow fixes the moved plane

The pointwise stabilizer of the selected noncentral cubic's fixed plane has
two-subgroups of order at most two. Its intersection with the original
Sylow action contains the order-two Thompson image, so they coincide.
Consequently C_T(Z₁) fixes U=[V,J₁(T)] pointwise. This uses the same selected
four-subgroup and does not assume the global residual conclusion.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The literal marked Sylow centralizer lies in the moved-plane centralizer,
before any global residual or component-selection conclusion. -/
theorem PreparedChosenModule.extraspecial_marked_sylow_centralizes_moved
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    letI := h.elementary
    ∀ c : ExtraspecialMarker.ImageMarking T M V h.normalized,
      (T : Subgroup G) ⊓ centralizer (ExtraspecialMarker.fixedSubgroup M V h.normalized c.X : Set G) ≤
        centralizer (⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ : Subgroup G) := by
  let := h.elementary
  intro c
  let D := internalActionImage M V h.normalized
  let ρ := imageRepresentation M V h.normalized
  let f : M →* D := (actionHom M V h.normalized).rangeRestrict
  let P := pResidual 2 D
  let W := fixedSpace ρ (c.X.map P.subtype)
  let K := subspaceKernel ρ W ⊤
  let S := ((T : Subgroup G).subgroupOf M).map f
  let R := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f
  obtain ⟨t,ht,htR,_⟩ := h.extraspecial_small_thompson_image
    hG T hempty hM hmany hJ hfull hex
  change zpowers t = R at htR
  have hRcard : Nat.card R = 2 := by rw [←htR,Nat.card_zpowers,ht]
  have hexcopy := hex
  obtain ⟨_,_,_,hP,hPc,_,h6,_⟩ := hexcopy
  let : IsExtraspecial 3 P := hP
  have hRS : R ≤ S := map_mono (subgroupOf_mono M (ChapterB.thompsonJ_le _ _))
  have hRK : R ≤ K := by
    intro r hr
    refine ⟨mem_top _,?_⟩
    intro w hw
    exact c.fixed_thompson hw ⟨r,hr⟩
  have hcard : Nat.card (S ⊓ K : Subgroup D) ≤ 2 :=
    ExtraspecialBinarySix.noncentral_cubic_stabilizer_two_subgroup_card_le_two
      ρ (imageRepresentation_injective M V h.normalized) P hPc h6 c.X
      c.card_X c.noncentral (S ⊓ K)
      ((((T.subtype hM.1.2).isPGroup').map f).to_le inf_le_left) inf_le_right
  have he : S ⊓ K = R :=
    (eq_of_le_of_card_ge (le_inf hRS hRK) (hcard.trans_eq hRcard.symm)).symm
  have hUE := h.extraspecial_thompson_moved_le_fixed hG T hempty hM hmany hJ hfull hex
  intro s hs u hu
  let sm : M := ⟨s,hM.1.2 hs.1⟩
  have hsS : f sm ∈ S := mem_map_of_mem f hs.1
  have hsK : f sm ∈ K :=
    (ExtraspecialMarker.image_mem_kernel_iff M V h.normalized W sm).mpr hs.2
  have hsR : f sm ∈ R := he ▸ ⟨hsS,hsK⟩
  obtain ⟨j,hj,hjs⟩ := hsR
  let uv : V := ⟨u,(hUE hu).1⟩
  have hjfix : (actionHom M V h.normalized) j uv = uv := by
    apply Subtype.ext
    change (j : G) * u * (j : G)⁻¹ = u
    rw [(hUE hu).2 j hj,mul_inv_cancel_right]
  have hsame := congrArg (fun a : D => a.val uv) hjs
  have hsfix : (actionHom M V h.normalized) sm uv = uv := hsame.symm.trans hjfix
  have hh := congrArg V.subtype hsfix
  change s*u*s⁻¹=u at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- The same marked local acts on the moved four-group with order one or
three: its original Sylow already fixes that four-group pointwise. -/
theorem PreparedChosenModule.extraspecial_marked_partner_moved_index
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    letI := h.elementary
    ∀ c : ExtraspecialMarker.ImageMarking T M V h.normalized,
      let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
      let Z1 := ExtraspecialMarker.fixedSubgroup M V h.normalized c.X
      let MZ := centralizer (Z1 : Set G) ⊓ Mc
      (centralizer (U : Set G)).relIndex MZ = 1 ∨
        (centralizer (U : Set G)).relIndex MZ = 3 := by
  let := h.elementary
  intro c
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  let Z1 := ExtraspecialMarker.fixedSubgroup M V h.normalized c.X
  let G1 := centralizer (Z1 : Set G)
  let MZ := G1 ⊓ Mc
  let S := (T : Subgroup G) ⊓ G1
  let W := fixedSpace (imageRepresentation M V h.normalized)
    (c.X.map (pResidual 2 (internalActionImage M V h.normalized)).subtype)
  have hZE : Z1 ≤ thompsonFixed T V :=
    (ExtraspecialMarker.fixed_and_generation T hM.1.2 h.normalized W
      c.fixed_thompson c.generates).1
  have hlocal : Chapter1.IsSylowIn 2 S (M ⊓ G1) :=
    ExtraspecialMarker.local_sylow T hM.1.2 h.normalized W c.sylow
  have hSyl : Chapter1.IsSylowIn 2 S G1 :=
    h.caseI_centralizer_sylow hG T hM hJ hZE (by
      change Chapter1.IsSylowIn 2 S (G1 ⊓ M)
      simpa only [inf_comm M G1] using hlocal)
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc :=
    (le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T)).trans hMc.2
  have hSMZ : S ≤ MZ := le_inf inf_le_right (inf_le_left.trans hTMc)
  obtain ⟨P,hP⟩ := hSyl.restrict hSMZ inf_le_left
  have hSC : S ≤ centralizer (U : Set G) :=
    h.extraspecial_marked_sylow_centralizes_moved hG T hempty hM hmany hJ hfull hex c
  have hn : MZ ≤ normalizer (U : Set G) :=
    inf_le_right.trans (h.extraspecial_partner_module_and_normalizer
      hG T hempty hM hmany hJ hu hfull hex).2.le
  let f := actionHom MZ U hn
  have hPk : (P : Subgroup MZ) ≤ f.ker := by
    intro p hp
    rw [show f = actionHom MZ U hn from rfl,actionHom_ker]
    exact hSC (hP ▸ mem_map_of_mem MZ.subtype hp)
  have htwo : ¬ 2 ∣ f.ker.index := fun hd =>
    P.not_dvd_index (hd.trans (index_dvd_of_le hPk))
  have hUc : Nat.card U = 4 :=
    (h.extraspecial_thompson_moved_seed_and_card hG T hempty hM hmany hJ hfull hex).2
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le
    ((h.extraspecial_thompson_moved_le_fixed hG T hempty hM hmany hJ hfull hex).trans inf_le_left)
  have hAut : Nat.card (MulAut U) = 6 := by
    let : Nontrivial U := (Finite.one_lt_card_iff_nontrivial).mp (by rw [hUc]; decide)
    let : IsKleinFour U := ⟨hUc,IsElementaryAbelian.exponent_eq_prime⟩
    exact IsKleinFour.card_mulAut U
  have hdiv : f.ker.index ∣ 6 := by
    rw [index_ker]
    exact hAut ▸ card_subgroup_dvd_card f.range
  have hthree : f.ker.index ∣ 3 :=
    (Nat.Coprime.dvd_mul_right (Nat.coprime_comm.mpr
      (Nat.prime_two.coprime_iff_not_dvd.mpr htwo))).mp hdiv
  have he : f.ker.index = (centralizer (U : Set G)).relIndex MZ := by
    rw [show f = actionHom MZ U hn from rfl,actionHom_ker]
    rfl
  have hh := (Nat.dvd_prime Nat.prime_three).mp hthree
  rw [he] at hh
  exact hh

end CFSG.Quasithin.Chapter15.Section01
