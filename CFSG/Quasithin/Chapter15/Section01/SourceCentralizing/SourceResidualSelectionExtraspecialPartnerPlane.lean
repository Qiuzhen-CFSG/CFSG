module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialPlane
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialNoThird
public import Theory.Representation.BinaryOffender.InvolutionRatio

/-!
# The actual centralizer partner normalizes the Thompson moved plane

In the full extraspecial source, the two maximal locals over T are M and
its centralizer partner. The moved plane U lies in the Thompson fixed
subgroup, so its normalizer escapes M and lies in the partner. Ordering
puts the partner's own module inside U. The original central cubic acts
without fixed points on U, forcing that module to be all of U.

Thus the literal partner is N_G(U). This does not assert that its kernel
on U normalizes the four-dimensional Thompson fixed subgroup.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open Section02.ChosenGeometry.Cyclic
variable {G : Type*} [Group G] [Finite G]

set_option backward.isDefEq.respectTransparency false in
private theorem moved_normalizer_of_image
    (T : Sylow 2 G) {M V X : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (h : PreparedChosenModule T M V) (hXM : X ≤ M)
    (hn : (X.subgroupOf M).map (actionHom M V h.normalized).rangeRestrict ≤
      normalizer (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V h.normalized).rangeRestrict : Set _)) :
    X ≤ normalizer (⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ : Subgroup G) := by
  let := h.elementary
  let ρ := imageRepresentation M V h.normalized
  let R := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
    (actionHom M V h.normalized).rangeRestrict
  let W := subspaceCommutator ρ ⊤ R
  have hs := subspaceCommutator_invariant_normalizer ρ
    (show (X.subgroupOf M).map (actionHom M V h.normalized).rangeRestrict ≤
      subspaceStabilizer ρ ⊤ from le_subspaceStabilizer ρ ⊤ (by intros; trivial)) hn
  have he := ambientSpace_moved h.normalized h.le_selected
    ((ChapterB.thompsonJ_le (T : Subgroup G) 1).trans hTM)
  change ambientSpace V W = _ at he
  rw [←he]
  apply le_normalizer_iff.mpr
  intro x hx v hv
  obtain ⟨v,hv,rfl⟩ := hv
  let a : M := ⟨x,hXM hx⟩
  have ha : (actionHom M V h.normalized).rangeRestrict a ∈
      (X.subgroupOf M).map (actionHom M V h.normalized).rangeRestrict :=
    mem_map_of_mem _ hx
  have hh := (hs ha (Additive.ofMul v)).2 hv
  exact ⟨(ρ ((actionHom M V h.normalized).rangeRestrict a) (Additive.ofMul v)).toMul,
    hh,rfl⟩

/-- The actual small involution makes the moved plane a subgroup of the
original Thompson fixed subgroup. -/
theorem PreparedChosenModule.extraspecial_thompson_moved_le_fixed
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ ≤ thompsonFixed T V := by
  let := h.elementary
  let ρ := imageRepresentation M V h.normalized
  let R := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
    (actionHom M V h.normalized).rangeRestrict
  obtain ⟨t,ht,htR,_⟩ := h.extraspecial_small_thompson_image hG T hempty hM hmany hJ hfull hex
  change zpowers t = R at htR
  have hq : IsQuadratic ρ R := by
    rw [←htR]
    exact (involution_actor_rank_and_fixedCodim ρ t ht).2.2.1
  have hle : subspaceCommutator ρ ⊤ R ≤ fixedSpace ρ R := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,v,_,rfl⟩ b
    exact hq b b.property a ha v
  have hh : ambientSpace V (subspaceCommutator ρ ⊤ R) ≤ ambientSpace V (fixedSpace ρ R) := by
    rintro x ⟨v,hv,rfl⟩
    exact ⟨v,hle hv,rfl⟩
  have hJM := (ChapterB.thompsonJ_le (T : Subgroup G) 1).trans hM.1.2
  have hm := ambientSpace_moved h.normalized h.le_selected hJM
  have hf := ambientSpace_fixed h.normalized hJM
  change ambientSpace V (subspaceCommutator ρ ⊤ R) = _ at hm
  change ambientSpace V (fixedSpace ρ R) = thompsonFixed T V at hf
  rwa [hm,hf] at hh

set_option backward.isDefEq.respectTransparency false in
/-- The original centralizer partner has the Thompson moved plane as its
own local module and is exactly the normalizer of that same plane. -/
theorem PreparedChosenModule.extraspecial_partner_module_and_normalizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    localModule T Mc = ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ ∧
      Mc = normalizer (⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ : Subgroup G) := by
  let := h.elementary
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  let D := internalActionImage M V h.normalized
  let ρ := imageRepresentation M V h.normalized
  let f : M →* D := (actionHom M V h.normalized).rangeRestrict
  have hf : Function.Surjective f := (actionHom M V h.normalized).rangeRestrict_surjective
  let S := (T.subtype hM.1.2).mapSurjective (f := f) hf
  let R := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f
  let A := ((M ⊓ Mc).subgroupOf M).map f
  let P := pResidual 2 D
  let ZP := (center P).map P.subtype
  have htwo := h.maximal_overgroups_of_full_extraspecial hG T hempty hM hmany hJ hu hfull hex
  have hMc : Mc ∈ maximalTwoLocalOvergroups (T : Subgroup G) := by
    rw [htwo]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hne : M ≠ Mc := by
    intro he
    rw [htwo,he] at hmany
    simp at hmany
  have hproper : A ≠ ⊤ := by
    intro htop
    have hMMc : M ≤ Mc := by
      intro m hm
      have hmA : f ⟨m,hm⟩ ∈ A := htop ▸ mem_top _
      obtain ⟨a,ha,he⟩ := hmA
      have hk : a⁻¹ * (⟨m,hm⟩ : M) ∈ f.ker := by
        change f (a⁻¹ * ⟨m,hm⟩) = 1
        rw [map_mul,map_inv,he,inv_mul_cancel]
      have hk' : a⁻¹ * (⟨m,hm⟩ : M) ∈ (actionHom M V h.normalized).ker :=
        congrArg Subtype.val hk
      rw [actionHom_ker] at hk'
      have hh := Mc.mul_mem ha.2 (h.centralizer_le_partner T hu hk')
      change (a : G) * ((a : G)⁻¹ * m) ∈ Mc at hh
      simpa only [mul_inv_cancel_left] using hh
    exact hne (hM.1.1.eq_of_le hMc.1.1 hMMc)
  obtain ⟨t,ht,htR,hcod⟩ := h.extraspecial_small_thompson_image hG T hempty hM hmany hJ hfull hex
  change zpowers t = R at htR
  change fixedCodim ρ R = 2 at hcod
  obtain ⟨hseed,hcard⟩ := h.extraspecial_thompson_moved_seed_and_card
    hG T hempty hM hmany hJ hfull hex
  change Nat.card U = 4 at hcard
  have hUE := h.extraspecial_thompson_moved_le_fixed hG T hempty hM hmany hJ hfull hex
  obtain ⟨_,_,_,hP,hPc,_,h6,hI⟩ := hex
  let : IsExtraspecial 3 P := hP
  have hSR := chosen_thompson_image_normalized T M V hM.1.2 h.normalized
  change (S : Subgroup D) ≤ normalizer (R : Set D) at hSR
  have hnA := SourceExtraspecialModel.proper_overgroup_normalizes_small_involution S hI ρ
    (imageRepresentation_injective M V h.normalized) hPc h6 t
    (ht ▸ pow_orderOf_eq_one t) (by rw [htR]; exact hcod.le)
    (htR ▸ hSR) A (map_mono (subgroupOf_mono M (le_inf hM.1.2 hMc.2))) hproper
  rw [htR] at hnA
  have hnU : M ⊓ Mc ≤ normalizer (U : Set G) :=
    moved_normalizer_of_image T hM.1.2 h inf_le_left hnA
  have hUV : U ≤ V := hUE.trans inf_le_left
  have hUOmega := hUE.trans (h.thompsonFixed_le_omega T hM)
  have hUN : normalizer (U : Set G) ≤ Mc := by
    have hUne : U ≠ ⊥ := by intro hb; rw [hb,card_bot] at hcard; omega
    have hlocal : IsTwoLocal (normalizer (U : Set G)) :=
      ⟨U,hUne,(IsElementaryAbelian.isPGroup 2 V).to_le hUV,rfl⟩
    obtain ⟨N,hUN,hN⟩ := Finite.exists_le_maximal hlocal
    have hNmem : N ∈ maximalTwoLocalOvergroups (T : Subgroup G) :=
      ⟨hN,(le_inf hM.1.2 hMc.2).trans (hnU.trans hUN)⟩
    rw [htwo,Set.mem_insert_iff,Set.mem_singleton_iff] at hNmem
    rcases hNmem with rfl | rfl
    · exact ((h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).1
        ((centralizer_le hUOmega).trans ((Subgroup.centralizer_le_normalizer _).trans hUN))).elim
    · exact hUN
  let X := (ZP.comap f).map M.subtype
  have hXi : (X.subgroupOf M).map f = ZP := by
    apply le_antisymm
    · rintro z ⟨m,hm,rfl⟩
      obtain ⟨a,ha,he⟩ := hm
      exact (show a = m from Subtype.ext he) ▸ ha
    · intro z hz
      obtain ⟨m,hm⟩ := hf z
      exact ⟨m,⟨m,show f m ∈ ZP from hm.symm ▸ hz,rfl⟩,hm⟩
  have htZ : t ∈ centralizer (ZP : Set D) :=
    ExtraspecialBinarySix.small_involution_centralizes_center ρ
      (imageRepresentation_injective M V h.normalized) P hPc h6 t
      (ht ▸ pow_orderOf_eq_one t) (by rw [htR]; exact hcod.le)
  have hZR : ZP ≤ normalizer (R : Set D) := by
    rw [←htR]
    exact (le_centralizer_iff.mp (zpowers_le.mpr htZ)).trans (Subgroup.centralizer_le_normalizer _)
  have hnX : (X.subgroupOf M).map f ≤ normalizer (R : Set D) := hXi.le.trans hZR
  have hXMc : X ≤ Mc :=
    (moved_normalizer_of_image T hM.1.2 h (map_subtype_le _) hnX).trans hUN
  have hord := source_ordering_of_centralizing_orderingMaximal hG T hempty hM hJ Mc hMc
  have hLU : localModule T Mc ≤ U := by
    change conjugateSpanBy (centralInvolutions T) Mc ≤ U
    apply (closure_le _).mpr
    rintro x ⟨m,hm,z,hz,rfl⟩
    obtain ⟨a,ha,c,hc,rfl⟩ := hord m hm
    have hcz := mem_centralizer_iff.mp hc.2 z (le_conjugateSpanBy (centralInvolutions T) Mc hz)
    have he : (a*c)*z*(a*c)⁻¹ = a*z*a⁻¹ := by
      calc
        _ = a*(c*z)*c⁻¹*a⁻¹ := by group
        _ = a*(z*c)*c⁻¹*a⁻¹ := by rw [hcz]
        _ = _ := by group
    rw [he]
    exact le_normalizer_iff.mp hnU a ⟨ha.2,ha.1⟩ z (hseed hz)
  have hLne : localModule T Mc ≠ ⊥ := by
    intro hb
    exact centralInvolutions_ne_bot_of_maximal_local T hMc
      (bot_unique ((le_conjugateSpanBy (centralInvolutions T) Mc).trans hb.le))
  have hnot2 : Nat.card (localModule T Mc) ≠ 2 := by
    intro hc
    have hXL : X ≤ centralizer (localModule T Mc : Set G) :=
      (hXMc.trans (le_normalizer_conjugateSpanBy _ _)).trans
        (normalizer_le_centralizer_of_card_two _ hc)
    have hzero := SourceExtraspecialModel.extraspecial_center_fixedSpace_eq_bot ρ
      (imageRepresentation_injective M V h.normalized) P hPc h6
    apply hLne
    apply bot_unique
    intro l hl
    let v : V := ⟨l,hUV (hLU hl)⟩
    have hv : Additive.ofMul v ∈ fixedSpace ρ ZP := by
      rintro ⟨z,hz⟩
      obtain ⟨m,hm,he⟩ := hXi.symm ▸ hz
      change ρ z (Additive.ofMul v) = Additive.ofMul v
      rw [←he]
      apply congrArg Additive.ofMul
      apply Subtype.ext
      change (m : G) * l * (m : G)⁻¹ = l
      have hc : l * (m : G) = (m : G) * l := hXL hm l hl
      rw [←hc,mul_inv_cancel_right]
    rw [hzero,Submodule.mem_bot] at hv
    exact congrArg (fun w : Additive V => (w.toMul : G)) hv
  have hLcard : Nat.card (localModule T Mc) = 4 := by
    have hd : Nat.card (localModule T Mc) ∣ 4 := hcard ▸ card_dvd_of_le hLU
    have hlo := (one_lt_card_iff_ne_bot _).mpr hLne
    have hhi := Nat.le_of_dvd (by decide : 0 < 4) hd
    have hn3 : Nat.card (localModule T Mc) ≠ 3 := by intro he; rw [he] at hd; norm_num at hd
    omega
  have he : localModule T Mc = U := eq_of_le_of_card_ge hLU (by rw [hLcard,hcard])
  exact ⟨he,by simpa only [he] using (maximal_local_normalizer_from_source hG T hMc).2⟩

end CFSG.Quasithin.Chapter15.Section01
