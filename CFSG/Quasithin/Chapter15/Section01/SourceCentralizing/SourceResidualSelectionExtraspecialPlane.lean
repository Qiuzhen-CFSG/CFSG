module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialModelSeed
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialGeometry
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Actions.Cyclic.Transport

/-!
# The original Thompson moved plane in the full extraspecial row

The square-root calculation places the actual central seed in [V,J₁(T)],
which has order four. Every third maximal intersection preserves that
literal subgroup. Original source ordering then identifies V(T,N) with
this plane and N with its normalizer. The no-third alternative remains
explicit; no existence or residual normalization is inferred from the
local extraspecial action alone.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open Section02.ChosenGeometry.Cyclic
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem ambientSpace_card {V : Subgroup G} [IsElementaryAbelian 2 V]
    (W : Submodule (ZMod 2) (Additive V)) : Nat.card (ambientSpace V W) = Nat.card W := by
  rw [ambientSpace,card_map_of_injective V.subtype_injective]
  apply Nat.card_congr
  exact {
    toFun := fun v => ⟨Additive.ofMul v.val,v.property⟩
    invFun := fun v => ⟨v.val.toMul,v.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- The literal original moved subgroup contains the central seed and has order four. -/
theorem PreparedChosenModule.extraspecial_thompson_moved_seed_and_card
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    centralInvolutions T ≤ ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ ∧
      Nat.card (⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ : Subgroup G) = 4 := by
  let := h.elementary
  have hm := h.extraspecial_seed_le_thompson_moved hG T hempty hM hmany hJ hfull hex
  have he := ambientSpace_moved h.normalized h.le_selected
    ((ChapterB.thompsonJ_le (T : Subgroup G) 1).trans hM.1.2)
  change ambientSpace V (subspaceCommutator (imageRepresentation M V h.normalized) ⊤
    (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V h.normalized).rangeRestrict)) = _ at he
  rw [←he]
  constructor
  · intro z hz
    have hzV : z ∈ V := hfull.symm ▸ le_conjugateSpanBy (centralInvolutions T) M hz
    exact (mem_ambientSpace _ ⟨z,hzV⟩).mpr (hm.1 hz)
  · rw [ambientSpace_card,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact (congrArg (fun n : ℕ => 2 ^ n) hm.2).trans (by norm_num)

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

/-- An actual third maximal intersection preserves the literal Thompson moved plane. -/
theorem PreparedChosenModule.extraspecial_third_normalizes_moved
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
    M ⊓ N ≤ normalizer (⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ : Subgroup G) := by
  let := h.elementary
  let D := internalActionImage M V h.normalized
  let ρ := imageRepresentation M V h.normalized
  let f : M →* D := (actionHom M V h.normalized).rangeRestrict
  let S := (T.subtype hM.1.2).mapSurjective (f := f)
    (actionHom M V h.normalized).rangeRestrict_surjective
  obtain ⟨t,ht,htR,hcod⟩ := h.extraspecial_small_thompson_image hG T hempty hM hmany hJ hfull hex
  obtain ⟨_,_,_,hP,hPc,_,h6,hI⟩ := hex
  let : IsExtraspecial 3 (pResidual 2 D) := hP
  have hSR := chosen_thompson_image_normalized T M V hM.1.2 h.normalized
  have hSt : (S : Subgroup D) ≤ normalizer (zpowers t : Set D) := htR ▸ hSR
  have hn := SourceExtraspecialModel.proper_overgroup_normalizes_small_involution S hI ρ
    (imageRepresentation_injective M V h.normalized) hPc h6 t
    (ht ▸ pow_orderOf_eq_one t) (by rw [htR]; exact hcod.le)
    hSt
    (((M ⊓ N).subgroupOf M).map f)
    (map_mono (subgroupOf_mono M (le_inf hM.1.2 hN.2)))
    (h.third_maximal_action_constraints hG T hempty hM hJ hu hN hNM hNMc).2.2
  rw [htR] at hn
  exact moved_normalizer_of_image T hM.1.2 h inf_le_left hn

/-- A third local has the original moved plane as its own module and is its normalizer. -/
theorem PreparedChosenModule.extraspecial_third_module_and_normalizer
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
    localModule T N = ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ ∧
      N = normalizer (⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ : Subgroup G) := by
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  obtain ⟨hseed,hcard⟩ := h.extraspecial_thompson_moved_seed_and_card hG T hempty hM hmany hJ hfull hex
  have hn := h.extraspecial_third_normalizes_moved hG T hempty hM hmany hJ hu hfull hex hN hNM hNMc
  have hord := source_ordering_of_centralizing_orderingMaximal hG T hempty hM hJ N hN
  have hle : localModule T N ≤ U := by
    change conjugateSpanBy (centralInvolutions T) N ≤ U
    apply (closure_le _).mpr
    rintro x ⟨n,hnN,z,hz,rfl⟩
    obtain ⟨a,ha,c,hc,rfl⟩ := hord n hnN
    have hcz := mem_centralizer_iff.mp hc.2 z (le_conjugateSpanBy (centralInvolutions T) N hz)
    have he : (a*c)*z*(a*c)⁻¹ = a*z*a⁻¹ := by
      calc
        _ = a*(c*z)*c⁻¹*a⁻¹ := by group
        _ = a*(z*c)*c⁻¹*a⁻¹ := by rw [hcz]
        _ = _ := by group
    rw [he]
    exact le_normalizer_iff.mp hn a ⟨ha.2,ha.1⟩ z (hseed hz)
  have hd : Nat.card (localModule T N) ∣ 4 := hcard ▸ card_dvd_of_le hle
  have hnontriv : localModule T N ≠ ⊥ := by
    intro hb
    exact centralInvolutions_ne_bot_of_maximal_local T hN
      (bot_unique ((le_conjugateSpanBy (centralInvolutions T) N).trans hb.le))
  have hlo := (one_lt_card_iff_ne_bot (localModule T N)).mpr hnontriv
  have hhi := Nat.le_of_dvd (by decide : 0 < 4) hd
  have hcases : Nat.card (localModule T N) = 2 ∨ Nat.card (localModule T N) = 4 := by
    have h3 : Nat.card (localModule T N) ≠ 3 := by intro he; rw [he] at hd; norm_num at hd
    omega
  have he : localModule T N = U := by
    rcases hcases with hc | hc
    · have hle' : N ≤ Mc :=
        (le_normalizer_conjugateSpanBy (centralInvolutions T) N).trans
          ((normalizer_le_centralizer_of_card_two (localModule T N) hc).trans
            (localModule_centralizer_le_partner T N hu))
      have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
        hu ▸ Set.mem_singleton Mc
      exact (hNMc (le_antisymm hle' (hN.1.2 hMc.1.1 hle'))).elim
    · exact eq_of_le_of_card_ge hle (by rw [hc,hcard])
  exact ⟨he,by simpa only [he] using (maximal_local_normalizer_from_source hG T hN).2⟩

/-- The full extraspecial source has either the original pair or exactly one
third maximal local, whose own module is the literal Thompson moved plane. -/
theorem PreparedChosenModule.extraspecial_full_maximal_overgroups_alternatives
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    (maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc} ∧
      normalizer (thompsonFixed T V : Set G) ≤ Mc) ∨
    ∃ N ∈ maximalTwoLocalOvergroups (T : Subgroup G), N ≠ M ∧ N ≠ Mc ∧
      localModule T N = ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ ∧
      N = normalizer (⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ : Subgroup G) ∧
      maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc,N} := by
  classical
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  by_cases ht : ∃ N ∈ maximalTwoLocalOvergroups (T : Subgroup G), N ≠ M ∧ N ≠ Mc
  · obtain ⟨N,hN,hNM,hNMc⟩ := ht
    obtain ⟨he,hn⟩ := h.extraspecial_third_module_and_normalizer hG T hempty hM hmany hJ hu
      hfull hex hN hNM hNMc
    right
    refine ⟨N,hN,hNM,hNMc,he,hn,?_⟩
    ext L
    constructor
    · intro hL
      by_cases hLM : L = M
      · simp [hLM]
      by_cases hLMc : L = Mc
      · simp [hLMc]
      have hLN : L = N :=
        (h.extraspecial_third_module_and_normalizer hG T hempty hM hmany hJ hu
          hfull hex hL hLM hLMc).2.trans hn.symm
      simp [hLN]
    · intro hL
      rcases Set.mem_insert_iff.mp hL with rfl | hL
      · exact hM.1
      rcases Set.mem_insert_iff.mp hL with rfl | hL
      · exact ⟨hMc.1,hTMc⟩
      obtain rfl := Set.mem_singleton_iff.mp hL
      exact hN
  · have htwo : maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc} := by
      ext L
      constructor
      · intro hL
        by_cases hLM : L = M
        · simp [hLM]
        have hLMc : L = Mc := by
          by_contra hn
          exact ht ⟨L,hL,hLM,hn⟩
        simp [hLMc]
      · intro hL
        rcases Set.mem_insert_iff.mp hL with rfl | hL
        · exact hM.1
        obtain rfl := Set.mem_singleton_iff.mp hL
        exact ⟨hMc.1,hTMc⟩
    exact Or.inl ⟨htwo,h.thompsonFixed_normalizer_le_of_maximal_overgroups_pair
      hG T hempty hM hmany hJ htwo⟩

end CFSG.Quasithin.Chapter15.Section01
