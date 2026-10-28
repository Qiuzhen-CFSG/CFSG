module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionFifteenIntersection
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionFifteenModel
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Actions.Cyclic.Transport
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# The third local module in the original marked-five row

The source ordering factors N through M∩N and the centralizer of V(N).
When M∩N preserves the Thompson fixed subgroup, every conjugate of the
original central seed by N therefore lies in that subgroup. A fixed subgroup
of order four then equals V(N): a one-dimensional V(N) would force all of N
into the distinguished centralizer partner. This uses the original full
module and does not treat the fixed plane as a four-dimensional proper support.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

private theorem full_seed_le_thompsonFixed
    (T : Sylow 2 G) {M V : Subgroup G} (hfull : V = localModule T M) :
    centralInvolutions T ≤ thompsonFixed T V := by
  refine le_inf ?_ ?_
  · rw [hfull]
    exact le_conjugateSpanBy _ _
  · intro z hz j hj
    exact ((mem_omegaOneCenterAmbient_iff _ z).mp hz).2.2 j
      (ChapterB.thompsonJ_le _ _ hj)

private theorem localModule_le_fixed_of_intersection
    {T : Sylow 2 G} {M Mc V N : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hfull : V = localModule T M)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hn : M ⊓ N ≤ normalizer (thompsonFixed T V : Set G)) :
    localModule T N ≤ thompsonFixed T V := by
  have hord := source_ordering_of_centralizing_orderingMaximal
    h.ambient T h.empty h.maximal h.centralizing N hN
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
  exact le_normalizer_iff.mp hn a ⟨ha.2,ha.1⟩ z
    (full_seed_le_thompsonFixed T hfull hz)

/-- In the full marked-five row, the third local's own module lies in the
literal Thompson fixed subgroup. -/
theorem ChosenSmallSource.marked_five_third_module_le_fixed
    {T : Sylow 2 G} {M Mc V N : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2)
    (hfull : V = localModule T M)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    localModule T N ≤ thompsonFixed T V := by
  exact localModule_le_fixed_of_intersection h hfull hN
    (h.marked_five_third_intersection hd hN hNM hNMc).2.2.2

private theorem localModule_eq_fixed_of_card_four
    {T : Sylow 2 G} {M Mc V N : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNMc : N ≠ Mc)
    (hle : localModule T N ≤ thompsonFixed T V)
    (hcard : Nat.card (thompsonFixed T V) = 4) :
    localModule T N = thompsonFixed T V := by
  have hd : Nat.card (localModule T N) ∣ 4 := hcard ▸ card_dvd_of_le hle
  have hne : localModule T N ≠ ⊥ := by
    intro hb
    exact centralInvolutions_ne_bot_of_maximal_local T hN
      (bot_unique ((le_conjugateSpanBy (centralInvolutions T) N).trans hb.le))
  have hlo := (one_lt_card_iff_ne_bot (localModule T N)).mpr hne
  have hhi := Nat.le_of_dvd (by decide : 0 < 4) hd
  have hcases : Nat.card (localModule T N) = 2 ∨ Nat.card (localModule T N) = 4 := by
    have h3 : Nat.card (localModule T N) ≠ 3 := by
      intro he
      rw [he] at hd
      norm_num at hd
    omega
  rcases hcases with hc | hc
  · have hle' : N ≤ Mc :=
      (le_normalizer_conjugateSpanBy (centralInvolutions T) N).trans
        ((normalizer_le_centralizer_of_card_two (localModule T N) hc).trans
          (localModule_centralizer_le_partner T N h.partner))
    have hMc : Mc ∈ maximalTwoLocalOvergroups
        (centralizer (centralInvolutions T : Set G)) := h.partner ▸ Set.mem_singleton Mc
    exact (hNMc (le_antisymm hle' (hN.1.2 hMc.1.1 hle'))).elim
  · exact eq_of_le_of_card_ge hle (by omega)

omit [Finite G] in
private theorem ambientSpace_card {V : Subgroup G} [IsElementaryAbelian 2 V]
    (W : Submodule (ZMod 2) (Additive V)) :
    Nat.card (ChosenGeometry.Cyclic.ambientSpace V W) = Nat.card W := by
  rw [ChosenGeometry.Cyclic.ambientSpace,card_map_of_injective V.subtype_injective]
  apply Nat.card_congr
  exact {
    toFun := fun v => ⟨Additive.ofMul v.val,v.property⟩
    invFun := fun v => ⟨v.val.toMul,v.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- The actual Thompson fixed subgroup in a marked-five chosen module has
order four. -/
theorem ChosenSmallSource.marked_five_fixed_card
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2) : Nat.card (thompsonFixed T V) = 4 := by
  let := h.prepared.elementary
  let ρ := imageRepresentation M V h.prepared.normalized
  let R := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
    (actionHom M V h.prepared.normalized).rangeRestrict
  have hdimen := SourceFifteenModel.two_subgroup_fixed_dimension ρ h.finrank_eq_four
    h.prepared.quadratic_ratio R (h.marked_five_thompson_image hd).1
  have he := ChosenGeometry.Cyclic.ambientSpace_fixed h.prepared.normalized
    ((ChapterB.thompsonJ_le (T : Subgroup G) 1).trans h.maximal.1.2)
  change ChosenGeometry.Cyclic.ambientSpace V (fixedSpace ρ R) = thompsonFixed T V at he
  rw [←he,ambientSpace_card,Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_zmod,hdimen]
  norm_num

/-- A third maximal local in the full marked-five row is exactly the
normalizer of the original Thompson fixed plane, and that plane is its own
source local module. -/
theorem ChosenSmallSource.marked_five_third_module_and_normalizer
    {T : Sylow 2 G} {M Mc V N : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2)
    (hfull : V = localModule T M)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    localModule T N = thompsonFixed T V ∧ N = normalizer (thompsonFixed T V : Set G) := by
  have he := localModule_eq_fixed_of_card_four h hN hNMc
    (h.marked_five_third_module_le_fixed hd hfull hN hNM hNMc)
    (h.marked_five_fixed_card hd)
  refine ⟨he,?_⟩
  simpa only [he] using (maximal_local_normalizer_from_source h.ambient T hN).2

/-- The original full marked-five source has exactly one third maximal
local, namely the normalizer of its Thompson fixed plane. -/
theorem ChosenSmallSource.marked_five_full_maximal_overgroups
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2)
    (hfull : V = localModule T M) :
    ∃ N ∈ maximalTwoLocalOvergroups (T : Subgroup G), N ≠ M ∧ N ≠ Mc ∧
      localModule T N = thompsonFixed T V ∧ N = normalizer (thompsonFixed T V : Set G) ∧
      maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc,N} := by
  classical
  obtain ⟨N,hN,hNM,hNMc⟩ := h.exists_third_of_marked_five hd
  obtain ⟨he,hn⟩ := h.marked_five_third_module_and_normalizer hd hfull hN hNM hNMc
  refine ⟨N,hN,hNM,hNMc,he,hn,?_⟩
  have hMc := h.partner ▸ (Set.mem_singleton Mc)
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  ext L
  constructor
  · intro hL
    by_cases hLM : L = M
    · simp [hLM]
    by_cases hLMc : L = Mc
    · simp [hLMc]
    have hLN : L = N :=
      (h.marked_five_third_module_and_normalizer hd hfull hL hLM hLMc).2.trans hn.symm
    simp [hLN]
  · intro hL
    rcases Set.mem_insert_iff.mp hL with rfl | hL
    · exact h.maximal.1
    rcases Set.mem_insert_iff.mp hL with rfl | hL
    · exact ⟨hMc.1,hTMc⟩
    obtain rfl := Set.mem_singleton_iff.mp hL
    exact hN

end CFSG.Quasithin.Chapter15.Section02
