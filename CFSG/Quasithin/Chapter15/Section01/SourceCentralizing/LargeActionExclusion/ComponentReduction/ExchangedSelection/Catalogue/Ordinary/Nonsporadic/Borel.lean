module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Alternatives
public import CFSG.Quasithin.Chapter15.Section01.CaseI.OrdinarySource.InnerPlacement
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SolvableControl
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels
public import Theory.GroupTheory.ComponentBorelOrbit
public import Theory.GroupTheory.SylowLocalCore
public import Theory.SpecificGroups.SU3.BinarySylowOrder
public import Theory.SpecificGroups.Suzuki.SubgroupParameters
public import BenderSuzuki.External.Huppert.II.theorem_6_14
/-!
# The initial ordinary rank-one Borel family

Each actual Bender model, or the actual Sz(8) two-core quotient, makes the
original M_L a subgroup of its unique Sylow Borel. Hence O₂(M_L)=S_L,
and the component stabilizer in M_Z preserves that Borel. The marked inner
involution and characteristic two of M_L give a self-centralizing Borel
core. Its M_Z-orbit has characteristic two and odd quotient, so original
15.1.19(2) places that orbit in M_Z and proves the reverse inclusion.

The earlier classifier's A₆ and A₇ exceptions to inner placement are
excluded by their orders. Thus the complete initial rank-one constructor
requires no action or Borel callback, including for central two-covers.
All subgroups retain the original component and singleton centralizer
marking. The literal earlier 15.1.14 residual remains a source input,
discharged by qt-e-1514-global-thompson-residual and the final pre-exclusion
catalogue assembly. Exhaustion of the other initial families and the later
15.1.22 refinement remain with the ordinary catalogue owner.

Source: Aschbacher--Smith 15.1.20, printed pp.1094--1097, using 15.1.19(2).
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
open ChapterF.Source
private theorem rankOne_not_alternating_card
    {X : Type*} [Group X]
    (hm : IsBenderModel X ∨ Nonempty ((X ⧸ pCore 2 X) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1))
    (hc : Nat.card X = 360 ∨ Nat.card X = 2520) : False := by
  have hsmall : ¬16 ∣ Nat.card X := by rcases hc with h|h <;> norm_num [h]
  rcases hm with hm | hm
  · cases hm with
    | linear n hn iso =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := iso
      let : Fintype F := Fintype.ofFinite F
      let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
        (by simpa only [Nat.card_eq_fintype_card] using hF)
      have hneg : (-1 : F) = 1 := by
        apply (neg_eq_iff_add_eq_zero).mpr
        rw [show (1 : F) + 1 = 2 by norm_num]
        exact CharP.cast_eq_zero F 2
      have hcenter := BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one hneg
      have hcX := BenderSuzuki.External.huppert614_card_psl_mul_center (K := F)
      rw [hcenter,mul_one,←Nat.card_congr e.toEquiv,hF] at hcX
      have hd : 2^n ∣ Nat.card X := by rw [hcX]; exact dvd_mul_right _ _
      have hn3 : n ≤ 3 := by
        by_contra! hh
        exact hsmall ((Nat.pow_dvd_pow 2 hh).trans hd)
      interval_cases n <;> norm_num at hn hcX <;> omega
    | unitary n hn iso =>
      obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := iso
      have hd := BenderSuzuki.MatrixGroups.HermitianForm.BinarySylowOrder.cube_dvd_card_projective
        J (by omega : n ≠ 0) hF hconj
      rw [←Nat.card_congr e.toEquiv,←pow_mul] at hd
      exact hsmall ((Nat.pow_dvd_pow 2 (show 4 ≤ n*3 by omega)).trans hd)
    | suzuki m hm iso =>
      obtain ⟨e⟩ := iso
      have hd : (2^(2*m+1))^2 ∣ Nat.card X := by
        rw [Nat.card_congr e.toEquiv,BenderSuzuki.MatrixGroups.suzukiMatrixGroup_card m (by omega)]
        exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
      rw [←pow_mul] at hd
      exact hsmall ((Nat.pow_dvd_pow 2 (show 4 ≤ (2*m+1)*2 by omega)).trans hd)
  · obtain ⟨e⟩ := hm
    have hd : 16 ∣ Nat.card (X ⧸ pCore 2 X) := by
      rw [Nat.card_congr e.toEquiv,BenderSuzuki.MatrixGroups.suzukiMatrixGroup_card 1 (by decide)]
      norm_num
    exact hsmall (hd.trans (pCore 2 X).card_quotient_dvd_card)


variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

private theorem borel_eq (d : CaseIComponentData T M Mc V) :
    d.ordinaryBorel = ChapterF.Source.borel d.L d.S := by
  unfold ordinaryBorel ChapterF.Source.borel
  rw [←subgroupOf_normalizer_eq d.SL_le_L,subgroupOf_map_subtype]
  exact inf_comm _ _

private theorem rankOne_facts
    (hm : IsBenderModel d.L ∨ Nonempty ((d.L ⧸ pCore 2 d.L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)) (P : Sylow 2 d.L) :
    RankOneSylowFacts P := by
  rcases hm with hm | hm
  · apply IsRankOneModel.rankOneSylowFacts
    cases hm with
    | linear n hn h => exact .linear n (by omega) h
    | unitary n hn h => exact .projective_unitary n (by omega) h
    | suzuki n hn h => exact .suzuki n h
  · exact rankOneSylowFacts_of_rankOneQuotient (.suzuki 1 hm) P

private theorem borel_facts (s : d.PreExclusionSource h.normalized p)
    (hm : IsBenderModel d.L ∨ Nonempty ((d.L ⧸ pCore 2 d.L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)) :
    RankOneBorelFacts d.L d.S := by
  obtain ⟨P,hP⟩ := s.component_sylow
  exact rankOneBorelFacts_of_sylow d.L d.S P hP (rankOne_facts hm P)

/-- Properness and the actual rank-one model place the original intersection in its Borel. -/
theorem PreExclusionSource.rankOne_borel_bound
    (s : d.PreExclusionSource h.normalized p)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hm : IsBenderModel d.L ∨ Nonempty ((d.L ⧸ pCore 2 d.L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)) : d.ML ≤ d.ordinaryBorel := by
  rw [borel_eq]
  exact (borel_facts (h := h) s hm).unique_maximal _
    (s.ordinary hL).sylow_le_local (s.ordinary hL).local_proper

/-- The original M_L has exactly S_L as its two-core in the rank-one case. -/
theorem PreExclusionSource.rankOne_local_core
    (s : d.PreExclusionSource h.normalized p)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hm : IsBenderModel d.L ∨ Nonempty ((d.L ⧸ pCore 2 d.L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)) : d.ML.pCoreIn 2 = d.SL := by
  have hn : d.ML ≤ normalizer (d.SL : Set G) := by
    have hh := s.rankOne_borel_bound (h := h) hL hm
    rw [borel_eq] at hh
    exact hh.trans inf_le_right
  obtain ⟨P,hP⟩ := s.component_sylow
  obtain ⟨Q,hQ⟩ := P.exists_map_subtype_eq_of_le
    (show d.ML ≤ d.L from inf_le_right) (hP ▸ (s.ordinary hL).sylow_le_local)
  exact le_antisymm ((pCoreIn_le_sylow _ Q).trans_eq (hQ.trans hP))
    (le_pCoreIn_of_normalizes (T.isPGroup'.to_le (d.SL_le_S.trans d.S_le_T))
      (s.ordinary hL).sylow_le_local hn)

/-- The component stabilizer in M_Z preserves the actual Borel, even when M_Z permutes components. -/
theorem PreExclusionSource.rankOne_borel_normalized
    (s : d.PreExclusionSource h.normalized p)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hm : IsBenderModel d.L ∨ Nonempty ((d.L ⧸ pCore 2 d.L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)) :
    d.MZ ⊓ normalizer (d.L : Set G) ≤ normalizer (d.ordinaryBorel : Set G) := by
  have hnA : d.MZ ⊓ normalizer (d.L : Set G) ≤ normalizer (d.ML : Set G) :=
    (le_inf (inf_le_left.trans d.MZ.le_normalizer) inf_le_right).trans
      inf_normalizer_le_normalizer_inf
  have hnP : d.MZ ⊓ normalizer (d.L : Set G) ≤ normalizer (d.SL : Set G) := by
    rw [←s.rankOne_local_core (h := h) hL hm]
    exact hnA.trans (normalizer_le_normalizer_characteristic_image d.ML (pCore 2 d.ML))
  rw [borel_eq]
  exact (le_inf inf_le_right (hnP.trans (normalizer (d.SL : Set G)).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf

/-- The inner marked action and the local two-core identify the characteristic-two Borel. -/
theorem PreExclusionSource.rankOne_borel_characteristicTwo
    (s : d.PreExclusionSource h.normalized p)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hm : IsBenderModel d.L ∨ Nonempty ((d.L ⧸ pCore 2 d.L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1))
    (hc : d.L ⊓ centralizer ((center d.SL).map d.SL.subtype : Set G) ≤ d.ML) :
    HasCharacteristicTwo d.ordinaryBorel := by
  have hcore : d.ordinaryBorel.pCoreIn 2 = d.SL := by
    rw [borel_eq]
    exact (borel_facts (h := h) s hm).twoCore_eq
  apply (inf_centralizer_pCoreIn_le_iff 2 d.ordinaryBorel).mp
  rw [hcore]
  have hlocal := (inf_centralizer_pCoreIn_le_iff 2 d.ML).mpr
    (s.ordinary hL).local_characteristicTwo
  rw [s.rankOne_local_core (h := h) hL hm] at hlocal
  intro x hx
  apply hlocal
  refine ⟨hc ⟨?_,?_⟩,hx.2⟩
  · exact map_subtype_le _ hx.1
  · exact centralizer_le (map_subtype_le _) hx.2

private theorem borel_odd_quotient
    (s : d.PreExclusionSource h.normalized p)
    (hm : IsBenderModel d.L ∨ Nonempty ((d.L ⧸ pCore 2 d.L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)) :
    Odd (Nat.card (d.ordinaryBorel ⧸ pCore 2 d.ordinaryBorel)) := by
  obtain ⟨P,hP⟩ := s.component_sylow
  have hSL : d.SL ≤ d.ordinaryBorel := by
    rw [borel_eq]
    exact le_inf d.SL_le_L d.SL.le_normalizer
  obtain ⟨Q,hQ⟩ := P.exists_map_subtype_eq_of_le
    (show d.ordinaryBorel ≤ d.L from map_subtype_le _) (hP ▸ hSL)
  have hcore : d.ordinaryBorel.pCoreIn 2 = d.SL := by
    rw [borel_eq]
    exact (borel_facts (h := h) s hm).twoCore_eq
  have he : pCore 2 d.ordinaryBorel = (Q : Subgroup d.ordinaryBorel) := by
    apply map_injective d.ordinaryBorel.subtype_injective
    exact hcore.trans (hQ.trans hP).symm
  apply Nat.not_even_iff_odd.mp
  intro heven
  have hd : 2 ∣ (pCore 2 d.ordinaryBorel).index := even_iff_two_dvd.mp heven
  rw [he] at hd
  exact Q.not_dvd_index hd

/-- Original 15.1.19(2) forces the invariant orbit Borel into M_Z, giving the missing reverse inclusion. -/
theorem PreExclusionSource.rankOne_borel_eq_of_centralizer_le
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hm : IsBenderModel d.L ∨ Nonempty ((d.L ⧸ pCore 2 d.L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1))
    (hc : d.L ⊓ centralizer ((center d.SL).map d.SL.subtype : Set G) ≤ d.ML) :
    d.ML = d.ordinaryBorel := by
  have hinv := s.rankOne_borel_normalized (h := h) hL hm
  have hBL : d.ordinaryBorel ≤ d.L := map_subtype_le _
  obtain ⟨hf,ho⟩ := hL.relative_local_orbit_fitting_odd d.L_component.1 hBL
    (show d.MZ ≤ d.G1 from inf_le_left) hinv
    (s.rankOne_borel_characteristicTwo (h := h) hL hm hc)
    (borel_odd_quotient (h := h) s hm)
  have hBG : componentOrbit d.ordinaryBorel d.MZ ≤ d.G1 := by
    apply iSup_le
    intro a
    rintro x ⟨b,hb,rfl⟩
    exact d.G1.mul_mem (d.G1.mul_mem a.property.1 (d.L_component.1 (hBL hb)))
      (d.G1.inv_mem a.property.1)
  have hle := s.constrained_solvable_control (h := h) hG hM hu hne hmany hres hBG
    (le_normalizer_componentOrbit _ _) hf ho
  exact le_antisymm (s.rankOne_borel_bound (h := h) hL hm)
    (le_inf ((le_componentOrbit _ _).trans hle) hBL)

/-- The actual rank-one carriers exclude the two alternating exceptions to inner placement. -/
theorem PreExclusionSource.rankOne_centralizer_le
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hm : IsBenderModel d.L ∨ Nonempty ((d.L ⧸ pCore 2 d.L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)) :
    d.L ⊓ centralizer ((center d.SL).map d.SL.subtype : Set G) ≤ d.ML := by
  obtain ⟨z,hz,hzne⟩ := (bot_or_exists_ne_one (centralInvolutions T)).resolve_left
    (centralInvolutions_ne_bot_of_maximal_local T hM.1)
  rcases d.ordinary_centralizer_placement_or_alternating hG hu h s.centralizer_sylow
    s.odd_core hL hz hzne with hc | ⟨α,ha,halt⟩
  · exact hc
  · apply False.elim
    apply rankOne_not_alternating_card hm
    rcases halt with ⟨σ,e,_,_⟩ | ⟨σ,e,_,_⟩
    · left
      let f := (subgroupOfEquivOfLe d.L_component.1).symm.trans e
      rw [Nat.card_congr f.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
      norm_num
    · right
      let f := (subgroupOfEquivOfLe d.L_component.1).symm.trans e
      rw [Nat.card_congr f.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
      norm_num

/-- The whole initial rank-one family, including central two-covers of Sz(8),
with its actual Borel clause proved from the original source hypotheses. -/
theorem PreExclusionSource.ordinary20_of_rankOne
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hm : IsBenderModel d.L ∨ Nonempty ((d.L ⧸ pCore 2 d.L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)) : d.Ordinary20Alternatives := by
  exact .rankOne hm (s.rankOne_borel_eq_of_centralizer_le (h := h) hG hM hu hne hmany hres hL hm
    (s.rankOne_centralizer_le (h := h) hG hM hu hL hm))

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
