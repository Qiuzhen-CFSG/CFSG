module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.OrbitCoordinates
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.OriginalOrbit
public import Theory.GroupTheory.PrimeRankAutomorphismOrder
public import Theory.Quasithin.CoprimeRank

/-!
# The original rank-one component is normal

The genuine cubic residual identifies the nonnormal orbit span and contains
Y₊. The actual component model comparison leaves PSL₂ or PSL₃(2).
The marked two-factor quotient excludes PSL₃(2); the binary PSL₂ Borel is
solvable, invariant and of cubic rank greater than one, contrary to the
proved original15.3.26(3). All index, model and residual inputs are obtained
from the original local source hypotheses.

Source: Aschbacher–Smith15.3.27(1), printed p.1130.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06
open RankOneConfiguration
open RankOneConfiguration.Parabolics
open Placement Placement.OrbitBorel
variable {G : Type*} [Group G] [Finite G]
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
open LinearTwo in
theorem source_orbit_borel_witness
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hS : Chapter1.IsSylowIn 2 d.S I) (h : RankOneFacts d I)
    (hi : (normalizer (c.L : Set G)).relIndex I = 2)
    (hYL : d.Yplus ≤ localSpan c.L d.S)
    (hr : primeRank 3 d.Yplus = 1)
    {n : ℕ} (hn₂ : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (a : Coordinates (localSpan c.L d.S) d.S F) :
    let B := canonicalBorel (localSpan c.L d.S) d.S
    B ≤ I ∧ d.Yplus ≤ B ∧ Group.IsSolvable B ∧
      d.Yplus ⊔ d.S ≤ normalizer (B : Set G) ∧
      Even n ∧ 1 < primeRank 3 B := by
  let L₀ := localSpan c.L d.S
  let B := canonicalBorel L₀ d.S
  have hLI := (orbit_normal_and_le d c hS hi).1
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact (show 4 = 2 ^ 2 from rfl).le.trans (Nat.pow_le_pow_right (by decide) hn₂)
  let H : Subgroup G := d.Yplus ⊔ (d.S ⊓ L₀)
  have hHY : H ≤ d.Yplus ⊔ d.S := sup_le le_sup_left (inf_le_left.trans le_sup_right)
  let := yplus_join_solvable d h
  have hsolH : Group.IsSolvable H :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hHY)
  have hYB : d.Yplus ≤ B := le_sup_left.trans
    (a.solvable_overgroup_le hfour H (sup_le hYL inf_le_right) le_sup_right hsolH)
  have hSN : d.S ≤ normalizer (B : Set G) :=
    canonicalBorel_normalized (le_normalizer_conjugateSpanBy c.L d.S)
      (sylow_normalizes_orbit_root d c)
  have hYSN : d.Yplus ⊔ d.S ≤ normalizer (B : Set G) :=
    sup_le (hYB.trans B.le_normalizer) hSN
  have hd : 3 ∣ Nat.card d.Yplus := by
    by_contra hnot
    have hz : primeRank 3 d.Yplus = 0 := PrimeRank.eq_zero_iff_not_dvd_card.mpr hnot
    omega
  have hb := a.borel_even_and_rank hF
    (hd.trans (card_dvd_of_injective (inclusion hYB) (inclusion_injective hYB)))
  exact ⟨(canonicalBorel_le _ _).trans hLI, hYB, a.borel_solvable hF, hYSN, hb⟩


/-- The actual shadow has cubic rank exactly one. -/
theorem source_yplus_three_rank_one
    (d : LocalData G) {I : Subgroup G} (h : OutsideStructure.Conclusions d I)
    (hshadow : SymmetricThreeShadow d.Yplus d.S) : primeRank 3 d.Yplus = 1 := by
  have hne : d.Yplus ≠ ⊥ := by
    intro he
    apply h.action_normalizer.2.2
    simp [LocalData.starImage, localActionImage, he]
  have hc : Nat.card (d.Yplus ⧸ pCore 2 d.Yplus) = 3 :=
    RankOne.index_three_of_shadow hshadow (by rw [h.theta_eq, theta_idempotent]) hne
  rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 d.Yplus) pCore_isPGroup]
  have hb : primeRank 3 (d.Yplus ⧸ pCore 2 d.Yplus) ≤ 1 :=
    primeRank_le_of_card_le_prime_pow (by simpa using hc.le)
  have hn : primeRank 3 (d.Yplus ⧸ pCore 2 d.Yplus) ≠ 0 := by
    intro hz
    have hd := PrimeRank.eq_zero_iff_not_dvd_card.mp hz
    simp only [hc, dvd_refl, not_true_eq_false] at hd
  omega

/-- The literal source residual contains the original Y₊. -/
theorem source_nonnormal_orbit_contains_yplus
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) (hn : ¬ (c.L.subgroupOf I).Normal)
    (hS : Chapter1.IsSylowIn 2 d.S I) (h : RankOneFacts d I) :
    d.Yplus ≤ localSpan c.L d.S := by
  obtain ⟨hi,hm⟩ := source_component_orbit_index_and_model hG d hI c hn
  let a := subgroupOfEquivOfLe (component_le c)
  let e := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let _ := c.core_quotient_quasisimple
  let _ := nonnormal_component_quotient_isSimple d c hm
  let _ := IsQuasisimple.of_mulEquiv e.symm
  let _ := e.isSimpleGroup
  have hd : 3 ∣ Nat.card ((c.L.subgroupOf I) ⧸ pCore 2 (c.L.subgroupOf I)) := by
    rw [Nat.card_congr e.toEquiv]
    exact component_three_divides_quotient d c
  have hres := Candidates.source_threeResidual_eq_nonnormal_orbit hG d hI
    (component_le c) (LocalData.thompson_component_in c.le_thompson c.component) hd
    (component_moved_by_sylow d c hS hi)
  exact yplus_le_orbit_of_residual d c h hres

/-- Original15.3.27(1), with every classification and orbit premise discharged. -/
theorem source_lemma_15_3_27_1
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) : (c.L.subgroupOf I).Normal := by
  by_contra hn
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection hG d hempty hM hu hmany I hI
  have hS : Chapter1.IsSylowIn 2 d.S I := h11.sylow
  have h := source_lemma_15_3_26_1 hG d hempty hM hu hmany hshadow hI
  have hr := source_yplus_three_rank_one d h11 hshadow
  have hcontrol : SolvableInvariantControl d I :=
    source_lemma_15_3_26_3 hG d hempty hM hu hmany hI hf
  have hi := (source_component_orbit_index_and_model hG d hI c hn).1
  have hYL := source_nonnormal_orbit_contains_yplus hG d hI c hn hS h
  rcases source_component_models_of_nonnormal hG d hI hf c hn hS with
    ⟨n,hn₂,hm,_⟩ | ⟨hm,_⟩
  · obtain ⟨F, hfield, hfinite, hF, ⟨e⟩⟩ := hm
    let _ := Fintype.ofFinite F
    let _ : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    obtain ⟨a⟩ := source_linearTwo_orbit_coordinates d c hS hi e
    obtain ⟨hBI, _, hs, hnB, _, hrB⟩ := source_orbit_borel_witness d c hS h hi hYL hr hn₂ hF a
    exact (not_lt_of_ge
      (invariant_solvable_three_rank_le_one d h hr hcontrol hBI hs hnB)) hrB
  · have hSM : d.S ≤ d.MI I :=
      le_inf (inf_le_left.trans d.sylow_le) (le_sup_right.trans hI.1.2)
    have hSY := hSM.trans (yplus_normalized_by_intersection d h)
    obtain ⟨a⟩ := source_linearThree_productCoordinates d c hS hi hYL hSY hm
    have hYM : d.Yplus ≤ d.MI I := h.residual ▸ map_subtype_le _
    have hcard := intersection_overgroup_sylow_three_card d h hr le_rfl hYM
    exact LinearThree.ProductCalculation.not_sylow_three_card_eq_three a.firstSylow a.secondSylow
      (LinearThree.model_sylow_self_normalizing a.firstModel a.firstSylow)
      (LinearThree.model_sylow_self_normalizing a.secondModel a.secondSylow)
      _ a.sylow_invariant a.exchange a.exchange_first a.exchange_second a.exchange_invariant
      (LinearThree.sylow_three_card_image a.quotient a.kernel_two _
        (LinearThree.sylow_three_card_subgroupOf _ _ hYL hcard))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
