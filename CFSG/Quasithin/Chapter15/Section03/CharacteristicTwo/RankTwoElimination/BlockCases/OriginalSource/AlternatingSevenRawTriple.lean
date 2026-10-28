module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.AlternatingSevenRawCover
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.RankTwoCoreCenterAction
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.CoreStarAction
public import Theory.GroupTheory.CComponent.TripleSevenTheta
public import Theory.Alternating.SevenQuasisimpleExtension
/-!
# Excluding the original raw symmetric-seven row

The marked natural seven-point moved section identifies the star component
with A₇. The actual core-to-star cover has only the ordinary and triple
possibilities. The ordinary case was excluded by the odd offender's
normalizer rank. For the triple case, the local theta generators lie in
L: a cubic actor outside a triple A₇ component would raise three-rank to
three. Thus Y₊ contains the cubic core center in its quotient image, and
the actual two-radical fixes that center. Every outer automorphism of
3·A₇ inverts it, forcing the radical's core automorphisms to be inner.
Equivariance through the literal core-to-star map then puts R* inside L*,
contradicting the odd offender on the actual moved section.

The final consumer retains the original selected local hypotheses, actual
component and all six B.5 source clauses. The stronger moved-section row
consumer avoids any short-block reconstruction or blanket assertion about
the local action kernel. Source: Aschbacher–Smith A.3.18,B.5.1,C.2.7,
15.3.17–21, pp.51–52,99–103,145–147,1126–1127; GLS3 5.2.3,5.2.7.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
/-- The literal triple-cover quotient places every local theta generator in L. -/
theorem yplus_le_of_tripleSeven_quotient
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hθ : theta (d.MI I) = d.Yplus) (hrI : primeRank 3 I ≤ 2)
    (e : (c.L ⧸ pCore 2 c.L) ≃* GLS3.Chapter5.OddCentralCovers.TripleSeven) : d.Yplus ≤ c.L := by
  let K := c.L.subgroupOf I
  let a : K ≃* c.L := subgroupOfEquivOfLe (component_le c)
  let b : (K ⧸ pCore 2 K) ≃* GLS3.Chapter5.OddCentralCovers.TripleSeven :=
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e
  have hYN : d.Yplus ≤ normalizer (c.L : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr c.commutator_eq.ge
  have hYNK : d.Yplus.subgroupOf I ≤ normalizer (K : Set I) := by
    rw [←subgroupOf_normalizer_eq (component_le c)]
    exact comap_mono hYN
  rw [←hθ]
  apply (closure_le _).mpr
  rintro x ⟨hx,hx3⟩
  let y : I := ⟨x,hx.2⟩
  have hy3 : orderOf y = 3 := by simpa only [←Subgroup.orderOf_coe] using hx3
  have hyN : y ∈ normalizer (K : Set I) :=
    hYNK (hθ ▸ subset_closure ⟨hx,hx3⟩)
  exact TripleSevenTheta.order_three_mem K
    (LinearThree.Extension.SourceCases.component_in_overgroup d c) b hrI hy3 hyN

/-- The actual radical acts innerly on a triple A₇ core quotient. -/
theorem source_rankTwo_tripleSeven_radical_inner
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (c : ComponentWitness d I) (hYL : d.Yplus ≤ c.L)
    (e : (c.L ⧸ pCore 2 c.L) ≃* GLS3.Chapter5.OddCentralCovers.TripleSeven)
    (r : normalizer (c.L : Set G)) (hr : (r : G) ∈ d.R) :
    ∃ k : c.L ⧸ pCore 2 c.L,
      quotientAut (pCore 2 c.L) (c.L.normalizerMonoidHom r) = MulAut.conj k := by
  by_contra hi
  let a := quotientAut (pCore 2 c.L) (c.L.normalizerMonoidHom r)
  have hout : ∀ k, a ≠ MulAut.conj k := fun k hk => hi ⟨k,hk⟩
  have hc : Nat.card (center (c.L ⧸ pCore 2 c.L)) = 3 :=
    (Nat.card_congr (centerCongr e).toEquiv).trans
      GLS3.Chapter5.OddCentralCovers.tripleSeven_center_card
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := center (c.L ⧸ pCore 2 c.L)) 3
    (by rw [hc])
  have hfix := source_rankTwo_radical_fixes_core_center hG d hI htwo c hYL hc r hr
    (z : c.L ⧸ pCore 2 c.L) z.property
  have hinv := Theory.AlternatingSevenExtension.center_inverted_of_tripleSeven_model
    e a hout (z : c.L ⧸ pCore 2 c.L) z.property
  have hpow : (z : c.L ⧸ pCore 2 c.L) ^ 2 = 1 := by
    rw [pow_two]
    calc
      (z : c.L ⧸ pCore 2 c.L) * z = (z : c.L ⧸ pCore 2 c.L)⁻¹ * z :=
        congrArg (fun t => t * (z : c.L ⧸ pCore 2 c.L)) (hfix.symm.trans hinv)
      _ = 1 := inv_mul_cancel _
  have hd := orderOf_dvd_of_pow_eq_one hpow
  rw [Subgroup.orderOf_coe,hz] at hd
  norm_num at hd

/-- The raw natural A₇ moved section also excludes the genuine triple cover. -/
theorem no_raw_alternatingSeven_of_triple_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (eq : (c.L ⧸ pCore 2 c.L) ≃* GLS3.Chapter5.OddCentralCovers.TripleSeven) :
    let C := starImage c.L d.R c.L
    let J := Representation.BinaryOffender.offenderSubgroup (starRepresentation c.L d.R)
    ∀ (s : MovedSection ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J)),
      ActionEquiv (s.action.comp (C.subgroupOf J).subtype) (alternatingNatural 7) → False := by
  intro C J s es
  have h := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI
  have hrI : primeRank 3 I ≤ 2 :=
    (OutsideStructure.outside_sqtk hG d hI).stronglyQuasithin 3 (by decide) (by decide)
  have hYL := yplus_le_of_tripleSeven_quotient d c h11.theta_eq.symm hrI eq
  have houter := alternatingSeven_raw_radical_not_le_component h s es
  let : (c.L.subgroupOf (c.L ⊔ d.R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le c.L.le_normalizer h.normalizes)
  have hfit := (ChapterC.C27Source.star_fitting_quasisimple
    (ChapterC.C27Source.source_join_input h)).1
  apply houter
  rintro x ⟨r,hr,rfl⟩
  let nr : normalizer (c.L : Set G) := ⟨(r : G),h.normalizes hr⟩
  exact star_mem_of_core_action_inner h.normalizes hfit nr r.property
    (source_rankTwo_tripleSeven_radical_inner hG d hI htwo c hYL eq nr hr)

private noncomputable def marked_seven_triple_restriction
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) {H L : Subgroup D}
    (e : MarkedActionEquiv ρ H L (BinaryPermutation.naturalRepresentation (Fin 7))
      (alternatingGroup (Fin 7))) :
    ActionEquiv (ρ.comp L.subtype) (alternatingNatural 7) where
  groupEquiv := e.subgroupEquiv
  linearEquiv := e.action.linearEquiv
  intertwines g v := by
    have he := e.action.intertwines ⟨g,e.contained g.property⟩ v
    rw [e.compatible] at he
    exact he

/-- The marked natural seven-point moved section is impossible under the
original selected rank-two hypotheses. No block reconstruction is required. -/
theorem source_15_3_21_symmetricSeven_row
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I) :
    let C := starImage c.L d.R c.L
    let J := Representation.BinaryOffender.offenderSubgroup (starRepresentation c.L d.R)
    ∀ (_hCJ : C ≤ J)
      (s : MovedSection ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J)),
      MarkedActionEquiv s.action (Representation.BinaryOffender.offenderSubgroup s.action)
        (C.subgroupOf J) (BinaryPermutation.naturalRepresentation (Fin 7))
        (alternatingGroup (Fin 7)) → False := by
  intro C J hCJ s e
  have h := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  let eC : C ≃* alternatingGroup (Fin 7) :=
    (subgroupOfEquivOfLe hCJ).symm.trans e.subgroupEquiv
  let es := marked_seven_triple_restriction s.action e
  rcases coreToStar_alternatingSeven_alternatives d c h.normalizes eC with hh | hh
  · obtain ⟨eq⟩ := hh
    exact no_raw_alternatingSeven_of_core_quotient
      hG d hempty hM hu hmany hI htwo hf c eq s es
  · obtain ⟨_,⟨eq⟩⟩ := hh
    exact no_raw_alternatingSeven_of_triple_quotient
      hG d hempty hM hu hmany hI htwo hf c eq s es

/-- Original15.3.21 excludes the literal symmetric-seven B.5 row with all
six actual source clauses and the original selected component. -/
theorem source_15_3_21_raw_symmetricSeven
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I) :
    let C := starImage c.L d.R c.L
    let J := Representation.BinaryOffender.offenderSubgroup (starRepresentation c.L d.R)
    ∀ (_hCJ : C ≤ J)
      (qsrc : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J)),
      MarkedActionEquiv qsrc.sectionData.action
        (Representation.BinaryOffender.offenderSubgroup qsrc.sectionData.action)
        (C.subgroupOf J) (BinaryPermutation.naturalRepresentation (Fin 7))
        (alternatingGroup (Fin 7)) → False := by
  intro C J hCJ qsrc e
  exact source_15_3_21_symmetricSeven_row
    hG d hempty hM hu hmany hI htwo hf c hCJ qsrc.sectionData e
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
