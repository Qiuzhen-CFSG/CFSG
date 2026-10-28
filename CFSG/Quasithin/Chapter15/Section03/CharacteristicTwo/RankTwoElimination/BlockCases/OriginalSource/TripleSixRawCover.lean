module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.RankTwoCoreCenterAction
public import Theory.Alternating.OddCentralCovers
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract

/-!
# The actual core cover in the raw triple-six row

The perfect core-to-star cover preserves the central simple quotient A₆.
The trivial two-core makes the core center odd, so the multiplier theorem
allows orders one and three. The cubic star center excludes order one.
Both groups are therefore the actual hexacode triple cover; equality of
orders makes the original surjective core-to-star map injective.

The final consumer keeps the actual B.5 moved section and all six source
clauses. Only the cubic center and central quotient of its triple-six row
are used. The module geometry needed for the source exclusion is separate.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.2(8),
B.5.1, C.2.7 and 15.3.21, printed pp.86,99–103,145–147,1127;
GLS3, Theorem 5.2.3(c).
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

/-- A literal triple-six star component has no further core-to-star kernel. -/
theorem coreToStar_tripleSix_data
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hR : d.R ≤ normalizer (c.L : Set G))
    (hcenter : Nat.card (center (starImage c.L d.R c.L)) = 3)
    (e : (starImage c.L d.R c.L ⧸ center (starImage c.L d.R c.L)) ≃*
      alternatingGroup (Fin 6)) :
    Function.Injective (coreToStar hR) ∧
      Nat.card (center (c.L ⧸ pCore 2 c.L)) = 3 ∧
      Nonempty ((c.L ⧸ pCore 2 c.L) ≃* Atlas.Codes.HexEvenAutomorphisms) := by
  let C := starImage c.L d.R c.L
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : Nontrivial (C ⧸ center C) := e.symm.injective.nontrivial
  let : Nontrivial C := (QuotientGroup.mk'_surjective (center C)).nontrivial
  have hne : C ≠ ⊥ := (nontrivial_iff_ne_bot C).mp inferInstance
  let f := coreStarCover hR c.core_quotient_quasisimple hne
  let q := f.quotientCenterEquiv.trans e
  let : IsQuasisimple (c.L ⧸ pCore 2 c.L) := c.core_quotient_quasisimple
  let : IsQuasisimple C := IsQuasisimple.of_surjective f.toMonoidHom f.surjective
  have ho : Odd (Nat.card (center (c.L ⧸ pCore 2 c.L))) :=
    Nat.not_even_iff_odd.mp (fun hh =>
      PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
        (pCore_quotient_pCore_eq_bot 2) _ le_rfl (even_iff_two_dvd.mp hh))
  have hc : Nat.card (center (c.L ⧸ pCore 2 c.L)) = 3 := by
    rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 6 (by decide) q ho with hc | ⟨_,hc⟩
    · have hz : center (c.L ⧸ pCore 2 c.L) = ⊥ := (eq_bot_iff_card _).mpr hc
      have hzC : center C = ⊥ := by
        apply bot_unique
        intro z hzC
        obtain ⟨x,hx⟩ := f.surjective z
        have hxZ : x ∈ center (c.L ⧸ pCore 2 c.L) := by
          rw [← f.comap_center]
          change f.toMonoidHom x ∈ center C
          rwa [hx]
        rw [hz,mem_bot] at hxZ
        rw [←hx,hxZ,map_one]
        exact one_mem _
      have hh := (eq_bot_iff_card _).mp hzC
      change Nat.card (center (starImage c.L d.R c.L)) = 1 at hh
      omega
    · exact hc
  obtain ⟨eQ⟩ := GLS3.Chapter5.OddCentralCovers.triple_six_equiv_hexacode q hc
  obtain ⟨eC⟩ := GLS3.Chapter5.OddCentralCovers.triple_six_equiv_hexacode e hcenter
  have hcard : Nat.card (c.L ⧸ pCore 2 c.L) = Nat.card C :=
    (Nat.card_congr eQ.toEquiv).trans (Nat.card_congr eC.toEquiv).symm
  exact ⟨(f.surjective.bijective_of_nat_card_le hcard.le).1,hc,⟨eQ⟩⟩

/-- The literal triple-six moved row supplies the actual core model. -/
theorem source_tripleSix_core_data
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
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
      ChapterB.SourceInduction.ProjectiveLine.TripleSixAction qsrc.sectionData.action (C.subgroupOf J) →
      ∃ hR : d.R ≤ normalizer (c.L : Set G),
        Function.Injective (coreToStar hR) ∧
        Nat.card (center (c.L ⧸ pCore 2 c.L)) = 3 ∧
        Nonempty ((c.L ⧸ pCore 2 c.L) ≃* Atlas.Codes.HexEvenAutomorphisms) := by
  intro C J hCJ qsrc a
  have h := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  let j : C ≃* C.subgroupOf J := (subgroupOfEquivOfLe hCJ).symm
  have hc : Nat.card (center C) = 3 := by
    rw [Nat.card_congr ((centerCongr j).trans a.centerEquiv).toEquiv]
    simp
  have hm : (center C).map j.toMonoidHom = center (C.subgroupOf J) := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact (centerCongr j ⟨x,hx⟩).property
    · intro hz
      exact ⟨j.symm z,(centerCongr j.symm ⟨z,hz⟩).property,j.apply_symm_apply z⟩
  let e := (QuotientGroup.congr _ _ j hm).trans a.quotientEquiv
  exact ⟨h.normalizes,coreToStar_tripleSix_data d c h.normalizes hc e⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
