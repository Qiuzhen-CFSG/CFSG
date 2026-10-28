module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.BaumannSylow.Source
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.Assembly

/-!
# Source15.4.11(3): the Thompson subgroup acts noncentrally

Suppose a maximal local M has central Thompson action. Its Baumann
normalizer is M, while an actual outside H-star member is a minimal
parabolic with noncentral Thompson action. Enclose H in a maximal local
to inherit solvability and three-rank at most two. The full B.2.16
theorem then supplies its exceptional decomposition. The proved B.6.10
application makes Baum(T) Sylow in O²(H)Baum(T), contradicting the
genuine earlier3.1.1 common-normal consequence.

The empty-family wrappers construct every local input from the original
source hypotheses and retain only the named universal earlier results.
Source: Aschbacher--Smith15.4.11(3), using the14.1.4 argument, pp.976,1160.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource
open MaximalPrimeSource FamilySource FamilySource.ModuleStructure
open ChapterA.Section05To06
open Chapter1.RadicalNormalizers.ThompsonSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal noncentrality assertion15.4.11(3), from the preceding
centralizer and solvability conclusions and full earlier source theorems. -/
theorem source_lemma_15_4_11_three
    (hB : TheoremB216.{u}) (h311 : RatioSource.Earlier311 (G := G))
    (T : Sylow 2 G) (h : SourceHypotheses T)
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T)
    (hsol : ∀ M ∈ maximalLocals T, Group.IsSolvable M) :
    ∀ M ∈ maximalLocals T,
      ⁅localV T M,elementaryAbelianMaxJ (T : Subgroup G)⁆ ≠ ⊥ := by
  intro M hM hcentral
  obtain ⟨H,hH⟩ := RatioSource.exists_HStar h hM.1
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hchar : HasCharacteristicTwo H := Chapter1.mem_He_iff.mp
    (Chapter1.lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T) hH.1.1)
  have hmoved := outside_thompson_moved_of_central h.simpleQTKE T M H
    hM.1 hM.2 hC hcentral hH
  have hpar := outside_minimalParabolic_of_central h.simpleQTKE T M H
    hM.1 hM.2 hC hcentral hH
  have hcore : pCore 2 H ≠ ⊥ := by
    intro he
    exact hH.1.1.1 (by simp only [Subgroup.pCoreIn,he,Subgroup.map_bot])
  obtain ⟨N,hN,hHN⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot H hcore
  let : Group.IsSolvable N := hsol N ⟨hN,hTH.trans hHN⟩
  have hsH : Group.IsSolvable H :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hHN)
  have hrank : primeRank 3 H ≤ 2 :=
    (Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion hHN) (inclusion_injective hHN)).trans
      ((h.simpleQTKE.twoLocal_sqtk hN.1).stronglyQuasithin 3 Nat.prime_three (by decide))
  have hd := hB H hsH (generalizedFitting_eq_pCore_of_selfCentralizing 2 hchar)
    (T.subtype hTH)
  let := hd.elementary
  rcases hd.alternatives with hj | hex
  · apply hmoved
    have hj' := map_mono (f := H.subtype) hj.1
    rw [←elementaryAbelianMaxJ_map_injective _ H.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,
      FamilySource.ThompsonSource.closure_eq_internalModule,map_centralizer_subtype] at hj'
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp (hj'.trans inf_le_right))
  · obtain ⟨d⟩ := hex
    have hc : d.count = 1 ∨ d.count = 2 := d.count_eq_one_or_two (by
      rw [FamilySource.ThompsonSource.star_kernel T H hTH hC]
      exact pCore_isPGroup) hrank
    exact outside_not_baumann_sylow_of_central h.simpleQTKE h311 T M H
      hM.1 hM.2 hC hcentral hH
      (BaumannSylow.ambient_sylow_of_exceptional T H hTH hC hpar d hc)

variable
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (h311 : RatioSource.Earlier311 (G := G))
    (hD15 : RatioSource.InsideCore.EarlierD15.{u})
    (hD14 : RatioSource.InsideCore.EarlierD14Sylow.{u})
    (h29 : RatioSource.OutsideWitness.EarlierE29Solvable.{u})
    (hB : TheoremB216.{u})

include hA hC h311 hD15 hD14 h29 hB

/-- No local noncentrality premise remains in the original empty-family branch. -/
theorem source_thompson_noncentral
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard) :
    ∀ M ∈ maximalLocals T,
      ⁅localV T M,elementaryAbelianMaxJ (T : Subgroup G)⁆ ≠ ⊥ := by
  obtain ⟨hc,hlocals,_⟩ := source_local_preparation hA hC h311 hD15 hD14 h29
    hG T hempty hmany
  exact source_lemma_15_4_11_three hB h311 T (sourceHypotheses hG T hempty hmany)
    hc (fun M hM => (hlocals M hM).1)

/-- The actual B.2.16 datum for each maximal local, with the formerly
separate15.4.11(3) input now discharged from the original hypotheses. -/
theorem source_exceptional_of_empty
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard)
    (M : Subgroup G) (hM : M ∈ maximalLocals T) :
    ∃ hE : IsElementaryAbelian 2
      (Chapter1.RadicalNormalizers.ThompsonSource.closure (T.subtype hM.2)),
      ∃ d : @Exceptional M _ (T.subtype hM.2) hE, d.count = 1 ∨ d.count = 2 := by
  exact source_exceptional hA hC h311 hD15 hD14 h29 hB hG T hempty hmany M hM
    (source_thompson_noncentral hA hC h311 hD15 hD14 h29 hB hG T hempty hmany M hM)

end CFSG.Quasithin.Chapter15.Section04.InitialSource
