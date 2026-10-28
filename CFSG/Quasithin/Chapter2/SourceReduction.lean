module
public import CFSG.Quasithin.Chapter2.Section05.Source
public import CFSG.Quasithin.Chapter2.Section04.CoreSource
public import CFSG.Quasithin.Chapter2.Section04.Statement
public import CFSG.Quasithin.Chapter2.EmptyDelta
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.CubicDoubleCenterSource

/-!
# The original Chapter 2 reduction to its selected-block classification

The original unique maximal local subgroup produces an actual minimal block
and an ambient Sylow containing its local Sylow strictly. The original
uniqueness hypothesis transports to that Sylow. Section 2.5 now supplies
the nonempty characteristic-two Gamma family, and the empty-delta branch
is proved by the native Bender theorem. Thus only the selected-block
classification in Section 2.4 remains explicit in the Chapter 2 theorem.

The terminal dispatcher uses the complete single-A₃ source branch and leaves
exactly the linear, A₅ and paired-A₃ exclusions. These are genuine source
obligations; this module does not assert the complete classification.

Source: Aschbacher–Smith, Theorems 2.1.1 and 2.4.1, printed pp.518,527–550,
and the completion of Section 2.5 on printed p.570.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G]

theorem theorem_2_4_1_of_selected_block_classification
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hblock : ∀ (M : Subgroup G) (d : MinimalBlockSetup M) (P : Sylow 2 G),
      IsMaximalTwoLocal M → (P : Subgroup G) ≤ M →
      (∀ N : Subgroup G, IsMaximalTwoLocal N → (P : Subgroup G) ≤ N → N = M) →
      (delta (Chapter1.He G) M).Nonempty →
      (d.S : Subgroup d.H).map d.H.subtype < (P : Subgroup G) →
      IsTheorem241Model G)
    (T : Sylow 2 G) (M : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty)
    (hgamma : (gammaEvenZero (Chapter1.He G) M).Nonempty) : IsTheorem241Model G := by
  obtain ⟨H,hH⟩ := hgamma
  obtain ⟨d,_hd,P,hPM,hSP,_hcore⟩ := exists_minimalBlockSetup_with_core hG T hTM hu hH
  have hPunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (P : Subgroup G) ≤ N → N = M := by
    intro N hN hPN
    have hNM : N ≤ M := by
      apply core_overgroup_le_of_sylow T hTM hu
        (Chapter1.mem_H_of_isTwoLocal hN.1) (P.subtype hPM)
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hPM] using hPN
    exact le_antisymm hNM (hN.2 hM.1 hNM)
  exact hblock M d P hM hPM hPunique hdelta hSP

theorem theorem_2_1_1_of_selected_block_classification
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hblock : ∀ (M : Subgroup G) (d : MinimalBlockSetup M) (P : Sylow 2 G),
      IsMaximalTwoLocal M → (P : Subgroup G) ≤ M →
      (∀ N : Subgroup G, IsMaximalTwoLocal N → (P : Subgroup G) ≤ N → N = M) →
      (delta (Chapter1.He G) M).Nonempty →
      (d.S : Subgroup d.H).map d.H.subtype < (P : Subgroup G) →
      IsTheorem241Model G)
    (T : Sylow 2 G) (M : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M) :
    ClassificationModels.IsTheorem211Model G := by
  classical
  by_cases hd : delta (Chapter1.He G) M = ∅
  · exact BenderFusion.theorem_2_1_1_of_delta_empty hG T M hM hTM hu hd
  · have hdelta := Set.nonempty_iff_ne_empty.mpr hd
    exact (theorem_2_4_1_of_selected_block_classification hG hblock T M hM hTM hu hdelta
      (Section05.gammaEvenZero_nonempty_of_delta_nonempty hG T hM hTM hu hdelta)).toTheorem211Model

variable {M : Subgroup G}

/-- The genuine remaining terminal families after the original single-cubic
classification has been discharged. -/
theorem selected_block_classification_of_terminal_cases
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (_hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hlinear : ¬ IsTheorem241Model G → ∀ n,
      ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n → False)
    (hfive : ¬ IsTheorem241Model G →
      ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5 → False)
    (hpair : ¬ IsTheorem241Model G → d.L0 ≠ d.block →
      ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 3 → False) :
    IsTheorem241Model G := by
  classical
  by_contra hn
  have htype := ChapterC.Section05.BlockAnalysis.chiZero_equiv
    (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective) d.block_type.2
  rcases htype with ⟨n,hL⟩ | h3 | h5
  · exact hlinear hn n hL
  · by_cases he : d.L0 = d.block
    · exact hn (d.single_cubic_classification hG T hST he h3 hM hu hdelta)
    · exact hpair hn he h3
  · exact hfive hn h5


end CFSG.Quasithin.Chapter2
