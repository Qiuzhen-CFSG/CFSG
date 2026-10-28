module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.FirstFlagBound
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.CoveredOne
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OrdinaryNormalizerRecognition

/-!
# The remaining covered residual in the original fixed-module problem

The original first-flag Baumann bound is now proved, so the two action-kernel
cases of the solvable-centralizer selection argument apply to that same R₁.
If every original relatively normal two-perfect subgroup satisfies 13.3.9,
both cases force an ordinary quotient, contradicting the retained triple
cover. Thus a covered solvable escape supplies a particular nontrivial
{2,3}-subgroup violating the selected-residual conclusion. The original
13.3.8 theorem supplies its prime support, and the proved L₀ normalizer
excludes the central residual alternative. Frattini lifting of the covered
augmentation comparison also excludes the full L₁ alternative.

The final theorem feeds this reduction into the original fixed-module
recognition alternative. No Baumann, fusion, normalizer supplement or local
classification callback is added. Proving 13.3.9 for this actual residual,
and discharging the retained earlier-source inputs, remain necessary for
13.4.1; this module does not claim that final theorem.

Source: Aschbacher--Smith 13.3.8--9 and 13.4.8, pp.886--887,904--905.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Solvable Nonsolvable
open Section03.Noncentrality.SupercriticalSource
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement (zero one)
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The proved original Baumann bound forces a concrete remaining 13.3.9
residual in any covered solvable escape. All normality is relative to C_G(z). -/
theorem covered_solvable_residual_obstruction
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Section08.SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G))) :
    ∃ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) ∧
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) ∧
      Y ≤ normalizer (L : Set G) ∧ IsPPerfect 2 Y ∧ IsPiGroup twoThreePrimes Y ∧
      Y ≠ ⊥ ∧ Y ≠ zero L ∧
      Y ≠ one L (T : Subgroup G) (V ⊓ omegaOneCenterAmbient (T : Subgroup G)) ∧
      (Y ≠ selectedFirstResidual T L V z.val ∨ Nat.card (Y ⧸ pCore 2 Y) ≠ 3) := by
  have hB := covered_firstFlagCore_baumann_normalizer h structural D m hc z hz hzL
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  have hnzero := covered_zero_not_normal_outside h.toHypothesis1221
    D.sylow_normalizes_component hc.2.1 hout
  have hN1 := covered_one_normalizer h structural D m hc.2.1 z hz hzL
  by_contra hex
  have h1339 (Y : Subgroup G) (hYH : Y ≤ centralizer ({z.val} : Set G))
      (hnY : centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G))
      (hYM : Y ≤ normalizer (L : Set G)) (hp : IsPPerfect 2 Y) :
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3) := by
    by_cases hY0 : Y = ⊥
    · exact Or.inl hY0
    right
    by_contra hf
    have h23 := augmentation_outside_twoThree_at h (structural G T) D m
      (centralizer ({z.val} : Set G)) ⟨centralizer_mem_HOver hz hz1,hout⟩
      Y hYH hnY hp hYM
    exact hex ⟨Y,hYH,hnY,hYM,hp,h23,hY0,
      (fun he => hnzero (he ▸ hnY)),
      (fun he => hout (hnY.trans (he.symm ▸ hN1))),not_and_or.mp hf⟩
  have hord : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) := by
    by_cases hkernel : centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
        (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))) =
        pCore 2 (centralizer ({z.val} : Set G))
    · exact ordinary_of_twoCore_kernel_original_R1 h₀ h structural D m z hz hzL hB hout
        h1339 hsolv hkernel
    · let R := firstFlagCore h structural D m
      obtain ⟨hRT,_,hQR⟩ := firstFlagCore_local_data h structural D m z hz hzL
      have hRC := firstFlagCore_le_residualSection h₀ h structural D m z hz hzL hout h1339 hkernel
      have hcore := (centralizer_intersection_of_residual_section h₀ hz hz1 R hRT hQR hRC).1
      have hJ := centralizer_thompson_noncentral_of_baumann_bound h₀ hz hz1 R hRT hcore hB hout
      have hr := centralizer_firstResidual_threeRank_of_residual_section h₀ h structural D m z hz hzL
        hkernel (selectedFirstResidual T L V z.val) h1339 R hRT hQR hRC hJ hsolv
      let := h.quasisimple
      exact ordinary_of_firstCentralizerResidual_threeRank D m z hzL hr
  obtain ⟨e⟩ := hord
  have hh := Nat.card_congr (centerCongr e).toEquiv
  rw [hc.2.1,alternatingGroup.center_eq_bot (by simp),card_bot] at hh
  omega

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion

/-- The original nonzero fixed part reduces to recognition or a specified
covered residual. The Baumann, L₀ and L₁ normalizer clauses are discharged. -/
theorem fixed_module_recognition_or_residual_obstruction
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3) :
    ClassicalGroup.IsPSp G 3 2 ∨
      (Section08.SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) ∧
        ∃ (z : V) (Y : Subgroup G), z ≠ 1 ∧
          z.val ∈ omegaOneCenterAmbient (T : Subgroup G) ∧
          z.val ∉ centralizer (L : Set G) ∧
          ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G) ∧
          Group.IsSolvable (centralizer ({z.val} : Set G)) ∧
          Y ≤ centralizer ({z.val} : Set G) ∧
          centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) ∧
          Y ≤ normalizer (L : Set G) ∧ IsPPerfect 2 Y ∧ IsPiGroup twoThreePrimes Y ∧
          Y ≠ ⊥ ∧ Y ≠ zero L ∧
          Y ≠ one L (T : Subgroup G) (V ⊓ omegaOneCenterAmbient (T : Subgroup G)) ∧
          (Y ≠ selectedFirstResidual T L V z.val ∨ Nat.card (Y ⧸ pCore 2 Y) ≠ 3)) := by
  rcases fixed_module_recognition_or_solvable_cover hl h₀ D hfixed structural modules earlier
      h1332 fixed five covered h13316 with hr | ⟨hc,z,hz1,hz,hzL,hout,hs⟩
  · exact Or.inl hr
  · have hstar := Section03.Noncentrality.source1332_faithful_maximal
      h₀.qtke T h1332 h₀.local_component
    have h : Hypothesis1223 KnownSimple.IsKnownSimple T L :=
      h₀.hypothesis1311.hypothesis1223
        ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
          h₀.local_component |>.2⟩ (component_quotient_quasisimple h1332 h₀.local_component)
    obtain ⟨m⟩ := coreMarking_of_original_fixed h₀ h D fixed hfixed
    obtain ⟨Y,hY⟩ := covered_solvable_residual_obstruction h₀ h structural D m hc z hz hzL hout hs
    exact Or.inr ⟨hc,z,Y,hz1,hz,hzL,hout,hs,hY⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
