module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.OriginalSource
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.Source
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.Complete
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.OriginalAssembly
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.OriginalSource.Source38
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.RankTwoRank

/-!+# The original orthogonal exclusion with later source inputs discharged

The original outside-subgroup alternative combines the rank-two exclusion
15.3.13 and rank-one exclusion 15.3.25. The proved 15.3.35--45 argument then
controls the fixed-plane centralizer for both choices in Hypothesis 15.3.10.
Once the original span is abelian, the proved 15.3.63--65 rank bound selects
the singular line and the complete F.6 theorem gives the final contradiction.

The remaining assumptions are precisely the two earlier characteristic-two
exclusions and abelian span 15.3.50, on the original local datum. In particular,
the rank-two exclusion is used only under its original three-rank hypothesis.

Source: Aschbacher--Smith 15.3.13, 15.3.25, 15.3.35--50 and 15.3.63--68.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizerSource
open ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The complete later argument from the actual fixed plane and abelian span.
The rank bound and corrected F.6 are proved internally. -/
theorem terminal_contradiction_of_original_fixed_span
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M)
    (hspan : IsMulCommutative (conjugateSpanBy d.V d.Mc)) : False := by
  let := hspan
  exact terminal_contradiction_of_original_span_rank hG d hempty hM hu hmany hfixed hspan
    (AbelianAmalgam.OriginalSource.globalR_eq_two_from_original
      hG d hempty hM hu hmany hfixed)
    GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.sourceClassification_knownSimple_complete

/-- The two genuine characteristic-two source branches imply the literal
fixed-plane bound, with original source38 and source35 discharged. -/
theorem fixedPlane_centralizer_le_of_original_exclusions
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (h13 : ∀ Yplus : Subgroup G, Hypothesis15310 d.M d.Y d.S d.V₁ Yplus →
      primeRank 3 Yplus = 2 →
      ∀ I ∈ outsideFamily Yplus d.S d.M, generalizedFitting I ≠ pCore 2 I)
    (h25 : ∀ Yplus : Subgroup G, Hypothesis15310 d.M d.Y d.S d.V₁ Yplus →
      SymmetricThreeShadow Yplus d.S →
      ∀ I ∈ outsideFamily Yplus d.S d.M, generalizedFitting I ≠ pCore 2 I) :
    centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M := by
  apply source_fixedPlane_centralizer_le_of_original_component_exclusions
    hG d hempty hM hu hmany h25
  intro Yplus hchoice I hI
  let d' : CharacteristicTwo.LocalData G := { d with Yplus := Yplus, choice := hchoice }
  apply RankTwo.OriginalSource.source_lemma_15_3_35_shadow_from_selection
    hG d' hempty hM hu hmany ?_ hI
  intro J hJ
  rcases (OutsideStructure.source_lemma_15_3_11_from_selection
    hG d' hempty hM hu hmany J hJ).local_structure with htwo | hone
  · exact h13 Yplus hchoice
      (OutsideStructure.rankTwoCase_three_rank hG d' hJ htwo) J hJ
  · exact h25 Yplus hchoice hone.2.1 J hJ

/-- Original 15.3.1 reduced to its remaining earlier source branches on the
literal orthogonal datum; no later rank, normalizer or recognition premise remains. -/
theorem terminal_contradiction_of_original_exclusions
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (h13 : ∀ Yplus : Subgroup G, Hypothesis15310 d.M d.Y d.S d.V₁ Yplus →
      primeRank 3 Yplus = 2 →
      ∀ I ∈ outsideFamily Yplus d.S d.M, generalizedFitting I ≠ pCore 2 I)
    (h25 : ∀ Yplus : Subgroup G, Hypothesis15310 d.M d.Y d.S d.V₁ Yplus →
      SymmetricThreeShadow Yplus d.S →
      ∀ I ∈ outsideFamily Yplus d.S d.M, generalizedFitting I ≠ pCore 2 I)
    (hspan : IsMulCommutative (conjugateSpanBy d.V d.Mc)) : False :=
  terminal_contradiction_of_original_fixed_span hG d hempty hM hu hmany
    (fixedPlane_centralizer_le_of_original_exclusions hG d hempty hM hu hmany h13 h25) hspan

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizerSource
