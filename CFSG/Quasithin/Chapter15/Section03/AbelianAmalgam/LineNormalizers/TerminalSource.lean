module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.CompleteSource
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Original

/-!
# The original orthogonal exclusion from its two earlier branches

The rank-two and rank-one component exclusions give the fixed-plane
centralizer bound. The original 15.3.50 theorem then makes the actual
involution-centralizer span abelian, so the proved line-normalizer argument
and complete F.6 classification give the contradiction. Thus neither the
fixed-plane bound nor the abelian span remains an input to the E assembly.

Source: Aschbacher--Smith, 15.3.13, 15.3.25 and 15.3.35--68.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizerSource
open ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original orthogonal contradiction with all later source inputs
discharged. Only the earlier rank-two and rank-one exclusions remain. -/
theorem terminal_contradiction_of_original_earlier_exclusions
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
      ∀ I ∈ outsideFamily Yplus d.S d.M, generalizedFitting I ≠ pCore 2 I) : False := by
  have hfixed := fixedPlane_centralizer_le_of_original_exclusions
    hG d hempty hM hu hmany h13 h25
  have hspan := Nonabelian.Fusion.Source50.local_span_abelian_from_original
    hG d hempty hM hu hmany hfixed
  exact terminal_contradiction_of_original_fixed_span
    hG d hempty hM hu hmany hfixed hspan

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizerSource
