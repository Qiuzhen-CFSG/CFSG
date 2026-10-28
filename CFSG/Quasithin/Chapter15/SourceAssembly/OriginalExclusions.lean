module
public import CFSG.Quasithin.Chapter15.SourceAssembly.OriginalEarlier
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.TerminalSource

/-!
# Theorem E from the three remaining original source branches

The original abelian-span theorem now discharges 15.3.50 inside the literal
orthogonal terminal argument. Hence the final Theorem E application retains
only the selected 15.1.3 implication and the earlier characteristic-two
exclusions 15.3.13 and 15.3.25. Their rank and shadow hypotheses remain
unchanged, and they are required only for the original residual rechoices.
The complete F.6 recognition and all later orthogonal inputs are proved.

Source: Aschbacher--Smith 15.1.3, 15.3.13, 15.3.25, and the final proof of
Theorem E, printed pp.1086,1124,1131,1165.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15
open Section03 ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The final E case split, retaining precisely its three original open branches. -/
theorem source_theoremE_of_original_exclusions
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (h1513 : ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      ClassificationModels.IsTheoremEModel G ∨
        ∃ M : Subgroup G, IsOrderingMaximal T M ∧
          Nonempty (NaturalOrthogonalAction M (localModule T M)))
    (h13 : ∀ d : CharacteristicTwo.LocalData G, d.T = T →
      IsOrderingMaximal d.T d.M →
      maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc} →
      ∀ Yplus : Subgroup G, Hypothesis15310 d.M d.Y d.S d.V₁ Yplus →
      primeRank 3 Yplus = 2 →
      ∀ I ∈ outsideFamily Yplus d.S d.M, generalizedFitting I ≠ pCore 2 I)
    (h25 : ∀ d : CharacteristicTwo.LocalData G, d.T = T →
      IsOrderingMaximal d.T d.M →
      maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc} →
      ∀ Yplus : Subgroup G, Hypothesis15310 d.M d.Y d.S d.V₁ Yplus →
      SymmetricThreeShadow Yplus d.S →
      ∀ I ∈ outsideFamily Yplus d.S d.M, generalizedFitting I ≠ pCore 2 I)
    : ClassificationModels.IsTheoremEModel G := by
  apply source_theoremE_of_original_singleton_reductions hG T hempty h1513
  intro M Mc hM hu action
  apply orthogonal_exclusion_of_original_local_data T hM hu ?_ action
  intro d hd hm hu
  have he : MainForward.faithfulLocalComponents d.T = ∅ := hd ▸ hempty
  have hn : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard := hd ▸ hmany
  exact AbelianAmalgam.LineNormalizerSource.terminal_contradiction_of_original_earlier_exclusions
    hG d he hm hu hn (h13 d hd hm hu) (h25 d hd hm hu)

end CFSG.Quasithin.Chapter15
