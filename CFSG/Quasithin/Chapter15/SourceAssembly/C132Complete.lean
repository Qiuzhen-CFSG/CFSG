module

public import CFSG.Quasithin.Chapter15.SourceAssembly.OriginalExclusions
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.C132Complete

/-!
# Original Theorem E with C.1.32 and 15.3.25 supplied

For every permitted residual rechoice, the original rank-one exclusion now
uses the proved C.1.32 theorem. The final E consumer retains precisely its
original 15.1.3 and 15.3.13 inputs, with the same Sylow, singleton-centralizer,
ordering, and residual-choice guards.
Source: Aschbacher--Smith 15.1.3,15.3.13,15.3.25 and Theorem E, p.1165.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15
open Section03 ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Supply the original rank-one branch internally; the independent original
15.1.3 and rank-two 15.3.13 statements retain their exact hypotheses. -/
theorem source_theoremE_of_original_1513_and_15313
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
      ∀ I ∈ outsideFamily Yplus d.S d.M, generalizedFitting I ≠ pCore 2 I) :
    ClassificationModels.IsTheoremEModel G := by
  apply source_theoremE_of_original_exclusions hG T hmany hempty h1513 h13
  intro d hd hM hu Yplus hchoice hshadow
  let d' : CharacteristicTwo.LocalData G := { d with Yplus := Yplus, choice := hchoice }
  have he : MainForward.faithfulLocalComponents d'.T = ∅ := hd ▸ hempty
  have hn : 1 < (maximalTwoLocalOvergroups (d'.T : Subgroup G)).ncard := hd ▸ hmany
  exact CharacteristicTwo.SourceRankOne.OriginalSource.source_lemma_15_3_25_knownSimple
    hG d' he hM hu hn hshadow

end CFSG.Quasithin.Chapter15
