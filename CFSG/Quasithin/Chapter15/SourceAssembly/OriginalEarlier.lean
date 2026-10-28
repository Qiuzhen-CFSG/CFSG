module
public import CFSG.Quasithin.Chapter15.SourceAssembly.MarkedRecognition
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.CompleteSource

/-!
# The final Theorem E consumer of the remaining original source inputs

The complete multiple-centralizer argument and the original singleton case
split reduce Theorem E to the selected 15.1.3 implication and the orthogonal
case. On the literal orthogonal datum, the rank-two and rank-one exclusions
15.3.13 and 15.3.25 supply the fixed-plane centralizer bound. That same bound
is passed to the original abelian-span assertion 15.3.50, and the completed
15.3 terminal argument gives the contradiction.

The three earlier assertions retain their original rank or shadow hypotheses,
all residual rechoices, and the actual Sylow and local module. No independent
rank bound, normalizer estimate, marked recognition, or full 15.3.1 callback
remains. The earlier assertions and 15.1.3 are still explicit source inputs;
this composition is not an unconditional proof of Theorem E.

Source: Aschbacher--Smith 15.1.3, 15.3.13, 15.3.25, 15.3.50 and the final
proof of Theorem E, printed pp.1086,1124,1131,1140,1165.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15
open Section03 ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal Theorem E application of the remaining original earlier sources. -/
theorem source_theoremE_of_original_earlier_inputs
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
    (h50 : ∀ d : CharacteristicTwo.LocalData G, d.T = T →
      IsOrderingMaximal d.T d.M →
      maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc} →
      centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M →
      IsMulCommutative (conjugateSpanBy d.V d.Mc)) :
    ClassificationModels.IsTheoremEModel G := by
  apply source_theoremE_of_original_singleton_reductions hG T hempty h1513
  intro M Mc hM hu action
  apply orthogonal_exclusion_of_original_local_data T hM hu ?_ action
  intro d hd hm hu
  have he : MainForward.faithfulLocalComponents d.T = ∅ := hd ▸ hempty
  have hn : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard := hd ▸ hmany
  have hf := AbelianAmalgam.LineNormalizerSource.fixedPlane_centralizer_le_of_original_exclusions
    hG d he hm hu hn (h13 d hd hm hu) (h25 d hd hm hu)
  exact AbelianAmalgam.LineNormalizerSource.terminal_contradiction_of_original_fixed_span
    hG d he hm hu hn hf (h50 d hd hm hu hf)

end CFSG.Quasithin.Chapter15
