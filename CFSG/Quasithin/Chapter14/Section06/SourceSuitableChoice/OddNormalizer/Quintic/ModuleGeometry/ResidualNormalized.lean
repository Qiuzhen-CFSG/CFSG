module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ModuleGeometry.ResidualPointClosure
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.SourceComponent.RadicalNormalization

/-!
# The normalized component comparison for the original residual factors

The constructed residual geometry now supplies C.2.7 and the marked
natural-row exclusion for every escaping component. The full-Sylow branch
is eliminated by the actual quotient-action Borel calculation, removing
the former radical-normalization premise from this consumer.

The original index-two normalizer assertion is still a premise. Its proof,
the exchanged module geometry, the remaining normalized model comparisons
and the final p=3 assembly remain with qt-e-14615-quintic-exclusion.
The original 14.6.12--14 inputs retain discharge with
qt-e-suitable-odd-normalizer. This theorem is not the completed 14.6.15.
Source: Aschbacher--Smith 14.6.15, printed pp.1034--1035.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ComponentExclusion ComponentExclusion.ContainedComparison
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)
local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))
variable (hclosure : residualClosure H Mc = residual H)
    (hindex : (Mc ⊓ normalizer (residual H2 : Set G)).relIndex Mc = 2)

include s hclosure hindex in
/-- The literal residual component is normalized and has no marked natural row;
no ordinary-centralizer identity or additional normalization premise is used. -/
theorem indexed_residual_normalized_component_comparison :
    Nonempty (SourceEscapingComponent Mc (residualClosure H Mc)
      (residual H1) (residual H2) (Mc.pCoreIn 2)) ∧
    ∀ j : SourceEscapingComponent Mc (residualClosure H Mc)
      (residual H1) (residual H2) (Mc.pCoreIn 2),
      Input KnownSimple.IsKnownSimple (normalizer (residual H2 : Set G))
        (Mc.pCoreIn 2) (Mc ⊓ normalizer (residual H2 : Set G)) j.J ∧
      ¬Nonempty (NaturalStarRow j.J (Mc.pCoreIn 2)) := by
  let d := indexedResidualNormalizerGeometry s hclosure hindex
  have he := indexedResidualNormalizerGeometry_factors s hclosure hindex
  change d.K1 = residual H1 ∧ d.K2 = residual H2 at he
  rw [←he.1,←he.2]
  refine ⟨exists_source_escaping_component s d,?_⟩
  intro j
  exact ⟨source_component_input s d j,source_component_no_natural_row s d j⟩

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
