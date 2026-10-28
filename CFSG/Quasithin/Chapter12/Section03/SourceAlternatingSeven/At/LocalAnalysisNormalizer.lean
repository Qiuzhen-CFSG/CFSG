module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNormalizer
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt

/-!
# LocalAnalysisNormalizer at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisNormalizer`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

namespace Setup

variable (S : Setup T L V)

theorem normalizer_le_component_at (S : Setup T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    normalizer (V : Set G) ≤ normalizer (L : Set G) :=
  CFSG.Quasithin.Chapter12.Section02.Hypothesis1223.source_chosen_normalizer_le_at
    S.hypothesis structural
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) S.chosen

namespace NaturalCoordinates

variable {S} (E : S.NaturalCoordinates)

def sourceNormalizerModel_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) : NormalizerModel V :=
  E.normalizerModel (S.normalizer_le_component_at structural)

theorem sourceNormalizerModel_component_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (l : L) :
    (E.sourceNormalizerModel_at structural).permutation ⟨l,S.chosen.normalizes l.property⟩ =
      (S.projection l).val := E.normalizerModel_component _ l

end NaturalCoordinates

end Setup

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

