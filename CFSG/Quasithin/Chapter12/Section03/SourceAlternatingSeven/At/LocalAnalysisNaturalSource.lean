module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalSource
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisFusion
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisNatural
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisNaturalFourExclusionSelection

/-!
# LocalAnalysisNaturalSource at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisNaturalSource`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory Representation

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

namespace Setup

variable (S : Setup T L V)

theorem naturalCoordinates_nonempty_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) : Nonempty S.NaturalCoordinates :=
  S.naturalCoordinates_of_four_exclusion_at modules (S.four_false_at structural escape)

def naturalCoordinates_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) : S.NaturalCoordinates :=
  Classical.choice (S.naturalCoordinates_nonempty_at structural modules escape)

def localAnalysis_of_natural_source_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hpoints : let E := S.naturalCoordinates_at structural modules escape
      ∀ v : V, v ≠ 1 →
        (weight (E.coordinates v).toAdd.val = 2 ∨
          weight (E.coordinates v).toAdd.val = 6) →
        centralizer ({(v:G)} : Set G) ≤ normalizer (L : Set G)) : S.LocalAnalysis :=
  (S.naturalCoordinates_at structural modules escape).localAnalysis_at structural hNT hpoints

end Setup

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

