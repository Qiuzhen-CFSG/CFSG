module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNatural
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisNaturalFourExclusionAugmentation
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisNaturalFourExclusionEndgame
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisNormalizer

/-!
# LocalAnalysisNatural at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisNatural`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

public section

open Subgroup Representation

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

namespace Setup

variable (S : Setup T L V)

theorem naturalCoordinates_of_four_exclusion_at
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (excludeFour : letI := S.chosen.actionCentralizer_normal
      ((L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7)) →
      Module.finrank (ZMod 2) S.chosen.space = 4 → False) :
    Nonempty S.NaturalCoordinates := by
  let := S.chosen.actionCentralizer_normal
  have rows := S.natural_quotient_or_four (modules L V S.hypothesis S.chosen)
  exact rows.elim
    (fun ha => S.naturalCoordinates_of_naturalQuotient (Classical.choice ha))
    (fun hf => (excludeFour (Classical.choice hf.1) hf.2).elim)

end Setup

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

