module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalRows
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalCoordinates
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalFour
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalFourExclusionAugmentation
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalFourExclusionEndgame

/-!
# Assembly of the natural-module branch of original 12.3.3

The seven source rows reduce to the natural quotient and the exceptional
four-space. The former reconstructs the entire original V by cohomology
and aligns its marking with the original central quotient. The theorem
below retains precisely the exceptional exclusion as an explicit input.

LocalAnalysisNaturalSource discharges that input using the central-line
residual, component and block arguments. This conditional assembly remains
available with its original public interface and does not assume the parent
A₇ theorem.
Source: Aschbacher--Smith, Lemma 12.3.3, printed pp.807--808.
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

/-- The literal natural coordinates follow from the seven source rows once
the independent ambient four-dimensional contradiction is supplied. -/
theorem naturalCoordinates_of_four_exclusion
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (excludeFour : letI := S.chosen.actionCentralizer_normal
      ((L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7)) →
      Module.finrank (ZMod 2) S.chosen.space = 4 → False) :
    Nonempty S.NaturalCoordinates := by
  let := S.chosen.actionCentralizer_normal
  have rows := S.natural_quotient_or_four (modules G T L V S.hypothesis S.chosen)
  exact rows.elim
    (fun ha => S.naturalCoordinates_of_naturalQuotient (Classical.choice ha))
    (fun hf => (excludeFour (Classical.choice hf.1) hf.2).elim)

end Setup
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
