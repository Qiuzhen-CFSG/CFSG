module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.Models.Moving
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.Models.Outer

/-!
# The actual bad-case edge offenders

All three marked bad alternatives rule out involution displacement one on
the literal X action. For the doubled and central-extension branches this
follows from full commutator generation on the actual U and its order; for
the outer extension it follows from the actual index and full fixed subgroup.
Faithfulness, the rank-two bound, and self-centrality of four-groups then
give uniqueness and equality for the offender already constructed on every
adjacent edge.

The conclusion is exactly SourceCases.EdgeOffenderUniqueness: existence,
uniqueness among nontrivial elementary offenders, equal fixed codimension
and rank, and the centralizer identity in the actual marked edge image.
This is the bad-alternative calculation used in (3.8), before its exclusion
argument.
Source: Meierfrankenfeld–Stellmacher (1993), printed pp.863,877.
-/

public section
open Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.Models
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- Every bad alternative excludes transvections on the actual marked X action. -/
theorem badCase_involutionBound (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (hbad : BadCase source) : InvolutionBound source := by
  rcases hbad with h | h | h
  · exact splitDouble_involutionBound source geometry hb h
  · exact centralExtension_involutionBound source geometry hb h
  · exact outerExtension_involutionBound source geometry hb h

/-- The exact all-edge rigidity statement used on printed p.877, proved for
each of the three actual marked binary bad alternatives. -/
theorem badCase_edgeOffenderUniqueness (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (hbad : BadCase source) : EdgeOffenderUniqueness source :=
  edgeOffenderUniqueness_of_involutionBound source geometry hb
    (badCase_involutionBound source geometry hb hbad)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.Models
