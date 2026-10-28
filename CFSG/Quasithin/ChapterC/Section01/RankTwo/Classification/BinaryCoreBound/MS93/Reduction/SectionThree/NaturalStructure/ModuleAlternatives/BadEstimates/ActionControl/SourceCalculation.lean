module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.ActionControl.SourceCalculation.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.ActionControl.SourceCalculation.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.ActionControl.SourceCalculation.SplitAndCentral
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.ActionControl.SourceCalculation.Outer

/-!
# The source-(3.3) bound in all three binary bad branches

The branch transports retain the actual conjugation models at every source
vertex. The quotient criterion uses the literal actor Q_t ∩ C([Z_a,Z_a'])
and the literal quotient X_a'/[Z_a,Z_a'], retaining the auxiliary commutator
on the right side of printed (3.3).

The doubled and central-extension calculations put the endpoint displacement
inside the critical commutator. The outer-extension calculation uses the
index of that commutator in the natural moving layer and retains it on the
right of the bound. Splitting the actual BadCase disjunction now gives
Source33Bound without any additional action or displacement premise.

These direct calculations establish the containment needed in the three
binary bad branches. Printed (3.3) itself states alternatives under failure
of this containment; no general failure-alternatives theorem is assumed here.

Source: Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.2)–(3.3), printed pp.863–868.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.SourceCalculation

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- Every binary bad branch satisfies the literal source-(3.3) bound,
with its penultimate vertex, centralizing actors and auxiliary commutator.
The three model calculations discharge all action and displacement premises. -/
theorem badCase_source33Bound (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (hbad : BadCase source) :
    Source33Bound R geometry := by
  rcases hbad with hsplit | hcentral | houter
  · exact Split.source33Bound source geometry hb hsplit
  · exact Central.source33Bound source geometry hb hcentral
  · exact Outer.source33Bound source geometry hb houter

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.SourceCalculation
