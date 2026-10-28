module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.Second.FullSpans

/-!
# The second marked factor and two-span generation

The actual small-branch recognition and its square-map obstruction discharge
non-smallness after the critical shift. The existing conditional assembly
then reapplies FirstStep and proves the literal starred generation identity.
FirstStep remains the explicit independent first-stage contract. The separate
`fullSpans` constructor gives the actual starred quotient by Z_alpha and
VStar = Z_alpha sup core_alpha under only SpanRecognition.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.12), printed p.912.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  (source : LocalSource L R) {geometry : Geometry R}
  (common : CommonFacts R source geometry)

/-- Reapply the first stage at the selected second vertex. The source small
branch is excluded by its genuine single-quotient producer. -/
theorem secondStep (radius : RadiusFacts R geometry) (hb : geometry.b R = 4) :
    SecondStep source common :=
  secondStep_of_singleQuotients source common radius hb
    (singleQuotient_of_smallIntersection source geometry common radius hb)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch
