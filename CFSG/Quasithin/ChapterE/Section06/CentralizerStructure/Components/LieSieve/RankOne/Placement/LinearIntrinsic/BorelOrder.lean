module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.Placement.LinearIntrinsic.Contracts
public import Theory.SpecificGroups.SL2.EvenBorelSubnormalOrder

/-!
# The binary linear Borel order input

The concrete matrix theorem excludes order twelve for subnormal subgroups
of every finite power of a projective SL₂ Borel over a field of order at
least eight. It supplies the Borel order input for the intrinsic A₃-block
exclusion; the separate short-group calculation remains with final assembly.

Source: Aschbacher–Smith, E.6.8, printed pp.247–248 (PDF pp.258–259).
-/

namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne

/-- The matrix-group order obstruction for the binary linear Borel branch. -/
public theorem linearBorelOrderInput : LinearBorelOrderInput := by
  intro F _ _ _ n hn hF k X hX
  exact Matrix.ProjectiveSpecialLinearGroup.EvenBorelSubnormalOrder.card_ne_twelve_of_isSubnormal
    F n hn hF k X hX

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne
