module
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.Second
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.Sporadic.Rudvalis

/-!
# The marked Rudvalis inspection in E.6.18

The checked order of the literal second involution centralizer discharges the
last numerical premise of the Rudvalis action inspection. The actual model
isomorphism, automorphism and transported centralizer remain unchanged.
Source: Aschbacher–Smith, Quasithin E.6.18 and 16.1.5(11), pp.252,1172.
-/

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SporadicInspection
public theorem rudvalis
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hnc : ¬ IsMulCommutative S) (e : S ≃* Rudvalis.Model) : SevenActionInspection S :=
  rudvalis_of_second_centralizer hnc e Rudvalis.InvolutionCentralizers.second_centralizer_not_nine
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SporadicInspection
