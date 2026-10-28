module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.SourceSetup
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.RankTwoBinary

/-!
# Original source application of the binary C.1.32 branch

The genuine source hypotheses construct the complete small MS-pair. In its
binary parabolic row, the proved central-kernel argument supplies the full
SL₃(2) core quotient and the C.1.32 alternative needed by the original
15.3.31 consumer. No rank-two classification premise remains in this row.

Source: Aschbacher--Smith C.1.32(5) and 15.3.31, printed pp.136,1132.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open RankOneConfiguration SmallExtension
variable {G : Type*} [Group G] [Finite G]

/-- The actual binary marked source satisfies C.1.32(5) unconditionally. -/
theorem source_linearThree_rankTwo
    {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}
    {κ : GroupClass} (s : SourceData κ d c)
    (m : Parabolics.RankTwoParabolicMarking d I c.L
      (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) Parabolics.linearThreeParabolic) :
    MarkedMS.RankTwoAlternatives c.L d.S :=
  MarkedMS.rankTwo_of_linearThree_marking d c s.normal s.sylow s.sylow_eq m
    (MarkedMS.smallMSPair_of_source d c s.sqtk s.characteristicTwo s.generated s.normal
      ⟨s.sylow, s.sylow_eq⟩ s.characteristic (.linearThree m))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
