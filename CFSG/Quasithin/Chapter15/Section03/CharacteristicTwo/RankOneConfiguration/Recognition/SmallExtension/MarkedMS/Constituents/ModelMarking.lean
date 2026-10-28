module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Constituents.Plane
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.Interfaces

/-!
# The given rank-two marking marks the actual V₂ stabilizer

The exact stabilizer calculated on U_L maps to the indicated minimal
parabolic under the very same equivalence supplied by 15.3.28. No new
group marking, representation or diagram action is substituted.
Constituent selection remains the separate B.5.6 action comparison.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.28(2) and proof of 15.3.31, printed pp.1131–1132.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents
open EightGeometry.NaturalModule.Recognition

/-- The source marking is also the marking of the literal plane stabilizer. -/
theorem plane_stabilizer_model {G H : Type*} [Group G] [Finite G] [Group H]
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hn : (c.L.subgroupOf I).Normal) (hI : I = c.L ⊔ d.S)
    (hf : HasCharacteristicTwo I)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    [IsElementaryAbelian 2 ((d.componentModule I c.L).subgroupOf I)]
    (hline : LineData d I) (hYL : d.Yplus ≤ c.L)
    (hRank : primeRank 3 d.Yplus = 1) (hYRank : 2 ≤ primeRank 3 d.Y)
    (parabolic : Fin 2 → Subgroup H)
    (m : Parabolics.RankTwoParabolicMarking d I c.L H parabolic) :
    (subspaceStabilizer ((componentAction d c hn hI hf P hP).comp
      (d.starImage I c.L).subtype) (planeSpace d c)).map m.equiv.toMonoidHom =
        parabolic m.node := by
  rw [plane_stabilizer_eq_of_rank_one d c hn hI hf P hP hline hYL hRank hYRank]
  exact m.intersection

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents
