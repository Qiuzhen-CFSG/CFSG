module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.CubicOrbit.Recognition
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.Source

/-!
# Complete exceptional exhaustion at critical distance two

The faithful initial hexacode branch is already exhausted. In the cubic
initial-kernel branch the original favorable orbit is now recognized; its
whole fixed preimage is retained, so the involution argument contradicts
movement of the generating plane. The two kernel cases therefore give
exhaustion of the entire intrinsic commutator core at distance two.

The applications retain all exceptional block clauses and the literal
C.1.32 rank-two conclusion. Larger-distance exclusion and final natural-or-
exceptional reconstruction remain with this reconstruction owner.
Source: Meierfrankenfeld--Stellmacher (1993), (3.6), pp.870--871;
Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)

include h e hz in
/-- The cubic initial-action kernel cannot occur at critical distance two. -/
theorem cubic_distanceTwo_impossible
    (hk : layerKernel L R = extensionKernel h) (hb : sourceDistance h = 2) : False :=
  CubicAction.false_of_preliminary_recognized h e hz hk
    (CubicAction.selectedOrbitPair h e hz hk hb)
    (CubicAction.preliminary_recognized h e hz hk _)

include h e hz in
/-- Exhaustion at distance two for both possible original action kernels. -/
theorem coreExhaustion_of_distanceTwo (hb : sourceDistance h = 2) : CoreExhaustion L R := by
  rcases centralOmega_centralizer_cases h e hz with hk | hk
  · exact coreExhaustion_of_distanceTwo_faithful h e hz hk hb
  · exact (cubic_distanceTwo_impossible h e hz hk hb).elim

include h e hz in
open ChapterC in
/-- Every exceptional clause on the entire original blockU at distance two. -/
theorem core_facts_of_distanceTwo (hb : sourceDistance h = 2) :
    IsElementaryAbelian 2 (blockU L) ∧
      blockU L ≤ centralizer (pCore 2 L : Set L) ∧
      BlockModuleIrreducible L ∧ Nat.card (blockU L) = 2 ^ 6 ∧
      centralizer (blockU L : Set L) = pCore 2 L :=
  core_facts_of_exhaustion h e hz (coreExhaustion_of_distanceTwo h e hz hb)

include h e hz in
/-- Actual C.1.32 consumer, with no orbit, kernel or recognition premise. -/
theorem rankTwo_of_distanceTwo (hb : sourceDistance h = 2) : RankTwoAlternatives L R :=
  rankTwo_of_exhaustion h e hz (coreExhaustion_of_distanceTwo h e hz hb)

end AlternatingSixReconstruction.Exceptional.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
