module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneComplete
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.Complete

/-!
# Unconditional exhaustion of the original exceptional core

The original source dichotomy now closes internally: point, Borel and plane
images have all been excluded, including every critical distance. This proves
the literal whole-core equality and all five exceptional reconstruction clauses
for the given pair and marking, without a Sylow or distance hypothesis.
Source: MS93 (5.11)--(5.12), Section 7; Aschbacher--Smith C.1.32(4).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
universe u

/-- The original cubic initial-kernel branch is impossible. -/
theorem cubic_initial_kernel_impossible
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (hk : layerKernel L R = extensionKernel h) : False := by
  obtain ⟨u,hR⟩ := radical_image_eq_plane h e hz hk
  exact plane_image_impossible h e hz hk u hR

/-- The entire intrinsic core is exhausted on the original source. -/
theorem coreExhaustion_knownSimple
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3) : CoreExhaustion L R := by
  rcases coreExhaustion_or_cubic_plane h e hz with hx | ⟨hk,_,_,_,u,hR⟩
  · exact hx
  · exact (plane_image_impossible h e hz hk u hR).elim

/-- Uniform original exceptional exhaustion, with every source duty proved. -/
theorem coreExhaustionInput_knownSimple :
    CoreExhaustionInput.{u} KnownSimple.IsKnownSimple := by
  intro G _ _ L R h e hz
  exact coreExhaustion_knownSimple h e hz

/-- All five original exceptional whole-block clauses. -/
theorem exceptionalCore_knownSimple :
    ExceptionalCoreInput.{u} KnownSimple.IsKnownSimple :=
  exceptionalCore_of_exhaustion coreExhaustionInput_knownSimple

/-- C.1.32 on the original exceptional pair with no Sylow premise. -/
theorem rankTwo_knownSimple
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3) : RankTwoAlternatives L R :=
  rankTwo_of_exhaustion h e hz (coreExhaustion_knownSimple h e hz)

end AlternatingSixReconstruction.Exceptional
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
