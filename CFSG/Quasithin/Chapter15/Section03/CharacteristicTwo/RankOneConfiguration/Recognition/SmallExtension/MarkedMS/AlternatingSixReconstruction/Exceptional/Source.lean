module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Recognition

/-!
# Exceptional reconstruction from the source exhaustion equality

The faithful FF classification and the concrete covered-six comparison prove
all five clauses of ExceptionalCoreInput once the MS93 graph argument supplies
[O₂(LR),L] = [Ω₁Z(O₂(LR)),L]. The actual C.1.32 consumer is included below.

The exhaustion input is still explicit. This conditional assembly is not the
unconditional exceptional reconstruction, whose final discharge stays here.
Source: Aschbacher--Smith C.1.22 and C.1.32(4), pp.129,135--136;
Meierfrankenfeld--Stellmacher (1993), Main Theorem (6), Section 7, pp.932--933.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open ChapterC
namespace AlternatingSixReconstruction.Exceptional
universe u

/-- The remaining whole-core source equality suffices; no separate module,
order, irreducibility, or full-centralizer input remains. -/
theorem exceptionalCore_of_exhaustion
    (hx : CoreExhaustionInput.{u} KnownSimple.IsKnownSimple) :
    ExceptionalCoreInput.{u} KnownSimple.IsKnownSimple := by
  intro G _ _ L R h e hz
  exact core_facts_of_exhaustion h e hz (hx G L R h e hz)

/-- Apply the reconstructed entire exceptional core to the unchanged relative
C.1.32 consumer, retaining the actual marking and odd-index radical. -/
theorem rankTwo_of_exhaustion
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3) (hx : CoreExhaustion L R) :
    RankTwoAlternatives L R := by
  obtain ⟨he, hc, hi, hu, hf⟩ := core_facts_of_exhaustion h e hz hx
  exact h.rankTwo_of_alternatingSix_reconstruction e ⟨he, hc, hi, Or.inr ⟨hz, hu, hf⟩⟩

end AlternatingSixReconstruction.Exceptional
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
